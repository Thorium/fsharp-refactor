/// The FsAutoComplete sidecar: one process per Visual Studio session,
/// spoken to over LSP. Out-of-process on purpose — VS's own F# tools load
/// their own FSharp.Compiler.Service in-proc, and loading ours beside it
/// is the assembly-binding wound Visual F# Power Tools kept reopening.
/// FSAC brings project cracking, incremental checking and analyzer
/// loading; this extension only renders what it publishes.
module FSharp.Refactor.Vsix.FsacClient

open System
open System.Collections.Concurrent
open System.Diagnostics
open System.IO
open System.Threading
open Newtonsoft.Json.Linq
open FSharp.Refactor.Vsix.Lsp

/// One key spelling for a document, whatever the URI looked like: the
/// sidecar publishes `file:///c%3A/...` (lowercase drive, encoded colon)
/// while the editor hands us `C:\...` — comparing URIs raw meant the
/// stored diagnostics could never be FOUND again. TOTAL by construction:
/// GetFullPath throwing on a URI-shaped input escaped the listener thread
/// once and took the whole of Visual Studio down with it.
let normalizePath (p: string) =
    // an LSP URI with an ENCODED drive colon (file:///c%3A/...) decodes
    // via Uri.LocalPath to unix-style "/c:/dir/file" — strip to a
    // windows path before GetFullPath, which throws on that shape
    let p =
        if p.Length >= 3 && p[0] = '/' && Char.IsLetter p[1] && p[2] = ':' then
            p.Substring 1
        else
            p

    let p = p.Replace('/', '\\')

    try
        Path.GetFullPath(p).ToLowerInvariant()
    with _ -> // fall back to raw casefold; a miss beats a crash; fsharpanalyzer: ignore-line FR0055
        p.ToLowerInvariant()

/// Diagnostics with FSharp.Refactor codes, keyed by NORMALIZED local
/// path. VS's F# tools already surface compiler errors; duplicating them
/// would be noise, so everything without an FR code is dropped on
/// arrival.
let diagnostics = ConcurrentDictionary<string, Diag list>()

/// Raised (with the document's local path) when a document's FR
/// diagnostics change; taggers subscribe.
let diagnosticsChanged = Event<string>()

let private log = ConcurrentQueue<string>()

/// Everything traced also lands here, because a frozen or silent editor
/// is undebuggable without it.
let logFile = Path.Combine(Path.GetTempPath(), "FSharpRefactor.Vsix.log")

let private fileLock = obj ()

let private trace (line: string) =
    let stamp = DateTime.Now.ToString "HH:mm:ss"
    let entry = $"[{stamp}] {line}"
    log.Enqueue entry

    while log.Count > 500 do
        log.TryDequeue() |> ignore

    try
        lock fileLock (fun () -> File.AppendAllText(logFile, entry + Environment.NewLine))
    with _ -> // logging must never take the editor down; fsharpanalyzer: ignore-line FR0055
        ()

/// The rolling client log, for a diagnostics command / debugging.
let recentLog () = log.ToArray()

/// Tracing for the rendering modules, same sink as the client's own.
let clientTrace (line: string) = trace line

/// Settings without an options page: `%APPDATA%\FSharp.Refactor\vsix.json`
///
///     { "fsac": "C:\\tools\\fsautocomplete.dll",
///       "analyzers": [ "C:\\my\\analyzers" ],
///       "root": "C:\\src\\MySolution" }
///
/// and the environment variables FSHARP_REFACTOR_FSAC,
/// FSHARP_REFACTOR_ANALYZERS (a `;` list) and FSHARP_REFACTOR_ROOT, which
/// win over the file. Read once per session; edit, restart Visual Studio.
let settingsFile =
    Path.Combine(Environment.GetFolderPath Environment.SpecialFolder.ApplicationData, "FSharp.Refactor", "vsix.json")

let private settings =
    lazy
        (try
            if File.Exists settingsFile then
                let parsed = JObject.Parse(File.ReadAllText settingsFile)
                trace $"settings read from {settingsFile}"
                parsed
            else
                JObject()
         with ex -> // a broken settings file must not take the editor down; fsharpanalyzer: ignore-line FR0055
             trace $"settings file {settingsFile} ignored: {ex.Message}"
             JObject())

let private setting (name: string) (variable: string) : string option =
    match Environment.GetEnvironmentVariable variable with
    | v when not (String.IsNullOrWhiteSpace v) -> Some(v.Trim())
    | _ ->
        match settings.Force().[name] with
        | null -> None
        | token ->
            match token.Type with
            | JTokenType.String when not (String.IsNullOrWhiteSpace(token.Value<string>())) ->
                Some(token.Value<string>().Trim())
            | _ -> None

let private settingList (name: string) (variable: string) : string list =
    match Environment.GetEnvironmentVariable variable with
    | v when not (String.IsNullOrWhiteSpace v) ->
        v.Split([| ';' |], StringSplitOptions.RemoveEmptyEntries)
        |> Array.map (fun s -> s.Trim())
        |> List.ofArray
    | _ ->
        match settings.Force().[name] with
        | :? JArray as items -> [ for i in items -> i.Value<string>() ]
        | null -> []
        | token -> [ token.Value<string>() ]

/// A workspace root the user pinned, when it exists.
let configuredRoot () =
    setting "root" "FSHARP_REFACTOR_ROOT" |> Option.filter Directory.Exists

/// Locate fsautocomplete: the configured one, then the copy bundled
/// beside this extension, then the user's global dotnet tool. A `.dll`
/// runs under `dotnet`, anything else is launched as it is.
let private findFsac () =
    let launch (path: string) =
        if path.EndsWith(".dll", StringComparison.OrdinalIgnoreCase) then
            "dotnet", $"\"%s{path}\""
        else
            path, ""

    let bundled =
        Path.Combine(Path.GetDirectoryName(typeof<Diag>.Assembly.Location), "fsac", "fsautocomplete.dll")

    let toolExe =
        Path.Combine(
            Environment.GetFolderPath Environment.SpecialFolder.UserProfile,
            ".dotnet",
            "tools",
            "fsautocomplete.exe"
        )

    match setting "fsac" "FSHARP_REFACTOR_FSAC" with
    | Some configured when File.Exists configured ->
        trace $"fsac: configured {configured}"
        ValueSome(launch configured)
    | Some configured ->
        trace $"fsac: configured {configured} does not exist, falling back"

        if File.Exists bundled then ValueSome(launch bundled)
        elif File.Exists toolExe then ValueSome(launch toolExe)
        else ValueNone
    | None ->
        if File.Exists bundled then
            trace "fsac: bundled"
            ValueSome(launch bundled)
        elif File.Exists toolExe then
            trace "fsac: global tool"
            ValueSome(launch toolExe)
        else
            ValueNone

/// Directories to hand FSAC as analyzer paths: any the user configured,
/// then the analyzers bundled with this extension (built against the same
/// SDK its FSAC pairs with).
let private analyzerPaths () =
    let beside =
        Path.Combine(Path.GetDirectoryName(typeof<Diag>.Assembly.Location), "analyzers")

    let configured =
        settingList "analyzers" "FSHARP_REFACTOR_ANALYZERS"
        |> List.filter Directory.Exists

    configured @ (if Directory.Exists beside then [ beside ] else [])

type Session =
    {
        Proc: Process
        Rpc: JsonRpc
        mutable Initialized: bool
        /// Tells one sidecar from the one that replaced it: a buffer whose
        /// didOpen went to a sidecar that has since died re-opens on the
        /// next one instead of sending a didChange it cannot place.
        Id: int
    }

let mutable private session: Session option = None
let private startLock = obj ()
let mutable private lastSessionId = 0

/// Gone, or unreadable — a process whose state cannot be asked for is not
/// one to write to either.
let private hasExited (s: Session) =
    try
        s.Proc.HasExited
    with _ -> // fsharpanalyzer: ignore-line FR0055
        true

/// Forget THAT session — a newer one already in its place stays — so the
/// next `ensure` starts a fresh sidecar. Before this the dead session was
/// kept and every send went on writing to its pipe.
let private dropSession (s: Session) (reason: string) =
    lock startLock (fun () ->
        match session with
        | Some current when obj.ReferenceEquals(current, s) ->
            trace $"fsac session #{s.Id} dropped: {reason}"
            session <- None
        | _ -> ())

/// The session that is still running, dropping one that has exited.
let private live () : Session option =
    match session with
    | Some s when not (hasExited s) -> Some s
    | Some s ->
        dropSession s "process has exited"
        None
    | None -> None

/// One exchange with the live sidecar, or `fallback` when there is none.
/// Nothing thrown leaves this function: the callers sit on timer threads
/// and inside MEF calls, where an unhandled exception ENDS Visual Studio
/// — the IOException from writing to an exited sidecar's pipe did just
/// that. A broken pipe, or any failure once the process is gone, drops
/// the session so the next `ensure` restarts it.
let private trySend (what: string) (fallback: 'a) (f: Session -> 'a) : 'a =
    match live () with
    | None -> fallback
    | Some s ->
        try
            f s
        with ex ->
            trace $"{what} FAILED: {ex.GetType().Name}: {ex.Message}"

            let rec pipeBroken (e: exn) =
                match e with
                | :? IOException
                | :? ObjectDisposedException
                | :? OperationCanceledException -> true
                | :? AggregateException as ae -> ae.InnerExceptions |> Seq.exists pipeBroken
                | _ -> false

            if pipeBroken ex then
                dropSession s "pipe broken"
            elif hasExited s then
                dropSession s "process exited during the exchange"

            fallback

/// The live sidecar's id, for buffers to tell a restart by; None while
/// there is none running.
let sessionId () : int option = live () |> Option.map (fun s -> s.Id)

let private startSession (rootDir: string) : Session option =
    match findFsac () with
    | ValueNone ->
        trace "fsautocomplete not found: bundle it or `dotnet tool install -g fsautocomplete`"
        None
    | ValueSome(exe, argPrefix) ->
        let psi =
            ProcessStartInfo(
                FileName = exe,
                Arguments = $"%s{argPrefix} --adaptive-lsp-server-enabled".Trim(),
                UseShellExecute = false,
                RedirectStandardInput = true,
                RedirectStandardOutput = true,
                RedirectStandardError = true,
                CreateNoWindow = true,
                WorkingDirectory = rootDir
            )

        let proc = Process.Start psi

        let rpc =
            JsonRpc(proc.StandardOutput.BaseStream, proc.StandardInput.BaseStream, trace)

        proc.ErrorDataReceived.Add(fun e ->
            if not (isNull e.Data) then
                trace $"fsac stderr: {e.Data}")

        proc.BeginErrorReadLine()

        rpc.OnNotification(
            "textDocument/publishDiagnostics",
            fun p ->
                let uri, diags = parseDiagnostics p
                let ours = diags |> List.filter (fun d -> d.Code.StartsWith "FR0")
                let path = normalizePath (pathOfUri uri)
                trace $"diagnostics for {path}: {List.length ours} FR of {List.length diags} total"
                diagnostics[path] <- ours
                diagnosticsChanged.Trigger path
        )

        rpc.OnNotification(
            "window/logMessage",
            fun p ->
                match p["message"] with
                | null -> ()
                | m -> trace $"fsac: {m.Value<string>()}"
        )

        let listener =
            Thread((fun () -> rpc.Listen CancellationToken.None), IsBackground = true)

        listener.Start()

        let initParams =
            JObject(
                [
                    JProperty("processId", Process.GetCurrentProcess().Id)
                    JProperty("rootUri", uriOfPath rootDir)
                    JProperty(
                        "capabilities",
                        JObject(
                            [
                                JProperty("textDocument", JObject([ JProperty("publishDiagnostics", JObject()) ]))
                            ]
                        )
                    )
                    JProperty("initializationOptions", JObject([ JProperty("AutomaticWorkspaceInit", true) ]))
                ]
            )

        try
            rpc.Request("initialize", initParams).Wait(TimeSpan.FromSeconds 30.) |> ignore
            rpc.Notify("initialized", JObject())

            // the settings Ionide would send: analyzers on, pointed at the
            // assemblies bundled with this extension
            let settings =
                JObject(
                    [
                        JProperty(
                            "settings",
                            JObject(
                                [
                                    JProperty(
                                        "FSharp",
                                        JObject(
                                            [
                                                JProperty("EnableAnalyzers", true)
                                                JProperty("AnalyzersPath", JArray(analyzerPaths ()))
                                            ]
                                        )
                                    )
                                ]
                            )
                        )
                    ]
                )

            rpc.Notify("workspace/didChangeConfiguration", settings)
            trace $"fsac started for {rootDir}"

            // under startLock, as every caller of startSession is
            lastSessionId <- lastSessionId + 1

            let s =
                {
                    Proc = proc
                    Rpc = rpc
                    Initialized = true
                    Id = lastSessionId
                }

            // a sidecar that dies is forgotten the moment it does, so no
            // send reaches its pipe; the sends check HasExited as well, for
            // the window before the event fires
            try
                proc.EnableRaisingEvents <- true
                proc.Exited.Add(fun _ -> dropSession s "process exited")
            with ex -> // the HasExited checks still stand; fsharpanalyzer: ignore-line FR0055
                trace $"fsac exit watch not registered: {ex.Message}"

            Some s
        with ex ->
            trace $"fsac initialize failed: {ex.Message}"

            try
                proc.Kill()
            with _ -> // deliberate best-effort cleanup; fsharpanalyzer: ignore-line FR0055
                ()

            None

/// The session, started on first use rooted at the given directory.
let ensure (rootDir: string) : Session option =
    lock startLock (fun () ->
        match session with
        | Some s when not (hasExited s) -> Some s
        | _ ->
            session <- startSession rootDir
            session)

let notifyOpened (path: string) (text: string) =
    trace $"didOpen {path} ({text.Length} chars), session={session.IsSome}"

    trySend "didOpen" () (fun s ->
        s.Rpc.Notify(
            "textDocument/didOpen",
            JObject(
                [
                    JProperty(
                        "textDocument",
                        JObject(
                            [
                                JProperty("uri", uriOfPath path)
                                JProperty("languageId", "fsharp")
                                JProperty("version", 1)
                                JProperty("text", text)
                            ]
                        )
                    )
                ]
            )
        ))

let notifyChanged (path: string) (version: int) (text: string) =
    trySend "didChange" () (fun s ->
        s.Rpc.Notify(
            "textDocument/didChange",
            JObject(
                [
                    JProperty(
                        "textDocument",
                        JObject([ JProperty("uri", uriOfPath path); JProperty("version", version) ])
                    )
                    JProperty("contentChanges", JArray(JObject([ JProperty("text", text) ])))
                ]
            )
        ))

/// The code actions the sidecar offers for the given FR diagnostics at a
/// position. Returns (title, list of (startLine, startCol, endLine,
/// endCol, newText)) per action — enough to apply against the buffer.
let codeActions (path: string) (diags: Diag list) : (string * (int * int * int * int * string) list) list =
    // a request the listener cancelled (the sidecar exited mid-wait) throws
    // out of Wait; trySend turns that into an empty answer and a restart
    trySend "codeAction" [] (fun s ->
        let range (d: Diag) =
            JObject(
                [
                    JProperty("start", JObject([ JProperty("line", d.StartLine); JProperty("character", d.StartCol) ]))
                    JProperty("end", JObject([ JProperty("line", d.EndLine); JProperty("character", d.EndCol) ]))
                ]
            )

        match diags with
        | [] -> []
        | first :: _ ->
            let ps =
                JObject(
                    [
                        JProperty("textDocument", JObject([ JProperty("uri", uriOfPath path) ]))
                        JProperty("range", range first)
                        JProperty(
                            "context",
                            JObject([ JProperty("diagnostics", JArray(diags |> List.map (fun d -> d.Raw))) ])
                        )
                    ]
                )

            let task = s.Rpc.Request("textDocument/codeAction", ps)

            if not (task.Wait(TimeSpan.FromSeconds 5.)) then
                trace "codeAction timed out"
                []
            else
                match task.Result with
                | :? JArray as actions ->
                    [
                        for a in actions do
                            let title =
                                match a["title"] with
                                | null -> "Fix"
                                | t -> t.Value<string>()

                            let edits =
                                [
                                    let editNode = a["edit"]

                                    if not (isNull editNode) then
                                        // WorkspaceEdit: either documentChanges or changes
                                        let textEdits =
                                            match editNode["documentChanges"] with
                                            | :? JArray as dcs ->
                                                [
                                                    for dc in dcs do
                                                        match dc["edits"] with
                                                        | :? JArray as es -> yield! es
                                                        | _ -> ()
                                                ]
                                            | _ ->
                                                match editNode["changes"] with
                                                | :? JObject as chs ->
                                                    [
                                                        for p in chs.Properties() do
                                                            match p.Value with
                                                            | :? JArray as es -> yield! es
                                                            | _ -> ()
                                                    ]
                                                | _ -> []

                                        for e in textEdits do
                                            let r = e["range"]

                                            yield
                                                r["start"].["line"].Value<int>(),
                                                r["start"].["character"].Value<int>(),
                                                r["end"].["line"].Value<int>(),
                                                r["end"].["character"].Value<int>(),
                                                e["newText"].Value<string>()
                                ]

                            if not edits.IsEmpty then
                                title, edits
                    ]
                | _ -> [])
