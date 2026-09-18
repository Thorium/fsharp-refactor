/// Wires an ITextBuffer to the sidecar's document sync: didOpen on first
/// sight, full-text didChange on edits (debounced). Created lazily by the
/// tagger provider, one per buffer, tracked by buffer properties.
module FSharp.Refactor.Vsix.BufferSessions

open System
open System.IO
open System.Threading
open Microsoft.VisualStudio.Text
open FSharp.Refactor.Vsix

type BufferSession(buffer: ITextBuffer, filePath: string) =
    let mutable version = 1
    let mutable pendingTimer: Timer option = None

    let rootDir =
        // FSAC discovers the workspace itself (AutomaticWorkspaceInit)
        // from the root it is given. The TOPMOST solution above the file
        // wins — rooted at the nearest project, FSAC saw one project and
        // none of its siblings, and a file's references into them stayed
        // unresolved. Failing a solution, the nearest project; failing
        // that, the file's own directory. A configured root overrides all
        // of it.
        match FsacClient.configuredRoot () with
        | Some root -> root
        | None ->
            let ancestors =
                DirectoryInfo(Path.GetDirectoryName filePath)
                |> Seq.unfold (fun (d: DirectoryInfo) -> if isNull d then None else Some(d, d.Parent))
                |> Seq.truncate 12
                |> List.ofSeq

            let holds (extensions: string list) (d: DirectoryInfo) =
                try
                    Directory.EnumerateFiles d.FullName
                    |> Seq.exists (fun f ->
                        extensions
                        |> List.exists (fun e -> f.EndsWith(e, StringComparison.OrdinalIgnoreCase)))
                with _ -> // an unreadable ancestor is not a root; fsharpanalyzer: ignore-line FR0055
                    false

            match ancestors |> List.filter (holds [ ".sln"; ".slnx" ]) |> List.tryLast with
            | Some solutionDir -> solutionDir.FullName
            | None ->
                match ancestors |> List.tryFind (holds [ ".fsproj" ]) with
                | Some projectDir -> projectDir.FullName
                | None -> Path.GetDirectoryName filePath

    /// The sidecar this buffer's didOpen went to. A sidecar that died and
    /// was restarted knows nothing of the document: the next change is
    /// sent to it as a fresh didOpen, not a didChange it cannot place.
    let mutable openedIn: int option = None

    let sendOpen () =
        match FsacClient.sessionId () with
        | Some id ->
            openedIn <- Some id
            version <- 1
            FsacClient.notifyOpened filePath (buffer.CurrentSnapshot.GetText())
        | None -> ()

    let sendChange () =
        match FsacClient.sessionId () with
        | Some id when openedIn = Some id ->
            version <- version + 1
            FsacClient.notifyChanged filePath version (buffer.CurrentSnapshot.GetText())
        | Some _ -> sendOpen ()
        // no live sidecar: the next buffer to open starts one, and this
        // buffer re-opens itself there on its next change
        | None -> ()

    do
        // OFF the UI thread: this constructor runs inside tagger creation,
        // and the first session spawns a process and waits for its LSP
        // initialize — synchronously that froze Visual Studio for the
        // whole handshake (the responsiveness banner fired at 8s, live)
        System.Threading.Tasks.Task.Run(fun () ->
            try
                match FsacClient.ensure rootDir with
                | Some _ -> sendOpen ()
                | None -> ()
            with ex ->
                FsacClient.clientTrace $"didOpen {filePath} FAILED: {ex.GetType().Name}: {ex.Message}")
        |> ignore

        buffer.Changed.Add(fun _ ->
            // debounce: FSAC rechecks per didChange; typing bursts collapse
            match pendingTimer with
            | Some t -> t.Dispose()
            | None -> ()

            pendingTimer <-
                Some(
                    new Timer(
                        (fun _ ->
                            // a timer thread: an exception here has no
                            // handler above it and ends Visual Studio —
                            // writing to the pipe of an exited sidecar did
                            // exactly that. The client guards its own sends;
                            // this is the last line of defence
                            try
                                sendChange ()
                            with ex ->
                                FsacClient.clientTrace
                                    $"didChange {filePath} FAILED: {ex.GetType().Name}: {ex.Message}"),
                        null,
                        500,
                        Timeout.Infinite
                    )
                ))

    member _.FilePath = filePath

/// F# sources only. The MEF export is bound to the "F#" content type,
/// but a content type is what Visual Studio believes about a buffer, not
/// what the file is: a .cs opened in an F# project, or any buffer some
/// other extension has classified, would otherwise be shipped to the
/// sidecar and analysed as if it were F#.
let private isFSharpSource (path: string) =
    let ext = (Path.GetExtension path).ToLowerInvariant()
    ext = ".fs" || ext = ".fsx" || ext = ".fsi" || ext = ".fsscript"

/// Paths whose contents are not the author's to fix: vendored sources,
/// package caches, and build output. Kept in step with the CLI's
/// defaultIgnoredSegments by hand — this extension targets net48 and
/// cannot reference the analyzers, which are net8.0.
let private ignoredSegments =
    [ "paket-files"; ".paket"; "node_modules"; "packages"; "obj"; "bin" ]

let private isIgnoredPath (path: string) =
    let segments = path.Replace('\\', '/').ToLowerInvariant().Split '/'
    ignoredSegments |> List.exists (fun s -> Array.contains s segments)

/// A generator's marker, in a header or an attribute. Same set the CLI
/// sniffs for; a file FAKE or Myriad rewrites on every build is nobody's
/// to hand-edit.
let private generatedMarkers =
    [
        "<auto-generated"
        "auto-generated"
        "autogenerated"
        "generated by"
        "do not edit"
        "[<GeneratedCode"
        "[<CompilerGenerated"
    ]

let private isGeneratedFile (path: string) =
    try
        File.ReadLines path
        |> Seq.truncate 30
        |> Seq.exists (fun line ->
            generatedMarkers
            |> List.exists (fun m -> line.IndexOf(m, StringComparison.OrdinalIgnoreCase) >= 0))
    with _ ->
        false

/// The CLI has refused these for a while; the editor was still offering
/// fixes on them, which is how a vendored paket-files source came to be
/// rewritten in SQLProvider.
let private isAnalysable (path: string) =
    isFSharpSource path && not (isIgnoredPath path) && not (isGeneratedFile path)

/// One session per buffer, created on demand.
let ensureFor (buffer: ITextBuffer) : BufferSession option =
    match buffer.Properties.TryGetProperty<BufferSession>(typeof<BufferSession>) with
    | true, s -> Some s
    | _ ->
        match buffer.Properties.TryGetProperty<ITextDocument>(typeof<ITextDocument>) with
        | true, doc when not (String.IsNullOrEmpty doc.FilePath) && isAnalysable doc.FilePath ->
            let s = BufferSession(buffer, doc.FilePath)
            buffer.Properties.AddProperty(typeof<BufferSession>, s)
            Some s
        | _ -> None
