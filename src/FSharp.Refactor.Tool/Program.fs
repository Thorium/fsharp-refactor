/// Applies the FSharp.Refactor analyzers' quick fixes from the command line.
///
///     dotnet tool install --global fsharp-refactor
///     fsharp-refactor Your.fsproj
///
/// (from this repository:
/// `dotnet run --project src/FSharp.Refactor.Tool -- Your.fsproj`)
///
/// The stock `fsharp-analyzers` CLI only REPORTS: fixes reach editors and
/// SARIF, never the files. This tool closes that gap:
///
///   1. `dotnet msbuild --getItem:FscCommandLineArgs` yields the exact
///      compiler arguments (no project-cracking library needed)
///   2. every [<CliAnalyzer>] in FSharp.Refactor.Analyzers runs against
///      each source file via reflection — new rules are picked up
///      automatically
///   3. non-overlapping fixes are applied bottom-up per file; because a fix
///      can enable further fixes (or invalidate siblings), analysis re-runs
///      until a pass applies nothing (bounded by --max-passes)
///   4. a final re-check compares the project's error count against the
///      baseline and fails loudly if applying introduced any
///
/// The first bare argument says what to fix, and its kind is read off the
/// path — no flag needed:
///
///     Your.fsproj      one project
///     Thing.fs         one source file: its project is found and analyzed,
///                      but only that file is edited
///     build.fsx        one script; needs no MSBuild at all, so it starts
///                      analysing immediately, and #load'ed files come along
///     Your.sln/.slnx   every F# project the solution lists
///     src/             the solution in that directory, or the projects under it
///     "src/**/*.fsproj"  everything the glob matches
///
/// Options:
///     --project / --script      accepted as aliases; the kind is inferred
///                               from the extension either way
///     --codes FR0002,FR0031    only apply these rule codes
///     --categories correctness only apply rules of these kinds
///     --dry-run                report what would be applied, change nothing
///     --api-changes            also apply CROSS-FILE fixes (rules that
///                              rewrite call sites of internal symbols
///                              across the project); without it those
///                              fixes are held back and counted. Public
///                              symbols are never rewritten: their callers
///                              can live outside the checked project
///     --no-if-defs             never emit #if/#else/#endif pairs for
///                              capability fixes on multi-targeted
///                              projects; fixes stay plain and the final
///                              build check alone decides their fate
///     --report <file>          write every surfaced finding as SARIF
///                              2.1.0 for CI annotation
///     --jobs <n>               files typechecked at once (default 4, capped
///                              by the core count). Trades CPU for wall
///                              clock: FCS reuses each file's prefix within
///                              one incremental build, and parallel checks
///                              give that reuse up, so the gain peaks around
///                              4 and reverses if pushed higher. --jobs 1
///                              restores the sequential sweep
///     --framework <tfm>        analyze against just this target framework.
///                              By default a multi-targeted project is worked
///                              through framework by framework, narrowest
///                              first: each activates its own #if branches,
///                              and code behind another one's is not in the
///                              parse tree at all. Every pass ends by building
///                              all the frameworks, so a fix that suits one
///                              but not the others fails loudly
///     --max-passes <n>         fix-then-reanalyze iterations (default 5)
module FSharp.Refactor.Tool.Program

open System
open System.Diagnostics
open System.IO
open System.Reflection
open System.Text.Json
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Text

// the tests drive the snapshot and process helpers below directly
[<assembly: System.Runtime.CompilerServices.InternalsVisibleTo("FSharp.Refactor.Tests")>]
do ()

/// Colour, when the terminal is actually a terminal.
///
/// A redirected stream is a pipe or a file, where escape codes are
/// corruption rather than decoration; NO_COLOR (no-color.org) is the de
/// facto way to ask for plain text, and TERM=dumb says the same thing.
/// `Console.ForegroundColor` rather than raw ANSI, because .NET already
/// knows how to say this to a legacy Windows console and a VT terminal
/// alike.
///
/// The palette carries PRIORITY, not decoration. A run prints a lot, and
/// someone reading it should be able to find what failed without reading
/// the progress: timings recede, skips are visibly deliberate, failures
/// come forward. Colour is never the only carrier — every line still says
/// in words what it is, because a fair share of readers cannot rely on hue.
module private Out =
    let mutable private forcePlain = false

    /// --no-color, for a terminal that claims colour it cannot show.
    let goPlain () = forcePlain <- true

    let private allowed (redirected: bool) =
        not forcePlain
        && not redirected
        && String.IsNullOrEmpty(Environment.GetEnvironmentVariable "NO_COLOR")
        && Environment.GetEnvironmentVariable "TERM" <> "dumb"

    /// Console colour is PROCESS-GLOBAL, and the sweep's heartbeat prints
    /// from inside Async.Parallel. Two threads interleaving read-previous /
    /// set / restore leave the terminal stuck in whichever colour lost the
    /// race — surviving the run and colouring the user's next prompt. One
    /// gate makes a line atomic; output is serialized for readability
    /// anyway, so it costs nothing worth measuring.
    let private gate = obj ()

    /// Emit exactly once, coloured if we can. Reading or setting the colour
    /// throws on a console that is not one; that costs the colour, never the
    /// message. The previous colour is always put back, so a piece of a line
    /// never leaves its colour hanging over whatever prints next.
    let private coloured
        (stream: IO.TextWriter)
        (redirected: bool)
        (color: ConsoleColor)
        (emit: IO.TextWriter -> unit)
        =
        lock gate (fun () ->
            let restore =
                if allowed redirected then
                    try
                        let previous = Console.ForegroundColor
                        Console.ForegroundColor <- color
                        Some previous
                    with _ -> // not a colour-capable console; fsharpanalyzer: ignore-line FR0055
                        None
                else
                    None

            try
                emit stream
            finally
                match restore with
                | Some previous ->
                    try
                        Console.ForegroundColor <- previous
                    with _ -> // fsharpanalyzer: ignore-line FR0055
                        ()
                | None -> ())

    let private line (stream: IO.TextWriter) redirected color (text: string) =
        coloured stream redirected color (fun s -> s.WriteLine text)

    let private part (stream: IO.TextWriter) redirected color (text: string) =
        coloured stream redirected color (fun s -> s.Write text)

    /// Progress and timing: true, and not what anyone is looking for.
    let dim text =
        line Console.Out Console.IsOutputRedirected ConsoleColor.DarkGray text

    /// A piece of a line that several writes assemble — a progress prefix
    /// printed before the work, completed by the elapsed time after it.
    let dimPart text =
        part Console.Out Console.IsOutputRedirected ConsoleColor.DarkGray text

    /// The same on stderr, where the sweep's heartbeat lives so that piped
    /// stdout stays machine-readable.
    let dimPartErr text =
        part Console.Error Console.IsErrorRedirected ConsoleColor.DarkGray text

    /// Work that landed.
    let good text =
        line Console.Out Console.IsOutputRedirected ConsoleColor.Green text

    /// A standing invitation about the RUN itself rather than about the
    /// code — brighter than the default foreground, so it reads as
    /// addressed to the operator without borrowing a finding's colour.
    let white text =
        line Console.Out Console.IsOutputRedirected ConsoleColor.White text

    /// Deliberately not done — a skip, a hold-back, a stand-down. Not a
    /// failure, and worth being able to tell apart at a glance.
    let skip text =
        line Console.Out Console.IsOutputRedirected ConsoleColor.DarkYellow text

    /// Advice with no fix behind it. Deliberately NOT the skip colour: a
    /// skip says we declined to act, a note asks the reader to — and for a
    /// note-only rule it is the whole output, not an aside.
    let note text =
        line Console.Out Console.IsOutputRedirected ConsoleColor.DarkCyan text

    /// Failure. Stays on stderr, where it already was.
    let bad text =
        line Console.Error Console.IsErrorRedirected ConsoleColor.Red text


type private Options =
    {
        Target: string
        ShowHelp: bool
        /// Print the version and stop. Worth its own flag: several builds
        /// can be installed over a session, and "which one am I running"
        /// should not require reading a nupkg name.
        ShowVersion: bool
        Codes: Set<string> option
        /// The codes the user TYPED in --codes, before any --categories
        /// expansion is folded into `Codes`. Only these outrank a rule's
        /// default-off status or a config disable: naming a rule is an
        /// ask, a category is merely a filter.
        ExplicitCodes: Set<string> option
        /// Narrows `Codes` once parsing is done, so the two flags combine the
        /// same way whichever order they were given in.
        Categories: Set<RuleCatalog.Category> option
        DryRun: bool
        /// Suppress colour even where the terminal supports it. NO_COLOR
        /// and TERM=dumb say the same thing; this is the flag form.
        NoColor: bool
        ApiChanges: bool
        /// Suppresses dual-framework #if pair emission: capability fixes
        /// stay plain everywhere, and the all-frameworks build check alone
        /// decides whether they survive on a legacy-targeting project.
        NoIfDefs: bool
        /// SARIF 2.1.0 output file: every finding the run surfaced, for CI
        /// annotation. Pairs naturally with --dry-run.
        Report: string option
        /// No MSBuild, no reference resolution: sources are read straight
        /// from the fsproj and only the analyzers that never consult the
        /// typechecker run. For codebases that cannot compile on this
        /// machine (a type provider needing its database, say).
        ParseOnly: bool
        /// A previous run's SARIF: findings whose fingerprints appear in it
        /// are neither reported nor fixed — the ratchet for agents and CI.
        Baseline: string option
        /// Exit 3 when the run surfaced any finding (after baseline
        /// filtering) — the hard lint gate.
        FailOnFindings: bool
        /// Honor every suppression comment regardless of the config's
        /// "suppressions" policy — the CI override.
        HonorSuppressions: bool
        /// List fix-less advisory notes inline instead of the one-line
        /// per-category summary.
        Notes: bool
        /// --notes only: report the fix-less findings alone; nothing is applied.
        NotesOnly: bool
        /// Machine-readable stdout: prose moves to stderr, and the run's
        /// findings leave as one JSON document on stdout.
        Json: bool
        /// Print the rule catalog and exit.
        ListRules: bool
        /// Write a fsharprefactor.json of this build's defaults and exit.
        /// Never overwrites: an existing config is someone's decisions.
        CreateConfig: bool
        /// Serve analyze/list_rules over MCP (JSON-RPC on stdio).
        Mcp: bool
        MaxPasses: int
        Jobs: int
        /// Overrides the automatic narrowest-framework choice, so the code
        /// behind another framework's #if can be reached.
        Framework: string
    }

let private helpText =
    """fsharp-refactor — applies F# refactoring quick fixes to your code.

USAGE
  fsharp-refactor <what> [options]

WHAT TO FIX — the kind is read off the path, no flag needed:
  Your.fsproj           one project
  Thing.fs              one source file; its project is found and analysed,
                        but only that file is edited
  build.fsx             one script; no MSBuild step at all, so it starts at once
  Your.sln, Your.slnx   every F# project the solution lists
  src/                  the solution in that directory, or the projects beneath
  "src/**/*.fsproj"     everything the glob matches

OPTIONS
  --dry-run             report every fix, change nothing. Rewriting is never
                        implicit: without this it edits, with it it does not
  --codes FR0002,FR0031 only these rules
  --categories <list>   only rules of these kinds: correctness, performance,
                        idiom, cosmetic. Combined with --codes it narrows
                        further. For a repository you do not maintain,
                        "correctness,performance" is the set worth a pull
                        request; nobody welcomes a stranger's punctuation
  --jobs <n>            files typechecked at once (default 4, clamped to 2-4 by
                        core count). --jobs 1 is the sequential sweep
  --framework <tfm>     analyse only this target framework. By default a
                        multi-targeted project is worked through framework by
                        framework, narrowest first, because code behind another
                        framework's #if is not in the parse tree at all
  --api-changes         also apply cross-file fixes that change internal
                        signatures, rewriting call sites project-wide. Held
                        back and merely counted without this. Public
                        signatures are never rewritten: their callers can
                        live outside the checked project
  --no-color            plain output, even on a colour-capable terminal.
                        NO_COLOR=1 and TERM=dumb do the same, and a piped or
                        redirected stream is never coloured either way
  --no-if-defs          never emit #if/#else/#endif pairs for capability
                        fixes on multi-targeted projects. The fixes stay
                        plain, and any that break a legacy framework are
                        simply put back by the final build check
  --report <file>       write every finding to a file: .sarif (SARIF 2.1.0,
                        what CI turns into inline annotations), .html (a
                        self-contained page) or .csv. Pairs with --dry-run
  --parse-only          no MSBuild, no reference resolution: sources come
                        straight from the fsproj and only the 55 of 113
                        analyzers that never consult the typechecker run.
                        NOT a substitute for a real run: what survives is
                        skewed the wrong way — roughly a quarter of the
                        correctness rules and a quarter of the performance
                        ones, against three quarters of the cosmetic. A
                        clean --parse-only says little about a codebase.
                        For projects that cannot compile here at all (a
                        type provider whose database is down, references
                        that will not restore); #if branches are also out
                        of reach
  --baseline <sarif>    findings whose fingerprints appear in this earlier
                        report are neither reported nor fixed: the ratchet.
                        Triage once, then only NEW findings surface
  --fail-on-findings    exit 3 when any finding survives the filters — the
                        hard CI gate (0 clean, 1 failure, 2 usage)
  --honor-suppressions  honor every suppression comment regardless of the
                        config's "suppressions" policy — the CI override
                        for a repo that wants comments inert locally
  --notes [on|off|only] on (the bare flag) lists fix-less advisory notes
                        inline; only lists nothing but them. By default a
                        run prints its FIXES and ends with one per-category
                        note count; SARIF (--report) and --format json
                        always carry the notes in full
  --notes only          a review pass: every rule runs, only the findings
                        without a fix are listed (inline), nothing is
                        written. Combine with --report for a notes file
  --format json         machine-readable stdout: progress prose moves to
                        stderr and the findings leave as one JSON document.
                        The default stays human-readable
  --rules               print the rule catalog (honors --format json)
  --create-config       write a fsharprefactor.json of this build's defaults
                        (every rule, every run-level key, one comment each)
                        into the current directory, or into <what> when that
                        is a directory. Never overwrites an existing one
  --mcp                 serve analyze/list_rules as an MCP server over
                        stdio, keeping the typechecker warm between calls
  --max-passes <n>      fix-then-reanalyse iterations (default 5)
  --version, -v         print the version being invoked and stop
  --help, -h, /?        this text

A run refuses a compilation that already has errors, and fails loudly if
applying introduces one. For a multi-targeted project every framework is built
before it reports success.

Rules can be turned off per repository with a fsharprefactor.json.
Full documentation: https://github.com/Thorium/fsharp-refactor"""

[<TailCall>]
let rec private parseArgsLoop opts args =
    match args with
    | [] -> Ok opts
    // --project and --script still work, but the kind is inferred from the
    // extension either way, so a bare path is enough
    | "--project" :: path :: rest
    | "--script" :: path :: rest -> parseArgsLoop { opts with Target = path } rest
    | "--codes" :: codes :: rest ->
        // codes are spelled upper case in the catalogue; accepting either
        // costs nothing and a lower-case code used to match nothing at all
        let parsed =
            codes.Split ','
            |> Array.map (fun c -> c.Trim().ToUpperInvariant())
            |> Array.filter (fun c -> c <> "")
            |> Set.ofArray

        // an unrecognised code is otherwise pure silence: `--codes FR013`,
        // one digit short, sweeps the whole project, matches nothing, and
        // reports zero findings as though the code were clean
        match parsed |> Set.filter (RuleCatalog.known.Contains >> not) |> Set.toList with
        | [] ->
            parseArgsLoop
                { opts with
                    Codes = Some parsed
                    ExplicitCodes = Some parsed }
                rest
        | unknown ->
            let listed = String.concat ", " unknown
            Error $"not a rule code: {listed}. --rules lists every code."
    | "--categories" :: names :: rest ->
        let parsed = names.Split(',') |> Array.map RuleCatalog.parse

        match parsed |> Array.tryFindIndex Option.isNone with
        | Some bad ->
            let known = RuleCatalog.all |> List.map RuleCatalog.name |> String.concat ", "
            Error $"'{names.Split(',').[bad].Trim()}' is not a category. Known categories: {known}."
        | None ->
            parseArgsLoop
                { opts with
                    Categories = Some(parsed |> Array.choose id |> Set.ofArray) }
                rest
    | "--help" :: _
    | "-h" :: _
    | "/?" :: _
    | "-?" :: _ -> Ok { opts with ShowHelp = true }
    | "--version" :: _
    | "-v" :: _ -> Ok { opts with ShowVersion = true }
    | "--dry-run" :: rest -> parseArgsLoop { opts with DryRun = true } rest
    | "--no-color" :: rest -> parseArgsLoop { opts with NoColor = true } rest
    | "--api-changes" :: rest -> parseArgsLoop { opts with ApiChanges = true } rest
    | "--no-if-defs" :: rest -> parseArgsLoop { opts with NoIfDefs = true } rest
    | "--report" :: file :: rest -> parseArgsLoop { opts with Report = Some file } rest
    | "--parse-only" :: rest -> parseArgsLoop { opts with ParseOnly = true } rest
    | "--baseline" :: file :: rest -> parseArgsLoop { opts with Baseline = Some file } rest
    | "--fail-on-findings" :: rest -> parseArgsLoop { opts with FailOnFindings = true } rest
    | "--honor-suppressions" :: rest -> parseArgsLoop { opts with HonorSuppressions = true } rest
    // --notes on|off|only: on lists the notes inline, only lists nothing
    // but them, off is the default; a bare --notes is on
    | "--notes" :: ("off" | "on" | "only" as mode) :: rest ->
        match mode with
        | "off" ->
            parseArgsLoop
                { opts with
                    Notes = false
                    NotesOnly = false }
                rest
        | "on" -> parseArgsLoop { opts with Notes = true } rest
        | _ ->
            parseArgsLoop
                { opts with
                    NotesOnly = true
                    Notes = true
                    DryRun = true }
                rest
    | "--notes" :: rest -> parseArgsLoop { opts with Notes = true } rest
    | "--format" :: "json" :: rest -> parseArgsLoop { opts with Json = true } rest
    | "--format" :: other :: _ -> Error $"--format knows 'json' (the default output is human-readable); got '{other}'"
    | "--rules" :: rest -> parseArgsLoop { opts with ListRules = true } rest
    | "--create-config" :: rest -> parseArgsLoop { opts with CreateConfig = true } rest
    | "--mcp" :: rest -> parseArgsLoop { opts with Mcp = true } rest
    | "--framework" :: tfm :: rest -> parseArgsLoop { opts with Framework = tfm } rest
    | "--jobs" :: n :: rest ->
        match Int32.TryParse n with
        | true, jobs when jobs > 0 -> parseArgsLoop { opts with Jobs = jobs } rest
        | _ -> Error $"--jobs needs a positive number, got '{n}'"
    | "--max-passes" :: n :: rest ->
        match Int32.TryParse n with
        | true, passes when passes > 0 -> parseArgsLoop { opts with MaxPasses = passes } rest
        | _ -> Error $"--max-passes needs a positive number, got '{n}'"
    // a bare path: the common case, no flag needed
    | path :: rest when not (path.StartsWith '-') && opts.Target = "" -> parseArgsLoop { opts with Target = path } rest
    // a SECOND bare path is not an unknown argument, it is one target too
    // many — saying "unknown" sends the reader hunting for a typo
    | extra :: _ when not (extra.StartsWith '-') -> Error $"'{extra}' is a second target; one target per run"
    // a value-taking flag given without its value would otherwise fall into
    // the catch-all below and be reported as UNKNOWN, sending the reader off
    // to hunt for a typo in a flag they spelled correctly
    | [ flag ] when
        [ "--report"
          "--baseline"
          "--format"
          "--framework"
          "--jobs"
          "--max-passes"
          "--codes"
          "--categories" ]
        |> List.contains flag
        ->
        Error $"'{flag}' needs a value after it"
    | unknown :: _ -> Error $"Unknown argument '{unknown}'"

/// Fold `--categories` into `--codes`. Doing it here rather than in the loop
/// keeps the two flags order-independent, and leaves one code filter for the
/// rest of the tool to consult.
let private applyCategories (opts: Options) =
    match opts.Categories with
    | None -> opts
    | Some wanted ->
        let fromCategories = RuleCatalog.codesIn wanted

        let combined =
            opts.Codes
            |> Option.map (fun explicitCodes -> Set.intersect explicitCodes fromCategories)
            |> Option.defaultValue fromCategories

        { opts with Codes = Some combined }

let private parseArgs (argv: string[]) =
    parseArgsLoop
        { Target = ""
          ShowHelp = false
          ShowVersion = false
          Codes = None
          ExplicitCodes = None
          Categories = None
          DryRun = false
          NoColor = false
          ApiChanges = false
          NoIfDefs = false
          Report = None
          ParseOnly = false
          Baseline = None
          FailOnFindings = false
          HonorSuppressions = false
          Notes = false
          NotesOnly = false
          Json = false
          ListRules = false
          CreateConfig = false
          Mcp = false
          MaxPasses = 5
          // Measured sweet spot. FCS reuses each file's prefix within one
          // incremental build, so parallel checks buy wall clock by giving
          // that reuse up: on a 113-file project the sweep runs 70 s at one
          // job, 53 s at four, and back up to 61 s at eleven. Clamped to
          // 2..4 — a small machine is not oversubscribed, and even a
          // single-core one still overlaps a check with an analyzer pass.
          Jobs = min 4 (max 2 Environment.ProcessorCount)
          Framework = "" }
        (List.ofArray argv)
    |> Result.map applyCategories

/// No child process gets to hang the tool.
///
/// Three ways that happens, and all three have. Draining one pipe to
/// completion before the other deadlocks as soon as the child fills the one
/// nobody is reading. An inherited stdin lets a child that decides to prompt
/// — NuGet asking for feed credentials is the usual one — wait forever on a
/// console that may not even be attached. And a child that simply never
/// finishes takes us with it, silently, which is the worst of the three
/// because there is nothing on screen to explain it.
let internal runProcessIn (workingDirectory: string option) (timeout: TimeSpan) (fileName: string) (arguments: string) =
    let psi =
        ProcessStartInfo(
            FileName = fileName,
            Arguments = arguments,
            RedirectStandardInput = true,
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false
        )

    workingDirectory |> Option.iter (fun dir -> psi.WorkingDirectory <- dir)

    // A child that cannot START is the fourth way: a blocked or missing
    // executable (a paket bootstrapper under application control, `mono`
    // absent, `dotnet` not on the PATH) throws out of Process.Start, and
    // that unwound the whole sweep from one checkout's restore. Reported
    // the way a failed exit is, so the caller skips that target and the
    // run goes on.
    let started =
        try
            Ok(Process.Start psi)
        with
        | :? System.ComponentModel.Win32Exception
        | :? IOException
        | :? UnauthorizedAccessException as e -> Error e.Message

    match started with
    | Error message -> -1, "", $"'{fileName}' could not be started: {message}"
    | Ok p ->

        use p = p

        // a prompt now reads end-of-input and gives up, instead of waiting
        p.StandardInput.Close()

        // Both pipes drain on their own callbacks. .NET raises each stream's
        // event in order, so a builder is never written from two threads at
        // once, and nothing here blocks on a task the child has to finish
        // first — which is what made reading one pipe then the other deadlock.
        let outText = Text.StringBuilder()
        let errText = Text.StringBuilder()

        p.OutputDataReceived.Add(fun e ->
            if not (isNull e.Data) then
                outText.AppendLine e.Data |> ignore)

        p.ErrorDataReceived.Add(fun e ->
            if not (isNull e.Data) then
                errText.AppendLine e.Data |> ignore)

        p.BeginOutputReadLine()
        p.BeginErrorReadLine()

        if p.WaitForExit(int timeout.TotalMilliseconds) then
            // the timed overload can return before the output callbacks have
            // flushed; the argument-less one waits for them
            p.WaitForExit()
            p.ExitCode, outText.ToString(), errText.ToString()
        else
            try
                // the whole tree: MSBuild leaves worker nodes behind
                p.Kill true
            with
            | :? InvalidOperationException
            | :? NotSupportedException
            | :? System.ComponentModel.Win32Exception -> ()

            let minutes = timeout.TotalMinutes

            -1, "", $"'{fileName} {arguments}' had not finished after {minutes} minutes, so it was stopped."

/// Long enough for a real build of a large project, short enough that a
/// stuck one is reported rather than waited on forever.
let private processTimeout = TimeSpan.FromMinutes 15.0

let private runProcess (timeout: TimeSpan) (fileName: string) (arguments: string) =
    runProcessIn None timeout fileName arguments

/// The files among `files` that git ignores, by full lower-cased path.
/// A compilation includes what its project lists, and a project may list
/// vendored or generated code that lives outside version control:
/// fantomas compiles a git-ignored `.deps/<sha>/src/Compiler/**` and its
/// fslex output under a git-ignored `generated/`. Editing those is churn
/// nobody can commit, and their notes (70 of fantomas's 105) drown the
/// ones on maintained code. Asked of git once per project over stdin —
/// the file list is far too long for a command line. No git, no
/// repository, or an error: nothing is ignored.
let private gitIgnoredFiles (projectDir: string) (files: string[]) : Set<string> =
    if files.Length = 0 then
        Set.empty
    else
        try
            let psi =
                ProcessStartInfo(
                    FileName = "git",
                    // -z: NUL-separated in and out, so a Windows path
                    // comes back verbatim rather than C-quoted
                    Arguments = "check-ignore --stdin -z",
                    WorkingDirectory = projectDir,
                    RedirectStandardInput = true,
                    RedirectStandardOutput = true,
                    RedirectStandardError = true,
                    UseShellExecute = false
                )

            use p = Process.Start psi
            let outText = Text.StringBuilder()

            p.OutputDataReceived.Add(fun e ->
                if not (isNull e.Data) then
                    outText.AppendLine e.Data |> ignore)

            p.ErrorDataReceived.Add(fun _ -> ())
            p.BeginOutputReadLine()
            p.BeginErrorReadLine()

            for f in files do
                p.StandardInput.Write(Path.GetFullPath f)
                p.StandardInput.Write '\000'

            p.StandardInput.Close()

            if p.WaitForExit(30_000) then
                p.WaitForExit()

                // 0: some ignored (listed); 1: none; 128: not a repository
                if p.ExitCode = 0 then
                    outText.ToString().Split([| '\000'; '\r'; '\n' |], StringSplitOptions.RemoveEmptyEntries)
                    |> Seq.map (fun l -> Path.GetFullPath(l.Trim()).ToLowerInvariant())
                    |> Set.ofSeq
                else
                    Set.empty
            else
                (try
                    p.Kill true
                 with _ ->
                     ()) // fsharpanalyzer: ignore-line FR0055

                Set.empty
        with _ -> // no git on this machine is not an error; fsharpanalyzer: ignore-line FR0055
            Set.empty

/// The sources of a compilation the run may EDIT: the project's files less
/// the vendored and generated ones above (ignored paths, git-ignored) -
/// the same partition the sweep makes, asked here by the api pass so that
/// a paket-files source is neither reshaped nor, when seventeen projects
/// compile it, the reason all seventeen are read as linkers of each other.
let private editableSources (options: FSharpProjectOptions) : string[] =
    let gitIgnored =
        gitIgnoredFiles (Path.GetDirectoryName options.ProjectFileName) options.SourceFiles

    options.SourceFiles
    |> Array.filter (fun f ->
        not (Configuration.isIgnoredPath f)
        && not (gitIgnored.Contains(Path.GetFullPath(f).ToLowerInvariant())))

/// Where a project's builds run from, decided once per project.
///
/// `dotnet` resolves global.json from its CURRENT directory upward, never
/// from the project's own folder — so a build launched from wherever the
/// user happened to stand ignored the repository's SDK pin, and a build
/// launched from a different place could verify a fix against a different
/// SDK. Builds now run from the project's directory, as the repository's
/// own build would.
///
/// Where the pinned SDK is not installed at all — Fable pins 10.0.100 with
/// latestPatch on a machine carrying only 10.0.302 — that build cannot run,
/// and the pass would analyse nothing. The build then falls back to a
/// neutral directory, outside any global.json, and says so: analysed with
/// the SDK `dotnet` resolves there, which is what a hand-run from above the
/// repository has always done, but now out loud rather than by accident.
let private buildDirectories =
    System.Collections.Generic.Dictionary<string, string option>()

let private sdkPinUnsatisfied (stdout: string) (stderr: string) =
    let text = stdout + stderr

    text.Contains "A compatible .NET SDK was not found"
    || text.Contains "compatible installed .NET SDK for global.json"

let private runForProject (project: string) (timeout: TimeSpan) (fileName: string) (arguments: string) =
    let key = Path.GetFullPath(project).ToLowerInvariant()

    match buildDirectories.TryGetValue key with
    | true, dir -> runProcessIn dir timeout fileName arguments
    | _ ->
        let projectDir = Path.GetDirectoryName(Path.GetFullPath project)
        let exit, stdout, stderr = runProcessIn (Some projectDir) timeout fileName arguments

        if exit <> 0 && sdkPinUnsatisfied stdout stderr then
            let neutral = Path.GetTempPath()

            let pin =
                let m =
                    Text.RegularExpressions.Regex.Match(stdout + stderr, @"Requested SDK version: ([^\r\n]+)")

                if m.Success then m.Groups.[1].Value.Trim() else "an SDK"

            Out.skip
                $"  (global.json pins {pin}, which is not installed — analysed with the SDK dotnet resolves outside the repository; install it or relax rollForward to verify against the pin)"

            buildDirectories.[key] <- Some neutral
            runProcessIn (Some neutral) timeout fileName arguments
        else
            buildDirectories.[key] <- Some projectDir
            exit, stdout, stderr

/// Visual Studio's MSBuild.exe, for old-style (non-SDK) projects whose
/// imports only evaluate under it. Located via vswhere.
let private vsMsBuildPath =
    lazy
        (try
            let vswhere =
                Path.Combine(
                    Environment.GetFolderPath Environment.SpecialFolder.ProgramFilesX86,
                    "Microsoft Visual Studio",
                    "Installer",
                    "vswhere.exe"
                )

            if File.Exists vswhere then
                let _, out, _ =
                    runProcess
                        (TimeSpan.FromMinutes 1.0)
                        vswhere
                        "-latest -requires Microsoft.Component.MSBuild -find MSBuild\\**\\Bin\\MSBuild.exe"

                out.Split('\n') |> Array.map _.Trim() |> Array.tryFind File.Exists
            else
                None
         // no Visual Studio here, or it refused to answer: old-style
         // projects then fall back to the SDK's msbuild
         with
         | :? System.ComponentModel.Win32Exception
         | :? InvalidOperationException
         | :? IOException
         | :? UnauthorizedAccessException -> None)

/// How narrow a target framework's API surface is; lower sorts first.
///
/// netstandard is the smallest common denominator, then .NET Framework,
/// then .NET Core, then modern .NET by version. Within a family the lower
/// version is narrower, so netstandard2.0 sorts ahead of netstandard2.1.
/// Framework monikers have no dot (net48, net481) where modern ones do
/// (net8.0, net10.0), which is what separates the two.
let private tfmRank (tfm: string) =
    // the OS suffix's digits would swamp the version: net8.0-windows10.0.19041.0
    // must rank as net8.0, not overflow Int32 and sort before net6.0
    let t = (tfm.ToLowerInvariant().Split '-').[0]
    let digits = String(t |> Seq.filter Char.IsDigit |> Seq.toArray)

    let version =
        match Int32.TryParse digits with
        | true, v -> v
        | false, _ -> 0

    if t.StartsWith "netstandard" then 0, version
    elif t.StartsWith "netcoreapp" then 2, version
    elif t.StartsWith "net" && t.Contains '.' then 3, version
    else 1, version

/// The frameworks a project lists, narrowest first. A plain
/// `<TargetFrameworks>a;b</TargetFrameworks>` is read off the text. One
/// under a Condition, or built from a property — the F# compiler's own
/// FSharp.Core lists `netstandard2.0;netstandard2.1;$(FSharpCoreShippedNetTargetFramework)`
/// behind `'$(Configuration)' != 'Proto'` — only MSBuild can evaluate, so
/// the text says "multi-targeted" and MSBuild says which. Read off the text
/// alone, that project looked single-targeted, its outer build was queried
/// for compiler arguments, and the outer build of a multi-targeted project
/// never runs CoreCompile: "no FscCommandLineArgs". Cached per project: the
/// evaluation costs seconds.
let private listedFrameworks =
    System.Collections.Concurrent.ConcurrentDictionary<string, string list>()

let private targetFrameworksOf (projectPath: string) : string list =
    listedFrameworks.GetOrAdd(
        Path.GetFullPath projectPath,
        fun path ->
            let text =
                try
                    File.ReadAllText path
                with
                | :? IOException
                | :? UnauthorizedAccessException -> ""

            // a moniker and nothing else: MSBuild's property output can carry
            // a warning line, which must not become a framework name
            let split (listed: string) =
                listed.Split ';'
                |> Array.map _.Trim()
                |> Array.filter (fun tfm ->
                    tfm <> ""
                    && Text.RegularExpressions.Regex.IsMatch(tfm, @"^[A-Za-z][A-Za-z0-9.\-+]*$"))
                |> Array.sortBy tfmRank
                |> List.ofArray

            let m =
                Text.RegularExpressions.Regex.Match(text, "<TargetFrameworks>([^<]+)</TargetFrameworks>")

            // a second, conditioned element (the compiler project adds
            // net10.0 to netstandard2.0 outside official builds) makes the
            // plain one only part of the answer
            let conditioned =
                Text.RegularExpressions.Regex.IsMatch(text, "<TargetFrameworks\\s+[^>]*Condition")

            if m.Success && not conditioned && not (m.Groups.[1].Value.Contains "$(") then
                split m.Groups.[1].Value
            elif text.Contains "<TargetFrameworks" && text.Contains "Sdk=" then
                let _, out, _ =
                    runForProject
                        path
                        (TimeSpan.FromMinutes 2.)
                        "dotnet"
                        $"msbuild \"{path}\" --getProperty:TargetFrameworks"

                // the value is the LAST line; anything before it is chatter
                out.Split('\n')
                |> Array.map _.Trim()
                |> Array.filter (fun l -> l <> "")
                |> Array.tryLast
                |> Option.map split
                |> Option.defaultValue []
            else
                []
    )

/// The project's fsc arguments, straight from MSBuild. SDK-style projects
/// go through `dotnet`; old-style (net48-era) projects need Visual
/// Studio's MSBuild, whose imports do not evaluate under the SDK's.
/// --parse-only's argument source: the fsproj text itself, no MSBuild.
/// Compile items in order plus whatever DefineConstants can be read
/// literally — conditions and $() are beyond a textual read and are
/// simply skipped, so `#if` branches behind them stay out of the parse
/// (documented limitation of the mode).
// compiled once: these run per project (and the whitespace collapser per
// FINDING), and FR0015 rightly flagged the re-parsed patterns — dogfood
let private propertyGroupRegex =
    Text.RegularExpressions.Regex(
        "<PropertyGroup([^>]*)>((?s:.*?))</PropertyGroup>",
        Text.RegularExpressions.RegexOptions.Compiled
    )

let private conditionAttributeRegex =
    Text.RegularExpressions.Regex("Condition\\s*=\\s*\"([^\"]*)\"", Text.RegularExpressions.RegexOptions.Compiled)

let private defineElementRegex =
    Text.RegularExpressions.Regex(
        "<DefineConstants([^>]*)>([^<]*)</DefineConstants>",
        Text.RegularExpressions.RegexOptions.Compiled
    )

let private whitespaceRunRegex =
    Text.RegularExpressions.Regex(@"\s+", Text.RegularExpressions.RegexOptions.Compiled)

let private compileItemRegex =
    Text.RegularExpressions.Regex("<Compile\\s+Include=\"([^\"]+)\"", Text.RegularExpressions.RegexOptions.Compiled)

/// A PropertyGroup carrying a Condition — usually `'$(TargetFramework)'
/// == 'net8.0'`. Its constants belong to ONE framework, and --parse-only
/// picks no framework at all, so taking them would activate `#if`
/// branches for a compilation that is no framework in particular:
/// SQLProvider defines NETSTANDARD21 only for net6/8/10 and
/// netstandard2.1, and reading it unconditionally hides the branch every
/// other target actually compiles. The README already promised these are
/// not parsed; now they are not.
let private conditionalPropertyGroupRegex =
    Text.RegularExpressions.Regex(
        "<PropertyGroup[^>]*\\sCondition\\s*=[^>]*>.*?</PropertyGroup>",
        Text.RegularExpressions.RegexOptions.Compiled
        ||| Text.RegularExpressions.RegexOptions.Singleline
        ||| Text.RegularExpressions.RegexOptions.IgnoreCase
    )

let private defineConstantsElementRegex =
    Text.RegularExpressions.Regex(
        "<DefineConstants[^>]*>([^<]*)</DefineConstants>",
        Text.RegularExpressions.RegexOptions.Compiled
    )

let private parseOnlyArgs (projectPath: string) =
    let projectText =
        try
            File.ReadAllText projectPath
        with
        | :? IOException
        | :? UnauthorizedAccessException -> ""

    let projectDir = Path.GetDirectoryName(Path.GetFullPath projectPath)

    // <Compile Include> is read verbatim, so an item carrying an
    // unexpanded MSBuild property ($(SourcesRoot)\X.fs) or pointing at a
    // file that is not on disk yet (mid-development trees, generated
    // sources) must be SKIPPED, not crash the sweep files later
    let sources, dropped =
        [| for m in compileItemRegex.Matches projectText -> m.Groups.[1].Value |]
        |> Array.filter (fun s -> not (s.Contains '*'))
        |> Array.partition (fun s ->
            not (s.Contains "$(")
            && (try
                    File.Exists(Path.Combine(projectDir, s.Replace('\\', Path.DirectorySeparatorChar)))
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    false))

    if dropped.Length > 0 then
        eprintfn
            $"  ({dropped.Length} <Compile Include> item(s) skipped: unexpanded MSBuild properties or files not on disk)"

    if sources.Length = 0 then
        Error "no <Compile Include> items to parse (wildcards and imported items are beyond --parse-only)"
    else
        // framework-conditional groups are blanked first, so only the
        // constants that hold for EVERY target survive
        let unconditionalText = conditionalPropertyGroupRegex.Replace(projectText, "")

        let defines =
            [| for m in defineConstantsElementRegex.Matches unconditionalText do
                   for piece in m.Groups.[1].Value.Split ';' do
                       let piece = piece.Trim()

                       if piece <> "" && not (piece.Contains "$(") then
                           $"--define:{piece}" |]
            |> Array.distinct

        Ok(Array.append defines sources)

/// A repository cloned and never built: paket declared, its restore targets
/// missing, and every project failing with "Paket.Restore.targets was not
/// found". Mended here, once per root, with the restores the repository
/// itself documents (dotnet tool restore, dotnet paket restore) — unless a
/// global.json pins an SDK this machine lacks, when those commands cannot
/// run either and the person is told what to run after installing it.
let private preparedRoots =
    System.Collections.Concurrent.ConcurrentDictionary<string, bool>()

/// A repository that ships its own .NET — global.json's `sdk.paths` naming
/// a directory beside it (the F# compiler's `.dotnet`, Arcade repositories
/// in general) — builds only with that .NET on DOTNET_ROOT. MSBuild finds
/// the SDK through global.json, but the compiler it then runs is an apphost
/// that resolves its runtime through DOTNET_ROOT alone, and exits with the
/// host's framework-missing code (0x80008096, "fsc.exe exited with code
/// -2147450730") when the runtime lives only in that directory. The
/// repository's own build script sets the variable; so does this, once per
/// directory, for every process started from here.
let private privateSdks =
    System.Collections.Concurrent.ConcurrentDictionary<string, bool>()

let private ensurePrivateSdk (projectPath: string) =
    let rec findGlobalJson (dir: DirectoryInfo) =
        if isNull dir then
            None
        else
            let candidate = Path.Combine(dir.FullName, "global.json")

            if File.Exists candidate then
                Some candidate
            else
                findGlobalJson dir.Parent

    let dotnetDirOf (globalJson: string) =
        try
            use doc = JsonDocument.Parse(File.ReadAllText globalJson)
            let mutable sdk = Unchecked.defaultof<JsonElement>
            let mutable paths = Unchecked.defaultof<JsonElement>

            if
                doc.RootElement.TryGetProperty("sdk", &sdk)
                && sdk.TryGetProperty("paths", &paths)
                && paths.ValueKind = JsonValueKind.Array
            then
                paths.EnumerateArray()
                |> Seq.choose (fun p ->
                    if p.ValueKind = JsonValueKind.String then
                        Some(p.GetString())
                    else
                        None)
                // "$host$" is the dotnet running this, not a directory
                |> Seq.filter (fun p -> not (p.StartsWith "$"))
                |> Seq.map (fun p -> Path.GetFullPath(Path.Combine(Path.GetDirectoryName globalJson, p)))
                |> Seq.tryFind (fun dir ->
                    File.Exists(Path.Combine(dir, "dotnet.exe"))
                    || File.Exists(Path.Combine(dir, "dotnet")))
            else
                None
        with
        | :? JsonException
        | :? IOException
        | :? UnauthorizedAccessException -> None

    match
        findGlobalJson (DirectoryInfo(Path.GetDirectoryName(Path.GetFullPath projectPath)))
        |> Option.bind dotnetDirOf
    with
    | Some dir ->
        privateSdks.GetOrAdd(
            dir,
            fun _ ->
                let current = Environment.GetEnvironmentVariable "DOTNET_ROOT"

                let already =
                    not (String.IsNullOrEmpty current)
                    && String.Equals(
                        Path.GetFullPath(current).TrimEnd(Path.DirectorySeparatorChar),
                        dir.TrimEnd(Path.DirectorySeparatorChar),
                        StringComparison.OrdinalIgnoreCase
                    )

                if not already then
                    Environment.SetEnvironmentVariable("DOTNET_ROOT", dir)

                    Environment.SetEnvironmentVariable(
                        "PATH",
                        dir + string Path.PathSeparator + Environment.GetEnvironmentVariable "PATH"
                    )

                    printfn
                        $"  global.json points at the repository's own .NET in {dir}: builds run with it on DOTNET_ROOT"

                true
        )
        |> ignore
    | None -> ()

let private ensureRestorable (projectPath: string) =
    let rec findRoot (dir: DirectoryInfo) =
        if isNull dir then
            None
        elif File.Exists(Path.Combine(dir.FullName, "paket.dependencies")) then
            Some dir.FullName
        else
            findRoot dir.Parent

    match findRoot (DirectoryInfo(Path.GetDirectoryName projectPath)) with
    | Some root ->
        preparedRoots.GetOrAdd(
            root,
            fun _ ->
                let modernTargets =
                    File.Exists(Path.Combine(root, ".paket", "Paket.Restore.targets"))

                let manifest = File.Exists(Path.Combine(root, ".config", "dotnet-tools.json"))
                let bootstrapper = Path.Combine(root, ".paket", "paket.bootstrapper.exe")
                let legacyExe = Path.Combine(root, ".paket", "paket.exe")
                // the pre-tool layout (Chessie, FsXaml, FSharp.CloudAgent): the
                // bootstrapper downloads paket.exe beside itself, and the
                // projects' paket.targets then call that exe. Judged by that
                // legacy targets file, not by the modern one's absence: a
                // restore by a newer paket leaves Paket.Restore.targets behind
                // while the projects still call the exe
                let legacy =
                    File.Exists bootstrapper
                    && (File.Exists(Path.Combine(root, ".paket", "paket.targets")) || not modernTargets)

                // (executable, arguments, what to call it) in order
                let steps =
                    [
                      // the local-tool manifest is what makes `dotnet paket`
                      // exist — needed even when Paket.Restore.targets is in
                      // place (suave: every project's restore failed without it)
                      if manifest then
                          "dotnet", "tool restore", "dotnet tool restore"
                      if legacy then
                          if not (File.Exists legacyExe) then
                              bootstrapper, "", ".paket/paket.bootstrapper.exe"

                          legacyExe, "restore", ".paket/paket.exe restore"
                      elif not modernTargets then
                          "dotnet", "paket restore", "dotnet paket restore" ]

                if not steps.IsEmpty then
                    let sdkCode, sdkOut, sdkErr =
                        runProcessIn (Some root) (TimeSpan.FromMinutes 1.) "dotnet" "--version"

                    if sdkCode <> 0 && sdkPinUnsatisfied sdkOut sdkErr then
                        printfn
                            $"  paket.dependencies in {root}, and its global.json pins an SDK not installed here: after installing it, run `dotnet tool restore` and `dotnet paket restore` there"
                    else
                        printfn $"  paket.dependencies in {root} — running the restores the repository documents"

                        for exe, args, label in steps do
                            // a Windows executable needs mono elsewhere
                            let exe, args =
                                if exe.EndsWith ".exe" && not (OperatingSystem.IsWindows()) then
                                    "mono", $"\"{exe}\" {args}"
                                else
                                    exe, args

                            let code, out, err = runProcessIn (Some root) (TimeSpan.FromMinutes 10.) exe args

                            if code <> 0 then
                                let text = (err + out).Trim()
                                eprintfn $"  ({label} failed: {text.Substring(0, min 300 text.Length)})"
                            else
                                printfn $"  {label}: done"

                true
        )
        |> ignore
    | None -> ()

let private fscArgs (chosenFramework: string) (projectPath: string) =
    // msbuild runs from the project's own directory (its global.json), so a
    // path given relative to the caller's directory must become absolute
    let projectPath = Path.GetFullPath projectPath
    ensurePrivateSdk projectPath
    ensureRestorable projectPath

    let projectText =
        try
            File.ReadAllText projectPath
        with
        | :? IOException
        | :? UnauthorizedAccessException -> ""

    let isSdkStyle = projectText.Contains "Sdk="

    // an .fsproj is not necessarily an F# compilation: SQL database
    // projects (MSBuild.Sdk.SqlProj, OutputType Database, dacpac output)
    // wear the extension too. Recognize them BEFORE paying for a
    // design-time build that can only end in "no FscCommandLineArgs"
    let isDatabaseProject =
        projectText.Contains "MSBuild.Sdk.SqlProj"
        || Text.RegularExpressions.Regex.IsMatch(
            projectText,
            "<OutputType>\\s*Database\\s*</OutputType>",
            Text.RegularExpressions.RegexOptions.IgnoreCase
        )

    if isDatabaseProject then
        Error "a SQL database project (dacpac), not an F# compilation — skipped"
    else

        // A multi-targeted project builds "outer" and dispatches one inner build
        // per framework. CoreCompile — and so FscCommandLineArgs — only runs in
        // the inner ones, so the outer query comes back empty. Pin a framework
        // to get an inner build.
        //
        // The MOST RESTRICTIVE one, not the first listed. Which matters: a rule
        // gated on what the target can resolve offers `s.Contains 'x'` under
        // net8.0, where the char overload exists, and that does not compile for
        // a netstandard2.0 target which lacks it. Analysing the narrowest
        // surface keeps every fix valid for the wider ones. (Measured: a probe
        // listing net8.0 first got exactly that break.)
        //
        // ...unless the caller named one. Code behind another framework's #if
        // is invisible to the narrowest analysis — it is not in the parse tree
        // at all — so reaching it means asking for that framework by name.
        let targetFramework =
            if chosenFramework <> "" then
                Some chosenFramework
            else
                targetFrameworksOf projectPath |> List.tryHead

        let tfmArg =
            match targetFramework with
            | Some tfm ->
                Out.dim $"  (multi-targeted; analysing against {tfm})"
                $" -p:TargetFramework={tfm}"
            | None -> ""

        let runner, prefix =
            if isSdkStyle then
                "dotnet", ""
            else
                // best effort without VS installed
                vsMsBuildPath.Value
                |> Option.map (fun msbuild -> msbuild, null)
                |> Option.defaultValue ("dotnet", "")

        let run (arguments: string) =
            let finalArgs =
                // dotnet needs the verb ("build"/"msbuild"); MSBuild.exe does not
                if isNull prefix then
                    let firstSpace = arguments.IndexOf ' '

                    if firstSpace > 0 then
                        arguments.Substring(firstSpace + 1)
                    else
                        arguments
                else
                    arguments

            runForProject projectPath processTimeout runner finalArgs

        // a REAL build first: project references must exist on disk for the
        // args-only pass below (SkipCompilerExecution skips them too), and a
        // project that does not build has no business being rewritten.
        //
        // Restore SEPARATELY, and without the framework: a restore that
        // carries -p:TargetFramework writes an assets file for that one
        // framework only, and everything that later builds another — the
        // all-frameworks verification, a sibling project's inner MSBuild of
        // this one — fails with NETSDK1005 "doesn't have a target for
        // net10.0", or with a half-resolved reference set ("The type
        // referenced through 'System.Array' is defined in an assembly that
        // is not referenced"). SwaggerProvider, whose Runtime project builds
        // DesignTime through an <MSBuild> task, had both, run after run, and
        // the verification put good fixes back on the strength of them.
        // `dotnet build` restores implicitly; `msbuild -t:Build` does not.
        let restoreExit, restoreOut, restoreErr =
            run $"msbuild \"{projectPath}\" -t:Restore"

        let buildExit, buildOut, buildErr =
            if restoreExit <> 0 then
                restoreExit, restoreOut, restoreErr
            // a verification switch: analyse a tree whose build is known to
            // fail (studying what the typecheck sees of that failure), on
            // the outputs already on disk
            elif Environment.GetEnvironmentVariable "FSREF_SKIP_BUILD" = "1" then
                0, "", ""
            else
                run $"msbuild \"{projectPath}\" -t:Build{tfmArg}"

        // FS3511 is emitted at CODEGEN, so no analyzer can see it — but this
        // build just did, and the warning carries the builder's own position
        // ("SignalRHubs.fs(2583,16): warning FS3511: This state machine is not
        // statically compilable"). Handing those lines to the analyzers lets
        // FR0029's tail extraction fire where the fallback is REAL rather than
        // wherever a size threshold guesses at one. Nothing here when the
        // build compiled nothing because it was already up to date; the
        // Rebuild below cleans, so the next run's build does compile.
        let fallbackPattern =
            Text.RegularExpressions.Regex(
                @"^\s*(?<file>[^\r\n(]+)\((?<line>\d+),\d+\):\s*warning FS3511",
                Text.RegularExpressions.RegexOptions.Multiline
            )

        for m in fallbackPattern.Matches($"{buildOut}\n{buildErr}") do
            let file: string = m.Groups.["file"].Value.Trim()

            match Int32.TryParse m.Groups.["line"].Value with
            | true, line ->
                let full =
                    if Path.IsPathRooted file then
                        file
                    else
                        Path.Combine(Path.GetDirectoryName(Path.GetFullPath projectPath), file)

                Configuration.setDynamicFallbackSites [ full, line ]
            | _ -> ()

        if buildExit <> 0 then
            // the raw MSBuild transcript buries the compile errors under
            // restore chatter and MSB warnings; show just the error lines
            // (a type provider's connection failure surfaces here too)
            let errorLines =
                ($"{buildOut}\n{buildErr}").Split '\n'
                |> Array.filter (fun l -> l.Contains "error")
                |> Array.distinct
                |> Array.truncate 8

            let detail =
                if errorLines.Length = 0 then
                    $"{buildOut}\n{buildErr}"
                else
                    String.concat "\n" errorLines

            Error $"dotnet build failed — fix the build before applying fixes:\n{detail}"
        else
            // Rebuild forces CoreCompile even when the build above left the
            // project up-to-date (an incremental skip yields no args at all);
            // BuildProjectReferences=false keeps the referenced outputs intact.
            // With SkipCompilerExecution the target fails AFTER emitting the
            // args (no dll to copy) — judge by the JSON, not the exit code.
            let exit, stdout, stderr =
                run
                    $"msbuild \"{projectPath}\" -t:Rebuild -p:BuildProjectReferences=false -p:ProvideCommandLineArgs=true -p:SkipCompilerExecution=true --getItem:FscCommandLineArgs --getProperty:DotnetFscCompilerPath{tfmArg}"

            // that Rebuild CLEANED the project's outputs and, compilation
            // skipped, wrote none back. An SDK-style sibling rebuilds this
            // project through its project reference; an old-style one
            // references the dll by path (FsXaml's demos:
            // `..\..\bin\FsXaml.Wpf.TypeProvider\...dll`) and finds nothing.
            // Build once more, so the outputs are there for whoever needs them
            if not isSdkStyle then
                run $"msbuild \"{projectPath}\" -t:Build{tfmArg}" |> ignore

            try
                use doc = JsonDocument.Parse stdout

                let args =
                    doc.RootElement.GetProperty("Items").GetProperty("FscCommandLineArgs").EnumerateArray()
                    |> Seq.map (fun item -> item.GetProperty("Identity").GetString())
                    |> Array.ofSeq

                // The FSharp.Core fsc would use when the project names none.
                //
                // A project with DisableImplicitFSharpCoreReference (paket's
                // convention) passes no -r: for FSharp.Core, and fsc quietly
                // takes the one bundled beside it in the SDK — the
                // netstandard2.0 build. FCS, handed the same arguments, takes
                // the FSharp.Core loaded in THIS process instead: the
                // netstandard2.1 build, whose task builder names
                // System.IAsyncDisposable through netstandard 2.1. Checked
                // against a netstandard2.0 project that resolves as "The
                // module/namespace 'System' from compilation unit
                // 'netstandard' did not contain ... 'IAsyncDisposable'" —
                // three errors on SwaggerProvider's DesignTime that its own
                // build never had, refusing the project run after run. So
                // when the arguments carry no FSharp.Core, the compiler's own
                // is added: the same assembly fsc resolves, and nothing else.
                let bundledFSharpCore =
                    try
                        let mutable properties = Unchecked.defaultof<JsonElement>

                        if doc.RootElement.TryGetProperty("Properties", &properties) then
                            let mutable fsc = Unchecked.defaultof<JsonElement>

                            if properties.TryGetProperty("DotnetFscCompilerPath", &fsc) then
                                let fscPath = (fsc.GetString()).Trim().Trim '"'
                                let core = Path.Combine(Path.GetDirectoryName fscPath, "FSharp.Core.dll")
                                if File.Exists core then Some core else None
                            else
                                None
                        else
                            None
                    with _ -> // an SDK that does not report the path simply gets no addition; fsharpanalyzer: ignore-line FR0055
                        None

                let referencesFSharpCore =
                    args
                    |> Array.exists (fun a ->
                        a.StartsWith("-r:", StringComparison.OrdinalIgnoreCase)
                        && Path
                            .GetFileName(a.Substring 3)
                            .Equals("FSharp.Core.dll", StringComparison.OrdinalIgnoreCase))

                let args =
                    match bundledFSharpCore with
                    | Some core when not referencesFSharpCore -> Array.append args [| $"-r:{core}" |]
                    | _ -> args

                if args.Length = 0 then
                    Error "MSBuild produced no FscCommandLineArgs (is this an SDK-style F# project?)"
                else
                    Ok args
            with :? JsonException ->
                Error $"dotnet msbuild (exit {exit}) produced no readable args:\n{stdout}\n{stderr}"

/// All [<CliAnalyzer>]-attributed functions of the analyzers assembly.
let private cliAnalyzers () =
    let assembly = typeof<FSharp.Refactor.RedundantParens.Suggestion>.Assembly

    [ for t in assembly.GetTypes() do
          for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
              if m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).Length > 0 then
                  m ]

/// FSREF_EDITOR_OFFERS=1: the [<EditorAnalyzer>] wrappers run too, and
/// their editor-only offers apply like any fix — the way to put every
/// offer through the build check on real code before an editor gets it.
/// Alternatives of one finding are separate messages at one range; the
/// overlap rule keeps the first. A verification switch, not a mode: the
/// editor-only offers are editor-only because a person picks among them.
let private editorOffers =
    Environment.GetEnvironmentVariable "FSREF_EDITOR_OFFERS" = "1"

let private editorAnalyzers =
    lazy
        (let assembly = typeof<FSharp.Refactor.RedundantParens.Suggestion>.Assembly

         [ for t in assembly.GetTypes() do
               for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
                   if m.GetCustomAttributes(typeof<EditorAnalyzerAttribute>, false).Length > 0 then
                       m ])

/// Analyzers whose CLI wrappers never touch CheckFileResults — the set a
/// --parse-only run may execute against an unresolvable compilation. The
/// typed analyzers are excluded outright rather than trusted to
/// self-silence: their conservative gates assume a compilation that at
/// least TRIED to resolve. Curated against the wrapper bodies in
/// Analyzers.fs; a new syntactic analyzer earns its entry here.
let parseOnlySafeAnalyzers =
    set
        [ "AbbreviatedType"
          "CommentDoc"
          "LiterateComment"
          "ArgNames"
          "AttributeMerge"
          "AutoProperty"
          "BooleanSimplify"
          "CeStrip"
          "CheckedArithmetic"
          "ConversionMove"
          // reads the parse tree only, so it belongs in the mode meant for
          // codebases that cannot compile
          "GenerativeLoop"
          "MapFusion"
          "StringEmptiness"
          "DuFieldNames"
          "ExceptionRules"
          "FormatArgs"
          "Hints"
          "IndexedLoop"
          "InterpToString"
          "LambdaBuiltin"
          "LoopPerf"
          "MatchBang"
          "MatchToIf"
          // MethodCallParens (FR0094) is syntactic, but not for here: on a
          // receiver the compilation cannot type, `x.Add(p)` and `x.Add p`
          // fail with DIFFERENT error sets, and the count-based regression
          // check reads that as a break (fsharplint's docs scripts, three
          // rollbacks for a matter of taste)
          "MiscRules"
          "ObjectRules"
          "PathSeparator"
          "PatternParens"
          "RaiseFailwith"
          "RecursiveAppend"
          "RecursiveSeq"
          "RedundantParens"
          "RedundantSyntax"
          "RegexUsage"
          "LiteralConst"
          "MatchArmMerge"
          "MatchGuards"
          "ObsoleteCrypto"
          "RecGroup"
          "RegexValidity"
          "SecretLiterals"
          "SecurityRules"
          "StructDu"
          "StructHints"
          "SwallowedException"
          "TabIndentation"
          "TaskStateMachine"
          "TrailingSemicolon"
          "TypeChecks"
          "TypeParens"
          "TypeTestChain"
          "UnicodeHygiene"
          "UnimplementedBranch"
          "WhileBang"
          "XmlDocParams" ]

let private analyzerName (m: MethodInfo) =
    (m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).[0] :?> CliAnalyzerAttribute).Name

/// The encoding a source file is written in, judged by its BOM — so an
/// edit does not silently strip a UTF-8 BOM or re-encode a UTF-16 file.
let private encodingOf (path: string) : System.Text.Encoding =
    let bom =
        try
            use fs = File.OpenRead path
            let buffer = Array.zeroCreate 3
            let n = fs.Read(buffer, 0, 3)
            Array.truncate n buffer
        with
        | :? IOException
        | :? UnauthorizedAccessException -> [||]

    match bom with
    | [| 0xEFuy; 0xBBuy; 0xBFuy |] -> System.Text.UTF8Encoding true
    | _ when bom.Length >= 2 && bom.[0] = 0xFFuy && bom.[1] = 0xFEuy -> System.Text.Encoding.Unicode
    | _ when bom.Length >= 2 && bom.[0] = 0xFEuy && bom.[1] = 0xFFuy -> System.Text.Encoding.BigEndianUnicode
    | _ -> System.Text.UTF8Encoding false

/// Write a source file back in the encoding it already had.
let private writeSource (path: string) (text: string) =
    File.WriteAllText(path, text, encodingOf path)

/// Set for the run by executeRun. In --parse-only mode nothing resolves,
/// so only PARSE-phase diagnostics are meaningful: a fix that spells a
/// new identifier (`CultureInfo.InvariantCulture`) adds unresolved-
/// reference errors to the pile, and a raw count comparison then blamed
/// the fix for pre-existing noise (found on PethostBackup: every FR0067
/// culture fix rolled back for inflating FS0039s that were ignored to
/// begin with).
let mutable internal parseOnlyRun = false

/// `fsi.CommandLineArgs` and friends live in
/// FSharp.Compiler.Interactive.Settings.dll, which FCS references under
/// useFsiAuxLib only when that assembly sits beside the compiler — this
/// tool's own directory, which does not ship it. The SDK dotnet resolves
/// for the script's directory does, so it is referenced from there;
/// without it every script touching `fsi` read as "does not typecheck"
/// (FSharp.Azure.Quantum's examples, all of them).
let private fsiAuxLib =
    let cache =
        System.Collections.Concurrent.ConcurrentDictionary<string, string option>()

    fun (scriptDir: string) ->
        cache.GetOrAdd(
            scriptDir,
            fun dir ->
                try
                    let _, version, _ =
                        runProcessIn (Some dir) (TimeSpan.FromSeconds 30.) "dotnet" "--version"

                    let _, sdks, _ =
                        runProcessIn (Some dir) (TimeSpan.FromSeconds 60.) "dotnet" "--list-sdks"

                    let version = version.Trim()

                    sdks.Split '\n'
                    |> Array.tryPick (fun line ->
                        let m = System.Text.RegularExpressions.Regex.Match(line.Trim(), @"^(\S+) \[(.+)\]$")

                        if m.Success && m.Groups.[1].Value = version then
                            Some(
                                Path.Combine(
                                    m.Groups.[2].Value,
                                    version,
                                    "FSharp",
                                    "FSharp.Compiler.Interactive.Settings.dll"
                                )
                            )
                        else
                            None)
                    |> Option.filter File.Exists
                with _ -> // no SDK found: the script is read without fsi, as before; fsharpanalyzer: ignore-line FR0055
                    None
        )

let private withFsiAuxLib (scriptPath: string) (options: FSharpProjectOptions) =
    if
        options.OtherOptions
        |> Array.exists (fun o -> o.Contains "FSharp.Compiler.Interactive.Settings")
    then
        options
    else
        match fsiAuxLib (Path.GetDirectoryName(Path.GetFullPath scriptPath)) with
        | Some dll ->
            { options with
                OtherOptions = Array.append options.OtherOptions [| $"-r:{dll}" |] }
        | None -> options

let private projectErrors (checker: FSharpChecker) (options: FSharpProjectOptions) =
    let results = checker.ParseAndCheckProject options |> Async.RunSynchronously

    results.Diagnostics
    |> Array.filter (fun d ->
        d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
        && (not parseOnlyRun || d.Subcategory = "parse"))

let private errorCount (checker: FSharpChecker) (options: FSharpProjectOptions) = (projectErrors checker options).Length

/// The project's errors, plus each named file checked on its own. The
/// project check is not the whole truth: on the F# compiler, whose every
/// implementation file has a signature, a member pulled out of a `let rec`
/// group generalised a parameter and the signature's concrete type failed
/// FS0034 in fsc — while ParseAndCheckProject reported nothing, and only a
/// per-file check of that file did. A pass that touched a file checks that
/// file the second way too.
let private projectErrorsWith (checker: FSharpChecker) (options: FSharpProjectOptions) (files: string list) =
    let project = projectErrors checker options

    // A pass can change a file this compilation does not contain: a
    // `#load`ing script is rewritten alongside the definition it calls.
    // FCS THROWS on a per-file check of a file that is not in the project
    // ("was not part of the project"), and there is nothing to check
    // anyway — the project build never compiled that script, which is
    // precisely why the script edit is answerable to the same-symbol
    // reasoning that produced it and to nothing else.
    let inProject =
        options.SourceFiles
        |> Array.map (fun f -> Path.GetFullPath(f).ToLowerInvariant())
        |> Set.ofArray

    let perFile =
        files
        |> List.filter (fun path ->
            try
                inProject.Contains(Path.GetFullPath(path).ToLowerInvariant())
            with _ -> // an unopenable path is not this project's; fsharpanalyzer: ignore-line FR0055
                false)
        |> List.toArray
        |> Array.collect (fun path ->
            try
                let text = FSharp.Compiler.Text.SourceText.ofString (File.ReadAllText path)

                let _, answer =
                    checker.ParseAndCheckFileInProject(path, 0, text, options)
                    |> Async.RunSynchronously

                match answer with
                | FSharpCheckFileAnswer.Succeeded results ->
                    results.Diagnostics
                    |> Array.filter (fun d ->
                        d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
                        && (not parseOnlyRun || d.Subcategory = "parse"))
                | FSharpCheckFileAnswer.Aborted -> [||]
            with
            | :? IOException
            | :? UnauthorizedAccessException -> [||])

    Array.append project perFile
    |> Array.distinctBy (fun d ->
        Path.GetFullPath(d.FileName).ToLowerInvariant(), d.StartLine, d.StartColumn, d.ErrorNumber)

/// Apply grouped edits, bottom-up per file, skipping any fix overlapping
/// one already taken; the original text is verified before each splice.
/// A rule's kind, padded so the file paths after it line up. "correctness"
/// and "performance" are the longest at eleven.
let private kindColumn (code: string) =
    let kind = RuleCatalog.name (RuleCatalog.categoryOf code)
    $"[{kind}]".PadRight 13

/// A file one pass changed: its path, its pre-pass text, and the fixes
/// that landed in it — enough to undo the pass's work on the file and to
/// suppress those fixes on later passes.
type private AppliedFile =
    {
        Path: string
        Before: string
        /// (suggestion group, rule code, fix) — the GROUP travels because a
        /// multi-edit suggestion applies all-or-nothing, and any later
        /// selective rollback must keep it that way: half a ParamOrder swap
        /// COMPILES and computes the wrong thing
        Fixes: (int * string * Fix) list
    }

/// The suppression key of a fix: rule code, file, and the edit's CONTENT.
/// Not coordinates — a later pass applying an unrelated fix ABOVE the
/// suppressed spot shifts every line below it, the coordinate key misses,
/// and the re-applied fix triggers another rollback, oscillating until
/// --max-passes. Content keys survive shifting; the cost is suppressing an
/// identical same-rule fix elsewhere in the same file, which — having
/// identical content — would almost certainly have broken identically.
let private fixKey (code: string) (file: string) (f: Fix) =
    code, Path.GetFullPath file, f.FromText, f.ToText

/// Files a verification put back for refusing another project or
/// framework, for the rest of the run: the next framework round would
/// otherwise apply the same fixes again and bisect again (the F#
/// compiler's sformat.fs, twice in one run).
let private putBackFiles =
    System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

/// The files the compilation's snapshot covers — its own sources — and
/// the ORIGINAL text of every file written OUTSIDE it: a sibling project's
/// sources, a #loading script, a linker's own files, which the api pass
/// (and a cross-file migration) rewrite and the project's build never
/// sees. Recorded the moment each is first written, so the end-of-run
/// put-backs — the error-count guard, the all-frameworks arbiter, the
/// bisection — can put them back with the definitions they were rewritten
/// for. Empty while there is no snapshot (--dry-run writes nothing anyway).
let internal snapshotFiles =
    System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

let internal extraSnapshot =
    System.Collections.Generic.Dictionary<string, string>(StringComparer.OrdinalIgnoreCase)

/// A file is about to be written over `before`: keep that text when the
/// file is outside the snapshot and not seen yet.
let internal recordExtra (file: string) (before: string) =
    let full = Path.GetFullPath file

    if
        snapshotFiles.Count > 0
        && not (snapshotFiles.Contains full)
        && not (extraSnapshot.ContainsKey full)
    then
        extraSnapshot.[full] <- before

/// Files of a LINKED compilation — another project's own sources, edited
/// by the api pass because that project compiles this one's files directly
/// — for the one-word note on their fix lines. Set by the api pass for
/// the duration of its apply, empty otherwise.
let private linkedFiles = System.Collections.Generic.HashSet<string>()

/// Returns the number of fixes applied and the files they changed.
/// `suppressed` holds fixes rolled back by an earlier pass's verification;
/// re-applying one would only be rolled back again.
///
/// Edits carry a GROUP id — one per suggestion — and a group applies all
/// or nothing within a file. A hoist is an insertion plus a deletion:
/// dropping the insertion (say, to an overlap with another suggestion at
/// the same point) while the deletion lands removes a binding its uses
/// still need. Found live on Fuuga: two FR0071 hoists inserting at one
/// point, half of the second applied, `startBlock` undefined.
let private applyEditGroups
    (dryRun: bool)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    (editsByFile: System.Collections.Generic.Dictionary<string, ResizeArray<int * string * Fix>>)
    : int * AppliedFile list =
    let mutable applied = 0
    let appliedFiles = ResizeArray<AppliedFile>()

    for kv in editsByFile do
        let file = kv.Key
        let text = File.ReadAllText file

        // bottom-up, so earlier splices never shift later ranges
        let edits =
            kv.Value
            |> Seq.sortByDescending (fun (_, _, f) -> f.FromRange.StartLine, f.FromRange.StartColumn)
            |> List.ofSeq

        let groupEdits =
            kv.Value
            |> Seq.groupBy (fun (g, _, _) -> g)
            |> Map.ofSeq
            |> Map.map (fun _ es -> List.ofSeq es)

        let mutable current = text
        let mutable appliedRanges: Range list = []
        let mutable appliedHere: (int * string * Fix) list = []
        let groupDecisions = System.Collections.Generic.Dictionary<int, bool>()

        let overlaps (r: Range) =
            appliedRanges
            |> List.exists (fun a ->
                Range.rangeContainsPos a r.Start
                || Range.rangeContainsPos a r.End
                || Range.rangeContainsRange r a)

        // can this edit be spliced into `current` exactly as promised?
        // (start/end computed against original coordinates, which stay
        // valid above every already-applied splice in the bottom-up sweep)
        let viable (f: Fix) =
            let lines = current.Split '\n'

            if
                f.FromRange.StartLine - 1 > lines.Length
                || f.FromRange.EndLine - 1 > lines.Length
            then
                None
            else
                let startIndex =
                    (lines
                     |> Seq.take (f.FromRange.StartLine - 1)
                     |> Seq.sumBy (fun l -> l.Length + 1))
                    + f.FromRange.StartColumn

                let endIndex =
                    (lines |> Seq.take (f.FromRange.EndLine - 1) |> Seq.sumBy (fun l -> l.Length + 1))
                    + f.FromRange.EndColumn

                if
                    startIndex <= current.Length
                    && endIndex <= current.Length
                    && current.Substring(startIndex, endIndex - startIndex).Replace("\r", "") = f.FromText.Replace(
                        "\r",
                        ""
                    )
                then
                    Some(startIndex, endIndex)
                else
                    None

        // decide a whole group the moment its bottom-most edit is reached:
        // every member must be unsuppressed, non-overlapping and viable, or
        // none of them applies. A self-identical edit is tolerated inside a
        // group (it changes nothing either way) but sinks a group of one.
        let decideGroup (groupId: int) =
            let members = groupEdits.[groupId]

            let ok =
                members
                |> List.forall (fun (_, code, f) ->
                    not (suppressed.Contains(fixKey code file f))
                    && not (putBackFiles.Contains(Path.GetFullPath file))
                    && not (overlaps f.FromRange)
                    && (f.ToText.Replace("\r", "") = f.FromText.Replace("\r", "") || (viable f).IsSome))
                && members
                   |> List.exists (fun (_, _, f) -> f.ToText.Replace("\r", "") <> f.FromText.Replace("\r", ""))

            if ok then
                // reserve every member's range at once, so no other group
                // can interleave between this one's edits
                for _, _, f in members do
                    appliedRanges <- f.FromRange :: appliedRanges
            elif members.Length > 1 then
                let _, code, f = List.head members

                printfn
                    $"  {code} {kindColumn code} {Path.GetFileName file}({f.FromRange.StartLine},{f.FromRange.StartColumn}): held back (its edits cannot all apply together)"

            groupDecisions.[groupId] <- ok
            ok

        for groupId, code, f in edits do
            let accepted =
                match groupDecisions.TryGetValue groupId with
                | true, decision -> decision
                | false, _ -> decideGroup groupId

            let changesSomething = f.ToText.Replace("\r", "") <> f.FromText.Replace("\r", "")

            if accepted && changesSomething then
                match viable f with
                | Some(startIndex, endIndex) ->
                    // splice in the file's own line-ending convention, so
                    // an LF replacement does not seed a CRLF file with
                    // mixed endings
                    let eol = if current.Contains "\r\n" then "\r\n" else "\n"
                    let toText = f.ToText.Replace("\r\n", "\n").Replace("\n", eol)

                    current <- current.Remove(startIndex, endIndex - startIndex).Insert(startIndex, toText)
                    appliedHere <- (groupId, code, f) :: appliedHere
                    applied <- applied + 1

                    // once per file: the first fix line in a linked file says so
                    let linked =
                        if linkedFiles.Remove(Path.GetFullPath(file).ToLowerInvariant()) then
                            " note: linked file"
                        else
                            ""

                    printfn
                        $"  {code} {kindColumn code} {Path.GetFileName file}({f.FromRange.StartLine},{f.FromRange.StartColumn}){linked}"
                | None -> ()

        if current <> text && not dryRun then
            recordExtra file text
            writeSource file current

            appliedFiles.Add
                { Path = file
                  Before = text
                  Fixes = appliedHere }

    applied, List.ofSeq appliedFiles

/// One project-wide suggestion, normalized across the API-changing rules:
/// a code, the symbol it rewrites, and edits that may land in any file.
type private ApiSuggestion =
    { Code: string
      FunctionName: string
      Edits: (Range * string * string) list }

/// One script's contribution, cached across the compilations of a run.
/// Discovery is per PROJECT, but the expensive part — resolving a script's
/// references and typechecking it — depends only on the script, and a
/// solution sweep calls the api pass once per compilation (Fuuga: 39).
/// Re-typechecking 13 scripts 39 times over is half an hour of nothing.
type private ScriptInfo =
    {
        /// Files this script pulls in, so a project can ask "does this
        /// concern me?" without recomputing anything.
        Loaded: string[]
        /// None when the script does not typecheck: its calls cannot be
        /// read, so nothing it #loads may be reshaped.
        Context: FileContext option
        Uses: FSharpSymbolUse[]
        /// The first errors of a script that does not typecheck — the
        /// reason beside the verdict.
        Errors: string list
    }

/// Keyed by script path; the write time is the invalidation, so a script
/// this run just edited is re-read on the next pass.
let private scriptCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, DateTime * ScriptInfo>(StringComparer.OrdinalIgnoreCase)

/// Call sites that live OUTSIDE the project's compilation: scripts under
/// the scanned path that `#load` its sources.
///
/// A `#load`ing script compiles those files INTO itself, so it sees the
/// `internal` bindings — exactly the ones this pass is allowed to reshape,
/// public ones being held back precisely because their callers can live
/// somewhere we cannot see. But the script is a separate compilation, so
/// its calls are absent from the project's symbol tables, and the pass's
/// own "every use resolves or the change is abandoned" guard never fires.
/// The definition changed shape and the script stopped compiling.
///
/// Note there is no build check behind this: `dotnet build` compiles the
/// project, not the scripts beside it. A script edit is answerable to the
/// same-symbol reasoning that produced it and nothing else, which is why
/// the matching below is by declaration rather than by name.
type private ScriptCallSites =
    {
        /// Parse contexts, so a call-site edit can be rendered in the script.
        Contexts: (string * FileContext) list
        /// Uses inside the scripts, indexed by the symbol's full name.
        UsesByFullName: System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>
        /// Project sources #loaded by a script we could NOT typecheck. Its
        /// call sites are unreadable, so nothing defined in these files may
        /// be reshaped — the same restraint as an unresolvable use.
        Unverifiable: System.Collections.Generic.HashSet<string>
        /// Scripts that `#r` the project's BUILT assembly. Such a script
        /// sees the public declarations, and its calls resolve to the dll's
        /// metadata rather than to the sources this pass rewrites, so
        /// nothing matches them to a declaration and nothing could rewrite
        /// them: the pass declines to reshape what the script can see.
        ReferencingScripts: string list
    }

/// The file name of the assembly a compilation builds — `Lib.dll` — from
/// its `-o:`/`--out:` argument, else from the project file's name, which
/// is the SDK's default AssemblyName.
let private outputFileNameOf (options: FSharpProjectOptions) =
    options.OtherOptions
    |> Array.tryPick (fun o ->
        [ "-o:"; "--out:" ]
        |> List.tryPick (fun flag ->
            if o.StartsWith(flag, StringComparison.OrdinalIgnoreCase) then
                Some(Path.GetFileName(o.Substring flag.Length))
            else
                None))
    |> Option.defaultWith (fun () -> Path.GetFileNameWithoutExtension options.ProjectFileName + ".dll")

/// FullName throws for a few symbol kinds; a symbol we cannot name simply
/// contributes no cross-compilation match.
/// A symbol's full name, or None when there is not one to be had.
///
/// The try alone was not enough. `FullName` can RETURN null as well as
/// throw, and a null answer used to travel on as `Some null` into a
/// Dictionary key - which throws ArgumentNullException outside this try and
/// takes the run down. Both shapes are the same answer to the caller: a use
/// that cannot be named, which the caller treats as a reason to leave the
/// sources alone rather than migrate one call site short.
let private symbolFullName (s: FSharpSymbol) =
    if isNull (box s) then
        None
    else
        try
            match s.FullName with
            | name when String.IsNullOrWhiteSpace name -> None
            | name -> Some name
        with _ -> // fsharpanalyzer: ignore-line FR0055
            None

/// Are these two symbols — one from the project's compilation, one from a
/// script's — the same declaration? Full names alone are not identity: a
/// referenced assembly can carry a module and function of exactly the same
/// name, and rewriting THAT call site would break a script no build check
/// covers. Both compilations read the same source file, so the declaration
/// position is shared and exact.
let private sameDeclaration (a: FSharpSymbol) (b: FSharpSymbol) =
    match a.DeclarationLocation, b.DeclarationLocation with
    | Some ra, Some rb ->
        ra.StartLine = rb.StartLine
        && ra.StartColumn = rb.StartColumn
        && String.Equals(Path.GetFullPath ra.FileName, Path.GetFullPath rb.FileName, StringComparison.OrdinalIgnoreCase)
    | _ -> false

/// Read one script: what it loads, and — when it typechecks — its parse
/// context and the uses it makes. Cached on the file's write time.
let private readScript (checker: FSharpChecker) (script: string) =
    let stamp =
        try
            File.GetLastWriteTimeUtc script
        with _ -> // fsharpanalyzer: ignore-line FR0055
            DateTime.MinValue

    match scriptCache.TryGetValue script with
    | true, (cached, info) when cached = stamp -> info
    | _ ->
        let info =
            let text =
                try
                    Some(File.ReadAllText script)
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    None

            match text with
            // only a #load can pull project sources into a script's
            // compilation; a `#r` against the built dll sees no internals,
            // so it is not a call site this pass can break
            | Some text when text.Contains "#load" ->
                let sourceText = SourceText.ofString text

                // FCS has to be told which reference set the script wants. .NET Core is
                // right for modern scripts, but a script targeting .NET Framework (bare
                // GAC `#r`s, net4x assemblies, System.Configuration.Install) cannot
                // typecheck against it at all: mscorlib resolves to the Core facade, so
                // even `open System.IO` reports DirectorySecurity as missing and every
                // file the script #loads is written off. Try Core, and when that does not
                // resolve retry as Framework, keeping whichever typechecks.
                // PethostBackup/backend/Program.fsx: 160 errors as Core, 0 as Framework.
                let attempt assumeDotNetFramework =
                    let options, _ =
                        checker.GetProjectOptionsFromScript(
                            script,
                            sourceText,
                            assumeDotNetFramework = assumeDotNetFramework,
                            useFsiAuxLib = true
                        )
                        |> Async.RunSynchronously

                    let options = withFsiAuxLib script options
                    let results = checker.ParseAndCheckProject options |> Async.RunSynchronously

                    let errors =
                        results.Diagnostics
                        |> Array.filter (fun d ->
                            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

                    options, results, errors

                let scriptOptions, results, errors =
                    let (_, _, coreErrors) as asCore = attempt false

                    if Array.isEmpty coreErrors then
                        asCore
                    else
                        let (_, _, frameworkErrors) as asFramework = attempt true

                        if frameworkErrors.Length < coreErrors.Length then
                            asFramework
                        else
                            asCore

                let broken = not (Array.isEmpty errors)

                let loaded = scriptOptions.SourceFiles |> Array.map Path.GetFullPath

                if broken then
                    { Loaded = loaded
                      Context = None
                      Uses = [||]
                      Errors =
                        results.Diagnostics
                        |> Array.filter (fun d ->
                            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
                        |> Array.truncate 2
                        |> Array.map (fun d ->
                            $"{Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}")
                        |> List.ofArray }
                else
                    let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions scriptOptions

                    let parsed =
                        checker.ParseFile(script, sourceText, parsingOptions) |> Async.RunSynchronously

                    let full = Path.GetFullPath script

                    // only uses IN THE SCRIPT: the #loaded files belong to
                    // this compilation too, and the project pass owns those
                    let uses =
                        results.GetAllUsesOfAllSymbols()
                        |> Array.filter (fun u ->
                            not u.IsFromDefinition
                            && String.Equals(
                                Path.GetFullPath u.Range.FileName,
                                full,
                                StringComparison.OrdinalIgnoreCase
                            ))

                    { Loaded = loaded
                      Context =
                        Some
                            { FileName = script
                              Source = sourceText
                              ParseTree = parsed.ParseTree }
                      Uses = uses
                      Errors = [] }
            | _ ->
                { Loaded = [||]
                  Context = None
                  Uses = [||]
                  Errors = [] }

        scriptCache.[script] <- (stamp, info)
        info

/// Build output can hold scripts too, and one there is neither a call site
/// worth honouring nor a file worth editing.
let private isBuildOutput (path: string) =
    let normalized = path.Replace("\\", "/").ToLowerInvariant()
    normalized.Contains "/obj/" || normalized.Contains "/bin/"

[<return: Struct>]
let inline private (|Exists|_|) (input: string) =
    if Directory.Exists input then
        ValueSome input
    else
        ValueNone

/// Index the call sites this project's compilation cannot see.
/// `applyEditGroups`, plus the check a script needs and the project build
/// cannot give it.
///
/// Scripts sit outside the build check: `dotnet build` compiles the
/// project, not the .fsx beside it, so nothing downstream would ever
/// notice a script we broke. Check them directly. Every script we edited
/// typechecked cleanly beforehand — call sites are never read from one
/// that did not — so the baseline is zero errors and any error now is
/// ours.
///
/// A suggestion is atomic across files, so a broken script takes its whole
/// group with it: leaving the definition reshaped while putting the script
/// back is precisely the breakage this exists to prevent.
///
/// Both passes go through here. The api pass (FR0090/FR0091) has always
/// rewritten `#load`ing scripts; the normal pass does too now that the
/// FR0069/FR0093 migrations read their call sites, and one rule's safety
/// net is no use to the other if it hangs in only one of the two places.
///
/// `brokenElsewhere` is the same question for whatever else the caller
/// edited outside the project — the api pass's sibling projects, which
/// it rechecks itself and answers with the groups to put back; the
/// normal pass has nothing to add and answers with none.
///
/// And one more thing a group can be, besides broken: HALF-APPLIED.
/// `applyEditGroups` decides a group per file, so a group whose edit in
/// one file was held back — suppressed from an earlier rollback, or in a
/// file the all-frameworks verification put back — while its edits in
/// another file went in has left a definition reshaped and a call site
/// not. That is exactly the state a group exists to make impossible, so
/// such a group is put back whole here, with the broken ones.
let rec private applyEditGroupsCheckingScripts
    (checker: FSharpChecker)
    (dryRun: bool)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    (brokenElsewhere: AppliedFile list -> Set<int>)
    (editsByFile: System.Collections.Generic.Dictionary<string, ResizeArray<int * string * Fix>>)
    : int * AppliedFile list =
    // which of the scripts about to be edited were typechecking BEFORE the
    // edit. The check below asks whether a rewritten script still has a
    // context, and a script that never had one — it does not resolve its
    // `#r`s, or it has no `#load` at all and so is never given one — would
    // fail that test no matter what was written, so every fix to it was
    // applied and put back on every run, forever. Only a script this pass
    // actually broke may take its group down.
    let contextBefore =
        if dryRun then
            System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)
        else
            let checkable =
                System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

            for path in editsByFile.Keys do
                if
                    path.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)
                    && (readScript checker path).Context.IsSome
                then
                    checkable.Add path |> ignore

            checkable

    let applied, changed = applyEditGroups dryRun suppressed editsByFile

    let brokenScriptGroups =
        if dryRun then
            Set.empty
        else
            changed
            |> List.filter (fun cf -> contextBefore.Contains cf.Path && (readScript checker cf.Path).Context.IsNone)
            |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g))
            |> Set.ofList

    // a group applied in one file and held back in another; only an edit
    // that changes something counts as expected, since a self-identical
    // member is never recorded as applied
    let halfAppliedGroups =
        if dryRun then
            Set.empty
        else
            let appliedIn =
                changed
                |> List.collect (fun cf ->
                    cf.Fixes
                    |> List.map (fun (g, _, _) -> g, Path.GetFullPath(cf.Path).ToLowerInvariant()))
                |> Set.ofList

            let appliedGroups = appliedIn |> Set.map fst

            [ for kv in editsByFile do
                  for g, _, f in kv.Value do
                      if
                          appliedGroups.Contains g
                          && f.ToText.Replace("\r", "") <> f.FromText.Replace("\r", "")
                          && not (appliedIn.Contains(g, Path.GetFullPath(kv.Key).ToLowerInvariant()))
                      then
                          g ]
            |> Set.ofList

    let brokenGroups =
        Set.unionMany
            [ brokenScriptGroups
              halfAppliedGroups
              (if dryRun then Set.empty else brokenElsewhere changed) ]

    if Set.isEmpty brokenGroups then
        applied, changed
    else
        // restore everything this pass wrote, then re-apply the groups that
        // were not implicated, so one bad suggestion does not cost the
        // others their edits
        for cf in changed do
            writeSource cf.Path cf.Before

        let survivors =
            System.Collections.Generic.Dictionary<string, ResizeArray<int * string * Fix>>(
                StringComparer.OrdinalIgnoreCase
            )

        for kv in editsByFile do
            let kept =
                kv.Value
                |> Seq.filter (fun (g, _, _) -> not (brokenGroups.Contains g))
                |> ResizeArray

            if kept.Count > 0 then
                survivors.[kv.Key] <- kept

        if not (Set.isEmpty brokenScriptGroups) then
            Out.skip
                $"  ({brokenScriptGroups.Count} suggestion(s) put back: the script they rewrote stopped typechecking)"

        if not (Set.isEmpty halfAppliedGroups) then
            Out.skip
                $"  ({halfAppliedGroups.Count} suggestion(s) put back: their edits could not all apply together across files)"

        applyEditGroupsCheckingScripts checker dryRun suppressed brokenElsewhere survivors

let private findScriptCallSites (checker: FSharpChecker) (root: string) (options: FSharpProjectOptions) =
    let searchRoot =
        let full =
            try
                Some(Path.GetFullPath root)
            with _ -> // a glob or otherwise unopenable target; fsharpanalyzer: ignore-line FR0055
                None

        // a glob target ("src/**/*.fsproj") resolves to no directory at all.
        // Falling through to "no scripts" there would silently restore the
        // very hazard this exists to close, so the project's own directory
        // is the floor.
        let projectDir =
            try
                match Path.GetDirectoryName(Path.GetFullPath options.ProjectFileName) with
                | null -> None
                | Exists dir -> Some dir
                | _ -> None
            with _ -> // fsharpanalyzer: ignore-line FR0055
                None

        match full with
        | Some f when Directory.Exists f -> Some f
        | Some f ->
            match Path.GetDirectoryName f with
            | null -> projectDir
            | dir when Directory.Exists dir -> Some dir
            | _ -> projectDir
        | None -> projectDir

    let projectSources =
        System.Collections.Generic.HashSet<string>(
            options.SourceFiles |> Array.map Path.GetFullPath,
            StringComparer.OrdinalIgnoreCase
        )

    let scripts =
        match searchRoot with
        | None -> [||]
        | Some dir ->
            try
                // `ignorePaths` is honoured here DELIBERATELY, and it is not an
                // oversight that it narrows this safety probe: a path the
                // repository has told the tool to ignore is external code, and
                // external code does not get a vote on how this repository's
                // declarations are shaped. Scripts outside the target tree are
                // invisible for the same reason - the search cannot be the
                // whole disk - so the guarantee is scoped to the code this run
                // is actually responsible for, which is the honest scope.
                Directory.EnumerateFiles(dir, "*.fsx", SearchOption.AllDirectories)
                |> Seq.filter (fun f -> not ((isBuildOutput f) || (Configuration.isIgnoredPath f)))
                |> Seq.toArray
            with _ -> // an unreadable tree contributes no call sites; fsharpanalyzer: ignore-line FR0055
                [||]

    // `#r "../bin/Debug/net8.0/Lib.dll"`, in any spelling of the path: a
    // textual probe, since the script is not typechecked for this — its
    // calls could not be matched to a declaration if it were
    let referencing =
        let assemblyFile = Text.RegularExpressions.Regex.Escape(outputFileNameOf options)

        let pattern =
            Text.RegularExpressions.Regex(
                "^\\s*#r\\s+@?\"(?:[^\"\\r\\n]*[\\\\/])?" + assemblyFile + "\"",
                Text.RegularExpressions.RegexOptions.IgnoreCase
                ||| Text.RegularExpressions.RegexOptions.Multiline
            )

        scripts
        |> Array.filter (fun script ->
            try
                pattern.IsMatch(File.ReadAllText script)
            with
            | :? IOException
            | :? UnauthorizedAccessException -> false)
        |> List.ofArray

    let contexts = ResizeArray()

    let usesByName =
        System.Collections.Generic.Dictionary<string, ResizeArray<FSharpSymbolUse>>()

    let unverifiable =
        System.Collections.Generic.HashSet<string>(StringComparer.OrdinalIgnoreCase)

    for script in scripts do
        let info = readScript checker script
        let loaded = info.Loaded |> Array.filter projectSources.Contains

        if not (Array.isEmpty loaded) then
            match info.Context with
            | None ->
                Out.skip
                    $"  ({Path.GetFileName script} does not typecheck, so its calls cannot be read; nothing it #loads will be reshaped)"

                for e in info.Errors do
                    Out.dim $"    {e}"

                for f in loaded do
                    unverifiable.Add f |> ignore
            | Some ctx ->
                contexts.Add(script, ctx)

                for u in info.Uses do
                    match symbolFullName u.Symbol with
                    | Some name ->
                        match usesByName.TryGetValue name with
                        | true, existing -> existing.Add u
                        | false, _ ->
                            let fresh = ResizeArray()
                            fresh.Add u
                            usesByName.[name] <- fresh
                    | None ->
                        // A use with no readable full name cannot be matched to
                        // a declaration, so proceeding would migrate one call
                        // site short - the single thing this probe exists to
                        // prevent. It only matters when the use points INTO the
                        // sources this script loads; an unnameable symbol from
                        // a referenced library is nothing to do with us.
                        let pointsAtLoaded =
                            match u.Symbol.DeclarationLocation with
                            | Some d ->
                                let declared =
                                    try
                                        Some(Path.GetFullPath d.FileName)
                                    with _ -> // fsharpanalyzer: ignore-line FR0055
                                        None

                                match declared with
                                | Some df ->
                                    loaded
                                    |> Array.exists (fun f -> String.Equals(f, df, StringComparison.OrdinalIgnoreCase))
                                | None -> false
                            | None -> false

                        if pointsAtLoaded then
                            for f in loaded do
                                unverifiable.Add f |> ignore

    let byName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()

    for kv in usesByName do
        byName.[kv.Key] <- kv.Value.ToArray()

    { Contexts = List.ofSeq contexts
      UsesByFullName = byName
      Unverifiable = unverifiable
      ReferencingScripts = referencing }

/// One sibling project's compilation, read for the api pass: the project
/// references the one being analyzed, so its sources are call sites of
/// that project's public declarations (and of its internal ones, when
/// InternalsVisibleTo names the sibling).
type private SiblingInfo =
    {
        Project: string
        /// The sibling's own compiler arguments, with the analyzed project
        /// referenced IN MEMORY (see readSibling) — the options the
        /// post-apply recheck uses again.
        Options: FSharpProjectOptions
        /// The sibling's sources, parsed with ITS parsing options, so a
        /// call-site edit can be rendered in them.
        Contexts: (string * FileContext) list
        /// Uses inside the sibling's own files.
        Uses: FSharpSymbolUse[]
        /// The first errors of a sibling that does not typecheck — the
        /// reason beside the verdict. Non-empty means unreadable.
        Errors: string list
    }

/// What the sibling projects of the run contribute to one project's api
/// pass, in the same shape as ScriptCallSites and folded into the same
/// `Outside` the rules read.
type private SiblingCallSites =
    {
        /// Parse contexts of every sibling read, for the file lookup.
        Contexts: (string * FileContext) list
        /// Uses inside the siblings, indexed by the symbol's full name.
        UsesByFullName: System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>
        /// Was every project that can see this project's PUBLIC
        /// declarations read — a workspace enumerated, every referencing
        /// project an F# one that typechecked?
        PublicRead: bool
        /// Has the project building the assembly of this name been read,
        /// or can it not see this project at all? The InternalsVisibleTo
        /// question, by friend name.
        AssemblyRead: string -> bool
        /// The siblings read, for the recheck after edits land in them.
        Read: SiblingInfo list
        /// This project's source files that another workspace project
        /// compiles directly (a `<Compile Include>` link) and that
        /// project could not be read: it holds its own copy of every
        /// declaration in them, with call sites of its own that nothing
        /// reaches, so nothing in such a file is reshaped. A linker that
        /// reads is a sibling like any other, its call sites rewritten.
        UnreadShared: string list
        /// The own files of the linking projects read, lower-cased full
        /// paths: an edit landing there is noted as such on its fix line.
        Linked: Set<string>
    }

/// A sibling's compiler arguments, once per run: they come from MSBuild,
/// which is the expensive half, and do not change as sources are edited.
let private siblingOptionsCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, Result<FSharpProjectOptions, string>>(
        StringComparer.OrdinalIgnoreCase
    )

/// A sibling's typecheck, keyed by (sibling, referenced project): the
/// sibling is checked against THAT project's sources in memory, so one
/// test project referencing three libraries is read three times over —
/// and once per ROUND, since the previous round's edits are what it must
/// now see; the api pass clears this as each round begins. What survives
/// the run is the MSBuild half above.
let private siblingCheckCache =
    System.Collections.Generic.Dictionary<string * string, SiblingInfo>()

/// Read one sibling: MSBuild for its arguments, then a typecheck with the
/// analyzed project referenced IN MEMORY rather than through the dll on
/// disk. Two reasons. The dll is stale the moment a round has rewritten
/// the project (nothing rebuilds it between rounds), and against a stale
/// dll every rewritten call site in the sibling is an error. And a symbol
/// resolved from source carries the declaration's exact position, which
/// is what `sameDeclaration` matches on; the pass would rather not depend
/// on what a dll's metadata says about where its sources were.
///
/// The `-r:` naming the project's output is the one replaced. A sibling
/// whose arguments carry no such reference is not compiled against the
/// project after all — a ProjectReference with ReferenceOutputAssembly
/// false, say — and is reported unreadable rather than assumed harmless.
let private readSibling
    (checker: FSharpChecker)
    (optionsOf: string -> Result<FSharpProjectOptions, string>)
    (project: FSharpProjectOptions)
    /// The sibling compiles some of the project's sources DIRECTLY (a
    /// `<Compile Include="..\Common\X.fs">` link) rather than referencing
    /// the built assembly: its own arguments already carry the sources,
    /// so there is no `-r:` to replace, and the declarations it shares
    /// resolve to the same positions the project's do.
    (linksSources: bool)
    (sibling: string)
    =
    let key =
        Path.GetFullPath(sibling).ToLowerInvariant(), Path.GetFullPath(project.ProjectFileName).ToLowerInvariant()

    match siblingCheckCache.TryGetValue key with
    | true, info -> info
    | false, _ ->
        let unreadable errors =
            { Project = sibling
              Options = project
              Contexts = []
              Uses = [||]
              Errors = errors }

        let info =
            match siblingOptionsCache.GetOrAdd(Path.GetFullPath sibling, (fun p -> optionsOf p)) with
            | Error message -> unreadable [ message ]
            | Ok siblingOptions ->
                let outputFile = outputFileNameOf project

                let referencesProject (arg: string) =
                    arg.StartsWith("-r:", StringComparison.OrdinalIgnoreCase)
                    && String.Equals(Path.GetFileName(arg.Substring 3), outputFile, StringComparison.OrdinalIgnoreCase)

                let inMemory =
                    if linksSources then
                        Some siblingOptions
                    else
                        siblingOptions.OtherOptions
                        |> Array.tryFind referencesProject
                        |> Option.map (fun reference ->
                            { siblingOptions with
                                ReferencedProjects =
                                    [| FSharpReferencedProject.FSharpReference(reference.Substring 3, project) |] })

                match inMemory with
                | None ->
                    unreadable
                        [ $"its compiler arguments carry no reference to {outputFile}, so it cannot be checked against this project" ]
                | Some options ->

                    // the previous round's edits are on disk; FCS must not
                    // answer from the tree it built before them
                    checker.InvalidateConfiguration options
                    let results = checker.ParseAndCheckProject options |> Async.RunSynchronously

                    let errors =
                        results.Diagnostics
                        |> Array.filter (fun d ->
                            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

                    if not (Array.isEmpty errors) then
                        { unreadable (
                              errors
                              |> Array.truncate 2
                              |> Array.map (fun d ->
                                  $"{Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}")
                              |> List.ofArray
                          ) with
                            Options = options }
                    else
                        let projectFiles =
                            System.Collections.Generic.HashSet<string>(
                                project.SourceFiles |> Array.map Path.GetFullPath,
                                StringComparer.OrdinalIgnoreCase
                            )

                        // the sibling's OWN files: a linker compiles the
                        // project's sources as well, and those are the
                        // project pass's business - their call sites come
                        // from the project's compilation, and their trees
                        // from the project's parse
                        let own =
                            System.Collections.Generic.HashSet<string>(
                                options.SourceFiles
                                |> Array.map Path.GetFullPath
                                |> Array.filter (projectFiles.Contains >> not),
                                StringComparer.OrdinalIgnoreCase
                            )

                        let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

                        let contexts =
                            [ for file in options.SourceFiles |> Array.filter (Path.GetFullPath >> own.Contains) do
                                  let sourceText = SourceText.ofString (File.ReadAllText file)

                                  let parsed =
                                      checker.ParseFile(file, sourceText, parsingOptions) |> Async.RunSynchronously

                                  file,
                                  { FileName = file
                                    Source = sourceText
                                    ParseTree = parsed.ParseTree } ]

                        // only uses IN THE SIBLING: the referenced project's
                        // own files are the project pass's business
                        let uses =
                            results.GetAllUsesOfAllSymbols()
                            |> Array.filter (fun u ->
                                not u.IsFromDefinition && own.Contains(Path.GetFullPath u.Range.FileName))

                        // a use of the project's declaration that cannot be
                        // NAMED cannot be matched to it, and might be the
                        // one call site the pass would miss — the same
                        // restraint findScriptCallSites shows a script
                        let unnameable =
                            uses
                            |> Array.exists (fun u ->
                                (symbolFullName u.Symbol).IsNone
                                && (match u.Symbol.DeclarationLocation with
                                    | Some d ->
                                        (try
                                            projectFiles.Contains(Path.GetFullPath d.FileName)
                                         with _ -> // fsharpanalyzer: ignore-line FR0055
                                             false)
                                    | None -> false))

                        { Project = sibling
                          Options = options
                          Contexts = contexts
                          Uses = uses
                          Errors =
                            if unnameable then
                                [ "it uses a declaration of this project that the pass cannot name, so its calls cannot all be matched" ]
                            else
                                [] }

        siblingCheckCache.[key] <- info
        info

/// Index the call sites in the sibling projects that can see this
/// project's declarations — the complement of findScriptCallSites for
/// the callers a `#load` does not explain.
///
/// The workspace is the run's solution, or the nearest one listing the
/// project, or the directory the run was pointed at (Workspace.workspaceOf);
/// its projects referencing this one, directly or through another, are the
/// siblings. Each F# sibling is typechecked and its uses indexed; a
/// sibling in another language, one that does not typecheck, or a
/// workspace that cannot be enumerated at all leaves the public
/// declarations as they are — said once, like the signature-file skip.
let private findSiblingCallSites
    (checker: FSharpChecker)
    (root: string)
    (options: FSharpProjectOptions)
    (optionsOf: string -> Result<FSharpProjectOptions, string>)
    : SiblingCallSites =
    let unread =
        { Contexts = []
          UsesByFullName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()
          PublicRead = false
          AssemblyRead = (fun _ -> false)
          Read = []
          UnreadShared = []
          Linked = Set.empty }

    // a script compilation is nobody's reference target, and the project
    // sources it #loads belong to a project whose other callers this
    // compilation cannot see: nothing public is reshaped from here
    if options.SourceFiles |> Array.exists Visibility.isScriptFile then
        unread
    else
        match Workspace.workspaceOf root options.ProjectFileName with
        | None ->
            Out.dim
                "  (no solution lists this project, so nothing referencing it can be read; public declarations keep their shape)"

            unread
        | Some workspace ->
            let referencers = Workspace.referencersOf workspace options.ProjectFileName

            let foreign, fsharp =
                referencers |> List.partition (Workspace.isFSharpProject >> not)

            if not foreign.IsEmpty then
                let names = foreign |> List.map Path.GetFileName |> String.concat ", "
                let verb = if foreign.Length = 1 then "references" else "reference"

                Out.skip $"  ({names} {verb} this project and cannot be read; public declarations keep their shape)"

            // a project compiling some of this project's sources directly
            // is another compilation of those declarations, read like a
            // referencer: its own files hold call sites of its own copy
            let linkers =
                Workspace.sharedSourcesOf workspace options.ProjectFileName (editableSources options)
                |> List.filter (fun (linker, _) ->
                    Workspace.isFSharpProject linker
                    && not (
                        fsharp
                        |> List.exists (fun r -> String.Equals(r, linker, StringComparison.OrdinalIgnoreCase))
                    ))

            let readOne (linksSources: bool) (sibling: string) (why: string) =
                if not linksSources then
                    Out.dim $"  {Path.GetFileName sibling} {why}; reading its call sites"

                let info = readSibling checker optionsOf options linksSources sibling

                if not info.Errors.IsEmpty then
                    Out.skip
                        $"  ({Path.GetFileName sibling} cannot be read, so its calls cannot be rewritten; declarations it can see keep their shape)"

                    for e in info.Errors do
                        Out.dim $"    {e}"

                info

            let read =
                [ for sibling in fsharp do
                      readOne false sibling "references this project"
                  for linker, _ in linkers do
                      readOne true linker "" ]

            // a linker's own files, for the note on their fix lines
            let linked =
                [ for linker, _ in linkers do
                      let info = readSibling checker optionsOf options true linker

                      for file, _ in info.Contexts do
                          Path.GetFullPath(file).ToLowerInvariant() ]
                |> Set.ofList

            // the shared files of a linker that could not be read: their
            // declarations have call sites nothing can reach
            let unreadShared =
                [ for linker, files in linkers do
                      if not (readSibling checker optionsOf options true linker).Errors.IsEmpty then
                          yield! files ]

            let usesByName =
                System.Collections.Generic.Dictionary<string, ResizeArray<FSharpSymbolUse>>()

            for info in read do
                for u in info.Uses do
                    match symbolFullName u.Symbol with
                    | Some name ->
                        match usesByName.TryGetValue name with
                        | true, existing -> existing.Add u
                        | false, _ ->
                            let fresh = ResizeArray()
                            fresh.Add u
                            usesByName.[name] <- fresh
                    | None -> ()

            let byName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()

            for kv in usesByName do
                byName.[kv.Key] <- kv.Value.ToArray()

            let readable = read |> List.filter (fun info -> info.Errors.IsEmpty)

            let verified =
                readable
                |> List.map (fun info -> Workspace.assemblyNameOf info.Project)
                |> Set.ofList

            // a workspace project that does not reference this one cannot
            // call it, friend or not
            let unreferencing =
                workspace
                |> List.filter (fun p ->
                    not (
                        referencers
                        |> List.exists (fun r -> String.Equals(r, p, StringComparison.OrdinalIgnoreCase))
                    )
                    && not (
                        String.Equals(
                            Path.GetFullPath p,
                            Path.GetFullPath options.ProjectFileName,
                            StringComparison.OrdinalIgnoreCase
                        )
                    ))
                |> List.map Workspace.assemblyNameOf
                |> Set.ofList

            { Contexts = readable |> List.collect (fun info -> info.Contexts)
              UsesByFullName = byName
              PublicRead = foreign.IsEmpty && read.Length = readable.Length
              AssemblyRead =
                (fun name ->
                    verified
                    |> Set.exists (fun v -> String.Equals(v, name, StringComparison.OrdinalIgnoreCase))
                    || unreferencing
                       |> Set.exists (fun v -> String.Equals(v, name, StringComparison.OrdinalIgnoreCase)))
              Read = readable
              UnreadShared = unreadShared
              Linked = linked }

/// The linkers alone, for the channel the ANALYZERS read: the FR0069,
/// FR0093 and FR0049 migrations reshape `internal` declarations
/// project-wide, and a project compiling this project's sources directly
/// holds those declarations as its own internals, with call sites in its
/// own files. Read like a sibling (cached with them), its uses are folded
/// into the same `Outside` a #loading script's are, and the shared files
/// of a linker that cannot be read are unreadable exactly as a file a
/// broken script #loads is. Referencers are not read here: they see only
/// public declarations, which those migrations never touch.
let private findLinkerCallSites
    (checker: FSharpChecker)
    (root: string)
    (options: FSharpProjectOptions)
    (optionsOf: string -> Result<FSharpProjectOptions, string>)
    : (string * FileContext) list * System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]> * string list =
    let byName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()

    if options.SourceFiles |> Array.exists Visibility.isScriptFile then
        [], byName, []
    else
        match Workspace.workspaceOf root options.ProjectFileName with
        | None -> [], byName, []
        | Some workspace ->
            let linkers =
                Workspace.sharedSourcesOf workspace options.ProjectFileName (editableSources options)
                |> List.filter (fst >> Workspace.isFSharpProject)

            let read =
                [ for linker, files in linkers -> files, readSibling checker optionsOf options true linker ]

            let usesByName =
                System.Collections.Generic.Dictionary<string, ResizeArray<FSharpSymbolUse>>()

            for _, info in read do
                for u in info.Uses do
                    match symbolFullName u.Symbol with
                    | Some name ->
                        match usesByName.TryGetValue name with
                        | true, existing -> existing.Add u
                        | false, _ ->
                            let fresh = ResizeArray()
                            fresh.Add u
                            usesByName.[name] <- fresh
                    | None -> ()

            for kv in usesByName do
                byName.[kv.Key] <- kv.Value.ToArray()

            let contexts = read |> List.collect (fun (_, info) -> info.Contexts)

            let unreadable =
                read
                |> List.collect (fun (files, info) -> if info.Errors.IsEmpty then [] else files)

            contexts, byName, unreadable

/// The API-CHANGING pass: project-wide refactorings whose edits cross file
/// boundaries — currying internal/public tupled functions (FR0090) and
/// reordering their parameters (FR0091), rewriting every call site in the
/// project. Runs only under --api-changes, BEFORE the normal passes so
/// they can polish the result. A project carrying signature files skips
/// the pass: the .fsi would need the same change.
///
/// A suggestion is atomic: its definition edit and every call-site edit
/// apply together or not at all — a call site left in the old shape while
/// the definition changes would not compile. When two suggestions collide
/// (a call to one inside a call tuple of another) the later one is held
/// back whole, and the caller's iteration picks it up on the next round.
///
/// The call sites are not all in the project. `#load`ing scripts and the
/// sibling projects that reference this one (findScriptCallSites,
/// findSiblingCallSites) are read first, their uses handed to the rules
/// as the `Outside` of this compilation, and their files supplied to the
/// same lookup the project's own go through, so an edit lands in a test
/// project's file exactly as it lands in a second file of the project —
/// and in the same group, so a sibling edit and the definition edit are
/// one all-or-nothing decision. What could not be read holds the
/// declarations it can see in their present shape.
let private runApiPass
    (checker: FSharpChecker)
    (options: FSharpProjectOptions)
    /// Call sites in #loading scripts, which the project compilation
    /// cannot see.
    (scriptSites: ScriptCallSites)
    /// Call sites in the sibling projects that reference this one, which
    /// the project compilation cannot see either. Lazy: the reading costs
    /// an MSBuild evaluation and a typecheck per referencing project (22
    /// of them, seven minutes, on SQLProvider.Common), and is asked for
    /// only once a file holds a tupled definition worth reshaping.
    (siblingSites: Lazy<SiblingCallSites>)
    (codes: Set<string> option)
    (dryRun: bool)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    =
    if options.SourceFiles |> Array.exists (fun f -> f.EndsWith ".fsi") then
        Out.skip "  (api pass skipped: signature files would need the same changes)"
        0, []
    else
        let wanted (file: string) (code: string) (name: string) =
            codes |> Option.forall (fun allowed -> allowed.Contains code)
            && Configuration.isRuleEnabled file code name

        for script in scriptSites.ReferencingScripts do
            Out.skip
                $"  ({Path.GetFileName script} #r's this project's built assembly, so its calls cannot be matched to the sources; public declarations keep their shape)"

        let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously

        let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

        let fileContexts =
            System.Collections.Generic.Dictionary<string, Text.FileContext>(StringComparer.OrdinalIgnoreCase)

        for file in options.SourceFiles do
            let sourceText = SourceText.ofString (File.ReadAllText file)

            let parsed =
                checker.ParseFile(file, sourceText, parsingOptions) |> Async.RunSynchronously

            fileContexts.[Path.GetFullPath file] <-
                { FileName = file
                  Source = sourceText
                  ParseTree = parsed.ParseTree }

        // a #loading script or a sibling's source is looked up exactly like
        // a project file: its edits are rendered from its own parse tree
        // and source
        for script, ctx in scriptSites.Contexts do
            fileContexts.[Path.GetFullPath script] <- ctx

        // a sibling's files arrive with the reading, when a rule first
        // asks for a file the project does not hold
        let fileLookup (name: string) =
            match fileContexts.TryGetValue(Path.GetFullPath name) with
            | true, ctx -> Some ctx
            | false, _ ->
                siblingSites.Value.Contexts
                |> List.tryFind (fun (file, _) ->
                    String.Equals(Path.GetFullPath file, Path.GetFullPath name, StringComparison.OrdinalIgnoreCase))
                |> Option.map snd

        let suggestions = ResizeArray<ApiSuggestion>()

        /// The uses the other compilations contribute for this symbol,
        /// matched by full name because each compiled it separately, then
        /// by declaration because a name is not identity.
        let usesIn (index: System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>) (symbol: FSharpSymbol) =
            match symbolFullName symbol with
            | Some name ->
                match index.TryGetValue name with
                | true, uses -> uses |> Array.filter (fun u -> sameDeclaration symbol u.Symbol)
                | false, _ -> [||]
            | None -> [||]

        let outside: Visibility.Outside =
            { Uses =
                (fun symbol ->
                    Array.append
                        (usesIn scriptSites.UsesByFullName symbol)
                        (usesIn siblingSites.Value.UsesByFullName symbol))
              // a script compiled against the dll is a caller of the public
              // declarations the sibling reading cannot vouch for
              PublicRead = (fun () -> scriptSites.ReferencingScripts.IsEmpty && siblingSites.Value.PublicRead)
              AssemblyRead = (fun name -> siblingSites.Value.AssemblyRead name) }

        // a file a broken script #loads is left alone entirely: we cannot
        // read that script's calls, and reshaping blind is how it broke
        // - and so is a vendored or generated file the sweep would not touch
        let reshapable =
            editableSources options
            |> Array.filter (Path.GetFullPath >> scriptSites.Unverifiable.Contains >> not)

        // and a file another project compiles directly when THAT project
        // could not be read: its own call sites are out of reach. Asked of
        // a file only once a rule found something in it, which is when the
        // sibling reading has been paid for anyway
        let inUnreadShared (file: string) =
            siblingSites.Value.UnreadShared
            |> List.exists (fun shared ->
                String.Equals(Path.GetFullPath shared, Path.GetFullPath file, StringComparison.OrdinalIgnoreCase))

        for file in reshapable do
            let ctx = fileContexts.[Path.GetFullPath file]

            let _, checkAnswer =
                checker.ParseAndCheckFileInProject(file, 0, ctx.Source, options)
                |> Async.RunSynchronously

            match checkAnswer with
            | FSharpCheckFileAnswer.Succeeded checkResults ->
                if wanted file "FR0090" "TupleParams" then
                    for s in
                        TupleParams.findApiChanges ctx checkResults projectResults fileLookup outside
                        |> List.filter (fun _ -> not (inUnreadShared file)) do
                        suggestions.Add
                            { Code = "FR0090"
                              FunctionName = s.FunctionName
                              Edits = s.Edits |> List.map (fun e -> e.Range, e.Original, e.Replacement) }

                if wanted file "FR0091" "ParamOrder" then
                    for s in
                        ParamOrder.findApiChanges ctx checkResults projectResults fileLookup outside
                        |> List.filter (fun _ -> not (inUnreadShared file)) do
                        suggestions.Add
                            { Code = "FR0091"
                              FunctionName = s.FunctionName
                              Edits = s.Edits }
            | FSharpCheckFileAnswer.Aborted -> ()

        let editsByFile =
            System.Collections.Generic.Dictionary<string, ResizeArray<int * string * Fix>>(
                StringComparer.OrdinalIgnoreCase
            )

        // one group per suggestion; within a FILE its edits then apply all
        // or nothing (a cross-file suggestion still applies per file)
        let mutable nextGroup = 0

        let acceptedRanges =
            System.Collections.Generic.Dictionary<string, ResizeArray<Range>>(StringComparer.OrdinalIgnoreCase)

        let overlapsAccepted (r: Range) =
            match acceptedRanges.TryGetValue(Path.GetFullPath r.FileName) with
            | true, ranges ->
                ranges
                |> Seq.exists (fun a ->
                    Range.rangeContainsPos a r.Start
                    || Range.rangeContainsPos a r.End
                    || Range.rangeContainsRange r a)
            | false, _ -> false

        for s in suggestions do
            if s.Edits |> List.exists (fun (r, _, _) -> overlapsAccepted r) then
                printfn
                    $"  {s.Code} {kindColumn s.Code} {s.FunctionName}: held back this round (edits nest inside another change)"
            else
                // scripts and sibling projects are worth naming: they are
                // the call sites a reader assumes were out of scope, and
                // the ones that used to break
                let inScripts =
                    s.Edits
                    |> List.filter (fun (r, _, _) -> r.FileName.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase))
                    |> List.length

                let inSiblings =
                    s.Edits
                    |> List.filter (fun (r, _, _) ->
                        siblingSites.Value.Contexts
                        |> List.exists (fun (file, _) ->
                            String.Equals(
                                Path.GetFullPath file,
                                Path.GetFullPath r.FileName,
                                StringComparison.OrdinalIgnoreCase
                            )))
                    |> List.length

                let elsewhereNote =
                    [ if inScripts > 0 then
                          $"{inScripts} of them in scripts"
                      if inSiblings > 0 then
                          $"{inSiblings} of them in referencing projects" ]
                    |> function
                        | [] -> ""
                        | notes -> " (" + String.concat ", " notes + ")"

                printfn
                    $"  {s.Code} {kindColumn s.Code} {s.FunctionName}: {s.Edits.Length} edit(s) across the project{elsewhereNote}"

                nextGroup <- nextGroup + 1

                for range, original, replacement in s.Edits do
                    let target = Path.GetFullPath range.FileName

                    let fix =
                        { FromRange = range
                          FromText = original
                          ToText = replacement }

                    match editsByFile.TryGetValue target with
                    | true, existing -> existing.Add(nextGroup, s.Code, fix)
                    | false, _ ->
                        let fresh = ResizeArray()
                        fresh.Add(nextGroup, s.Code, fix)
                        editsByFile.[target] <- fresh

                    match acceptedRanges.TryGetValue target with
                    | true, ranges -> ranges.Add range
                    | false, _ ->
                        let fresh = ResizeArray()
                        fresh.Add range
                        acceptedRanges.[target] <- fresh

        /// Once the edits are on disk, every sibling read is typechecked
        /// again — against the project's rewritten sources, through the
        /// same in-memory reference. A sibling with an error now is one
        /// this pass broke: it typechecked when it was read, or it would
        /// not have been. The groups that edited it go back; when none
        /// did, every group of the round does, since the definition edit
        /// alone then broke a call the reading missed. The sibling's own
        /// turn in the run would build it too, but that is a report, not
        /// a rollback, and comes after the project was left rewritten.
        let siblingsBroken (changed: AppliedFile list) =
            if
                changed.IsEmpty
                || not siblingSites.IsValueCreated
                || siblingSites.Value.Read.IsEmpty
            then
                Set.empty
            else
                checker.InvalidateConfiguration options

                let groupsIn (files: AppliedFile list) =
                    files |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g))

                siblingSites.Value.Read
                |> List.collect (fun info ->
                    checker.InvalidateConfiguration info.Options
                    let results = checker.ParseAndCheckProject info.Options |> Async.RunSynchronously

                    let errors =
                        results.Diagnostics
                        |> Array.filter (fun d ->
                            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

                    if Array.isEmpty errors then
                        []
                    else
                        let own =
                            info.Options.SourceFiles
                            |> Array.map (fun f -> Path.GetFullPath(f).ToLowerInvariant())
                            |> Set.ofArray

                        let touched =
                            changed
                            |> List.filter (fun cf -> own.Contains(Path.GetFullPath(cf.Path).ToLowerInvariant()))

                        let blamed =
                            (if touched.IsEmpty then
                                 groupsIn changed
                             else
                                 groupsIn touched)
                            |> List.distinct

                        Out.skip
                            $"  ({Path.GetFileName info.Project} stopped typechecking after the edits: {blamed.Length} suggestion(s) put back)"

                        for d in errors |> Array.truncate 2 do
                            Out.dim $"    {Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"

                        blamed)
                |> Set.ofList

        linkedFiles.Clear()

        if siblingSites.IsValueCreated then
            linkedFiles.UnionWith siblingSites.Value.Linked

        try
            applyEditGroupsCheckingScripts checker dryRun suppressed siblingsBroken editsByFile
        finally
            linkedFiles.Clear()

/// One analyze-and-apply pass over every file. Returns the number of fixes
/// applied.
/// The project's OWN guard constant for dual-framework capability fixes:
/// a DefineConstants value whose $(TargetFramework) conditions cover
/// modern frameworks and none of the legacy ones — SQLProvider's
///
///     <DefineConstants Condition=" '$(TargetFramework)' == 'netstandard2.1'
///         Or '$(TargetFramework)' == 'net8.0' ...">NETSTANDARD21</DefineConstants>
///
/// says "NETSTANDARD21 marks the net6+-capable half", so #if blocks are
/// written in the project's own vocabulary. Both condition placements are
/// read (on the element, or on its PropertyGroup); only conditions built
/// purely from '$(TargetFramework)' == '...' comparisons joined by Or are
/// trusted — anything fancier is ignored. No usable constant means no
/// dual emission at all: nothing is invented.
let private chooseDualConstant (projectPath: string) (modern: string list) (legacy: string list) : string option =
    try
        let text = File.ReadAllText projectPath

        let tfmsOf (condition: string) =
            let comparisons =
                System.Text.RegularExpressions.Regex.Matches(condition, "'\\$\\(TargetFramework\\)'\\s*==\\s*'([^']+)'")

            if comparisons.Count = 0 || condition.Contains "!=" then
                None
            else
                // strip the recognized comparisons; only Or, parens and
                // whitespace may remain, or the condition is too clever
                let stripped =
                    System.Text.RegularExpressions.Regex.Replace(
                        condition,
                        "'\\$\\(TargetFramework\\)'\\s*==\\s*'[^']+'",
                        ""
                    )

                let leftovers =
                    System.Text.RegularExpressions.Regex.Replace(stripped, "(?i)\\bOr\\b|[()\\s]", "")

                if leftovers = "" then
                    Some [ for m in comparisons -> m.Groups.[1].Value ]
                else
                    None

        let definedOn =
            System.Collections.Generic.Dictionary<string, System.Collections.Generic.HashSet<string>>()

        // constants also defined SOMEWHERE we cannot resolve to a framework
        // set — an unconditioned <DefineConstants>$(DefineConstants);FIREBIRD</...>,
        // a Configuration condition, anything clever. Those may be active on
        // legacy frameworks too, so they are disqualified outright: when the
        // scope cannot be known, the constant is not a candidate
        let tainted = System.Collections.Generic.HashSet<string>()

        for groupMatch in propertyGroupRegex.Matches text do
            let groupCondition = conditionAttributeRegex.Match groupMatch.Groups.[1].Value

            for defineMatch in defineElementRegex.Matches groupMatch.Groups.[2].Value do
                let elementCondition = conditionAttributeRegex.Match defineMatch.Groups.[1].Value

                let condition =
                    if elementCondition.Success then
                        elementCondition.Groups.[1].Value
                    elif groupCondition.Success then
                        groupCondition.Groups.[1].Value
                    else
                        ""

                let constants =
                    [ for c in defineMatch.Groups.[2].Value.Split ';' do
                          let c = c.Trim()

                          if c <> "" && not (c.Contains "$(") then
                              c ]

                match (if condition = "" then None else tfmsOf condition) with
                | None ->
                    for constant in constants do
                        tainted.Add constant |> ignore
                | Some tfms ->
                    for constant in constants do
                        match definedOn.TryGetValue constant with
                        | true, existing -> existing.UnionWith tfms
                        | false, _ -> definedOn.[constant] <- System.Collections.Generic.HashSet tfms

        // only framework-SHAPED names qualify (NETSTANDARD21, NET8, net80):
        // a flavor constant like MICROSOFTSQL or LOGARY5 may share the exact
        // TFM condition in this fsproj, but its meaning is the flavor, and a
        // sibling project compiling the same shared file can define it
        // unconditionally — legacy included — turning our #if into a break.
        // The trailing digits are required: SQLProvider's bare NETSTANDARD
        // is a fossil of netstandard-vs-net451 days and is nowadays defined
        // everywhere
        let frameworkShaped =
            System.Text.RegularExpressions.Regex @"^(?i)net(standard|coreapp)?[\d_]+$"

        // a name that DENOTES a legacy framework (NET48, NET451, NET481,
        // NETSTANDARD2_0...) can never guard the modern branch, whatever
        // its fsproj conditions say: the SDK implicitly defines exactly
        // that constant during the legacy compilation itself, invisibly
        // to this textual parse, and #if NET48 would then flip the modern
        // branch ON for net48
        let legacyNamed =
            System.Text.RegularExpressions.Regex @"^(?i)(net4\d*|netstandard1[\d_]*|netstandard2_?0|netcoreapp2_?0)$"

        definedOn
        |> Seq.filter (fun kv ->
            // never defined for a legacy framework, never defined anywhere
            // unknowable, framework-shaped without naming a legacy one, and
            // active for at least one of this project's modern frameworks
            not (tainted.Contains kv.Key)
            && frameworkShaped.IsMatch kv.Key
            && not (legacyNamed.IsMatch kv.Key)
            && legacy |> List.forall (kv.Value.Contains >> not)
            && modern |> List.exists kv.Value.Contains)
        |> Seq.sortByDescending (fun kv -> modern |> List.filter kv.Value.Contains |> List.length)
        |> Seq.tryHead
        |> Option.map (fun kv -> kv.Key)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// Do any of the project's sources use conditional compilation? Parsed
/// from the fsproj's own Compile items — cheap, and it fails TOWARD
/// caution: wildcards, imports or an unreadable file all report true, so
/// the full framework-by-framework sweep still happens. Only a plainly
/// #if-free project earns the single-framework fast path (its other
/// frameworks are still verified by the final all-frameworks build).
let private sourcesUseConditionals (projectPath: string) =
    try
        let dir = Path.GetDirectoryName(Path.GetFullPath projectPath)
        let projText = File.ReadAllText projectPath

        let includes =
            System.Text.RegularExpressions.Regex.Matches(projText, "Compile\\s+Include=\"([^\"]+)\"")
            |> Seq.map (fun m -> m.Groups.[1].Value)
            |> List.ofSeq

        if includes.IsEmpty || includes |> List.exists (fun i -> i.Contains '*') then
            true // items come from elsewhere or globs: assume conditionals
        else
            includes
            |> List.exists (fun rel ->
                let path = Path.Combine(dir, rel)
                not (File.Exists path) || (File.ReadAllText path).Contains "#if")
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        true

/// (lowercased full path, conditional-defines key) pairs already swept in
/// THIS run. Shared-source solutions compile the same file into many
/// projects; under identical defines the parse tree is identical, its
/// fixes are already applied, and re-sweeping it is pure cost. Registered
/// per file only when its TARGET completes (intra-target passes must
/// re-sweep, because a pass-1 fix can enable a pass-2 one); cleared at
/// the start of each run.
let private sweptFiles = System.Collections.Generic.HashSet<string * string>()

/// Fixes applied anywhere in this run so far — the whole-compilation skip
/// is only sound while the tree is untouched (or the run is a dry run).
let mutable internal runTotalApplied = 0

/// Compilations this run attempted — a multi-targeted project contributes
/// one per framework, which is what the coverage warning counts against.
let mutable internal runCompilations = 0

/// Compilations this run could not analyse because they would not build.
/// The exit code already reflects them, but a HUMAN reads the tail of the
/// output, and the per-project errors scroll past long before it: a
/// SwaggerProvider clone missing its paket restore failed 7 of 10
/// compilations and still signed off with a cheerful finding count. A
/// silent gap in coverage reads exactly like clean code.
let mutable internal runBuildFailures = 0

/// A source file with no `#if` in it parses identically under EVERY
/// define set, so one sweep covers all frameworks and all projects — the
/// key degrades to "". Files carrying directives keep the exact-defines
/// key. Cached: solutions ask per project.
///
/// Documented limit: identical parse tree does not mean identical TYPED
/// findings — a sibling file's `#if` or a project's different references
/// can change what a typed rule sees. The trade is deliberate: those
/// deltas are rare, the narrowest-first ordering analyses the most
/// restrictive context first, and the alternative is the full N×TFM
/// re-sweep this dedup exists to remove.
let private directiveFreeCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, bool>()

let private isDirectiveFree (path: string) =
    directiveFreeCache.GetOrAdd(
        path,
        fun p ->
            try
                File.ReadLines p |> Seq.forall (fun l -> not (l.TrimStart().StartsWith "#if"))
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false
    )

let private fileSweepKey (definesKeyStr: string) (path: string) =
    if isDirectiveFree path then "" else definesKeyStr

/// Every finding the run surfaced, for the --report SARIF file: fixable or
/// not, applied or held back. Deduplicated because passes re-analyze and a
/// multi-targeted project sweeps the same file once per framework.
/// One surfaced finding, carrying everything a report (or an agent)
/// needs without re-opening the file.
type ReportedFinding =
    {
        File: string
        Code: string
        Message: string
        Severity: Severity
        StartLine: int
        StartColumn: int
        EndLine: int
        EndColumn: int
        /// Does a quick fix exist, or is this a note?
        Fixable: bool
        /// The fix's edits — (startLine, startColumn, endLine, endColumn,
        /// original, replacement) — so a report reader can render or apply
        /// them.
        Fixes: (int * int * int * int * string * string) list
        /// Stable identity across line shifts and sessions: a hash of the
        /// rule code, the file's NAME (not path — checkouts differ), and the
        /// whitespace-normalized source lines around the finding. Two
        /// sessions looking at the same code agree on it; an unrelated edit
        /// elsewhere in the file does not change it.
        Fingerprint: string
        /// The finding's own line(s) with one line of margin.
        Snippet: string
        /// The 1-based first and last line the snippet covers.
        SnippetLines: int * int
        /// The text of the finding's range itself, as the source spells it.
        RegionText: string
    }

/// The fingerprint version key used in SARIF partialFingerprints.
[<Literal>]
let private FingerprintKey = "fsrefContextHash/v1"

let private fingerprintAndSnippet (source: ISourceText) (file: string) (code: string) (r: range) =
    let lineCount = source.GetLineCount()
    let clamp l = max 0 (min (lineCount - 1) l)
    let firstContext = clamp (r.StartLine - 3)
    let lastContext = clamp (r.EndLine + 1)

    let normalized =
        [ for l in firstContext..lastContext -> whitespaceRunRegex.Replace(source.GetLineString(l).Trim(), " ") ]
        |> String.concat "\n"

    let hash =
        use sha = System.Security.Cryptography.SHA256.Create()

        let bytes =
            System.Text.Encoding.UTF8.GetBytes($"{code}|{Path.GetFileName(file).ToLowerInvariant()}|{normalized}")

        (sha.ComputeHash bytes)[..7] |> Array.map (sprintf "%02x") |> String.concat ""

    let snippetFirst = clamp (r.StartLine - 2)
    let snippetLast = clamp r.EndLine

    let snippet =
        [ for l in snippetFirst..snippetLast -> source.GetLineString l ]
        |> String.concat "\n"

    let regionText =
        try
            source.GetSubTextFromRange r
        with _ -> // fsharpanalyzer: ignore-line FR0055
            ""

    hash, snippet, (snippetFirst + 1, snippetLast + 1), regionText

/// Fingerprints an earlier run accepted (--baseline): findings matching
/// them are neither reported nor fixed this run.
let mutable private baselineFingerprints: Set<string> = Set.empty
let mutable private baselineSuppressed = 0

/// Findings a suppression comment silenced this run — never silent
/// silence: the run summary counts them.
let mutable private commentSuppressed = 0

/// Suppression comments the config's "suppressions" policy declined to
/// honor: their findings were reported anyway (though never auto-fixed).
let mutable private suppressionOverridden = 0

/// --honor-suppressions: comments silence everything regardless of the
/// config policy — the CI override.
let mutable private honorAllSuppressions = false

/// --notes: list fix-less advisory notes inline. Off by default — the
/// fixes are the product; held notes are counted per category and
/// summarized at the end (SARIF/JSON always carry them in full).
let mutable private showNotes = false

/// --notes only: findings that carry a fix are dropped before they are
/// reported or applied, so the run is the advisory notes alone.
let mutable private notesOnly = false

/// Category name -> held note count for the run summary.
let private heldNoteCounts = System.Collections.Generic.Dictionary<string, int>()

let private reportedFindings = ResizeArray<ReportedFinding>()

let private reportedKeys = System.Collections.Generic.HashSet<string>()

/// Console notes already shown this run — later passes recompute the same
/// fix-less findings, and printing them once is enough.
let private printedNotes = System.Collections.Generic.HashSet<string>()

/// Every comment in a parse tree, as (range, text) — the guard against
/// fixes that would silently swallow one.
let private commentsIn (parseTree: ParsedInput) (source: ISourceText) =
    let ranges =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(trivia = trivia)) -> trivia.CodeComments
        | ParsedInput.SigFile(ParsedSigFileInput(trivia = trivia)) -> trivia.CodeComments
        |> List.map (fun c ->
            match c with
            | CommentTrivia.LineComment r
            | CommentTrivia.BlockComment r -> r)

    ranges |> List.map (fun r -> r, textOfRange source r)

/// The tool's version as Directory.Build.props set it: the informational
/// version, minus any +sha suffix a source build carries.
let private toolVersion =
    lazy
        (let asm = Reflection.Assembly.GetExecutingAssembly()

         asm.GetCustomAttributes(typeof<Reflection.AssemblyInformationalVersionAttribute>, false)
         |> Array.tryHead
         |> Option.map (fun a -> (a :?> Reflection.AssemblyInformationalVersionAttribute).InformationalVersion)
         |> Option.map (fun v -> v.Split('+').[0])
         |> Option.defaultValue (string (asm.GetName().Version)))

/// When this process started, for the report's invocation record.
let private startedUtc = DateTime.UtcNow

/// The source root every report location is relative to: the repository
/// that holds the target (code scanning matches blobs from the repo root),
/// else the target's own directory, else where the tool ran. Forward
/// slashes, trailing slash.
let private sourceRootOf (target: string) =
    let targetDir =
        try
            let full = Path.GetFullPath target

            if Directory.Exists full then
                full
            else
                Path.GetDirectoryName full
        with _ -> // fsharpanalyzer: ignore-line FR0055
            Directory.GetCurrentDirectory()

    let rec repoRoot (dir: string) depth =
        if depth > 24 || String.IsNullOrEmpty dir then
            None
        elif
            Directory.Exists(Path.Combine(dir, ".git"))
            || File.Exists(Path.Combine(dir, ".git"))
        then
            Some dir
        else
            repoRoot (Path.GetDirectoryName dir) (depth + 1)

    let chosen =
        repoRoot targetDir 0
        |> Option.defaultValue (
            if String.IsNullOrEmpty targetDir then
                Directory.GetCurrentDirectory()
            else
                targetDir
        )

    chosen.Replace('\\', '/').TrimEnd('/') + "/"

/// A file's path relative to the root when it sits under it, else the
/// full path.
let private relativeToRoot (root: string) (file: string) =
    let full = Path.GetFullPath(file).Replace('\\', '/')

    if full.StartsWith(root, StringComparison.OrdinalIgnoreCase) then
        full.Substring root.Length
    else
        full

// Every analyzer speaks at Hint severity — that is the SDK's editor
// channel, not a statement about how much the finding matters — so
// mapping severity alone stamped `note` on all of them and a swallowed
// exception rendered exactly like a redundant paren. The CATEGORY is
// the judgement the rules actually make, so it is what the reports
// carry: correctness earns a warning, the rest stay notes. Nothing
// becomes an error — every finding here is advice about code that
// compiles.
let private reportLevel (code: string) severity =
    match severity with
    | Severity.Error -> "error"
    | Severity.Warning -> "warning"
    | Severity.Info
    | Severity.Hint ->
        // a priority rule is a likely defect whatever its category
        if RuleCatalog.isPriority code then
            "warning"
        else
            match RuleCatalog.categoryOf code with
            | RuleCatalog.Category.Correctness -> "warning"
            | _ -> "note"

let private reportCategory (code: string) =
    RuleCatalog.name (RuleCatalog.categoryOf code)

/// The console message ends in its category tag; the reports carry the
/// category as its own column, so the sentence stands alone there.
let private plainMessage (f: ReportedFinding) =
    let tag = $" [{reportCategory f.Code}]"

    if f.Message.EndsWith tag then
        f.Message.Substring(0, f.Message.Length - tag.Length)
    else
        f.Message

/// SARIF 2.1.0, hand-built with System.Text.Json (no Sarif.Sdk dependency).
/// The layout is the standard's; what makes the file read well is the
/// optional content it allows, all of which is here: a tool.driver with a
/// version and an information link, one rule entry per surfaced code with
/// its description, help link and default level, results carrying
/// ruleIndex, level, a fingerprint, the range's text plus a context
/// region and — where a fix exists — the fix itself as artifactChanges
/// (code scanning renders those as suggested changes), locations under a
/// `%SRCROOT%` base id, an artifact table, an automation id per target,
/// and an invocation record with times and the command line.
let private writeSarifReport (path: string) (target: string) (findings: ReportedFinding seq) =
    let root = sourceRootOf target

    let fileUri (dir: string) =
        Uri(dir.Replace('/', Path.DirectorySeparatorChar)).AbsoluteUri

    let rootUri = fileUri root

    // a location: relative to %SRCROOT% when the file sits under the root,
    // absolute otherwise
    let artifactLocation (file: string) =
        let relative = relativeToRoot root file

        if relative <> Path.GetFullPath(file).Replace('\\', '/') then
            dict [ "uri", box relative; "uriBaseId", box "%SRCROOT%" ]
        else
            dict [ "uri", box (Uri(Path.GetFullPath file).AbsoluteUri) ]

    let regionEntries (startLine, startColumn, endLine, endColumn) =
        [ "startLine", box (max 1 startLine)
          "startColumn", box (startColumn + 1)
          "endLine", box (max 1 endLine)
          "endColumn", box (endColumn + 1) ]

    let region bounds = dict (regionEntries bounds)

    // one entry per rule the run surfaced, in code order: code scanning
    // groups and filters by these, and without them every finding is an
    // opaque id. The description is the catalog's one line; help points at
    // the rule table
    let codes =
        findings |> Seq.map (fun f -> f.Code) |> Seq.distinct |> Seq.sort |> List.ofSeq

    let ruleIndex = codes |> List.mapi (fun i code -> code, i) |> Map.ofList

    let rulesMetadata =
        codes
        |> List.map (fun code ->
            let description = RuleCatalog.describe code
            let category = reportCategory code

            dict
                [ "id", box code
                  "name", box code
                  "shortDescription", box (dict [ "text", box description ])
                  "fullDescription", box (dict [ "text", box $"{description} ({category} rule of fsharp-refactor)" ])
                  "helpUri", box "https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md"
                  "help", box (dict [ "text", box $"See {code} in Rules.md." ])
                  "defaultConfiguration", box (dict [ "level", box (reportLevel code Severity.Hint) ])
                  "properties",
                  box (dict [ "category", box category; "tags", box [ category; "fsharp"; "refactoring" ] ]) ])

    // every file a finding names, once, in path order: the run's artifact
    // table, which results point into by relative uri
    let artifacts =
        findings
        |> Seq.map (fun f -> Path.GetFullPath f.File)
        |> Seq.distinct
        |> Seq.sort
        |> Seq.map (fun file -> dict [ "location", box (artifactLocation file); "roles", box [ "analysisTarget" ] ])
        |> List.ofSeq

    let results =
        [ for f in findings ->
              let snippetStart, snippetEnd = f.SnippetLines

              let entries =
                  [ "ruleId", box f.Code
                    "ruleIndex", box ruleIndex.[f.Code]
                    "level", box (reportLevel f.Code f.Severity)
                    "message", box (dict [ "text", box (plainMessage f) ])
                    // stable across line shifts and sessions; the baseline
                    // mechanism keys on this
                    "partialFingerprints", box (dict [ FingerprintKey, box f.Fingerprint ])
                    "properties", box (dict [ "autoFixable", box f.Fixable; "category", box (reportCategory f.Code) ])
                    "locations",
                    box
                        [ dict
                              [ "physicalLocation",
                                box (
                                    dict
                                        [ "artifactLocation", box (artifactLocation f.File)
                                          // the range itself, with its text
                                          "region",
                                          box (
                                              dict (
                                                  regionEntries (f.StartLine, f.StartColumn, f.EndLine, f.EndColumn)
                                                  @ [ "snippet", box (dict [ "text", box f.RegionText ]) ]
                                              )
                                          )
                                          // the surrounding lines: saves the
                                          // reader (human or agent) one
                                          // file-open per finding
                                          "contextRegion",
                                          box (
                                              dict
                                                  [ "startLine", box snippetStart
                                                    "endLine", box snippetEnd
                                                    "snippet", box (dict [ "text", box f.Snippet ]) ]
                                          ) ]
                                ) ] ] ]

              // the fix as SARIF spells it: code scanning shows it as a
              // suggested change, and any consumer can apply it
              let fixes =
                  match f.Fixes with
                  | [] -> []
                  | edits ->
                      [ "fixes",
                        box
                            [ dict
                                  [ "description", box (dict [ "text", box $"{f.Code}: {RuleCatalog.describe f.Code}" ])
                                    "artifactChanges",
                                    box
                                        [ dict
                                              [ "artifactLocation", box (artifactLocation f.File)
                                                "replacements",
                                                box
                                                    [ for (sl, sc, el, ec, _, text) in edits ->
                                                          dict
                                                              [ "deletedRegion", box (region (sl, sc, el, ec))
                                                                "insertedContent", box (dict [ "text", box text ]) ] ] ] ] ] ] ]

              dict (entries @ fixes) ]

    let invocation =
        dict
            [ "executionSuccessful", box true
              "startTimeUtc", box (startedUtc.ToString("o"))
              "endTimeUtc", box (DateTime.UtcNow.ToString("o"))
              "workingDirectory",
              box (
                  dict [ "uri", box (fileUri (Directory.GetCurrentDirectory().Replace('\\', '/').TrimEnd('/') + "/")) ]
              )
              "commandLine", box (Environment.CommandLine) ]

    // the id code scanning files this run under: one per target, so a
    // repository with several solutions keeps their reports apart
    let automationId =
        let name = Path.GetFileName(target.TrimEnd('\\', '/'))
        let name = if String.IsNullOrEmpty name then "run" else name
        $"fsharp-refactor/{name}/"

    let report =
        dict
            [ "$schema", box "https://json.schemastore.org/sarif-2.1.0.json"
              "version", box "2.1.0"
              "runs",
              box
                  [ dict
                        [ "tool",
                          box (
                              dict
                                  [ "driver",
                                    box (
                                        dict
                                            [ "name", box "fsharp-refactor"
                                              "fullName", box "fsharp-refactor: F# refactoring analyzers and apply tool"
                                              "version", box toolVersion.Value
                                              "semanticVersion", box toolVersion.Value
                                              // the URL the package and --help both publish; this
                                              // one said FSharp.Refactorings, and it is the link
                                              // GitHub code scanning puts in front of users
                                              "informationUri", box "https://github.com/Thorium/fsharp-refactor"
                                              "rules", box rulesMetadata ]
                                    ) ]
                          )
                          "automationDetails", box (dict [ "id", box automationId ])
                          "originalUriBaseIds", box (dict [ "%SRCROOT%", box (dict [ "uri", box rootUri ]) ])
                          "invocations", box [ invocation ]
                          "artifacts", box artifacts
                          "columnKind", box "utf16CodeUnits"
                          "results", box results ] ] ]

    File.WriteAllText(path, JsonSerializer.Serialize(report, JsonSerializerOptions(WriteIndented = true)))

/// CSV, one row per finding, RFC 4180 quoting, UTF-8 with a BOM so Excel
/// opens it as text rather than guessing. The columns are what a
/// spreadsheet triage needs: rule, category, level, file (relative to the
/// source root), the 1-based range, whether a fix exists, the message,
/// and the fingerprint the baseline keys on.
let private writeCsvReport (path: string) (target: string) (findings: ReportedFinding seq) =
    let root = sourceRootOf target

    let cell (text: string) =
        if text.IndexOfAny [| ','; '"'; '\n'; '\r' |] >= 0 then
            "\"" + text.Replace("\"", "\"\"") + "\""
        else
            text

    let row (cells: string list) =
        cells |> List.map cell |> String.concat ","

    let lines =
        seq {
            yield
                row
                    [ "Rule"
                      "Category"
                      "Level"
                      "File"
                      "StartLine"
                      "StartColumn"
                      "EndLine"
                      "EndColumn"
                      "AutoFixable"
                      "Message"
                      "Description"
                      "Fingerprint" ]

            for f in findings do
                yield
                    row
                        [ f.Code
                          reportCategory f.Code
                          reportLevel f.Code f.Severity
                          relativeToRoot root f.File
                          string (max 1 f.StartLine)
                          string (f.StartColumn + 1)
                          string (max 1 f.EndLine)
                          string (f.EndColumn + 1)
                          (if f.Fixable then "yes" else "no")
                          plainMessage f
                          RuleCatalog.describe f.Code
                          f.Fingerprint ]
        }

    File.WriteAllText(path, String.concat "\r\n" lines + "\r\n", Text.UTF8Encoding(true))

/// A self-contained HTML page — no scripts fetched, no stylesheets
/// linked, so it opens from a build artifact or an email attachment. A
/// summary strip (findings, fixes, per-category counts), then the
/// findings grouped by rule, each with its file and range, the message,
/// the source with the range highlighted, and the fix as before/after
/// text. Filter boxes at the top narrow the page by category, level, and
/// fixability without a round trip.
let private writeHtmlReport (path: string) (target: string) (findings: ReportedFinding seq) =
    let root = sourceRootOf target
    let findings = List.ofSeq findings
    let esc (s: string) = Net.WebUtility.HtmlEncode s
    let sb = Text.StringBuilder()
    let line (s: string) = sb.AppendLine s |> ignore

    let byCategory =
        findings
        |> List.countBy (fun f -> reportCategory f.Code)
        |> List.sortBy (fun (category, _) ->
            match RuleCatalog.parse category with
            | Some c -> RuleCatalog.all |> List.findIndex ((=) c)
            | None -> 99)

    let fixable = findings |> List.filter (fun f -> f.Fixable) |> List.length

    let files =
        findings
        |> List.map (fun f -> Path.GetFullPath f.File)
        |> List.distinct
        |> List.length

    let grouped =
        findings
        |> List.groupBy (fun f -> f.Code)
        |> List.sortBy (fun (code, items) ->
            not (RuleCatalog.isPriority code),
            (match RuleCatalog.categoryOf code with
             | RuleCatalog.Category.Correctness -> 0
             | RuleCatalog.Category.Performance -> 1
             | RuleCatalog.Category.Idiom -> 2
             | RuleCatalog.Category.Cosmetic -> 3),
            -items.Length,
            code)

    // the context snippet with the finding's own range wrapped in <mark>:
    // the snippet starts at SnippetLines' first line, and the range's
    // columns are 0-based offsets into its lines
    let highlighted (f: ReportedFinding) =
        let snippetStart, _ = f.SnippetLines
        let lines = f.Snippet.Split '\n'
        let firstIndex = f.StartLine - snippetStart
        let lastIndex = f.EndLine - snippetStart

        let clampCol (text: string) c = max 0 (min text.Length c)

        lines
        |> Array.mapi (fun i text ->
            if i < firstIndex || i > lastIndex || firstIndex < 0 then
                esc text
            else
                let startCol = if i = firstIndex then clampCol text f.StartColumn else 0

                let endCol =
                    if i = lastIndex then
                        clampCol text f.EndColumn
                    else
                        text.Length

                let endCol = max startCol endCol

                esc (text.Substring(0, startCol))
                + "<mark>"
                + esc (text.Substring(startCol, endCol - startCol))
                + "</mark>"
                + esc (text.Substring endCol))
        |> String.concat "\n"

    line "<!DOCTYPE html>"

    line
        "<html lang=\"en\"><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">"

    line $"<title>fsharp-refactor report: {esc (Path.GetFileName(target.TrimEnd('\\', '/')))}</title>"
    line "<style>"

    line
        ":root{--bg:#fff;--fg:#1f2328;--muted:#656d76;--line:#d0d7de;--code:#f6f8fa;--mark:#fff8c5;--warn:#9a6700;--note:#0969da;--del:#ffebe9;--ins:#dafbe1}"

    line
        "@media (prefers-color-scheme:dark){:root{--bg:#0d1117;--fg:#e6edf3;--muted:#8b949e;--line:#30363d;--code:#161b22;--mark:#4d3800;--warn:#d29922;--note:#58a6ff;--del:#3c1618;--ins:#12261e}}"

    line
        "body{margin:0;padding:24px 32px;font:14px/1.5 -apple-system,'Segoe UI',Roboto,Helvetica,Arial,sans-serif;color:var(--fg);background:var(--bg);max-width:1200px}"

    line
        "h1{font-size:22px;margin:0 0 4px}h2{font-size:16px;margin:32px 0 8px;padding-top:12px;border-top:1px solid var(--line)}"

    line ".meta{color:var(--muted);margin-bottom:16px}.meta code{font-size:13px}"
    line ".summary{display:flex;flex-wrap:wrap;gap:12px;margin:16px 0}"
    line ".card{border:1px solid var(--line);border-radius:6px;padding:8px 14px;min-width:96px}"
    line ".card b{display:block;font-size:20px}.card span{color:var(--muted);font-size:12px}"

    line
        ".filters{display:flex;flex-wrap:wrap;gap:16px;margin:12px 0 4px;color:var(--muted)}.filters label{margin-right:8px;cursor:pointer}"

    line ".rule .desc{color:var(--muted);font-weight:normal}"
    line ".finding{border:1px solid var(--line);border-radius:6px;margin:10px 0;overflow:hidden}"
    line ".finding.hidden{display:none}"

    line
        ".head{display:flex;flex-wrap:wrap;gap:8px 16px;align-items:baseline;padding:8px 12px;background:var(--code);border-bottom:1px solid var(--line)}"

    line ".loc{font-family:ui-monospace,SFMono-Regular,Consolas,monospace;font-size:13px}"

    line
        ".lvl{font-size:11px;text-transform:uppercase;letter-spacing:.04em;padding:1px 6px;border-radius:10px;border:1px solid}"

    line ".lvl.warning{color:var(--warn);border-color:var(--warn)}.lvl.note{color:var(--note);border-color:var(--note)}"
    line ".cat{font-size:12px;color:var(--muted)}.msg{padding:8px 12px}"

    line
        "pre{margin:0;padding:10px 12px;font:12.5px/1.45 ui-monospace,SFMono-Regular,Consolas,monospace;overflow-x:auto;white-space:pre;tab-size:4}"

    line "pre.src{border-top:1px solid var(--line)}mark{background:var(--mark);color:inherit;border-radius:2px}"

    line
        ".fix{border-top:1px solid var(--line)}.fix .lbl{padding:4px 12px;font-size:12px;color:var(--muted);background:var(--code)}"

    line "pre.del{background:var(--del)}pre.ins{background:var(--ins)}"
    line ".empty{padding:24px;border:1px dashed var(--line);border-radius:6px;color:var(--muted)}"
    line "footer{margin-top:32px;color:var(--muted);font-size:12px}"
    line "</style></head><body>"

    line "<h1>fsharp-refactor report</h1>"
    let stamp = DateTime.UtcNow.ToString "yyyy-MM-dd HH:mm"

    line
        $"<div class=\"meta\"><code>{esc (Path.GetFullPath target)}</code> · fsharp-refactor {esc toolVersion.Value} · {stamp} UTC · paths relative to <code>{esc root}</code></div>"

    line "<div class=\"summary\">"
    line $"<div class=\"card\"><b>{findings.Length}</b><span>findings</span></div>"
    line $"<div class=\"card\"><b>{fixable}</b><span>auto-fixable</span></div>"
    line $"<div class=\"card\"><b>{grouped.Length}</b><span>rules</span></div>"
    line $"<div class=\"card\"><b>{files}</b><span>files</span></div>"

    for category, count in byCategory do
        line $"<div class=\"card\"><b>{count}</b><span>{esc category}</span></div>"

    line "</div>"

    if findings.IsEmpty then
        line "<div class=\"empty\">No findings. The run surfaced nothing for the enabled rules.</div>"
    else
        line "<div class=\"filters\">"
        line "<span>Category:"

        for category, _ in byCategory do
            line
                $"<label><input type=\"checkbox\" data-filter=\"cat\" value=\"{esc category}\" checked> {esc category}</label>"

        line "</span><span>Level:"

        for level in [ "warning"; "note" ] do
            line $"<label><input type=\"checkbox\" data-filter=\"lvl\" value=\"{level}\" checked> {level}</label>"

        line "</span><span>Auto-fix:"
        line "<label><input type=\"checkbox\" data-filter=\"fix\" value=\"yes\" checked> auto-fixable</label>"
        line "<label><input type=\"checkbox\" data-filter=\"fix\" value=\"no\" checked> advisory only</label>"
        line "</span></div>"

        for code, items in grouped do
            line
                $"<h2 class=\"rule\" id=\"{code}\">{code} <span class=\"desc\">— {esc (RuleCatalog.describe code)}</span> <span class=\"cat\">({items.Length})</span></h2>"

            for f in items |> List.sortBy (fun f -> f.File, f.StartLine, f.StartColumn) do
                let level = reportLevel f.Code f.Severity
                let category = reportCategory f.Code
                let fixFlag = if f.Fixable then "yes" else "no"

                line $"<div class=\"finding\" data-cat=\"{esc category}\" data-lvl=\"{level}\" data-fix=\"{fixFlag}\">"

                line
                    $"<div class=\"head\"><span class=\"loc\">{esc (relativeToRoot root f.File)}:{max 1 f.StartLine}:{f.StartColumn + 1}</span><span class=\"lvl {level}\">{level}</span><span class=\"cat\">{esc category}</span></div>"

                line $"<div class=\"msg\">{esc (plainMessage f)}</div>"
                line $"<pre class=\"src\">{highlighted f}</pre>"

                match f.Fixes with
                | [] -> ()
                | edits ->
                    line "<div class=\"fix\">"

                    for (sl, sc, _, _, original, text) in edits do
                        let verb = if original = "" then "insert" else "fix"
                        line $"<div class=\"lbl\">{verb} at {max 1 sl}:{sc + 1}</div>"

                        if original <> "" then
                            line $"<pre class=\"del\">- {esc original}</pre>"

                        line $"<pre class=\"ins\">+ {esc text}</pre>"

                    line "</div>"

                line "</div>"

        line "<script>"

        line
            "(function(){var boxes=document.querySelectorAll('input[data-filter]');function apply(){var on={};boxes.forEach(function(b){(on[b.dataset.filter]=on[b.dataset.filter]||{})[b.value]=b.checked});document.querySelectorAll('.finding').forEach(function(f){var show=on.cat[f.dataset.cat]&&on.lvl[f.dataset.lvl]&&on.fix[f.dataset.fix];f.classList.toggle('hidden',!show)});document.querySelectorAll('h2.rule').forEach(function(h){var n=h.nextElementSibling,any=false;while(n&&n.tagName!=='H2'){if(n.classList.contains('finding')&&!n.classList.contains('hidden'))any=true;n=n.nextElementSibling}h.style.display=any?'':'none'})}boxes.forEach(function(b){b.addEventListener('change',apply)})})();"

        line "</script>"

    line
        "<footer>Rules are described in <a href=\"https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md\">Rules.md</a>. The same run written as <code>--report findings.sarif</code> uploads to GitHub code scanning.</footer>"

    line "</body></html>"
    File.WriteAllText(path, sb.ToString(), Text.UTF8Encoding(false))

/// --report writes the format its file name asks for: .html/.htm a page,
/// .csv a spreadsheet, anything else (.sarif, .json) SARIF 2.1.0.
let private writeReport (path: string) (target: string) (findings: ReportedFinding seq) =
    match Path.GetExtension(path).ToLowerInvariant() with
    | ".html"
    | ".htm" -> writeHtmlReport path target findings
    | ".csv" -> writeCsvReport path target findings
    | _ -> writeSarifReport path target findings

let private recordForReport (finding: ReportedFinding) =
    lock reportedFindings (fun () ->
        // the same file reaches here under different spellings from the
        // per-framework passes of a multi-targeted project (relative vs
        // full, differing case), so the path is normalized or the report
        // repeats every finding once per framework
        let file =
            try
                Path.GetFullPath(finding.File).ToLowerInvariant()
            with _ -> // fsharpanalyzer: ignore-line FR0055
                finding.File.ToLowerInvariant()

        let key =
            $"{finding.Code}|{file}|{finding.StartLine}|{finding.StartColumn}|{finding.Message}"

        if reportedKeys.Add key then
            reportedFindings.Add finding)

/// The conditional-compilation identity of a compilation: its sorted
/// --define set. Same file, same defines — same tree.
let private definesKey (options: FSharpProjectOptions) =
    options.OtherOptions
    |> Array.filter (fun o -> o.StartsWith "--define:")
    |> Array.sort
    |> String.concat ";"

/// Mark every non-ignored source of a completed target as swept.
let private markSwept (options: FSharpProjectOptions) =
    let key = definesKey options

    for f in options.SourceFiles do
        if not (Configuration.isIgnoredPath f) then
            sweptFiles.Add(Path.GetFullPath(f).ToLowerInvariant(), fileSweepKey key f)
            |> ignore

let private runPass
    (checker: FSharpChecker)
    (options: FSharpProjectOptions)
    (analyzers: MethodInfo list)
    (codes: Set<string> option)
    (dryRun: bool)
    (apiChanges: bool)
    (jobs: int)
    (onlyFile: string option)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    (blockedRuleFile: System.Collections.Generic.HashSet<string * string>)
    =
    let projectSw = Stopwatch.StartNew()
    let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously
    projectSw.Stop()

    // where the wall clock goes, reported at the end of the pass: on a large
    // project typechecking dominates, and knowing that stops people hunting
    // for a slow rule that is not there
    let mutable checkMs = 0L
    let analyzerMs = System.Collections.Generic.Dictionary<string, int64>()

    // every accepted fix, grouped by the file it EDITS: a fix range names
    // its file, so a cross-file (API-changing) rule can edit call sites
    // anywhere in the project — but only under --api-changes. Keys are
    // normalized full paths: two spellings of one file must land in ONE
    // group, or the second write would clobber the first group's edits.
    let editsByFile =
        System.Collections.Generic.Dictionary<string, ResizeArray<int * string * Fix>>(StringComparer.OrdinalIgnoreCase)

    // one group per suggestion (message): its edits apply all or nothing
    let mutable nextGroup = 0

    let mutable crossFileSkipped = 0

    // files FCS could not check cleanly: most rules stay silent on those, so
    // without this a run over a project that does not typecheck would just
    // report nothing and look clean
    let mutable filesWithErrors = 0

    // Typecheck and analyze each file independently, then aggregate in file
    // order. Everything the analyzers share is already safe to touch from
    // several threads (AstIndex keys a ConditionalWeakTable by parse tree,
    // Configuration and HintEngine cache in ConcurrentDictionaries), and
    // FSharpChecker supports concurrent calls. Nothing is written here — the
    // edits are applied afterwards, sequentially.
    let analyzeFile (file: string) =
        async {
            let sourceText = SourceText.ofString (File.ReadAllText file)
            let checkSw = Stopwatch.StartNew()
            let! parseResults, checkAnswer = checker.ParseAndCheckFileInProject(file, 0, sourceText, options)
            checkSw.Stop()

            match checkAnswer with
            | FSharpCheckFileAnswer.Succeeded checkResults ->
                let context: CliContext =
                    { FileName = file
                      SourceText = sourceText
                      ParseFileResults = parseResults
                      CheckFileResults = checkResults
                      TypedTree = checkResults.ImplementationFile
                      CheckProjectResults = projectResults
                      ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
                      // `// fsharpanalyzer: ignore-line FR0031` and friends
                      // (ignore-line-next, ignore-file, ignore-region-start/
                      // end) — the SDK's own suppression comments, honored
                      // here exactly as editors honor them
                      AnalyzerIgnoreRanges = Ignore.getAnalyzerIgnoreRanges parseResults sourceText }

                let timings = ResizeArray<string * int64>()
                let collected = ResizeArray<Message>()

                // bound each analyzer's Async rather than blocking on it:
                // with several files in flight, an Async.RunSynchronously
                // here would tie up a thread-pool thread per job (our own
                // FR0049 flags exactly this, and caught it here)
                for m in analyzers do
                    let sw = Stopwatch.StartNew()

                    let! produced =
                        async {
                            try
                                let work = m.Invoke(null, [| box context |]) :?> Async<Message list>
                                return! work
                            with
                            // an analyzer that throws must not take the run
                            // down, but say so: a silently skipped rule looks
                            // like a clean file
                            | :? TargetInvocationException as ex ->
                                eprintfn $"  (analyzer {m.Name} failed: {ex.InnerException.Message})"
                                return []
                            | :? InvalidCastException as ex ->
                                eprintfn $"  (analyzer {m.Name} has an unexpected signature: {ex.Message})"
                                return []
                        }

                    sw.Stop()
                    timings.Add(m.Name, sw.ElapsedMilliseconds)
                    collected.AddRange produced

                if editorOffers then
                    let editorContext: EditorContext =
                        { FileName = file
                          SourceText = sourceText
                          ParseFileResults = parseResults
                          CheckFileResults = Some checkResults
                          TypedTree = checkResults.ImplementationFile
                          CheckProjectResults = Some projectResults
                          ProjectOptions = context.ProjectOptions
                          AnalyzerIgnoreRanges = context.AnalyzerIgnoreRanges }

                    for m in editorAnalyzers.Value do
                        let! produced =
                            async {
                                try
                                    let work = m.Invoke(null, [| box editorContext |]) :?> Async<Message list>
                                    return! work
                                with
                                | :? TargetInvocationException as ex ->
                                    eprintfn $"  (editor analyzer {m.Name} failed: {ex.InnerException.Message})"
                                    return []
                                | :? InvalidCastException as ex ->
                                    eprintfn $"  (editor analyzer {m.Name} has an unexpected signature: {ex.Message})"
                                    return []
                            }

                        collected.AddRange produced

                    // the CLI wrapper's fix-less note of a finding the editor
                    // wrapper offers a fix for is the same finding: keep the
                    // offer, drop the note
                    let offered =
                        collected
                        |> Seq.filter (fun m -> not m.Fixes.IsEmpty)
                        |> Seq.map (fun m -> $"{m.Code}|{m.Range}")
                        |> Set.ofSeq

                    let kept =
                        collected
                        |> Seq.filter (fun m -> not m.Fixes.IsEmpty || not (offered.Contains $"{m.Code}|{m.Range}"))
                        |> List.ofSeq

                    collected.Clear()
                    collected.AddRange kept

                // a suppressed finding is neither reported nor FIXED — for
                // an apply tool the second half is the important one. Same
                // semantics as the SDK's own filter (which its signature
                // file keeps internal), so editors and this tool agree on
                // what a suppression comment silences
                let isSuppressed (msg: Message) =
                    match context.AnalyzerIgnoreRanges |> Map.tryFind msg.Code with
                    | None -> false
                    | Some ranges ->
                        ranges
                        |> List.exists (function
                            | AnalyzerIgnoreRange.File -> true
                            | AnalyzerIgnoreRange.Range(commentStart, commentEnd) ->
                                msg.Range.StartLine - 1 >= commentStart && msg.Range.EndLine - 1 <= commentEnd
                            | AnalyzerIgnoreRange.NextLine line -> msg.Range.StartLine - 1 = line
                            | AnalyzerIgnoreRange.CurrentLine line -> msg.Range.StartLine = line)

                let toFinding (msg: Message) =
                    let findingFile =
                        if String.IsNullOrEmpty msg.Range.FileName then
                            file
                        else
                            msg.Range.FileName

                    let fingerprint, snippet, snippetLines, regionText =
                        fingerprintAndSnippet sourceText findingFile msg.Code msg.Range

                    { File = findingFile
                      Code = msg.Code
                      Message = msg.Message
                      Severity = msg.Severity
                      StartLine = msg.Range.StartLine
                      StartColumn = msg.Range.StartColumn
                      EndLine = msg.Range.EndLine
                      EndColumn = msg.Range.EndColumn
                      Fixable = not msg.Fixes.IsEmpty
                      Fixes =
                        msg.Fixes
                        |> List.map (fun f ->
                            f.FromRange.StartLine,
                            f.FromRange.StartColumn,
                            f.FromRange.EndLine,
                            f.FromRange.EndColumn,
                            f.FromText,
                            f.ToText)
                      Fingerprint = fingerprint
                      Snippet = snippet
                      SnippetLines = snippetLines
                      RegionText = regionText }

                // whether a comment is honored is the team's call — the
                // config's "suppressions" policy; --honor-suppressions is
                // the CI override that says yes to all of them
                let policy =
                    if honorAllSuppressions then
                        "all"
                    else
                        Configuration.suppressionPolicy file

                let honoredByPolicy (msg: Message) =
                    match policy with
                    | "none" -> false
                    | "no-correctness" -> RuleCatalog.categoryOf msg.Code <> RuleCatalog.Category.Correctness
                    | _ -> true

                let byCode =
                    collected
                    |> Seq.filter (fun msg -> codes |> Option.forall (fun wanted -> wanted.Contains msg.Code))
                    |> List.ofSeq

                let suppressedByComment, live = byCode |> List.partition isSuppressed
                let silenced, overridden = suppressedByComment |> List.partition honoredByPolicy

                if not suppressedByComment.IsEmpty then
                    lock reportedFindings (fun () ->
                        commentSuppressed <- commentSuppressed + silenced.Length
                        suppressionOverridden <- suppressionOverridden + overridden.Length)

                // an overridden comment still REPORTS its finding — the
                // policy says a comment cannot silence this category — but
                // never auto-fixes over someone's explicit comment
                let overriddenAsNotes =
                    overridden
                    |> List.map (fun m ->
                        { m with
                            Fixes = []
                            Message = m.Message + " (suppression comment not honored — \"suppressions\" policy)" })

                // baseline last: a finding an earlier accepted run already
                // carried is neither reported nor FIXED — the ratchet only
                // moves on what is new
                let reportable, baselined =
                    live @ overriddenAsNotes
                    |> Seq.map (fun msg -> msg, toFinding msg)
                    |> List.ofSeq
                    |> List.partition (fun (_, f) -> not (baselineFingerprints.Contains f.Fingerprint))

                if not baselined.IsEmpty then
                    lock reportedFindings (fun () -> baselineSuppressed <- baselineSuppressed + baselined.Length)

                let reportable =
                    if notesOnly then
                        reportable |> List.filter (fun (msg, _) -> msg.Fixes.IsEmpty)
                    else
                        reportable

                for _, finding in reportable do
                    recordForReport finding

                let messages, notes =
                    reportable |> List.map fst |> List.partition (fun msg -> not msg.Fixes.IsEmpty)

                return
                    {| File = file
                       CheckMs = checkSw.ElapsedMilliseconds
                       Timings = List.ofSeq timings
                       HasErrors = OptionModule.hasErrors checkResults
                       Messages = messages
                       Notes = notes
                       Comments = commentsIn parseResults.ParseTree sourceText |}
            | FSharpCheckFileAnswer.Aborted ->
                return
                    {| File = file
                       CheckMs = checkSw.ElapsedMilliseconds
                       Timings = []
                       HasErrors = true
                       Messages = []
                       Notes = []
                       Comments = [] |}
        }

    // naming one source file means analyzing its project — the references
    // and the files before it are what give its names meaning — but
    // sweeping only that file
    let named =
        match onlyFile with
        | Some only ->
            options.SourceFiles
            |> Array.filter (fun f -> String.Equals(Path.GetFullPath f, only, StringComparison.OrdinalIgnoreCase))
        | None -> options.SourceFiles

    // vendored and generated code a compilation nonetheless includes —
    // paket-files above all — is neither analyzed nor typechecked here:
    // fixing someone else's vendored source is churn, and sweeping it in
    // every project that includes it is where multi-project runs go to die
    // partitioned rather than filtered: the skipped names are worth keeping,
    // since a short list says more than a count
    let gitIgnored =
        gitIgnoredFiles (Path.GetDirectoryName options.ProjectFileName) named

    let ignoredFiles, filesToSweep =
        named
        |> Array.partition (fun f ->
            Configuration.isIgnoredPath f
            || gitIgnored.Contains(Path.GetFullPath(f).ToLowerInvariant()))

    // files an earlier compilation of this RUN already swept under the
    // same conditional-compilation defines: same defines, same parse tree,
    // same fixes — which are already applied. Shared-source solutions
    // (twenty projects compiling one Common) pay for each file once.
    let alreadySwept, filesToSweep =
        filesToSweep
        |> Array.partition (fun f ->
            sweptFiles.Contains(Path.GetFullPath(f).ToLowerInvariant(), fileSweepKey (definesKey options) f))

    if ignoredFiles.Length > 0 then
        // a handful of names tells you WHICH file was passed over and lets
        // you judge whether that was right; a long list is just a wall, so
        // past a handful the count carries it alone. Base names only — the
        // paths are long, repetitive, and not what identifies the file
        if ignoredFiles.Length < 9 then
            let names = ignoredFiles |> Array.map Path.GetFileName |> String.concat ", "

            Out.skip $"  ({ignoredFiles.Length} ignored-path or git-ignored file(s) skipped: {names})"
        else
            Out.skip $"  ({ignoredFiles.Length} ignored-path or git-ignored file(s) skipped)"

    if alreadySwept.Length > 0 then
        printfn $"  ({alreadySwept.Length} shared file(s) already swept in an earlier compilation)"

    Out.dimPart $"sweeping {filesToSweep.Length} file(s)... "
    Console.Out.Flush()
    let sweepSw = Stopwatch.StartNew()

    // a heartbeat on stderr: on a big project a sweep is half a minute of
    // silence when the files are clean, which reads as a hang. Stderr so
    // that piped/JSON stdout stays intact
    let sweptCount = ref 0

    let progress () =
        let n = System.Threading.Interlocked.Increment sweptCount

        if n % 25 = 0 then
            Out.dimPartErr $"[{n}/{filesToSweep.Length}] "

    let outcomes =
        filesToSweep
        |> Array.map (fun file ->
            async {
                let! outcome = analyzeFile file
                progress ()
                return outcome
            })
        |> fun work -> Async.Parallel(work, maxDegreeOfParallelism = jobs)
        |> Async.RunSynchronously

    sweepSw.Stop()

    // Async.Parallel preserves input order, so the fix listing stays in file
    // order and a run is reproducible regardless of how the work interleaved
    for outcome in outcomes do
        checkMs <- checkMs + outcome.CheckMs

        if outcome.HasErrors then
            filesWithErrors <- filesWithErrors + 1

        for name, ms in outcome.Timings do
            analyzerMs.[name] <-
                (match analyzerMs.TryGetValue name with
                 | true, existing -> existing
                 | false, _ -> 0L)
                + ms

        // fix-less findings (FR0055, FR0028...) have no edit to apply — the
        // note IS the rule's entire output. Counted once per run; the wall
        // of advice is opt-in: the fixes are the product, and a screen of
        // structural homework after them is an anticlimax nobody reads.
        // --notes lists them, --report/--format json always carry them
        for note in outcome.Notes do
            let key =
                $"{note.Code}|{outcome.File}|{note.Range.StartLine}|{note.Range.StartColumn}|{note.Message}"

            if printedNotes.Add key then
                if
                    showNotes
                    || RuleCatalog.isPriority note.Code
                    || note.Severity = Severity.Warning
                then
                    let firstSentence =
                        let text = note.Message
                        // a bare '.' is not a sentence end — "String.Equals"
                        // must survive the cut
                        let cutAt =
                            [ text.IndexOf ". "; text.IndexOf ".\n"; text.IndexOf '\n' ]
                            |> List.filter (fun i -> i >= 0)

                        match cutAt with
                        | [] -> text
                        | cuts -> text.Substring(0, List.min cuts + 1)

                    Out.note
                        $"  {note.Code} {kindColumn note.Code} {Path.GetFileName outcome.File}({note.Range.StartLine},{note.Range.StartColumn}) note: {firstSentence}"
                else
                    let kind = RuleCatalog.name (RuleCatalog.categoryOf note.Code)

                    lock heldNoteCounts (fun () ->
                        heldNoteCounts.[kind] <-
                            (match heldNoteCounts.TryGetValue kind with
                             | true, n -> n
                             | false, _ -> 0)
                            + 1)

        // depends only on the file under analysis, so it is computed once
        // rather than per fix: a sweep applies thousands of them
        let companionSignature =
            try
                Path.GetFullPath(Path.ChangeExtension(outcome.File, ".fsi"))
            with _ -> // fsharpanalyzer: ignore-line FR0055
                ""

        // a fix whose span contains a comment the replacement does not carry
        // would silently DELETE it — a match collapsed to one line takes its
        // Note1/Note2 lines with it. Held back instead: the reader's notes
        // outrank our rewrite
        // MESSAGE-level, not fix-level: a compound fix may MOVE code — a
        // remove whose ToText is empty paired with an insert that carries
        // the text (FR0116's extraction). A comment inside any fix's span
        // is only lost when NO fix of the same message re-emits it
        let losesComment (siblingToTexts: string list) (f: Fix) =
            // only consulted for same-file fixes, so the comment list and
            // the range coordinates already speak about the same file
            outcome.Comments
            |> List.exists (fun (r: range, text: string) ->
                Range.rangeContainsRange f.FromRange r
                && not (siblingToTexts |> List.exists (fun t -> t.Contains text)))

        for msg in outcome.Messages do
            nextGroup <- nextGroup + 1

            for f in msg.Fixes do
                let target =
                    Path.GetFullPath(
                        if String.IsNullOrEmpty f.FromRange.FileName then
                            outcome.File
                        else
                            f.FromRange.FileName
                    )

                // a fix landing in this file's own COMPANION SIGNATURE is not
                // a cross-file change. It is the other half of a single edit —
                // naming a union case's fields in the .fs while the .fsi still
                // declares them unnamed does not compile — so gating it behind
                // --api-changes would apply one half and roll the pair back.
                let sameFile =
                    String.Equals(target, Path.GetFullPath outcome.File, StringComparison.OrdinalIgnoreCase)
                    || (companionSignature <> ""
                        && String.Equals(target, companionSignature, StringComparison.OrdinalIgnoreCase))

                // a cross-file fix guards against the TARGET file's comments,
                // parsed through ProjectSources — the same rule as same-file
                let losesCrossFileComment () =
                    match ProjectSources.tryParse target with
                    | Some(targetTree, targetSource) ->
                        Text.commentsWithText targetTree targetSource
                        |> List.exists (fun (r, text) ->
                            Range.rangeContainsRange f.FromRange r
                            && not (msg.Fixes |> List.exists (fun sibling -> sibling.ToText.Contains text)))
                    | None -> false

                if
                    (sameFile && losesComment [ for sibling in msg.Fixes -> sibling.ToText ] f)
                    || (not sameFile && apiChanges && losesCrossFileComment ())
                then
                    // a comment inside the span is information the rewrite
                    // would delete, and code that carries one is already
                    // good F#. Nothing is wrong and nothing is deferred, so
                    // there is nothing to say: this is not a held-back fix,
                    // it is simply not a fix.
                    ()
                // a rule the divergence guard blocked in this file: it kept
                // re-firing pass after pass while the file GREW — the
                // signature of a fix feeding on its own output
                elif blockedRuleFile.Contains(msg.Code, target) then
                    ()
                elif sameFile || apiChanges then
                    match editsByFile.TryGetValue target with
                    | true, existing -> existing.Add(nextGroup, msg.Code, f)
                    | false, _ ->
                        let fresh = ResizeArray()
                        fresh.Add(nextGroup, msg.Code, f)
                        editsByFile.[target] <- fresh
                else
                    crossFileSkipped <- crossFileSkipped + 1

    if crossFileSkipped > 0 then
        Out.skip $"  ({crossFileSkipped} cross-file fix(es) held back — rerun with --api-changes to apply them)"

    if filesWithErrors > 0 then
        eprintfn
            $"  ({filesWithErrors} of {filesToSweep.Length} file(s) have type errors; most rules stay silent on those)"

    let totalAnalyzerMs = analyzerMs.Values |> Seq.sum

    // the per-file and analyzer figures are summed across threads, so they
    // add up to more than the sweep's wall clock — that gap IS the parallelism
    Out.dim
        $"  timing: project check {projectSw.ElapsedMilliseconds} ms, file sweep {sweepSw.ElapsedMilliseconds} ms wall"

    Out.dim $"          (summed across threads: checks {checkMs} ms, analyzers {totalAnalyzerMs} ms)"

    let slowest =
        analyzerMs
        |> Seq.sortByDescending (fun kv -> kv.Value)
        |> Seq.truncate 5
        |> Seq.map (fun kv -> $"{kv.Key} {kv.Value}ms")
        |> String.concat ", "

    if slowest <> "" then
        Out.dim $"  slowest analyzers: {slowest}"

    // the normal pass edits nothing outside the project but scripts, which
    // are checked above; it has no sibling compilations to answer for
    applyEditGroupsCheckingScripts checker dryRun suppressed (fun _ -> Set.empty) editsByFile

/// One compilation to work on. Which kind it is comes from the file
/// extension — the caller never has to say.
[<RequireQualifiedAccess>]
type private Target =
    /// A whole project, or — when a single source file was named — that
    /// project analyzed but only that one file edited.
    | Project of project: string * onlyFile: string option
    | Script of string

/// The project a source file belongs to, searching upwards. A .fs file is
/// not a compilation on its own: it needs the project's references, and F#
/// is order-dependent, so the files before it decide what its names mean.
/// A project that actually lists the file wins over a merely nearer one.
let private owningProject (sourceFile: string) =
    let full = Path.GetFullPath sourceFile
    let name = Path.GetFileName full

    // F# projects list their sources explicitly — the order is part of the
    // language — so "lists this file" is a reliable test rather than a guess
    let lists (project: string) =
        try
            (File.ReadAllText project).Contains name
        with
        | :? IOException
        | :? UnauthorizedAccessException -> false

    let projectsUnder dir =
        FileWalk.files "*.fsproj" dir |> List.ofSeq

    // Widen from the file outwards, searching BENEATH each level too,
    // because a project commonly compiles sources from a sibling folder
    // (`<Compile Include="..\Code\Thing.fs" />`) that walking up alone
    // would miss.
    //
    // Stopping matters more than widening. The repository root is the
    // natural edge: above it lies the rest of the disk, and one level too
    // far means recursively enumerating a whole drive — minutes of I/O for
    // a file that was never going to be there. A level cap backstops the
    // case where there is no repository at all.
    let mutable dir = Path.GetDirectoryName full
    let mutable found = None
    let mutable atEdge = false
    let mutable levels = 0

    while found.IsNone && not atEdge && levels < 4 && not (String.IsNullOrEmpty dir) do
        found <- projectsUnder dir |> List.tryFind lists

        let parent = Path.GetDirectoryName dir

        atEdge <-
            Directory.Exists(Path.Combine(dir, ".git"))
            || String.IsNullOrEmpty parent
            // a drive root: Path.GetDirectoryName "C:\\" is null, but be
            // explicit rather than relying on that
            || parent = Path.GetPathRoot dir

        dir <- parent
        levels <- levels + 1

    found

/// The .fsproj paths a solution lists, resolved against the solution's own
/// directory. MSBuild refuses to report compiler arguments for a solution
/// itself, so the tool works through the projects instead. The C# and VB
/// projects a solution also lists are not compilations for this tool, but
/// the api pass still has to know of them (Workspace.projectsInSolution
/// keeps them): one referencing an F# project is a caller it cannot read.
let private projectsInSolution (solutionPath: string) =
    Workspace.projectsInSolution solutionPath
    |> List.filter Workspace.isFSharpProject

let private targetOf (path: string) =
    match (Path.GetExtension path).ToLowerInvariant() with
    | ".fsproj" -> Some(Target.Project(path, None))
    | ".fsx"
    | ".fsscript" -> Some(Target.Script path)
    | _ -> None

/// Turn whatever the user pointed at into the list of compilations to run:
/// a project or script directly, every project in a solution, everything a
/// glob matches, or — for a directory — the solution or projects inside it.
let private resolveTargets (raw: string) : Result<Target list, string> =
    let expandGlob (pattern: string) =
        let normalized = pattern.Replace('\\', '/')
        let starIndex = normalized.IndexOf '*'

        let root =
            let head = normalized.Substring(0, starIndex)
            let slash = head.LastIndexOf '/'

            if slash >= 0 then head.Substring(0, slash) else "."

        let leaf = Path.GetFileName normalized

        if Directory.Exists root then
            FileWalk.files leaf root |> List.ofSeq
        else
            []

    let rec fromDirectory (dir: string) =
        let solutionsIn (d: string) =
            [ yield! Directory.EnumerateFiles(d, "*.slnx")
              yield! Directory.EnumerateFiles(d, "*.sln") ]

        let solutions = solutionsIn dir

        // a workspace of checkouts — C:\git — has no solution of its own,
        // but its children do. Each child is then resolved as its own
        // target set, so every checkout's solutions (and the projects they
        // leave out) are honoured, instead of one flat walk of every
        // fsproj under the workspace
        let checkouts =
            if solutions.IsEmpty then
                Directory.EnumerateDirectories dir
                |> Seq.filter (fun child ->
                    let name = Path.GetFileName child

                    not (name.StartsWith '.')
                    && not (List.contains name [ "node_modules"; "bin"; "obj"; "packages"; "paket-files" ]))
                |> List.ofSeq
            else
                []

        let workspace =
            solutions.IsEmpty
            && checkouts |> List.exists (fun child -> not (solutionsIn child).IsEmpty)

        if workspace then
            let named =
                checkouts |> List.filter (fun c -> not (solutionsIn c).IsEmpty) |> List.length

            printfn $"({named} checkouts with solutions under {dir} — analysing each checkout on its own)"

            let nested =
                checkouts
                |> List.collect (fun child ->
                    try
                        fromDirectory child
                    with ex -> // fsharpanalyzer: ignore-line FR0055
                        eprintfn $"  ({Path.GetFileName child}: skipped — {ex.Message})"
                        [])

            let looseScripts =
                Directory.EnumerateFiles(dir, "*.fsx")
                |> Seq.filter (Configuration.isIgnoredPath >> not)
                |> Seq.map Target.Script
                |> List.ofSeq

            nested @ looseScripts
        else

            let projects =
                match solutions with
                | [] ->
                    FileWalk.files "*.fsproj" dir
                    |> Seq.map (fun p -> Target.Project(p, None))
                    |> List.ofSeq
                | _ ->
                    // EVERY solution in the directory, projects deduplicated —
                    // picking the alphabetically first silently skipped
                    // FsCDK.sln's whole library because FsCDK.Samples.sln
                    // sorted ahead of it
                    if solutions.Length > 1 then
                        printfn $"({solutions.Length} solutions here — analysing the union of their projects)"

                    solutions
                    |> List.collect projectsInSolution
                    |> List.distinctBy (fun p -> Path.GetFullPath(p).ToLowerInvariant())
                    |> List.map (fun p -> Target.Project(p, None))

            // loose scripts are code too: build.fsx and friends never appear in
            // any fsproj, so a directory sweep that stopped at projects silently
            // skipped them. The walker already prunes obj/bin/packages/.git;
            // ignorePaths (paket-files above all) applies on top
            let scripts =
                FileWalk.files "*.fsx" dir
                |> Seq.filter (Configuration.isIgnoredPath >> not)
                |> Seq.map Target.Script
                |> List.ofSeq

            projects @ scripts

    if raw.Contains '*' || raw.Contains '?' then
        match expandGlob raw |> List.choose targetOf with
        | [] -> Error $"'{raw}' matched no .fsproj or .fsx files."
        | targets -> Ok targets
    elif Directory.Exists raw then
        match fromDirectory raw with
        | [] -> Error $"No solution or F# project found in '{raw}'."
        | targets -> Ok targets
    elif not (File.Exists raw) then
        Error $"No such file or directory: {raw}"
    else
        match (Path.GetExtension raw).ToLowerInvariant() with
        | ".sln"
        | ".slnx" ->
            match projectsInSolution raw |> List.map (fun p -> Target.Project(p, None)) with
            | [] -> Error $"'{Path.GetFileName raw}' lists no F# projects."
            | targets -> Ok targets
        | ".slnf" -> Error "Solution filters are not supported; pass the solution or a project."
        // one source file: analyze its project (a .fs needs the project's
        // references, and F# is order-dependent) but edit only this file
        | ".fs"
        | ".fsi" ->
            match owningProject raw with
            | Some project -> Ok [ Target.Project(project, Some(Path.GetFullPath raw)) ]
            | None ->
                Error
                    $"No .fsproj found above '{Path.GetFileName raw}'. A source file is not a compilation on its own — it needs its project for references and file order."
        | _ ->
            match targetOf raw with
            | Some target -> Ok [ target ]
            | None ->
                Error
                    $"Don't know what to do with '{Path.GetFileName raw}' — pass a .fsproj, .fsx, solution, directory or glob."

/// A script's own compilation, as FCS resolves it.
///
/// `assumeDotNetFramework` picks the reference set, and it is not a mere
/// preference: a .NET Framework script resolved against .NET Core's gets
/// mscorlib as the Core facade, so `open System.IO` reports DirectorySecurity
/// as missing and every file the script `#load`s is written off. Callers try
/// Core and retry as Framework.
let private scriptProjectOptions (checker: FSharpChecker) (path: string) (assumeDotNetFramework: bool) =
    let sourceText = SourceText.ofString (File.ReadAllText path)

    let options, diagnostics =
        // useFsiAuxLib: scripts run under fsi get the fsi object
        // (fsi.CommandLineArgs and friends); resolving without it
        // reported "'fsi' is not defined" on perfectly good scripts
        checker.GetProjectOptionsFromScript(
            path,
            sourceText,
            assumeDotNetFramework = assumeDotNetFramework,
            useFsiAuxLib = true
        )
        |> Async.RunSynchronously

    withFsiAuxLib path options, diagnostics

/// The compilation to analyze, from either input kind.
///
/// A script needs no MSBuild at all — FCS resolves a script's own
/// references, including `#load`ed files, which land in SourceFiles and so
/// get analyzed and fixed alongside the script itself. That also makes
/// --script far quicker than --project, which spends its first half-minute
/// in MSBuild before any analysis starts.
let private optionsFor (checker: FSharpChecker) (parseOnly: bool) (chosenFramework: string) (target: Target) =
    match target with
    | Target.Script script ->
        let path = Path.GetFullPath script

        // .NET Core first — right for modern scripts, and the caller retries
        // as .NET Framework when this reference set does not resolve (the
        // retry lives beside baselineErrorList, where the typecheck is)
        let options, diagnostics = scriptProjectOptions checker path false

        // a reference the script host could not resolve leaves the script
        // half-typed, and most rules then stay silent; say so rather than
        // reporting a suspiciously clean file
        for d in diagnostics |> List.truncate 5 do
            eprintfn $"  (script reference: {d.Message})"

        Ok options
    | Target.Project(project, _) ->
        // announced BEFORE it starts: this step can take a minute, and a
        // line that only appears afterwards is no help while you are
        // staring at a silent terminal wondering whether it is stuck
        Out.dimPart (
            if parseOnly then
                "reading sources from the project file... "
            else
                "building and reading compiler arguments... "
        )

        Console.Out.Flush()
        let argsSw = Stopwatch.StartNew()

        let fscResult =
            if parseOnly then
                parseOnlyArgs project
            else
                fscArgs chosenFramework project

        argsSw.Stop()
        Out.dim $"{argsSw.ElapsedMilliseconds} ms"

        match fscResult with
        | Error message -> Error message
        | Ok args ->
            let projectDir = Path.GetDirectoryName(Path.GetFullPath project)

            // FCS leaves SourceFiles empty for command-line args; partition
            // and rebase the relative paths MSBuild emits ourselves
            let sourceExtensions = [| ".fs"; ".fsi"; ".fsx" |]

            let isSource (arg: string) =
                not (arg.StartsWith '-')
                && sourceExtensions
                   |> Array.exists (fun ext -> arg.EndsWith(ext, StringComparison.OrdinalIgnoreCase))

            // Signing is about emitting an assembly, which analysis never
            // does — but FCS still tries to open the key file, and a
            // relative --keyfile: path it cannot resolve reports as a
            // project error, refusing a project that builds perfectly well.
            let isOutputOnly (arg: string) =
                [ "--keyfile:"; "--delaysign"; "--publicsign"; "--sourcelink:" ]
                |> List.exists (fun flag -> arg.StartsWith(flag, StringComparison.OrdinalIgnoreCase))

            let sources, otherArgs =
                args |> Array.filter (isOutputOnly >> not) |> Array.partition isSource

            let absoluteSources =
                sources
                |> Array.map (fun s ->
                    if Path.IsPathRooted s then
                        s
                    else
                        Path.Combine(projectDir, s))

            Ok
                { checker.GetProjectOptionsFromCommandLineArgs(Path.GetFullPath project, otherArgs) with
                    SourceFiles = absoluteSources }

/// Does this target carry frameworks beyond the one we analyze?
let private isMultiTargeted (target: Target) =
    match target with
    | Target.Script _ -> false
    | Target.Project(project, _) -> not (targetFrameworksOf project).IsEmpty

/// Every framework a project targets, narrowest first.
let private frameworksOf (target: Target) =
    match target with
    | Target.Script _ -> []
    | Target.Project(project, _) -> targetFrameworksOf project

/// Build every framework, so a fix that suits the one we analyzed but not
/// the others cannot pass as success.
/// Every distinct error the build reported, not just the first few. The
/// COUNT is what decides blame when a project was already broken: a
/// pass/fail answer cannot tell "the breakage is not ours" from "the
/// breakage is not ONLY ours", and answering the first when the second
/// is true puts genuinely broken fixes back. SQLProvider had a vendored
/// paket-files source broken outside this run; restoring the snapshot
/// left it broken, the rebuild failed again, and every fix that had
/// broken netstandard2.0 was re-applied on the strength of it.
let private buildAllFrameworks (project: string) =
    // the build runs from the project's own directory (its global.json), so
    // a path given relative to the caller's directory must become absolute
    let project = Path.GetFullPath project

    let exitCode, stdout, stderr =
        runForProject project processTimeout "dotnet" $"build \"{project}\" --nologo -v q"

    if exitCode = 0 then
        Ok()
    else
        Error(
            (stdout + stderr).Split '\n'
            |> Array.filter (fun l -> l.Contains "error")
            |> Array.map (fun l -> l.Trim())
            |> Array.distinct
        )

/// An error line with its position taken out, so the same pre-existing
/// error reads the same after a fix above it has moved the line it sits
/// on. Comparing SETS of these, rather than counts, is what separates "the
/// breakage is not ours" from "the breakage is not ONLY ours": an error
/// that appears with the fixes and never without them is ours.
let private errorSignature (line: string) =
    Text.RegularExpressions.Regex.Replace(line, @"\(\d+,\d+(?:,\d+,\d+)?\)", "")

/// What a failed all-frameworks build says about this run's fixes, once
/// the build is known to fail WITHOUT them too.
type private Blame =
    /// Every error was there before the fixes: theirs, not ours.
    | PreExisting
    /// The build fails differently from one run to the next, so an error
    /// seen only with the fixes proves nothing either way.
    | Unverifiable
    /// Errors that appear with the fixes and never without them.
    | Introduced of Set<string>

/// Judge a build that fails with this run's fixes AND without them.
///
/// Only COMPILER errors can be ours: a source edit cannot make an assets
/// file lose a framework (NETSDK1005) or a package fail to resolve (NU*),
/// so those never count. SwaggerProvider's Runtime restores its DesignTime
/// sibling from inside its own per-framework build, which leaves a
/// one-framework assets file behind and fails on whichever framework built
/// second — a different one after each sweep — and by count that read as
/// "2 errors with the fixes, 1 without", putting good fixes back run after
/// run.
///
/// Among compiler errors, one seen with the fixes and not in the first
/// baseline gets a second baseline build: a build that is already broken
/// is often broken DIFFERENTLY from run to run, and where the two baselines
/// disagree the failure is not evidence of anything.
let private judgeAgainstBaseline (withFixes: string array) (project: string) (firstBaseline: string array) =
    let compilerErrors (errors: string array) =
        errors
        |> Array.filter (fun e -> Text.RegularExpressions.Regex.IsMatch(e, @"error FS\d+"))
        |> Array.map errorSignature
        |> Set.ofArray

    let introduced =
        Set.difference (compilerErrors withFixes) (compilerErrors firstBaseline)

    if introduced.IsEmpty then
        PreExisting
    else
        match buildAllFrameworks project with
        | Ok() -> Unverifiable
        | Error secondBaseline when compilerErrors secondBaseline <> compilerErrors firstBaseline -> Unverifiable
        | Error secondBaseline ->
            let remaining = Set.difference introduced (compilerErrors secondBaseline)

            if remaining.IsEmpty then
                PreExisting
            else
                Introduced remaining

/// The source files as they stand, so one framework's pass can be undone
/// if it turns out to have broken another's. Starts the record of files
/// written outside it afresh: an empty `files` is "no snapshot", and then
/// nothing outside it is kept either.
let internal takeSnapshot (files: string array) =
    snapshotFiles.Clear()
    extraSnapshot.Clear()

    let snapshot =
        files
        |> Array.choose (fun f ->
            try
                Some(f, File.ReadAllText f)
            with
            | :? IOException
            | :? UnauthorizedAccessException -> None)
        |> Map.ofArray

    for KeyValue(path, _) in snapshot do
        snapshotFiles.Add(Path.GetFullPath path) |> ignore

    snapshot

/// Put back every file that changed since the snapshot — and every file
/// the run wrote outside it since; returns how many.
let internal restoreSnapshot (snapshot: Map<string, string>) =
    let putBack (path: string, original: string) =
        try
            if File.ReadAllText path <> original then
                writeSource path original
                1
            else
                0
        with
        | :? IOException
        | :? UnauthorizedAccessException -> 0

    (snapshot |> Map.toSeq |> Seq.sumBy putBack)
    + (extraSnapshot |> Seq.sumBy (fun kv -> putBack (kv.Key, kv.Value)))

/// Type-check the project after an applying pass; on new errors, roll the
/// pass back — first only the changed files the errors name, then (F#
/// inference being order-dependent, an edit in one file can break a later
/// one) every file the pass changed, which must return the count to zero
/// since the pass started clean. Rolled-back fixes go into `suppressed` so
/// the next pass does not re-apply them and oscillate until --max-passes.
///
/// Nearly free on the happy path: the pass ahead re-uses this check's
/// cached results, so it replaces rather than adds a full project check.
/// Re-apply a subset of a file's already-applied fixes to its Before text.
/// Bottom-up in original coordinates, exactly as applyEditGroups spliced
/// them the first time — a subset of non-overlapping bottom-up splices
/// stays viable, and the FromText check makes any drift fail safe (the
/// fix is silently dropped rather than misapplied).
let private reapplySubset (before: string) (fixes: (int * string * Fix) list) : string =
    let mutable current = before

    let ordered =
        fixes
        |> List.sortByDescending (fun (_, _, f) -> f.FromRange.StartLine, f.FromRange.StartColumn)

    for _, _, f in ordered do
        let lines = current.Split '\n'

        if
            f.FromRange.StartLine - 1 <= lines.Length
            && f.FromRange.EndLine - 1 <= lines.Length
        then
            let startIndex =
                (lines
                 |> Seq.take (f.FromRange.StartLine - 1)
                 |> Seq.sumBy (fun l -> l.Length + 1))
                + f.FromRange.StartColumn

            let endIndex =
                (lines |> Seq.take (f.FromRange.EndLine - 1) |> Seq.sumBy (fun l -> l.Length + 1))
                + f.FromRange.EndColumn

            if
                startIndex <= current.Length
                && endIndex <= current.Length
                && current.Substring(startIndex, endIndex - startIndex).Replace("\r", "") = f.FromText.Replace("\r", "")
            then
                let eol = if current.Contains "\r\n" then "\r\n" else "\n"
                let toText = f.ToText.Replace("\r\n", "\n").Replace("\n", eol)
                current <- current.Remove(startIndex, endIndex - startIndex).Insert(startIndex, toText)

    current

/// The fixes in an applied file whose PATCHED position sits within five
/// lines of one of the file's error lines. Patched positions are the
/// original ranges shifted by the line growth of every fix applied above
/// them — approximate under same-line stacking. The slack is five, not
/// two, because an error anchors at the START of its construct while the
/// offending edit can sit lines inside it (a record's inconsistent-fields
/// error points at the record, not the rewritten field — seen live on
/// WebsitePlayground's build.fsx). Sweeping in a neighbor costs one
/// suppressed innocent; missing the culprit costs the whole file.
let private fixesNearErrors (cf: AppliedFile) (errorLines: Set<int>) : (int * string * Fix) list =
    let newlinesIn (s: string) =
        s |> Seq.filter ((=) '\n') |> Seq.length

    let ascending =
        cf.Fixes
        |> List.sortBy (fun (_, _, f) -> f.FromRange.StartLine, f.FromRange.StartColumn)

    let mutable delta = 0

    let near =
        [ for g, code, f in ascending do
              let patchedStart = f.FromRange.StartLine + delta
              let patchedEnd = patchedStart + newlinesIn f.ToText

              if errorLines |> Set.exists (fun l -> l >= patchedStart - 5 && l <= patchedEnd + 5) then
                  g, code, f

              delta <- delta + (newlinesIn f.ToText - newlinesIn f.FromText) ]

    // a culprit's WHOLE suggestion group joins it: a multi-edit suggestion
    // applies all-or-nothing, and keeping half (a ParamOrder def swap
    // without its call sites) can compile into wrong code
    let culpritGroups = near |> List.map (fun (g, _, _) -> g) |> Set.ofList

    cf.Fixes |> List.filter (fun (g, _, _) -> culpritGroups.Contains g)

let private verifyPass
    (checker: FSharpChecker)
    (options: FSharpProjectOptions)
    (baselineErrors: int)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    (changedFiles: AppliedFile list)
    : bool =
    checker.InvalidateConfiguration options

    // measured against the baseline, not zero: a --parse-only run starts
    // with hundreds of unresolved-reference errors that are nobody's fault.
    //
    // And measured TWICE before blame: a type provider that loses its
    // database connection between two checks turns every provided type
    // into "not defined" for that one check and is back for the next.
    // welendus lost 493 fixes and CarenioBackup 165 to exactly that — a
    // clean baseline, then an SQLProvider SSL error mid-run, then a pass
    // rolled back for errors it never caused. A second check costs one
    // project typecheck, only on the failing path.
    // the files this pass changed are checked one by one as well: see
    // projectErrorsWith
    let recount () =
        projectErrorsWith checker options (changedFiles |> List.map (fun cf -> cf.Path))

    let errors =
        let first = recount ()

        if first.Length <= baselineErrors then
            first
        else
            checker.InvalidateConfiguration options
            let second = recount ()

            if second.Length <= baselineErrors then
                Out.dim
                    "  (the check reported errors once and was clean on a second look — a transient failure, not this pass)"

            second

    if errors.Length <= baselineErrors then
        true
    else
        // case-insensitive: script diagnostics can spell the path with a
        // different drive/segment casing than the target we edited
        let canonical (p: string) = Path.GetFullPath(p).ToLowerInvariant()

        let errorFiles = errors |> Array.map (fun d -> canonical d.FileName) |> Set.ofArray

        let named =
            changedFiles |> List.filter (fun cf -> errorFiles.Contains(canonical cf.Path))

        let writeBack (files: AppliedFile list) =
            for cf in files do
                writeSource cf.Path cf.Before

            checker.InvalidateConfiguration options

        let suppressAll (files: AppliedFile list) =
            for cf in files do
                for _, code, f in cf.Fixes do
                    suppressed.Add(fixKey code cf.Path f) |> ignore

        let restore (files: AppliedFile list) =
            writeBack files
            suppressAll files

        let rolledBack =
            if not named.IsEmpty then
                writeBack named

                if (recount ()).Length <= baselineErrors then
                    // the pass IS to blame — but usually one fix is, and a
                    // whole-file rollback would take every innocent fix in
                    // the file down with it (a batch of 36 lost 30 good
                    // fixes to one bad one on prismatic). Pin it on the
                    // fixes AT the error sites: re-apply everything else
                    // and recheck.
                    let errorLinesFor (path: string) =
                        errors
                        |> Array.filter (fun d -> canonical d.FileName = canonical path)
                        |> Array.map (fun d -> d.StartLine)
                        |> Set.ofArray

                    let split =
                        named
                        |> List.map (fun cf ->
                            match fixesNearErrors cf (errorLinesFor cf.Path) with
                            // no fix near any error line: the blame is
                            // non-local (an inference ripple), so the whole
                            // file stays rolled back
                            | [] -> cf, cf.Fixes
                            | culprits -> cf, culprits)

                    let salvageable =
                        split |> List.exists (fun (cf, culprits) -> culprits.Length < cf.Fixes.Length)

                    let salvaged =
                        if not salvageable then
                            false
                        else
                            for cf, culprits in split do
                                writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except culprits))

                            checker.InvalidateConfiguration options
                            (recount ()).Length <= baselineErrors

                    if salvaged then
                        let kept =
                            split |> List.sumBy (fun (cf, culprits) -> cf.Fixes.Length - culprits.Length)

                        printfn
                            $"  ({kept} fix(es) away from the error sites kept — the retry without the error-site fixes checks clean)"

                        for cf, culprits in split do
                            for _, code, f in culprits do
                                suppressed.Add(fixKey code cf.Path f) |> ignore

                        // a rolled-back suggestion can have members in
                        // files the errors never named (a cross-file edit
                        // set under --api-changes) — those members go too,
                        // or the suggestion is left half-applied
                        let culpritGroups =
                            split
                            |> List.collect (fun (_, culprits) -> culprits |> List.map (fun (g, _, _) -> g))
                            |> Set.ofList

                        let orphanFiles =
                            [ for cf in changedFiles |> List.except named do
                                  let orphans = cf.Fixes |> List.filter (fun (g, _, _) -> culpritGroups.Contains g)

                                  if not orphans.IsEmpty then
                                      writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except orphans))

                                      for _, code, f in orphans do
                                          suppressed.Add(fixKey code cf.Path f) |> ignore

                                      { cf with Fixes = orphans } ]

                        if not orphanFiles.IsEmpty then
                            checker.InvalidateConfiguration options

                        [ for cf, culprits in split do
                              if not culprits.IsEmpty then
                                  { cf with Fixes = culprits } ]
                        @ orphanFiles
                    else
                        if salvageable then
                            // the retry did not check clean — the blame was
                            // not (only) at the error sites after all
                            writeBack named

                        suppressAll named

                        // groups rolled back with the named files can have
                        // members applied in OTHER files — strip those too
                        let rolledGroups =
                            named
                            |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g))
                            |> Set.ofList

                        let orphanFiles =
                            [ for cf in changedFiles |> List.except named do
                                  let orphans = cf.Fixes |> List.filter (fun (g, _, _) -> rolledGroups.Contains g)

                                  if not orphans.IsEmpty then
                                      writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except orphans))

                                      for _, code, f in orphans do
                                          suppressed.Add(fixKey code cf.Path f) |> ignore

                                      { cf with Fixes = orphans } ]

                        if not orphanFiles.IsEmpty then
                            checker.InvalidateConfiguration options

                        named @ orphanFiles
                else
                    let rest = changedFiles |> List.except named
                    restore rest
                    suppressAll named
                    changedFiles
            else
                // every error sits in a file this pass never touched. That
                // can still be our doing (an edit's inference ripple), so
                // TEST it: restore, recount — if the errors stay, they were
                // never ours (a vendored file broken for another reason —
                // the SQLProvider paket-files case burned 40 minutes of
                // apply-restore on exactly this), so the fixes go back in
                let currentTexts =
                    changedFiles
                    |> List.map (fun cf ->
                        cf.Path,
                        (try
                            Some(File.ReadAllText cf.Path)
                         with _ ->
                             None)) // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055

                // writeBack, not restore: suppression must happen only if the
                // rollback STICKS. Suppressing here and then writing the
                // fixes back left KEPT fixes marked suppressed, so a later
                // identical-content fix in the same file was silently dropped
                writeBack changedFiles

                if (recount ()).Length <= baselineErrors then
                    suppressAll changedFiles
                    changedFiles
                else
                    for path, text in currentTexts do
                        match text with
                        | Some t -> writeSource path t
                        | None -> ()

                    checker.InvalidateConfiguration options

                    eprintfn
                        "  (the new errors persist without this pass's fixes — pre-existing breakage elsewhere, fixes kept)"

                    []

        if rolledBack.IsEmpty then
            // the errors survived the un-apply test: not ours, fixes kept
            true
        else
            eprintfn
                "  this pass introduced type errors — its changes were rolled back and the offending fixes suppressed:"

            // the errors themselves, or diagnosing WHICH fix broke means
            // re-running the whole thing by hand
            for d in errors |> Array.truncate 5 do
                eprintfn $"    {Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"

            for cf in rolledBack do
                for _, code, f in cf.Fixes do
                    eprintfn
                        $"    {code} {Path.GetFileName cf.Path}({f.FromRange.StartLine},{f.FromRange.StartColumn}) rolled back"

            false

/// Analyze and fix one compilation; returns its exit code.
let private runTarget (checker: FSharpChecker) (opts: Options) (showHeader: bool) (target: Target) =
    // counted here, not from the target list: a multi-targeted project is
    // ONE target but several compilations, so the target count would make
    // the coverage warning read "2 of 1"
    System.Threading.Interlocked.Increment(&runCompilations) |> ignore

    let onlyFile =
        match target with
        | Target.Project(_, only) -> only
        | Target.Script _ -> None

    // which framework this pass is for, when the project has several
    let frameworkLabel = if opts.Framework = "" then "" else $" [{opts.Framework}]"

    if showHeader then
        let label =
            match target with
            | Target.Project(p, Some file) -> $"{Path.GetFileName file} (in {Path.GetFileName p})"
            | Target.Project(p, None) -> Path.GetFileName p
            | Target.Script s -> Path.GetFileName s

        printfn $"== {label}{frameworkLabel} =="

    match optionsFor checker opts.ParseOnly opts.Framework target with
    | Error message ->
        eprintfn $"{message}"

        // NOT-APPLICABLE targets are not failures: a dacpac project or a
        // wildcard-item fsproj beyond --parse-only was skipped, not broken
        // (a solution containing one used to fail the whole run's exit)
        if message.Contains "— skipped" || message.Contains "beyond --parse-only" then
            0
        else
            if message.Contains "dotnet build failed" then
                System.Threading.Interlocked.Increment(&runBuildFailures) |> ignore

            1
    | Ok options ->
        let analyzers =
            cliAnalyzers ()
            |> List.filter (fun m -> not opts.ParseOnly || parseOnlySafeAnalyzers.Contains(analyzerName m))

        printfn $"{analyzers.Length} analyzers, {options.SourceFiles.Length} files"

        // cross-file (API-changing) rule variants gate on this: they
        // stay silent in editors and in default runs
        if opts.ApiChanges then
            Environment.SetEnvironmentVariable("FSREF_API_CHANGES", "1")

        // only codes the user TYPED outrank a rule's default-off status and
        // a config disable — asking for FR0099 by name and getting silence
        // would be a lie. A --categories expansion deliberately does NOT
        // qualify: a category is a filter, not an ask, and
        // `--categories idiom` must not quietly turn on FR0002
        match opts.ExplicitCodes with
        | Some codes -> Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", String.concat "," codes)
        | None -> ()

        // Not worth skipping on a dry run: measured, the cost simply
        // moves to runPass's own ParseAndCheckProject, which is only
        // cheap here BECAUSE this call warmed FCS. One full project
        // typecheck is paid either way; this ordering at least reports
        // a broken project up front.
        // before anything is written, so a pass that turns out to break the
        // build — this framework's or another's — can be undone rather than
        // merely reported
        // cross-file migrations (internal FR0069/FR0093 under --api-changes)
        // classify uses in OTHER files against those files' parse trees;
        // this host supplies them, under THIS compilation's defines
        (let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

         ProjectSources.configure (
             Some(fun path ->
                 try
                     let sourceText = SourceText.ofString (File.ReadAllText path)

                     let parseResults =
                         checker.ParseFile(path, sourceText, parsingOptions) |> Async.RunSynchronously

                     Some(parseResults.ParseTree, sourceText)
                 with
                 | :? IOException
                 | :? UnauthorizedAccessException -> None)
         ))

        // The same probe the api pass uses for FR0090/FR0091, on the
        // channel the ANALYZERS can reach: the FR0069 and FR0093 cross-file
        // migrations reshape `internal` declarations, which a `#load`ing
        // script sees — it compiles the file into itself — and whose calls
        // are in neither the project's symbol tables nor the verification
        // build. Only under --api-changes, which is the only thing that
        // opens those migrations, so the script typecheck is paid exactly
        // where it already was.
        if opts.ApiChanges then
            let sites = findScriptCallSites checker opts.Target options

            // a script's edits are rendered from the tree the script host
            // typechecked, not from one parsed with the project's options
            for script, ctx in sites.Contexts do
                ProjectSources.seed script ctx.ParseTree ctx.Source

            // a project compiling some of this project's sources directly
            // (a `<Compile Include>` link) holds those declarations as
            // its own, with call sites in its own files that neither this
            // compilation nor its verification build sees: read like a
            // sibling, its uses join the scripts' and its files are
            // rendered from its own parse; where it cannot be read, its
            // shared files are unreadable as a broken script's #loads are
            let linkerContexts, linkerUses, unreadShared =
                findLinkerCallSites checker opts.Target options (fun linker ->
                    optionsFor checker opts.ParseOnly "" (Target.Project(linker, None)))

            for file, ctx in linkerContexts do
                ProjectSources.seed file ctx.ParseTree ctx.Source

            let usesIn (index: System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>) name symbol =
                match index.TryGetValue name with
                | true, uses -> uses |> Array.filter (fun u -> sameDeclaration symbol u.Symbol)
                | false, _ -> [||]

            ProjectSources.configureOutside
                (Some(fun symbol ->
                    match symbolFullName symbol with
                    | Some name ->
                        Array.append (usesIn sites.UsesByFullName name symbol) (usesIn linkerUses name symbol)
                    | None -> [||]))
                (Seq.append sites.Unverifiable unreadShared)
        else
            ProjectSources.configureOutside None []

        // every sweepable source already swept by an earlier compilation of
        // this run (same defines, or directive-free): the sweep will visit
        // zero files, so the project typecheck buys nothing. Only while the
        // tree is untouched (or dry) — applied fixes make the recheck the
        // cross-project verification, which must stay
        let skipCompilationCheck =
            (opts.DryRun || runTotalApplied = 0)
            && onlyFile.IsNone
            // the api pass ignores the sweep dedup and can still WRITE this
            // project's files — skipping would leave it an empty snapshot to
            // roll back to and a zero error baseline to verify against
            && not opts.ApiChanges
            && (let sweepable =
                    options.SourceFiles |> Array.filter (Configuration.isIgnoredPath >> not)

                sweepable.Length > 0
                && sweepable
                   |> Array.forall (fun f ->
                       sweptFiles.Contains(Path.GetFullPath(f).ToLowerInvariant(), fileSweepKey (definesKey options) f)))

        // Which reference set a script wants is not knowable before it is
        // typechecked, and getting it wrong loses not a reference but the
        // whole compilation: a .NET Framework script resolved against .NET
        // Core's mscorlib facade reports DirectorySecurity missing from
        // `open System.IO` and writes off every file it `#load`s — 158
        // errors on PethostBackup/backend/Program.fsx, 0 as Framework. So
        // typecheck what optionsFor chose and retry as Framework when that
        // did not resolve, keeping whichever set resolves better. This IS
        // the typecheck baselineErrorList would run, handed on rather than
        // repeated. readScript chooses the same way for the scripts the
        // --api-changes pass discovers.
        let options, scriptBaseline =
            match target with
            | Target.Script script when not (skipCompilationCheck || opts.ParseOnly) ->
                Out.dimPart "typechecking the script... "
                Console.Out.Flush()
                let sw = Stopwatch.StartNew()
                let asCore = projectErrors checker options

                let retried =
                    if Array.isEmpty asCore then
                        None
                    else
                        let frameworkOptions, _ =
                            scriptProjectOptions checker (Path.GetFullPath script) true

                        let asFramework = projectErrors checker frameworkOptions

                        // fewer, not zero: a Framework script can still have
                        // a genuine error, and the only question here is
                        // which reference set it was written against
                        if asFramework.Length < asCore.Length then
                            Some(frameworkOptions, asFramework)
                        else
                            None

                sw.Stop()

                match retried with
                | Some(frameworkOptions, errors) ->
                    Out.dim
                        $"{sw.ElapsedMilliseconds} ms (.NET Framework reference set: {asCore.Length} error(s) as .NET Core, {errors.Length} as .NET Framework)"

                    frameworkOptions, Some errors
                | None ->
                    Out.dim $"{sw.ElapsedMilliseconds} ms"
                    options, Some asCore
            | _ -> options, None

        let snapshot =
            if opts.DryRun || skipCompilationCheck then
                // no snapshot — and, through it, no record of files written
                // outside one
                takeSnapshot [||]
            else
                takeSnapshot options.SourceFiles

        // Every set of files one suggestion edited together, pass by pass:
        // a definition and its call sites in a sibling project, a script
        // or a linker (the api pass), or across this project's own files.
        // The end-of-run bisection puts WHOLE files back, and a file it
        // puts back takes these with it — a sibling's rewritten call site
        // must not outlive its reverted definition.
        let ties = ResizeArray<Set<string>>()
        let canonicalPath (p: string) = Path.GetFullPath(p).ToLowerInvariant()

        let recordTies (changedFiles: AppliedFile list) =
            changedFiles
            |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g, canonicalPath cf.Path))
            |> List.groupBy fst
            |> List.iter (fun (_, members) ->
                let files = members |> List.map snd |> Set.ofList

                if files.Count > 1 then
                    ties.Add files)

        /// `files` and everything tied to them, transitively
        let rec tiedTo (files: Set<string>) =
            let more =
                ties
                |> Seq.filter (fun t -> not (Set.isEmpty (Set.intersect t files)))
                |> Set.unionMany

            let all = Set.union files more
            if all = files then files else tiedTo all

        // fixes a verification rollback rejected; never re-applied this run
        let suppressed =
            System.Collections.Generic.HashSet<string * string * string * string>()

        let baselineErrorList =
            if skipCompilationCheck then
                printfn "  (every source file already swept in an earlier compilation — project check skipped)"
                [||]
            else
                match scriptBaseline with
                // the script's reference set was chosen by typechecking it;
                // that is this same compilation, so it is the baseline
                | Some errors -> errors
                | None ->
                    Out.dimPart "typechecking the project... "
                    Console.Out.Flush()
                    let baselineSw = Stopwatch.StartNew()
                    let errors = projectErrors checker options
                    baselineSw.Stop()
                    Out.dim $"{baselineSw.ElapsedMilliseconds} ms"
                    errors

        let baselineErrors = baselineErrorList.Length

        // a SCRIPT that does not resolve is not refused: scripts routinely
        // reference things fsi would supply at run time (or nothing at all —
        // a README-snippet checker), and the syntactic rules still apply.
        // Projects keep the refusal: they are supposed to compile
        let degradedScript =
            baselineErrors > 0
            && not opts.ParseOnly
            && (match target with
                | Target.Script _ -> true
                | Target.Project _ -> false)

        // FSharp.Core ITSELF (`--compiling-fslib`) is checked by the compiler
        // it is written for, and no other: an older FCS meets intrinsics it
        // does not know ("did not contain the val
        // 'ValLinkagePartialKey(.ctor)'" on the F# repository's own
        // FSharp.Core). Not refused either: the syntactic rules still apply
        let degradedCore =
            baselineErrors > 0
            && not opts.ParseOnly
            && options.OtherOptions |> Array.exists (fun o -> o.StartsWith "--compiling-fslib")

        let degraded = degradedScript || degradedCore

        let analyzers =
            if degraded then
                // the syntactic rules, plus (for a script) the one rule whose
                // input IS the broken compilation: ScriptLoads reads the
                // FS0039s and offers the #load or #r that would resolve them
                analyzers
                |> List.filter (fun m ->
                    let name = analyzerName m

                    parseOnlySafeAnalyzers.Contains name
                    || degradedScript
                       && (name = "ScriptLoads"
                           || name = "ScriptReferences"
                           // a record expression's missing fields: a compile
                           // error is its input too
                           || name = "RecordFields"))
            else
                analyzers

        if (opts.ParseOnly || degraded) && baselineErrors > 0 then
            // expected: nothing was resolved. The count still serves as the
            // end-of-run regression baseline — a fix that breaks the parse
            // RAISES it and is put back
            if degradedCore then
                printfn
                    $"  (FSharp.Core itself, --compiling-fslib: only its own compiler can typecheck it; syntactic rules only ({analyzers.Length}))"
            else
                printfn
                    $"  ({baselineErrors} unresolved-reference error(s) ignored; syntactic rules only ({analyzers.Length}))"

            // the first few, so "does not typecheck" has a reason next to
            // it: a #load list missing a file, a reference to a dll not
            // yet built, a package the script host could not resolve
            for d in baselineErrorList |> Array.truncate 3 do
                Out.dim $"    {Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"

            if baselineErrors > 3 then
                Out.dim $"    ... and {baselineErrors - 3} more"

        if baselineErrors > 0 && not opts.ParseOnly && not degraded then
            Out.bad $"The project has {baselineErrors} error(s) before any fix; fix those first:"

            if showHeader && not opts.DryRun then
                // in a multi-compilation run these "pre-existing" errors can
                // be an earlier project's applied fixes breaking a shared
                // source file — that is our doing, not the caller's. A dry
                // run modifies nothing, so there the errors are simply
                // pre-existing
                eprintfn
                    "  (multi-project run: if an earlier project was just modified, its fixes may have introduced these — review the diff)"

            for d in projectErrors checker options |> Array.truncate 5 do
                eprintfn $"  {d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"

            1
        else
            // asking for one file and getting edits in its callers would be
            // a surprise, and that is exactly what the cross-file rules do
            if opts.ApiChanges && onlyFile.IsSome then
                Out.skip "  (api pass skipped: a single file was named, and these fixes edit call sites elsewhere)"

            // Everything the run actually wrote, across the api-changes
            // rounds and the normal passes. Zero means an untouched tree:
            // there is nothing to arbitrate, so the end-of-run error
            // recount and the all-frameworks verification build are pure
            // cost and are skipped — on a large solution that is one full
            // `dotnet build` per framework pass of every clean project.
            let mutable totalApplied = 0

            if opts.ApiChanges && onlyFile.IsNone then
                // iterated: a suggestion held back because its edits
                // nest inside another suggestion's applies next round
                let mutable apiPass = 0
                let mutable apiApplied = -1

                while apiPass < opts.MaxPasses && apiApplied <> 0 do
                    apiPass <- apiPass + 1
                    ProjectSources.invalidate ()
                    // a sibling's typecheck is a round's worth of truth: the
                    // previous round's edits are on disk now, and the
                    // sibling must be read against them
                    siblingCheckCache.Clear()
                    printfn $"api pass {apiPass}:"

                    let applied, changedFiles =
                        runApiPass
                            checker
                            options
                            (findScriptCallSites checker opts.Target options)
                            // the sibling's arguments come from MSBuild the
                            // way the project's own did, framework chosen
                            // the same way (its narrowest)
                            (lazy
                                (findSiblingCallSites checker opts.Target options (fun sibling ->
                                    optionsFor checker opts.ParseOnly "" (Target.Project(sibling, None)))))
                            opts.Codes
                            opts.DryRun
                            suppressed

                    if not opts.DryRun then
                        recordTies changedFiles

                    apiApplied <- applied
                    totalApplied <- totalApplied + applied
                    runTotalApplied <- runTotalApplied + applied
                    // --dry-run writes nothing; saying "applied" there reads
                    // as though the project had just been rewritten
                    printfn
                        $"""  {apiApplied} api-changing fix(es) {if opts.DryRun then "would be applied" else "applied"}"""

                    if opts.DryRun then
                        // nothing was written, so a second round would
                        // only repeat the same report
                        apiApplied <- 0
                    elif apiApplied > 0 then
                        // a cross-file suggestion's edits all land in the
                        // same pass, so a rollback keeps them consistent
                        verifyPass checker options baselineErrors suppressed changedFiles |> ignore

            let mutable pass = 0
            let mutable lastApplied = -1

            // divergence guard: a rule re-firing in the same file for a
            // THIRD pass while the file has GROWN since the run began is
            // feeding on its own output (the arm-wrap escape nested ten
            // `return! task {` layers exactly this way). Legitimate
            // repeat-firing — paren peeling, layer-by-layer unwinding —
            // SHRINKS the file and passes freely.
            let blockedRuleFile = System.Collections.Generic.HashSet<string * string>()
            let ruleFilePasses = System.Collections.Generic.Dictionary<string * string, int>()

            let updateDivergenceGuard (changedFiles: AppliedFile list) =
                for cf in changedFiles do
                    let codes = cf.Fixes |> List.map (fun (_, c, _) -> c) |> List.distinct

                    for code in codes do
                        let key = code, Path.GetFullPath cf.Path

                        let n =
                            (match ruleFilePasses.TryGetValue key with
                             | true, c -> c
                             | _ -> 0)
                            + 1

                        ruleFilePasses.[key] <- n

                        let grown =
                            match snapshot.TryFind cf.Path with
                            | Some before ->
                                (try
                                    File.ReadAllText(cf.Path).Length > before.Length + 100
                                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                     false)
                            | None -> false

                        if n >= 3 && grown && blockedRuleFile.Add(code, Path.GetFullPath cf.Path) then
                            eprintfn
                                $"  ({code} re-fired in {Path.GetFileName cf.Path} across {n} passes while the file grew — likely rewriting its own output; blocked for this run, please report)"

            while pass < opts.MaxPasses && lastApplied <> 0 do
                pass <- pass + 1
                ProjectSources.invalidate ()
                printfn $"pass {pass}:"

                let applied, changedFiles =
                    runPass
                        checker
                        options
                        analyzers
                        opts.Codes
                        opts.DryRun
                        opts.ApiChanges
                        opts.Jobs
                        onlyFile
                        suppressed
                        blockedRuleFile

                lastApplied <- applied
                totalApplied <- totalApplied + applied
                runTotalApplied <- runTotalApplied + applied

                if not opts.DryRun then
                    updateDivergenceGuard changedFiles
                    recordTies changedFiles

                let prefix = if opts.DryRun then "would be " else ""
                Out.good $"  {lastApplied} fix(es) {prefix}applied"

                if opts.DryRun then
                    lastApplied <- 0 // a dry run never converges; stop after one pass
                elif lastApplied > 0 then
                    // verify while the pre-pass texts are in hand; a clean
                    // result warms the next pass's project check, so this
                    // REPLACES the end-of-run check rather than adding one
                    verifyPass checker options baselineErrors suppressed changedFiles |> ignore

            if not opts.DryRun && lastApplied > 0 && pass = opts.MaxPasses then
                eprintfn
                    $"did not converge: fixes were still being applied after {opts.MaxPasses} pass(es) — rerun to continue, or raise --max-passes"

            if opts.DryRun then
                markSwept options
                0
            elif totalApplied = 0 then
                // no file was written: the tree is exactly as the baseline
                // check found it, so re-counting errors and rebuilding every
                // framework would verify nothing
                markSwept options
                0
            else
                checker.InvalidateConfiguration options
                let finalErrors = errorCount checker options

                if finalErrors > baselineErrors then
                    // per-pass verification should have made this
                    // unreachable; if something slipped through anyway, do
                    // not leave a broken tree behind
                    let restored = restoreSnapshot snapshot

                    eprintfn
                        $"Applying introduced {finalErrors - baselineErrors} error(s); the {restored} changed file(s) were put back."

                    1
                // The check above only covers the framework we analysed. A
                // multi-targeted project has others, and a fix valid for one
                // can fail on another, so build the lot before claiming
                // success.
                elif isMultiTargeted target && not opts.ParseOnly then
                    match target with
                    | Target.Project(project, _) ->
                        printfn "verifying every target framework..."

                        match buildAllFrameworks project with
                        | Ok() ->
                            printfn "done; every target framework still builds"
                            markSwept options
                            0
                        | Error output ->
                            // This pass changed code the other frameworks
                            // also compile — shared code, outside any #if —
                            // and offered something only this framework can
                            // resolve. Reporting is not enough: put the
                            // files back, or the caller is left with a
                            // project that does not build.
                            //
                            // ...unless the framework was ALREADY broken by
                            // something this run never wrote (a vendored
                            // paket-files source, most famously): test by
                            // un-applying — if the build still fails, the
                            // breakage is not ours and the fixes go back.
                            // the project's own files AND the ones the run
                            // wrote outside it, so a put-back and a
                            // write-back below move the same set
                            let currentTexts =
                                Seq.append (Map.toSeq snapshot) (extraSnapshot |> Seq.map (fun kv -> kv.Key, kv.Value))
                                |> List.ofSeq
                                |> List.choose (fun (path, _) ->
                                    try
                                        Some(path, File.ReadAllText path)
                                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                        None)

                            let restored = restoreSnapshot snapshot

                            let report (errors: string array) =
                                errors |> Array.truncate 5 |> String.concat "\n"

                            let keepFixes (why: string) =
                                for path, text in currentTexts do
                                    writeSource path text

                                eprintfn $"{why}"
                                eprintfn $"{report output}"
                                1

                            // a verification switch: a failure that needs the
                            // fixes in place to be studied (the F# compiler's
                            // FSharp.Core failing only with the compiler
                            // project's fixes applied) is kept, not undone
                            let keepOnFailure = Environment.GetEnvironmentVariable "FSREF_KEEP_ON_FAILURE" = "1"

                            match buildAllFrameworks project with
                            | Error _ when keepOnFailure ->
                                keepFixes
                                    "FSREF_KEEP_ON_FAILURE: a target framework fails with this run's fixes (and without them); kept for inspection:"
                            // Still broken without the fixes — but "still
                            // broken" is not "not our fault". Comparing the
                            // errors themselves separates the two: one that
                            // appears only with our changes is ours, and
                            // putting the files back would hand over a
                            // project broken in ways this run caused.
                            | Error withoutFixes ->
                                match judgeAgainstBaseline output project withoutFixes with
                                | PreExisting ->
                                    keepFixes
                                        "A target framework fails to build, but it fails WITHOUT this run's fixes too — pre-existing breakage, fixes kept:"
                                | Unverifiable ->
                                    keepFixes
                                        "A target framework fails to build, and fails DIFFERENTLY from one build to the next without this run's fixes — this build cannot verify them; fixes kept (each passed the typecheck of the framework analysed), review the diff:"
                                | Introduced introduced ->
                                    eprintfn
                                        $"A target framework was ALREADY broken, but applying broke it further ({introduced.Count} error(s) seen only with this run's fixes), so the {restored} file(s) it changed were put back:"

                                    eprintfn $"{report (Array.ofSeq introduced)}"
                                    1
                            | Ok() ->
                                // the baseline builds — so the failure is
                                // ours, or a build that only fails
                                // sometimes. One more build with the fixes
                                // back in place tells which: a project that
                                // restores from inside its own build
                                // (SwaggerProvider) fails on one sample
                                // and passes on the next
                                for path, text in currentTexts do
                                    writeSource path text

                                match buildAllFrameworks project with
                                | Ok() ->
                                    printfn
                                        "done; every target framework still builds (the first verification build failed and the second passed — a build that only fails sometimes)"

                                    markSwept options
                                    0
                                | Error again when keepOnFailure ->
                                    eprintfn
                                        "FSREF_KEEP_ON_FAILURE: a target framework fails with this run's fixes and builds without them; the fixes are kept for inspection:"

                                    eprintfn $"{report again}"
                                    1
                                | Error again ->
                                    // ONE file's fixes can be the whole trouble — the
                                    // F# compiler's sformat.fs is also a source of
                                    // FSharp.Core, compiled there before printf.fs,
                                    // where an interpolated string has no
                                    // PrintfFormat yet — and putting all 199 changed
                                    // files back for it throws away every other fix.
                                    // Bisect instead: revert halves of the changed
                                    // files until the build passes, keep the rest
                                    let changed =
                                        currentTexts
                                        |> List.filter (fun (path, text) ->
                                            match Map.tryFind path snapshot with
                                            | Some original -> original <> text
                                            | None -> false)
                                        |> List.map fst

                                    let fixedText = Map.ofList currentTexts
                                    let mutable builds = 0
                                    let maxBuilds = 12

                                    // the tree with exactly these files put back
                                    let passesReverting (reverted: Set<string>) =
                                        builds <- builds + 1

                                        for path in changed do
                                            writeSource
                                                path
                                                (if reverted.Contains path then
                                                     Map.find path snapshot
                                                 else
                                                     Map.find path fixedText)

                                        match buildAllFrameworks project with
                                        | Ok() -> true
                                        | Error _ -> false

                                    // a signature and its implementation move as ONE:
                                    // split across halves, both halves fail (the
                                    // compiler repository, where every .fs has its
                                    // .fsi) and the bisection learns nothing
                                    let units =
                                        changed
                                        |> List.groupBy (fun path ->
                                            Path.ChangeExtension(path, null).ToLowerInvariant())
                                        |> List.map snd

                                    let filesOf (us: string list list) = us |> List.concat |> Set.ofList

                                    // with `context` and `suspects` all put back the
                                    // build passes; find the suspects that matter
                                    let rec culprits (context: Set<string>) (suspects: string list list) =
                                        if suspects.Length <= 1 || builds >= maxBuilds then
                                            suspects
                                        else
                                            let h1, h2 = List.splitAt (suspects.Length / 2) suspects

                                            if passesReverting (Set.union context (filesOf h1)) then
                                                culprits context h1
                                            elif passesReverting (Set.union context (filesOf h2)) then
                                                culprits context h2
                                            else
                                                culprits (Set.union context (filesOf h2)) h1
                                                @ culprits (Set.union context (filesOf h1)) h2

                                    // the errors name the project that refused
                                    // (`[...\FSharp.Core.fsproj::TargetFramework=...]`);
                                    // when it is ANOTHER project, the changed files it
                                    // compiles itself are the first suspects — one
                                    // build, before any bisection
                                    let compiledElsewhere =
                                        let canonical (p: string) = Path.GetFullPath(p).ToLowerInvariant()

                                        again
                                        |> Array.choose (fun line ->
                                            let m =
                                                Text.RegularExpressions.Regex.Match(
                                                    line,
                                                    @"\[([^\[\]]+\.fsproj)(?:::|\])"
                                                )

                                            if m.Success then
                                                Some(canonical m.Groups.[1].Value)
                                            else
                                                None)
                                        |> Array.distinct
                                        |> Array.filter (fun p -> p <> canonical project)
                                        |> Array.collect (fun otherProject ->
                                            try
                                                let dir = Path.GetDirectoryName otherProject

                                                Text.RegularExpressions.Regex.Matches(
                                                    File.ReadAllText otherProject,
                                                    "Include=\"([^\"]+\\.fsi?)\""
                                                )
                                                |> Seq.map (fun m -> canonical (Path.Combine(dir, m.Groups.[1].Value)))
                                                |> Array.ofSeq
                                            with
                                            | :? IOException
                                            | :? UnauthorizedAccessException -> [||])
                                        |> Set.ofArray

                                    let shared =
                                        changed
                                        |> List.filter (fun path ->
                                            compiledElsewhere.Contains(Path.GetFullPath(path).ToLowerInvariant()))

                                    printfn
                                        $"  bisecting the {changed.Length} changed file(s) for the ones the other framework refuses (a build per step)..."

                                    // (found, already confirmed by a passing build)
                                    let found, confirmed =
                                        if not shared.IsEmpty && passesReverting (set shared) then
                                            printfn
                                                $"  ({shared.Length} of them are compiled by the refusing project itself, and putting those back is enough)"

                                            shared, true
                                        else
                                            culprits Set.empty units |> List.concat, false

                                    if
                                        found.Length < changed.Length
                                        && (confirmed || (builds < maxBuilds && passesReverting (set found)))
                                    then
                                        eprintfn
                                            $"Applying broke a target framework this run did not analyze; the fixes in {found.Length} file(s) were put back and the other {changed.Length - found.Length} kept:"

                                        for path in found do
                                            putBackFiles.Add(Path.GetFullPath path) |> ignore
                                            eprintfn $"  {path}"

                                        // A suggestion's edits move as ONE across
                                        // files, and this project's build says
                                        // nothing about the sibling test project,
                                        // #loading script or linker in which a
                                        // put-back definition's call sites were
                                        // rewritten. Those go back with it — and
                                        // then whatever else THEIR suggestions tied
                                        // them to, so that no file is left reshaped
                                        // against a reverted one (a ParamOrder swap
                                        // compiles either way and computes the
                                        // wrong thing). Lossy, and consistent.
                                        let closure = tiedTo (found |> List.map canonicalPath |> Set.ofList)

                                        let extras =
                                            [ for kv in extraSnapshot do
                                                  if closure.Contains(canonicalPath kv.Key) then
                                                      kv.Key, kv.Value ]

                                        let alsoOwn =
                                            changed
                                            |> List.filter (fun path ->
                                                closure.Contains(canonicalPath path)
                                                && not (
                                                    found
                                                    |> List.exists (fun f -> canonicalPath f = canonicalPath path)
                                                ))

                                        for path, original in extras do
                                            writeSource path original

                                            eprintfn
                                                $"  {path} (outside this project, rewritten by the same suggestion)"

                                        for path in alsoOwn do
                                            writeSource path (Map.find path snapshot)
                                            putBackFiles.Add(Path.GetFullPath path) |> ignore
                                            eprintfn $"  {path} (tied to one of those by a suggestion of its own)"

                                        eprintfn $"{report again}"

                                        // more of the project's own files went back
                                        // than the bisection's last build saw
                                        if not alsoOwn.IsEmpty then
                                            match buildAllFrameworks project with
                                            | Ok() -> ()
                                            | Error _ ->
                                                let restored = restoreSnapshot snapshot

                                                eprintfn
                                                    $"With those put back too a target framework still fails, so the {restored} file(s) this run changed were all put back."

                                        1
                                    else
                                        let restored = restoreSnapshot snapshot

                                        eprintfn
                                            $"Applying broke a target framework this run did not analyze, so the {restored} file(s) it changed were put back:"

                                        eprintfn $"{report again}"
                                        1
                    | Target.Script _ ->
                        printfn "done; project still checks clean"
                        markSwept options
                        0
                else
                    printfn "done; project still checks clean"
                    markSwept options
                    0

/// The fingerprint set of an earlier SARIF report, for --baseline.
let private loadBaseline (path: string) : Result<Set<string>, string> =
    try
        use doc = JsonDocument.Parse(File.ReadAllText path)

        let prints =
            [ for run in doc.RootElement.GetProperty("runs").EnumerateArray() do
                  match run.TryGetProperty "results" with
                  | true, results ->
                      for result in results.EnumerateArray() do
                          match result.TryGetProperty "partialFingerprints" with
                          | true, fps ->
                              match fps.TryGetProperty FingerprintKey with
                              | true, v -> v.GetString()
                              | _ -> ()
                          | _ -> ()
                  | _ -> () ]

        Ok(Set.ofList prints)
    with ex ->
        Error $"could not read baseline '{path}': {ex.Message}"

let private severityName (s: Severity) =
    match s with
    | Severity.Error -> "error"
    | Severity.Warning -> "warning"
    | Severity.Info -> "info"
    | Severity.Hint -> "hint"

let private findingsPayload (findings: ReportedFinding list) =
    [ for f in findings ->
          dict
              [ "code", box f.Code
                "severity", box (severityName f.Severity)
                "autoFixable", box f.Fixable
                "file", box f.File
                "startLine", box f.StartLine
                "startColumn", box f.StartColumn
                "endLine", box f.EndLine
                "endColumn", box f.EndColumn
                "message", box f.Message
                "fingerprint", box f.Fingerprint
                "snippet", box f.Snippet ] ]

/// The run's findings as one JSON document (--format json and --mcp).
let private findingsAsJson (findings: ReportedFinding list) (baselined: int) =
    let payload =
        dict
            [ "findings", box (findingsPayload findings)
              "baselineSuppressed", box baselined
              "commentSuppressed", box commentSuppressed
              "suppressionsOverridden", box suppressionOverridden ]

    JsonSerializer.Serialize(payload, JsonSerializerOptions(WriteIndented = true))

let private rulesAsRows () =
    RuleCatalog.allRules
    |> List.map (fun (code, category) -> code, RuleCatalog.name category, Configuration.isEnabledIn Map.empty code "")

/// Order a multi-compilation run NARROWEST TARGET FIRST, solution-wide.
/// Within one project the narrowest framework already goes first; across
/// projects the same principle protects shared source files — a fix
/// proposed while analysing the net8.0-only project would compile there
/// and break the netstandard2.0 sibling a whole compilation later. With
/// the restrictive context up front, capability-gated rules see the
/// narrow surface, the fixes they offer hold everywhere wider, and the
/// sweep dedup then skips the already-clean shared files. Scripts keep
/// their place at the end; projects whose framework a textual read
/// cannot see (Directory.Build.props inheritance) sort after the known
/// ones, in their original order.
let private orderNarrowestFirst (targets: Target list) =
    if targets.Length < 2 then
        targets
    else
        let projectRank (path: string) =
            try
                let text = File.ReadAllText path

                let m =
                    Text.RegularExpressions.Regex.Match(text, "<TargetFrameworks?>([^<]+)</TargetFrameworks?>")

                if m.Success then
                    m.Groups.[1].Value.Split ';'
                    |> Array.map _.Trim()
                    |> Array.filter (fun t -> t <> "" && not (t.Contains "$("))
                    |> Array.map tfmRank
                    |> Array.sort
                    |> Array.tryHead
                    |> Option.defaultValue (98, 0)
                else
                    (98, 0)
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                (98, 0)

        targets
        |> List.sortBy (fun t ->
            match t with
            | Target.Project(path, _) -> projectRank path
            | Target.Script _ -> (99, 0))

/// The whole run for one Options value: resolve targets, sweep, verify,
/// report. The checker comes from the caller so a resident host (--mcp)
/// can keep it — and every reference assembly FCS has parsed — warm
/// between calls.
let private executeRun (checker: FSharpChecker) (opts: Options) : int =
    match resolveTargets opts.Target with
    | Error message ->
        eprintfn $"{message}"
        2
    | Ok targets ->
        let targets = orderNarrowestFirst targets

        // `"apiChanges": true` in fsharprefactor.json is the flag as a
        // standing decision, for a repository where it is always the right
        // answer. It can only widen: a run that already passed the flag is
        // unaffected, and no config can take it away.
        let opts =
            if opts.ApiChanges then
                opts
            else
                let probe =
                    targets
                    |> List.tryPick (fun t ->
                        match t with
                        | Target.Project(path, _)
                        | Target.Script path -> Some path)

                match probe |> Option.map Configuration.apiChangesFor with
                | Some true ->
                    Out.white $"--api-changes is on: {Configuration.ConfigFileName} asks for it."
                    { opts with ApiChanges = true }
                | _ -> opts

        let several = targets.Length > 1

        if several then
            printfn $"{targets.Length} compilations to work through (narrowest target first)"

        // Said twice, at both ends of the run, and deliberately: the flag
        // changes which rules fire at all, and a sweep prints enough that
        // one line in the middle of it is a line nobody reads. Before the
        // work so it can be acted on without paying for the run twice;
        // after it because that is where the reader is looking. Scripts are
        // left out — they have no assembly surface for the scope gate to
        // hold anything back from.
        let inviteApiChanges () =
            if
                not opts.ApiChanges
                && targets
                   |> List.exists (fun t ->
                       match t with
                       | Target.Project _ -> true
                       | Target.Script _ -> false)
            then
                Out.white "Consider running with --api-changes if public changes are allowed."

        inviteApiChanges ()

        sweptFiles.Clear()
        // a sibling's compiler arguments and typecheck are this run's: the
        // corpus harness runs main in-process, and the next run's sources
        // may be another tree's
        siblingOptionsCache.Clear()
        siblingCheckCache.Clear()
        // the corpus harness runs main in-process; a leaked count would
        // report the previous run's held-back findings as this one's
        Analyzers.heldByScope.Clear()
        directiveFreeCache.Clear()
        runTotalApplied <- 0
        runBuildFailures <- 0
        runCompilations <- 0
        honorAllSuppressions <- opts.HonorSuppressions
        parseOnlyRun <- opts.ParseOnly
        showNotes <- opts.Notes
        notesOnly <- opts.NotesOnly
        lock heldNoteCounts heldNoteCounts.Clear
        // the corpus harness runs main in-process, so per-run stores
        // must not leak findings across invocations
        lock reportedFindings (fun () ->
            reportedFindings.Clear()
            reportedKeys.Clear())

        printedNotes.Clear()

        // A multi-targeted project is really several compilations: each
        // framework activates its own #if branches, and code behind
        // another framework's is not in the parse tree at all. So work
        // through them rather than making the caller name each one —
        // narrowest first, so the fixes valid everywhere land before any
        // that only suit a wider surface. The final all-framework build
        // is what catches a fix that does not generalise.
        let runOne target =
            match opts.Framework, frameworksOf target with
            // parse-only has no per-framework defines to vary; one pass
            | _ when opts.ParseOnly -> runTarget checker opts several target
            | "", (_ :: _ :: _ as frameworks) ->
                let conditionals =
                    match target with
                    | Target.Project(project, _) -> sourcesUseConditionals project
                    | Target.Script _ -> true

                if not conditionals then
                    // no #if anywhere: every framework parses the same
                    // tree, so one sweep covers them all — and the
                    // final all-frameworks build still verifies the rest
                    printfn
                        $"{Path.GetFileName opts.Target}: {frameworks.Length} target frameworks, no conditional compilation — sweeping the narrowest only"

                    runTarget
                        checker
                        { opts with
                            Framework = List.head frameworks }
                        true
                        target
                else
                    printfn $"{Path.GetFileName opts.Target}: {frameworks.Length} target frameworks"

                    // legacy targets present AND the fsproj defines its
                    // own modern-only constant: capability rules
                    // (FR0038/FR0106) emit #if <that constant> pairs on
                    // the modern passes instead of fixes the legacy
                    // half cannot compile. No such constant, no dual
                    // emission — nothing is invented.
                    let isLegacy (tfm: string) =
                        tfm.StartsWith "net4"
                        || tfm.StartsWith "netstandard1"
                        || tfm = "netstandard2.0"
                        || tfm = "netcoreapp2.0"

                    let legacyTfms, modernTfms = frameworks |> List.partition isLegacy

                    let dualConstant =
                        if opts.NoIfDefs || legacyTfms.IsEmpty then
                            None
                        else
                            match target with
                            | Target.Project(project, _) -> chooseDualConstant project modernTfms legacyTfms
                            | Target.Script _ -> None

                    match dualConstant with
                    | Some constant ->
                        printfn
                            $"  (capability fixes will pair with the project's own #if {constant} for the legacy frameworks)"
                    | None -> ()

                    let results =
                        frameworks
                        |> List.map (fun tfm ->
                            Environment.SetEnvironmentVariable(
                                "FSREF_DUAL_TFM",
                                (match dualConstant with
                                 | Some c when not (isLegacy tfm) -> c
                                 | _ -> null)
                            )

                            // no constant to guard with, and this pass sees a
                            // wider surface than the narrowest target: a
                            // capability fix here can only go in plainly and
                            // be reverted by the all-frameworks build, taking
                            // the innocent fixes in those files with it
                            Environment.SetEnvironmentVariable(
                                "FSREF_NO_GUARD",
                                (if dualConstant.IsNone && not (isLegacy tfm) && not legacyTfms.IsEmpty then
                                     "1"
                                 else
                                     null)
                            )

                            runTarget checker { opts with Framework = tfm } true target)

                    // both are this project's rounds' business only: a
                    // leaked FSREF_NO_GUARD dropped the capability fixes of
                    // every later target in the run, single-target net8.0
                    // projects included
                    Environment.SetEnvironmentVariable("FSREF_DUAL_TFM", null)
                    Environment.SetEnvironmentVariable("FSREF_NO_GUARD", null)
                    results |> List.fold max 0
            | _ -> runTarget checker opts several target

        try
            let writeReportNow () =
                match opts.Report with
                | Some reportPath ->
                    writeReport reportPath opts.Target (lock reportedFindings (fun () -> List.ofSeq reportedFindings))
                | None -> ()

            // a many-target run rewrites the report after every target, so
            // a crash or a Ctrl-C an hour in still leaves what was found
            let exitCode =
                targets
                |> List.map (fun target ->
                    let code = runOne target

                    if targets.Length > 1 then
                        writeReportNow ()

                    code)
                |> List.fold max 0

            match opts.Report with
            | Some reportPath ->
                writeReportNow ()
                printfn $"{reportedFindings.Count} finding(s) written to {reportPath}"
            | None -> ()

            let heldNotes = lock heldNoteCounts (fun () -> heldNoteCounts |> List.ofSeq)

            if not heldNotes.IsEmpty then
                let total = heldNotes |> List.sumBy (fun kv -> kv.Value)

                let breakdown =
                    heldNotes
                    |> List.sortByDescending (fun kv -> kv.Value)
                    |> List.map (fun kv -> $"{kv.Value} {kv.Key}")
                    |> String.concat ", "

                Out.note $"  {total} advisory note(s) held: {breakdown} — list with --notes, export with --report"

            if baselineSuppressed > 0 then
                printfn $"  ({baselineSuppressed} finding(s) matched the baseline and were suppressed)"

            if commentSuppressed > 0 then
                printfn $"  ({commentSuppressed} finding(s) silenced by suppression comments)"

            if suppressionOverridden > 0 then
                printfn
                    $"  ({suppressionOverridden} suppression comment(s) not honored by the \"suppressions\" policy — reported above, never auto-fixed)"

            // What the scope gate held back, named. Without this the
            // invitation below is an abstraction: nobody widens a scope for
            // an unknown number of unknown findings, and a rule that finds
            // nothing to say says nothing here either.
            let held =
                Analyzers.heldByScope
                |> Seq.map (fun kv -> kv.Key, kv.Value)
                |> Seq.sortByDescending snd
                |> List.ofSeq

            if not held.IsEmpty then
                let total = held |> List.sumBy snd

                let breakdown =
                    held |> List.map (fun (code, n) -> $"{n} {code}") |> String.concat ", "

                Out.white
                    $"  {total} finding(s) held back by scope: {breakdown} — public declarations this run may not reshape. Set \"publicApi\": false in {Configuration.ConfigFileName} if nothing outside this assembly links to them or serializes them."

            // the second half of the pair the run opened with — after every
            // count, where the reader has just seen what the run found and
            // is deciding whether to run it again
            inviteApiChanges ()

            // LAST, after every count, because a coverage gap changes what
            // all of them mean: a clean-looking tally over the projects that
            // happened to build reads exactly like clean code
            if runBuildFailures > 0 then
                let scope =
                    if runBuildFailures >= runCompilations then
                        "NOTHING was analysed"
                    else
                        $"the findings above cover only the {runCompilations - runBuildFailures} that built"

                Out.bad
                    $"  WARNING: {runBuildFailures} of {runCompilations} compilation(s) could not be analysed — they do not build, so {scope}. Fix the build (a missing `dotnet tool restore`/`paket restore` is the usual cause), or use --parse-only for the syntactic rules."

            if exitCode = 0 && opts.FailOnFindings && reportedFindings.Count > 0 then
                3
            else
                exitCode
        finally
            // runTarget sets these for the rule variants; the corpus
            // harness runs main IN-PROCESS, so a leaked flag would make
            // later analyzer calls in the same process api-changes- or
            // forced-code-scoped
            Environment.SetEnvironmentVariable("FSREF_API_CHANGES", null)
            Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", null)
            Environment.SetEnvironmentVariable("FSREF_DUAL_TFM", null)
            Environment.SetEnvironmentVariable("FSREF_NO_GUARD", null)

/// --rules: the catalog, human table by default, JSON on request.
let private printRules (json: bool) =
    if json then
        let payload =
            [ for code, category, enabledByDefault in rulesAsRows () ->
                  dict
                      [ "code", box code
                        "category", box category
                        "enabledByDefault", box enabledByDefault ] ]

        printfn $"{JsonSerializer.Serialize(payload, JsonSerializerOptions(WriteIndented = true))}"
    else
        for code, category, enabledByDefault in rulesAsRows () do
            let marker = if enabledByDefault then "" else "  (off by default)"
            printfn $"%s{code}  %-12s{category}%s{marker}"

/// The text of a fsharprefactor.json that changes nothing: every rule at
/// the default this build would apply anyway, every run-level key at its
/// own default, and a comment on each saying what turning it round does.
///
/// Written out rather than described because the catalog is the part
/// nobody can type from memory — and because a file whose every line is
/// already the default is the one safe starting point: a repository can
/// flip the lines it disagrees with and delete the rest.
///
/// JSON with comments and trailing commas, which is what the config
/// parser accepts (JsonCommentHandling.Skip, AllowTrailingCommas).
let defaultConfigText () =
    let text = System.Text.StringBuilder()
    let line (s: string) = text.AppendLine s |> ignore

    line "// fsharprefactor.json — per-repository configuration for fsharp-refactor."
    line "// Generated by `fsharp-refactor --create-config`: every value below is this"
    line "// version's default, so an untouched file changes nothing. Delete a line to"
    line "// follow the tool's default for it as that default changes between versions;"
    line "// keep a line to pin today's answer. Comments and trailing commas are fine."
    line "{"
    line "  // Does anything OUTSIDE this assembly link against its public declarations?"
    line "  // F# makes a declaration public by default, so `public` is usually the"
    line "  // absence of a decision rather than one. `false` says this is a leaf — an"
    line "  // application, an internal tool — and the rules that change a declaration's"
    line "  // compiled shape in place ([<Struct>], [<Literal>], named union fields) then"
    line "  // treat public as internal. It never licenses an edit to another file."
    line "  //"
    line "  // Left COMMENTED OUT because the default is not a fixed value: with no"
    line "  // setting the compilation answers, and an OutputType of Exe or WinExe — or"
    line "  // a script — is read as a leaf, a library is not. Uncomment to overrule"
    line "  // that either way: `true` is what an executable writes when it serializes"
    line "  // its own public types or loads plugins by reflection."
    line "  // \"publicApi\": true,"
    line ""
    line "  // --api-changes on every run: fixes that rewrite call sites project-wide"
    line "  // (currying a function, reordering its parameters). Implies publicApi: false."
    line "  \"apiChanges\": false,"
    line ""
    line "  // What a `// fsharpanalyzer: ignore-line FRxxxx` comment is worth:"
    line "  //   \"all\"            it silences the finding (what editors do regardless)"
    line "  //   \"no-correctness\" correctness findings are reported anyway, never fixed"
    line "  //   \"none\"           every suppressed finding is reported anyway"
    line "  \"suppressions\": \"all\","
    line ""
    line "  // Extra paths never analysed, ADDITIVE over the built-in defaults"
    line "  // (git-ignored files, obj/, generated sources). Substring or glob."
    line "  \"ignorePaths\": [],"
    line ""
    line "  // Extra fsharplint-style hints, e.g. \"not (a = b) ===> a <> b\""
    line "  \"hints\": { \"add\": [] },"
    line ""
    line "  // Every rule this build knows, at its default. false turns one off."
    line "  \"rules\": {"

    let rows = rulesAsRows ()

    for category in RuleCatalog.all do
        let name = RuleCatalog.name category

        let inCategory =
            rows
            |> List.filter (fun (_, c, _) -> c = name)
            |> List.sortBy (fun (code, _, _) -> code)

        if not inCategory.IsEmpty then
            line ""
            line $"    // ---- {name} ({inCategory.Length}) ----"

            for code, _, enabledByDefault in inCategory do
                let value = if enabledByDefault then "true" else "false"

                // catalog descriptions run to a paragraph for some rules;
                // a config file wants a label, and Rules.md has the rest
                let summary =
                    let full = (RuleCatalog.describe code).Replace('\n', ' ').Replace('\r', ' ')

                    if full.Length > 90 then
                        full.Substring(0, 87) + "..."
                    else
                        full

                line $"    \"{code}\": {value}, // {summary}"

    line "  }"
    line "}"
    text.ToString()

/// One MCP tool-call response body: text content plus the protocol wrapper.
let private mcpToolResult (text: string) =
    dict [ "content", box [ dict [ "type", box "text"; "text", box text ] ] ]

[<return: Struct>]
let inline private (|IsNullOrWhiteSpace|_|) (input: string) =
    if String.IsNullOrWhiteSpace input then
        ValueSome input
    else
        ValueNone

/// --mcp: a minimal MCP server over stdio — newline-delimited JSON-RPC
/// 2.0, no extra dependencies, and one warm FSharpChecker across every
/// call, which is the entire point: the first analyze pays the reference
/// parse, the rest answer from a hot cache. Progress prose is diverted to
/// stderr so the protocol stream stays clean.
let private runMcp () =
    let protocolOut = Console.Out
    Console.SetOut Console.Error

    let checker = FSharpChecker.Create(keepAssemblyContents = true)

    let respond (idJson: string) (resultJson: string) =
        protocolOut.WriteLine($"{{\"jsonrpc\":\"2.0\",\"id\":{idJson},\"result\":{resultJson}}}")
        protocolOut.Flush()

    let respondError (idJson: string) (code: int) (message: string) =
        let msg = JsonSerializer.Serialize message

        protocolOut.WriteLine(
            $"{{\"jsonrpc\":\"2.0\",\"id\":{idJson},\"error\":{{\"code\":{code},\"message\":{msg}}}}}"
        )

        protocolOut.Flush()

    let serialize (o: obj) = JsonSerializer.Serialize o

    let toolsJson =
        serialize (
            dict
                [ "tools",
                  box
                      [ dict
                            [ "name", box "analyze"
                              "description",
                              box
                                  "Analyze an F# project, script or directory with fsharp-refactor. Dry-run by default: reports findings without editing. Set apply=true to write the fixes (build-verified). Returns findings as JSON with stable fingerprints and source snippets."
                              "inputSchema",
                              box (
                                  dict
                                      [ "type", box "object"
                                        "properties",
                                        box (
                                            dict
                                                [ "target",
                                                  box (
                                                      dict
                                                          [ "type", box "string"
                                                            "description",
                                                            box "fsproj, fsx, sln, directory or glob to analyze" ]
                                                  )
                                                  "codes",
                                                  box (
                                                      dict
                                                          [ "type", box "string"
                                                            "description",
                                                            box "comma-separated rule codes to restrict to" ]
                                                  )
                                                  "categories",
                                                  box (
                                                      dict
                                                          [ "type", box "string"
                                                            "description",
                                                            box
                                                                "comma-separated: correctness,performance,idiom,cosmetic" ]
                                                  )
                                                  "parseOnly",
                                                  box (
                                                      dict
                                                          [ "type", box "boolean"
                                                            "description", box "no MSBuild, syntactic rules only" ]
                                                  )
                                                  "apply",
                                                  box (
                                                      dict
                                                          [ "type", box "boolean"
                                                            "description", box "write the fixes (default: dry-run)" ]
                                                  ) ]
                                        )
                                        "required", box [ "target" ] ]
                              ) ]
                        dict
                            [ "name", box "list_rules"
                              "description", box "The rule catalog: code, category, enabled-by-default."
                              "inputSchema", box (dict [ "type", box "object"; "properties", box (dict []) ]) ] ] ]
        )

    let handleAnalyze (args: JsonElement) =
        let getString name =
            match args.TryGetProperty(name: string) with
            | true, v when v.ValueKind = JsonValueKind.String -> Some(v.GetString())
            | _ -> None

        let getBool name =
            match args.TryGetProperty(name: string) with
            | true, v -> v.ValueKind = JsonValueKind.True
            | _ -> false

        match getString "target" with
        | None -> Error "analyze needs a 'target'"
        | Some target ->

            match parseArgs [| target |] with
            | Error message -> Error message
            | Ok baseOpts ->

                let codes =
                    getString "codes"
                    |> Option.map (fun s ->
                        s.Split ',' |> Array.map (fun c -> c.Trim().ToUpperInvariant()) |> Set.ofArray)

                let categories =
                    getString "categories"
                    |> Option.map (fun s -> s.Split ',' |> Array.choose RuleCatalog.parse |> Set.ofArray)

                let opts =
                    { baseOpts with
                        DryRun = not (getBool "apply")
                        ParseOnly = getBool "parseOnly"
                        Codes = codes
                        ExplicitCodes = codes
                        Categories = categories }
                    |> applyCategories

                lock reportedFindings (fun () ->
                    reportedFindings.Clear()
                    reportedKeys.Clear()
                    baselineSuppressed <- 0
                    commentSuppressed <- 0
                    suppressionOverridden <- 0)

                printedNotes.Clear()
                let exitCode = executeRun checker opts
                let findings = lock reportedFindings (fun () -> List.ofSeq reportedFindings)

                let body =
                    dict
                        [ "exitCode", box exitCode
                          "applied", box (not opts.DryRun)
                          "findingCount", box findings.Length
                          "findings", box (findingsPayload findings)
                          "baselineSuppressed", box baselineSuppressed
                          "commentSuppressed", box commentSuppressed
                          "suppressionsOverridden", box suppressionOverridden ]

                Ok(JsonSerializer.Serialize body)

    let mutable running = true

    while running do
        match Console.In.ReadLine() with
        | null -> running <- false
        | IsNullOrWhiteSpace line -> ()
        | line ->
            let idJson, method_, params_ =
                try
                    use doc = JsonDocument.Parse line
                    let root = doc.RootElement

                    let id =
                        match root.TryGetProperty "id" with
                        | true, v -> v.GetRawText()
                        | _ -> "null"

                    let m =
                        match root.TryGetProperty "method" with
                        | true, v -> v.GetString()
                        | _ -> ""

                    let p =
                        match root.TryGetProperty "params" with
                        | true, v -> Some(v.Clone())
                        | _ -> None

                    id, m, p
                with _ ->
                    "null", "", None

            match method_ with
            | "initialize" ->
                respond
                    idJson
                    """{"protocolVersion":"2024-11-05","capabilities":{"tools":{}},"serverInfo":{"name":"fsharp-refactor","version":"0.6.6"}}"""
            | "notifications/initialized"
            | "notifications/cancelled" -> ()
            | "ping" -> respond idJson "{}"
            | "tools/list" -> respond idJson toolsJson
            | "tools/call" ->
                let name, args =
                    match params_ with
                    | Some p ->
                        let n =
                            match p.TryGetProperty "name" with
                            | true, v -> v.GetString()
                            | _ -> ""

                        let a =
                            match p.TryGetProperty "arguments" with
                            | true, v -> v
                            | _ -> JsonDocument.Parse("{}").RootElement

                        n, a
                    | None -> "", JsonDocument.Parse("{}").RootElement

                match name with
                | "list_rules" ->
                    let rules =
                        [ for code, category, enabledByDefault in rulesAsRows () ->
                              dict
                                  [ "code", box code
                                    "category", box category
                                    "enabledByDefault", box enabledByDefault ] ]

                    respond idJson (serialize (mcpToolResult (serialize rules)))
                | "analyze" ->
                    try
                        (handleAnalyze args)
                        |> Result.map (mcpToolResult >> serialize >> respond idJson)
                        |> Result.defaultWith (fun msg -> respondError idJson -32602 msg)
                    with ex ->
                        respondError idJson -32603 $"analyze failed: {ex.Message}"
                | other -> respondError idJson -32601 $"unknown tool '{other}'"
            | "" -> respondError idJson -32700 "unparseable request"
            | notification when not (notification.StartsWith "notifications/") && idJson <> "null" ->
                respondError idJson -32601 $"unknown method '{notification}'"
            | _ -> ()

    0

[<EntryPoint>]
let main argv =
    // colour is decided before anything is printed, so --no-color governs
    // even the argument errors below
    let parsed = parseArgs argv

    match parsed with
    | Ok opts when opts.NoColor -> Out.goPlain ()
    | _ -> ()

    match parsed with
    | Error message ->
        eprintfn $"{message}"
        2
    | Ok opts when opts.ShowHelp ->
        printfn $"{helpText}"
        0
    | Ok opts when opts.ShowVersion ->
        // the informational version carries what Directory.Build.props set;
        // the assembly version drops the patch component
        let asm = Reflection.Assembly.GetExecutingAssembly()

        let version =
            asm.GetCustomAttributes(typeof<Reflection.AssemblyInformationalVersionAttribute>, false)
            |> Array.tryHead
            |> Option.map (fun a -> (a :?> Reflection.AssemblyInformationalVersionAttribute).InformationalVersion)
            // a source-built run may carry a +sha suffix; the version is the part before it
            |> Option.map (fun v -> v.Split('+').[0])
            |> Option.defaultValue (string (asm.GetName().Version))

        printfn $"fsharp-refactor {version}"
        0
    | Ok opts when opts.ListRules ->
        printRules opts.Json
        0
    | Ok opts when opts.CreateConfig ->
        // a path that is not a directory is a typo, not an instruction to
        // write somewhere else: falling back to the current directory once
        // put a config in a repository root nobody asked about
        let directory =
            if opts.Target = "" then
                Ok(Directory.GetCurrentDirectory())
            elif Directory.Exists opts.Target then
                Ok opts.Target
            else
                Error $"--create-config writes into a DIRECTORY; '{opts.Target}' is not one."

        match directory with
        | Error message ->
            eprintfn $"{message}"
            2
        | Ok directory ->

            let path = Path.Combine(directory, Configuration.ConfigFileName)

            if File.Exists path then
                // someone's decisions live in there; --create-config is a
                // starting point, never a reset
                eprintfn $"{path} already exists — delete it first, or write the new one elsewhere."
                2
            else
                try
                    File.WriteAllText(path, defaultConfigText ())

                    printfn
                        $"Wrote {path} — every rule at this build's default, so it changes nothing until you edit it."

                    0
                with
                | :? IOException
                | :? UnauthorizedAccessException as e ->
                    eprintfn $"Could not write {path}: {e.Message}"
                    1
    | Ok opts when opts.Mcp -> runMcp ()
    // no arguments at all is a question, not a mistake: show the help
    | Ok opts when opts.Target = "" ->
        printfn $"{helpText}"
        2
    | Ok opts ->
        let baseline =
            match opts.Baseline with
            | Some path -> loadBaseline path
            | None -> Ok Set.empty

        match baseline with
        | Error message ->
            eprintfn $"{message}"
            2
        | Ok prints ->
            baselineFingerprints <- prints
            baselineSuppressed <- 0
            commentSuppressed <- 0
            suppressionOverridden <- 0

            // --format json: prose to stderr, one clean JSON document on
            // the real stdout. The default output stays human-readable.
            let realOut = Console.Out

            if opts.Json then
                Console.SetOut Console.Error

            // ONE checker for the whole run: FCS caches parsed reference
            // assemblies on the instance, and a twenty-project solution's
            // flavors share nearly all of them — a fresh checker per
            // compilation was paying that parse twenty times over.
            // (Analyzers may read the typed tree, hence assembly contents.)
            let checker = FSharpChecker.Create(keepAssemblyContents = true)
            let code = executeRun checker opts

            if opts.Json then
                Console.SetOut realOut
                let findings = lock reportedFindings (fun () -> List.ofSeq reportedFindings)
                printfn $"{findingsAsJson findings baselineSuppressed}"

            code
