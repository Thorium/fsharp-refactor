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
///                      (one a project compiles is left to that project)
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
                        straight from the fsproj and only the 56 of 116
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
                    ExplicitCodes = Some parsed
                }
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
                    Categories = Some(parsed |> Array.choose id |> Set.ofArray)
                }
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
                    NotesOnly = false
                }
                rest
        | "on" -> parseArgsLoop { opts with Notes = true } rest
        | _ ->
            parseArgsLoop
                { opts with
                    NotesOnly = true
                    Notes = true
                    DryRun = true
                }
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
        [
            "--report"
            "--baseline"
            "--format"
            "--framework"
            "--jobs"
            "--max-passes"
            "--codes"
            "--categories"
        ]
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
        {
            Target = ""
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
            Framework = ""
        }
        (List.ofArray argv)
    |> Result.map applyCategories

/// The stderr line runProcessIn writes for a child stopped at its time cap
/// begins with this, so that a classifier (stoppedAtTimeCap) tests for the
/// cap itself and not for the prose after it.
[<Literal>]
let internal TimeCapMark = "[stopped at the time cap]"

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

            -1,
            "",
            $"{TimeCapMark} '{fileName} {arguments}' had not finished after {minutes} minutes, so it was stopped."

/// Long enough for a real build of a large project, short enough that a
/// stuck one is reported rather than waited on forever. FSREF_BUILD_MINUTES
/// raises it for a project whose compile alone takes longer: FSharpPlus's
/// SRTP-heavy test project needs ~23 minutes, and was skipped as "does not
/// build" at the default.
let private processTimeout =
    match Environment.GetEnvironmentVariable "FSREF_BUILD_MINUTES" with
    | null
    | "" -> TimeSpan.FromMinutes 15.0
    | v ->
        match Double.TryParse(v, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture) with
        | true, minutes when minutes > 0.0 -> TimeSpan.FromMinutes minutes
        | _ -> TimeSpan.FromMinutes 15.0

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

/// A project file's text with its XML comments taken out: a framework list
/// an author commented away is not one the project builds. welendus's
/// WelendusLogic.fsproj carries `<!-- <TargetFrameworks>netstandard2.0;net48
/// </TargetFrameworks> -->` above the live element, the text match took
/// the commented one first, and the run asked MSBuild for a net48 pass that
/// no restore had produced (NETSDK1005).
let internal projectTextWithoutComments (text: string) =
    Workspace.projectTextWithoutComments text

let internal targetFrameworksOf (projectPath: string) : string list =
    listedFrameworks.GetOrAdd(
        Path.GetFullPath projectPath,
        fun path ->
            let text =
                try
                    projectTextWithoutComments (File.ReadAllText path)
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

/// The `<Compile>` items of one fsproj: the lowercased full path, the
/// membership key every other path here is compared by, to the path as
/// the project spells it. The spelled path is the one to READ: a Linux
/// file system does not find `library.fs` where `Library.fs` is, and a
/// reader handed the key took every project for one branching on the
/// build configuration there. Read once per project file; items with a
/// property or a wildcard are the evaluation's business and are left out,
/// as `registerFileFloors` does.
let private compileItemsCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, Map<string, string>>(StringComparer.OrdinalIgnoreCase)

let private compileItemsOf (project: string) =
    compileItemsCache.GetOrAdd(
        project,
        fun p ->
            try
                let dir = Path.GetDirectoryName p

                compileItemRegex.Matches(File.ReadAllText p)
                |> Seq.map (fun m -> m.Groups.[1].Value)
                |> Seq.filter (fun item -> not (item.Contains '$') && not (item.Contains '*'))
                |> Seq.map (fun item ->
                    let full = Path.GetFullPath(Path.Combine(dir, item.Replace('\\', '/')))
                    full.ToLowerInvariant(), full)
                |> Map.ofSeq
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                Map.empty
    )

/// Do the project's sources branch on the build CONFIGURATION — `#if
/// DEBUG`, `#if !DEBUG`, `#if RELEASE`, `#if TRACE`? The analysis sees one
/// configuration's branch; the other is not in the parse tree at all, and
/// a call-site migration rewrites the definition for both while reaching
/// the call sites of one. Rare (7 of the 34 repositories swept), and the
/// extra build below is a cheap price for knowing. Read from the parser's
/// directive trivia (Text.hasConfigurationConditional), so a `#if DEBUG`
/// quoted in a comment or a string is not one.
let private configurationConditionals =
    System.Collections.Concurrent.ConcurrentDictionary<string, bool>(StringComparer.OrdinalIgnoreCase)

/// Memoised per project for the run: asked at the verification, at the
/// extra pass and at the sibling check, and no fix writes such a
/// directive (the capability fixes emit framework ones).
let internal hasConfigurationConditionals (project: string) =
    configurationConditionals.GetOrAdd(
        Path.GetFullPath project,
        fun p ->
            compileItemsOf p
            |> Map.toSeq
            |> Seq.exists (fun (_, spelled) -> Text.hasConfigurationConditional spelled)
    )

/// A build configuration: the two the `#if DEBUG` / `RELEASE` conditionals
/// tell apart. Its text is what MSBuild is handed and what the pass labels
/// say.
[<RequireQualifiedAccess>]
type private BuildConfiguration =
    | Debug
    | Release

    override this.ToString() =
        match this with
        | BuildConfiguration.Debug -> "Debug"
        | BuildConfiguration.Release -> "Release"

    /// The one the conditionals switch to.
    member this.Other =
        match this with
        | BuildConfiguration.Debug -> BuildConfiguration.Release
        | BuildConfiguration.Release -> BuildConfiguration.Debug

    /// MSBuild's answer; anything but Release reads as Debug, the default.
    static member Parse(text: string) =
        if String.Equals(text.Trim(), "Release", StringComparison.OrdinalIgnoreCase) then
            BuildConfiguration.Release
        else
            BuildConfiguration.Debug

/// The build configuration the CURRENT compilation is analysed under:
/// None for the project's default, or the other one during the extra pass a
/// project with configuration conditionals gets (see executeRun), where
/// the `#if !DEBUG` branches are the parse tree. Process-wide like the
/// FSREF_* flags: one compilation runs at a time.
let mutable private analysisConfiguration: BuildConfiguration option = None

let private configurationArg () =
    match analysisConfiguration with
    | None -> ""
    | Some configuration -> $" -p:Configuration={configuration}"

let private configurationSuffix () =
    match analysisConfiguration with
    | None -> ""
    | Some configuration -> $"+{configuration}"

/// The configuration the project builds by default (Debug unless it says
/// otherwise), so the verification can build the OTHER one.
let private defaultConfigurations =
    System.Collections.Concurrent.ConcurrentDictionary<string, BuildConfiguration>(StringComparer.OrdinalIgnoreCase)

let private defaultConfiguration (project: string) =
    defaultConfigurations.GetOrAdd(
        Path.GetFullPath project,
        fun p ->
            let exitCode, stdout, _ =
                runForProject p processTimeout "dotnet" $"msbuild \"{p}\" -getProperty:Configuration"

            let answer = stdout.Trim()

            if exitCode = 0 && answer <> "" && not (answer.Contains '\n') then
                BuildConfiguration.Parse answer
            else
                BuildConfiguration.Debug
    )

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
            projectTextWithoutComments (File.ReadAllText projectPath)
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
            [|
                for m in defineConstantsElementRegex.Matches unconditionalText do
                    for piece in m.Groups.[1].Value.Split ';' do
                        let piece = piece.Trim()

                        if piece <> "" && not (piece.Contains "$(") then
                            $"--define:{piece}"
            |]
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
/// repository's own build script sets the variable; so does this, for every
/// process started from here — and undoes it again for the next checkout
/// that has none. Both variables are process-wide: set once for the F#
/// compiler's `.dotnet` and never restored, they made every later checkout
/// of a workspace sweep build with THAT SDK, whatever its own global.json
/// asked for, and a second private SDK was prepended in front of the first
/// rather than in its place.
let private sdkEnvironmentLock = obj ()

/// DOTNET_ROOT and PATH as this process was started with, read the first
/// time a private SDK is put in front of them: what a checkout without one
/// gets back.
let private originalSdkEnvironment =
    lazy (Environment.GetEnvironmentVariable "DOTNET_ROOT", Environment.GetEnvironmentVariable "PATH")

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

    let sameDirectory (a: string) (b: string) =
        not (String.IsNullOrEmpty a)
        && not (String.IsNullOrEmpty b)
        && (try
                String.Equals(
                    Path.GetFullPath(a).TrimEnd(Path.DirectorySeparatorChar),
                    Path.GetFullPath(b).TrimEnd(Path.DirectorySeparatorChar),
                    StringComparison.OrdinalIgnoreCase
                )
            with _ -> // a DOTNET_ROOT that is no path is not this directory; fsharpanalyzer: ignore-line FR0055
                false)

    lock sdkEnvironmentLock (fun () ->
        match
            findGlobalJson (DirectoryInfo(Path.GetDirectoryName(Path.GetFullPath projectPath)))
            |> Option.bind dotnetDirOf
        with
        | Some dir ->
            let current = Environment.GetEnvironmentVariable "DOTNET_ROOT"

            if not (sameDirectory current dir) then
                // the originals are read before the first change, and a
                // second private SDK REPLACES the first on PATH rather than
                // queueing behind it
                let _, originalPath = originalSdkEnvironment.Force()
                Environment.SetEnvironmentVariable("DOTNET_ROOT", dir)
                Environment.SetEnvironmentVariable("PATH", dir + string Path.PathSeparator + originalPath)

                printfn
                    $"  global.json points at the repository's own .NET in {dir}: builds run with it on DOTNET_ROOT"
        | None ->
            // no private SDK here: the variables go back to what the process
            // started with — only if this run changed them, so a DOTNET_ROOT
            // the person set is left alone
            if originalSdkEnvironment.IsValueCreated then
                let originalRoot, originalPath = originalSdkEnvironment.Force()
                let current = Environment.GetEnvironmentVariable "DOTNET_ROOT"

                if current <> originalRoot then
                    Environment.SetEnvironmentVariable("DOTNET_ROOT", originalRoot)
                    Environment.SetEnvironmentVariable("PATH", originalPath)

                    printfn "  (no private .NET here: builds run with the .NET this process started with again)")

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
                            "dotnet", "paket restore", "dotnet paket restore"
                    ]

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

/// `-p:NonExistentFile=…` names a file CoreCompile lists among its
/// outputs, so the target is never up to date and always runs — the
/// property `_ComputeNonExistentFileProperty` sets for Visual Studio's
/// design-time builds, passed directly. It is what lets an args query run
/// on `-t:Build` instead of `-t:Rebuild`: no clean, so the outputs a
/// script's `#r` or an old-style project's path reference need stay where
/// they are, and no third build to put them back.
let private forceCoreCompile =
    " -p:NonExistentFile=__NonExistentSubDir__\\__NonExistentFile__"

/// The FS3511 harvest of one project tree, remembered between runs.
///
/// FS3511 is emitted at codegen, so only a compile that actually RAN
/// reports it, and an up-to-date tree gives MSBuild no reason to run one.
/// Forcing one costs the whole fsc compile — 28 s for FunStripe.Core's
/// 141 files — per compilation per run, and that was the largest single
/// cost of a sweep, paid twice over while the args query cleaned the
/// outputs and a third build put them back. The same tree yields the same
/// warnings, so the harvest is cached under a hash of the sources: a hit
/// runs the incremental build (a second or two — and still a real,
/// harvested compile when something changed), a miss forces the compile
/// once and records what it said. Keyed per framework, since a state
/// machine can compile statically on one and not another; a project whose
/// fsproj does not list its sources plainly (wildcards, imports) has no
/// key and forces every time, as before.
let private fallbackCacheDir =
    lazy
        (let dir =
            Path.Combine(
                Environment.GetFolderPath Environment.SpecialFolder.LocalApplicationData,
                "fsharp-refactor",
                "fs3511"
            )

         try
             Directory.CreateDirectory dir |> ignore
             Some dir
         with _ -> // no cache is only slower; fsharpanalyzer: ignore-line FR0055
             None)

let private fallbackHarvestKey (projectPath: string) =
    try
        let dir = Path.GetDirectoryName projectPath
        let text = File.ReadAllText projectPath

        let items =
            compileItemRegex.Matches text
            |> Seq.map (fun m -> m.Groups.[1].Value)
            |> List.ofSeq

        if items |> List.exists (fun i -> i.Contains '$' || i.Contains '*') then
            None
        else
            use sha = System.Security.Cryptography.SHA256.Create()

            let feed (s: string) =
                sha.TransformBlock(Text.Encoding.UTF8.GetBytes s, 0, Text.Encoding.UTF8.GetByteCount s, null, 0)
                |> ignore

            feed projectPath
            feed text

            for item in items do
                let path = Path.GetFullPath(Path.Combine(dir, item.Replace('\\', '/')))
                feed path
                feed (File.ReadAllText path)

            sha.TransformFinalBlock([||], 0, 0) |> ignore
            Some(Convert.ToHexString sha.Hash)
    with _ -> // an unreadable source: no key, the compile is forced; fsharpanalyzer: ignore-line FR0055
        None

let private fallbackCachePath (key: string) (framework: string) =
    fallbackCacheDir.Value
    |> Option.map (fun dir -> Path.Combine(dir, $"{key}-{framework}.txt"))

let private readFallbackCache (key: string) (framework: string) : (string * int) list option =
    match fallbackCachePath key framework with
    | Some path when File.Exists path ->
        try
            File.ReadAllLines path
            |> Array.choose (fun line ->
                match line.LastIndexOf '\t' with
                | -1 -> None
                | i ->
                    match Int32.TryParse(line.Substring(i + 1)) with
                    | true, n -> Some(line.Substring(0, i), n)
                    | _ -> None)
            |> List.ofArray
            |> Some
        with _ -> // a torn cache reads as a miss; fsharpanalyzer: ignore-line FR0055
            None
    | _ -> None

let private writeFallbackCache (key: string) (framework: string) (sites: (string * int) list) =
    match fallbackCachePath key framework with
    | Some path ->
        try
            File.WriteAllLines(path, sites |> List.map (fun (file, line) -> $"{file}\t{line}"))
        with _ -> // no cache is only slower; fsharpanalyzer: ignore-line FR0055
            ()
    | None -> ()

let private fscArgs (chosenFramework: string) (projectPath: string) =
    // msbuild runs from the project's own directory (its global.json), so a
    // path given relative to the caller's directory must become absolute
    let projectPath = Path.GetFullPath projectPath
    ensurePrivateSdk projectPath
    ensureRestorable projectPath

    let projectText =
        try
            projectTextWithoutComments (File.ReadAllText projectPath)
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
            (match targetFramework with
             | Some tfm ->
                 Out.dim $"  (multi-targeted; analysing against {tfm})"
                 $" -p:TargetFramework={tfm}"
             | None -> "")
            + configurationArg ()

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

        let frameworks = targetFrameworksOf projectPath

        let frameworkName =
            (targetFramework |> Option.defaultValue "all") + configurationSuffix ()

        let harvestKey = fallbackHarvestKey projectPath

        let cachedSites =
            harvestKey |> Option.bind (fun key -> readFallbackCache key frameworkName)

        // the FIRST of a multi-targeted project's frameworks builds them
        // ALL: the inner builds run in parallel (35 s for both of
        // FunStripe.Core's, against 28 s for one), and every later
        // framework's own build is then incremental — a no-op when the
        // narrower pass changed nothing, exactly the compile it needs when
        // it did
        let buildsEveryFramework =
            frameworks.Length > 1 && targetFramework = List.tryHead frameworks

        let buildScope = if buildsEveryFramework then configurationArg () else tfmArg

        let skipBuild = Environment.GetEnvironmentVariable "FSREF_SKIP_BUILD" = "1"

        let buildExit, buildOut, buildErr =
            if restoreExit <> 0 then
                restoreExit, restoreOut, restoreErr
            // a verification switch: analyse a tree whose build is known to
            // fail (studying what the typecheck sees of that failure), on
            // the outputs already on disk
            elif skipBuild then
                0, "", ""
            else
                let force = if cachedSites.IsNone then forceCoreCompile else ""
                let outer = run $"msbuild \"{projectPath}\" -t:Build{buildScope}{force}"

                // a framework this machine cannot build (a targeting pack
                // it lacks) must not cost the narrowest one its analysis:
                // the outer build failing, the pass falls back to building
                // its own framework alone, as it did before the outer build
                match outer with
                | exit, _, _ when exit <> 0 && buildsEveryFramework ->
                    run $"msbuild \"{projectPath}\" -t:Build{tfmArg}{force}"
                | _ -> outer

        // FS3511 is emitted at CODEGEN, so no analyzer can see it — but this
        // build just did, and the warning carries the builder's own position
        // ("SignalRHubs.fs(2583,16): warning FS3511: This state machine is not
        // statically compilable"). Handing those lines to the analyzers lets
        // FR0029's tail extraction fire where the fallback is REAL rather than
        // wherever a size threshold guesses at one. Nothing here when the
        // build compiled nothing because it was already up to date — which
        // is what the cache above is for (see fallbackHarvestKey).
        let fallbackPattern =
            Text.RegularExpressions.Regex(
                @"^\s*(?<file>[^\r\n(]+)\((?<line>\d+),\d+\):\s*warning FS3511",
                Text.RegularExpressions.RegexOptions.Multiline
            )

        let harvestedSites =
            [
                for m in fallbackPattern.Matches($"{buildOut}\n{buildErr}") do
                    let file: string = m.Groups.["file"].Value.Trim()

                    match Int32.TryParse m.Groups.["line"].Value with
                    | true, line ->
                        let full =
                            if Path.IsPathRooted file then
                                file
                            else
                                Path.Combine(Path.GetDirectoryName(Path.GetFullPath projectPath), file)

                        full, line
                    | _ -> ()
            ]
            |> List.distinct

        Configuration.setDynamicFallbackSites harvestedSites

        match harvestKey, cachedSites with
        | _, Some sites -> Configuration.setDynamicFallbackSites sites
        | Some key, None when buildExit = 0 && not skipBuild ->
            // a forced compile of every framework answers for each of
            // them; of one, for that one
            if buildsEveryFramework then
                for tfm in "all" :: frameworks do
                    writeFallbackCache key tfm harvestedSites
            else
                writeFallbackCache key frameworkName harvestedSites
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
            // the build above left the project up to date, and an
            // incremental skip of CoreCompile yields no args at all — so the
            // target is forced (forceCoreCompile) rather than the outputs
            // cleaned: a `-t:Rebuild` here once cost every project a clean
            // and a third build to put the outputs back for a script's
            // `#r "../../src/X/bin/Debug/net9.0/X.dll"` (four of
            // svg_path_fsharp's five debug scripts had lost their
            // reference) or an old-style project's path reference (FsXaml's
            // demos). BuildProjectReferences=false keeps the referenced
            // outputs intact. Judge by the JSON, not the exit code.
            let exit, stdout, stderr =
                run
                    $"msbuild \"{projectPath}\" -t:Build -p:BuildProjectReferences=false -p:ProvideCommandLineArgs=true -p:SkipCompilerExecution=true{forceCoreCompile} --getItem:FscCommandLineArgs --getProperty:DotnetFscCompilerPath{tfmArg}"

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

    [
        for t in assembly.GetTypes() do
            for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
                if m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).Length > 0 then
                    m
    ]

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

         [
             for t in assembly.GetTypes() do
                 for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
                     if m.GetCustomAttributes(typeof<EditorAnalyzerAttribute>, false).Length > 0 then
                         m
         ])

/// Analyzers whose CLI wrappers never touch CheckFileResults — the set a
/// --parse-only run may execute against an unresolvable compilation. The
/// typed analyzers are excluded outright rather than trusted to
/// self-silence: their conservative gates assume a compilation that at
/// least TRIED to resolve. Curated against the wrapper bodies in
/// Analyzers.fs; a new syntactic analyzer earns its entry here.
let parseOnlySafeAnalyzers =
    set
        [
            "AbbreviatedType"
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
            "XmlDocParams"
        ]

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

/// The typecheck of a multi-targeted project's NEXT framework, started
/// while the current one is swept (see prefetchNextFramework). FCS runs
/// two project checks concurrently on one checker at full speed — both of
/// FunStripe.Core's frameworks in 24.8 s against 51 s one after the
/// other, measured — so the wider framework's 27 s baseline is paid
/// behind the narrower one's sweep instead of after it.
///
/// A source written while that check reads it could be parsed half-way
/// and cached against a stamp the write already set, so no source is
/// written while one is in flight: writeSource waits for it first. The
/// wait is nearly always nothing (the check finishes inside the sweep),
/// and a pass that then applies fixes simply leaves FCS to re-check the
/// changed files incrementally, as it would have anyway.
let private speculativeCheck: System.Threading.Tasks.Task ref =
    ref System.Threading.Tasks.Task.CompletedTask

let private awaitSpeculation () =
    let inFlight = speculativeCheck.Value

    if not inFlight.IsCompleted then
        try
            // a check that never returns (a type provider hanging) must not
            // hold the run: the framework's own, timed check reports it
            inFlight.Wait(TimeSpan.FromMinutes 30.) |> ignore
        with _ -> // its failure is reported by the framework's own check; fsharpanalyzer: ignore-line FR0055
            ()

/// Write a source file back in the encoding it already had.
let private writeSource (path: string) (text: string) =
    awaitSpeculation ()
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
                OtherOptions = Array.append options.OtherOptions [| $"-r:{dll}" |]
            }
        | None -> options

let private checkDirectoryLock = obj ()

/// ParseAndCheckProject from the project's own directory, the way MSBuild
/// runs fsc. The typecheck ends by resolving the assembly's identity, and
/// for that FCS opens the strong-name key exactly as the source spells it
/// — `[<assembly: AssemblyKeyFile("../../FsCheckKey.snk")>]` is read
/// relative to the PROCESS directory, not the project's (implicitIncludeDir
/// covers `#r` and `--lib`, not this). A solution run from FsCheck's root
/// refused all four library projects with "The key file could not be
/// opened" while `dotnet build` and a run from each project directory
/// were fine. The directory is process-wide state, so the change lasts
/// exactly one synchronous check, under a lock; nothing else reads a
/// relative path meanwhile (the sweep's parallel file checks come later
/// and do not finalize an assembly).
/// How long one typecheck may take before it is given up as hung. A type
/// provider connects to its database at design time, and SQLProvider's
/// DuckDbTest.fsx sat in that connection for two and a half hours with no
/// way out; the FCS call cannot be cancelled, so the wait is abandoned and
/// the compilation reported, the work left to finish on its own thread.
/// FSREF_CHECK_MINUTES raises it for a project whose check alone takes
/// longer.
let private checkTimeout =
    let asked =
        match Environment.GetEnvironmentVariable "FSREF_CHECK_MINUTES" with
        | null
        | "" -> TimeSpan.FromMinutes 30.0
        | v ->
            match Double.TryParse(v, Globalization.NumberStyles.Float, Globalization.CultureInfo.InvariantCulture) with
            | true, minutes when minutes > 0.0 -> TimeSpan.FromMinutes minutes
            | _ -> TimeSpan.FromMinutes 30.0

    // a project whose BUILD was allowed longer (FSREF_BUILD_MINUTES) can
    // typecheck as long: FSharpPlus's test project compiles in 23 minutes
    max asked processTimeout

/// `work`, given up after `timeout` with a TimeoutException carrying
/// `describe ()` — the computation itself left running.
///
/// Not `Async.RunSynchronously(_, timeout)`: that overload cancels the
/// computation and then waits, with no timeout of its own, for it to
/// notice — measured, a 6 s `Thread.Sleep` inside the async came back
/// after 6 s against a 500 ms timeout. A type provider sitting in a
/// database connection never observes cancellation, so the DuckDbTest.fsx
/// wait this exists to end went on exactly as before. Started as a Task
/// instead, and the wait alone is bounded; the task finishes, or does not,
/// on its own thread. `WaitAny` rather than `Wait` so a failure is not
/// wrapped in an AggregateException on the way out: `GetResult` rethrows
/// the original.
///
/// Left running is not left alone: the task is started under a token that
/// is cancelled on the way out, and not waited for. A typecheck that does
/// observe cancellation (FCS checks the token between files) then stops
/// and lets go of the checker it was rooting — an abandoned check kept the
/// old checker, and everything it had cached, alive for the rest of the
/// run. One that never observes it runs on exactly as before.
let internal awaitWithin (timeout: TimeSpan) (describe: unit -> string) (work: Async<'T>) : 'T =
    let cts = new Threading.CancellationTokenSource()
    let task = Async.StartAsTask(work, cancellationToken = cts.Token)

    // the source lives as long as the work holding its token: disposed at
    // return while an abandoned check still runs, the check's next
    // registration on the token would throw - the shape FR0075 now refuses
    // (welendus's loan search under a `use`d source) - so the work disposes
    // it on its own completion, however it ends
    task.ContinueWith(
        (fun (_: Threading.Tasks.Task) -> cts.Dispose()),
        Threading.Tasks.TaskContinuationOptions.ExecuteSynchronously
    )
    |> ignore

    if Threading.Tasks.Task.WaitAny([| (task :> Threading.Tasks.Task) |], timeout) < 0 then
        cts.Cancel()
        raise (TimeoutException(describe ()))
    else
        task.GetAwaiter().GetResult()

/// `ParseAndCheckProject`, abandoned after `checkTimeout`: a
/// TimeoutException naming the compilation, for the caller to report.
let internal checkWithin (checker: FSharpChecker) (options: FSharpProjectOptions) =
    awaitWithin
        checkTimeout
        (fun () ->
            $"the typecheck of {Path.GetFileName options.ProjectFileName} had not finished after {checkTimeout.TotalMinutes:N0} minutes (FSREF_CHECK_MINUTES raises the limit)")
        (checker.ParseAndCheckProject options)

let internal checkProject (checker: FSharpChecker) (options: FSharpProjectOptions) =
    let projectDir =
        try
            let dir = Path.GetDirectoryName(Path.GetFullPath options.ProjectFileName)

            if not (String.IsNullOrEmpty dir) && Directory.Exists dir then
                Some dir
            else
                None
        with _ -> // a name that is no path checks from wherever we are; fsharpanalyzer: ignore-line FR0055
            None

    match projectDir with
    | None -> checkWithin checker options
    | Some dir ->
        lock checkDirectoryLock (fun () ->
            let previous = Environment.CurrentDirectory

            // a directory the process cannot make current (a path past the
            // OS limit) checks from wherever we are, as before
            let switched =
                try
                    Environment.CurrentDirectory <- dir
                    true
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false

            try
                checkWithin checker options
            finally
                // Restored on the timeout path too, when the check is still
                // RUNNING (see awaitWithin): from here on it runs under
                // whatever directory the process has, and the next check
                // under this lock changes that under it again. Its result
                // goes to nobody, so a key file it then fails to open costs
                // nothing; the residual risk is FCS's own — a relative path
                // it resolves late, on a thread this cannot reach — and is
                // noted rather than fixed.
                if switched then
                    Environment.CurrentDirectory <- previous)

let private projectErrors (checker: FSharpChecker) (options: FSharpProjectOptions) =
    let results = checkProject checker options

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
    // keyed by the normalised path, valued by the project's OWN spelling:
    // FCS decides "last file of the compilation" by comparing the name it
    // is handed with the last SourceFiles entry as plain strings, and an
    // MSBuild item written `src/main.fs` keeps its forward slash there
    // while the edited path arrives through GetFullPath with a backslash.
    // Checked under the wrong spelling, an anonymous-module last file of
    // an exe fails FS0222 whatever its text - Fable's quicktest-rust
    // main.fs lost its one fix to that, and would have lost any other
    let inProject =
        options.SourceFiles
        |> Array.map (fun f -> Path.GetFullPath(f).ToLowerInvariant(), f)
        |> Map.ofArray

    let perFile =
        files
        |> List.choose (fun path ->
            try
                inProject.TryFind(Path.GetFullPath(path).ToLowerInvariant())
            with _ -> // an unopenable path is not this project's; fsharpanalyzer: ignore-line FR0055
                None)
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
type internal AppliedFile =
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

/// The text every file had when the RUN first saw it - across
/// compilations, unlike a snapshot, which starts afresh per compilation.
/// What a later compilation's failed build is put back to when the file
/// it fails on is one an earlier compilation of the run rewrote
/// (`putBackRunEdits`).
let internal runOriginals =
    System.Collections.Generic.Dictionary<string, string>(StringComparer.OrdinalIgnoreCase)

/// A file is about to be written over `before`: keep that text when the
/// file is outside the snapshot and not seen yet.
let internal recordExtra (file: string) (before: string) =
    let full = Path.GetFullPath file
    runOriginals.TryAdd(full, before) |> ignore

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

    let appliedFiles: AppliedFile list =
        [
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
                            && current.Substring(startIndex, endIndex - startIndex).Replace("\r", "") =
                                f.FromText.Replace("\r", "")
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

                    {
                        Path = file
                        Before = text
                        Fixes = appliedHere
                    }
        ]

    applied, appliedFiles

/// One project-wide suggestion, normalized across the API-changing rules:
/// a code, the symbol it rewrites, and edits that may land in any file.
type private ApiSuggestion =
    {
        Code: string
        FunctionName: string
        Edits: (Range * string * string) list
    }

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
        /// The scripts that `#r` the project's BUILT assembly, read on
        /// demand: each costs a typecheck of the project in memory, paid -
        /// like the sibling reading - only once a rule asks about a
        /// declaration's outside uses.
        Referencing: Lazy<ReferencingScripts>
    }

/// Scripts that `#r` the project's built assembly, read against its
/// SOURCES: the reference redirected to the project's in-memory
/// compilation (as a sibling project's is), so their uses carry source
/// positions and match declarations like any other call site.
and private ReferencingScripts =
    {
        /// Parse contexts of the scripts read, for rendering their edits.
        Contexts: (string * FileContext) list
        /// Their uses, indexed by the symbol's full name.
        UsesByFullName: System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>
        /// The scripts read, with the options that read them: the recheck
        /// once the edits are on disk goes through the same redirected
        /// reference - the dll they name is not rebuilt between rounds,
        /// and a rewritten call checked against it would always fail.
        Read: (string * FSharpProjectOptions) list
        /// The scripts that could NOT be read (they do not typecheck, their
        /// `#r` resolved to no reference FCS could redirect, or a use of
        /// theirs points into the project under a name the pass cannot
        /// match). Such a script sees the public declarations and its calls
        /// are out of reach, so the pass declines to reshape what it can see.
        Unread: string list
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
let private readScriptUnguarded (checker: FSharpChecker) (script: string) =
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
                    let results = checkWithin checker options

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
                    {
                        Loaded = loaded
                        Context = None
                        Uses = [||]
                        Errors =
                            results.Diagnostics
                            |> Array.filter (fun d ->
                                d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
                            |> Array.truncate 2
                            |> Array.map (fun d ->
                                $"{Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}")
                            |> List.ofArray
                    }
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

                    {
                        Loaded = loaded
                        Context =
                            Some
                                {
                                    FileName = script
                                    Source = sourceText
                                    ParseTree = parsed.ParseTree
                                }
                        Uses = uses
                        Errors = []
                    }
            | _ ->
                {
                    Loaded = [||]
                    Context = None
                    Uses = [||]
                    Errors = []
                }

        scriptCache.[script] <- (stamp, info)
        info

/// `readScriptUnguarded`, with a typecheck that never finishes (a type
/// provider waiting on its database) reported once and remembered, so no
/// later pass waits on it again.
let private readScript (checker: FSharpChecker) (script: string) =
    try
        readScriptUnguarded checker script
    with :? TimeoutException as t ->
        Out.skip $"  ({Path.GetFileName script}: {t.Message}; its calls cannot be read)"

        let info =
            {
                Loaded = [||]
                Context = None
                Uses = [||]
                Errors = [ t.Message ]
            }

        let stamp =
            try
                File.GetLastWriteTimeUtc script
            with _ -> // fsharpanalyzer: ignore-line FR0055
                DateTime.MinValue

        scriptCache.[script] <- (stamp, info)
        info

/// Read a script that `#r`s the project's built assembly, against the
/// project's SOURCES: the `-r:` FCS resolved the directive to is redirected
/// to the project's in-memory compilation, the way `readSibling` reads a
/// referencing project. Two things follow. The script's uses then carry
/// the declarations' source positions, so `sameDeclaration` matches them
/// as it matches a `#load`ing script's; and the dll on disk - built before
/// this pass and never again until the run ends - plays no part, so the
/// same options recheck the script against the REWRITTEN sources once the
/// edits are in. Farmer's amortisationFaq.fsx held every public
/// declaration of its project in place before this.
///
/// Read once per round per script: cleared with the sibling cache.
let private referencingCheckCache =
    System.Collections.Generic.Dictionary<
        string * string,
        Result<FileContext * FSharpSymbolUse[] * FSharpProjectOptions, string list>
     >()

let private readReferencingScript (checker: FSharpChecker) (project: FSharpProjectOptions) (script: string) =
    let key =
        Path.GetFullPath(script).ToLowerInvariant(), Path.GetFullPath(project.ProjectFileName).ToLowerInvariant()

    match referencingCheckCache.TryGetValue key with
    | true, known -> known
    | false, _ ->
        let read =
            try
                let text = File.ReadAllText script
                let sourceText = SourceText.ofString text
                let outputFile = outputFileNameOf project

                let referencesProject (arg: string) =
                    arg.StartsWith("-r:", StringComparison.OrdinalIgnoreCase)
                    && String.Equals(Path.GetFileName(arg.Substring 3), outputFile, StringComparison.OrdinalIgnoreCase)

                // the same two reference sets `readScript` tries, kept
                // whichever redirects and typechecks
                let attempt assumeDotNetFramework =
                    let scriptOptions, _ =
                        checker.GetProjectOptionsFromScript(
                            script,
                            sourceText,
                            assumeDotNetFramework = assumeDotNetFramework,
                            useFsiAuxLib = true
                        )
                        |> Async.RunSynchronously

                    let scriptOptions = withFsiAuxLib script scriptOptions

                    match scriptOptions.OtherOptions |> Array.tryFind referencesProject with
                    | None ->
                        Error
                            [
                                $"its #r of {outputFile} did not resolve to a reference this pass can redirect"
                            ]
                    | Some reference ->
                        let options =
                            { scriptOptions with
                                ReferencedProjects =
                                    [| FSharpReferencedProject.FSharpReference(reference.Substring 3, project) |]
                            }

                        checker.InvalidateConfiguration options
                        let results = checkProject checker options

                        let errors =
                            results.Diagnostics
                            |> Array.filter (fun d ->
                                d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

                        if Array.isEmpty errors then
                            let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

                            let parsed =
                                checker.ParseFile(script, sourceText, parsingOptions) |> Async.RunSynchronously

                            let full = Path.GetFullPath script

                            let uses =
                                results.GetAllUsesOfAllSymbols()
                                |> Array.filter (fun u ->
                                    not u.IsFromDefinition
                                    && String.Equals(
                                        Path.GetFullPath u.Range.FileName,
                                        full,
                                        StringComparison.OrdinalIgnoreCase
                                    ))

                            // a use of the project's the pass cannot name
                            // would go unmatched, and the declaration it
                            // calls reshaped one call site short - the same
                            // restraint the `#load` reading and the sibling
                            // reading apply
                            let projectFiles =
                                System.Collections.Generic.HashSet<string>(
                                    project.SourceFiles |> Array.map Path.GetFullPath,
                                    StringComparer.OrdinalIgnoreCase
                                )

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

                            if unnameable then
                                Error
                                    [
                                        "it uses a declaration of this project that the pass cannot name, so its calls cannot all be matched"
                                    ]
                            else
                                Ok(
                                    {
                                        FileName = script
                                        Source = sourceText
                                        ParseTree = parsed.ParseTree
                                    },
                                    uses,
                                    options
                                )
                        else
                            Error(
                                errors
                                |> Array.truncate 2
                                |> Array.map (fun d ->
                                    $"{Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}")
                                |> List.ofArray
                            )

                match attempt false with
                | Ok read -> Ok read
                | Error coreErrors ->
                    match attempt true with
                    | Ok read -> Ok read
                    | Error _ -> Error coreErrors
            with
            | :? IOException
            | :? UnauthorizedAccessException -> Error [ "the script could not be read" ]
            | :? TimeoutException as t -> Error [ t.Message ]

        referencingCheckCache.[key] <- read
        read

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

            [
                for kv in editsByFile do
                    for g, _, f in kv.Value do
                        if
                            appliedGroups.Contains g
                            && f.ToText.Replace("\r", "") <> f.FromText.Replace("\r", "")
                            && not (appliedIn.Contains(g, Path.GetFullPath(kv.Key).ToLowerInvariant()))
                        then
                            g
            ]
            |> Set.ofList

    // the siblings' recheck runs AFTER the edits are on disk: a typecheck
    // given up on there (checkWithin) would otherwise leave them, unread by
    // anything, for the per-target handler to skip past — so they go back
    // first, and the exception goes on to skip the target
    let brokenOutside () =
        try
            brokenElsewhere changed
        with :? TimeoutException ->
            for cf in changed do
                writeSource cf.Path cf.Before

            eprintfn
                $"  (the recheck of the projects reading this one was given up on, so the {changed.Length} file(s) this round edited were put back unverified)"

            reraise ()

    let brokenGroups =
        Set.unionMany
            [
                brokenScriptGroups
                halfAppliedGroups
                (if dryRun then Set.empty else brokenOutside ())
            ]

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

    // the directories the walk could not read (and the reparse points it
    // does not follow): scripts there, if any, are invisible to this probe
    let unwalked = ResizeArray<string>()

    let scripts =
        match searchRoot with
        | None -> [||]
        | Some dir ->
            // `ignorePaths` is honoured here DELIBERATELY, and it is not an
            // oversight that it narrows this safety probe: a path the
            // repository has told the tool to ignore is external code, and
            // external code does not get a vote on how this repository's
            // declarations are shaped. Scripts outside the target tree are
            // invisible for the same reason - the search cannot be the
            // whole disk - so the guarantee is scoped to the code this run
            // is actually responsible for, which is the honest scope.
            //
            // Walked a directory at a time, not by
            // `Directory.EnumerateFiles(_, _, AllDirectories)`: that gives
            // up the whole enumeration at the first directory it cannot
            // open, and the `with _ -> [||]` that caught it here made ONE
            // dead symlink (Fable's, under its Beam build output) drop every
            // script of the repository — and with them this guard, silently.
            // A directory the walk had to skip is recorded instead, and
            // answered for below.
            FileWalk.filesNoting "*.fsx" dir unwalked.Add
            |> Seq.filter (fun f -> not ((isBuildOutput f) || (Configuration.isIgnoredPath f)))
            |> Seq.toArray

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

    // a directory this walk could not read may hold a script that #loads
    // any file of this project, and its calls cannot be read: the same
    // restraint as for a script that does not typecheck, over every file,
    // since nothing says which. An unreadable tree used to contribute "no
    // call sites", which is the one answer this probe must never give.
    if unwalked.Count > 0 then
        let named =
            if unwalked.Count > 1 then
                unwalked.[0] + ", ..."
            else
                unwalked.[0]

        Out.skip
            $"  ({unwalked.Count} director(ies) under the target could not be searched for scripts ({named}): a script there could #load any file of this project, so none gets a cross-file signature migration (FR0049/FR0069/FR0090/FR0091/FR0093); every other rule still runs)"

        for f in options.SourceFiles do
            unverifiable.Add(Path.GetFullPath f) |> ignore

    for script in scripts do
        let info = readScript checker script
        let loaded = info.Loaded |> Array.filter projectSources.Contains

        if not (Array.isEmpty loaded) then
            match info.Context with
            | None ->
                Out.skip
                    $"  ({Path.GetFileName script} does not typecheck, so its calls cannot be read: the files it #loads get no cross-file signature migration (FR0049/FR0069/FR0090/FR0091/FR0093), every other rule still runs on them)"

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

    // a script that `#r`s the built assembly: read against the sources
    // when a rule first asks, its uses beside the `#load`ing scripts'; one
    // that also `#load`s a project source compiles that source twice (once
    // through the dll) and is left to the `#load` reading above
    let referencingRead =
        lazy
            (let read = ResizeArray()
             let unread = ResizeArray()
             let contexts = ResizeArray()

             let usesByName =
                 System.Collections.Generic.Dictionary<string, ResizeArray<FSharpSymbolUse>>()

             for script in referencing do
                 let loadsSources =
                     (readScript checker script).Loaded |> Array.exists projectSources.Contains

                 if loadsSources then
                     unread.Add script
                 else
                     match readReferencingScript checker options script with
                     | Ok(ctx, uses, scriptOptions) ->
                         contexts.Add(script, ctx)
                         read.Add(script, scriptOptions)

                         for u in uses do
                             match symbolFullName u.Symbol with
                             | Some name ->
                                 match usesByName.TryGetValue name with
                                 | true, existing -> existing.Add u
                                 | false, _ ->
                                     let fresh = ResizeArray()
                                     fresh.Add u
                                     usesByName.[name] <- fresh
                             | None -> ()
                     | Error reasons ->
                         unread.Add script

                         Out.skip
                             $"  ({Path.GetFileName script} #r's this project's built assembly and could not be checked against its sources, so its calls cannot be read; public declarations keep their shape)"

                         for reason in reasons do
                             Out.dim $"    {reason}"

             let byName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()

             for kv in usesByName do
                 byName.[kv.Key] <- kv.Value.ToArray()

             {
                 Contexts = List.ofSeq contexts
                 UsesByFullName = byName
                 Read = List.ofSeq read
                 Unread = List.ofSeq unread
             })

    let byName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()

    for kv in usesByName do
        byName.[kv.Key] <- kv.Value.ToArray()

    {
        Contexts = List.ofSeq contexts
        UsesByFullName = byName
        Unverifiable = unverifiable
        Referencing = referencingRead
    }

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
            {
                Project = sibling
                Options = project
                Contexts = []
                Uses = [||]
                Errors = errors
            }

        let info =
            match siblingOptionsCache.GetOrAdd(Path.GetFullPath sibling, optionsOf) with
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
                                    [| FSharpReferencedProject.FSharpReference(reference.Substring 3, project) |]
                            })

                match inMemory with
                | None ->
                    unreadable
                        [
                            $"its compiler arguments carry no reference to {outputFile}, so it cannot be checked against this project"
                        ]
                | Some options ->

                    // the previous round's edits are on disk; FCS must not
                    // answer from the tree it built before them
                    checker.InvalidateConfiguration options
                    let results = checkProject checker options

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
                            Options = options
                        }
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
                            [
                                for file in options.SourceFiles |> Array.filter (Path.GetFullPath >> own.Contains) do
                                    let sourceText = SourceText.ofString (File.ReadAllText file)

                                    let parsed =
                                        checker.ParseFile(file, sourceText, parsingOptions) |> Async.RunSynchronously

                                    file,
                                    {
                                        FileName = file
                                        Source = sourceText
                                        ParseTree = parsed.ParseTree
                                    }
                            ]

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

                        {
                            Project = sibling
                            Options = options
                            Contexts = contexts
                            Uses = uses
                            Errors =
                                if unnameable then
                                    [
                                        "it uses a declaration of this project that the pass cannot name, so its calls cannot all be matched"
                                    ]
                                else
                                    []
                        }

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
        {
            Contexts = []
            UsesByFullName = System.Collections.Generic.Dictionary<string, FSharpSymbolUse[]>()
            PublicRead = false
            AssemblyRead = (fun _ -> false)
            Read = []
            UnreadShared = []
            Linked = Set.empty
        }

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
                [
                    for sibling in fsharp do
                        readOne false sibling "references this project"
                    for linker, _ in linkers do
                        readOne true linker ""
                ]

            // a linker's own files, for the note on their fix lines
            let linked =
                [
                    for linker, _ in linkers do
                        let info = readSibling checker optionsOf options true linker

                        for file, _ in info.Contexts do
                            Path.GetFullPath(file).ToLowerInvariant()
                ]
                |> Set.ofList

            // the shared files of a linker that could not be read: their
            // declarations have call sites nothing can reach
            let unreadShared =
                [
                    for linker, files in linkers do
                        if not (readSibling checker optionsOf options true linker).Errors.IsEmpty then
                            yield! files
                ]

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

            {
                Contexts = readable |> List.collect (fun info -> info.Contexts)
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
                Linked = linked
            }

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
                [
                    for linker, files in linkers -> files, readSibling checker optionsOf options true linker
                ]

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

        // the unreadable `#r` scripts were reported as they were read
        let projectResults = checkProject checker options

        let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

        let fileContexts =
            System.Collections.Generic.Dictionary<string, Text.FileContext>(StringComparer.OrdinalIgnoreCase)

        for file in options.SourceFiles do
            let sourceText = SourceText.ofString (File.ReadAllText file)

            let parsed =
                checker.ParseFile(file, sourceText, parsingOptions) |> Async.RunSynchronously

            fileContexts.[Path.GetFullPath file] <-
                {
                    FileName = file
                    Source = sourceText
                    ParseTree = parsed.ParseTree
                }

        // a #loading script or a sibling's source is looked up exactly like
        // a project file: its edits are rendered from its own parse tree
        // and source
        for script, ctx in scriptSites.Contexts do
            fileContexts.[Path.GetFullPath script] <- ctx

        // a sibling's or a `#r` script's files arrive with the reading,
        // when a rule first asks for a file the project does not hold
        let fileLookup (name: string) =
            let sameFile (file: string, _) =
                String.Equals(Path.GetFullPath file, Path.GetFullPath name, StringComparison.OrdinalIgnoreCase)

            match fileContexts.TryGetValue(Path.GetFullPath name) with
            | true, ctx -> Some ctx
            | false, _ ->
                scriptSites.Referencing.Value.Contexts
                |> List.tryFind sameFile
                |> Option.orElseWith (fun () -> siblingSites.Value.Contexts |> List.tryFind sameFile)
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
            {
                Uses =
                    (fun symbol ->
                        Array.concat
                            [
                                usesIn scriptSites.UsesByFullName symbol
                                usesIn scriptSites.Referencing.Value.UsesByFullName symbol
                                usesIn siblingSites.Value.UsesByFullName symbol
                            ])
                // a script compiled against the dll that could not be read
                // against the sources is a caller of the public declarations
                // nothing can vouch for
                PublicRead = (fun () -> scriptSites.Referencing.Value.Unread.IsEmpty && siblingSites.Value.PublicRead)
                AssemblyRead = (fun name -> siblingSites.Value.AssemblyRead name)
            }

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

        // a function a STRING LITERAL names, anywhere in this project or in
        // one that reads it, has call sites no symbol table lists: a code
        // generator's template. SQLProvider.Fable's CodeGen emits
        // `Row.text r "Name"` from a string; FR0091 reordered `Row.text`,
        // rewrote the fifty calls it could see, and the generated code kept
        // the old order. Such a function keeps its shape.
        let sourcesInPlay =
            lazy
                (Seq.concat
                    [
                        options.SourceFiles |> Seq.ofArray
                        siblingSites.Value.Read |> Seq.collect (fun info -> info.Options.SourceFiles)
                        scriptSites.Referencing.Value.Read |> Seq.map fst
                    ]
                 |> Seq.distinct
                 |> List.ofSeq)

        let namedInAString (functionName: string) =
            let short = functionName.Split('.') |> Array.last
            Text.stringLiteralMentions sourcesInPlay.Value short

        let templated = ResizeArray<string>()
        let branched = ResizeArray<string>()

        // ...and one named inside an `#if` region has call sites in a
        // branch the parse tree does not hold: the migration would reach
        // one configuration's calls and leave the other's tupled
        let notTemplated (functionName: string) =
            let short = functionName.Split('.') |> Array.last

            if namedInAString functionName then
                templated.Add functionName
                false
            elif Text.namedInDirectiveRegion sourcesInPlay.Value short then
                branched.Add functionName
                false
            else
                true

        // FR0157's world: the project's uses beside every sibling's, so an
        // exported function's call sites are in sight rather than assumed
        // absent. Built once, and only once a file holds a candidate match:
        // forcing the siblings is the expensive reading
        let stringUnionWorld =
            lazy
                (let siblingUses =
                    siblingSites.Value.Read |> Seq.collect (fun info -> info.Uses) |> Array.ofSeq

                 let internalsVisible =
                     match ProjectSources.internalsVisibleTo projectResults with
                     | Some friends -> not (friends |> List.forall outside.AssemblyRead)
                     | None -> ProjectSources.hasInternalsVisibleTo projectResults

                 Analyzers.stringUnionApiWorld
                     projectResults
                     options.SourceFiles
                     siblingUses
                     (fun name -> fileLookup name |> Option.map (fun c -> c.ParseTree, c.Source))
                     // an executable's public declarations have no caller elsewhere
                     // by construction, and a `publicApi: false` says the same
                     (outside.PublicRead()
                      || (not (Visibility.publicSurfaceHeld ())
                          && Visibility.compilationIsLeaf options.SourceFiles options.OtherOptions)
                      // a script is the ultimate leaf: nothing links to it
                      || options.SourceFiles |> Array.exists Visibility.isScriptFile
                      || (options.SourceFiles
                          |> Array.exists (fun f -> Configuration.publicSurfaceSetting f = Some false)))
                     internalsVisible)

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
                        |> List.filter (fun s -> not (inUnreadShared file) && notTemplated s.FunctionName) do
                        suggestions.Add
                            {
                                Code = "FR0090"
                                FunctionName = s.FunctionName
                                Edits = s.Edits |> List.map (fun e -> e.Range, e.Original, e.Replacement)
                            }

                if wanted file "FR0091" "ParamOrder" then
                    for s in
                        ParamOrder.findApiChanges ctx checkResults projectResults fileLookup outside
                        |> List.filter (fun s -> not (inUnreadShared file) && notTemplated s.FunctionName) do
                        suggestions.Add
                            {
                                Code = "FR0091"
                                FunctionName = s.FunctionName
                                Edits = s.Edits
                            }

                if wanted file "FR0157" "StringUnion" && StringUnion.hasCandidates ctx.ParseTree then
                    for s in
                        StringUnion.find stringUnionWorld.Value ctx.ParseTree ctx.Source
                        |> List.filter (fun s -> not (inUnreadShared file) && s.Reshaped |> List.forall notTemplated) do
                        suggestions.Add
                            {
                                Code = "FR0157"
                                FunctionName = s.Name
                                Edits = s.Edits |> List.map (fun e -> e.Range, e.Original, e.Replacement)
                            }
            | FSharpCheckFileAnswer.Aborted -> ()

        if templated.Count > 0 then
            let names = templated |> Seq.distinct |> String.concat ", "

            Out.skip
                $"  ({templated.Count} migration(s) kept back: a string literal in the project names the function — a template's calls no symbol table lists: {names})"

        if branched.Count > 0 then
            let names = branched |> Seq.distinct |> String.concat ", "

            Out.skip
                $"  ({branched.Count} migration(s) kept back: the function is named inside an #if region, whose other branch has call sites no parse tree holds: {names})"

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
                    [
                        if inScripts > 0 then
                            $"{inScripts} of them in scripts"
                        if inSiblings > 0 then
                            $"{inSiblings} of them in referencing projects"
                    ]
                    |> function
                        | [] -> ""
                        | notes -> " (" + String.concat ", " notes + ")"

                printfn
                    $"  {s.Code} {kindColumn s.Code} {s.FunctionName}: {s.Edits.Length} edit(s) across the project{elsewhereNote}"

                nextGroup <- nextGroup + 1

                for range, original, replacement in s.Edits do
                    let target = Path.GetFullPath range.FileName

                    let fix =
                        {
                            FromRange = range
                            FromText = original
                            ToText = replacement
                        }

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
        ///
        /// A script that `#r`s the built assembly is rechecked the same
        /// way, through the same redirected reference: the dll it names
        /// is not rebuilt between rounds, and `readScript`'s check - the
        /// one `applyEditGroupsCheckingScripts` runs - never gives such a
        /// script a context, so this is the only check it gets.
        let outsideBroken (changed: AppliedFile list) =
            let siblings =
                if siblingSites.IsValueCreated then
                    siblingSites.Value.Read
                    |> List.map (fun info -> Path.GetFileName info.Project, info.Options)
                else
                    []

            let scripts =
                if scriptSites.Referencing.IsValueCreated then
                    scriptSites.Referencing.Value.Read
                    |> List.map (fun (script, scriptOptions) -> Path.GetFileName script, scriptOptions)
                else
                    []

            let compilations = siblings @ scripts

            if changed.IsEmpty || compilations.IsEmpty then
                Set.empty
            else
                checker.InvalidateConfiguration options


                let groupsIn (files: AppliedFile list) =
                    files |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g))

                compilations
                |> List.collect (fun (name, compilation) ->
                    checker.InvalidateConfiguration compilation
                    let results = checkProject checker compilation

                    let errors =
                        results.Diagnostics
                        |> Array.filter (fun d ->
                            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

                    let own =
                        compilation.SourceFiles
                        |> Array.map (fun f -> Path.GetFullPath(f).ToLowerInvariant())
                        |> Set.ofArray

                    let touched =
                        changed
                        |> List.filter (fun cf -> own.Contains(Path.GetFullPath(cf.Path).ToLowerInvariant()))

                    let blamed () =
                        (if touched.IsEmpty then
                             groupsIn changed
                         else
                             groupsIn touched)
                        |> List.distinct

                    // the check above saw the configuration the sibling was
                    // read under. An edited file that branches on `#if DEBUG`
                    // has call sites in the OTHER configuration's branch that
                    // no parse tree showed and the definition just changed
                    // under: only a build of that configuration knows
                    let otherConfigurationBreaks () =
                        let project = compilation.ProjectFileName

                        if
                            project.EndsWith(".fsproj", StringComparison.OrdinalIgnoreCase)
                            && File.Exists project
                            && touched |> List.exists (fun cf -> Text.hasConfigurationConditional cf.Path)
                        then
                            let other = (defaultConfiguration project).Other

                            let exitCode, stdout, stderr =
                                runForProject
                                    project
                                    processTimeout
                                    "dotnet"
                                    $"build \"{project}\" --nologo -v q -c {other}"

                            if exitCode = 0 then
                                None
                            else
                                Some(
                                    other,
                                    (stdout + stderr).Split '\n'
                                    |> Array.filter (fun l -> l.Contains "error")
                                    |> Array.map (fun l -> l.Trim())
                                    |> Array.distinct
                                )
                        else
                            None

                    // FCS checked the sibling against this project IN MEMORY - unless
                    // it could not: a project whose typecheck creates generated
                    // provided types (a JsonProvider sample, a SQL provider)
                    // yields no in-memory assembly data, and FCS binds the
                    // sibling to the dll on disk instead, built BEFORE this
                    // round's edits, so every migrated call site fails against
                    // the old signature (CarmelNet's tests against FSharp.Data).
                    // A failed check is therefore confirmed by a real build of
                    // the sibling, which builds this project first; only a
                    // build that fails blames the edits
                    let confirmedByBuild () =
                        let project = compilation.ProjectFileName

                        if
                            not (Array.isEmpty errors)
                            && project.EndsWith(".fsproj", StringComparison.OrdinalIgnoreCase)
                            && File.Exists project
                        then
                            let exitCode, stdout, stderr =
                                runForProject project processTimeout "dotnet" $"build \"{project}\" --nologo -v q"

                            if exitCode = 0 then
                                Out.dim
                                    $"  ({name}: the in-memory typecheck reported errors but the project builds with the edits; the check bound to a stale assembly - a type provider's, most likely)"

                                // the next pass reads the sibling the same way, so
                                // the assembly it binds to must carry this pass's
                                // edits: every framework's, the sibling's arguments
                                // may name the one this compilation analyses
                                let own = Path.GetFullPath options.ProjectFileName

                                if own.EndsWith(".fsproj", StringComparison.OrdinalIgnoreCase) && File.Exists own then
                                    runForProject own processTimeout "dotnet" $"build \"{own}\" --nologo -v q"
                                    |> ignore

                                false
                            else
                                true
                        else
                            not (Array.isEmpty errors)

                    if confirmedByBuild () then
                        let blamed = blamed ()

                        Out.skip
                            $"  ({name} stopped typechecking after the edits: {blamed.Length} suggestion(s) put back)"

                        for d in errors |> Array.truncate 2 do
                            Out.dim $"    {Path.GetFileName d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"


                        blamed
                    else
                        match otherConfigurationBreaks () with
                        | Some(other, lines) ->
                            let blamed = blamed ()

                            Out.skip
                                $"  ({name} stopped building as {other} after the edits — the #if branch the analysis could not see: {blamed.Length} suggestion(s) put back)"

                            for l in lines |> Array.truncate 2 do
                                Out.dim $"    {l}"

                            blamed
                        | None -> [])
                |> Set.ofList

        linkedFiles.Clear()

        if siblingSites.IsValueCreated then
            linkedFiles.UnionWith siblingSites.Value.Linked

        try
            applyEditGroupsCheckingScripts checker dryRun suppressed outsideBroken editsByFile
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
        let text = projectTextWithoutComments (File.ReadAllText projectPath)

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
                    [
                        for c in defineMatch.Groups.[2].Value.Split ';' do
                            let c = c.Trim()

                            if c <> "" && not (c.Contains "$(") then
                                c
                    ]

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

/// `#if INTERACTIVE` / `#if !INTERACTIVE` / `#if COMPILED` is how a file
/// is written to work as both a project source and a `#load`ed script:
/// the script half skips the email send or the service call, the
/// compiled half does it. Neither symbol ever varies BETWEEN a project's
/// frameworks — INTERACTIVE is never defined in a project compilation,
/// COMPILED always is — so a file whose only conditions are those still
/// parses identically under every framework and needs one sweep, not one
/// per framework. (Between a project and a script it does vary; a script
/// leaves the project's files to the project — see projectCompiling.)
let private interactiveOnlyCondition =
    Text.RegularExpressions.Regex(
        @"^#if\s+[!\s()]*(INTERACTIVE|COMPILED)(\s*(&&|\|\|)\s*[!\s()]*(INTERACTIVE|COMPILED))*[\s()]*(//.*)?$"
    )

let internal isDirectiveFree (path: string) =
    directiveFreeCache.GetOrAdd(
        path,
        fun p ->
            try
                File.ReadLines p
                |> Seq.forall (fun l ->
                    let line = l.TrimStart()
                    not (line.StartsWith "#if") || interactiveOnlyCondition.IsMatch line)
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false
    )

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
                not (File.Exists path) || not (isDirectiveFree path))
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

/// The project that compiles a source file a SCRIPT `#load`s, when one
/// does: an fsproj in the file's directory or one above it (up to the
/// repository root) whose `<Compile>` items name it.
///
/// A script compiles what it `#load`s into ITSELF, against the script
/// host's reference set — .NET Core, or Framework on the retry — and the
/// script's check then passes for the script. It says nothing about the
/// project the file was written for: Owin.Compression's Script.fsx
/// `#load`s CompressionModule.fs, a net48 source, and the script's sweep
/// wrote `Convert.ToHexString` and `File.ReadAllBytesAsync` into it —
/// both real under the script's .NET 10, neither on net48, and the net48
/// project, checked a compilation EARLIER, never saw them. The sweep dedup
/// does not cover this: it keys on conditional defines, the file carries
/// an `#if INTERACTIVE`, and the script's defines differ. So a file a
/// project owns is the project's to edit; the script sweeps only what no
/// project claims. Memoised per file: a run of many scripts asks about
/// the same shared sources over and over.
let private projectCompilingCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, string option>(StringComparer.OrdinalIgnoreCase)

let private projectCompiling (file: string) : string option =
    projectCompilingCache.GetOrAdd(
        file,
        fun f ->
            let full = Path.GetFullPath f
            let key = full.ToLowerInvariant()

            let rec climb (dir: string) (depth: int) =
                if isNull dir || depth > 8 then
                    None
                else
                    let here =
                        try
                            Directory.EnumerateFiles(dir, "*.fsproj")
                            |> Seq.tryFind (fun p -> (compileItemsOf p).ContainsKey key)
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            None

                    match here with
                    | Some p -> Some p
                    | None when
                        Directory.Exists(Path.Combine(dir, ".git"))
                        || File.Exists(Path.Combine(dir, ".git"))
                        ->
                        None // the repository root: a project above it is another repository's
                    | None -> climb (Path.GetDirectoryName dir) (depth + 1)

            climb (Path.GetDirectoryName full) 0
    )

/// Fixes applied anywhere in this run so far — the whole-compilation skip
/// is only sound while the tree is untouched (or the run is a dry run).
let mutable internal runTotalApplied = 0

/// Compilations this run attempted — a multi-targeted project contributes
/// one per framework, which is what the coverage warning counts against.
let mutable internal runCompilations = 0

/// Why each compilation of this run exited non-zero, one line each
/// ("Tests.fsproj [net9.0]: all 25 changed file(s) put back by the
/// all-frameworks build"). The run's exit code is the worst of them, and
/// without this list a reader of an hour-long log had to find the one
/// put-back paragraph that explained an exit 1 the tail never mentioned
/// (FsToolkit: exit 1, no line saying why).
let internal exitReasons = ResizeArray<string>()

/// Compilations this run could not analyse because they would not build.
/// The exit code already reflects them, but a HUMAN reads the tail of the
/// output, and the per-project errors scroll past long before it: a
/// SwaggerProvider clone missing its paket restore failed 7 of 10
/// compilations and still signed off with a cheerful finding count. A
/// silent gap in coverage reads exactly like clean code.
let mutable internal runBuildFailures = 0

/// Rule invocations this run abandoned because the rule threw. Caught per
/// file so one rule's bug costs its findings in that file and not the run
/// — but a silently skipped rule looks exactly like a clean file, so each
/// is counted here, named among the exit reasons, and the run exits
/// non-zero for it.
let mutable internal runAnalyzerFailures = 0

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
        [
            for l in firstContext..lastContext -> whitespaceRunRegex.Replace(source.GetLineString(l).Trim(), " ")
        ]
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
        [
            "startLine", box (max 1 startLine)
            "startColumn", box (startColumn + 1)
            "endLine", box (max 1 endLine)
            "endColumn", box (endColumn + 1)
        ]

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
                [
                    "id", box code
                    "name", box code
                    "shortDescription", box (dict [ "text", box description ])
                    "fullDescription", box (dict [ "text", box $"{description} ({category} rule of fsharp-refactor)" ])
                    "helpUri", box "https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md"
                    "help", box (dict [ "text", box $"See {code} in Rules.md." ])
                    "defaultConfiguration", box (dict [ "level", box (reportLevel code Severity.Hint) ])
                    "properties",
                    box (dict [ "category", box category; "tags", box [ category; "fsharp"; "refactoring" ] ])
                ])

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
        [
            for f in findings ->
                let snippetStart, snippetEnd = f.SnippetLines

                let entries =
                    [
                        "ruleId", box f.Code
                        "ruleIndex", box ruleIndex.[f.Code]
                        "level", box (reportLevel f.Code f.Severity)
                        "message", box (dict [ "text", box (plainMessage f) ])
                        // stable across line shifts and sessions; the baseline
                        // mechanism keys on this
                        "partialFingerprints", box (dict [ FingerprintKey, box f.Fingerprint ])
                        "properties",
                        box (dict [ "autoFixable", box f.Fixable; "category", box (reportCategory f.Code) ])
                        "locations",
                        box
                            [
                                dict
                                    [
                                        "physicalLocation",
                                        box (
                                            dict
                                                [
                                                    "artifactLocation", box (artifactLocation f.File)
                                                    // the range itself, with its text
                                                    "region",
                                                    box (
                                                        dict (
                                                            regionEntries (
                                                                f.StartLine,
                                                                f.StartColumn,
                                                                f.EndLine,
                                                                f.EndColumn
                                                            )
                                                            @ [ "snippet", box (dict [ "text", box f.RegionText ]) ]
                                                        )
                                                    )
                                                    // the surrounding lines: saves the
                                                    // reader (human or agent) one
                                                    // file-open per finding
                                                    "contextRegion",
                                                    box (
                                                        dict
                                                            [
                                                                "startLine", box snippetStart
                                                                "endLine", box snippetEnd
                                                                "snippet", box (dict [ "text", box f.Snippet ])
                                                            ]
                                                    )
                                                ]
                                        )
                                    ]
                            ]
                    ]

                // the fix as SARIF spells it: code scanning shows it as a
                // suggested change, and any consumer can apply it
                let fixes =
                    match f.Fixes with
                    | [] -> []
                    | edits ->
                        [
                            "fixes",
                            box
                                [
                                    dict
                                        [
                                            "description",
                                            box (dict [ "text", box $"{f.Code}: {RuleCatalog.describe f.Code}" ])
                                            "artifactChanges",
                                            box
                                                [
                                                    dict
                                                        [
                                                            "artifactLocation", box (artifactLocation f.File)
                                                            "replacements",
                                                            box
                                                                [
                                                                    for (sl, sc, el, ec, _, text) in edits ->
                                                                        dict
                                                                            [
                                                                                "deletedRegion",
                                                                                box (region (sl, sc, el, ec))
                                                                                "insertedContent",
                                                                                box (dict [ "text", box text ])
                                                                            ]
                                                                ]
                                                        ]
                                                ]
                                        ]
                                ]
                        ]

                dict (entries @ fixes)
        ]

    let invocation =
        dict
            [
                "executionSuccessful", box true
                "startTimeUtc", box (startedUtc.ToString("o"))
                "endTimeUtc", box (DateTime.UtcNow.ToString("o"))
                "workingDirectory",
                box (
                    dict
                        [
                            "uri", box (fileUri (Directory.GetCurrentDirectory().Replace('\\', '/').TrimEnd('/') + "/"))
                        ]
                )
                "commandLine", box (Environment.CommandLine)
            ]

    // the id code scanning files this run under: one per target, so a
    // repository with several solutions keeps their reports apart
    let automationId =
        let name = Path.GetFileName(target.TrimEnd('\\', '/'))
        let name = if String.IsNullOrEmpty name then "run" else name
        $"fsharp-refactor/{name}/"

    let report =
        dict
            [
                "$schema", box "https://json.schemastore.org/sarif-2.1.0.json"
                "version", box "2.1.0"
                "runs",
                box
                    [
                        dict
                            [
                                "tool",
                                box (
                                    dict
                                        [
                                            "driver",
                                            box (
                                                dict
                                                    [
                                                        "name", box "fsharp-refactor"
                                                        "fullName",
                                                        box "fsharp-refactor: F# refactoring analyzers and apply tool"
                                                        "version", box toolVersion.Value
                                                        "semanticVersion", box toolVersion.Value
                                                        // the URL the package and --help both publish; this
                                                        // one said FSharp.Refactorings, and it is the link
                                                        // GitHub code scanning puts in front of users
                                                        "informationUri",
                                                        box "https://github.com/Thorium/fsharp-refactor"
                                                        "rules", box rulesMetadata
                                                    ]
                                            )
                                        ]
                                )
                                "automationDetails", box (dict [ "id", box automationId ])
                                "originalUriBaseIds", box (dict [ "%SRCROOT%", box (dict [ "uri", box rootUri ]) ])
                                "invocations", box [ invocation ]
                                "artifacts", box artifacts
                                "columnKind", box "utf16CodeUnits"
                                "results", box results
                            ]
                    ]
            ]

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
                    [
                        "Rule"
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
                        "Fingerprint"
                    ]

            for f in findings do
                yield
                    row
                        [
                            f.Code
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
                            f.Fingerprint
                        ]
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
    let projectResults = checkProject checker options
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

            let! parseResults, checkAnswer =
                checker.ParseAndCheckFileInProject(file, 0, sourceText, options)

            checkSw.Stop()

            match checkAnswer with
            | FSharpCheckFileAnswer.Succeeded checkResults ->
                let context: CliContext =
                    {
                        FileName = file
                        SourceText = sourceText
                        ParseFileResults = parseResults
                        CheckFileResults = checkResults
                        // the typed tree is not kept (keepAssemblyContents = false): no rule of
                        // ours reads it, and keeping it held every project's typed trees - 6.3 GB
                        // peak on Fuuga against 0.7 without
                        TypedTree = None
                        CheckProjectResults = projectResults
                        ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
                        // `// fsharpanalyzer: ignore-line FR0031` and friends
                        // (ignore-line-next, ignore-file, ignore-region-start/
                        // end) — the SDK's own suppression comments, honored
                        // here exactly as editors honor them
                        AnalyzerIgnoreRanges = Ignore.getAnalyzerIgnoreRanges parseResults sourceText
                    }

                let timings = ResizeArray<string * int64>()
                let collected = ResizeArray<Message>()

                // an analyzer that throws must not take the run down, but
                // say so: a silently skipped rule looks like a clean file.
                // `Invoke` only BUILDS the rule's Async — the body runs at
                // `return! work`, and the deep-stack worker rethrows its
                // exception as the original type, so only a catch-all here
                // sees it: with the two named cases alone, one rule's
                // KeyNotFoundException ended a whole workspace sweep.
                let analyzerFailed (kind: string) (m: MethodInfo) (ex: exn) =
                    System.Threading.Interlocked.Increment(&runAnalyzerFailures) |> ignore
                    eprintfn $"  ({kind} {m.Name} failed on {file}: {ex.GetType().Name}: {ex.Message})"

                    // one reason per rule and compilation: the tail of the
                    // run names the rule, the lines above name the files
                    let reason =
                        $"{Path.GetFileName options.ProjectFileName}: {kind} {m.Name} threw {ex.GetType().Name}, so its findings in the file(s) named above are unknown"

                    lock exitReasons (fun () ->
                        if not (exitReasons.Contains reason) then
                            exitReasons.Add reason)

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
                            | :? TargetInvocationException as ex when not (isNull ex.InnerException) ->
                                analyzerFailed "analyzer" m ex.InnerException
                                return []
                            | :? InvalidCastException as ex ->
                                eprintfn $"  (analyzer {m.Name} has an unexpected signature: {ex.Message})"
                                analyzerFailed "analyzer" m ex
                                return []
                            | ex ->
                                analyzerFailed "analyzer" m ex
                                return []
                        }

                    sw.Stop()
                    timings.Add(m.Name, sw.ElapsedMilliseconds)
                    collected.AddRange produced

                if editorOffers then
                    let editorContext: EditorContext =
                        {
                            FileName = file
                            SourceText = sourceText
                            ParseFileResults = parseResults
                            CheckFileResults = Some checkResults
                            // the typed tree is not kept (keepAssemblyContents = false): no rule of
                            // ours reads it, and keeping it held every project's typed trees - 6.3 GB
                            // peak on Fuuga against 0.7 without
                            TypedTree = None
                            CheckProjectResults = Some projectResults
                            ProjectOptions = context.ProjectOptions
                            AnalyzerIgnoreRanges = context.AnalyzerIgnoreRanges
                        }

                    for m in editorAnalyzers.Value do
                        let! produced =
                            async {
                                try
                                    let work = m.Invoke(null, [| box editorContext |]) :?> Async<Message list>
                                    return! work
                                with
                                | :? TargetInvocationException as ex when not (isNull ex.InnerException) ->
                                    analyzerFailed "editor analyzer" m ex.InnerException
                                    return []
                                | :? InvalidCastException as ex ->
                                    eprintfn $"  (editor analyzer {m.Name} has an unexpected signature: {ex.Message})"
                                    analyzerFailed "editor analyzer" m ex
                                    return []
                                | ex ->
                                    analyzerFailed "editor analyzer" m ex
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

                    {
                        File = findingFile
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
                        RegionText = regionText
                    }

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
                            Message = m.Message + " (suppression comment not honored — \"suppressions\" policy)"
                        })

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
                    {|
                        File = file
                        CheckMs = checkSw.ElapsedMilliseconds
                        Timings = List.ofSeq timings
                        HasErrors = OptionModule.hasErrors checkResults
                        Messages = messages
                        Notes = notes
                        Comments = commentsIn parseResults.ParseTree sourceText
                    |}
            | FSharpCheckFileAnswer.Aborted ->
                return
                    {|
                        File = file
                        CheckMs = checkSw.ElapsedMilliseconds
                        Timings = []
                        HasErrors = true
                        Messages = []
                        Notes = []
                        Comments = []
                    |}
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

    // a script's `#load`ed sources that some project compiles: the
    // project's reference set is the one the file was written against,
    // and the project's build check the one that would catch a fix that
    // only holds under the script host's (see projectCompiling)
    let projectOwned, filesToSweep =
        if options.UseScriptResolutionRules then
            filesToSweep
            |> Array.partition (fun f -> not (Visibility.isScriptFile f) && (projectCompiling f).IsSome)
        else
            [||], filesToSweep

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

    if projectOwned.Length > 0 then
        let names =
            projectOwned
            |> Array.map (fun f ->
                let owner =
                    projectCompiling f |> Option.map Path.GetFileName |> Option.defaultValue "?"

                $"{Path.GetFileName f} ({owner})")
            |> String.concat ", "

        Out.skip
            $"  ({projectOwned.Length} #loaded file(s) left to the project that compiles them — a script's reference set is not the project's: {names})"

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

        let targetOf (f: Fix) =
            Path.GetFullPath(
                if String.IsNullOrEmpty f.FromRange.FileName then
                    outcome.File
                else
                    f.FromRange.FileName
            )

        // a fix landing in this file's own COMPANION SIGNATURE is not
        // a cross-file change. It is the other half of a single edit -
        // naming a union case's fields in the .fs while the .fsi still
        // declares them unnamed does not compile - so gating it behind
        // --api-changes would apply one half and roll the pair back.
        let isSameFile (target: string) =
            String.Equals(target, Path.GetFullPath outcome.File, StringComparison.OrdinalIgnoreCase)
            || (companionSignature <> ""
                && String.Equals(target, companionSignature, StringComparison.OrdinalIgnoreCase))

        // a single-line edit that changes its line's length, with the next
        // line anchored to an offside context that opens after the edit -
        // the operand of a paren block, a tuple element under its sibling
        // - and would read differently once that anchor moves (see
        // Text.alignmentHazard: a line to the right of every anchor is a
        // continuation before and after, and is not held). The rules that
        // shorten lines most (FR0094, FR0013) check the same layout
        // themselves; this is the backstop for every rule, found on
        // fparsec's CharParsers.fs where FR0094 dropped two characters and
        // the `(flags <- ...` block's lines under them stayed put. Held at
        // MESSAGE level: a compound fix applies whole or not at all
        let sourceLines =
            lazy
                (try
                    File.ReadAllLines outcome.File
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     [||])

        let breaksAlignment (f: Fix) =
            f.FromRange.StartLine = f.FromRange.EndLine
            && not (f.ToText.Contains '\n')
            && (let lines = sourceLines.Value

                f.FromRange.StartLine <= lines.Length
                && Text.alignmentHazard
                    (fun l -> lines.[l - 1])
                    lines.Length
                    f.FromRange.StartLine
                    f.FromRange.EndColumn
                    (f.ToText.Length - (f.FromRange.EndColumn - f.FromRange.StartColumn)))

        // a fix whose span covers a `#if` / `#else` / `#endif` line: the
        // parse tree only sees the active branch, so the replacement
        // would splice the directive structure apart and leave the OTHER
        // configuration's code broken or gone. Most rules ask
        // Text.spansDirective themselves; this is the backstop for every
        // rule, since one that does not is one directive away from
        // deleting an `#else` branch
        let spansDirective (f: Fix) =
            let lines = sourceLines.Value

            f.FromRange.StartLine <> f.FromRange.EndLine
            && seq { f.FromRange.StartLine .. min f.FromRange.EndLine lines.Length }
               |> Seq.exists (fun l ->
                   let text = lines.[l - 1].TrimStart()

                   text.StartsWith "#if" || text.StartsWith "#else" || text.StartsWith "#endif")

        for msg in outcome.Messages do
            nextGroup <- nextGroup + 1

            let alignmentHazard =
                msg.Fixes
                |> List.exists (fun f -> isSameFile (targetOf f) && (breaksAlignment f || spansDirective f))

            for f in msg.Fixes do
                let target = targetOf f
                let sameFile = isSameFile target

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
                    || alignmentHazard
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
            [
                yield! Directory.EnumerateFiles(d, "*.slnx")
                yield! Directory.EnumerateFiles(d, "*.sln")
            ]

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

/// The compiler arguments with every relative path made absolute against
/// the project directory. MSBuild hands fsc paths as the project spells
/// them, relative to its own directory, which is fsc's working directory
/// under a build — and is not this process's: a solution run starts from
/// the solution's root and the tool checks each project from wherever it
/// was started. A relative `--keyfile:`, `--doc:`, `--resource:`, `-r:`
/// or `--lib:` in the arguments would otherwise be looked for in the wrong
/// place. The source-attribute twin of the key file (AssemblyKeyFile in an
/// AssemblyInfo.fs) never appears here; `checkProject` covers that one.
let internal absolutizeArgs (projectDir: string) (args: string array) =
    let rebase (path: string) =
        let trimmed = path.Trim().Trim '"'

        if trimmed = "" || Path.IsPathRooted trimmed then
            path
        else
            Path.GetFullPath(Path.Combine(projectDir, trimmed))

    // `--resource:file[,name[,public|private]]` — the file is the first
    // component; `--lib:` takes a `;`-separated list
    let firstComponentOf (separator: char) (value: string) =
        value.Split separator
        |> Array.mapi (fun i part -> if i = 0 then rebase part else part)
        |> String.concat (string separator)

    let everyComponentOf (separator: char) (value: string) =
        value.Split separator |> Array.map rebase |> String.concat (string separator)

    let single =
        [
            "-r:"
            "--reference:"
            "--doc:"
            "-o:"
            "--out:"
            "--keyfile:"
            "--pdb:"
            "--win32res:"
            "--win32manifest:"
            "--win32icon:"
        ]

    args
    |> Array.map (fun arg ->
        let lower = arg.ToLowerInvariant()

        match single |> List.tryFind lower.StartsWith with
        | Some flag -> arg.Substring(0, flag.Length) + rebase (arg.Substring flag.Length)
        | None ->
            if lower.StartsWith "--resource:" || lower.StartsWith "--linkresource:" then
                let colon = arg.IndexOf ':'
                arg.Substring(0, colon + 1) + firstComponentOf ',' (arg.Substring(colon + 1))
            elif lower.StartsWith "--lib:" || lower.StartsWith "-i:" then
                let colon = arg.IndexOf ':'
                arg.Substring(0, colon + 1) + everyComponentOf ';' (arg.Substring(colon + 1))
            else
                arg)

/// Compiler arguments read ahead for a framework not yet analysed (see
/// prefetchNextFramework), keyed by full project path and framework and
/// taken exactly once: the framework's own turn starts from them.
let private prefetchedOptions =
    System.Collections.Concurrent.ConcurrentDictionary<string * string, Result<FSharpProjectOptions, string>>()

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
        let mutable ahead = Unchecked.defaultof<_>

        if prefetchedOptions.TryRemove((Path.GetFullPath project, chosenFramework), &ahead) then
            Out.dim "compiler arguments read ahead during the previous framework's pass"
            ahead
        else

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
                    args
                    |> Array.filter (isOutputOnly >> not)
                    |> absolutizeArgs projectDir
                    |> Array.partition isSource

                let absoluteSources =
                    sources
                    |> Array.map (fun s ->
                        if Path.IsPathRooted s then
                            s
                        else
                            Path.Combine(projectDir, s))

                Ok
                    { checker.GetProjectOptionsFromCommandLineArgs(Path.GetFullPath project, otherArgs) with
                        SourceFiles = absoluteSources
                    }

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

/// The lines a failed build is judged by: every distinct line naming an
/// error — or, when it reported none, the tail of what it did say. A build
/// stopped at the time cap (runProcessIn's `TimeCapMark` line), one whose
/// `dotnet` could not start, or one that crashed has no error line at
/// all, and keeping only those left `[||]`: an empty list that the
/// baseline comparison read as "no compiler error introduced" and so as
/// pre-existing breakage, fixes kept. The tail keeps the reason on record,
/// and `stoppedAtTimeCap` finds the cap among it.
let internal buildFailureLines (stdout: string) (stderr: string) =
    let lines =
        (stdout + stderr).Split '\n'
        |> Array.map (fun l -> l.Trim())
        |> Array.filter (fun l -> l <> "")

    let errors = lines |> Array.filter (fun l -> l.Contains "error") |> Array.distinct

    if Array.isEmpty errors then
        lines |> Array.skip (max 0 (lines.Length - 5)) |> Array.distinct
    else
        errors

/// A compiler's error line: F#'s `error FS1234`, or — from a referencing
/// C# or VB project built with the verification — `error CS0426`,
/// `error BC30002`. Tooling (MSB*, NETSDK*, NU*) is deliberately not one.
let private compilerErrorRegex =
    Text.RegularExpressions.Regex(@"error (?:FS|CS|BC)\d+", Text.RegularExpressions.RegexOptions.Compiled)

/// Did a failed build say anything about the CODE? Only a compiler error
/// can be this run's doing — see judgeAgainstBaseline: a source edit
/// cannot make an assets file lose a framework or a package fail to
/// resolve, so the baseline comparison weighs these lines alone.
let internal hasCompilerErrors (errors: string array) =
    errors |> Array.exists compilerErrorRegex.IsMatch

/// Was this build stopped at the time cap? The one failure that is not a
/// failed build at all: it compiled none of what it was asked to, so it
/// can neither clear the fixes nor blame them, and a baseline compared
/// against it compares nothing (see judgeAgainstBaseline). Tested by the
/// marker runProcessIn writes, not by the prose around it.
let internal stoppedAtTimeCap (errors: string array) =
    errors
    |> Array.exists (fun e -> e.StartsWith(TimeCapMark, StringComparison.Ordinal))

/// One `dotnet build` of a project — of any language — run from its own
/// directory, its failure as the lines the baseline comparison judges by.
let private buildOnce (project: string) (arguments: string) =
    let exitCode, stdout, stderr =
        runForProject project processTimeout "dotnet" $"build \"{project}\" --nologo -v q{arguments}"

    if exitCode = 0 then
        Ok()
    else
        Error(buildFailureLines stdout stderr)

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

    let build (arguments: string) = buildOnce project arguments

    match build "" with
    | Ok() when hasConfigurationConditionals project ->
        // the configuration the analysis did not see: its `#if` branches
        // hold code no rule read, and a migration's call sites among them
        let other = (defaultConfiguration project).Other

        printfn $"  (the sources branch on the build configuration: building {other} too)"
        build $" -c {other}"
    | result -> result

/// Per project and run: the consumers of another language that build here
/// and the ones that do not (see consumersOf). Asked by every framework
/// pass over the project and again at its verification, and the probe is
/// a build.
let private consumerProjects =
    System.Collections.Concurrent.ConcurrentDictionary<string, string list * string list>(
        StringComparer.OrdinalIgnoreCase
    )

/// The C# and VB projects that reference `project` — those of its solution,
/// or of the directory the run was pointed at (Workspace.workspaceOf), with
/// a `ProjectReference` to it, directly or through another — split into
/// the ones the verification can BUILD and the ones it cannot.
///
/// The verification build of an F# project compiles F#. A C# project in
/// the same solution casting to a union's nested case class consumes the
/// public surface through a compile no F# check ever runs: FR0016 made
/// FSharp.Azure.Quantum's union a struct under --api-changes, the F#
/// project built, the C# one stopped compiling — and the tool, seeing
/// success, re-applied the change after the user had reverted it by hand.
/// So a consumer that builds as the tree stands joins the verification
/// build, where its failure with the fixes and not without them puts them
/// back like an F# framework's would. One that does not build as it
/// stands — no SDK for its framework, broken before this run — can verify
/// nothing, and the project's public surface is held for it instead
/// (Scope.PublicSurfaceHeld), said out loud. Not probed when nothing will
/// be written (`probe` is off on a dry run): every consumer then counts
/// as buildable, and the verification that would build it never runs.
let private consumersOf (probe: bool) (root: string) (project: string) : string list * string list =
    consumerProjects.GetOrAdd(
        Path.GetFullPath project,
        fun full ->
            let foreign =
                match Workspace.workspaceOf root full with
                | None -> []
                | Some workspace ->
                    // resolved paths only: a by-name or unresolvable reference
                    // would make one csproj the consumer of every project in a
                    // whole-tree run, probed once per project
                    Workspace.resolvedReferencersOf workspace full
                    |> List.filter (Workspace.isFSharpProject >> not)

            let names (projects: string list) =
                projects |> List.map Path.GetFileName |> String.concat ", "

            let verb (projects: string list) =
                if projects.Length = 1 then "references" else "reference"

            if foreign.IsEmpty then
                [], []
            elif not probe then
                Out.dim
                    $"  ({names foreign} {verb foreign} this project, and would be built with it to verify the fixes of a run that writes)"

                foreign, []
            else
                let buildable, held =
                    foreign
                    |> List.partition (fun consumer ->
                        match buildOnce consumer "" with
                        | Ok() -> true
                        | Error lines ->
                            Out.skip
                                $"  ({Path.GetFileName consumer} references this project and does not build here, so it cannot verify this run's fixes; public declarations keep their shape)"

                            for line in lines |> Array.truncate 3 do
                                Out.dim $"    {line}"

                            false)

                if not buildable.IsEmpty then
                    printfn
                        $"  ({names buildable} {verb buildable} this project: built with it to verify this run's fixes, since a public shape it links to can change under it)"

                buildable, held
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
type internal Blame =
    /// Every error was there before the fixes: theirs, not ours.
    | PreExisting
    /// The build fails differently from one run to the next, so an error
    /// seen only with the fixes proves nothing either way.
    | Unverifiable
    /// Errors that appear with the fixes and never without them.
    | Introduced of Set<string>
    /// A build in the comparison was stopped at the time cap: it compiled
    /// nothing, so nothing it said is about the code, and the fixes are
    /// neither cleared nor blamed — they are unverified, and an unverified
    /// fix does not stay.
    | NotVerified

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
/// baseline gets a second baseline build (`rebuild`): a build that is
/// already broken is often broken DIFFERENTLY from run to run, and where
/// the two baselines disagree the failure is not evidence of anything.
///
/// But a build stopped at the time cap is not "no compiler error
/// introduced". A verification build that ran into the 15-minute cap came
/// back as `Error [||]`, the difference of two empty sets was empty, and
/// every fix was written back as "pre-existing breakage" — the build had
/// never compiled a line of them. Either side stopped at the cap, or a
/// second baseline stopped there, is NotVerified, whatever the other says.
///
/// The cap ALONE, though. A build that fails on its tooling with the fixes
/// and without them — a post-compile `Exec` target (MSB3073), packing in
/// Release (NU5xxx), a targeting pack that is not installed (NETSDK1045,
/// MSB3644) — did compile the code and said nothing against it: that is
/// pre-existing breakage, fixes kept, as it always was. Reading every
/// failure without a compiler error as the cap restored whole snapshots on
/// repositories that could then never keep a fix.
let internal judgeAgainstBaseline
    (rebuild: unit -> Result<unit, string array>)
    (withFixes: string array)
    (firstBaseline: string array)
    =
    let compilerErrors (errors: string array) =
        errors
        |> Array.filter compilerErrorRegex.IsMatch
        |> Array.map errorSignature
        |> Set.ofArray

    if stoppedAtTimeCap withFixes || stoppedAtTimeCap firstBaseline then
        NotVerified
    else
        let introduced =
            Set.difference (compilerErrors withFixes) (compilerErrors firstBaseline)

        if introduced.IsEmpty then
            PreExisting
        else
            match rebuild () with
            // the first baseline failed on tooling alone (a file in use right
            // after a build, a restore hiccup) and the rebuild passes: the code
            // without the fixes compiles, so every compiler error the build
            // with them reported is theirs - "the two baselines disagree" is
            // not the case, both say the same about the code
            | Ok() when not (hasCompilerErrors firstBaseline) -> Introduced introduced
            | Ok() -> Unverifiable
            | Error secondBaseline when stoppedAtTimeCap secondBaseline -> NotVerified
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

    for KeyValue(path, text) in snapshot do
        let full = Path.GetFullPath path
        snapshotFiles.Add full |> ignore
        runOriginals.TryAdd(full, text) |> ignore

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

let private errorSiteRegex =
    System.Text.RegularExpressions.Regex(
        @"^\s*(?<file>[^\r\n(]+?)\(\d+,\d+\):\s*error ",
        System.Text.RegularExpressions.RegexOptions.Multiline
    )

/// A compilation fails to build on files an EARLIER compilation of this
/// run rewrote: the failure is the run's own - a file several projects
/// compile holds to every one of them, and the first project's build
/// check spoke for itself alone (elmish's src/program.fs: interpolated
/// under Elmish.fsproj on FSharp.Core 10, then Fable.Elmish.fsproj on 4.7
/// would not build, and the run blamed the tree). Those files go back to
/// the text the run started from; returns each with the text it carried,
/// so the caller can load the compilation again - and hand the text back
/// when that fails too, since the failure was then never ours.
let internal putBackRunEdits (buildMessage: string) (label: string) =
    [
        for m in errorSiteRegex.Matches buildMessage -> m.Groups.["file"].Value.Trim()
    ]
    |> List.filter Path.IsPathRooted
    |> List.map Path.GetFullPath
    |> List.distinct
    |> List.choose (fun file ->
        match runOriginals.TryGetValue file with
        | true, original ->
            try
                let current = File.ReadAllText file

                if current <> original then
                    writeSource file original

                    eprintfn
                        $"  put back {Path.GetFileName file}: rewritten by an earlier compilation of this run, and {label} does not build with it"

                    Some(file, current)
                else
                    None
            with
            | :? IOException
            | :? UnauthorizedAccessException -> None
        | false, _ -> None)

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
        [
            for g, code, f in ascending do
                let patchedStart = f.FromRange.StartLine + delta
                let patchedEnd = patchedStart + newlinesIn f.ToText

                if errorLines |> Set.exists (fun l -> l >= patchedStart - 5 && l <= patchedEnd + 5) then
                    g, code, f

                delta <- delta + (newlinesIn f.ToText - newlinesIn f.FromText)
        ]

    // a culprit's WHOLE suggestion group joins it: a multi-edit suggestion
    // applies all-or-nothing, and keeping half (a ParamOrder def swap
    // without its call sites) can compile into wrong code
    let culpritGroups = near |> List.map (fun (g, _, _) -> g) |> Set.ofList

    cf.Fixes |> List.filter (fun (g, _, _) -> culpritGroups.Contains g)

let private verifyPassChecked
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

        // the text of each changed file as the pass left it, read before
        // anything is put back: what a kept file is written back to
        let appliedTexts =
            changedFiles
            |> List.map (fun cf ->
                cf.Path,
                (try
                    File.ReadAllText cf.Path
                 with _ -> // unreadable now: the same fixes re-applied to the pre-pass text; fsharpanalyzer: ignore-line FR0055
                     reapplySubset cf.Before cf.Fixes))
            |> Map.ofList

        let appliedTextOf (cf: AppliedFile) =
            match Map.tryFind cf.Path appliedTexts with
            | Some text -> text
            | None -> reapplySubset cf.Before cf.Fixes

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
                            [
                                for cf in changedFiles |> List.except named do
                                    let orphans = cf.Fixes |> List.filter (fun (g, _, _) -> culpritGroups.Contains g)

                                    if not orphans.IsEmpty then
                                        writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except orphans))

                                        for _, code, f in orphans do
                                            suppressed.Add(fixKey code cf.Path f) |> ignore

                                        { cf with Fixes = orphans }
                            ]

                        if not orphanFiles.IsEmpty then
                            checker.InvalidateConfiguration options

                        [
                            for cf, culprits in split do
                                if not culprits.IsEmpty then
                                    { cf with Fixes = culprits }
                        ]
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
                            [
                                for cf in changedFiles |> List.except named do
                                    let orphans = cf.Fixes |> List.filter (fun (g, _, _) -> rolledGroups.Contains g)

                                    if not orphans.IsEmpty then
                                        writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except orphans))

                                        for _, code, f in orphans do
                                            suppressed.Add(fixKey code cf.Path f) |> ignore

                                        { cf with Fixes = orphans }
                            ]

                        if not orphanFiles.IsEmpty then
                            checker.InvalidateConfiguration options

                        named @ orphanFiles
                else
                    // The named files are back and the errors stay: the
                    // culprit sits in a file the errors never named. FR0130
                    // put [<Literal>] on `let lat` in FsToolkit's
                    // TestData.fs and the errors landed on `let! lat` in
                    // Result.fs — and the old answer here, every fix of the
                    // pass rolled back and suppressed, cost that project 152
                    // innocent fixes; the next pass re-applied nothing. So
                    // find the file(s) whose fixes carry the blame by
                    // bisecting the rest — a project check per step, bounded
                    // — keep the others, and give the named files' own fixes
                    // one more chance beside them.
                    let rest = changedFiles |> List.except named
                    let mutable checks = 0
                    let maxChecks = 8

                    // the project check alone: the per-file second look of
                    // recount () is for the FS0034 signature case, and is
                    // paid once, on the final answer, not per bisection step
                    let failsQuick () =
                        checker.InvalidateConfiguration options
                        (projectErrors checker options).Length > baselineErrors

                    // the tree with `named` put back and exactly `applied`
                    // of the rest re-applied
                    let failsApplying (applied: AppliedFile list) =
                        checks <- checks + 1

                        for cf in rest do
                            if applied |> List.exists (fun a -> a.Path = cf.Path) then
                                writeSource cf.Path (appliedTextOf cf)
                            else
                                writeSource cf.Path cf.Before

                        failsQuick ()

                    // with `context` and `suspects` all applied the check
                    // fails; find the suspects that matter
                    let rec culprits (context: AppliedFile list) (suspects: AppliedFile list) =
                        if suspects.Length <= 1 || checks >= maxChecks then
                            suspects
                        else
                            let h1, h2 = List.splitAt (suspects.Length / 2) suspects

                            if failsApplying (context @ h1) then culprits context h1
                            elif failsApplying (context @ h2) then culprits context h2
                            else culprits (context @ h2) h1 @ culprits (context @ h1) h2

                    // a rolled-back suggestion can have members in kept
                    // files (a cross-file edit set under --api-changes):
                    // those go too, or the suggestion is left half-applied
                    let stripOrphans (rolled: AppliedFile list) (kept: AppliedFile list) =
                        let rolledGroups =
                            rolled
                            |> List.collect (fun cf -> cf.Fixes |> List.map (fun (g, _, _) -> g))
                            |> Set.ofList

                        [
                            for cf in kept do
                                let orphans = cf.Fixes |> List.filter (fun (g, _, _) -> rolledGroups.Contains g)

                                if not orphans.IsEmpty then
                                    writeSource cf.Path (reapplySubset cf.Before (cf.Fixes |> List.except orphans))

                                    for _, code, f in orphans do
                                        suppressed.Add(fixKey code cf.Path f) |> ignore

                                    { cf with Fixes = orphans }
                        ]

                    // everything back: the pass started clean, so this must
                    // check clean — unless the errors were never ours
                    writeBack rest

                    if failsQuick () && (recount ()).Length > baselineErrors then
                        // the same verdict the unnamed branch gives: a
                        // breakage that survives the un-apply is not this
                        // pass's, and its fixes go back in
                        for cf in changedFiles do
                            writeSource cf.Path (appliedTextOf cf)

                        checker.InvalidateConfiguration options

                        eprintfn
                            "  (the new errors persist without this pass's fixes — pre-existing breakage elsewhere, fixes kept)"

                        []
                    else
                        let blamed = if rest.IsEmpty then [] else culprits [] rest
                        let innocent = rest |> List.except blamed

                        // the innocent files re-applied without the blamed
                        // ones — clean, or the bisection ran out of budget
                        // and its answer is not to be trusted
                        let innocentClean = innocent.IsEmpty || not (failsApplying innocent)

                        if not innocentClean then
                            restore rest
                            suppressAll named
                            changedFiles
                        else
                            // the named files' own fixes were only ever
                            // guilty by location: back in beside the
                            // innocent ones, do they check clean too?
                            for cf in named do
                                writeSource cf.Path (appliedTextOf cf)

                            let namedClean = not (failsQuick ()) && (recount ()).Length <= baselineErrors

                            if not namedClean then
                                writeBack named

                            let rolled = if namedClean then blamed else blamed @ named
                            let kept = changedFiles |> List.except rolled

                            suppressAll rolled
                            let orphanFiles = stripOrphans rolled kept

                            if not orphanFiles.IsEmpty then
                                checker.InvalidateConfiguration options

                            let keptFixes =
                                (kept |> List.sumBy (fun cf -> cf.Fixes.Length))
                                - (orphanFiles |> List.sumBy (fun cf -> cf.Fixes.Length))

                            let verdict =
                                if namedClean then
                                    $"the errors in {named.Length} file(s) were caused by the fixes in {blamed.Length} other file(s)"
                                else
                                    $"the fixes in {blamed.Length} file(s) the errors never named are to blame, and the {named.Length} named file(s) do not check clean without them either"

                            printfn
                                $"  ({keptFixes} fix(es) in {kept.Length} file(s) kept — {verdict}; found by bisection in {checks} check(s))"

                            rolled @ orphanFiles
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

/// Verify one pass's edits against the project check, rolling back what
/// broke it (verifyPassChecked) — and when the check itself is given up
/// on (checkWithin's TimeoutException), roll back ALL of them first. The
/// pass has written its files by now; the exception used to pass straight
/// through to the per-target handler, which printed "skipped" and moved on
/// with every unverified edit left on disk. The texts each file had before
/// the pass are in hand, so they go back, and the exception goes on: the
/// target is still skipped, on a tree the run has not altered.
let internal verifyPass
    (checker: FSharpChecker)
    (options: FSharpProjectOptions)
    (baselineErrors: int)
    (suppressed: System.Collections.Generic.HashSet<string * string * string * string>)
    (changedFiles: AppliedFile list)
    : bool =
    try
        verifyPassChecked checker options baselineErrors suppressed changedFiles
    with :? TimeoutException ->
        for cf in changedFiles do
            writeSource cf.Path cf.Before

        checker.InvalidateConfiguration options

        eprintfn
            $"  (the typecheck verifying this pass was given up on, so its {changedFiles.Length} changed file(s) were put back unverified)"

        reraise ()

/// One checker per framework of a multi-targeted project, beyond the
/// run's own for the first.
///
/// FCS keeps ONE incremental builder per project file name: setting a
/// builder for options that name the same fsproj evicts the other
/// ("similar" keys, in its MRU cache), and every framework's options name
/// the same fsproj. So on one checker the frameworks threw each other's
/// typecheck away at every switch — measured: the second framework's
/// check, done in parallel and cached, cost its full 25 s again — and a
/// check run ahead could never be found. A separate checker per framework
/// index keeps each builder alive; the checkers are kept for the run, so
/// the next multi-targeted project finds its reference assemblies parsed.
/// Memory is the price (a checker's caches, a few hundred MB), paid once
/// per extra framework.
let private frameworkCheckers = ResizeArray<FSharpChecker>()

/// The checker for the framework at `index` in the project's list; 0 is
/// the run's own, passed in.
let private checkerForFramework (runChecker: FSharpChecker) (index: int) =
    if index = 0 then
        runChecker
    else
        lock frameworkCheckers (fun () ->
            while frameworkCheckers.Count < index do
                frameworkCheckers.Add(FSharpChecker.Create(keepAssemblyContents = false))

            frameworkCheckers.[index - 1])

/// The frameworks the current project's loop takes in turn, set by
/// executeRun: a project swept on its narrowest framework alone has
/// nothing to read ahead for.
let mutable private frameworksInTurn: string list = []

/// May this compilation be typechecked in the background, beside another?
///
/// Two things make a check depend on the process rather than its own
/// options. A TYPE PROVIDER: its design-time assembly is loaded once per
/// process by simple name, and instantiating it from two checkers at once
/// — the netstandard2.1 flavour racing the netstandard2.0 one — left
/// welendus's SqlDataProvider throwing "unexpected exception from provided
/// type" into 652 errors, on a project that checks clean alone. A
/// STRONG-NAME KEY named in source: FCS opens `AssemblyKeyFile("../k.snk")`
/// relative to the process directory, which checkProject sets for the
/// duration of a check, and a background check cannot have its own. Either
/// one, and the framework's check waits its turn.
let private checksAheadSafely (options: FSharpProjectOptions) =
    let providerAssembly (o: string) =
        o.StartsWith("-r:", StringComparison.OrdinalIgnoreCase)
        && (let name = Path.GetFileNameWithoutExtension(o.Substring 3)

            name.Contains("TypeProvider", StringComparison.OrdinalIgnoreCase)
            || name.Contains("SQLProvider", StringComparison.OrdinalIgnoreCase)
            || name.Contains("SwaggerProvider", StringComparison.OrdinalIgnoreCase)
            || name.StartsWith("FSharp.Data", StringComparison.OrdinalIgnoreCase)
            || name.Equals("FSharp.Configuration", StringComparison.OrdinalIgnoreCase))

    let sourceMentions =
        options.SourceFiles
        |> Array.exists (fun f ->
            try
                let text = File.ReadAllText f
                text.Contains "Provider<" || text.Contains "AssemblyKeyFile"
            with _ -> // unreadable: assume the worst, the check waits; fsharpanalyzer: ignore-line FR0055
                true)

    not (options.OtherOptions |> Array.exists providerAssembly)
    && not sourceMentions

/// Read the NEXT framework's compiler arguments now and start its
/// typecheck on its own checker, so that both are done by the time its
/// turn comes (see speculativeCheck). Called once this framework's own
/// arguments are in hand: MSBuild runs are kept one at a time — two
/// builds of one project race on its obj directory — and this
/// framework's build was the outer one that compiled every framework, so
/// the next one's is incremental. The check is fire-and-forget: its
/// result lives in FCS's own cache, where the framework's timed check
/// finds it, and a failure or a hang is that check's to report.
let private prefetchNextFramework (runChecker: FSharpChecker) (opts: Options) (target: Target) =
    match target with
    | Target.Project(project, _) when opts.Framework <> "" && not opts.ParseOnly ->
        let frameworks = frameworksInTurn

        let next =
            frameworks
            |> List.tryFindIndex (fun tfm -> tfm = opts.Framework)
            |> Option.bind (fun i -> List.tryItem (i + 1) frameworks |> Option.map (fun tfm -> i + 1, tfm))

        match next with
        | Some(index, tfm) ->
            Out.dim $"  ({tfm}: compiler arguments and typecheck run ahead, alongside this pass)"
            let checker = checkerForFramework runChecker index
            let ahead = optionsFor checker false tfm target
            prefetchedOptions.[(Path.GetFullPath project, tfm)] <- ahead

            match ahead with
            | Ok options when checksAheadSafely options ->
                speculativeCheck.Value <-
                    System.Threading.Tasks.Task.Run(fun () ->
                        try
                            checker.ParseAndCheckProject options |> Async.RunSynchronously |> ignore
                        with _ -> // reported by the framework's own check; fsharpanalyzer: ignore-line FR0055
                            ())
            | Ok _ ->
                Out.dim $"  ({tfm}: its typecheck waits its turn — a type provider or a strong-name key is involved)"
            | Error _ -> ()
        | None -> ()
    | _ -> ()

/// After a multi-targeted project's last framework: the pool checkers'
/// builders hold that project's typed trees, which nothing will ask for
/// again; let them go before the next project's arrive.
let private releaseFrameworkCheckers () =
    lock frameworkCheckers (fun () ->
        for c in frameworkCheckers do
            try
                c.ClearLanguageServiceRootCachesAndCollectAndFinalizeAllTransients()
            with _ -> // fsharpanalyzer: ignore-line FR0055
                ())

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
    let frameworkLabel =
        match opts.Framework, analysisConfiguration with
        | "", None -> ""
        | tfm, None -> $" [{tfm}]"
        | "", Some cfg -> $" [{cfg}]"
        | tfm, Some cfg -> $" [{tfm} {cfg}]"

    let label =
        match target with
        | Target.Project(p, Some file) -> $"{Path.GetFileName file} (in {Path.GetFileName p})"
        | Target.Project(p, None) -> Path.GetFileName p
        | Target.Script s -> Path.GetFileName s

    if showHeader then
        printfn $"== {label}{frameworkLabel} =="

    /// exit 1 for this compilation, with the reason the end of the run
    /// will repeat beside the exit code
    let failed (why: string) =
        lock exitReasons (fun () -> exitReasons.Add $"{label}{frameworkLabel}: {why}")
        1

    // a build failing on a file an earlier compilation of this run rewrote
    // is the run's own doing: put those files back and load once more
    let loaded =
        match optionsFor checker opts.ParseOnly opts.Framework target with
        | Error message when message.Contains "dotnet build failed" && not opts.DryRun ->
            match putBackRunEdits message label with
            | [] -> Error message
            | putBack ->
                match optionsFor checker opts.ParseOnly opts.Framework target with
                | Ok options -> Ok options
                | Error second ->
                    // still broken without them: the failure was never
                    // the earlier fixes', and they go back in
                    for file, text in putBack do
                        writeSource file text

                    eprintfn $"  ({label} does not build without them either; the earlier fixes are back in place)"

                    Error second
        | first -> first

    match loaded with
    | Error message ->
        eprintfn $"{message}"

        // NOT-APPLICABLE targets are not failures: a dacpac project or a
        // wildcard-item fsproj beyond --parse-only was skipped, not broken
        // (a solution containing one used to fail the whole run's exit)
        if message.Contains "— skipped" || message.Contains "beyond --parse-only" then
            0
        else if message.Contains "dotnet build failed" then
            System.Threading.Interlocked.Increment(&runBuildFailures) |> ignore
            failed "does not build, so it was not analysed"
        else
            failed "could not be loaded (no compiler arguments), so it was not analysed"
    | Ok options ->
        prefetchNextFramework checker opts target

        let analyzers =
            cliAnalyzers ()
            |> List.filter (fun m -> not opts.ParseOnly || parseOnlySafeAnalyzers.Contains(analyzerName m))

        printfn $"{analyzers.Length} analyzers, {options.SourceFiles.Length} files"

        if analysisConfiguration.IsSome then
            let defines =
                options.OtherOptions
                |> Array.filter (fun o -> o.StartsWith "--define:")
                |> String.concat " "

            Out.dim $"  (defines: {defines})"

        // a test project exports no API: nothing links to its declarations,
        // so the cross-file reshapes --api-changes gates (FR0090, FR0091,
        // FR0069, FR0093, FR0049) are as safe there as in a private module
        // and run without the flag. Known by the test framework it
        // references; a `dotnet test` project always does
        let testProject =
            match target with
            | Target.Project _ ->
                options.OtherOptions
                |> Array.exists (fun o ->
                    o.StartsWith("-r:", StringComparison.OrdinalIgnoreCase)
                    && (let name = Path.GetFileName(o.Substring 3).ToLowerInvariant()

                        name.StartsWith "xunit."
                        || name = "nunit.framework.dll"
                        || name = "microsoft.visualstudio.testplatform.testframework.dll"
                        || name = "expecto.dll"))
            | Target.Script _ -> false

        let opts =
            if testProject && not opts.ApiChanges then
                Out.dim
                    "  (a test project: its declarations have no callers outside it, so the --api-changes reshapes apply)"

                { opts with ApiChanges = true }
            else
                opts

        // the C# and VB projects referencing this one: no F# check sees
        // what they link to, so they are built with the verification — or,
        // where they cannot be built, the public surface is held for them.
        // The probe build that decides "buildable" is paid only where a
        // public shape can change at all, under --api-changes (a test
        // project's own included): a run that keeps the public surface
        // cannot break a consumer's compile, and its consumers are built
        // with the verification without a probe. Nothing to hold or build
        // on a parse-only run, which writes nothing
        let buildableConsumers, heldConsumers =
            match target with
            | Target.Project(project, _) when not opts.ParseOnly ->
                consumersOf (not opts.DryRun && opts.ApiChanges) opts.Target project
            | _ -> [], []

        // cross-file (API-changing) rule variants gate on this: they
        // stay silent in editors and in default runs. Set per compilation
        // either way: a test project turns it on for itself alone, and the
        // library compiled after it must find it off again
        // only codes the user TYPED outrank a rule's default-off status and
        // a config disable — asking for FR0099 by name and getting silence
        // would be a lie. A --categories expansion deliberately does NOT
        // qualify: a category is a filter, not an ask, and
        // `--categories idiom` must not quietly turn on FR0002
        Scope.set
            { Scope.scope () with
                ApiChanges = opts.ApiChanges
                ForcedCodes = opts.ExplicitCodes |> Option.defaultValue Set.empty
                PublicSurfaceHeld = not heldConsumers.IsEmpty
            }

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
        // the project's own type providers must be the FIRST loaded into
        // this process. FCS keeps a design-time assembly by name, and a
        // script read against a .NET Framework reference set (readScript's
        // second try) can pull another flavour of the same provider in
        // first: welendus's Program.fsx `#I`s packages/FSharp.Data/lib/net45,
        // and from then on every project's `FSharp.Data.JsonProvider` was
        // "not defined in 'FSharp.Data'" - 52 errors before any fix, four
        // projects skipped, in a tree that builds. The typecheck is cached,
        // so the baseline below pays nothing twice
        if opts.ApiChanges && not opts.ParseOnly then
            match target with
            | Target.Project _ -> projectErrors checker options |> ignore
            | Target.Script _ -> ()

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

            if showHeader && not opts.DryRun && runTotalApplied > 0 then
                // in a multi-compilation run these "pre-existing" errors can
                // be an earlier project's applied fixes breaking a shared
                // source file — that is our doing, not the caller's. Only
                // when an earlier compilation of this run DID write
                // something: on the first project, or after clean ones, the
                // hint pointed at a diff that did not exist (FsCheck's
                // key-file refusal wore it on its very first project). A
                // dry run modifies nothing, so there the errors are simply
                // pre-existing
                eprintfn
                    $"  (multi-project run: an earlier compilation of this run applied {runTotalApplied} fix(es) — those may have introduced these; review the diff)"

            for d in projectErrors checker options |> Array.truncate 5 do
                eprintfn $"  {d.FileName}({d.StartLine},{d.StartColumn}): {d.Message}"

            failed $"has {baselineErrors} error(s) before any fix, so it was not analysed"
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
                    referencingCheckCache.Clear()
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

                    failed
                        $"applying introduced {finalErrors - baselineErrors} error(s) in the end-of-run check; its {restored} changed file(s) were put back"
                // The check above only covers the framework we analysed. A
                // multi-targeted project has others, and a fix valid for one
                // can fail on another, so build the lot before claiming
                // success. A project of another language referencing this
                // one is in the same position — its compile of this
                // project's public surface is one no F# check ran — and is
                // built alongside (consumersOf).
                elif
                    not opts.ParseOnly
                    && (isMultiTargeted target
                        || not buildableConsumers.IsEmpty
                        || (match target with
                            | Target.Project(project, _) -> hasConfigurationConditionals project
                            | Target.Script _ -> false))
                then
                    match target with
                    | Target.Project(project, _) ->
                        let ownBuildNeeded = isMultiTargeted target || hasConfigurationConditionals project

                        let consumerNames =
                            buildableConsumers |> List.map Path.GetFileName |> String.concat ", "

                        /// what the verification covers, for the lines below
                        let verified =
                            match ownBuildNeeded, buildableConsumers.IsEmpty with
                            | true, true -> "every target framework"
                            | true, false -> "every target framework and referencing project"
                            | false, _ -> "every referencing project"

                        /// what a failure names: the framework, or the
                        /// referencing project, this run did not analyse
                        let subject =
                            match ownBuildNeeded, buildableConsumers.IsEmpty with
                            | true, true -> "a target framework"
                            | true, false -> "a target framework or referencing project"
                            | false, _ -> "a referencing project"

                        let subjectCap = string (Char.ToUpperInvariant subject.[0]) + subject.Substring 1

                        if buildableConsumers.IsEmpty then
                            printfn "verifying every target framework and configuration..."
                        elif ownBuildNeeded then
                            printfn
                                $"verifying every target framework and configuration, and the referencing {consumerNames}..."
                        else
                            printfn $"verifying the referencing {consumerNames}..."

                        /// the verification build: this project's every
                        /// framework and configuration, where it has more than
                        /// the one analysed, then each consumer that could be
                        /// built — the first failure is the verdict
                        let verificationBuild () =
                            let own = if ownBuildNeeded then buildAllFrameworks project else Ok()

                            match own with
                            | Error _ -> own
                            | Ok() ->
                                buildableConsumers
                                |> List.fold
                                    (fun result consumer ->
                                        match result with
                                        | Ok() -> buildOnce consumer ""
                                        | refused -> refused)
                                    (Ok())

                        // a verification switch: a failure that needs the
                        // fixes in place to be studied (the F# compiler's
                        // FSharp.Core failing only with the compiler
                        // project's fixes applied) is kept, not undone
                        let keepOnFailure = Environment.GetEnvironmentVariable "FSREF_KEEP_ON_FAILURE" = "1"

                        let tail (lines: string array) =
                            lines |> Array.truncate 5 |> String.concat "\n"

                        /// the build was stopped at the time cap, so it said
                        /// nothing about the code: the fixes are unverified,
                        /// and go back (or stay, under the switch)
                        let notVerified (lines: string array) (putBack: unit -> int) =
                            if keepOnFailure then
                                eprintfn
                                    "FSREF_KEEP_ON_FAILURE: a verification build was stopped at the time cap, so it could not verify this run's fixes; kept for inspection:"

                                eprintfn $"{tail lines}"

                                failed
                                    "FSREF_KEEP_ON_FAILURE: a verification build was stopped at the time cap and could not verify this run's fixes; they were kept for inspection"
                            else
                                let restored = putBack ()

                                eprintfn
                                    $"A verification build was stopped at the time cap before it had compiled this run's fixes, so they are unverified; the {restored} file(s) it changed were put back. FSREF_BUILD_MINUTES raises the cap (now {processTimeout.TotalMinutes:N0})."

                                eprintfn $"{tail lines}"

                                failed
                                    $"a verification build was stopped at the time cap, so this run's fixes could not be verified; its {restored} changed file(s) were put back"

                        match verificationBuild () with
                        | Ok() ->
                            printfn $"done; {verified} still builds"
                            markSwept options
                            0
                        // Not a failed build to be judged, a build that never
                        // judged: with the fixes in place it was stopped at
                        // the time cap, so it compiled nothing this run
                        // wrote. The baseline comparison below cannot help —
                        // a baseline that times out too reads as "no new
                        // error" — and was how a timed-out build kept every
                        // fix as pre-existing breakage. The cap ALONE, though:
                        // a build that fails on its tooling (an `Exec` target,
                        // packing, a missing targeting pack) is judged against
                        // the baseline like any other failure, and a
                        // repository broken that way before this run keeps
                        // its fixes as it always did.
                        | Error output when stoppedAtTimeCap output ->
                            notVerified output (fun () -> restoreSnapshot snapshot)
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

                                failed
                                    $"{subject} fails to build with and without this run's fixes; the fixes were kept, the build needs attention"

                            match verificationBuild () with
                            | Error _ when keepOnFailure ->
                                keepFixes
                                    $"FSREF_KEEP_ON_FAILURE: {subject} fails with this run's fixes (and without them); kept for inspection:"
                            // Still broken without the fixes — but "still
                            // broken" is not "not our fault". Comparing the
                            // errors themselves separates the two: one that
                            // appears only with our changes is ours, and
                            // putting the files back would hand over a
                            // project broken in ways this run caused.
                            | Error withoutFixes ->
                                match judgeAgainstBaseline verificationBuild output withoutFixes with
                                | PreExisting ->
                                    keepFixes
                                        $"{subjectCap} fails to build, but it fails WITHOUT this run's fixes too — pre-existing breakage, fixes kept:"
                                | Unverifiable ->
                                    keepFixes
                                        $"{subjectCap} fails to build, and fails DIFFERENTLY from one build to the next without this run's fixes — this build cannot verify them; fixes kept (each passed the typecheck of the framework analysed), review the diff:"
                                // the baseline build (or the second) was
                                // stopped at the cap and said nothing about
                                // the code; the files are already back, and
                                // stay back
                                | NotVerified -> notVerified withoutFixes (fun () -> restored)
                                | Introduced introduced ->
                                    eprintfn
                                        $"{subjectCap} was ALREADY broken, but applying broke it further ({introduced.Count} error(s) seen only with this run's fixes), so the {restored} file(s) it changed were put back:"

                                    eprintfn $"{report (Array.ofSeq introduced)}"

                                    failed
                                        $"applying broke an already-failing build ({subject}) further ({introduced.Count} new error(s)); its {restored} changed file(s) were put back"
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

                                match verificationBuild () with
                                | Ok() ->
                                    printfn
                                        $"done; {verified} still builds (the first verification build failed and the second passed — a build that only fails sometimes)"

                                    markSwept options
                                    0
                                | Error again when keepOnFailure ->
                                    eprintfn
                                        $"FSREF_KEEP_ON_FAILURE: {subject} fails with this run's fixes and builds without them; the fixes are kept for inspection:"

                                    eprintfn $"{report again}"

                                    failed
                                        $"FSREF_KEEP_ON_FAILURE: {subject} fails to build with this run's fixes; they were kept for inspection"
                                // the baseline built and the rebuild with the
                                // fixes was stopped at the cap: no bisection
                                // over builds that cannot finish — the fixes
                                // are unverified and go back whole
                                | Error again when stoppedAtTimeCap again ->
                                    notVerified again (fun () -> restoreSnapshot snapshot)
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

                                    // every file this run changed, the ones outside
                                    // the project included — counted NOW, before the
                                    // bisection below writes any of them back: a
                                    // restoreSnapshot count taken after it only
                                    // sees the files the last bisection step had
                                    // not already put back ("the 6 file(s) it
                                    // changed were put back" on FsToolkit, where
                                    // all 25 went back)
                                    let changedTotal =
                                        changed.Length
                                        + (currentTexts
                                           |> List.filter (fun (path, text) ->
                                               not (Map.containsKey path snapshot)
                                               && (match extraSnapshot.TryGetValue path with
                                                   | true, original -> original <> text
                                                   | _ -> false))
                                           |> List.length)

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

                                        match verificationBuild () with
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
                                        $"  bisecting the {changed.Length} changed file(s) for the ones the refusing build ({subject}) rejects (a build per step)..."

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
                                            $"Applying broke {subject} this run did not analyze; the fixes in {found.Length} file(s) were put back and the other {changed.Length - found.Length} kept:"

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
                                            [
                                                for kv in extraSnapshot do
                                                    if closure.Contains(canonicalPath kv.Key) then
                                                        kv.Key, kv.Value
                                            ]

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
                                        let allBack =
                                            if alsoOwn.IsEmpty then
                                                false
                                            else
                                                match verificationBuild () with
                                                | Ok() -> false
                                                | Error _ ->
                                                    restoreSnapshot snapshot |> ignore

                                                    eprintfn
                                                        $"With those put back too {subject} still fails, so the {changedTotal} file(s) this run changed were all put back."

                                                    true

                                        if allBack then
                                            failed
                                                $"all {changedTotal} changed file(s) put back: {subject} this run did not analyze fails with its fixes"
                                        else
                                            failed
                                                $"the fixes in {found.Length + alsoOwn.Length} of {changedTotal} changed file(s) put back: {subject} this run did not analyze refused them"
                                    else
                                        restoreSnapshot snapshot |> ignore

                                        eprintfn
                                            $"Applying broke {subject} this run did not analyze, so the {changedTotal} file(s) it changed were put back:"

                                        eprintfn $"{report again}"

                                        failed
                                            $"all {changedTotal} changed file(s) put back: {subject} this run did not analyze fails with its fixes"
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
            [
                for run in doc.RootElement.GetProperty("runs").EnumerateArray() do
                    match run.TryGetProperty "results" with
                    | true, results ->
                        for result in results.EnumerateArray() do
                            match result.TryGetProperty "partialFingerprints" with
                            | true, fps ->
                                match fps.TryGetProperty FingerprintKey with
                                | true, v -> v.GetString()
                                | _ -> ()
                            | _ -> ()
                    | _ -> ()
            ]

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
    [
        for f in findings ->
            dict
                [
                    "code", box f.Code
                    "severity", box (severityName f.Severity)
                    "autoFixable", box f.Fixable
                    "file", box f.File
                    "startLine", box f.StartLine
                    "startColumn", box f.StartColumn
                    "endLine", box f.EndLine
                    "endColumn", box f.EndColumn
                    "message", box f.Message
                    "fingerprint", box f.Fingerprint
                    "snippet", box f.Snippet
                ]
    ]

/// The run's findings as one JSON document (--format json and --mcp).
let private findingsAsJson (findings: ReportedFinding list) (baselined: int) =
    let payload =
        dict
            [
                "findings", box (findingsPayload findings)
                "baselineSuppressed", box baselined
                "commentSuppressed", box commentSuppressed
                "suppressionsOverridden", box suppressionOverridden
            ]

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
                let text = projectTextWithoutComments (File.ReadAllText path)

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

let private fsharpCorePinRegex =
    System.Text.RegularExpressions.Regex(
        @"<PackageReference\s+(?:Include|Update)\s*=\s*""FSharp\.Core""[^>]*Version\s*=\s*""(\d+)\.",
        System.Text.RegularExpressions.RegexOptions.IgnoreCase
    )

/// Every project of the run, with the lowest FSharp.Core major its restore
/// (or, before one, its own `FSharp.Core` pin) resolves, and the files its
/// `<Compile>` items name: a file two projects share holds to the older
/// one's FSharp.Core (elmish's src/program.fs, in Elmish.fsproj on
/// FSharp.Core 10 AND Fable.Elmish.fsproj on 4.7 - the interpolation
/// FR0042 offered for the first broke the second, whose build check the
/// run reached only afterwards). Textual on purpose: compiler arguments
/// arrive one compilation at a time, and the floor must be known before
/// the first. Items with a property or a wildcard are the evaluation's
/// business and are left out; `putBackRunEdits` catches what this misses.
let private registerFileFloors (targets: Target list) =
    CapabilityFix.clearFileFloors ()

    let projects =
        targets
        |> List.choose (fun t ->
            match t with
            | Target.Project(p, _) -> Some(Path.GetFullPath p)
            | Target.Script _ -> None)
        |> List.distinct

    if projects.Length > 1 then
        for project in projects do
            try
                let text = File.ReadAllText project

                let floor =
                    match CapabilityFix.minFSharpCoreMajor project with
                    | ValueSome n -> Some n
                    | ValueNone ->
                        let m = fsharpCorePinRegex.Match text

                        if m.Success then Some(int m.Groups.[1].Value) else None

                match floor with
                | Some major ->
                    let dir = Path.GetDirectoryName project

                    for m in compileItemRegex.Matches text do
                        let item = m.Groups.[1].Value

                        if not (item.Contains '$') && not (item.Contains '*') then
                            CapabilityFix.registerFileFloor (Path.Combine(dir, item.Replace('\\', '/'))) major
                | None -> ()
            with
            | :? IOException
            | :? UnauthorizedAccessException -> ()

/// The whole run for one Options value: resolve targets, sweep, verify,
/// report. The checker comes from the caller so a resident host (--mcp)
/// can keep it — and every reference assembly FCS has parsed — warm
/// between calls.
let private executeRun (initialChecker: FSharpChecker) (opts: Options) : int =
    // replaced after a typecheck that never returned (checkWithin): the
    // abandoned check still holds the old checker's locks and caches, and
    // every later compilation would queue behind it
    let checkerRef = ref initialChecker

    match resolveTargets opts.Target with
    | Error message ->
        eprintfn $"{message}"
        2
    | Ok targets ->
        let targets = orderNarrowestFirst targets
        registerFileFloors targets
        // a resident host runs again on a tree the user has edited since:
        // the originals of THIS run start empty, or a put-back would
        // hand a file its text from the last run
        runOriginals.Clear()

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
        // a resident host may see a project file edited between runs
        compileItemsCache.Clear()
        projectCompilingCache.Clear()
        prefetchedOptions.Clear()
        configurationConditionals.Clear()
        defaultConfigurations.Clear()
        // a sibling's compiler arguments and typecheck are this run's: the
        // corpus harness runs main in-process, and the next run's sources
        // may be another tree's
        siblingOptionsCache.Clear()
        siblingCheckCache.Clear()
        referencingCheckCache.Clear()
        // whether a consumer builds was answered for the last run's tree
        consumerProjects.Clear()
        // the corpus harness runs main in-process; a leaked count would
        // report the previous run's held-back findings as this one's
        Analyzers.heldByScope.Clear()
        directiveFreeCache.Clear()
        runTotalApplied <- 0
        runBuildFailures <- 0
        runAnalyzerFailures <- 0
        lock exitReasons exitReasons.Clear
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
        /// The extra pass a project with `#if DEBUG`-style conditionals
        /// gets: the same rules under the OTHER build configuration, where
        /// the branches the first pass could not see are the parse tree.
        /// The sweep dedup keys a file carrying such a directive by its
        /// defines, so only those files are swept again; the rest are
        /// skipped as already done. A configuration that does not build
        /// here (a dacpac step, an npm task) costs a note, not the run's
        /// exit code: the default configuration's pass stands on its own.
        let otherConfigurationPass (checker: FSharpChecker) (target: Target) =
            match target with
            | Target.Project(project, _) when not opts.ParseOnly && hasConfigurationConditionals project ->
                let other = (defaultConfiguration project).Other

                printfn
                    $"{Path.GetFileName project}: its sources branch on the build configuration — analysing the {other} branches too"

                analysisConfiguration <- Some other

                try
                    let narrowest = frameworksOf target |> List.tryHead |> Option.defaultValue ""

                    let code = runTarget checker { opts with Framework = narrowest } true target

                    if code <> 0 then
                        // reported by runTarget; the exit reason it recorded
                        // names the configuration, and the default pass's
                        // result is what the caller relies on
                        Out.skip $"  ({other} did not complete cleanly; the {other}-only branches keep their code)"

                    0
                finally
                    analysisConfiguration <- None
            | _ -> 0

        let runOneConfiguration (checker: FSharpChecker) target =
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
                            Framework = List.head frameworks
                        }
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

                    frameworksInTurn <- frameworks

                    try
                        frameworks
                        |> List.mapi (fun index tfm ->
                            // no constant to guard with, and this pass sees a
                            // wider surface than the narrowest target: a
                            // capability fix here can only go in plainly and
                            // be reverted by the all-frameworks build, taking
                            // the innocent fixes in those files with it
                            Scope.set
                                { Scope.scope () with
                                    DualTfmConstant =
                                        (match dualConstant with
                                         | Some c when not (isLegacy tfm) -> ValueSome c
                                         | _ -> ValueNone)
                                    GuardUnavailable =
                                        dualConstant.IsNone && not (isLegacy tfm) && not legacyTfms.IsEmpty
                                }

                            runTarget (checkerForFramework checker index) { opts with Framework = tfm } true target)
                        |> List.fold max 0
                    finally
                        // both are this project's rounds' business only: a
                        // leaked no-guard flag once dropped the capability fixes
                        // of every later target in the run, single-target net8.0
                        // projects included. In a `finally`, because a
                        // typecheck given up on (checkWithin) leaves this loop
                        // by exception: the next target's Scope.set carries
                        // both flags over, and that is the same regression
                        // through a different door.
                        Scope.set
                            { Scope.scope () with
                                DualTfmConstant = ValueNone
                                GuardUnavailable = false
                            }

                        frameworksInTurn <- []
                        releaseFrameworkCheckers ()
            | _ -> runTarget checker opts several target

        let runOne target =
            let checker = checkerRef.Value
            let code = runOneConfiguration checker target
            max code (otherConfigurationPass checker target)

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
                    // a typecheck that never returns (see checkWithin) costs
                    // this target, not the run: the rest still get their turn
                    let code =
                        try
                            runOne target
                        with :? TimeoutException as t ->
                            eprintfn $"  ({t.Message}; this compilation was skipped)"
                            checkerRef.Value <- FSharpChecker.Create(keepAssemblyContents = false)
                            1

                    if targets.Length > 1 then
                        writeReportNow ()

                    // FSREF_MEMORY=1: the process's working set and the managed
                    // heap after each compilation, to tell a per-project plateau
                    // from growth across the run
                    if Environment.GetEnvironmentVariable "FSREF_MEMORY" = "1" then
                        let working = Diagnostics.Process.GetCurrentProcess().WorkingSet64 / 1048576L
                        let heap = GC.GetTotalMemory false / 1048576L

                        eprintfn
                            $"  (memory after {(match target with
                                                | Target.Project(p, _) -> Path.GetFileName p
                                                | Target.Script s -> Path.GetFileName s)}: working set {working} MB, managed heap {heap} MB)"

                    code)
                |> List.fold max 0

            // a rule that threw was skipped for that file, and the file's
            // tally is short by whatever it would have found: not a clean
            // run, whatever the counts below say
            let exitCode = if runAnalyzerFailures > 0 then max exitCode 1 else exitCode

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

            if runAnalyzerFailures > 0 then
                Out.bad
                    $"  WARNING: {runAnalyzerFailures} rule invocation(s) threw and were skipped (the `(analyzer ... failed on ...)` lines above name them) — those files were not fully analysed, and a fix of the failing rule was neither offered nor applied there. Please report the exception."

            // the last line before a non-zero exit says which compilations
            // caused it and why — the paragraphs that did are pages up
            let reasons = lock exitReasons (fun () -> List.ofSeq exitReasons)

            if exitCode <> 0 && not reasons.IsEmpty then
                Out.bad $"""exit {exitCode}: {reasons.Length} compilation(s) — {String.concat "; " reasons}"""

            if exitCode = 0 && opts.FailOnFindings && reportedFindings.Count > 0 then
                3
            else
                exitCode
        finally
            // runTarget sets the scope for the rule variants; the corpus
            // harness runs main IN-PROCESS, so a leaked scope would make
            // later analyzer calls in the same process api-changes- or
            // forced-code-scoped
            Scope.reset ()

/// --rules: the catalog, human table by default, JSON on request.
let private printRules (json: bool) =
    if json then
        let payload =
            [
                for code, category, enabledByDefault in rulesAsRows () ->
                    dict
                        [
                            "code", box code
                            "category", box category
                            "enabledByDefault", box enabledByDefault
                        ]
            ]

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

    let checker = FSharpChecker.Create(keepAssemblyContents = false)

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
                [
                    "tools",
                    box
                        [
                            dict
                                [
                                    "name", box "analyze"
                                    "description",
                                    box
                                        "Analyze an F# project, script or directory with fsharp-refactor. Dry-run by default: reports findings without editing. Set apply=true to write the fixes (build-verified). Returns findings as JSON with stable fingerprints and source snippets."
                                    "inputSchema",
                                    box (
                                        dict
                                            [
                                                "type", box "object"
                                                "properties",
                                                box (
                                                    dict
                                                        [
                                                            "target",
                                                            box (
                                                                dict
                                                                    [
                                                                        "type", box "string"
                                                                        "description",
                                                                        box
                                                                            "fsproj, fsx, sln, directory or glob to analyze"
                                                                    ]
                                                            )
                                                            "codes",
                                                            box (
                                                                dict
                                                                    [
                                                                        "type", box "string"
                                                                        "description",
                                                                        box "comma-separated rule codes to restrict to"
                                                                    ]
                                                            )
                                                            "categories",
                                                            box (
                                                                dict
                                                                    [
                                                                        "type", box "string"
                                                                        "description",
                                                                        box
                                                                            "comma-separated: correctness,performance,idiom,cosmetic"
                                                                    ]
                                                            )
                                                            "parseOnly",
                                                            box (
                                                                dict
                                                                    [
                                                                        "type", box "boolean"
                                                                        "description",
                                                                        box "no MSBuild, syntactic rules only"
                                                                    ]
                                                            )
                                                            "apply",
                                                            box (
                                                                dict
                                                                    [
                                                                        "type", box "boolean"
                                                                        "description",
                                                                        box "write the fixes (default: dry-run)"
                                                                    ]
                                                            )
                                                        ]
                                                )
                                                "required", box [ "target" ]
                                            ]
                                    )
                                ]
                            dict
                                [
                                    "name", box "list_rules"
                                    "description", box "The rule catalog: code, category, enabled-by-default."
                                    "inputSchema", box (dict [ "type", box "object"; "properties", box (dict []) ])
                                ]
                        ]
                ]
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
                        Categories = categories
                    }
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
                        [
                            "exitCode", box exitCode
                            "applied", box (not opts.DryRun)
                            "findingCount", box findings.Length
                            "findings", box (findingsPayload findings)
                            "baselineSuppressed", box baselineSuppressed
                            "commentSuppressed", box commentSuppressed
                            "suppressionsOverridden", box suppressionOverridden
                        ]

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
                        [
                            for code, category, enabledByDefault in rulesAsRows () ->
                                dict
                                    [
                                        "code", box code
                                        "category", box category
                                        "enabledByDefault", box enabledByDefault
                                    ]
                        ]

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
            let checker = FSharpChecker.Create(keepAssemblyContents = false)
            let code = executeRun checker opts

            if opts.Json then
                Console.SetOut realOut
                let findings = lock reportedFindings (fun () -> List.ofSeq reportedFindings)
                printfn $"{findingsAsJson findings baselineSuppressed}"

            code
