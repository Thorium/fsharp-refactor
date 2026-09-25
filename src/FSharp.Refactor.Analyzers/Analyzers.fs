/// FSharp.Analyzers.SDK entry points. Each refactoring is exposed twice:
/// once for editors (FsAutoComplete/Ionide) and once for the CLI
/// (fsharp-analyzers tool, usable in CI). The logic itself lives in the
/// per-refactoring modules; this file only builds the diagnostic messages
/// and applies the optional per-repository configuration
/// (fsharprefactor.json), which can disable rules by code or name.
module FSharp.Refactor.Analyzers

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Compiler.Symbols
open System

[<Literal>]
let private HelpBase =
    "https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md"

let private fix (range: range) (original: string) (replacement: string) : Fix =
    {
        FromRange = range
        FromText = original
        ToText = replacement
    }

/// Every rule's message ends with its kind, so the one place a reader meets a
/// suggestion — an editor hover, a SARIF entry, a CI log — says whether it is
/// a defect or a matter of punctuation, without looking the code up. It is a
/// suffix rather than a prefix because editors truncate from the right, and
/// the sentence matters more than the label.
let private hint (code: string) (message: string) (range: range) (fixes: Fix list) : Message =
    {
        Type = "FSharp.Refactor"
        Message = $"{message} [{RuleCatalog.name (RuleCatalog.categoryOf code)}]"
        Code = code
        Severity =
            (if RuleCatalog.isPriority code then
                 Severity.Warning
             else
                 Severity.Hint)
        Range = range
        Fixes = fixes
    }

/// Run a typed rule only when check results are available.
let private whenChecked (ctx: EditorContext) (produce: FSharpCheckFileResults -> Message list) : Message list =
    ctx.CheckFileResults |> Option.map produce |> Option.defaultValue []

/// The rules walk syntax recursively, and a walker's depth follows the
/// shape of the code it reads: a statement chain nests one `Sequential`
/// per statement, `a + b + c + ...` one application per operand, so a
/// long generated file can be thousands deep. The hosts run analyzers on
/// ordinary 1 MB threads, and a StackOverflowException cannot be caught —
/// it ends the process, FsAutoComplete under an editor or the apply tool
/// mid-sweep. So every rule runs on one of a few workers with a 64 MB
/// stack (reserved, not committed: the cost is address space). A pool
/// rather than a thread per call: a sweep calls the rules a few hundred
/// thousand times.
module private DeepStack =
    open System.Threading
    open System.Collections.Concurrent

    let private stackBytes = 64 * 1024 * 1024
    let private onWorker = new ThreadLocal<bool>(fun () -> false)
    let private queue = new BlockingCollection<unit -> unit>()

    let private workers =
        lazy
            (for i in 1 .. max 2 Environment.ProcessorCount do
                let t =
                    Thread(
                        (fun () ->
                            onWorker.Value <- true

                            for work in queue.GetConsumingEnumerable() do
                                work ()),
                        stackBytes
                    )

                t.IsBackground <- true
                t.Name <- $"fsharp-refactor deep stack {i}"
                t.Start())

    /// Run `work` on a deep-stack worker and hand back its result — or,
    /// already on one, run it right here (a rule calling a rule).
    let run (work: unit -> 'T) : 'T =
        if onWorker.Value then
            work ()
        else
            workers.Force()
            let done' = new ManualResetEventSlim(false)
            let mutable result = Unchecked.defaultof<'T>
            let mutable failure: System.Runtime.ExceptionServices.ExceptionDispatchInfo = null

            queue.Add(fun () ->
                try
                    try
                        result <- work ()
                    with e ->
                        failure <- System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture e
                finally
                    done'.Set())

            done'.Wait()
            done'.Dispose()

            if isNull failure then
                result
            else
                failure.Throw()
                result

/// Run a rule's message builder only when the configuration enables the rule
/// for the analyzed file. A disabled rule skips all analysis work.
let private whenEnabled (fileName: string) (code: string) (name: string) (produce: unit -> Message list) =
    async {
        return
            if Configuration.isRuleEnabled fileName code name then
                DeepStack.run produce
            else
                []
    }

/// The same gate for an analyzer that emits MORE THAN ONE code. It runs
/// when any of them is enabled, and each code's own builder asks its own
/// switch — so `"FR0017": false` does not take FR0149 down with it, and
/// `--codes FR0149` alone brings FR0149 back.
let private whenAnyEnabled (fileName: string) (codes: string list) (name: string) (produce: unit -> Message list) =
    async {
        return
            if
                codes
                |> List.exists (fun code -> Configuration.isRuleEnabled fileName code name)
            then
                DeepStack.run produce
            else
                []
    }

/// The scope gate for the rules whose fix changes a declaration's
/// compiled SHAPE in place — `[<Struct>]`, `[<Literal>]`, named union
/// fields, a field's Option becoming ValueOption.
///
/// Two quite different things can open it, and they are worth keeping
/// apart. `--api-changes` (or `"apiChanges": true`) is the caller saying
/// they own the callers of everything, cross-file rewrites included.
/// `"publicApi": false` is the narrower and much commoner statement: this
/// assembly is a leaf — an application, an internal tool — so a
/// declaration that is public merely because F# has no other default is
/// not an API, and reshaping it in one file changes nothing anyone can
/// see. The second never licenses an edit to another file; that is the
/// first's job alone.
///
/// With no config saying either way, the COMPILATION answers: an
/// executable has no external linker, so its public surface is not an API
/// and the gate opens by itself. A project that disagrees — an
/// application that serializes its own public types, or loads plugins by
/// reflection — writes `"publicApi": true` and gets the closed gate back.
/// Whether a compilation is a leaf depends on its source list and its
/// compiler arguments, both of which run to hundreds of entries — and the
/// gate is consulted once per scope-gated rule per file. So the answer is
/// held per compilation. Keyed by project file, which is what identifies
/// one: a multi-targeted project varies its defines and references per
/// framework, never its OutputType or whether it is a script.
let private leafCompilations =
    System.Collections.Concurrent.ConcurrentDictionary<string, bool>(StringComparer.OrdinalIgnoreCase)

/// The gate for a rule whose proof READS every caller: `--api-changes`
/// cannot open it, because a sibling project's call sites are not in this
/// compilation's symbol tables - a public function with no caller in sight
/// is one whose callers sit in the test project, not one with none. Only
/// a leaf compilation (or an explicit `publicApi: false`) says its public
/// declarations have no callers elsewhere.
let private leafScopeOpen (fileName: string) (options: AnalyzerProjectOptions) =
    // a consumer the apply tool found and cannot build (a C# test project
    // of an executable) disproves "nothing links to it", whatever the
    // config or the leaf heuristic say
    not (Visibility.publicSurfaceHeld ())
    && (match Configuration.publicSurfaceSetting fileName with
        | Some declared -> declared
        | None ->
            let leaf =
                leafCompilations.GetOrAdd(
                    options.ProjectFileName,
                    fun _ -> Visibility.compilationIsLeaf options.SourceFiles options.OtherOptions
                )

            Visibility.isApplication fileName leaf)

let private shapeScopeOpen (fileName: string) (options: AnalyzerProjectOptions) =
    // a consumer the apply tool found and cannot build closes the gate
    // over every other answer: "nothing outside links to it" is exactly
    // what that consumer disproves, config and leaf heuristic included
    not (Visibility.publicSurfaceHeld ())
    && (Visibility.apiChangesAllowed ()
        || match Configuration.publicSurfaceSetting fileName with
           | Some declared -> declared
           | None ->
               let leaf =
                   leafCompilations.GetOrAdd(
                       options.ProjectFileName,
                       fun _ -> Visibility.compilationIsLeaf options.SourceFiles options.OtherOptions
                   )

               Visibility.isApplication fileName leaf)

/// The extra question for the two gated rules whose in-place rewrite
/// changes a BINDING'S TYPE rather than a type's representation —
/// FR0035's `|> Set.ofList` on a module value, FR0011's
/// `[<return: Struct>]` on an active pattern.
///
/// "Nothing outside the assembly can see it" is what opens the gate for an
/// executable, and it is true — but a LATER FILE of the same executable
/// can, and consumes the binding at its old type: `Data.names` read as a
/// list in Program.fs, `List.choose (|Int|_|)` wanting an option. Both
/// rules check their own file's uses; this answers for the rest of the
/// compilation, by name. Only when the gate stands open on the leaf
/// heuristic ALONE: `--api-changes` and an explicit `publicApi` /
/// `apiChanges` are the caller vouching for the callers, cross-file
/// included, and a closed gate never asks. Textual and over-eager, like
/// `Text.signatureMentions` and for the same reason: it has to hold in
/// the editor, which installs no cross-file parser and reads the sibling
/// from disk instead. A sibling that cannot be read counts as a use.
let private seenByLaterFile (fileName: string) (options: AnalyzerProjectOptions) : string -> bool =
    if
        Visibility.apiChangesAllowed ()
        || (Configuration.publicSurfaceSetting fileName).IsSome
        || not (shapeScopeOpen fileName options)
    then
        fun _ -> false
    else
        match Visibility.laterSourceFiles fileName options.SourceFiles with
        | [] -> fun _ -> false
        | later ->
            // read once per analysis of this file, and only once a
            // candidate binding asks
            let texts =
                lazy
                    (later
                     |> List.map (fun path ->
                         if ProjectSources.available () then
                             ProjectSources.tryParse path
                             |> Option.map (fun (_, source) -> source.GetSubTextString(0, source.Length))
                         else
                             try
                                 Some(System.IO.File.ReadAllText path)
                             with _ -> // an unreadable sibling counts as a use; fsharpanalyzer: ignore-line FR0055
                                 None))

            fun name ->
                texts.Value
                |> List.exists (fun text ->
                    match text with
                    | Some text -> Text.mentionsIdentifier text name
                    | None -> true)

/// What one sibling of the compilation says about a name, read once per
/// analysis of a file (see patternBoundInSibling).
type private SiblingPatterns =
    /// The host parses siblings: the exact set of bare pattern binders.
    | SiblingParsed of Set<string>
    /// No cross-file parser (an editor): the text, for a mention scan.
    | SiblingText of string
    /// Cannot be read: counts as binding every name (fail closed).
    | SiblingUnreadable

/// FR0130's cross-file question: does any OTHER source file of this
/// compilation — before or after this one — bind `name` as a bare
/// pattern? A lowercase literal shadowed by a pattern is FS3190, an
/// error: `let lat = 13.067439` in FsToolkit's TestData.fs took the
/// attribute, and `let! lat = validLatR` in Result.fs of the same test
/// project stopped compiling — the fix survived in a sibling project only
/// because that one happened not to bind `lat`. The in-file veto in
/// LiteralConst.find is this same check for the file itself.
///
/// Under the CLI's cross-file parser the answer is exact, from each
/// sibling's parse tree, for any name (an UPPERCASE pattern binder in
/// another file would silently start matching the constant, the in-file
/// veto's reason). An editor installs no parser and reads the sibling's
/// text instead: a whole-identifier mention is the conservative superset
/// of a pattern binding, asked for lowercase names only — an uppercase
/// name's mentions are overwhelmingly uses, and uppercase binders in
/// patterns are the shape FS0049 already warns about. A sibling that
/// cannot be read counts as binding the name.
let patternBoundInSibling (fileName: string) (options: AnalyzerProjectOptions) : string -> bool =
    let full (p: string) =
        try
            System.IO.Path.GetFullPath p
        with _ -> // fsharpanalyzer: ignore-line FR0055
            p

    let analyzed = full fileName

    let siblings =
        options.SourceFiles
        |> Seq.filter (fun p ->
            not (String.Equals(full p, analyzed, StringComparison.OrdinalIgnoreCase))
            // a signature file declares, it never binds a pattern
            && not (p.EndsWith(".fsi", StringComparison.OrdinalIgnoreCase)))
        |> List.ofSeq

    match siblings with
    | [] -> fun _ -> false
    | _ ->
        // read once per analysis of this file, and only once a candidate
        // binding asks
        let patterns =
            lazy
                (siblings
                 |> List.map (fun path ->
                     if ProjectSources.available () then
                         match ProjectSources.tryParse path with
                         | Some(tree, _) -> SiblingParsed(LiteralConst.patternBoundNames tree)
                         | None -> SiblingUnreadable
                     else
                         try
                             SiblingText(System.IO.File.ReadAllText path)
                         with _ -> // an unreadable sibling counts as a binder; fsharpanalyzer: ignore-line FR0055
                             SiblingUnreadable))

        // without a parser, a sibling's text only vetoes on a BINDER-shaped
        // mention — `let! lat`, `| lat ->`, `fun lat ->`, `for lat in`,
        // `(lat, lng)`, `as lat` — not on a plain read, or every public
        // lowercase constant another file uses would go dark in editors
        let bindsAsPattern (text: string) (name: string) =
            let n = Text.identifierPattern name

            // anywhere in a let's pattern (`let! lat`, `let (a, lat)`, a
            // parameter), a lambda's, a for's, a match clause's (`| Ok lat
            // ->`, a guard read counts too — the safe side) or an `as`
            [
                $@"\b(let|use)!?\s+[^=\n]*{n}[^=\n]*="
                $@"\bfun\b[^\n>]*{n}"
                $@"\bfor\b[^\n]*{n}[^\n]*\b(in|to|downto)\b"
                $@"\|[^\n]*{n}[^\n]*->"
                $@"\bas\s+{n}"
            ]
            |> List.exists (fun pattern -> System.Text.RegularExpressions.Regex.IsMatch(text, pattern))

        fun name ->
            let lowercase = name.Length > 0 && not (Char.IsUpper name.[0])

            patterns.Value
            |> List.exists (fun sibling ->
                match sibling with
                | SiblingParsed names -> names.Contains name
                | SiblingText text -> lowercase && Text.mentionsIdentifier text name && bindsAsPattern text name
                | SiblingUnreadable -> true)

/// What the scope gate is holding back, per rule code, for the run to
/// report. Only the CLI reads it; editors show the findings themselves.
let heldByScope = System.Collections.Concurrent.ConcurrentDictionary<string, int>()

/// The caveat a widened finding carries. Deliberately about SHAPE rather
/// than about visibility: the risk is not that the declaration is public,
/// it is that something outside this assembly can observe its compiled
/// form — a linker, or a serializer. And serialization cannot be detected:
/// System.Text.Json, Newtonsoft, XmlSerializer, DataContract, protobuf,
/// MessagePack and whatever a consumer wired up by reflection all read the
/// shape, and a guard that enumerated some of them would break the rest
/// silently. So the tool does not guess — it says what changes and leaves
/// the judgement to the person reading the code, who is the only reliable
/// detector there is.
[<Literal>]
let private ShapeCaveat =
    " CHANGES THE PUBLIC SHAPE: safe only if nothing outside this assembly links to it or serializes it (JSON, XML, protobuf - the tool cannot tell)."

/// The findings a widened scope adds, marked with the caveat.
///
/// The rules take the gate as a plain bool, so "which declarations did it
/// exclude?" is answered by running them both ways and differencing on
/// range — no rule needs to learn to explain itself. Editors show the
/// extras as light bulbs, because a light bulb is per-site consent from
/// the one person who knows whether that record crosses a wire. The CLI
/// only counts them: a batch run has nobody to ask, and the answer there
/// is a repository-level `"publicApi": false` rather than a fix applied on
/// a guess.
/// `scopeOpen` short-circuits: with the gate already open the second run
/// would find exactly the first one's findings, and these rules would pay
/// twice on every file for nothing.
///
/// Which host this is decides what happens to the extras, and
/// `ProjectSources.available ()` already answers that: the CLI installs a
/// cross-file parser, editors do not.
let private widened (scopeOpen: bool) (build: bool -> Message list) =
    let narrow = build scopeOpen

    if scopeOpen then
        narrow
    else

        // range carries NoComparison, so identity is its coordinates
        let key (m: Message) =
            m.Code, m.Range.FileName, m.Range.StartLine, m.Range.StartColumn

        let known = narrow |> List.map key |> Set.ofList
        let extras = build true |> List.filter (key >> known.Contains >> not)

        for m in extras do
            heldByScope.AddOrUpdate(m.Code, 1, (fun _ n -> n + 1)) |> ignore

        if ProjectSources.available () then
            // a batch run has nobody to ask; the answer there is a
            // repository-level `"publicApi": false`, which the summary names
            narrow
        else
            narrow
            @ (extras
               |> List.map (fun m ->
                   { m with
                       // NOTE-ONLY, deliberately. FsAutoComplete titles every
                       // analyzer fix "Fix <code>", so this caveat never
                       // reaches the light bulb the user clicks - it lands in
                       // the squiggle's tooltip. This branch is the EDITOR
                       // (the CLI installs a cross-file parser and took
                       // `narrow` above), the one host with no build check and
                       // no rollback. A one-click rewrite of a declaration's
                       // public compiled shape there is what the safety model
                       // rules out, so the finding is reported and the fix
                       // withheld.
                       Message = m.Message + ShapeCaveat
                       Fixes = []
                   }))

/// The EDITOR-side twin of the apply tool's comment guard: a fix whose
/// span contains a comment that no fix of the same message re-emits would
/// silently DELETE it through the light bulb — and unlike the CLI, the
/// editor has no build check or hold-back behind it. Messages carrying
/// such fixes are dropped from editor results entirely; the CLI keeps its
/// own guard, which also REPORTS the hold-back. Applied by the editor
/// wrappers of every rule whose fixes can span multiple lines.
let commentSafeOnly (parseTree: ParsedInput) (source: ISourceText) (messages: Message list) : Message list =
    match messages |> List.filter (fun m -> not m.Fixes.IsEmpty) with
    | [] -> messages
    | _ ->
        let comments = Text.commentsWithText parseTree source

        if comments.IsEmpty then
            messages
        else
            messages
            |> List.filter (fun m ->
                m.Fixes.IsEmpty
                || (let toTexts = m.Fixes |> List.map (fun f -> f.ToText)

                    m.Fixes
                    |> List.forall (fun f ->
                        comments
                        |> List.forall (fun (r, text) ->
                            not (Range.rangeContainsRange f.FromRange r)
                            || toTexts |> List.exists (fun t -> t.Contains text)))))

/// Does the project's --langversion allow at least this F# major version?
/// An absent flag means the SDK default, which is the latest.
let private langVersionAtLeast (major: float) (options: AnalyzerProjectOptions) =
    let explicitVersion =
        options.OtherOptions
        |> List.tryPick (fun (arg: string) ->
            if arg.StartsWith "--langversion:" then
                Some(arg.Substring "--langversion:".Length)
            else
                None)

    match explicitVersion with
    | None
    | Some("latest" | "preview" | "latestmajor") -> true
    | Some v ->
        match
            Double.TryParse(
                v,
                System.Globalization.NumberStyles.Float,
                System.Globalization.CultureInfo.InvariantCulture
            )
        with
        | true, n -> n >= major
        | false, _ -> false

/// FSharp.Core versions already read, keyed by the reference path: the
/// probe is file IO and every analyzer would otherwise repeat it per file.
let private fsharpCoreVersions =
    System.Collections.Concurrent.ConcurrentDictionary<string, int>()

/// Does the project reference an FSharp.Core new enough for this major?
///
/// String interpolation is a LIBRARY feature, and the compiler says so:
/// "Feature 'string interpolation' requires the F# library for language
/// version 5.0 or greater". `--langversion` cannot answer that, and a
/// legacy project usually sets no langversion at all — so the flag gate
/// waves it through and every interpolation fix then fails to compile.
/// PethostBackup pins FSharp.Core 4.7 out of a net45 packages folder: 28
/// FR0031 fixes applied, failed, and took a pass of unrelated fixes down
/// with them when the whole pass rolled back.
///
/// An absent or unreadable reference answers TRUE — the same
/// assume-the-latest stance the langversion gate takes, so a probe
/// failure never silences a rule that works today.
///
/// A multi-targeted project compiles the same file against EVERY
/// framework's FSharp.Core, and a pass over a wide framework sees only its
/// own: FsToolkit's net9.0 pass (FSharp.Core 9) offered `Result.isOk` in
/// files its netstandard2.0 target compiles against FSharp.Core 6. The
/// apply tool hands the lowest FSharp.Core it has resolved for the project
/// to CapabilityFix.minFSharpCoreMajor, and the gate answers for that one.
/// A file OTHER projects of the run compile too holds to theirs as well
/// (CapabilityFix.minFSharpCoreMajorFor): elmish's src/program.fs sits in
/// Elmish.fsproj on FSharp.Core 10 and in Fable.Elmish.fsproj on 4.7.
let private fsharpCoreAtLeast (major: int) (fileName: string) (options: AnalyzerProjectOptions) =
    let referencePath =
        options.OtherOptions
        |> List.tryPick (fun (arg: string) ->
            if arg.StartsWith "-r:" then
                // a path with spaces arrives quoted; matching the raw arg
                // would miss it and silently wave the project through
                let path = (arg.Substring 3).Trim '"'

                if path.EndsWith("FSharp.Core.dll", StringComparison.OrdinalIgnoreCase) then
                    Some path
                else
                    None
            else
                None)

    let own =
        match referencePath with
        | None -> Int32.MaxValue
        | Some path ->
            fsharpCoreVersions.GetOrAdd(
                path,
                fun p ->
                    try
                        System.Reflection.AssemblyName.GetAssemblyName(p).Version.Major
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        Int32.MaxValue
            )

    let found =
        match CapabilityFix.minFSharpCoreMajorFor options.ProjectFileName fileName with
        | ValueSome projectMin -> min own projectMin
        | ValueNone -> own

    found >= major

/// Interpolation needs BOTH halves: the F# 5 syntax and the FSharp.Core
/// that backs it.
let private canInterpolate (fileName: string) (options: AnalyzerProjectOptions) =
    langVersionAtLeast 5.0 options && fsharpCoreAtLeast 5 fileName options

/// Does the project reference an assembly of this simple name?
let private referencesAssembly (name: string) (options: AnalyzerProjectOptions) =
    options.OtherOptions
    |> List.exists (fun (arg: string) ->
        arg.StartsWith "-r:"
        && System.IO.Path.GetFileNameWithoutExtension((arg.Substring 3).Trim '"')
           |> fun n -> n.Equals(name, StringComparison.OrdinalIgnoreCase))

/// `task { }` needs FSharp.Core 6, and a Fable project compiles to a
/// target where a test's blocking IS the behaviour under test — Fable's
/// own suites assert `Async.RunSynchronously` semantics — so neither may
/// have its tests rewritten around a Task.
let private canReturnTask (fileName: string) (options: AnalyzerProjectOptions) =
    fsharpCoreAtLeast 6 fileName options
    && not (referencesAssembly "Fable.Core" options)

// ---- FR0001 MatchToIf ----

let private matchToIfMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MatchToIf.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0001"
            "This boolean match expression can be written as an if-else expression."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("MatchToIf", "Rewrite a boolean match expression as if-else", HelpBase)>]
let matchToIfEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0001" "MatchToIf" (fun () ->
        matchToIfMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MatchToIf", "Rewrite a boolean match expression as if-else", HelpBase)>]
let matchToIfCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0001" "MatchToIf" (fun () ->
        matchToIfMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0108 / FR0109 BooleanSimplify ----

let private booleanSimplifyMessages (fileName: string) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    let identityEnabled =
        Configuration.isRuleEnabled fileName "FR0108" "BooleanIdentity"

    let duplicateEnabled =
        Configuration.isRuleEnabled fileName "FR0109" "BooleanDuplicate"

    if not (identityEnabled || duplicateEnabled) then
        []
    else
        BooleanSimplify.find parseTree source
        |> List.choose (fun s ->
            match s.Kind with
            | BooleanSimplify.Kind.Identity when identityEnabled ->
                Some(
                    hint
                        "FR0108"
                        "The boolean literal contributes nothing here; the expression is the other operand."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ]
                )
            | BooleanSimplify.Kind.Duplicate when duplicateEnabled ->
                Some(
                    hint
                        "FR0109"
                        "Both operands are the same expression; one suffices - unless the duplicate was meant to be something else, which is worth a look."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ]
                )
            | _ -> None)

[<EditorAnalyzer("BooleanSimplify", "Drop boolean identity literals and duplicated operands", HelpBase)>]
let booleanSimplifyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () -> booleanSimplifyMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("BooleanSimplify", "Drop boolean identity literals and duplicated operands", HelpBase)>]
let booleanSimplifyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () -> booleanSimplifyMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

// ---- FR0110 MissingCases ----

let private missingCasesMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    MissingCases.find parseTree source checkResults
    |> List.map (fun s ->
        let names = s.MissingCases |> String.concat ", "

        hint
            "FR0110"
            $"This match has no arm for {names} and no wildcard (FS0025); the fix adds the missing arm(s) raising NotImplementedException, so the gap reports itself."
            s.Range
            [ fix s.Range "" s.InsertText ])

[<EditorAnalyzer("MissingCases", "Complete an incomplete DU match with explicit raising arms", HelpBase)>]
let missingCasesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0110" "MissingCases" (fun () ->
        whenChecked ctx (missingCasesMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("MissingCases", "Complete an incomplete DU match with explicit raising arms", HelpBase)>]
let missingCasesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0110" "MissingCases" (fun () ->
        missingCasesMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0118 CancellationOverload ----

let private cancellationMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    let calls = CancellationOverload.find parseTree source checkResults

    let loops =
        CancellationOverload.findUnobservedLoopsWith calls parseTree source checkResults
        |> List.map (fun (s: CancellationOverload.LoopSuggestion) ->
            hint
                "FR0118"
                $"'{s.TokenName}' is in scope but this loop never observes it - no call in the body takes it and nothing checks it - so cancellation cannot stop the loop; pass it to a call inside, or start the body with `{s.TokenName}.ThrowIfCancellationRequested()` (the fix)."
                s.Range
                (s.Fix
                 |> Option.map (fun (r, original, replacement) -> fix r original replacement)
                 |> Option.toList))

    calls
    |> List.map (fun (s: CancellationOverload.Suggestion) ->
        let message =
            match s.Kind with
            | CancellationOverload.TokenGap.Omitted ->
                $"'{s.MethodName}' has an overload accepting a CancellationToken and '{s.TokenName}' sits unused in scope; without it, cancellation stops propagating exactly one call too early."
            | CancellationOverload.TokenGap.NonePassed ->
                $"CancellationToken.None is passed although '{s.TokenName}' is in scope; the chain is cut here instead of propagated."

        hint "FR0118" message s.Range [ fix s.Range s.Original s.Replacement ])
    |> fun calls -> calls @ loops

[<EditorAnalyzer("CancellationOverload", "Pass the in-scope CancellationToken to calls that take one", HelpBase)>]
let cancellationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0118" "CancellationOverload" (fun () ->
        whenChecked ctx (cancellationMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("CancellationOverload", "Pass the in-scope CancellationToken to calls that take one", HelpBase)>]
let cancellationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0118" "CancellationOverload" (fun () ->
        cancellationMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0119 AwaitableOverload ----

let private awaitableMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    // The async twin is a CAPABILITY: DbConnection.BeginTransactionAsync
    // and its kind arrived in netstandard2.1, and the twin resolves only
    // against the framework being swept. On a wider pass of a
    // multi-targeted project this rewrite lands in shared code and the
    // narrow frameworks stop compiling — SQLProvider's Postgresql
    // provider did exactly that.
    //
    // Unlike FR0038 the fix is SEVERAL edits (the binding keyword and the
    // call), so it cannot pair with the project's guard the way a
    // single-span swap does: two independent #if blocks would leave a
    // `let!` in one world and its call in another. So on a pass that
    // would need a guard the advice stands and the edit does not.
    // EITHER position means this pass sees a wider surface than the
    // project's narrowest target: a guard exists and the multi-edit swap
    // cannot pair with it, or no guard exists at all. Reading only the
    // first left SwaggerProvider — which has no framework-shaped constant
    // — taking `Dispose()` to `DisposeAsync()`, whose interface
    // netstandard2.0 does not have: "System from netstandard did not
    // contain IAsyncDisposable".
    let widerThanNarrowest =
        (CapabilityFix.dualGuardConstant ()).IsSome || CapabilityFix.guardUnavailable ()

    AwaitableOverload.find parseTree source checkResults
    |> List.map (fun s ->
        let fixes =
            if widerThanNarrowest then
                []
            else
                s.Fixes
                |> List.map (fun (r, original, replacement) -> fix r original replacement)

        let suffix =
            if widerThanNarrowest then
                " (no automatic fix here: this project targets frameworks whose surface differs, and the swap spans more than one edit)"
            else
                ""

        hint
            "FR0119"
            $"'{s.MethodName}' blocks inside the computation although '{s.MethodName}Async' exists; binding the async twin keeps the thread free - and FR0118 hands it the CancellationToken on the next pass.{suffix}"
            s.Range
            fixes)

[<EditorAnalyzer("AwaitableOverload", "Use the async twin of a blocking call inside task/async", HelpBase)>]
let awaitableEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0119" "AwaitableOverload" (fun () ->
        whenChecked ctx (awaitableMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("AwaitableOverload", "Use the async twin of a blocking call inside task/async", HelpBase)>]
let awaitableCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0119" "AwaitableOverload" (fun () ->
        awaitableMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0120 CatchLogException ----

let private catchLogMessages
    (parseTree: ParsedInput)
    (source: ISourceText)
    (offerAlternatives: bool)
    checkResults
    : Message list =
    CatchLogException.find parseTree source checkResults
    |> List.collect (fun s ->
        // the insert each library spells: an exception-first argument for
        // MEL and Serilog, an addExn stage for a Logary pipeline
        let insert (exception': string) =
            match s.Family with
            | "Logary" when exception'.Contains '.' -> $" |> Message.addExn ({exception'})"
            | "Logary" -> $" |> Message.addExn {exception'}"
            | _ -> $"{exception'}, "

        let howItLands =
            match s.Family with
            | "Logary" -> "adding it with Message.addExn lets the sink decide rendering"
            | _ -> "passing it first lets the sink decide rendering"

        let primary =
            hint
                "FR0120"
                $"This {s.LogMethod} inside the handler never mentions '{s.ExceptionName}' - the one fact the handler exists to record; {howItLands} (logging only {s.ExceptionName}.Message deliberately is a legitimate PII choice - write that instead)."
                s.Range
                [ fix s.Range "" (insert s.ExceptionName) ]

        if offerAlternatives then
            [
                primary
                hint
                    "FR0120"
                    $"Alternative: pass {s.ExceptionName}.GetBaseException() - the root cause of a wrapped or aggregate exception."
                    s.Range
                    [ fix s.Range "" (insert $"{s.ExceptionName}.GetBaseException()") ]
            ]
        else
            [ primary ])

[<EditorAnalyzer("CatchLogException", "Pass the caught exception to catch-clause log calls", HelpBase)>]
let catchLogEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0120" "CatchLogException" (fun () ->
        whenChecked ctx (catchLogMessages ctx.ParseFileResults.ParseTree ctx.SourceText true))

[<CliAnalyzer("CatchLogException", "Pass the caught exception to catch-clause log calls", HelpBase)>]
let catchLogCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0120" "CatchLogException" (fun () ->
        catchLogMessages ctx.ParseFileResults.ParseTree ctx.SourceText false ctx.CheckFileResults)

// ---- FR0151 ExceptionDetail / FR0152 CachedFailure ----

let private exceptionDetailMessages
    (offerFix: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    ExceptionDetail.find parseTree source checkResults
    |> List.collect (fun s ->
        // editor-only, like FR0049's sync swap: it compiles either way,
        // but WHAT GETS LOGGED is the author's call, not the tool's
        if not offerFix then
            [ hint "FR0151" s.Advice s.Range [] ]
        else
            let detail =
                match s.Fix with
                | Some(r, original, replacement) -> [ fix r original replacement ]
                | None -> []

            // an editor applies EVERY fix of a message as one action, so
            // the two repairs are two messages: the carry-on FIRST where
            // it applies — not failing at all beats reporting the failure
            // better — and the LoaderExceptions join as the alternative
            match s.AlternativeFix with
            | Some(r, original, replacement) ->
                [
                    hint "FR0151" s.Advice s.Range [ fix r original replacement ]
                    if not detail.IsEmpty then
                        hint
                            "FR0151"
                            "Alternative: report the failure with every LoaderExceptions message joined, in place of the .Message that names none of them."
                            s.Range
                            detail
                ]
            | None -> [ hint "FR0151" s.Advice s.Range detail ])

let private cachedFailureMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    CachedFailure.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0152"
            (sprintf
                "A cached %s REMEMBERS a failure instead of raising it, so the entry has to be removed when the value faults - otherwise every later GetOrAdd hands out the same failure. One transient error then outlives whatever caused it, and the dependency looks down long after it recovered. (A factory that simply THROWS is fine: GetOrAdd stores nothing and the next caller retries.)"
                s.ValueKind)
            s.Range
            [])

[<EditorAnalyzer("ExceptionDetail", "Report handlers that read only .Message from an exception carrying more", HelpBase)>]
let exceptionDetailEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0151" "ExceptionDetail" (fun () ->
        whenChecked ctx (exceptionDetailMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ExceptionDetail", "Report handlers that read only .Message from an exception carrying more", HelpBase)>]
let exceptionDetailCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0151" "ExceptionDetail" (fun () ->
        exceptionDetailMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

[<EditorAnalyzer("CachedFailure", "Report GetOrAdd caching a Task or Lazy that can remember a failure", HelpBase)>]
let cachedFailureEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0152" "CachedFailure" (fun () ->
        whenChecked ctx (cachedFailureMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("CachedFailure", "Report GetOrAdd caching a Task or Lazy that can remember a failure", HelpBase)>]
let cachedFailureCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0152" "CachedFailure" (fun () ->
        cachedFailureMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0121 DateTimeRules ----

let private dateTimeMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (offerNowFix: bool)
    checkResults
    : Message list =
    DateTimeRules.find parseTree source checkResults
    |> List.map (fun s ->
        match s.Kind, s.FixRange with
        | DateTimeRules.WallClockKind.UtcDateCut text, _ ->
            hint
                "FR0121"
                $"'{text}' cuts a calendar date at a timezone-random instant - UTC midnight is nobody's midnight, and the server's own date is a deployment accident the end user never sees; convert to the USER'S timezone first, then take the date."
                s.Range
                []
        | DateTimeRules.WallClockKind.LocalNow, Some fixRange when
            offerNowFix
            || Configuration.parameterInt fileName "FR0121" "DateTimeRules" "utcNow" 0 = 1
            ->
            hint
                "FR0121"
                "DateTime.Now reads the server's local clock - a deployment accident; DateTime.UtcNow records an instant. (Local time is right for Fable/desktop code: leave this off there.)"
                s.Range
                [ fix fixRange "Now" "UtcNow" ]
        | DateTimeRules.WallClockKind.LocalNow, _ ->
            hint
                "FR0121"
                "DateTime.Now reads the server's local clock - a deployment accident; DateTime.UtcNow records an instant. Opt the rewrite in with { \"FR0121\": { \"utcNow\": 1 } } (server code), or ignore for Fable/desktop."
                s.Range
                [])

[<EditorAnalyzer("DateTimeRules", "Timezone-random date cuts; opt-in UtcNow rewrite", HelpBase)>]
let dateTimeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0121" "DateTimeRules" (fun () ->
        whenChecked ctx (dateTimeMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText true))

[<CliAnalyzer("DateTimeRules", "Timezone-random date cuts; opt-in UtcNow rewrite", HelpBase)>]
let dateTimeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0121" "DateTimeRules" (fun () ->
        dateTimeMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText false ctx.CheckFileResults)

// ---- FR0123 MonitorLock ----

let private monitorLockMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    let leaks =
        MonitorLock.findLeaks parseTree source checkResults
        |> List.map (fun (s: MonitorLock.LeakSuggestion) ->
            hint
                "FR0123"
                $"'{s.AcquireText}' takes a slot that nothing releases on the failure path: the first exception in the body that follows leaks it and every later waiter blocks forever; put the body under `try ... finally {s.ReleaseText}`."
                s.Range
                [
                    for r, original, replacement in Option.toList s.Fix do
                        fix r original replacement
                ])

    MonitorLock.find parseTree source checkResults
    |> List.map (fun (s: MonitorLock.Suggestion) ->
        match s.Fix with
        | Some(r, original, replacement) ->
            hint
                "FR0123"
                $"Monitor.Enter/try/finally/Monitor.Exit over '{s.LockText}' is the `lock` function spelled dangerously; `lock` releases on every path by construction."
                s.Range
                [ fix r original replacement ]
        | None when s.Guarded ->
            // the shape is right and cannot leak; only the rewrite is
            // withheld, and the note must not call it a leak
            hint
                "FR0123"
                $"Monitor.Enter/try/finally/Monitor.Exit over '{s.LockText}' is what `lock {s.LockText} (fun () -> ...)` spells in one line; not rewritten here because the body binds in a computation, reads a mutable declared outside it, or crosses a compiler directive - a lambda could not take it verbatim."
                s.Range
                []
        | None ->
            hint
                "FR0123"
                $"Monitor.Enter '{s.LockText}' without a guarding try/finally leaks the lock on the first exception; `lock {s.LockText} (fun () -> ...)` cannot."
                s.Range
                [])
    |> fun monitors -> monitors @ leaks

[<EditorAnalyzer("MonitorLock", "Monitor.Enter/Exit pairs become the lock function", HelpBase)>]
let monitorLockEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0123" "MonitorLock" (fun () ->
        whenChecked ctx (monitorLockMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MonitorLock", "Monitor.Enter/Exit pairs become the lock function", HelpBase)>]
let monitorLockCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0123" "MonitorLock" (fun () ->
        monitorLockMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0124 LogTemplates ----

let private logTemplateMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    LogTemplates.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            match s.Problem with
            | LogTemplates.TemplateProblem.CountMismatch(placeholders, arguments) ->
                $"This {s.LogMethod} template names {placeholders} placeholder(s) but receives {arguments} argument(s); the sink logs holes or drops values silently."
            | LogTemplates.TemplateProblem.DuplicateName name ->
                $"This {s.LogMethod} template names '{{{name}}}' twice; structured sinks key properties by name, so one value overwrites the other."
            | LogTemplates.TemplateProblem.Interpolated ->
                $"An interpolated string as a {s.LogMethod} template destroys structured logging: every message becomes a distinct event, and the values lose their property names - use a constant template with placeholders."
            | LogTemplates.TemplateProblem.MissingFields names ->
                let listed = names |> List.map (fun n -> "{" + n + "}") |> String.concat ", "

                $"This {s.LogMethod} template names {listed} but no Message.setField in this pipeline fills them; the sink prints the braces as they are."

        hint "FR0124" message s.Range [])

[<EditorAnalyzer("LogTemplates", "Structured-log templates must match their arguments", HelpBase)>]
let logTemplatesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0124" "LogTemplates" (fun () ->
        whenChecked ctx (logTemplateMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("LogTemplates", "Structured-log templates must match their arguments", HelpBase)>]
let logTemplatesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0124" "LogTemplates" (fun () ->
        logTemplateMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0117 MatchArmMerge ----

let private matchArmMergeMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MissingCases.findMergeableArms parseTree source
    |> List.map (fun s ->
        hint
            "FR0117"
            $"{s.Count} adjacent arms return the same result; one or-pattern arm says it once - same patterns, same order."
            s.ReplaceRange
            [ fix s.ReplaceRange (Text.textOfRange source s.ReplaceRange) s.NewText ])

[<EditorAnalyzer("MatchArmMerge", "Fold adjacent same-result match arms into an or-pattern", HelpBase)>]
let matchArmMergeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0117" "MatchArmMerge" (fun () ->
        matchArmMergeMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MatchArmMerge", "Fold adjacent same-result match arms into an or-pattern", HelpBase)>]
let matchArmMergeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0117" "MatchArmMerge" (fun () ->
        matchArmMergeMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0111 / FR0112 / FR0113 IfRestructure ----

let private ifRestructureMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    let elseIfEnabled = Configuration.isRuleEnabled fileName "FR0111" "ElseIfFlatten"

    let chainEnabled =
        Configuration.isRuleEnabled fileName "FR0112" "EqualityChainToMatch"

    let mergeEnabled = Configuration.isRuleEnabled fileName "FR0113" "NestedIfMerge"

    let flipEnabled = Configuration.isRuleEnabled fileName "FR0114" "PyramidFlip"

    let guardOrderEnabled = Configuration.isRuleEnabled fileName "FR0115" "GuardOrder"

    // configurable knobs, FR0114's per-rule parameters:
    //     { "FR0114": { "enabled": true, "thenAtLeast": 30, "elseAtMost": 2 } }
    let thenAtLeast =
        Configuration.parameterInt fileName "FR0114" "PyramidFlip" "thenAtLeast" 20

    let elseAtMost =
        Configuration.parameterInt fileName "FR0114" "PyramidFlip" "elseAtMost" 3
        // overlapping thresholds would make the flip fire on its own
        // output and oscillate every pass; clamp so a flipped branch can
        // never re-qualify
        |> min (thenAtLeast - 1)

    [
        if flipEnabled then
            for s in IfRestructure.findPyramidFlips thenAtLeast elseAtMost parseTree source do
                hint
                    "FR0114"
                    "A large then-branch behind a small else reads bottom-heavy; flipping the condition puts the short exit first."
                    s.Range
                    [ fix s.Range s.OriginalText s.ReplacementText ]
        if guardOrderEnabled then
            for s in IfRestructure.findGuardOrderNotes parseTree source do
                hint
                    "FR0115"
                    $"The base case sits FIRST behind a compound guard on '{s.Variable}'; every new error condition must be threaded into it. Inverted - error guards first, the base case as the final arm - the match reads top-down and extends by appending."
                    s.Range
                    []
        if elseIfEnabled then
            for s in IfRestructure.findElseIf parseTree source do
                hint
                    "FR0111"
                    "This `else` holds a whole nested if; `elif` says the same thing one level flatter."
                    s.Range
                    [ fix s.Range s.OriginalText s.ReplacementText ]
        if chainEnabled then
            for s in IfRestructure.findEqualityChains parseTree source checkResults do
                hint
                    "FR0112"
                    "This if/elif chain compares one identifier against distinct literals; a match states the same dispatch directly."
                    s.Range
                    [ fix s.Range s.OriginalText s.ReplacementText ]
        if mergeEnabled then
            for s in IfRestructure.findNestedIfMerges parseTree source do
                hint
                    "FR0113"
                    "The nested if can merge into one `&&` condition - the branches are unchanged, one level of nesting is gone."
                    s.Range
                    [ fix s.Range s.OriginalText s.ReplacementText ]
    ]

[<EditorAnalyzer("IfRestructure", "Flatten else-if, chain-to-match, nested-if merges", HelpBase)>]
let ifRestructureEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                whenChecked ctx (ifRestructureMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
                |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("IfRestructure", "Flatten else-if, chain-to-match, nested-if merges", HelpBase)>]
let ifRestructureCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                ifRestructureMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)
    }

// ---- FR0116 RecGroup ----

let private recGroupMessages check (parseTree: ParsedInput) (source: ISourceText) : Message list =
    let extractions =
        RecGroup.find check parseTree source
        |> List.map (fun s ->
            let explanation =
                match s.Members with
                | [ _ ] when s.IsSelfRecursive ->
                    $"'{s.MemberName}' calls only itself, no other member of its `let rec` group; its own `let rec` above the group narrows the knot."
                | [ _ ] ->
                    $"'{s.MemberName}' references no member of its `let rec` group; a plain `let` above the group says it takes part in no recursion."
                | members ->
                    let named = members |> List.map (fun (n, _) -> $"'{n}'") |> String.concat ", "

                    $"{named} reference no member of their `let rec` group beyond each other; their own `let`s above the group say they take part in no recursion."

            hint
                "FR0116"
                explanation
                s.RemoveRange
                // explicit yields: an element followed by a `for` in a list
                // is a discarded statement (FS0020), and the insert was
                // silently lost - FAKE's Wix.fs had a member deleted and
                // never put back
                (fix s.InsertRange "" s.InsertText
                 :: [ for r in s.Removes -> fix r (Text.textOfRange source r) "" ]))

    let recrowns =
        RecGroup.findHeadRecrowns check parseTree source
        |> List.map (fun s ->
            hint
                "FR0116"
                $"'{s.MemberName}' heads its `let rec` group but references no member; a plain `let` with the group re-crowned below says it takes part in no recursion."
                s.LetRecRange
                [
                    fix s.LetRecRange (Text.textOfRange source s.LetRecRange) "let"
                    fix s.AndRange (Text.textOfRange source s.AndRange) "let rec"
                ])

    extractions @ recrowns

[<EditorAnalyzer("RecGroup", "Pull non-recursive members out of let rec groups", HelpBase)>]
let recGroupEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0116" "RecGroup" (fun () ->
        recGroupMessages None ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RecGroup", "Pull non-recursive members out of let rec groups", HelpBase)>]
let recGroupCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0116" "RecGroup" (fun () ->
        recGroupMessages (Some ctx.CheckFileResults) ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0002 OptionModule ----

let private optionModuleMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    OptionModule.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            if s.Target = "" then
                "This match expression is the identity on an option and can be removed."
            else
                $"This match expression can be written with %s{s.Target}."

        hint "FR0002" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("OptionModule", "Rewrite Some/None matching with Option-module functions", HelpBase)>]
let optionModuleEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0002" "OptionModule" (fun () ->
        whenChecked ctx (optionModuleMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("OptionModule", "Rewrite Some/None matching with Option-module functions", HelpBase)>]
let optionModuleCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0002" "OptionModule" (fun () ->
        optionModuleMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0003 Composition ----

let private compositionMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    Composition.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0003"
            "This lambda is a function composition and can be written with >>."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("Composition", "Extract a function composition from a lambda", HelpBase)>]
let compositionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0003" "Composition" (fun () ->
        whenChecked ctx (fun checkResults ->
            compositionMessages ctx.ParseFileResults.ParseTree ctx.SourceText checkResults
            |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("Composition", "Extract a function composition from a lambda", HelpBase)>]
let compositionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0003" "Composition" (fun () ->
        compositionMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0004 ConversionMove ----

let private conversionMoveMessages
    (check: FSharpCheckFileResults option)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    ConversionMove.findWith check parseTree source
    |> List.map (fun s ->
        let message =
            if s.Eliminated then
                "This collection conversion is unnecessary before a consuming operation."
            else
                "This collection conversion can be moved after the operation, avoiding an intermediate collection."

        hint "FR0004" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ConversionMove", "Move or drop List/Seq/Array conversions in pipelines", HelpBase)>]
let conversionMoveEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0004" "ConversionMove" (fun () ->
        // the check results are optional: a short-circuiting consumer over
        // a source only the typed proof can clear waits for them
        conversionMoveMessages ctx.CheckFileResults ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ConversionMove", "Move or drop List/Seq/Array conversions in pipelines", HelpBase)>]
let conversionMoveCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0004" "ConversionMove" (fun () ->
        conversionMoveMessages (Some ctx.CheckFileResults) ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0005 CeStrip ----

let private ceStripMessages
    (check: FSharpCheckFileResults option)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    CeStrip.findWith check parseTree source
    |> List.map (fun s ->
        let message =
            match s.Kind with
            | CeStrip.StripKind.WithRunner -> "This async wrapping is immediately run and can be removed."
            | CeStrip.StripKind.Forwarded -> "This async wrapping does nothing and can be removed."
            | CeStrip.StripKind.ReturnBangIdentity ->
                "return! around a builder whose whole body is one return statement is a no-op machine; the inner statement is the arm."
            | CeStrip.StripKind.TaskFromResult ->
                "This task wrapping only wraps a value and can be written with Task.FromResult."
            | CeStrip.StripKind.ThunkIdentity ->
                "This tail thunk is defined and immediately called; the binding is its body."

        hint "FR0005" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("CeStrip", "Strip computation-expression wrapping that does nothing", HelpBase)>]
let ceStripEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0005" "CeStrip" (fun () ->
        ceStripMessages ctx.CheckFileResults ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("CeStrip", "Strip computation-expression wrapping that does nothing", HelpBase)>]
let ceStripCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0005" "CeStrip" (fun () ->
        ceStripMessages (Some ctx.CheckFileResults) ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0006 ActivePattern ----

let private activePatternMessages
    (structForm: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    ActivePattern.find structForm parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0006"
            ($"This guard can be extracted into an active pattern (|%s{s.PatternName}|_|).")
            s.ClauseRange
            [
                fix s.ClauseRange s.OriginalClauseText s.ClauseText
                fix s.InsertRange "" s.InsertText
            ])

[<EditorAnalyzer("ActivePattern", "Extract a when-guard into an active pattern", HelpBase)>]
let activePatternEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0006" "ActivePattern" (fun () ->
        whenChecked
            ctx
            (activePatternMessages
                (fsharpCoreAtLeast 6 ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText))

[<CliAnalyzer("ActivePattern", "Extract a when-guard into an active pattern", HelpBase)>]
let activePatternCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0006" "ActivePattern" (fun () ->
        activePatternMessages
            (fsharpCoreAtLeast 6 ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

// ---- FR0007 MutableRemoval ----

let private mutableRemovalMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    MutableRemoval.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0007"
            ($"'%s{s.Name}' is never mutated; the mutable keyword can be removed.")
            s.Range
            [ fix s.Range s.OriginalText "" ])

[<EditorAnalyzer("MutableRemoval", "Remove mutable from never-mutated local bindings", HelpBase)>]
let mutableRemovalEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0007" "MutableRemoval" (fun () ->
        whenChecked ctx (mutableRemovalMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("MutableRemoval", "Remove mutable from never-mutated local bindings", HelpBase)>]
let mutableRemovalCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0007" "MutableRemoval" (fun () ->
        mutableRemovalMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0008 TupleParams ----

let private tupleParamsMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    TupleParams.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0008"
            ($"Private function '%s{s.FunctionName}' takes a tuple; curried parameters are more idiomatic F#.")
            s.DefRange
            (s.Edits |> List.map (fun e -> fix e.Range e.Original e.Replacement)))

[<EditorAnalyzer("TupleParams", "Convert private tupled functions to curried parameters", HelpBase)>]
let tupleParamsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0008" "TupleParams" (fun () ->
        whenChecked ctx (tupleParamsMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("TupleParams", "Convert private tupled functions to curried parameters", HelpBase)>]
let tupleParamsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0008" "TupleParams" (fun () ->
        tupleParamsMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0009 ResultModule ----

/// `Result.defaultValue`, `defaultWith`, `isOk` and `isError` arrived in
/// FSharp.Core 9: on Giraffe's example project (FSharp.Core 6) every such
/// rewrite was "The value, constructor, namespace or type 'defaultValue'
/// is not defined" and rolled back. `iter` (ResultModule.Iterate) is one of
/// the same set: FSharp.Core 6.0.0-6.0.5 have only `map`, `bind` and
/// `mapError`, and the set landed in 6.0.6 — which shares its assembly
/// version 6.0.0.0 with them, so the major-version gate cannot tell them
/// apart and holds `iter` to the same threshold. `map`, `bind` and
/// `mapError` are older and stay.
let private needsCore9 (target: string) =
    [
        "Result.defaultValue"
        "Result.defaultWith"
        "Result.isOk"
        "Result.isError"
        "Result.iter"
    ]
    |> List.exists target.Contains

let private resultModuleMessages
    (allowCore9: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    ResultModule.find parseTree source checkResults
    |> List.filter (fun s -> allowCore9 || not (needsCore9 s.Target))
    |> List.map (fun s ->
        let message =
            if s.Target = "" then
                "This match expression is the identity on a Result and can be removed."
            else
                $"This match expression can be written with %s{s.Target}."

        hint "FR0009" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ResultModule", "Rewrite Ok/Error matching with Result-module functions", HelpBase)>]
let resultModuleEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0009" "ResultModule" (fun () ->
        whenChecked
            ctx
            (resultModuleMessages
                (fsharpCoreAtLeast 9 ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ResultModule", "Rewrite Ok/Error matching with Result-module functions", HelpBase)>]
let resultModuleCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0009" "ResultModule" (fun () ->
        resultModuleMessages
            (fsharpCoreAtLeast 9 ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

// ---- FR0010 Simplification ----

let private simplificationMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    Simplification.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            match s.Kind with
            | Simplification.SimplificationKind.BooleanIdentity ->
                "This if-expression just returns the condition and can be simplified."
            | Simplification.SimplificationKind.OptionComparison ->
                "Comparing against None is the IsNone/IsSome test spelled as an equality."
            | Simplification.SimplificationKind.OptionProperty ->
                "Option.isSome/isNone on a name is the IsSome/IsNone property spelled as a call; the property reads directly."
            | Simplification.SimplificationKind.Emptiness ->
                "Comparing length against zero can be written with isEmpty (and avoids forcing a full sequence)."

        hint "FR0010" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("Simplification", "Simplify boolean, None-comparison, and emptiness idioms", HelpBase)>]
let simplificationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0010" "Simplification" (fun () ->
        simplificationMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

[<CliAnalyzer("Simplification", "Simplify boolean, None-comparison, and emptiness idioms", HelpBase)>]
let simplificationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0010" "Simplification" (fun () ->
        simplificationMessages ctx.ParseFileResults.ParseTree ctx.SourceText (Some ctx.CheckFileResults))

// ---- FR0011 StructActivePattern ----

let private structActivePatternMessages
    (scopeOpen: bool)
    (seenByLaterFile: string -> bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    widened scopeOpen (fun scope ->
        StructActivePattern.findWith seenByLaterFile scope parseTree source checkResults
        |> List.map (fun s ->
            hint
                "FR0011"
                (sprintf
                    "Active pattern (%s) can return a struct option ([<return: Struct>]), avoiding an allocation per match attempt."
                    s.PatternName)
                s.NameRange
                (s.Edits |> List.map (fun e -> fix e.Range e.Original e.Replacement))))

[<EditorAnalyzer("StructActivePattern", "Make trivial partial active patterns struct-returning", HelpBase)>]
let structActivePatternEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0011" "StructActivePattern" (fun () ->
        whenChecked ctx (fun check ->
            if fsharpCoreAtLeast 6 ctx.FileName ctx.ProjectOptions then
                structActivePatternMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    (seenByLaterFile ctx.FileName ctx.ProjectOptions)
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    check
            else
                []))

[<CliAnalyzer("StructActivePattern", "Make trivial partial active patterns struct-returning", HelpBase)>]
let structActivePatternCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0011" "StructActivePattern" (fun () ->
        if fsharpCoreAtLeast 6 ctx.FileName ctx.ProjectOptions then
            structActivePatternMessages
                (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                (seenByLaterFile ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText
                ctx.CheckFileResults
        else
            [])

// ---- FR0012 Hints ----

let private hintMessages
    (extraRules: string list)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults option)
    : Message list =
    HintEngine.find extraRules parseTree source check
    |> List.map (fun s ->
        hint
            "FR0012"
            ($"This expression can be simplified (%s{s.Rule}).")
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("Hints", "Term-rewriting hints (fsharplint-style rules)", HelpBase)>]
let hintsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0012" "Hints" (fun () ->
        hintMessages
            (Configuration.hintsFor ctx.FileName)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

[<CliAnalyzer("Hints", "Term-rewriting hints (fsharplint-style rules)", HelpBase)>]
let hintsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0012" "Hints" (fun () ->
        hintMessages
            (Configuration.hintsFor ctx.FileName)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            (Some ctx.CheckFileResults))

// ---- FR0013 RedundantParens ----

let private redundantParensMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    RedundantParens.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0013"
            "Redundant parentheses around a single atomic argument."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("RedundantParens", "Drop redundant parentheses around single atomic arguments", HelpBase)>]
let redundantParensEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0013" "RedundantParens" (fun () ->
        redundantParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RedundantParens", "Drop redundant parentheses around single atomic arguments", HelpBase)>]
let redundantParensCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0013" "RedundantParens" (fun () ->
        redundantParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0094 MethodCallParens ----

let private methodCallParensMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MethodCallParens.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0094"
            "Redundant parentheses around a single atomic method-call argument."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("MethodCallParens", "Drop redundant parentheses around single method-call arguments", HelpBase)>]
let methodCallParensEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0094" "MethodCallParens" (fun () ->
        methodCallParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MethodCallParens", "Drop redundant parentheses around single method-call arguments", HelpBase)>]
let methodCallParensCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0094" "MethodCallParens" (fun () ->
        methodCallParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0095 LambdaBuiltin ----

let private lambdaBuiltinMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    LambdaBuiltin.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0095"
            $"This lambda is exactly `{s.ReplacementText}`."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("LambdaBuiltin", "Lambdas that restate id, fst or snd", HelpBase)>]
let lambdaBuiltinEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0095" "LambdaBuiltin" (fun () ->
        lambdaBuiltinMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("LambdaBuiltin", "Lambdas that restate id, fst or snd", HelpBase)>]
let lambdaBuiltinCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0095" "LambdaBuiltin" (fun () ->
        lambdaBuiltinMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0096 PatternParens ----

let private patternParensMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    PatternParens.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0096"
            "Redundant parentheses around a pattern."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("PatternParens", "Drop redundant parentheses around patterns", HelpBase)>]
let patternParensEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0096" "PatternParens" (fun () ->
        patternParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("PatternParens", "Drop redundant parentheses around patterns", HelpBase)>]
let patternParensCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0096" "PatternParens" (fun () ->
        patternParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0097 / FR0098 TypeSyntax ----

let private typeParensMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    TypeSyntax.findRedundantParens parseTree source
    |> List.map (fun s ->
        hint "FR0097" "Redundant parentheses around a type." s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("TypeParens", "Drop redundant parentheses around types", HelpBase)>]
let typeParensEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0097" "TypeParens" (fun () ->
        typeParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("TypeParens", "Drop redundant parentheses around types", HelpBase)>]
let typeParensCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0097" "TypeParens" (fun () ->
        typeParensMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

let private abbreviatedTypeMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    TypeSyntax.findAbbreviations parseTree source
    |> List.map (fun s ->
        hint
            "FR0098"
            $"F# abbreviates this type as `{s.ReplacementText}`."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("AbbreviatedType", "Use F# type abbreviations for BCL names", HelpBase)>]
let abbreviatedTypeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0098" "AbbreviatedType" (fun () ->
        abbreviatedTypeMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("AbbreviatedType", "Use F# type abbreviations for BCL names", HelpBase)>]
let abbreviatedTypeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0098" "AbbreviatedType" (fun () ->
        abbreviatedTypeMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0099 TrailingSemicolon ----

let private trailingSemicolonMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    TrailingSemicolon.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0099"
            "A `;` at the end of a line does nothing in light syntax."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("TrailingSemicolon", "Drop line-ending semicolons", HelpBase)>]
let trailingSemicolonEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0099" "TrailingSemicolon" (fun () ->
        trailingSemicolonMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("TrailingSemicolon", "Drop line-ending semicolons", HelpBase)>]
let trailingSemicolonCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0099" "TrailingSemicolon" (fun () ->
        trailingSemicolonMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0100 UnimplementedBranch ----

let private unimplementedBranchMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    UnimplementedBranch.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0100"
            "This branch says it is unfinished and then returns a value a caller cannot tell from a real one; `raise (NotImplementedException())` reports the gap where it is."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("UnimplementedBranch", "Unfinished match branches returning a stand-in value", HelpBase)>]
let unimplementedBranchEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0100" "UnimplementedBranch" (fun () ->
        unimplementedBranchMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("UnimplementedBranch", "Unfinished match branches returning a stand-in value", HelpBase)>]
let unimplementedBranchCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0100" "UnimplementedBranch" (fun () ->
        unimplementedBranchMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0014 DictTryGet ----

let private dictTryGetMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    DictTryGet.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            if s.Concurrent then
                "ContainsKey followed by the indexer is a race on ConcurrentDictionary; use a single TryGetValue."
            else
                "ContainsKey followed by the indexer looks the key up twice; use a single TryGetValue."

        hint "FR0014" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("DictTryGet", "Replace ContainsKey-plus-indexer with TryGetValue", HelpBase)>]
let dictTryGetEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0014" "DictTryGet" (fun () ->
        whenChecked ctx (dictTryGetMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("DictTryGet", "Replace ContainsKey-plus-indexer with TryGetValue", HelpBase)>]
let dictTryGetCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0014" "DictTryGet" (fun () ->
        dictTryGetMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0015 RegexUsage ----

/// Is the per-call (non-loop) hoist on? Default true: a function is far
/// likelier to be called many times than a module is to be initialised
/// and its hoisted binding never read — F# builds a module's bindings on
/// first access, so the one that is never reached costs nothing. A
/// codebase that would rather keep the construction where it is written
/// sets `{ "FR0015": { "perCall": false } }` and keeps the loop hoists.
let private regexPerCallHoist (fileName: string) =
    Configuration.parameterBool fileName "FR0015" "RegexUsage" "perCall" true

let private regexUsageMessages (fileName: string) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    RegexUsage.find parseTree source
    |> RegexUsage.keepingPerCall (regexPerCallHoist fileName)
    |> List.map (fun s ->
        let message =
            match s.Kind with
            | RegexUsage.RegexSuggestionKind.StringOperation ->
                "This literal regex pattern is a plain string operation."
            | RegexUsage.RegexSuggestionKind.HoistFromLoop ->
                match s.Repeat with
                | RegexUsage.Repeat.LoopIteration ->
                    "This Regex call re-parses its pattern on every loop iteration; construct one Regex before the loop and reuse it."
                | RegexUsage.Repeat.FunctionCall ->
                    "This Regex call looks its pattern up in the runtime's cache on every call, and re-parses it once the cache (fifteen patterns) turns over; the fix hoists one Regex instance to a module-level binding built once."
            | RegexUsage.RegexSuggestionKind.HoistConstruction ->
                match s.Repeat with
                | RegexUsage.Repeat.LoopIteration ->
                    "This Regex is constructed - its pattern parsed and compiled - on every loop iteration; the fix hoists the construction to a module-level binding built once."
                | RegexUsage.Repeat.FunctionCall ->
                    "This Regex is constructed - its pattern parsed and compiled - on every call of the enclosing function; the fix hoists the construction to a module-level binding built once."

        hint "FR0015" message s.Range (s.Edits |> List.map (fun (r, o, t) -> fix r o t)))

[<EditorAnalyzer("RegexUsage", "Simplify literal regex patterns; hoist Regex construction out of loops", HelpBase)>]
let regexUsageEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0015" "RegexUsage" (fun () ->
        regexUsageMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RegexUsage", "Simplify literal regex patterns; hoist Regex construction out of loops", HelpBase)>]
let regexUsageCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0015" "RegexUsage" (fun () ->
        regexUsageMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0122 RegexValidity ----

let private regexValidityMessages (parseTree: ParsedInput) : Message list =
    RegexUsage.findInvalidPatterns parseTree
    |> List.map (fun (r, pattern, error) ->
        let firstLine =
            match error.IndexOf '\n' with
            | -1 -> error
            | cut -> error.Substring(0, cut).TrimEnd()

        hint
            "FR0122"
            $"This regex pattern does not compile - a guaranteed ArgumentException on first use: {firstLine}"
            r
            [])

[<EditorAnalyzer("RegexValidity", "Literal regex patterns must compile", HelpBase)>]
let regexValidityEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0122" "RegexValidity" (fun () -> regexValidityMessages ctx.ParseFileResults.ParseTree)

[<CliAnalyzer("RegexValidity", "Literal regex patterns must compile", HelpBase)>]
let regexValidityCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0122" "RegexValidity" (fun () -> regexValidityMessages ctx.ParseFileResults.ParseTree)

// ---- FR0016 StructDu ----

let private structDuMessages
    (check: FSharpCheckFileResults option)
    (sharedFieldNames: bool)
    (scopeOpen: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    widened scopeOpen (fun scope ->
        StructDu.findWith check sharedFieldNames scope parseTree source
        |> List.map (fun s ->
            hint
                "FR0016"
                (sprintf
                    "Union '%s' holds only small value types; [<Struct>] avoids a heap allocation per value."
                    s.TypeName)
                s.InsertRange
                (fix s.InsertRange "" s.InsertText
                 :: (s.SignatureEdits
                     |> List.map (fun (r, original, replacement) -> fix r original replacement)))))

[<EditorAnalyzer("StructDu", "Mark small discriminated unions with Struct", HelpBase)>]
let structDuEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0016" "StructDu" (fun () ->
        structDuMessages
            ctx.CheckFileResults
            (langVersionAtLeast 9.0 ctx.ProjectOptions)
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

[<CliAnalyzer("StructDu", "Mark small discriminated unions with Struct", HelpBase)>]
let structDuCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0016" "StructDu" (fun () ->
        structDuMessages
            (Some ctx.CheckFileResults)
            (langVersionAtLeast 9.0 ctx.ProjectOptions)
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

// ---- FR0022 DuFieldNames ----

let private duFieldNamesMessages (scopeOpen: bool) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    widened scopeOpen (fun scope ->
        DuFieldNames.find scope parseTree source
        |> List.map (fun s ->
            hint
                "FR0022"
                (sprintf
                    "Union case '%s' can name its fields (%s) after the names %s already spell."
                    s.CaseName
                    (String.concat ", " s.Names)
                    s.Source)
                s.Range
                (s.Edits
                 |> List.map (fun (r, original, replacement) -> fix r original replacement))))

[<EditorAnalyzer("DuFieldNames", "Name private union case fields after their match sites", HelpBase)>]
let duFieldNamesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0022" "DuFieldNames" (fun () ->
        duFieldNamesMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

[<CliAnalyzer("DuFieldNames", "Name private union case fields after their match sites", HelpBase)>]
let duFieldNamesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0022" "DuFieldNames" (fun () ->
        duFieldNamesMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

// ---- FR0023 ParamOrder ----

let private paramOrderMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    ParamOrder.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0023"
            (sprintf
                "'%s' takes its varying argument first; the fix swaps the definition to data-last order and rewrites every call site, so 'fun x -> %s x k' lambdas become the partial application '%s k'."
                s.FunctionName
                s.FunctionName
                s.FunctionName)
            s.DefRange
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("ParamOrder", "Reorder private function parameters data-last", HelpBase)>]
let paramOrderEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0023" "ParamOrder" (fun () ->
        whenChecked ctx (paramOrderMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ParamOrder", "Reorder private function parameters data-last", HelpBase)>]
let paramOrderCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0023" "ParamOrder" (fun () ->
        paramOrderMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0017 AsyncIgnore ----

let private discardedAsyncMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    if not (Configuration.isRuleEnabled fileName "FR0017" "AsyncIgnore") then
        []
    else
        AsyncIgnore.find parseTree source checkResults
        |> List.map (fun s ->
            hint
                "FR0017"
                (if s.IsValueTask then
                     sprintf
                         "'%s' returns a ValueTask: ignore drops its outcome - a failure is never observed, and a pooled ValueTask must be consumed exactly once. Await it (let! _ = / do! inside task { }) or call .AsTask() and hand the task to whoever waits."
                         s.Name
                 else
                     sprintf
                         "'%s' is an Async computation: ignore discards it without running it. Bind it inside the computation - let! _ = %s (do! when it returns unit) - or Async.Start it to fire and forget."
                         s.Name
                         s.Name)
                s.Range
                [])

// ---- FR0149 UnhandledStart ----

let private unhandledStartMessages
    (fileName: string)
    (offerMove: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    =
    if not (Configuration.isRuleEnabled fileName "FR0149" "AsyncIgnore") then
        []
    else
        AsyncIgnore.findUnhandledStart parseTree source checkResults
        |> List.map (fun s ->
            hint
                "FR0149"
                (sprintf
                    "%s hands this computation to the thread pool with nobody to observe a failure: an exception in it is UNHANDLED on a pool thread, which terminates the process rather than stopping the work quietly. %s Handle it in the body - a try/with, or Async.Catch bound and matched on both Choice1Of2 and Choice2Of2 (producing the Choice is not handling it).%s"
                    s.Starter
                    (if s.Starter = "Async.Start" then
                         "A try/with around this call catches nothing: the work never runs on this thread."
                     else
                         "Async.StartImmediate runs on this thread only until the first await; past it the pool has the failure and a try/with around this call can no longer reach it.")
                    ((if s.WrappedInTry then
                          (if s.TryFix.IsSome then
                               " The try/with around this call does not cover it either - that handler is on this thread, the work is not; it wraps this start and nothing else, so it moves inside the computation as it stands."
                           else
                               " The try/with around this call does not cover it either - that handler is on this thread, the work is not.")
                      else
                          "")
                     + (if s.LoopsInBody then
                            " The body loops, so where the handler goes decides the behaviour: around the whole computation it still stops on the first failure, INSIDE the loop it keeps running - which of the two is wanted is yours to choose, and why no fix is offered."
                        else
                            "")))
                s.Range
                // the one repair this rule can make: the author's own
                // handler, moved where it fires. Editor-offered — it
                // restructures the expression, and the handler then runs
                // on the pool thread rather than the calling one
                (match s.TryFix with
                 | Some(r, original, replacement) when offerMove -> [ fix r original replacement ]
                 | _ -> []))

[<EditorAnalyzer("AsyncIgnore", "Flag Async computations discarded with ignore", HelpBase)>]
let asyncIgnoreEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0017"; "FR0149" ] "AsyncIgnore" (fun () ->
        whenChecked ctx (fun check ->
            discardedAsyncMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText check
            @ unhandledStartMessages ctx.FileName true ctx.ParseFileResults.ParseTree ctx.SourceText check))

[<CliAnalyzer("AsyncIgnore", "Flag Async computations discarded with ignore", HelpBase)>]
let asyncIgnoreCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0017"; "FR0149" ] "AsyncIgnore" (fun () ->
        discardedAsyncMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        @ unhandledStartMessages ctx.FileName false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0018 DictTryAdd ----

let private dictTryAddMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    DictTryGet.findTryAdd parseTree source checkResults
    |> List.map (fun s ->
        let message =
            if s.Concurrent then
                "Check-then-add is a race on ConcurrentDictionary; use a single TryAdd."
            else
                "ContainsKey followed by an indexer add looks the key up twice; use a single TryAdd."

        hint "FR0018" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("DictTryAdd", "Replace check-then-add with TryAdd", HelpBase)>]
let dictTryAddEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0018" "DictTryAdd" (fun () ->
        whenChecked ctx (dictTryAddMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("DictTryAdd", "Replace check-then-add with TryAdd", HelpBase)>]
let dictTryAddCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0018" "DictTryAdd" (fun () ->
        dictTryAddMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0154 DictGetOrAdd ----

let private dictGetOrAddMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    DictTryGet.findGetOrAdd parseTree source checkResults
    |> List.map (fun s ->
        let factory = defaultArg s.Factory "..."
        let lazyShape = $"{s.Head} lazy ({factory})).Force()"

        if s.Deferred then
            hint
                "FR0154"
                $"A store after a TryGetValue miss leaves a window for another thread to store first, and two concurrent misses START two of the value and throw one away already running - which GetOrAdd alone does not change. A Lazy value - `{lazyShape}` on a ConcurrentDictionary<_, Lazy<_>> - starts it once and hands every caller the same one; remove the entry when it faults (FR0152)."
                s.Range
                []
        else
            let lazyHint =
                match s.Factory with
                | Some factory ->
                    $" If `{factory}` is costly, a Lazy value - `{lazyShape}` - runs it once across concurrent misses (FR0152 on removing a faulted one)."
                | None -> ""

            hint
                "FR0154"
                $"A store after a TryGetValue miss leaves a window for another thread to store first, after which two callers hold two different values for the key; GetOrAdd in the miss arm adds atomically, and the hit path keeps TryGetValue's speed.{lazyHint}"
                s.Range
                [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("DictGetOrAdd", "Replace TryGetValue-then-store on ConcurrentDictionary with GetOrAdd", HelpBase)>]
let dictGetOrAddEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0154" "DictGetOrAdd" (fun () ->
        whenChecked ctx (dictGetOrAddMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("DictGetOrAdd", "Replace TryGetValue-then-store on ConcurrentDictionary with GetOrAdd", HelpBase)>]
let dictGetOrAddCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0154" "DictGetOrAdd" (fun () ->
        dictGetOrAddMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0155 SealedClass ----

let private sealedClassMessages
    (scopeOpen: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (project: FSharpCheckProjectResults option)
    : Message list =
    widened scopeOpen (fun scope ->
        SealedClass.find scope parseTree source check project
        |> List.map (fun s ->
            let fixes =
                match s.Fix with
                | Some(r, text) -> [ fix r "" text ]
                | None -> []

            hint
                "FR0155"
                $"Class '%s{s.TypeName}' is inherited by nothing in this project and the project keeps %s{s.Reason}; [<Sealed>] lets the JIT drop the covariance check on every array store and make the type test one compare (measured 2x on both)."
                s.Range
                fixes))

[<EditorAnalyzer("SealedClass",
                 "Seal an internal class nothing inherits, where arrays or type tests pay for it",
                 HelpBase)>]
let sealedClassEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0155" "SealedClass" (fun () ->
        whenChecked ctx (fun check ->
            sealedClassMessages
                (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText
                check
                ctx.CheckProjectResults)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("SealedClass", "Seal an internal class nothing inherits, where arrays or type tests pay for it", HelpBase)>]
let sealedClassCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0155" "SealedClass" (fun () ->
        sealedClassMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults
            (Some ctx.CheckProjectResults))

// ---- FR0019 / FR0020 / FR0054 ObjectRules ----

let private objectRulesMessages (fileName: string) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    let equalsEnabled = Configuration.isRuleEnabled fileName "FR0019" "EqualsHashCode"
    let ctorEnabled = Configuration.isRuleEnabled fileName "FR0020" "CtorAbstractCall"

    let raiseEnabled =
        Configuration.isRuleEnabled fileName "FR0054" "RaiseInSpecialMember"

    if not (equalsEnabled || ctorEnabled || raiseEnabled) then
        []
    else
        let equalsSuggestions, ctorSuggestions, raiseSuggestions =
            ObjectRules.find parseTree source

        let equalsMessages =
            if equalsEnabled then
                equalsSuggestions
                |> List.map (fun s ->
                    hint
                        "FR0019"
                        (sprintf
                            "Type '%s' overrides Equals without overriding GetHashCode; hash-based collections will misbehave."
                            s.TypeName)
                        s.Range
                        [])
            else
                []

        let ctorMessages =
            if ctorEnabled then
                ctorSuggestions
                |> List.map (fun s ->
                    hint
                        "FR0020"
                        (sprintf
                            "Abstract member '%s' is used during construction; the override runs before the derived class is initialized."
                            s.MemberName)
                        s.Range
                        [])
            else
                []

        let raiseMessages =
            if raiseEnabled then
                raiseSuggestions
                |> List.map (fun s ->
                    hint
                        "FR0054"
                        (sprintf
                            "Raising from %s surprises its implicit callers (hash containers, debuggers, string formatting, finalization); return a defined value or restructure so the failure surfaces elsewhere."
                            s.MemberName)
                        s.Range
                        [])
            else
                []

        equalsMessages @ ctorMessages @ raiseMessages

[<EditorAnalyzer("ObjectRules",
                 "Equals/GetHashCode pairing, ctor-time abstract calls, raises in special members",
                 HelpBase)>]
let objectRulesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return DeepStack.run (fun () -> objectRulesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("ObjectRules", "Equals/GetHashCode pairing, ctor-time abstract calls, raises in special members", HelpBase)>]
let objectRulesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return DeepStack.run (fun () -> objectRulesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

// ---- FR0024 RaiseFailwith ----

let private raiseFailwithMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    RaiseFailwith.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0024"
            "raise with a plain Exception is exactly failwith; the raised type and message are unchanged."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("RaiseFailwith", "Rewrite raise (Exception msg) as failwith", HelpBase)>]
let raiseFailwithEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0024" "RaiseFailwith" (fun () ->
        raiseFailwithMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RaiseFailwith", "Rewrite raise (Exception msg) as failwith", HelpBase)>]
let raiseFailwithCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0024" "RaiseFailwith" (fun () ->
        raiseFailwithMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0025 OptionOfObj ----

let private optionOfObjMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    OptionOfObj.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0025"
            ($"This null test wraps the value into an option and can be written with %s{s.ModuleName}.ofObj.")
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("OptionOfObj", "Rewrite null-test-and-wrap as Option.ofObj", HelpBase)>]
let optionOfObjEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0025" "OptionOfObj" (fun () ->
        whenChecked ctx (optionOfObjMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("OptionOfObj", "Rewrite null-test-and-wrap as Option.ofObj", HelpBase)>]
let optionOfObjCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0025" "OptionOfObj" (fun () ->
        optionOfObjMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0026 AutoProperty ----

let private autoPropertyMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    AutoProperty.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0026"
            (sprintf
                "Property '%s' is a mutable backing field with trivial accessors; 'member val' says the same in one line."
                s.PropertyName)
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("AutoProperty", "Collapse trivial get/set with a backing field to member val", HelpBase)>]
let autoPropertyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0026" "AutoProperty" (fun () ->
        autoPropertyMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("AutoProperty", "Collapse trivial get/set with a backing field to member val", HelpBase)>]
let autoPropertyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0026" "AutoProperty" (fun () ->
        autoPropertyMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0027 ClosureCapture ----

let private closureCaptureMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    ClosureCapture.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            match s.Publisher with
            // AppDomain.CurrentDomain.*, Console.*: the publisher lives as
            // long as the process, so the object does too — the real leak
            | ClosureCapture.PublisherKind.ProcessWide ->
                $"This handler captures '{s.CapturedName}', and the {s.SinkName} subscription hangs it on a process-wide publisher: the whole object stays alive until the process exits, or until the handler is removed. Bind the needed values to locals before the lambda, or keep and dispose the subscription."
            // a publisher handed in from elsewhere: a leak only if it
            // outlives the subscriber
            | ClosureCapture.PublisherKind.External ->
                $"This handler captures '{s.CapturedName}', so the {s.SinkName} subscription keeps the whole object alive as long as the publisher lives - a leak when the publisher outlives it. If the object is large, bind the needed values to locals before the lambda, or keep and dispose the subscription."

        hint "FR0027" message s.Range [])

[<EditorAnalyzer("ClosureCapture", "Note this-capturing handlers given to event/observable sinks", HelpBase)>]
let closureCaptureEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0027" "ClosureCapture" (fun () ->
        whenChecked ctx (closureCaptureMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ClosureCapture", "Note this-capturing handlers given to event/observable sinks", HelpBase)>]
let closureCaptureCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0027" "ClosureCapture" (fun () ->
        closureCaptureMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0028 QueryInLoop ----

let private queryInLoopMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    QueryInLoop.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0028"
            (sprintf
                "'%s' is an IQueryable iterated inside another loop: each outer iteration executes a separate database query (N+1). Materialize it once before the loop, join both sources in a single query { }, or batch the keys (e.g. chunkBySize ~300 per query)."
                s.SourceText)
            s.Range
            [])

[<EditorAnalyzer("QueryInLoop", "Note IQueryable iteration nested in another loop (N+1)", HelpBase)>]
let queryInLoopEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0028" "QueryInLoop" (fun () ->
        whenChecked ctx (queryInLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("QueryInLoop", "Note IQueryable iteration nested in another loop (N+1)", HelpBase)>]
let queryInLoopCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0028" "QueryInLoop" (fun () ->
        queryInLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0029 TaskStateMachine ----

let private taskStateMachineMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults option)
    : Message list =
    // How long a non-awaiting tail must be before `runTail` is offered on a
    // task the compiler did NOT warn about. It invents a name for code whose
    // only sin was sitting after the last await, so on a healthy task it is
    // worth neither a fix nor a note: forty lines is a shape unwieldy enough
    // to stand on its own, where ten was a state-machine-size argument that
    // only FS3511 makes. A warned task drops to ten - there the cause is
    // established. Configurable per repository:
    //     { "FR0029": { "tailLines": 25 } }
    let tailLines =
        Configuration.parameterInt fileName "FR0029" "TaskStateMachine" "tailLines" 40

    // `async { }` has no resumable state machine, so none of the FS3511
    // advice applies to it; only the return hoist does, and its payoff there
    // is generated code size (~27% less IL on a twelve-arm branch), not
    // speed - measured identical on both time and allocation. Off by
    // default because that is a smaller claim than the rest of this rule
    // makes. Per repository:
    //     { "FR0029": { "hoistReturnOnAsync": true } }
    let hoistReturnOnAsync =
        Configuration.parameterBool fileName "FR0029" "TaskStateMachine" "hoistReturnOnAsync" false

    // the compiler's own verdict, read off the build the apply tool already
    // ran; empty in the IDE, where nothing compiled
    let dynamicFallbackLines = Configuration.dynamicFallbackLines fileName

    TaskStateMachine.find parseTree source check tailLines hoistReturnOnAsync dynamicFallbackLines
    |> List.map (fun s ->
        let message =
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistRecursiveFunction ->
                "A let rec inside task { } cannot be compiled into the static state machine (FS3511 at build time); move the recursive function out of the task."
            | TaskStateMachine.AdviceKind.HoistPlainLets count ->
                sprintf
                    "This task is large enough to risk the dynamic state-machine fallback (FS3511): %d plain let binding(s) before the first await can move out of the task (note: a throw in hoisted code then surfaces at the call instead of faulting the Task)."
                    count
            | TaskStateMachine.AdviceKind.SplitBranches ->
                "This task is large enough to risk the dynamic state-machine fallback (FS3511): each branch can become its own smaller task { } - a branch without awaits becomes a trivially static one."
            | TaskStateMachine.AdviceKind.HoistReturn leaves ->
                sprintf
                    "Every one of this branch's %d leaves returns, so one `return` in front of the whole branch hands the builder a value once instead of %d times - the branch becomes an ordinary expression rather than an exit per arm. Nothing moves: the branch stays where it is and gains an indent level."
                    leaves
                    leaves
            | TaskStateMachine.AdviceKind.ExtractTail lines ->
                sprintf
                    "This task is large enough to risk the dynamic state-machine fallback (FS3511): %d lines of non-awaiting code follow the last await and can extract into a plain function."
                    lines

        hint "FR0029" message s.Range (s.Edits |> List.map (fun (r, t) -> fix r (Text.textOfRange source r) t)))

[<EditorAnalyzer("TaskStateMachine", "Advice for shrinking oversized task expressions", HelpBase)>]
let taskStateMachineEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0029" "TaskStateMachine" (fun () ->
        taskStateMachineMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("TaskStateMachine", "Advice for shrinking oversized task expressions", HelpBase)>]
let taskStateMachineCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0029" "TaskStateMachine" (fun () ->
        taskStateMachineMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText (Some ctx.CheckFileResults))

// ---- FR0030 AddRange ----

let private addRangeMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    AddRange.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0030"
            "This loop only accumulates into a ResizeArray; a single AddRange call does the same (and pre-sizes when the source count is known)."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("AddRange", "Collapse accumulate-only loops to ResizeArray.AddRange", HelpBase)>]
let addRangeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0030" "AddRange" (fun () ->
        whenChecked ctx (addRangeMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("AddRange", "Collapse accumulate-only loops to ResizeArray.AddRange", HelpBase)>]
let addRangeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0030" "AddRange" (fun () ->
        addRangeMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)


// ---- FR0156 AccumulatorLoop ----

let private accumulatorLoopMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    // an accumulator drained as an array becomes an array expression only
    // on request: measured 1.6x the ResizeArray fill's time
    //     { "FR0156": { "arrays": true } }
    let arrays =
        Configuration.parameterBool fileName "FR0156" "AccumulatorLoop" "arrays" false

    // implicit yields arrived with F# 4.7; an older compiler wants them spelled
    //     { "FR0156": { "explicitYield": true } }
    let explicitYield =
        Configuration.parameterBool fileName "FR0156" "AccumulatorLoop" "explicitYield" false

    AccumulatorLoop.findWith arrays explicitYield parseTree source checkResults
    |> List.map (fun s ->
        let message =
            if s.Mutable then
                $"Mutable list '%s{s.Name}' is built one element at a time by its loops and only read after: the loops are a list expression with each element as its yield, built once - an append copied the whole list per element (measured at 1000 elements: 250x faster on 0.3%% of the allocation; a cons and List.rev 1.5x on half)."
            else
                $"ResizeArray '%s{s.Name}' is filled one Add at a time by its loops and only read after: the loops are a list expression, with each Add's argument as its yield."

        hint "FR0156" message s.Range (s.Edits |> List.map (fun e -> fix e.Range e.Original e.Replacement)))

[<EditorAnalyzer("AccumulatorLoop", "Turn an Add-by-Add ResizeArray fill into a list expression", HelpBase)>]
let accumulatorLoopEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0156" "AccumulatorLoop" (fun () ->
        whenChecked ctx (accumulatorLoopMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("AccumulatorLoop", "Turn an Add-by-Add ResizeArray fill into a list expression", HelpBase)>]
let accumulatorLoopCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0156" "AccumulatorLoop" (fun () ->
        accumulatorLoopMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)


// ---- FR0157 StringUnion ----

/// Every symbol use of the project, indexed once per project results (see
/// StringUnion.indexUses): a flow analysis asks for the uses of a dozen
/// locals, parameters and fields per candidate, and a walk of every file's
/// typed tree per question would be the whole sweep's cost. Public: the
/// apply tool's api pass adds the sibling projects' uses beside it.
let private projectUseIndexes =
    System.Runtime.CompilerServices.ConditionalWeakTable<FSharpCheckProjectResults, StringUnion.UseIndex>()

let projectUseIndex (project: FSharpCheckProjectResults) : StringUnion.UseIndex =
    projectUseIndexes.GetValue(
        project,
        fun p ->
            StringUnion.indexUses (
                try
                    p.GetAllUsesOfAllSymbols()
                with _ -> // no uses known: every candidate stands down; fsharpanalyzer: ignore-line FR0055
                    [||]
            )
    )

/// The type names a compilation declares, nested ones included: one walk
/// into a list, where a `seq { yield! }` per level allocated an enumerator
/// per nesting and made every name pay the depth.
let private entityNames (entities: FSharpEntity seq) : string list =
    let rec walk (found: string list) (level: FSharpEntity seq) =
        level
        |> Seq.fold (fun found (e: FSharpEntity) -> walk (e.DisplayName :: found) e.NestedEntities) found

    walk [] entities |> List.rev

/// The world a rule sees from one file: the project's uses where the host
/// has project results, this file's alone where it has not.
let private stringUnionWorld
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (project: FSharpCheckProjectResults option)
    (options: AnalyzerProjectOptions)
    (scopeOpen: bool)
    : StringUnion.World =
    let sameFile (a: string) (b: string) =
        String.Equals(IO.Path.GetFullPath a, IO.Path.GetFullPath b, StringComparison.OrdinalIgnoreCase)

    // the project's use index is built on the first question, never for a
    // file that asks none: it is the whole compilation's symbol uses
    let indexes =
        lazy
            (match project with
             | Some p -> [ projectUseIndex p ]
             | None -> [])

    {
        UsesOf =
            (fun symbol ->
                match project with
                | Some _ -> StringUnion.usesIn indexes.Value symbol
                | None -> check.GetUsesOfSymbolInFile symbol)
        File =
            (fun path ->
                if sameFile path fileName then
                    Some(parseTree, source)
                else
                    ProjectSources.tryParse path)
        SymbolAt =
            (fun file id ->
                if sameFile file fileName then
                    let r = id.idRange
                    let lineText = source.GetLineString(r.EndLine - 1)
                    OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ])
                else
                    StringUnion.symbolIn indexes.Value file id)
        FileOrder =
            (fun path ->
                options.SourceFiles
                |> Seq.tryFindIndex (fun f -> sameFile f path)
                |> Option.defaultValue Int32.MaxValue)
        ScopeOpen = scopeOpen
        TypeNames =
            try
                match project with
                | Some p -> entityNames p.AssemblySignature.Entities |> Set.ofSeq
                | None -> entityNames check.PartialAssemblySignature.Entities |> Set.ofSeq
            with _ -> // fsharpanalyzer: ignore-line FR0055
                Set.empty
        InternalsVisible =
            match project with
            | Some p -> ProjectSources.hasInternalsVisibleTo p
            | None -> true
        SourceFiles = List.ofSeq options.SourceFiles
    }

/// The world the apply tool's api pass builds, with the sibling projects'
/// uses and files beside the project's own: every call site of an exported
/// function is then in sight, and its literals can prove the set closed.
let stringUnionApiWorld
    (project: FSharpCheckProjectResults)
    (sourceFiles: string[])
    (siblingUses: FSharpSymbolUse seq)
    (fileLookup: string -> (ParsedInput * ISourceText) option)
    (publicRead: bool)
    (internalsVisible: bool)
    : StringUnion.World =
    let sameFile (a: string) (b: string) =
        String.Equals(IO.Path.GetFullPath a, IO.Path.GetFullPath b, StringComparison.OrdinalIgnoreCase)

    let indexes = lazy [ projectUseIndex project; StringUnion.indexUses siblingUses ]

    {
        UsesOf = (fun symbol -> StringUnion.usesIn indexes.Value symbol)
        File = fileLookup
        SymbolAt = (fun file id -> StringUnion.symbolIn indexes.Value file id)
        // a sibling's files come after every file of the project: the union
        // belongs beside the project's declaration, never in a caller
        FileOrder =
            (fun path ->
                sourceFiles
                |> Array.tryFindIndex (fun f -> sameFile f path)
                |> Option.defaultValue Int32.MaxValue)
        ScopeOpen = publicRead
        TypeNames =
            try
                entityNames project.AssemblySignature.Entities |> Set.ofSeq
            with _ -> // fsharpanalyzer: ignore-line FR0055
                Set.empty
        InternalsVisible = internalsVisible
        SourceFiles = List.ofArray sourceFiles
    }

/// The FR0157 messages for a file, from a world the host built. A rewrite
/// that retypes a record field carries its fixes only where
/// `offerFieldSlots` (the editor): the record's `%A` text and structural
/// order change with the field, which no scan fully rules out, so a sweep
/// reports it without a fix.
let stringUnionMessagesIn
    (offerFieldSlots: bool)
    (world: StringUnion.World)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    // the cheap syntactic question first: most files hold no match on two
    // string literals, and the world's index is not built for them
    (if StringUnion.hasCandidates parseTree then
         StringUnion.find world parseTree source
     else
         [])
    |> List.map (fun s ->
        let cases = s.Literals |> List.map (fun l -> $"\"{l}\"") |> String.concat ", "

        let shadowed =
            match s.ShadowedConstants with
            | [] -> ""
            | names ->
                let list = names |> List.map (fun n -> $"'{n}'") |> String.concat ", "

                $" The arm(s) {list} bind a fresh variable and match every value, not the constant of that name; the case is the comparison they read as."

        let files =
            s.Edits |> List.map (fun e -> e.Range.FileName) |> List.distinct |> List.length

        let crossFile = if files > 1 then $" ({files} files)" else ""

        let withheld = s.FieldSlot && not offerFieldSlots

        let fieldNote =
            if withheld then
                " A record field changes type, and with it the record's printed text and sort order: the editor offers the rewrite, a sweep does not apply it."
            else
                ""

        hint
            "FR0157"
            $"This value can only ever be one of {cases}: a union '{s.Name}' with a case for each, and a ToString returning the original text, names them and makes the match exhaustive{crossFile}.{shadowed}{fieldNote}"
            s.Range
            (if withheld then
                 []
             else
                 s.Edits |> List.map (fun e -> fix e.Range e.Original e.Replacement)))


[<EditorAnalyzer("StringUnion", "Turn a closed set of matched string literals into a union", HelpBase)>]
let stringUnionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0157" "StringUnion" (fun () ->
        whenChecked ctx (fun check ->
            let world =
                stringUnionWorld
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    check
                    None
                    ctx.ProjectOptions
                    (leafScopeOpen ctx.FileName ctx.ProjectOptions)

            stringUnionMessagesIn true world ctx.ParseFileResults.ParseTree ctx.SourceText
            // the editor applies a fix to the file in the buffer: a
            // rewrite that reaches another file is reported without it
            |> List.map (fun m ->
                if m.Fixes |> List.exists (fun f -> f.FromRange.FileName <> ctx.FileName) then
                    { m with Fixes = [] }
                else
                    m))
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("StringUnion", "Turn a closed set of matched string literals into a union", HelpBase)>]
let stringUnionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0157" "StringUnion" (fun () ->
        // under --api-changes the apply tool's api pass runs the rule with the
        // sibling projects' call sites in sight, which this pass has not got:
        // its findings would be the same set minus the exported ones. The raw
        // flag, not apiChangesAllowed: a held public surface closes the
        // latter, and the api pass still owns the rule on such a run
        if (Scope.scope ()).ApiChanges then
            []
        else

            let world =
                stringUnionWorld
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    ctx.CheckFileResults
                    (Some ctx.CheckProjectResults)
                    ctx.ProjectOptions
                    (leafScopeOpen ctx.FileName ctx.ProjectOptions)

            stringUnionMessagesIn false world ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0158 IndexScan ----

let private indexScanMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    IndexScan.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0158"
            $"This while loop only walks '%s{s.Name}' while the condition holds: a tail-recursive local function returns the index it stops at, and '%s{s.Name}' needs no mutable (measured level with the loop)."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("IndexScan", "Turn a while loop that walks an index into a tail-recursive function", HelpBase)>]
let indexScanEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0158" "IndexScan" (fun () ->
        whenChecked ctx (indexScanMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("IndexScan", "Turn a while loop that walks an index into a tail-recursive function", HelpBase)>]
let indexScanCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0158" "IndexScan" (fun () ->
        indexScanMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0031 StringConcat ----

let private stringConcatMessages
    (offerAlternatives: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    StringConcat.find parseTree source checkResults
    |> List.collect (fun s ->
        let primary =
            hint
                "FR0031"
                "This string concatenation chain can be an interpolated string."
                s.Range
                [ fix s.Range s.OriginalText s.ReplacementText ]

        match s.ConcatAlternative with
        | Some concat when offerAlternatives ->
            [
                primary
                hint
                    "FR0031"
                    "...or as one explicit String.Concat call - the same thing the compiler emits for the interpolation, spelled out."
                    s.Range
                    [ fix s.Range s.OriginalText concat ]
            ]
        | _ -> [ primary ])

[<EditorAnalyzer("StringConcat", "Rewrite string + chains as interpolated strings", HelpBase)>]
let stringConcatEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0031" "StringConcat" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            whenChecked ctx (stringConcatMessages true ctx.ParseFileResults.ParseTree ctx.SourceText)
        else
            [])

[<CliAnalyzer("StringConcat", "Rewrite string + chains as interpolated strings", HelpBase)>]
let stringConcatCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0031" "StringConcat" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            stringConcatMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        else
            [])

// ---- FR0032 / FR0033 ObjectDesign ----

let private objectDesignMessages
    (scopeOpen: bool)
    (fileName: string)
    (offerFixes: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    let disposableEnabled =
        Configuration.isRuleEnabled fileName "FR0032" "DisposableField"

    let staticEnabled = Configuration.isRuleEnabled fileName "FR0033" "StaticMember"

    let undisposedEnabled =
        Configuration.isRuleEnabled fileName "FR0047" "UndisposedField"

    let disposeWithoutInterfaceEnabled =
        Configuration.isRuleEnabled fileName "FR0148" "DisposeWithoutInterface"

    let disposeWithoutInterfaceMessages =
        if disposeWithoutInterfaceEnabled then
            ObjectDesign.disposeWithoutInterface parseTree source checkResults
            |> List.map (fun s ->
                hint
                    "FR0148"
                    (sprintf
                        "Type '%s' exposes a public Dispose() but does not implement IDisposable; nothing can `use` it, and only a caller that knows the member releases what it holds - implement IDisposable and let Dispose be its member."
                        s.TypeName)
                    s.Range
                    [])
        else
            []

    if not (disposableEnabled || staticEnabled || undisposedEnabled) then
        disposeWithoutInterfaceMessages
    else
        let disposables, statics, undisposedFields =
            ObjectDesign.find scopeOpen parseTree source checkResults

        let disposableMessages =
            if disposableEnabled then
                disposables
                |> List.map (fun s ->
                    // the editor's fix rides on the type's first leaked
                    // field: one IDisposable disposing them all — the plain
                    // form, no Dispose(bool) ceremony
                    hint
                        "FR0032"
                        (match s.DisposableBase with
                         | Some baseName ->
                             sprintf
                                 "Type '%s' creates disposable '%s' that its disposable base '%s' never sees; override Dispose(disposing) (or re-implement IDisposable over the base's) and dispose '%s' there."
                                 s.TypeName
                                 s.FieldName
                                 baseName
                                 s.FieldName
                         | None ->
                             sprintf
                                 "Type '%s' creates disposable '%s' but does not implement IDisposable; the resource has no owner to dispose it."
                                 s.TypeName
                                 s.FieldName)
                        s.Range
                        (match s.Fix with
                         | Some(r, original, replacement) when offerFixes -> [ fix r original replacement ]
                         | _ -> []))
            else
                []

        let staticMessages =
            if staticEnabled then
                statics
                |> List.map (fun s ->
                    hint
                        "FR0033"
                        (sprintf
                            "Member '%s' uses no instance state and can be a static member (call sites change from instance to type)."
                            s.MemberName)
                        s.Range
                        [])
            else
                []

        let undisposedMessages =
            if undisposedEnabled then
                undisposedFields
                |> List.map (fun s ->
                    hint
                        "FR0047"
                        (if s.MentionedOnly then
                             sprintf
                                 "Type '%s' is IDisposable and its Dispose uses field '%s' without disposing it - cancelling or closing a handle is not releasing it; add '%s.Dispose()'."
                                 s.TypeName
                                 s.FieldName
                                 s.FieldName
                         else
                             sprintf
                                 "Type '%s' is IDisposable but its Dispose never touches disposable field '%s'; the resource leaks despite the pattern."
                                 s.TypeName
                                 s.FieldName)
                        s.Range
                        (match s.Fix with
                         | Some(r, original, replacement) when offerFixes -> [ fix r original replacement ]
                         | _ -> []))
            else
                []

        disposableMessages
        @ staticMessages
        @ undisposedMessages
        @ disposeWithoutInterfaceMessages

[<EditorAnalyzer("ObjectDesign", "Disposable fields without IDisposable; could-be-static members", HelpBase)>]
let objectDesignEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                whenChecked
                    ctx
                    (objectDesignMessages
                        (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                        ctx.FileName
                        true
                        ctx.ParseFileResults.ParseTree
                        ctx.SourceText))
    }

[<CliAnalyzer("ObjectDesign", "Disposable fields without IDisposable; could-be-static members", HelpBase)>]
let objectDesignCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                objectDesignMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    ctx.FileName
                    false
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    ctx.CheckFileResults)
    }

// ---- FR0034 OptionMatch ----

let private optionMatchMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    OptionMatch.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0034"
            "IsSome test plus .Value access can be a pattern match; .Value throws when the option is empty, the match cannot."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("OptionMatch", "Rewrite IsSome/.Value conditionals as pattern matches", HelpBase)>]
let optionMatchEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0034" "OptionMatch" (fun () ->
        whenChecked ctx (optionMatchMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("OptionMatch", "Rewrite IsSome/.Value conditionals as pattern matches", HelpBase)>]
let optionMatchCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0034" "OptionMatch" (fun () ->
        optionMatchMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0035 / FR0037 LoopPerf ----

let private loopPerfMessages
    (scopeOpen: bool)
    (seenByLaterFile: string -> bool)
    (check: FSharpCheckFileResults option)
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    let containsEnabled = Configuration.isRuleEnabled fileName "FR0035" "ContainsInLoop"

    let constructionEnabled =
        Configuration.isRuleEnabled fileName "FR0037" "ConstructionInLoop"

    if not (containsEnabled || constructionEnabled) then
        []
    else
        let contains, constructions =
            LoopPerf.findWith seenByLaterFile scopeOpen check parseTree source

        let containsMessages =
            if containsEnabled then
                contains
                |> List.map (fun s ->
                    if not s.Fix.IsEmpty then
                        hint
                            "FR0035"
                            (sprintf
                                "%s.contains scans '%s' linearly on every iteration; '%s' is a startup-built module binding, so the fix adds a private HashSet companion beside it (built once) and probes that in O(1) - every probe of it in this file converts together."
                                s.ModuleName
                                s.CollectionName
                                s.CollectionName)
                            s.Range
                            (s.Fix |> List.map (fun (r, original, replacement) -> fix r original replacement))
                    else
                        hint
                            "FR0035"
                            (sprintf
                                "%s.contains scans '%s' linearly on every iteration. If the loop is long and '%s' is more than a handful of elements, build a HashSet from it once outside the loop for O(1) probes - the one-time build only pays for itself then; for a few elements the linear scan is already the fastest option, and F# Set's persistent tree costs more to build and probe than HashSet unless you need its immutability."
                                s.ModuleName
                                s.CollectionName
                                s.CollectionName)
                            s.Range
                            [])
            else
                []

        let constructionMessages =
            if constructionEnabled then
                // a Regex construction FR0015 can hoist (literal pattern,
                // constant options, a free name, the open in place) gets
                // its FIX there; a note here on the same range would only
                // repeat the finding. Wherever FR0015 declines - or is off
                // - the construction still deserves the note
                let hoistedByRegexUsage =
                    if
                        constructions |> List.exists (fun s -> s.TypeName = "Regex")
                        && Configuration.isRuleEnabled fileName "FR0015" "RegexUsage"
                    then
                        RegexUsage.hoistedConstructions (regexPerCallHoist fileName) parseTree source
                    else
                        []

                // a test building a client per case is not the lifetime
                // question (CR0110 stands down the same way)
                let inTestFile = lazy (AstIndex.isTestFile (AstIndex.ofTree parseTree) source)

                constructions
                |> List.filter (fun s -> not (hoistedByRegexUsage |> List.exists (Range.equals s.Range)))
                |> List.filter (fun s -> not (s.TypeName = "HttpClient" && inTestFile.Value))
                |> List.map (fun s ->
                    let message =
                        if s.TypeName = "HttpClient" then
                            // not merely expensive: each instance owns a
                            // socket pool, and per-iteration construction
                            // exhausts ports under load (TIME_WAIT). The
                            // right lifetime is framework-dependent (a
                            // long-lived instance, or IHttpClientFactory
                            // under DI), so this stays advice
                            "An HttpClient is constructed on every iteration - under load this exhausts sockets (TIME_WAIT) and skips DNS refresh. Reuse one long-lived client (it is thread-safe for concurrent requests) or take an IHttpClientFactory."
                        else
                            sprintf
                                "A %s is constructed on every iteration; it is expensive by design - hoist it outside the loop or make it static."
                                s.TypeName

                    hint "FR0037" message s.Range [])
            else
                []

        containsMessages @ constructionMessages

[<EditorAnalyzer("LoopPerf", "Linear probes and expensive constructions inside loops", HelpBase)>]
let loopPerfEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                loopPerfMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    (seenByLaterFile ctx.FileName ctx.ProjectOptions)
                    ctx.CheckFileResults
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText)
    }

[<CliAnalyzer("LoopPerf", "Linear probes and expensive constructions inside loops", HelpBase)>]
let loopPerfCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                loopPerfMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    (seenByLaterFile ctx.FileName ctx.ProjectOptions)
                    (Some ctx.CheckFileResults)
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText)
    }

// ---- FR0036 TypeChecks ----

let private typeChecksMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    TypeChecks.find parseTree source
    |> List.map (fun s ->
        let message =
            match s.Kind with
            | TypeChecks.TypeCheckKind.NameComparison prop ->
                sprintf
                    "Comparing GetType().%s to a string breaks silently on renames and namespaces; compare types instead (a ':?' type test or typeof<_> equality)."
                    prop
            | TypeChecks.TypeCheckKind.TypeofEquality(receiver, typeName) ->
                sprintf
                    "GetType() = typeof<%s> is exact-type equality; if matching subtypes is fine (it usually is), '%s :? %s' says it directly."
                    typeName
                    receiver
                    typeName

        hint "FR0036" message s.Range [])

[<EditorAnalyzer("TypeChecks", "Fragile runtime type comparisons", HelpBase)>]
let typeChecksEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0036" "TypeChecks" (fun () ->
        typeChecksMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("TypeChecks", "Fragile runtime type comparisons", HelpBase)>]
let typeChecksCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0036" "TypeChecks" (fun () ->
        typeChecksMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0038 CharOverload ----

let private charOverloadMessages
    (offerOrdinal: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    CharOverload.find parseTree source checkResults
    |> List.map (fun s ->
        match s.ReplacementText with
        | Some replacement ->
            // a capability fix: on a dual-framework run this may emit an
            // #if NET6_0_OR_GREATER / #else pair (char overloads are
            // net-core-era; net4x siblings compile the #else). Where no
            // guard can be emitted the advice says why the fix is withheld
            // — the narrowest framework has no such overload
            if CapabilityFix.guardUnavailable () then
                hint
                    "FR0038"
                    (sprintf
                        "%s has a char overload for a single character on the newer frameworks this project targets; it skips the string-comparison setup, but the narrowest target lacks it.%s"
                        s.MethodName
                        (match s.PortableOffer with
                         | Some _ ->
                             " The portable form compiles everywhere: IndexOf takes a char on every framework and is ordinal, as Contains(string) already is."
                         | None -> " The rewrite needs an #if guard of your own."))
                    s.Range
                    // the portable rewrite restates the call, so it is the
                    // author's to take in the editor — a sweep does not
                    // reshape working code for a portability nicety
                    (match s.PortableOffer with
                     | Some(r, original, replacement) when offerOrdinal -> [ fix r original replacement ]
                     | _ -> [])
            else
                hint
                    "FR0038"
                    (sprintf
                        "%s has a char overload for a single character; it skips the string-comparison setup."
                        s.MethodName)
                    s.Range
                    [ CapabilityFix.make source s.Range s.OriginalText replacement ]
        | None ->
            // the editor offers the ordinal char overload as a one-click
            // choice — taking it IS the author's decision that ordinal
            // was meant; a sweep never decides that
            hint
                "FR0038"
                (sprintf
                    "%s with a single-character string has a faster char overload - but the char overload compares ordinally while the string overload is culture-sensitive; switch (or add StringComparison.Ordinal) only if ordinal is intended."
                    s.MethodName)
                s.Range
                (match s.OrdinalOffer with
                 | Some(r, original, replacement) when offerOrdinal -> [ fix r original replacement ]
                 | _ -> []))

[<EditorAnalyzer("CharOverload", "Use char overloads for single-character strings", HelpBase)>]
let charOverloadEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0038" "CharOverload" (fun () ->
        whenChecked ctx (charOverloadMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("CharOverload", "Use char overloads for single-character strings", HelpBase)>]
let charOverloadCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0038" "CharOverload" (fun () ->
        charOverloadMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0039 CaseInsensitive ----

let private caseInsensitiveMessages
    (offerAlternatives: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    CaseInsensitive.find parseTree source checkResults
    |> List.collect (fun s ->
        let message =
            match s.Kind with
            | CaseInsensitive.CaseKind.Equality when s.Replacement.IsSome ->
                sprintf
                    "%s() allocates a copy just to compare with an ASCII literal; String.Equals(..., OrdinalIgnoreCase) is allocation-free and agrees with it on every input except two Unicode compatibility characters (KELVIN SIGN, LONG S)."
                    s.LoweringName
            | CaseInsensitive.CaseKind.Equality ->
                sprintf
                    "%s() allocates a copy just to compare; String.Equals(a, b, StringComparison...IgnoreCase) is allocation-free - pick the comparison type deliberately (Ordinal vs Culture)."
                    s.LoweringName
            | CaseInsensitive.CaseKind.MethodCall method when s.Replacement.IsSome ->
                sprintf
                    "%s() allocates a copy just to call %s with an ASCII literal; %s(..., OrdinalIgnoreCase) is allocation-free and agrees with it on every input except two Unicode compatibility characters (KELVIN SIGN, LONG S)."
                    s.LoweringName
                    method
                    method
            | CaseInsensitive.CaseKind.MethodCall method ->
                sprintf
                    "%s() allocates a copy just to call %s; the %s overload taking a StringComparison is allocation-free - pick the comparison type deliberately (Ordinal vs Culture)."
                    s.LoweringName
                    method
                    method

        // a capability fix like FR0038's: the StringComparison overloads of
        // Contains/StartsWith/EndsWith arrived in netstandard2.1, so on a
        // multi-targeted project this pairs with the project's own guard
        // rather than breaking the frameworks that lack them. SQLProvider
        // took `Contains("UNSIGNED", StringComparison.OrdinalIgnoreCase)`
        // into shared code and stopped compiling for netstandard2.0.
        let fixes =
            match s.Replacement with
            | Some _ when CapabilityFix.guardUnavailable () -> []
            | Some replacement ->
                [
                    CapabilityFix.make source s.Range (Text.textOfRange source s.Range) replacement
                ]
            | None -> []

        let primary = hint "FR0039" message s.Range fixes

        // ALTERNATIVE spellings ride as separate messages so an editor
        // offers each as its own code action; the CLI never sees them and
        // auto-applies only the primary
        match s.CultureReplacement with
        | Some culture when offerAlternatives && s.Replacement.IsSome ->
            [
                primary
                hint
                    "FR0039"
                    "...or culture-aware: InvariantCultureIgnoreCase compares by linguistic rules (ligatures, accents) where ordinal compares code points."
                    s.Range
                    [ fix s.Range (Text.textOfRange source s.Range) culture ]
            ]
        | _ -> [ primary ])

[<EditorAnalyzer("CaseInsensitive", "Allocation-free case-insensitive comparisons", HelpBase)>]
let caseInsensitiveEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0039" "CaseInsensitive" (fun () ->
        whenChecked ctx (caseInsensitiveMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("CaseInsensitive", "Allocation-free case-insensitive comparisons", HelpBase)>]
let caseInsensitiveCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0039" "CaseInsensitive" (fun () ->
        caseInsensitiveMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0040 RedundantGuard ----

let private redundantGuardMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    RedundantGuard.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0040"
            (sprintf
                "%s already handles the miss (it returns false); the %s guard just doubles the lookup."
                s.ActionName
                s.GuardName)
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("RedundantGuard", "Drop membership guards before miss-tolerant Remove/Add", HelpBase)>]
let redundantGuardEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0040" "RedundantGuard" (fun () ->
        whenChecked ctx (redundantGuardMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("RedundantGuard", "Drop membership guards before miss-tolerant Remove/Add", HelpBase)>]
let redundantGuardCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0040" "RedundantGuard" (fun () ->
        redundantGuardMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0041 VectorizedLinq ----

let private vectorizedLinqMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    VectorizedLinq.find parseTree source checkResults
    |> List.map (fun s ->
        let message =
            if s.FunctionName = "contains" then
                $"{s.ModuleName}.contains over an array is a scalar loop; on .NET 8+ System.Linq's Contains() is SIMD-vectorized for '{s.ArrayName}''s element type (measured ~5x at 1000 elements, ~6x at 100k), with the same answers and the same ArgumentNullException on a null array."
            else
                sprintf
                    "%s.%s over an array is a scalar loop; on .NET 8+ System.Linq's %s%s() is SIMD-vectorized for '%s''s element type (note: LINQ Sum throws on overflow where F#'s sum wraps)."
                    s.ModuleName
                    s.FunctionName
                    (string (Char.ToUpperInvariant s.FunctionName.[0]))
                    (s.FunctionName.Substring 1)
                    s.ArrayName

        // Array.contains is exact as Enumerable.Contains; the aggregations
        // (overflow, empty) stay notes
        let fixes =
            match s.ReplacementText with
            | Some replacement -> [ fix s.Range (Text.textOfRange source s.Range) replacement ]
            | None -> []

        hint "FR0041" message s.Range fixes)

[<EditorAnalyzer("VectorizedLinq", "SIMD-vectorized LINQ aggregations for primitive arrays", HelpBase)>]
let vectorizedLinqEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0041" "VectorizedLinq" (fun () ->
        // LINQ's SIMD path is a .NET runtime matter; a Fable target compiles to
        // JS/Python/Dart/Rust where the advice does not apply
        if referencesAssembly "Fable.Core" ctx.ProjectOptions then
            []
        else
            whenChecked ctx (vectorizedLinqMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("VectorizedLinq", "SIMD-vectorized LINQ aggregations for primitive arrays", HelpBase)>]
let vectorizedLinqCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0041" "VectorizedLinq" (fun () ->
        if referencesAssembly "Fable.Core" ctx.ProjectOptions then
            []
        else
            vectorizedLinqMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0042 SprintfInterpolation ----

let private sprintfInterpolationMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    SprintfInterpolation.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0042"
            "This sprintf can be a typed interpolated string; the specifiers stay, so the output is identical and the arguments read in place."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("SprintfInterpolation", "Rewrite fully applied sprintf as typed interpolation", HelpBase)>]
let sprintfInterpolationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0042" "SprintfInterpolation" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            whenChecked ctx (sprintfInterpolationMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
        else
            [])

[<CliAnalyzer("SprintfInterpolation", "Rewrite fully applied sprintf as typed interpolation", HelpBase)>]
let sprintfInterpolationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0042" "SprintfInterpolation" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            sprintfInterpolationMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        else
            [])

// ---- FR0043 TypedHoles ----

let private typedHolesMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    TypedHoles.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0043"
            (sprintf
                "This string already uses typed holes; '%s{%s}' pins the type at compile time with identical output."
                s.Specifier
                s.FillText)
            s.Range
            [ fix s.Range "" s.Specifier ])

[<EditorAnalyzer("TypedHoles", "Type the remaining holes of already-typed interpolations", HelpBase)>]
let typedHolesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0043" "TypedHoles" (fun () ->
        whenChecked ctx (typedHolesMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("TypedHoles", "Type the remaining holes of already-typed interpolations", HelpBase)>]
let typedHolesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0043" "TypedHoles" (fun () ->
        typedHolesMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0044 Reraise ----

let private reraiseMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    Reraise.find parseTree source checkResults
    |> List.map (fun s ->
        match s.Removal with
        | Some(r, original, replacement) ->
            hint
                "FR0044"
                (sprintf
                    "raise %s resets the exception's stack trace, and reraise () is not allowed inside a computation expression; this handler only rethrows, so the try/with goes and an unmatched exception propagates with its trace intact."
                    s.ExceptionName)
                s.Range
                [ fix r original replacement ]
        | None ->
            hint
                "FR0044"
                (sprintf
                    "raise %s resets the exception's stack trace; reraise () rethrows it with the original trace intact."
                    s.ExceptionName)
                s.Range
                [ fix s.Range s.OriginalText "reraise ()" ])

[<EditorAnalyzer("Reraise", "Rethrow with reraise () to preserve the stack trace", HelpBase)>]
let reraiseEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0044" "Reraise" (fun () ->
        whenChecked ctx (reraiseMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("Reraise", "Rethrow with reraise () to preserve the stack trace", HelpBase)>]
let reraiseCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0044" "Reraise" (fun () ->
        reraiseMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0045 NaNComparison ----

let private nanComparisonMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    NaNComparison.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0045"
            "Equality against NaN never holds (IEEE 754: NaN is unequal to everything); IsNaN performs the test this comparison meant."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("NaNComparison", "Test NaN with IsNaN, not equality", HelpBase)>]
let nanComparisonEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0045" "NaNComparison" (fun () ->
        whenChecked ctx (nanComparisonMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("NaNComparison", "Test NaN with IsNaN, not equality", HelpBase)>]
let nanComparisonCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0045" "NaNComparison" (fun () ->
        nanComparisonMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0046 WeakLock ----

let private weakLockMessages
    (offerLockObject: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    WeakLock.find parseTree source checkResults
    |> List.map (fun s ->
        let shared =
            match s.Kind with
            | WeakLock.WeakKind.StringValue -> "interned strings are shared process-wide"
            | WeakLock.WeakKind.TypeObject -> "runtime Type objects are shared process-wide"
            | WeakLock.WeakKind.SelfObject -> "every holder of the reference can take the same monitor"
            | WeakLock.WeakKind.SharedSingleton name -> $"{name} belongs to the whole process"

        // the lock object is a structural decision — the editor offers it,
        // a sweep only notes
        let fixes =
            if offerLockObject then
                s.Fix |> List.map (fun (r, original, replacement) -> fix r original replacement)
            else
                []

        hint
            "FR0046"
            (sprintf
                "Locking on %s synchronizes with any code locking the same value (%s); use a dedicated private lock object (let lockObj = obj ())."
                s.TargetText
                shared)
            s.Range
            fixes)

[<EditorAnalyzer("WeakLock", "Do not lock on strings, Type objects, this or shared singletons", HelpBase)>]
let weakLockEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0046" "WeakLock" (fun () ->
        whenChecked ctx (weakLockMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("WeakLock", "Do not lock on strings, Type objects, this or shared singletons", HelpBase)>]
let weakLockCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0046" "WeakLock" (fun () ->
        weakLockMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0048 FormatArgs ----

let private formatArgsMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    FormatArgs.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0048"
            (sprintf
                "The format string references {%d} but only %d argument(s) are supplied; this throws FormatException at runtime (sprintf or interpolation would catch it at compile time)."
                s.MissingIndex
                s.ArgCount)
            s.Range
            [])

[<EditorAnalyzer("FormatArgs", "String.Format placeholders must have arguments", HelpBase)>]
let formatArgsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0048" "FormatArgs" (fun () ->
        formatArgsMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("FormatArgs", "String.Format placeholders must have arguments", HelpBase)>]
let formatArgsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0048" "FormatArgs" (fun () ->
        formatArgsMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0049 SyncOverAsync ----

let private syncOverAsyncMessages
    (parseTree: ParsedInput)
    (source: ISourceText)
    (fileName: string)
    (offerSyncSwap: bool)
    (taskAvailable: bool)
    checkResults
    : Message list =
    SyncOverAsync.findWith taskAvailable parseTree source checkResults
    |> List.collect (fun s ->
        let message =
            match s.Kind, s.Builder with
            | SyncOverAsync.BlockKind.AntecedentResult, _ ->
                ".Result on a continuation's antecedent does not block, but a faulted antecedent throws its exception wrapped in an AggregateException there; the continuation is a bind - task { let! r = t ... } gets the value, the exception itself, and no ContinueWith."
            | kind, None ->
                let what =
                    match kind with
                    | SyncOverAsync.BlockKind.TaskResult -> ".Result"
                    | SyncOverAsync.BlockKind.TaskWait -> ".Wait()"
                    | SyncOverAsync.BlockKind.AwaiterGetResult -> "GetAwaiter().GetResult()"
                    | SyncOverAsync.BlockKind.RunSynchronously -> "Async.RunSynchronously"
                    | SyncOverAsync.BlockKind.ThreadSleep -> "Thread.Sleep"
                    | SyncOverAsync.BlockKind.PrimitiveWait name -> name
                    | SyncOverAsync.BlockKind.AntecedentResult -> ".Result"

                sprintf
                    "%s is sync-over-async: either make this code async (wrap it in task { } and let!/do!) or call the synchronous API version."
                    what
            | kind, Some builder ->
                let what =
                    match kind with
                    | SyncOverAsync.BlockKind.TaskResult -> ".Result blocks the thread"
                    | SyncOverAsync.BlockKind.TaskWait -> ".Wait() blocks the thread"
                    | SyncOverAsync.BlockKind.AwaiterGetResult -> "GetAwaiter().GetResult() blocks the thread"
                    | SyncOverAsync.BlockKind.RunSynchronously -> "Async.RunSynchronously blocks the thread"
                    | SyncOverAsync.BlockKind.ThreadSleep -> "Thread.Sleep blocks the thread"
                    | SyncOverAsync.BlockKind.PrimitiveWait name -> $"{name} blocks the thread"
                    | SyncOverAsync.BlockKind.AntecedentResult -> ".Result"

                match s.Kind with
                | SyncOverAsync.BlockKind.PrimitiveWait _ ->
                    // no task to bind: the work the primitive signals is
                    // what the computation should await
                    sprintf
                        "%s inside %s { }; await the work it waits for instead (the task or a TaskCompletionSource that completes it, SemaphoreSlim.WaitAsync) - sync-over-async in a computation expression invites thread-pool starvation and deadlocks."
                        what
                        builder
                | _ when s.InFinally ->
                    // no let!/do! may appear in a finally block: the wait
                    // has to leave the handler before it can become a bind
                    sprintf
                        "%s inside the finally block of %s { }, where no let!/do! can appear; move the wait out of the handler (record the outcome in the body, await after the try) - sync-over-async in a computation expression invites thread-pool starvation and deadlocks."
                        what
                        builder
                | _ when s.InLambda ->
                    // the builder's bind cannot reach into a lambda: the
                    // callback's own signature is where the blocking is
                    // decided
                    sprintf
                        "%s inside a lambda within %s { }; the builder's let!/do! cannot reach into the callback, so its signature is the synchronous boundary - make the callback return a computation, or move the blocking call out of %s { } - sync-over-async here invites thread-pool starvation and deadlocks."
                        what
                        builder
                        builder
                | _ ->
                    sprintf
                        "%s inside %s { }; bind with let!/do! instead - sync-over-async in a computation expression invites thread-pool starvation and deadlocks."
                        what
                        builder

        // the sync-sibling swap walks code AWAY from async — an editor
        // action the author picks, or a config opt-in for the CLI:
        //     { "FR0049": { "syncSwap": 1 } }
        let swapAllowed =
            offerSyncSwap
            || Configuration.parameterInt fileName "FR0049" "SyncOverAsync" "syncSwap" 0 = 1

        let asFixes edits =
            edits |> List.map (fun (r, original, replacement) -> fix r original replacement)

        // the swap is an ALTERNATIVE to the async-ward fix, so it is its
        // own message: an editor applies every fix of one message together
        [
            hint "FR0049" message s.Range (asFixes s.Fixes)
            if swapAllowed && not s.AlternativeFixes.IsEmpty then
                hint
                    "FR0049"
                    (match s.Kind with
                     | SyncOverAsync.BlockKind.AntecedentResult ->
                         "Read the antecedent with GetAwaiter().GetResult(): a fault then arrives as the exception itself, not wrapped in an AggregateException - an observable change for a caller that catches the wrapper."
                     | _ ->
                         "Alternative: call the synchronous sibling API instead - this walks the code away from async, a waypoint at best.")
                    s.Range
                    (asFixes s.AlternativeFixes)
        ])

// the taskify fix: a file-private sync function draining a task at its
// boundary becomes task-returning, its callers awaiting — same rule code,
// its own message, all edits in this file
let private taskifyMessages (parseTree: ParsedInput) (source: ISourceText) checkResults projectCheck : Message list =
    Taskify.find parseTree source checkResults projectCheck
    |> List.map (fun s ->
        hint
            "FR0049"
            $"'{s.Name}' drains a task synchronously at its boundary, and every caller already sits in a task/async block; it becomes a task-returning function and the callers await it."
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("SyncOverAsync", "Blocking waits inside async/task expressions", HelpBase)>]
let syncOverAsyncEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0049" "SyncOverAsync" (fun () ->
        whenChecked ctx (fun check ->
            // the antecedent bind and the taskify fix both write `task { }`:
            // FSharp.Core 6+ on a non-Fable target only
            let taskAvailable = canReturnTask ctx.FileName ctx.ProjectOptions

            syncOverAsyncMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.FileName true taskAvailable check
            @ (if taskAvailable then
                   taskifyMessages ctx.ParseFileResults.ParseTree ctx.SourceText check None
               else
                   [])))

[<CliAnalyzer("SyncOverAsync", "Blocking waits inside async/task expressions", HelpBase)>]
let syncOverAsyncCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0049" "SyncOverAsync" (fun () ->
        let taskAvailable = canReturnTask ctx.FileName ctx.ProjectOptions

        syncOverAsyncMessages
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.FileName
            false
            taskAvailable
            ctx.CheckFileResults
        @ (if taskAvailable then
               taskifyMessages
                   ctx.ParseFileResults.ParseTree
                   ctx.SourceText
                   ctx.CheckFileResults
                   (Some ctx.CheckProjectResults)
           else
               []))

// ---- FR0050 / FR0051 Accumulation ----

let private accumulationMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    let foldEnabled = Configuration.isRuleEnabled fileName "FR0050" "MutableFold"

    let quadraticEnabled =
        Configuration.isRuleEnabled fileName "FR0051" "QuadraticAppend"

    let flagEnabled = Configuration.isRuleEnabled fileName "FR0107" "FlagLoop"

    if not (foldEnabled || quadraticEnabled || flagEnabled) then
        []
    else
        let folds, quadratics = Accumulation.find parseTree source checkResults

        let flagMessages =
            if flagEnabled then
                Accumulation.findFlagLoops parseTree source checkResults
                |> List.map (fun s ->
                    hint
                        "FR0107"
                        "This mutable flag loop asks an exists/forall question; the rewrite answers it directly - and short-circuits, doing the same or less work."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ])
            else
                []

        let foldMessages =
            if foldEnabled then
                folds
                |> List.map (fun s ->
                    hint
                        "FR0050"
                        "This mutable accumulator loop is a fold; the rewrite evaluates the same expression with the same bindings, without the mutable."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ])
            else
                []

        let quadraticMessages =
            if quadraticEnabled then
                quadratics
                |> List.map (fun s ->
                    let message =
                        match s.Kind with
                        | Accumulation.QuadraticKind.Collection ->
                            sprintf
                                "Appending to '%s' inside a loop copies it every iteration (O(n^2)); write the loop as a list expression (FR0156 rewrites a `let mutable` list that is only read after its loops), accumulate into a ResizeArray, or cons with :: and List.rev once at the end."
                                s.Name
                        | Accumulation.QuadraticKind.Str ->
                            sprintf
                                "Building the string '%s' with + inside a loop copies it every iteration (O(n^2)) - the slowest way to build a string (measured: 36x slower and 200x the allocation of a StringBuilder at 1000 pieces). Use a StringBuilder, or collect the pieces and String.concat once."
                                s.Name

                    hint "FR0051" message s.Range [])
            else
                []

        foldMessages @ quadraticMessages @ flagMessages

[<EditorAnalyzer("Accumulation", "Mutable accumulator loops and quadratic appends", HelpBase)>]
let accumulationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                whenChecked ctx (accumulationMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
                |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("Accumulation", "Mutable accumulator loops and quadratic appends", HelpBase)>]
let accumulationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                accumulationMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)
    }

// ---- FR0052 CountIsEmpty ----

let private countIsEmptyMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    CountIsEmpty.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0052"
            "Count on a concurrent collection walks its segments (O(n) with a snapshot); IsEmpty peeks at the head."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("CountIsEmpty", "Prefer IsEmpty over Count for emptiness checks", HelpBase)>]
let countIsEmptyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0052" "CountIsEmpty" (fun () ->
        whenChecked ctx (countIsEmptyMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("CountIsEmpty", "Prefer IsEmpty over Count for emptiness checks", HelpBase)>]
let countIsEmptyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0052" "CountIsEmpty" (fun () ->
        countIsEmptyMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0053 HexString ----

let private hexStringMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    HexString.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0053"
            "BitConverter.ToString + Replace allocates the dashed string just to strip it; Convert.ToHexString produces the identical hex directly."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("HexString", "Hex-encode with Convert.ToHexString", HelpBase)>]
let hexStringEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0053" "HexString" (fun () ->
        whenChecked ctx (hexStringMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("HexString", "Hex-encode with Convert.ToHexString", HelpBase)>]
let hexStringCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0053" "HexString" (fun () ->
        hexStringMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0055 SwallowedException ----

let private swallowedExceptionMessages
    (offerFixes: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults option)
    : Message list =
    let offered (offers: SwallowedException.Offer list) (at: range) =
        [
            if offerFixes then
                for offer in offers do
                    hint
                        "FR0055"
                        offer.Label
                        at
                        (offer.Edits
                         |> List.map (fun (r, original, replacement) -> fix r original replacement))
        ]

    // a try whose FR0168 fix removes it — `try T.Parse s with _ -> 0` —
    // is that rule's: one message, with the rewrite, not a swallow note
    // beside it
    let parseSites =
        if Configuration.isRuleEnabled parseTree.FileName "FR0168" "ParseControlFlow" then
            SwallowedException.findParseControlFlow parseTree source
            |> List.filter (fun s -> not s.Offers.IsEmpty)
            |> List.map (fun s -> s.Range)
        else
            []

    SwallowedException.find parseTree source check
    // the swallow's range is its handler clause, inside the try FR0168 reports
    |> List.filter (fun s -> not (parseSites |> List.exists (fun site -> Range.rangeContainsRange site s.Range)))
    |> List.collect (fun (s: SwallowedException.Suggestion) ->
        let clause = s.FallbackText |> Option.defaultValue "()"

        let message =
            match s.Probe with
            // a probe answers for a missing path instead of throwing: the
            // try adds nothing but a hidden failure, so the advice is to
            // delete it, not to guard a value
            | Some probe when probe.EndsWith "Exists" ->
                $"'with %s{s.PatternText} -> %s{clause}' swallows every exception around %s{probe}, which already answers false for a missing path and throws only for a malformed one or a permissions failure, which the catch then hides; delete the try and let the probe answer."
            | Some probe ->
                $"'with %s{s.PatternText} -> %s{clause}' swallows every exception around %s{probe}, which does not throw for a missing path (it answers 1601-01-01) and throws only for a malformed one or a permissions failure, which the fallback then hides; delete the try, and check File.Exists first if a missing file needs the fallback."
            | None when s.Teardown ->
                $"'with %s{s.PatternText} -> ()' around a teardown call is the best-effort release idiom, and still hides an ObjectDisposedException that says the release ran twice; narrow the catch to what a release throws - IOException, SocketException, ObjectDisposedException - and let the rest surface."
            | None ->
                match s.FallbackText with
                | Some fallback ->
                    $"'with %s{s.PatternText} -> %s{fallback}' swallows every exception and disguises the failure as a legitimate result; the best fix is usually a guard on the value that would throw and no catch at all, then a specific exception type, then at least a log line."
                | None ->
                    $"'with %s{s.PatternText} -> ()' silently swallows every exception, including cancellation and programming errors; the best fix is usually a guard on the value that would throw and no catch at all, then a specific exception type, then at least a log line."

        // each offer is its own message: an editor applies every fix of
        // one message together
        hint "FR0055" message s.Range [] :: offered s.Offers s.Range)

[<EditorAnalyzer("SwallowedException", "Empty catch-all handlers swallow every exception", HelpBase)>]
let swallowedExceptionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0055" "SwallowedException" (fun () ->
        swallowedExceptionMessages true ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

[<CliAnalyzer("SwallowedException", "Empty catch-all handlers swallow every exception", HelpBase)>]
let swallowedExceptionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0055" "SwallowedException" (fun () ->
        swallowedExceptionMessages false ctx.ParseFileResults.ParseTree ctx.SourceText (Some ctx.CheckFileResults))

// ---- FR0168 ParseControlFlow ----

/// `try T.Parse s with <parse failure or catch-all> -> fallback` is
/// `match T.TryParse s with | true, v -> v | false, _ -> fallback`: a
/// failed parse then costs a bool instead of a throw and a stack unwind.
/// The fix is a sweep's where the catch covers what TryParse answers false
/// to (a catch-all; FormatException, plus OverflowException on a numeric
/// type); a narrower catch is a note. CSharp.Refactor's CR0166.
let private parseControlFlowMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    SwallowedException.findParseControlFlow parseTree source
    |> List.map (fun s ->
        let message =
            if s.Offers.IsEmpty then
                $"'try {s.TypeName}.Parse ... with {s.PatternText}' uses the exception as the expected case's signal - a failed parse pays a throw and a stack unwind for what {s.TypeName}.TryParse answers with a bool; the catch covers less than TryParse answers false to (an overflow would propagate here and fall back there), so the rewrite is yours to judge."
            elif s.CatchAll then
                $"'try {s.TypeName}.Parse ... with {s.PatternText}' uses the exception as the expected case's signal - a failed parse pays a throw and a stack unwind for what {s.TypeName}.TryParse answers with a bool; the fix drops the try, and with it the catch-all that swallowed every other failure (a null input, which Parse threw for, takes the fallback either way)."
            else
                $"'try {s.TypeName}.Parse ... with {s.PatternText}' uses the exception as the expected case's signal - a failed parse pays a throw and a stack unwind for what {s.TypeName}.TryParse answers with a bool; the catch says which failures are expected, TryParse says it without the cost (a null input, which Parse threw for, then takes the fallback too)."

        hint
            "FR0168"
            message
            s.Range
            (s.Offers
             |> List.collect (fun offer -> offer.Edits)
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("ParseControlFlow", "A try around T.Parse with a parse-failure catch is T.TryParse", HelpBase)>]
let parseControlFlowEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0168" "ParseControlFlow" (fun () ->
        parseControlFlowMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ParseControlFlow", "A try around T.Parse with a parse-failure catch is T.TryParse", HelpBase)>]
let parseControlFlowCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0168" "ParseControlFlow" (fun () ->
        parseControlFlowMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0057 XmlDocParams ----

// the editor offers to scaffold the missing tags (empty, for the author
// to fill); a sweep never writes an empty tag, so the CLI only notes
let private xmlDocParamsMessages (offerScaffold: bool) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    XmlDocParams.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0057"
            (sprintf
                "The doc comment on '%s' documents some parameters but not %s; drifting docs mislead more than missing ones."
                s.BindingName
                (s.MissingParams |> List.map (sprintf "'%s'") |> String.concat ", "))
            s.Range
            (match s.Insertion with
             | Some(at, text) when offerScaffold -> [ fix at "" text ]
             | _ -> []))

[<EditorAnalyzer("XmlDocParams", "Doc comments that document only some parameters", HelpBase)>]
let xmlDocParamsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0057" "XmlDocParams" (fun () ->
        xmlDocParamsMessages true ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("XmlDocParams", "Doc comments that document only some parameters", HelpBase)>]
let xmlDocParamsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0057" "XmlDocParams" (fun () ->
        xmlDocParamsMessages false ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0058 RecursiveSeq ----

let private recursiveSeqMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    RecursiveSeq.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0058"
            (sprintf
                "'%s' re-enters itself through %s { }: each recursion level allocates a fresh enumerator and every element pays O(depth) MoveNexts. Walk with an explicit Stack/queue inside a single %s { } instead."
                s.FunctionName
                s.Builder
                s.Builder)
            s.Range
            [])

[<EditorAnalyzer("RecursiveSeq", "Recursive re-entry through sequence builders", HelpBase)>]
let recursiveSeqEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0058" "RecursiveSeq" (fun () ->
        recursiveSeqMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RecursiveSeq", "Recursive re-entry through sequence builders", HelpBase)>]
let recursiveSeqCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0058" "RecursiveSeq" (fun () ->
        recursiveSeqMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0059 StructOption ----

let private structOptionMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    StructOption.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0059"
            (sprintf
                "Private '%s' returns Option, allocating per call; ValueOption is a struct - the definition and every match site are rewritten together."
                s.FunctionName)
            s.DefRange
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("StructOption", "Move private option-returning functions to ValueOption", HelpBase)>]
let structOptionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0059" "StructOption" (fun () ->
        whenChecked ctx (structOptionMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("StructOption", "Move private option-returning functions to ValueOption", HelpBase)>]
let structOptionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0059" "StructOption" (fun () ->
        structOptionMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0060 AttributeMerge ----

let private attributeMergeMessages (fileName: string) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    // how wide a merged bracket may get is house style, not correctness:
    //     { "FR0060": { "maxAttributes": 6, "wrapColumn": 120 } }
    let maxAttributes =
        Configuration.parameterInt
            fileName
            "FR0060"
            "AttributeMerge"
            "maxAttributes"
            AttributeMerge.DefaultMaxAttributes

    let wrapColumn =
        Configuration.parameterInt fileName "FR0060" "AttributeMerge" "wrapColumn" AttributeMerge.DefaultWrapColumn

    AttributeMerge.find maxAttributes wrapColumn parseTree source
    |> List.map (fun s ->
        hint
            "FR0060"
            "Consecutive attribute brackets can merge into one [<...; ...>] list."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("AttributeMerge", "Merge consecutive attribute brackets", HelpBase)>]
let attributeMergeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0060" "AttributeMerge" (fun () ->
        attributeMergeMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("AttributeMerge", "Merge consecutive attribute brackets", HelpBase)>]
let attributeMergeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0060" "AttributeMerge" (fun () ->
        attributeMergeMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0061 ArgNames ----

let private argNamesMessages (offerRename: bool) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    ArgNames.find parseTree source
    |> List.map (fun s ->
        // one parameter leaves no doubt which name was meant: the editor
        // offers it; with several the author picks
        let fixes =
            match s.ParameterNames with
            | [ only ] when offerRename -> [ fix s.Range (Text.textOfRange source s.Range) ($"\"{only}\"") ]
            | _ -> []

        hint
            "FR0061"
            (sprintf
                "'%s' is not a parameter of this function (parameters: %s); the wrong name sends the caller debugging the wrong argument - nameof would keep it honest."
                s.UsedName
                (String.concat ", " s.ParameterNames))
            s.Range
            fixes)

[<EditorAnalyzer("ArgNames", "Argument-exception parameter names must exist", HelpBase)>]
let argNamesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0061" "ArgNames" (fun () ->
        argNamesMessages true ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ArgNames", "Argument-exception parameter names must exist", HelpBase)>]
let argNamesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0061" "ArgNames" (fun () ->
        argNamesMessages false ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0063 / FR0064 ExceptionRules ----

let private exceptionRulesMessages (fileName: string) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    let finallyEnabled = Configuration.isRuleEnabled fileName "FR0063" "RaiseInFinally"

    let reservedEnabled =
        Configuration.isRuleEnabled fileName "FR0064" "ReservedException"

    if not (finallyEnabled || reservedEnabled) then
        []
    else
        let finallies, reserved = ExceptionRules.find parseTree source

        let finallyMessages =
            if finallyEnabled then
                finallies
                |> List.map (fun s ->
                    hint
                        "FR0063"
                        "Raising inside finally replaces any exception already in flight - the original failure vanishes."
                        s.Range
                        [])
            else
                []

        let reservedMessages =
            if reservedEnabled then
                reserved
                |> List.map (fun s ->
                    hint
                        "FR0064"
                        $"%s{s.TypeName} is reserved for the runtime; raising it manually misleads catchers and debuggers - InvalidOperationException or an Argument exception says what actually happened."
                        s.Range
                        [])
            else
                []

        finallyMessages @ reservedMessages

[<EditorAnalyzer("ExceptionRules", "Raise-in-finally and reserved exceptions", HelpBase)>]
let exceptionRulesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () -> exceptionRulesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("ExceptionRules", "Raise-in-finally and reserved exceptions", HelpBase)>]
let exceptionRulesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () -> exceptionRulesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

// ---- FR0065 / FR0066 SecurityRules ----

let private securityRulesMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (offerAlternatives: bool)
    (checkResults: FSharpCheckFileResults option)
    : Message list =
    let cryptoEnabled = Configuration.isRuleEnabled fileName "FR0065" "WeakCrypto"

    // Retiring Ssl3/Tls/Tls11 changes what the process will negotiate with a
    // REMOTE endpoint - a wire-behaviour change, not an API one, so
    // `--api-changes` is the wrong permission to borrow for it: that flag is
    // about callers needing a recompile. A repository that knows no ancient
    // endpoint depends on the legacy protocol says so itself:
    //     { "FR0065": { "dropLegacyProtocols": true } }
    let dropLegacyProtocols =
        Configuration.parameterBool fileName "FR0065" "WeakCrypto" "dropLegacyProtocols" false

    let sqlEnabled = Configuration.isRuleEnabled fileName "FR0066" "SqlStrings"

    let unparametrizedEnabled =
        Configuration.isRuleEnabled fileName "FR0146" "UnparametrizedSql"

    let processEnabled = Configuration.isRuleEnabled fileName "FR0126" "ProcessSinks"

    if not (cryptoEnabled || sqlEnabled || unparametrizedEnabled || processEnabled) then
        []
    else
        // whatever the framework HAS marked, beside the curated list: an
        // enum member carrying [<Obsolete>] is the runtime saying the same
        // thing, and a later .NET retiring more needs no release from us
        let isObsoleteProtocol (r: range) =
            match checkResults with
            | None -> false
            | Some check ->
                try
                    let lineText = source.GetLineString(r.EndLine - 1)

                    match
                        OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ Text.textOfRange source r ])
                    with
                    | Some symbolUse ->
                        let attributes =
                            match symbolUse.Symbol with
                            // an enum member carries its attributes as a FIELD,
                            // not a property - reading only the latter found
                            // nothing on a deliberately obsoleted case
                            | :? FSharpField as field ->
                                Seq.toList field.FieldAttributes @ Seq.toList field.PropertyAttributes
                            | :? FSharpMemberOrFunctionOrValue as value -> Seq.toList value.Attributes
                            | _ -> []

                        attributes
                        |> List.exists (fun a ->
                            try
                                a.AttributeType.TryFullName = Some "System.ObsoleteAttribute"
                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                false)
                    | None -> false
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false

        let crypto, sql, processSinks =
            SecurityRules.find parseTree source isObsoleteProtocol

        let processMessages =
            if processEnabled then
                processSinks
                |> List.collect (fun s ->
                    [
                        hint
                            "FR0126"
                            $"A dynamically built string reaches {s.Sink} - the command/argument-injection sink, and doubly so when the string carries LLM or agent output; pass a fixed executable with an argument LIST (ProcessStartInfo.ArgumentList) instead."
                            s.Range
                            []
                        // the list form needs .NET Core 3 or later, and a shell's
                        // command line is not a list of arguments: an editor
                        // action, with the person looking at the executable
                        match s.Fix with
                        | Some(r, original, replacement) when offerAlternatives ->
                            hint
                                "FR0126"
                                "Alternative: pass the arguments as a list - each reaches the process whole, quoting and all (a hole that already carries several arguments becomes one; split it)."
                                s.Range
                                [ fix r original replacement ]
                        | _ -> ()
                    ])
            else
                []

        let cryptoMessages =
            if cryptoEnabled then
                crypto
                |> List.collect (fun s ->
                    // SHA1 only: MD5-as-checksum is a legitimate non-security
                    // use, and swapping any persisted hash algorithm is an
                    // API-shaped change — so this is an EDITOR action, never
                    // CLI-applied
                    match s.Kind, s.AlgoRange with
                    // MD5 too: its checksum uses (an ETag, a pid-file name) swap
                    // just as well — the person picking the offer knows what
                    // the hash feeds
                    | SecurityRules.WeakKind.Hash(("SHA1" | "MD5") as weak), Some algo when offerAlternatives ->
                        [
                            hint
                                "FR0065"
                                "Alternative: switch to SHA256 (mind persisted hashes and interop - the output size changes)."
                                s.Range
                                [ fix algo weak "SHA256" ]
                            hint
                                "FR0065"
                                "Alternative: switch to SHA512 (mind persisted hashes and interop - the output size changes)."
                                s.Range
                                [ fix algo weak "SHA512" ]
                        ]
                    // Retiring a protocol changes what the process negotiates
                    // with a remote endpoint, so the edit is made VISIBLE:
                    // commenting the dead operand out leaves the diff saying
                    // what was retired, where a deletion says only that
                    // something changed. Two offers, because the note asks for
                    // two different things - keep Tls12 and drop the rest, or
                    // set nothing at all and let the OS negotiate
                    | SecurityRules.WeakKind.Protocol proto, Some ident when offerAlternatives || dropLegacyProtocols ->
                        let commentOperand =
                            s.ObsoleteOperand
                            |> Option.map (fun operand ->
                                let original = Text.textOfRange source operand

                                hint
                                    "FR0065"
                                    $"Alternative: comment {proto} out of the flags, keeping the protocols beside it."
                                    s.Range
                                    [ fix operand original $"(* {original} *)" ])

                        let commentSetting =
                            s.AssignmentRange
                            |> Option.map (fun assignment ->
                                let original = Text.textOfRange source assignment

                                // a `()` stays where the setting was, and
                                // FIRST: the setting may be a function's
                                // whole body, where `let f () =` over a
                                // bare comment does not parse, and a
                                // comment before the `()` would move the
                                // block's offside column to the `()`,
                                // putting the next statement offside
                                hint
                                    "FR0065"
                                    "Alternative: comment the whole setting out and let the framework default stand (the OS negotiates the strongest protocol both ends share)."
                                    s.Range
                                    [ fix assignment original $"() (* {original} *)" ])

                        let swap =
                            hint
                                "FR0065"
                                $"Alternative: replace {proto} with Tls12 (mind endpoints that only speak the legacy protocol)."
                                s.Range
                                [ fix ident proto "Tls12" ]

                        // the editor shows every way out and a person picks;
                        // an unattended run has to CHOOSE, and the narrowest
                        // edit wins on its own when three overlap - which is
                        // the swap, leaving `Tls12 ||| Tls12`. Retiring the
                        // operand says what happened and keeps the live
                        // protocol, so that is the one a `dropLegacyProtocols`
                        // run applies; the whole-setting and swap variants
                        // stay a person's call
                        if offerAlternatives then
                            [
                                yield! Option.toList commentOperand
                                yield! Option.toList commentSetting
                                yield swap
                            ]
                        else
                            [ defaultArg commentOperand swap ]
                    | _ -> [])
                |> List.append (
                    crypto
                    |> List.map (fun s ->
                        let message =
                            match s.Kind with
                            | SecurityRules.WeakKind.Hash name ->
                                $"%s{name} is collision-broken for security purposes; use SHA-256 or stronger (for non-security checksums, note the intent)."
                            | SecurityRules.WeakKind.Cipher name ->
                                $"%s{name}'s key size is within practical attack range; use AES."
                            | SecurityRules.WeakKind.CertificateBypass ->
                                "Overriding certificate validation silently accepts any man-in-the-middle; scope trust to the specific expected certificate instead."
                            | SecurityRules.WeakKind.Protocol name ->
                                $"%s{name} is broken or deprecated on the wire; prefer setting nothing (the OS negotiates the strongest protocol) or Tls12+."

                        hint "FR0065" message s.Range [])
                )
            else
                []

        let sqlMessages =
            sql
            |> List.choose (fun s ->
                if s.Unparametrized then
                    if unparametrizedEnabled then
                        Some(
                            hint
                                "FR0146"
                                (sprintf
                                    "This SQL command carries no parameter at all (%s): a full-table statement, or values written into the text - possible, but suspicious; parameters are where the values were supposed to go."
                                    s.Sink)
                                s.Range
                                []
                        )
                    else
                        None
                elif sqlEnabled then
                    Some(
                        hint
                            "FR0066"
                            (sprintf
                                "SQL assembled from strings flows user data into the query language (%s); use parameters (@name + Parameters.Add) instead."
                                s.Sink)
                            s.Range
                            []
                    )
                else
                    None)

        cryptoMessages @ sqlMessages @ processMessages

[<EditorAnalyzer("SecurityRules", "Weak crypto and string-built SQL", HelpBase)>]
let securityRulesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                securityRulesMessages
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    true
                    ctx.CheckFileResults)
    }

[<CliAnalyzer("SecurityRules", "Weak crypto and string-built SQL", HelpBase)>]
let securityRulesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                securityRulesMessages
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    false
                    (Some ctx.CheckFileResults))
    }

// ---- FR0125 UnicodeHygiene ----

let private unicodeMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    UnicodeHygiene.find parseTree source
    |> List.map (fun s ->
        let fixes =
            match s.Fix with
            | Some(r, original, replacement) -> [ fix r original replacement ]
            | None -> []

        hint
            "FR0125"
            $"Invisible character {s.CodePoint} ({s.FamilyName}) - it cannot be seen in review, which is exactly how Trojan Source and prompt-smuggling work; spell it as an escape or remove it."
            s.Range
            fixes)

[<EditorAnalyzer("UnicodeHygiene", "Invisible and bidirectional Unicode in source", HelpBase)>]
let unicodeEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0125" "UnicodeHygiene" (fun () ->
        unicodeMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("UnicodeHygiene", "Invisible and bidirectional Unicode in source", HelpBase)>]
let unicodeCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0125" "UnicodeHygiene" (fun () ->
        unicodeMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0127 SecretLiterals ----

let private secretMessages (fileName: string) (parseTree: ParsedInput) : Message list =
    // two codes from one scan, each behind its own switch: a config that
    // turns FR0153 off keeps the FR0127 leaks, and the other way round
    let leakEnabled = Configuration.isRuleEnabled fileName "FR0127" "SecretLiterals"

    let designTimeEnabled =
        Configuration.isRuleEnabled fileName "FR0153" "SecretLiterals"

    SecretLiterals.find parseTree
    |> List.filter (fun s ->
        if s.DesignTimeLiteral then
            designTimeEnabled
        else
            leakEnabled)
    |> List.map (fun s ->
        // a literal cannot move to configuration, so the check is a different
        // one: the value should be a development credential
        if s.DesignTimeLiteral then
            let what =
                match s.Provider with
                | "connection-string password" -> "This connection string carries its password"
                | provider -> $"This literal matches {provider}'s credential format and holds it"

            hint "FR0153" $"{what} in a literal - it should be a development credential." s.Range []
        else

            let text =
                match s.Provider with
                | "connection-string password" ->
                    "This connection string carries its password in source - a leaked credential until proven otherwise; rotate it and move the string to configuration or a secret store."
                | "JWT"
                | "bearer token" ->
                    $"This literal is a signed {s.Provider} - a leaked credential until proven otherwise; revoke it and move it to configuration or a secret store."
                | provider ->
                    $"This literal matches {provider}'s documented credential format - a leaked key until proven otherwise; rotate it and move it to configuration or a secret store."

            hint "FR0127" text s.Range [])

[<EditorAnalyzer("SecretLiterals", "Provider-format API keys in string literals", HelpBase)>]
let secretsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0127"; "FR0153" ] "SecretLiterals" (fun () ->
        secretMessages ctx.FileName ctx.ParseFileResults.ParseTree)

[<CliAnalyzer("SecretLiterals", "Provider-format API keys in string literals", HelpBase)>]
let secretsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0127"; "FR0153" ] "SecretLiterals" (fun () ->
        secretMessages ctx.FileName ctx.ParseFileResults.ParseTree)

// ---- FR0128 ObsoleteCrypto ----

let private obsoleteCryptoMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    ObsoleteCrypto.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0128"
            $"'{s.ObsoleteName}' is the obsolete constructor spelling (SYSLIB0021); the static factory picks the platform implementation of the SAME algorithm."
            s.Range
            [ fix s.Range (Text.textOfRange source s.Range) s.Replacement ])

[<EditorAnalyzer("ObsoleteCrypto", "Obsolete crypto constructors become static factories", HelpBase)>]
let obsoleteCryptoEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0128" "ObsoleteCrypto" (fun () ->
        obsoleteCryptoMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ObsoleteCrypto", "Obsolete crypto constructors become static factories", HelpBase)>]
let obsoleteCryptoCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0128" "ObsoleteCrypto" (fun () ->
        obsoleteCryptoMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0129 MatchGuards ----

let private matchGuardsMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MatchGuards.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0129"
            $"The guard only equality-tests '{s.BinderName}' against {s.LiteralText} - that IS the literal pattern."
            s.Range
            [ fix s.Range (Text.textOfRange source s.Range) s.LiteralText ])

[<EditorAnalyzer("MatchGuards", "A guard that only equality-tests the binder is the literal pattern", HelpBase)>]
let matchGuardsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0129" "MatchGuards" (fun () ->
        matchGuardsMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MatchGuards", "A guard that only equality-tests the binder is the literal pattern", HelpBase)>]
let matchGuardsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0129" "MatchGuards" (fun () ->
        matchGuardsMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0130 LiteralConst ----

let private literalConstMessages
    (scopeOpen: bool)
    (boundAsPatternElsewhere: string -> bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    widened scopeOpen (fun scope ->
        LiteralConst.findWith boundAsPatternElsewhere scope parseTree source
        |> List.map (fun s ->
            let insertRange, text = s.Fix

            hint
                "FR0130"
                $"'{s.Name}' is a compile-time constant; [<Literal>] lets it serve in patterns and attribute arguments and const-folds at use sites."
                s.Range
                (fix insertRange "" text
                 :: (s.SignatureEdits
                     |> List.map (fun (r, original, replacement) -> fix r original replacement)))))

[<EditorAnalyzer("LiteralConst", "Module-level constants gain [<Literal>]", HelpBase)>]
let literalConstEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0130" "LiteralConst" (fun () ->
        literalConstMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            (patternBoundInSibling ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

[<CliAnalyzer("LiteralConst", "Module-level constants gain [<Literal>]", HelpBase)>]
let literalConstCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0130" "LiteralConst" (fun () ->
        literalConstMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            (patternBoundInSibling ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText)

// ---- FR0131 RecTailCall ----

let private recTailCallMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    RecTailCall.find parseTree source checkResults
    |> List.map (fun s ->
        let insertRange, text = s.Fix

        hint
            "FR0131"
            $"every recursive call in '{s.Name}' sits in tail position; [<TailCall>] makes the compiler warn (FS3569) if a later edit changes that."
            s.Range
            [ fix insertRange "" text ])

[<EditorAnalyzer("RecTailCall", "Provably tail-recursive functions gain [<TailCall>]", HelpBase)>]
let recTailCallEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0131" "RecTailCall" (fun () ->
        whenChecked ctx (recTailCallMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("RecTailCall", "Provably tail-recursive functions gain [<TailCall>]", HelpBase)>]
let recTailCallCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0131" "RecTailCall" (fun () ->
        recTailCallMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0132 CommentDoc ----

let private commentDocMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    CommentDoc.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0132"
            $"this public {s.What} has no XML doc, but its trailing comment says exactly what one would; promoted to /// it reaches tooltips and generated docs."
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("CommentDoc", "Trailing comments promoted to XML doc position", HelpBase)>]
let commentDocEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0132" "CommentDoc" (fun () ->
        commentDocMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("CommentDoc", "Trailing comments promoted to XML doc position", HelpBase)>]
let commentDocCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0132" "CommentDoc" (fun () ->
        commentDocMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0133 NameQuoting ----

let private nameQuotingMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    projectCheck
    : Message list =
    // test-attributed names rewrite by default; local and file-private
    // names are the config opt-in:  { "FR0133": { "locals": 1 } }
    let includeLocals =
        Configuration.parameterInt fileName "FR0133" "NameQuoting" "locals" 0 = 1

    NameQuoting.find includeLocals parseTree source checkResults projectCheck
    |> List.map (fun s ->
        hint
            "FR0133"
            $"'{s.Name}' is {s.Name.Length} characters of camel case; the double-backtick name ``{s.Quoted}`` reads as the sentence it is - renamed at its definition and every use."
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("NameQuoting", "Five-word names become double-backtick names", HelpBase)>]
let nameQuotingEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0133" "NameQuoting" (fun () ->
        whenChecked ctx (fun check ->
            nameQuotingMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText check None))

[<CliAnalyzer("NameQuoting", "Five-word names become double-backtick names", HelpBase)>]
let nameQuotingCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0133" "NameQuoting" (fun () ->
        nameQuotingMessages
            ctx.FileName
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults
            (Some ctx.CheckProjectResults))

// ---- FR0134 DateTimeOffsetMigration ----

let private dateTimeOffsetMessages
    (scopeOpen: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    DateTimeOffsetMigration.find scopeOpen parseTree source
    |> List.choose (fun s ->
        if s.IsFilePrivate then
            DateTimeOffsetMigration.migrate parseTree source checkResults s
            |> Option.map (fun edits ->
                hint
                    "FR0134"
                    $"Field '{s.FieldName}: DateTime' of the file-private type '{s.TypeName}' drops the clock it was read from; every write and read fits DateTimeOffset, which keeps the instant AND its offset - migrated in one edit set."
                    s.Range
                    (edits |> List.map (fun (r, original, replacement) -> fix r original replacement)))
        else
            None)

[<EditorAnalyzer("DateTimeOffsetMigration", "DateTime record fields migrate to DateTimeOffset", HelpBase)>]
let dateTimeOffsetEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0134" "DateTimeOffsetMigration" (fun () ->
        whenChecked
            ctx
            (dateTimeOffsetMessages
                (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText))

[<CliAnalyzer("DateTimeOffsetMigration", "DateTime record fields migrate to DateTimeOffset", HelpBase)>]
let dateTimeOffsetCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0134" "DateTimeOffsetMigration" (fun () ->
        dateTimeOffsetMessages
            (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

// ---- FR0135 LiterateComment ----

let private literateCommentMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    LiterateComment.find parseTree source
    |> List.map (fun s ->
        let r, text = s.Fix

        hint
            "FR0135"
            $"this block comment carries {s.Evidence} - markdown FSharp.Formatting silently drops from a plain comment; one more star makes it the literate cell it reads as."
            s.Range
            [ fix r "" text ])

[<EditorAnalyzer("LiterateComment", "Markdown-bearing script comments become literate cells", HelpBase)>]
let literateCommentEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0135" "LiterateComment" (fun () ->
        literateCommentMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("LiterateComment", "Markdown-bearing script comments become literate cells", HelpBase)>]
let literateCommentCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0135" "LiterateComment" (fun () ->
        literateCommentMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0136 EmptyGuid ----

let private emptyGuidMessages
    (parseTree: ParsedInput)
    (source: ISourceText)
    (offerAlternatives: bool)
    checkResults
    : Message list =
    EmptyGuid.find parseTree source checkResults
    |> List.collect (fun s ->
        let original = Text.textOfRange source s.Range

        [
            hint
                "FR0136"
                $"the zero-argument Guid constructor is 00000000-...: if the empty value is intended, {s.EmptyText} says so; if a FRESH guid was meant, this is the classic .NET slip."
                s.Range
                [ fix s.Range original s.EmptyText ]
            // the behavior-CHANGING repair — the likely intent, but only a
            // human knows; never CLI-applied
            if offerAlternatives then
                hint
                    "FR0136"
                    $"Alternative: {s.NewGuidText} - if a fresh guid was the intent, this is the actual bug fix."
                    s.Range
                    [ fix s.Range original s.NewGuidText ]
        ])

[<EditorAnalyzer("EmptyGuid", "Zero-argument Guid constructors state Empty or become NewGuid", HelpBase)>]
let emptyGuidEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0136" "EmptyGuid" (fun () ->
        whenChecked ctx (emptyGuidMessages ctx.ParseFileResults.ParseTree ctx.SourceText true))

[<CliAnalyzer("EmptyGuid", "Zero-argument Guid constructors state Empty or become NewGuid", HelpBase)>]
let emptyGuidCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0136" "EmptyGuid" (fun () ->
        emptyGuidMessages ctx.ParseFileResults.ParseTree ctx.SourceText false ctx.CheckFileResults)

// ---- FR0137 MapFusion ----

let private mapFusionMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MapFusion.find parseTree source
    |> List.map (fun s ->
        let message =
            if s.Module = "Seq" then
                "These two Seq.map stages can fuse into one, removing a lazy wrapper."
            else
                $"These two {s.Module}.map passes can fuse into one, avoiding an intermediate {s.Module.ToLowerInvariant()}."

        hint "FR0137" message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("MapFusion", "Fuse consecutive map passes with function composition", HelpBase)>]
let mapFusionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0137" "MapFusion" (fun () ->
        mapFusionMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MapFusion", "Fuse consecutive map passes with function composition", HelpBase)>]
let mapFusionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0137" "MapFusion" (fun () ->
        mapFusionMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0139 SeqOnArray ----

let private seqOnArrayMessages
    (offerAlternatives: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    SeqOnArray.find parseTree source checkResults
    |> List.collect (fun s ->
        let primary =
            match s.LinqSpelling with
            | None ->
                hint
                    "FR0139"
                    (sprintf
                        "Seq.%s on '%s' walks an array through IEnumerable - an interface call per element; Array.%s reads the block directly. Arrays only: a Seq call on a list or a lazy source can be deliberate."
                        s.FunctionName
                        s.CollectionText
                        s.FunctionName)
                    s.Range
                    [ fix s.Range "Seq" "Array" ]
            | Some(callRange, linqText) ->
                // the DEFAULT for a vectorisable element type is the LINQ
                // spelling: 5.4x against the Array module's 1.27x, and a
                // performance rule should apply the faster answer
                hint
                    "FR0139"
                    (sprintf
                        "Seq.contains on '%s' walks the array element by element; Enumerable.Contains vectorises over its span - measured 587ns to 109ns over 1000 ints. Equivalent for int and int64, whose structural equality agrees with EqualityComparer.Default."
                        s.CollectionText)
                    callRange
                    [ fix callRange (Text.textOfRange source callRange) linqText ]

        // the SECOND answer rides as its own message so an editor offers
        // it as a separate code action; the CLI never sees it and applies
        // only the default above
        match s.LinqSpelling with
        | Some _ when offerAlternatives ->
            [
                primary
                hint
                    "FR0139"
                    "...or keep the F# module: Array.contains is the idiomatic step and still beats Seq (measured 587ns to 464ns), without bringing System.Linq into the file."
                    s.Range
                    [ fix s.Range "Seq" "Array" ]
            ]
        | _ -> [ primary ])

[<EditorAnalyzer("SeqOnArray", "Seq functions on a proven array use the Array module", HelpBase)>]
let seqOnArrayEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0139" "SeqOnArray" (fun () ->
        whenChecked ctx (seqOnArrayMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("SeqOnArray", "Seq functions on a proven array use the Array module", HelpBase)>]
let seqOnArrayCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0139" "SeqOnArray" (fun () ->
        seqOnArrayMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0140 ObjectInitializer ----

let private objectInitializerMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    ObjectInitializer.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0140"
            (sprintf
                "This constructor and the %d property assignment(s) after it are F#'s named-property construction spelled out. Setting them in the call reads as one constructed value instead of an assembled one, and the half-built object stops being nameable in between - the same calls, in the same order."
                s.Count)
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ObjectInitializer", "Fold property assignments into the construction", HelpBase)>]
let objectInitializerEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0140" "ObjectInitializer" (fun () ->
        whenChecked ctx (objectInitializerMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ObjectInitializer", "Fold property assignments into the construction", HelpBase)>]
let objectInitializerCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0140" "ObjectInitializer" (fun () ->
        objectInitializerMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0141 GenerativeLoop ----

let private generativeLoopMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    GenerativeLoop.find parseTree source
    |> List.map (fun s ->
        let carried = s.Carried |> List.map (sprintf "'%s'") |> String.concat ", "

        // the tail is the point when there IS one: raising the flag reads
        // as a break, but the iteration finishes first
        let exit =
            if s.TailAfterFlag > 0 then
                sprintf
                    "raising '%s' does not leave the loop - the %d statement(s) after it still run in that same iteration, and the loop exits only at the next condition check"
                    s.Flag
                    s.TailAfterFlag
            else
                sprintf
                    "the loop leaves through '%s' at the next condition check rather than where the decision is made"
                    s.Flag

        hint
            "FR0141"
            (sprintf
                "Consider a tail-recursive function here: this loop carries %s forward by mutation, and %s. Recursion would take that state as parameters and return at the point the decision is made, leaving no flag, no mutables, and no tail to run. Note only - naming the function and its parameters is yours."
                carried
                exit)
            s.Range
            [])

[<EditorAnalyzer("GenerativeLoop", "State-carrying while loops read as tail recursion", HelpBase)>]
let generativeLoopEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0141" "GenerativeLoop" (fun () ->
        generativeLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("GenerativeLoop", "State-carrying while loops read as tail recursion", HelpBase)>]
let generativeLoopCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0141" "GenerativeLoop" (fun () ->
        generativeLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0138 StringEmptiness ----

let private stringEmptinessMessages
    (offerAlternatives: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    StringEmptiness.find parseTree source
    |> List.collect (fun s ->
        let predicate =
            if s.WhiteSpace then
                "String.IsNullOrWhiteSpace"
            else
                "String.IsNullOrEmpty"

        if s.Guarded then
            [
                hint
                    "FR0138"
                    $"this hand-rolled emptiness test IS {predicate} - the null guard short-circuits exactly as the predicate answers, and the Trim spellings stop allocating a trimmed copy."
                    s.Range
                    [ fix s.Range s.OriginalText s.ReplacementText ]
            ]
        else
            // null behavior changes: the original throws, the predicate
            // answers true. Almost always the intent — but a human signs
            [
                hint
                    "FR0138"
                    $"trimming a copy just to test it: {predicate} tests the same whitespace set without allocating - but it answers true for null where this throws, so apply deliberately."
                    s.Range
                    (if offerAlternatives then
                         [ fix s.Range s.OriginalText s.ReplacementText ]
                     else
                         [])
            ])

[<EditorAnalyzer("StringEmptiness", "Hand-rolled emptiness tests become the BCL predicates", HelpBase)>]
let stringEmptinessEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0138" "StringEmptiness" (fun () ->
        stringEmptinessMessages true ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("StringEmptiness", "Hand-rolled emptiness tests become the BCL predicates", HelpBase)>]
let stringEmptinessCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0138" "StringEmptiness" (fun () ->
        stringEmptinessMessages false ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0062 / FR0067 / FR0068 MiscRules ----

let private miscRulesMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (offerAlternatives: bool)
    (fableTarget: bool)
    : Message list =
    let mutableEnabled =
        Configuration.isRuleEnabled fileName "FR0062" "VisibleMutableState"

    // Fable compiles to another runtime whose parsing is not culture-bound;
    // the culture note is a .NET concern and stays quiet there
    let parseEnabled =
        Configuration.isRuleEnabled fileName "FR0067" "CultureParse" && not fableTarget

    let enumEnabled = Configuration.isRuleEnabled fileName "FR0068" "DuplicateEnumValue"

    if not (mutableEnabled || parseEnabled || enumEnabled) then
        []
    else
        let mutables, parses, enums = MiscRules.find parseTree source

        let mutableMessages =
            if mutableEnabled then
                mutables
                |> List.collect (fun s ->
                    // the editor offers `private` in one click; whether
                    // another file writes the value is what the compiler
                    // then says, and the CLI cannot know without a
                    // cross-file pass, so it only notes
                    let insertAt = Range.mkRange s.Range.FileName s.Range.Start s.Range.Start

                    [
                        hint
                            "FR0062"
                            (sprintf
                                "'%s' is visible mutable module state - a global variable any consumer can write, with no thread safety; make it private (internal when another module of the same assembly writes it) or pass the state explicitly."
                                s.Name)
                            s.Range
                            (if offerAlternatives then
                                 [ fix insertAt "" "private " ]
                             else
                                 [])
                        if offerAlternatives then
                            hint
                                "FR0062"
                                $"Alternative: make '{s.Name}' internal - for when another module of the same assembly writes it."
                                s.Range
                                [ fix insertAt "" "internal " ]
                    ])
            else
                []

        let parseMessages =
            if parseEnabled then
                // wire/config data wants InvariantCulture — the clear
                // default; spelling out CurrentCulture is the alternative
                // when today's implicit behavior WAS the intent. The CLI
                // auto-applies invariant only on the config opt-in:
                //     { "FR0067": { "invariant": 1 } }
                let autoInvariant =
                    Configuration.parameterInt fileName "FR0067" "MiscRules" "invariant" 0 = 1

                parses
                |> List.collect (fun s ->
                    let note =
                        hint
                            "FR0067"
                            (sprintf
                                "%s without a culture reads differently under different server cultures ('1,5' vs '1.5', day/month order); pass CultureInfo.InvariantCulture or the intended culture explicitly. The editor offers both; a sweep applies the invariant one with { \"FR0067\": { \"invariant\": 1 } }."
                                s.CallName)
                            s.Range
                            (match s.CultureFix with
                             | Some mk when autoInvariant ->
                                 let r, original, replacement = mk "InvariantCulture"

                                 [ fix r original replacement ]
                             | _ -> [])

                    match s.CultureFix with
                    | Some mk when offerAlternatives && not autoInvariant ->
                        let ri, oi, pi = mk "InvariantCulture"
                        let rc, oc, pc = mk "CurrentCulture"

                        [
                            note
                            hint
                                "FR0067"
                                "Fix: parse with InvariantCulture (wire and config data)."
                                s.Range
                                [ fix ri oi pi ]
                            hint
                                "FR0067"
                                "Alternative: spell out CurrentCulture - today's implicit behavior, made deliberate."
                                s.Range
                                [ fix rc oc pc ]
                        ]
                    | _ -> [ note ])
            else
                []

        let enumMessages =
            if enumEnabled then
                enums
                |> List.map (fun s ->
                    hint
                        "FR0068"
                        (sprintf
                            "Enum case '%s' has the same value as '%s'; comparisons and ToString silently conflate them - usually a copy-paste slip."
                            s.CaseName
                            s.OriginalName)
                        s.Range
                        [])
            else
                []

        mutableMessages @ parseMessages @ enumMessages

[<EditorAnalyzer("MiscRules", "Visible mutable state, culture parsing, duplicate enum values", HelpBase)>]
let miscRulesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                miscRulesMessages
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    true
                    (referencesAssembly "Fable.Core" ctx.ProjectOptions))
    }

[<CliAnalyzer("MiscRules", "Visible mutable state, culture parsing, duplicate enum values", HelpBase)>]
let miscRulesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                miscRulesMessages
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    false
                    (referencesAssembly "Fable.Core" ctx.ProjectOptions))
    }

// ---- FR0069 / FR0070 StructHints ----

let private structHintsMessages
    (scopeOpen: bool)
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (checkOpt: FSharpCheckFileResults option)
    (projectCheck: FSharpCheckProjectResults option)
    : Message list =
    widened scopeOpen (fun scope ->
        let voptionEnabled = Configuration.isRuleEnabled fileName "FR0069" "VOptionField"
        let structEnabled = Configuration.isRuleEnabled fileName "FR0070" "SmallStructType"

        let structTupleEnabled =
            Configuration.isRuleEnabled fileName "FR0093" "StructTupleField"

        if not (voptionEnabled || structEnabled || structTupleEnabled) then
            []
        else
            // A companion .fsi declares these types too, and a migration changes
            // what it declares — `{ Seen: int option }` becoming voption stops
            // the project compiling. The api pass sidesteps this by skipping
            // signature-carrying projects wholesale, but these migrations run in
            // the NORMAL pass, so that skip never covered them: verified by
            // running FR0069 against a signature, which applied four edits and
            // was rolled back.
            //
            // The advice still stands; only the edit is withheld, the same way a
            // capability fix stands down where it has nowhere safe to live.
            let signatureBound = Text.hasSignatureFile parseTree.FileName

            let voptions, structs, structTuples =
                StructHints.findWith checkOpt scope parseTree source

            let voptionMessages =
                if voptionEnabled then
                    voptions
                    |> List.map (fun s ->
                        // a strictly file-private field migrates as ONE edit
                        // set: field type plus every use, all in this file by
                        // construction. Any use outside the provably-
                        // rewritable shapes keeps it a note
                        let migration =
                            match checkOpt with
                            | Some check when s.IsFilePrivate && not signatureBound ->
                                VOptionMigration.migrate
                                    parseTree
                                    source
                                    check
                                    s.FieldIdRange
                                    s.FieldName
                                    s.OptionNameRange
                            | Some check when
                                Visibility.apiChangesAllowed ()
                                && s.IsConfined
                                && not signatureBound
                                // a file #loaded by a script that does not typecheck:
                                // its calls cannot be read, so nothing declared in
                                // it may be reshaped
                                && not (ProjectSources.isUnreadable parseTree.FileName)
                                ->
                                // a strictly INTERNAL field under --api-changes:
                                // every use in the project classified against its
                                // own file, one edit set spanning files. Public
                                // fields never take this path (consumers can sit
                                // in a sibling project no scan sees), and neither
                                // does an assembly that opens its internals to
                                // friends
                                projectCheck
                                |> Option.filter (ProjectSources.hasInternalsVisibleTo >> not)
                                |> Option.bind (fun pc ->
                                    VOptionMigration.migrateProject
                                        parseTree
                                        source
                                        check
                                        pc
                                        s.FieldIdRange
                                        s.FieldName
                                        s.OptionNameRange)
                            | _ -> None

                        let containment = if s.IsFilePrivate then "file-private" else "internal"

                        match migration with
                        | Some edits ->
                            hint
                                "FR0069"
                                $"Field '%s{s.FieldName}: %s{s.ElementText} option' of the %s{containment} type '%s{s.TypeName}' boxes the %s{s.ElementText} on every Some; the fix migrates the field and its %d{edits.Length - 1} use(s) to '%s{s.ElementText} voption'."
                                s.Range
                                (edits |> List.map (fun (r, original, replacement) -> fix r original replacement))
                        | None ->
                            hint
                                "FR0069"
                                $"Field '%s{s.FieldName}: %s{s.ElementText} option' of the contained type '%s{s.TypeName}' boxes the %s{s.ElementText} on every Some; '%s{s.ElementText} voption' keeps it flat - and private/internal visibility keeps the migration contained (public types risk serialization changes and unbounded call-site churn)."
                                s.Range
                                [])
                else
                    []

            let structMessages =
                if structEnabled then
                    structs
                    |> List.map (fun s ->
                        let fixes =
                            match s.Fix with
                            | Some(r, text) -> [ fix r "" text ]
                            | None -> []

                        hint
                            "FR0070"
                            $"Contained record '%s{s.TypeName}' has only %d{s.FieldCount} small struct field(s); [<Struct>] removes a heap allocation per instance (mind copy semantics: struct records copy on assignment)."
                            s.Range
                            fixes)
                else
                    []

            let structTupleMessages =
                if structTupleEnabled then
                    structTuples
                    |> List.map (fun s ->
                        // a strictly file-private field migrates as ONE edit set:
                        // field type plus every construction/destructuring, all
                        // in this file by construction
                        let migration =
                            match checkOpt with
                            | Some check when s.IsFilePrivate && not signatureBound ->
                                StructTupleMigration.migrate parseTree source check s.FieldIdRange s.FieldName s.Range
                            | Some check when
                                Visibility.apiChangesAllowed ()
                                && s.IsConfined
                                && not signatureBound
                                // a file #loaded by a script that does not typecheck:
                                // its calls cannot be read, so nothing declared in
                                // it may be reshaped
                                && not (ProjectSources.isUnreadable parseTree.FileName)
                                ->
                                projectCheck
                                |> Option.filter (ProjectSources.hasInternalsVisibleTo >> not)
                                |> Option.bind (fun pc ->
                                    StructTupleMigration.migrateProject
                                        parseTree
                                        source
                                        check
                                        pc
                                        s.FieldIdRange
                                        s.FieldName
                                        s.Range)
                            | _ -> None

                        let containment = if s.IsFilePrivate then "file-private" else "internal"

                        match migration with
                        | Some edits ->
                            hint
                                "FR0093"
                                $"Field '%s{s.FieldName}: %s{s.TupleText}' of the %s{containment} type '%s{s.TypeName}' is a reference tuple: one heap object per value; the fix migrates the field and its %d{edits.Length - 1} use(s) to 'struct (%s{s.TupleText})'."
                                s.Range
                                (edits |> List.map (fun (r, original, replacement) -> fix r original replacement))
                        | None ->
                            hint
                                "FR0093"
                                $"Field '%s{s.FieldName}: %s{s.TupleText}' of the contained type '%s{s.TypeName}' is a reference tuple: one heap object per value. 'struct (%s{s.TupleText})' stores it inline - but every construction and destructuring of the field needs the struct keyword too, so this is advice, not a mechanical fix."
                                s.Range
                                [])
                else
                    []

            voptionMessages @ structMessages @ structTupleMessages)

[<EditorAnalyzer("StructHints", "voption fields and [<Struct>] candidates in contained types", HelpBase)>]
let structHintsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        // no ProjectSources host in editors: the cross-file path degrades
        // to the note by itself
        return
            DeepStack.run (fun () ->
                structHintsMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    ctx.CheckFileResults
                    None)
    }

[<CliAnalyzer("StructHints", "voption fields and [<Struct>] candidates in contained types", HelpBase)>]
let structHintsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        // parse-only runs carry degraded check results; the migration
        // itself refuses to run on error files, so passing them is safe
        return
            DeepStack.run (fun () ->
                structHintsMessages
                    (shapeScopeOpen ctx.FileName ctx.ProjectOptions)
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    (Some ctx.CheckFileResults)
                    (Some ctx.CheckProjectResults))
    }

// ---- FR0071 LoopInvariant ----

let private loopInvariantMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    LoopInvariant.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0071"
            $"'let %s{s.Name} = ...' does not depend on the loop, but every iteration re-evaluates it; the rewrite hoists it above the loop (the value is pure, so evaluating it once is the only observable change - a saving)."
            s.Range
            [
                for range, original, replacement in s.Edits -> fix range original replacement
            ])

[<EditorAnalyzer("LoopInvariant", "Hoist pure loop-invariant bindings out of loops", HelpBase)>]
let loopInvariantEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0071" "LoopInvariant" (fun () ->
        whenChecked ctx (loopInvariantMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("LoopInvariant", "Hoist pure loop-invariant bindings out of loops", HelpBase)>]
let loopInvariantCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0071" "LoopInvariant" (fun () ->
        loopInvariantMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0072 ExpandWildcard ----

let private expandWildcardMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    ExpandWildcard.find parseTree source checkResults
    |> List.map (fun s ->
        let hidden = String.concat ", " s.HiddenCases

        hint
            "FR0072"
            $"This wildcard stands in for exactly %s{hidden}; matching explicitly keeps the match closed, so a future union case raises an incomplete-match warning instead of silently taking this branch."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ExpandWildcard", "Expand a wildcard hiding one or two DU cases", HelpBase)>]
let expandWildcardEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0072" "ExpandWildcard" (fun () ->
        whenChecked ctx (expandWildcardMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ExpandWildcard", "Expand a wildcard hiding one or two DU cases", HelpBase)>]
let expandWildcardCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0072" "ExpandWildcard" (fun () ->
        expandWildcardMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0073 MatchBang ----

let private matchBangMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MatchBangRule.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0073"
            $"'{s.Name}' exists only to be matched; 'match!' binds and matches in one step (F# 4.5+)."
            s.Range
            [
                for range, original, replacement in s.Edits -> fix range original replacement
            ])

[<EditorAnalyzer("MatchBang", "Collapse let!-then-match into match!", HelpBase)>]
let matchBangEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0073" "MatchBang" (fun () ->
        matchBangMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("MatchBang", "Collapse let!-then-match into match!", HelpBase)>]
let matchBangCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0073" "MatchBang" (fun () ->
        matchBangMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0078 WhileBang ----

let private whileBangMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    MatchBangRule.findWhileBang parseTree source
    |> List.map (fun s ->
        hint
            "FR0078"
            $"This mutable-'%s{s.Name}' loop is the F# 8 'while!' idiom spelled out; 'while!' re-evaluates the computation each iteration, replacing all three bindings."
            s.Range
            [
                for range, original, replacement in s.Edits -> fix range original replacement
            ])

[<EditorAnalyzer("WhileBang", "Collapse the mutable-condition loop idiom into while! (F# 8)", HelpBase)>]
let whileBangEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0078" "WhileBang" (fun () ->
        if langVersionAtLeast 8.0 ctx.ProjectOptions then
            whileBangMessages ctx.ParseFileResults.ParseTree ctx.SourceText
            |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText
        else
            [])

[<CliAnalyzer("WhileBang", "Collapse the mutable-condition loop idiom into while! (F# 8)", HelpBase)>]
let whileBangCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0078" "WhileBang" (fun () ->
        if langVersionAtLeast 8.0 ctx.ProjectOptions then
            whileBangMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        else
            [])

// ---- FR0074 NestedRecordUpdate ----

let private nestedRecordUpdateMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    NestedRecordUpdate.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0074"
            $"F# 8 updates nested fields directly: this copy-and-update chain flattens to '%s{s.Path}' path syntax."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("NestedRecordUpdate", "Flatten nested record copy-and-update (F# 8)", HelpBase)>]
let nestedRecordUpdateEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0074" "NestedRecordUpdate" (fun () ->
        if langVersionAtLeast 8.0 ctx.ProjectOptions then
            whenChecked ctx (nestedRecordUpdateMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
            |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText
        else
            [])

[<CliAnalyzer("NestedRecordUpdate", "Flatten nested record copy-and-update (F# 8)", HelpBase)>]
let nestedRecordUpdateCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0074" "NestedRecordUpdate" (fun () ->
        if langVersionAtLeast 8.0 ctx.ProjectOptions then
            nestedRecordUpdateMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        else
            [])

// ---- FR0075 UseBinding ----

let private useBindingMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    UseBinding.find parseTree source checkResults
    |> List.map (fun s ->
        // what the leak costs in this particular scope
        let context =
            match s.Context with
            | Some UseBinding.ScopeContext.EntryPoint ->
                " Nothing disposes it later either: .NET runs no finalizers at process exit, so a writer's last buffer or a transaction's last work is lost; 'use' disposes it before main returns."
            | Some UseBinding.ScopeContext.RequestHandler ->
                " This handler runs once per request, so the leak repeats with every call until the pool behind it runs dry."
            | None -> ""

        // a per-request leak is a likely production defect: it carries
        // warning weight whatever the rule's own priority
        let weigh (m: Message) =
            if s.Context = Some UseBinding.ScopeContext.RequestHandler then
                { m with Severity = Severity.Warning }
            else
                m

        match s.Fix with
        | Some(original, replacement) ->
            hint
                "FR0075"
                $"'%s{s.Name}' is a locally constructed disposable that nothing disposes; 'use' disposes it at scope exit, and every mention stays inside the scope.%s{context}"
                s.Range
                [ fix s.Range original replacement ]
            |> weigh
        | None ->

            let escape = UseBinding.describeEscape s

            hint
                "FR0075"
                $"'%s{s.Name}' is a locally constructed disposable that nothing here disposes; %s{escape}, so decide the owner - 'use' here if the value only gets borrowed, or disposal at the destination.%s{context}"
                s.Range
                []
            |> weigh)

/// FR0075 behind its own switch: the analyzer carries FR0150 too, and
/// one code's config entry must not decide the other's.
let private useBindingMessagesFor
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    if Configuration.isRuleEnabled fileName "FR0075" "UseBinding" then
        useBindingMessages parseTree source checkResults
    else
        []

// ---- FR0150 EscapingUse ----

let private escapingUseMessages
    (fileName: string)
    (offerMove: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    if not (Configuration.isRuleEnabled fileName "FR0150" "UseBinding") then
        []
    else
        UseBinding.findEscapingUse parseTree source checkResults
        |> List.map (fun s ->
            hint
                "FR0150"
                (sprintf
                    "'%s' is disposed when this scope returns, but the %s { } the scope hands back reads it afterwards - the first read past the return throws ObjectDisposedException. The computation owns it: move the `use` inside the %s { }, where it is disposed when the work finishes."
                    s.Name
                    s.Builder
                    s.Builder)
                s.Range
                // moving the construction inside the computation delays it
                // to when the work runs: a timing change the author signs
                // off in the editor, not one a sweep makes
                (if offerMove then
                     s.Edits
                     |> List.map (fun (r, original, replacement) -> fix r original replacement)
                 else
                     []))

[<EditorAnalyzer("UseBinding", "Locally constructed disposables become use-bindings", HelpBase)>]
let useBindingEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0075"; "FR0150" ] "UseBinding" (fun () ->
        whenChecked ctx (fun check ->
            useBindingMessagesFor ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText check
            @ escapingUseMessages ctx.FileName true ctx.ParseFileResults.ParseTree ctx.SourceText check))

[<CliAnalyzer("UseBinding", "Locally constructed disposables become use-bindings", HelpBase)>]
let useBindingCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenAnyEnabled ctx.FileName [ "FR0075"; "FR0150" ] "UseBinding" (fun () ->
        useBindingMessagesFor ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        @ escapingUseMessages ctx.FileName false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0076 MapIgnore ----

let private mapIgnoreMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    MapIgnore.find parseTree source checkResults
    |> List.map (fun s ->
        match s.ReplacementText with
        | Some replacement ->
            hint
                "FR0076"
                $"%s{s.ModuleName}.map allocates a result list just to discard it; iter runs the same calls in the same order without it."
                s.Range
                [ fix s.Range s.OriginalText replacement ]
        | None ->
            hint
                "FR0076"
                "Seq.map is lazy: piping it to ignore evaluates nothing - the mapping never runs. Seq.iter would run the effects; if none are wanted, delete the line."
                s.Range
                [])

[<EditorAnalyzer("MapIgnore", "map-then-ignore pipelines", HelpBase)>]
let mapIgnoreEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0076" "MapIgnore" (fun () ->
        whenChecked ctx (mapIgnoreMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("MapIgnore", "map-then-ignore pipelines", HelpBase)>]
let mapIgnoreCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0076" "MapIgnore" (fun () ->
        mapIgnoreMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0092 FailwithContext ----

// The text of an exception is observable behaviour: tests assert on it
// (FSharp.Data's `at least one global complex element is needed` broke on
// the sweep that rewrote an `internal` function's message) and callers
// match on it. So the fix applies only under --api-changes, where the user
// owns the callers and runs the tests; otherwise this is an advisory note.
let private failwithContextMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    let applies = Visibility.apiChangesAllowed ()
    let index = AstIndex.ofTree parseTree

    // a test's own failwith is an assertion, and the runner names the test
    if SwallowedException.isTestFile index source then
        []
    else
        FailwithContext.find parseTree source checkResults
        |> List.map (fun s ->
            // a test pinning the exact text is the observer of this
            // behaviour. Without --api-changes that is the end of it: the
            // note says where. With it, the message is enriched and the
            // assertion loosened to a prefix check IN THE SAME FIX, as
            // cross-file edits: the two halves apply together or not at
            // all. (The test file used to loosen on its own turn, for any
            // literal a production `failwith` spelled - and a `failwith
            // "Error"` in a doc comment had this repository's own
            // `Assert.Equal("Error", s.LogMethod)` loosened with nothing
            // enriched anywhere.)
            // the test files pinning the text, read FRESH: an earlier pass
            // may have rewritten one since the repository scan, and a stale
            // range would not match its text and hold the whole fix. One
            // that cannot be read now keeps the enrichment out: its
            // assertions cannot be loosened with it
            let assertedIn =
                Configuration.testFilesMentioning fileName s.OriginalText
                |> List.map (fun (testFile, _) ->
                    try
                        testFile, System.IO.File.ReadAllText testFile
                    with _ -> // an unreadable test file vetoes below; fsharpanalyzer: ignore-line FR0055
                        testFile, null)

            // a mention the loosening cannot rewrite - another assertion
            // dialect, or a test stub throwing the same text - keeps the
            // enrichment out even under --api-changes: the test would go red
            let unrewritable =
                assertedIn
                |> List.tryFind (fun (_, text) ->
                    isNull text || not (FailwithContext.everyMentionRewritable text s.OriginalText))

            match assertedIn, unrewritable with
            | (testFile, _) :: _, _ when not applies ->
                hint
                    "FR0092"
                    $"This failure message is a constant, but a test pins its exact text ({System.IO.Path.GetFileName testFile}), so it is left alone. Under --api-changes it would be interpolated with %s{s.FunctionName}'s arguments and the assertion loosened to a prefix check."
                    s.Range
                    []
            | _, Some(testFile, _) ->
                hint
                    "FR0092"
                    $"This failure message is a constant, but {System.IO.Path.GetFileName testFile} mentions its exact text in a form the rewrite cannot loosen to a prefix check (only FsUnit `should equal` and xUnit `Assert.Equal` on an exception's `Message` are), so it is left alone."
                    s.Range
                    []
            | _ ->
                hint
                    "FR0092"
                    $"This failure message is a constant: every occurrence in the log reads the same. Interpolating %s{s.FunctionName}'s arguments says which call produced it - check the values are safe to log first, and that no test asserts on the text."
                    s.Range
                    (if applies then
                         [
                             fix s.Range s.OriginalText s.ReplacementText
                             // `let f = function ... | _ -> failwith`: the wildcard
                             // arm is named in the same fix
                             for r, original, replacement in Option.toList s.PatternEdit do
                                 fix r original replacement
                             // the assertions pinning the text loosen in the
                             // same atomic set
                             for testFile, text in assertedIn do
                                 for r, original, replacement in
                                     FailwithContext.findAssertions
                                         (SourceText.ofString text)
                                         testFile
                                         [ s.OriginalText ] do
                                     fix r original replacement
                         ]
                     else
                         []))

// The fix is an interpolated string, which needs the F# 5 syntax AND an
// FSharp.Core that backs it: on PethostBackup's net48 project with
// FSharp.Core 4.x it compiled to "Feature 'string interpolation' requires
// the F# library for language version 5.0 or greater" and was rolled
// back — the same gate FR0031 and FR0021 already consult.
[<EditorAnalyzer("FailwithContext", "Static failwith messages that could carry their arguments", HelpBase)>]
let failwithContextEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0092" "FailwithContext" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            whenChecked ctx (failwithContextMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
        else
            [])

[<CliAnalyzer("FailwithContext", "Static failwith messages that could carry their arguments", HelpBase)>]
let failwithContextCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0092" "FailwithContext" (fun () ->
        if canInterpolate ctx.FileName ctx.ProjectOptions then
            failwithContextMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        else
            [])

// ---- FR0142 TestReturnsTask ----

let private testReturnsTaskMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    TestReturnsTask.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0142"
            $"Test '{s.Name}' blocks a thread on async work at {s.Sites} site(s); returning the work as a Task lets the framework await it instead."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("TestReturnsTask", "Tests that block on async work return a Task instead", HelpBase)>]
let testReturnsTaskEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0142" "TestReturnsTask" (fun () ->
        if canReturnTask ctx.FileName ctx.ProjectOptions then
            whenChecked ctx (testReturnsTaskMessages ctx.ParseFileResults.ParseTree ctx.SourceText)
            |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText
        else
            [])

[<CliAnalyzer("TestReturnsTask", "Tests that block on async work return a Task instead", HelpBase)>]
let testReturnsTaskCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0142" "TestReturnsTask" (fun () ->
        if canReturnTask ctx.FileName ctx.ProjectOptions then
            testReturnsTaskMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        else
            [])

// ---- FR0143 ScriptLoads ----

let private scriptLoadsMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (projectDiagnostics: FSharp.Compiler.Diagnostics.FSharpDiagnostic[])
    : Message list =
    ScriptLoads.find fileName parseTree projectDiagnostics
    |> List.map (fun s ->
        hint
            "FR0143"
            s.Message
            s.InsertRange
            (match s.InsertText with
             | Some text -> [ fix s.InsertRange "" text ]
             | None -> []))

// the one rule whose input IS a broken compilation: it reads the FS0039
// diagnostics of the whole script compilation, so it needs project
// results, and the apply tool admits it on scripts that do not typecheck
[<EditorAnalyzer("ScriptLoads", "A script #load chain missing a file of the project it loads from", HelpBase)>]
let scriptLoadsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0143" "ScriptLoads" (fun () ->
        match ctx.CheckProjectResults with
        | Some project -> scriptLoadsMessages ctx.FileName ctx.ParseFileResults.ParseTree project.Diagnostics
        | None -> [])

[<CliAnalyzer("ScriptLoads", "A script #load chain missing a file of the project it loads from", HelpBase)>]
let scriptLoadsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0143" "ScriptLoads" (fun () ->
        scriptLoadsMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.CheckProjectResults.Diagnostics)

// ---- FR0144 ScriptReferences ----

let private scriptReferencesMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (options: AnalyzerProjectOptions)
    : Message list =
    ScriptReferences.find fileName parseTree source options.OtherOptions
    // a package reference is resolved by F# 5's `#r "nuget: ..."`, which the
    // .NET Framework fsi.exe does not have: offered only where the script is
    // checked against a language version that can run it
    |> List.filter (fun s -> not s.IsNugetReference || langVersionAtLeast 5.0 options)
    |> List.map (fun s -> hint "FR0144" s.Message s.Range [ fix s.Range s.OriginalText s.ReplacementText ])

// existence on disk is the input, so this runs on a script that does not
// typecheck, like FR0143
[<EditorAnalyzer("ScriptReferences", "A script #r or #I path the package no longer has", HelpBase)>]
let scriptReferencesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0144" "ScriptReferences" (fun () ->
        scriptReferencesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.ProjectOptions)

[<CliAnalyzer("ScriptReferences", "A script #r or #I path the package no longer has", HelpBase)>]
let scriptReferencesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0144" "ScriptReferences" (fun () ->
        scriptReferencesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.ProjectOptions)

// ---- FR0145 RecordFields ----

// deliberately NO hasErrors gate: like FR0077 this rule exists to fix a
// compile error. `applyPlaceholders` is the editor's privilege: a
// placeholder fires when the record is BUILT, so the apply tool takes only
// the fixes whose every default is obvious
let private recordFieldsMessages
    (applyPlaceholders: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    RecordFields.find parseTree source checkResults
    |> List.collect (fun s ->
        let missing = String.concat ", " s.Missing

        let text =
            if s.AllObvious then
                $"This {s.TypeName} leaves {s.Missing.Length} field(s) unassigned ({missing}); the fix adds them with the empty value their types make obvious."
            else
                $"This {s.TypeName} leaves {s.Missing.Length} field(s) unassigned ({missing}); the fix adds them, with a NotImplementedException placeholder where no default is obvious - replace it before the record is built."

        // an editor applies EVERY fix of a message as one action, so two
        // alternatives must be two messages — one message carrying both
        // wrote `X = raise ...; X = false` into a record
        if s.AllObvious then
            [ hint "FR0145" text s.Range [ fix s.Range "" s.InsertText ] ]
        elif applyPlaceholders then
            // the editor's two offers: placeholders that report
            // themselves, or zero values (literal zeros, and
            // Unchecked.defaultof for the rest)
            [
                hint "FR0145" text s.Range [ fix s.Range "" s.InsertText ]
                hint
                    "FR0145"
                    $"Alternative: add the {s.Missing.Length} missing field(s) ({missing}) with zero values - false, 0, \"\", Guid.Empty, Unchecked.defaultof for the rest."
                    s.Range
                    [ fix s.Range "" s.ZeroInsertText ]
            ]
        else
            [ hint "FR0145" text s.Range [] ])

[<EditorAnalyzer("RecordFields", "Add the fields a record expression leaves unassigned", HelpBase)>]
let recordFieldsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0145" "RecordFields" (fun () ->
        whenChecked ctx (recordFieldsMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("RecordFields", "Add the fields a record expression leaves unassigned", HelpBase)>]
let recordFieldsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0145" "RecordFields" (fun () ->
        recordFieldsMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0079 SingleAwaitable ----

let private singleAwaitableMessages
    (offerFixes: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    SingleAwaitable.find parseTree source checkResults
    |> List.map (fun s ->
        let advice =
            if s.CallName = "Async.Parallel" then
                "nothing runs in parallel - run the one computation directly (the result becomes 'T instead of 'T[])"
            elif s.CallName = "Task.WaitAll" then
                "wait on the one task directly with its own Wait() (the blocking stays; FR0049 covers moving it toward async)"
            else
                "await the one task directly (the task keeps its result where WhenAll returns plain Task)"

        hint
            "FR0079"
            $"%s{s.CallName} over a single-element literal adds indirection for nothing; %s{advice}."
            s.Range
            (match s.Fix with
             | Some(r, original, replacement) when offerFixes -> [ fix r original replacement ]
             | _ -> []))

[<EditorAnalyzer("SingleAwaitable", "WhenAll/WaitAll/Parallel over a single awaitable", HelpBase)>]
let singleAwaitableEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0079" "SingleAwaitable" (fun () ->
        whenChecked ctx (singleAwaitableMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("SingleAwaitable", "WhenAll/WaitAll/Parallel over a single awaitable", HelpBase)>]
let singleAwaitableCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0079" "SingleAwaitable" (fun () ->
        singleAwaitableMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0077 ImplementMissing ----

// `offerEmpty`: the editor's second fix, stubs that return the empty value
// of their types instead of raising — a choice for a person, never the
// sweep's: a quiet stub hides the gap the raising one reports
let private implementMissingMessages
    (offerEmpty: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    // deliberately NO hasErrors gate: this rule exists to fix the
    // missing-members compile error
    ImplementMissing.find parseTree source checkResults
    |> List.collect (fun s ->
        let missing = String.concat ", " s.MissingNames

        // two alternatives are two messages: an editor applies every fix
        // of one message together
        [
            hint
                "FR0077"
                $"This object expression is missing %d{s.MissingNames.Length} member(s) of %s{s.InterfaceName} (%s{missing}); the fix stubs them with NotImplementedException so the code compiles and the TODOs are explicit."
                s.Range
                [ fix s.Range "" s.InsertText ]
            if offerEmpty then
                hint
                    "FR0077"
                    $"Alternative: stub the %d{s.MissingNames.Length} missing member(s) (%s{missing}) returning each type's empty value - None, [], 0, \"\", Unchecked.defaultof for the rest."
                    s.Range
                    [ fix s.Range "" s.EmptyInsertText ]
        ])

[<EditorAnalyzer("ImplementMissing", "Stub missing interface members with NotImplementedException", HelpBase)>]
let implementMissingEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0077" "ImplementMissing" (fun () ->
        whenChecked ctx (implementMissingMessages true ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ImplementMissing", "Stub missing interface members with NotImplementedException", HelpBase)>]
let implementMissingCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0077" "ImplementMissing" (fun () ->
        implementMissingMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0080 TabIndentation ----

let private tabIndentationMessages (fileName: string) (source: ISourceText) : Message list =
    // works from source text alone: tab-indented files do not parse
    // (FS1161), and repairing that is the point
    TabIndentation.find fileName source
    |> List.map (fun s ->
        hint
            "FR0080"
            $"TABs are not allowed as F# indentation (FS1161) - pasted code often brings them along; the fix expands each leading TAB to four spaces on all %d{s.Edits.Length} affected line(s)."
            s.Range
            [
                for range, original, replacement in s.Edits -> fix range original replacement
            ])

[<EditorAnalyzer("TabIndentation", "Expand pasted TAB indentation to spaces", HelpBase)>]
let tabIndentationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0080" "TabIndentation" (fun () -> tabIndentationMessages ctx.FileName ctx.SourceText)

[<CliAnalyzer("TabIndentation", "Expand pasted TAB indentation to spaces", HelpBase)>]
let tabIndentationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0080" "TabIndentation" (fun () -> tabIndentationMessages ctx.FileName ctx.SourceText)

// ---- FR0081 PathSeparator ----

let private pathSeparatorMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    PathSeparator.find parseTree source
    |> List.map (fun s ->
        let sep = if s.Separator = "/" then "'/'" else "'\\'"

        hint
            "FR0081"
            $"This concatenation joins path fragments with a hard-coded %s{sep}; Path.Combine handles separators and platform differences (advice: it treats a ROOTED second argument as absolute, and a URL should stay string-joined or use Uri)."
            s.Range
            [])

[<EditorAnalyzer("PathSeparator", "Hand-built path concatenation", HelpBase)>]
let pathSeparatorEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0081" "PathSeparator" (fun () ->
        pathSeparatorMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("PathSeparator", "Hand-built path concatenation", HelpBase)>]
let pathSeparatorCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0081" "PathSeparator" (fun () ->
        pathSeparatorMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0082 / FR0083 / FR0084 / FR0086 RedundantSyntax ----

let private redundantSyntaxMessages
    check
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    let codeOf kind =
        match kind with
        | RedundantSyntax.Kind.AttributeSuffix -> "FR0082", "AttributeSuffix"
        | RedundantSyntax.Kind.AttributeParens -> "FR0083", "AttributeParens"
        | RedundantSyntax.Kind.Backticks -> "FR0084", "RedundantBackticks"
        | RedundantSyntax.Kind.HoleFreeInterpolation -> "FR0086", "HoleFreeInterpolation"

    let messageOf kind =
        match kind with
        | RedundantSyntax.Kind.AttributeSuffix ->
            "The Attribute suffix is redundant; the compiler resolves the short form."
        | RedundantSyntax.Kind.AttributeParens -> "An empty argument list on an attribute says nothing."
        | RedundantSyntax.Kind.Backticks -> "These backticks quote a plain identifier; the quoting does nothing."
        | RedundantSyntax.Kind.HoleFreeInterpolation ->
            "This interpolated string has no holes; a plain string literal says the same with less."

    RedundantSyntax.find check parseTree source
    |> List.choose (fun s ->
        let code, name = codeOf s.Kind

        if Configuration.isRuleEnabled fileName code name then
            Some(hint code (messageOf s.Kind) s.Range [ fix s.Range s.OriginalText s.ReplacementText ])
        else
            None)

[<EditorAnalyzer("RedundantSyntax", "Attribute suffix/parens, backticks, hole-free interpolation", HelpBase)>]
let redundantSyntaxEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                redundantSyntaxMessages ctx.CheckFileResults ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
    }

[<CliAnalyzer("RedundantSyntax", "Attribute suffix/parens, backticks, hole-free interpolation", HelpBase)>]
let redundantSyntaxCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                redundantSyntaxMessages
                    (Some ctx.CheckFileResults)
                    ctx.FileName
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText)
    }

// ---- FR0085 RedundantNew ----

let private redundantNewMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    RedundantNew.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0085"
            $"'new' is conventionally reserved for disposable constructions (the compiler warns the inverse as FS0760); %s{s.TypeName} is not IDisposable, so the keyword is noise."
            s.Range
            [ fix s.Range s.OriginalText "" ])

[<EditorAnalyzer("RedundantNew", "new on non-disposable constructions", HelpBase)>]
let redundantNewEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0085" "RedundantNew" (fun () ->
        whenChecked ctx (redundantNewMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("RedundantNew", "new on non-disposable constructions", HelpBase)>]
let redundantNewCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0085" "RedundantNew" (fun () ->
        redundantNewMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0087 / FR0088 / FR0089 PatternCleanups ----

let private patternCleanupMessages
    (fileName: string)
    (offerFixes: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    let consEnabled = Configuration.isRuleEnabled fileName "FR0087" "ConsListPat"

    let wildEnabled =
        Configuration.isRuleEnabled fileName "FR0088" "RedundantCaseFieldPats"

    let tupleEnabled = Configuration.isRuleEnabled fileName "FR0089" "TupleInList"

    if not (consEnabled || wildEnabled || tupleEnabled) then
        []
    else
        let conses, wilds, tuples = PatternCleanups.find parseTree source checkResults

        [
            if consEnabled then
                for s in conses do
                    hint
                        "FR0087"
                        "The pattern `x :: []` is a one-element list; `[ x ]` says so directly."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ]
            if wildEnabled then
                for s in wilds do
                    hint
                        "FR0088"
                        $"Every field of %s{s.CaseName} is a wildcard; '%s{s.CaseName} _' matches the same and survives field-count changes."
                        s.Range
                        [ fix s.Range s.OriginalText s.ReplacementText ]
            if tupleEnabled then
                for s in tuples do
                    hint
                        "FR0089"
                        $"This literal holds ONE tuple of %d{s.Elements} elements - ',' builds a tuple, ';' separates elements; if a single-tuple collection is intended, ignore or disable this rule."
                        s.Range
                        (if offerFixes then
                             (let (r, original, replacement) = s.Fix in [ fix r original replacement ])
                         else
                             [])
        ]

[<EditorAnalyzer("PatternCleanups", "Cons-of-empty, all-wildcard case fields, tuple-in-list", HelpBase)>]
let patternCleanupsEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                whenChecked
                    ctx
                    (patternCleanupMessages ctx.FileName true ctx.ParseFileResults.ParseTree ctx.SourceText))
    }

[<CliAnalyzer("PatternCleanups", "Cons-of-empty, all-wildcard case fields, tuple-in-list", HelpBase)>]
let patternCleanupsCliAnalyzer (ctx: CliContext) : Async<Message list> =
    async {
        return
            DeepStack.run (fun () ->
                patternCleanupMessages
                    ctx.FileName
                    false
                    ctx.ParseFileResults.ParseTree
                    ctx.SourceText
                    ctx.CheckFileResults)
    }

// ---- FR0021 InterpToString ----

let private interpToStringMessages check (parseTree: ParsedInput) (source: ISourceText) : Message list =
    InterpToString.find check parseTree source
    |> List.map (fun s ->
        hint
            "FR0021"
            "Redundant ToString() inside an interpolated string; interpolation formats the value already."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("InterpToString", "Drop redundant ToString() in interpolated strings", HelpBase)>]
let interpToStringEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0021" "InterpToString" (fun () ->
        interpToStringMessages ctx.CheckFileResults ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("InterpToString", "Drop redundant ToString() in interpolated strings", HelpBase)>]
let interpToStringCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0021" "InterpToString" (fun () ->
        interpToStringMessages (Some ctx.CheckFileResults) ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0101 IndexedLoop ----

let private indexedLoopMessages
    (parseTree: ParsedInput)
    (source: ISourceText)
    (gate: IndexedLoop.SourceGate)
    (check: FSharpCheckFileResults option)
    : Message list =
    // the source must be PROVEN to enumerate in index order: without
    // check results nothing is
    (match check with
     | Some check -> IndexedLoop.findChecked parseTree source gate check
     | None -> [])
    |> List.map (fun s ->
        hint
            "FR0101"
            ($"The index only ever reads '%s{s.CollectionText}.[i]'; iterate '%s{s.CollectionText}' directly.")
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

/// Fable's Rust target has no string enumerator, so in a Fable project a
/// loop over a string keeps its index; the typed tree tells the strings.
let private indexedLoopGate (options: AnalyzerProjectOptions) (check: FSharpCheckFileResults option) =
    if referencesAssembly "Fable.Core" options then
        IndexedLoop.SourceGate.NoStrings check
    else
        IndexedLoop.SourceGate.Any

[<EditorAnalyzer("IndexedLoop", "Index-based loops that only ever index the bound collection", HelpBase)>]
let indexedLoopEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0101" "IndexedLoop" (fun () ->
        indexedLoopMessages
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            (indexedLoopGate ctx.ProjectOptions ctx.CheckFileResults)
            ctx.CheckFileResults)

[<CliAnalyzer("IndexedLoop", "Index-based loops that only ever index the bound collection", HelpBase)>]
let indexedLoopCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0101" "IndexedLoop" (fun () ->
        indexedLoopMessages
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            (indexedLoopGate ctx.ProjectOptions (Some ctx.CheckFileResults))
            (Some ctx.CheckFileResults))

// ---- FR0102 ListIndexing ----

let private listIndexingMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    ListIndexing.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0102"
            (match s.Kind with
             | ListIndexing.AccessKind.Index ->
                 sprintf
                     "Indexing the F# list '%s' is O(i) per access - inside a loop that is quadratic. Iterate it directly, or convert once with List.toArray if random access is needed."
                     s.CollectionText
             | ListIndexing.AccessKind.Length ->
                 sprintf
                     "Reading the F# list '%s''s length walks the whole list - inside a loop that is quadratic. Bind the length once outside the loop, or convert once with List.toArray."
                     s.CollectionText)
            s.Range
            [])

[<EditorAnalyzer("ListIndexing", "Positional indexing into an F# list inside a loop", HelpBase)>]
let listIndexingEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0102" "ListIndexing" (fun () ->
        whenChecked ctx (listIndexingMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("ListIndexing", "Positional indexing into an F# list inside a loop", HelpBase)>]
let listIndexingCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0102" "ListIndexing" (fun () ->
        listIndexingMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0103 TypeTestChain ----

let private typeTestChainMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    TypeTestChain.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0103"
            "This if/elif ladder of type tests can be a match with type-test patterns: one test per branch instead of test-plus-cast, and no unsafe :?> left behind."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("TypeTestChain", "Type-test if-chains rewritten as match", HelpBase)>]
let typeTestChainEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0103" "TypeTestChain" (fun () ->
        typeTestChainMessages ctx.ParseFileResults.ParseTree ctx.SourceText
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("TypeTestChain", "Type-test if-chains rewritten as match", HelpBase)>]
let typeTestChainCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0103" "TypeTestChain" (fun () ->
        typeTestChainMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0104 RecursiveAppend ----

let private recursiveAppendMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    RecursiveAppend.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0104"
            (sprintf
                "'%s' appends one element to '%s' on every recursive call - the accumulator is copied each step, O(n^2) overall. Cons instead ('x :: %s') and List.rev once in the base case, or accumulate into an array when the result is consumed positionally."
                s.FunctionName
                s.AccumulatorName
                s.AccumulatorName)
            s.Range
            [])

[<EditorAnalyzer("RecursiveAppend", "Singleton appends to a recursive accumulator", HelpBase)>]
let recursiveAppendEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0104" "RecursiveAppend" (fun () ->
        recursiveAppendMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RecursiveAppend", "Singleton appends to a recursive accumulator", HelpBase)>]
let recursiveAppendCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0104" "RecursiveAppend" (fun () ->
        recursiveAppendMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0105 CheckedArithmetic ----

let private checkedArithmeticMessages (offerFixes: bool) (parseTree: ParsedInput) (source: ISourceText) : Message list =
    CheckedArithmetic.find parseTree source
    |> List.collect (fun s ->
        let message =
            match s.Kind with
            | CheckedArithmetic.OverflowKind.ScaleFactor ->
                // the literal as SOURCE TEXT: `1_000_000`, `1000000l` (the
                // int32 suffix), a negated `-2147483648` whose magnitude no
                // int32 holds. Parsed as int64 after stripping both, so the
                // note never throws building itself; a text that still
                // does not parse gets the note without the figure
                let digits = s.ConstantText.Replace("_", "").TrimEnd('l', 'L', 'u', 'U', 'y', 's')

                match
                    Int64.TryParse(
                        digits,
                        System.Globalization.NumberStyles.AllowLeadingSign,
                        System.Globalization.CultureInfo.InvariantCulture
                    )
                with
                | true, n when n <> 0L ->
                    sprintf
                        "Multiplying by %s overflows int32 once the other operand passes %d - the seconds-to-microseconds, milliseconds-to-ticks conversion that wraps SILENTLY; widen to int64 (`int64 x * %sL`), or open Checked so it throws instead."
                        s.ConstantText
                        // one times any int32 fits, so the threshold is
                        // never below 1 (the minimum's magnitude is 2^31)
                        (max 1L (int64 Int32.MaxValue / abs n))
                        digits
                | _ ->
                    sprintf
                        "Multiplying by %s overflows int32 once the other operand is large enough - the seconds-to-microseconds, milliseconds-to-ticks conversion that wraps SILENTLY; widen to int64 (`int64 x * %sL`), or open Checked so it throws instead."
                        s.ConstantText
                        digits
            | CheckedArithmetic.OverflowKind.LimitConstant ->
                sprintf
                    "Arithmetic on %s overflows for every operand but zero - F# operators wrap SILENTLY; a wider type, Checked operators, or a comment saying the wraparound is intended."
                    s.ConstantText
            | CheckedArithmetic.OverflowKind.NearLimit ->
                sprintf
                    "Arithmetic on the near-limit constant %s wraps SILENTLY on overflow - F# operators are unchecked by default. Consider `open Microsoft.FSharp.Core.Operators.Checked` in this scope, a wider type (int64/bigint), or a comment saying the wraparound is intended."
                    s.ConstantText

        // the editor's two offers, as two messages: widening keeps the
        // result's meaning, Checked only makes the failure loud
        [
            hint "FR0105" message s.Range []
            if offerFixes then
                match s.WidenFix with
                | Some(r, original, replacement) ->
                    hint "FR0105" $"Fix: widen to int64 - {replacement}." s.Range [ fix r original replacement ]
                | None -> ()

                match s.CheckedFix with
                | Some(r, original, replacement) ->
                    hint
                        "FR0105"
                        $"Alternative: {replacement} - still fails on overflow, but with an OverflowException instead of a wrong number."
                        s.Range
                        [ fix r original replacement ]
                | None -> ()
        ])

[<EditorAnalyzer("CheckedArithmetic", "Unchecked arithmetic on near-limit constants", HelpBase)>]
let checkedArithmeticEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0105" "CheckedArithmetic" (fun () ->
        checkedArithmeticMessages true ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("CheckedArithmetic", "Unchecked arithmetic on near-limit constants", HelpBase)>]
let checkedArithmeticCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0105" "CheckedArithmetic" (fun () ->
        checkedArithmeticMessages false ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0106 SubstringSpan ----

let private substringSpanMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    SubstringSpan.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0106"
            (sprintf
                "This Substring allocates a copy that %s immediately discards - AsSpan %s in place (Parse measured 2.6x, allocation-free; Append 32 B less per call). The span overload is present in this compilation."
                s.ParserName
                s.Verb)
            s.Range
            // a capability fix: on a dual-framework run this may emit an
            // #if NET6_0_OR_GREATER / #else pair instead of the plain swap
            (if CapabilityFix.guardUnavailable () then
                 []
             else
                 [ CapabilityFix.make source s.Range "Substring" "AsSpan" ]))

[<EditorAnalyzer("SubstringSpan", "Parse from a span instead of a Substring copy", HelpBase)>]
let substringSpanEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0106" "SubstringSpan" (fun () ->
        whenChecked ctx (substringSpanMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("SubstringSpan", "Parse from a span instead of a Substring copy", HelpBase)>]
let substringSpanCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0106" "SubstringSpan" (fun () ->
        substringSpanMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0147 QualifiedNames ----

let private qualifiedNamesMessages
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    // how many spellings earn an open: { "FR0147": { "uses": 6, "deepUses": 4 } }
    let uses = Configuration.parameterInt fileName "FR0147" "QualifiedNames" "uses" 6

    let deepUses =
        Configuration.parameterInt fileName "FR0147" "QualifiedNames" "deepUses" 4

    QualifiedNames.find uses deepUses parseTree source checkResults
    |> List.map (fun s ->
        let message =
            match s.Reason with
            | Some reason ->
                $"'{s.Namespace}' is spelled out {s.Uses} time(s) in this file, but an `open {s.Namespace}` cannot go in: {reason}; left as it is."
            | None ->
                $"'{s.Namespace}' is spelled out {s.Uses} time(s) in this file; one `open {s.Namespace}` after the existing opens shortens every use."

        hint
            "FR0147"
            message
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("QualifiedNames", "Repeated qualified names become an open", HelpBase)>]
let qualifiedNamesEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0147" "QualifiedNames" (fun () ->
        whenChecked ctx (qualifiedNamesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("QualifiedNames", "Repeated qualified names become an open", HelpBase)>]
let qualifiedNamesCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0147" "QualifiedNames" (fun () ->
        qualifiedNamesMessages ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0159 IntDivisionToFloat ----

let private intDivisionMessages
    (offerFixes: bool)
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    // a literal operand, or a dividend that is a product, may mean the
    // truncation (Kasino centres on `float (screenW / 2)`, FsLemming maps a
    // minimap with `float (x * mw / tw)`), so a sweep passes those by unless
    // asked (`{ "FR0159": { "all": true } }`); the editor shows them too
    let all =
        offerFixes
        || Configuration.parameterBool fileName "FR0159" "IntDivisionToFloat" "all" false

    IntDivisionToFloat.find parseTree source checkResults
    |> List.choose (fun s ->
        if s.LikelyMeant && not all then
            None
        else
            // the editor offers the rewrite; a sweep never applies it — an
            // integer division into a floating target is occasionally meant
            // (a page count, whole kilobytes), and the C# twin (CR0168)
            // draws the same line
            let fixes =
                if offerFixes then
                    [ fix s.Range s.OriginalText s.ReplacementText ]
                else
                    []

            let message =
                if s.LikelyMeant then
                    $"'{s.OriginalText}' divides as integers first - the quotient is truncated before `{s.Conversion}` widens it; if the whole-number quotient is the intent (a unit conversion, a pixel centre, a coordinate scaled by a ratio) this is right as it is, otherwise convert the operands, then divide: `{s.ReplacementText}`."
                else
                    $"'{s.OriginalText}' divides as integers first - the quotient is truncated before `{s.Conversion}` widens it, and the fraction the conversion was there to keep is gone; convert the operands, then divide: `{s.ReplacementText}`."

            Some(hint "FR0159" message s.Range fixes))

[<EditorAnalyzer("IntDivisionToFloat", "A float conversion of an integer division truncates first", HelpBase)>]
let intDivisionEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0159" "IntDivisionToFloat" (fun () ->
        whenChecked ctx (intDivisionMessages true ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("IntDivisionToFloat", "A float conversion of an integer division truncates first", HelpBase)>]
let intDivisionCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0159" "IntDivisionToFloat" (fun () ->
        intDivisionMessages false ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0160 LostInnerException ----

let private lostInnerMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    LostInnerException.find parseTree source checkResults
    |> List.map (fun s ->
        match s.Edits with
        | [] when LostInnerException.isFailureFunction s.Raised ->
            hint
                "FR0160"
                $"`{s.Raised}` in a handler raises a new exception and drops the one it caught - no InnerException, no original stack trace; `raise (Exception(message, {s.Binder}))` keeps the cause, or the exception type's own (message, inner) constructor."
                s.Range
                []
        | [] ->
            hint
                "FR0160"
                $"'{s.Raised}' is raised in place of the exception the handler caught, which it does not carry - no InnerException, no original stack trace; pass the caught exception as the constructor's last argument."
                s.Range
                []
        | edits ->
            hint
                "FR0160"
                $"'{s.Raised}' is raised in place of the exception the handler caught, which it does not carry - no InnerException, no original stack trace; '{s.Raised}' has a constructor taking it last."
                s.Range
                (edits |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("LostInnerException",
                 "A handler raising a new exception keeps the one it caught as the inner",
                 HelpBase)>]
let lostInnerEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0160" "LostInnerException" (fun () ->
        whenChecked ctx (lostInnerMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("LostInnerException", "A handler raising a new exception keeps the one it caught as the inner", HelpBase)>]
let lostInnerCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0160" "LostInnerException" (fun () ->
        lostInnerMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0161 StructPropertyMutation ----

let private structPropertyMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    StructPropertyMutation.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0161"
            $"'{s.PropertyText}' is a property returning a struct: `.{s.Method}` mutates the copy the getter handed out and the stored value never changes; copy it to a `let mutable`, mutate that and store it back, or make the type a class."
            s.Range
            [])

[<EditorAnalyzer("StructPropertyMutation", "A mutating method on a struct a property returns mutates a copy", HelpBase)>]
let structPropertyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0161" "StructPropertyMutation" (fun () ->
        whenChecked ctx (structPropertyMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("StructPropertyMutation", "A mutating method on a struct a property returns mutates a copy", HelpBase)>]
let structPropertyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0161" "StructPropertyMutation" (fun () ->
        structPropertyMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0162 LazyInit ----

let private lazyInitMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    LazyInit.find parseTree source
    |> List.map (fun s ->
        hint
            "FR0162"
            $"'{s.Name}' is a shared mutable filled by check-then-assign (line {s.AssignmentRange.StartLine}): two threads that both find it empty both run the factory, and a reader between the two stores can see a half-built value; `let {s.Name} = lazy (...)`, read as `{s.Name}.Value`, runs the factory once and is thread-safe by default."
            s.Range
            [])

[<EditorAnalyzer("LazyInit", "Check-then-assign on a shared mutable is a racing Lazy", HelpBase)>]
let lazyInitEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0162" "LazyInit" (fun () ->
        lazyInitMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("LazyInit", "Check-then-assign on a shared mutable is a racing Lazy", HelpBase)>]
let lazyInitCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0162" "LazyInit" (fun () ->
        lazyInitMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0163 DroppedTimer ----

let private droppedTimerMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    DroppedTimer.find parseTree source checkResults
    |> List.map (fun s ->
        hint
            "FR0163"
            "This System.Threading.Timer is constructed and dropped: nothing references it, so the next garbage collection finalizes it and the callbacks stop - bind it (`use` for the scope it should fire in, a `let` or a field for longer) for as long as it should run."
            s.Range
            [])

[<EditorAnalyzer("DroppedTimer", "An unreferenced System.Threading.Timer is collected mid-flight", HelpBase)>]
let droppedTimerEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0163" "DroppedTimer" (fun () ->
        whenChecked ctx (droppedTimerMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("DroppedTimer", "An unreferenced System.Threading.Timer is collected mid-flight", HelpBase)>]
let droppedTimerCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0163" "DroppedTimer" (fun () ->
        droppedTimerMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0164 EnumerationMutation ----

let private enumerationMutationMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    EnumerationMutation.find parseTree source checkResults
    |> List.map (fun s ->
        match s.Filter with
        | Some(r, original, replacement) ->
            // the filter shape is the list's own RemoveAll: one pass, no
            // snapshot (CR0171's first fix)
            hint
                "FR0164"
                $"'{s.Collection}' is edited ({s.Mutation}) inside a `for` loop over itself, which throws InvalidOperationException at the next step - and only on the runs that take the branch; the loop is a filter: `{replacement}`."
                r
                [ fix r original replacement ]
        | None ->
            hint
                "FR0164"
                $"'{s.Collection}' is edited ({s.Mutation}) inside a `for` loop over itself, which throws InvalidOperationException at the next step - and only on the runs that take the branch; walk a snapshot: `for ... in {s.ReplacementText} do`."
                s.Range
                [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("EnumerationMutation", "A collection edited inside a for loop over itself throws", HelpBase)>]
let enumerationMutationEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0164" "EnumerationMutation" (fun () ->
        whenChecked ctx (enumerationMutationMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("EnumerationMutation", "A collection edited inside a for loop over itself throws", HelpBase)>]
let enumerationMutationCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0164" "EnumerationMutation" (fun () ->
        enumerationMutationMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0165 DateTimeKindMix ----

let private dateTimeKindMixMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    // a test pins its clocks on purpose (CR0169 stands down the same way)
    if AstIndex.isTestFile (AstIndex.ofTree parseTree) source then
        []
    else
        DateTimeKindMix.find parseTree source checkResults
        |> List.map (fun (s: DateTimeKindMix.Suggestion) ->
            hint
                "FR0165"
                $"'{s.LocalText}' is local time and '{s.UtcText}' is UTC: the two differ by the machine's UTC offset, so this `{s.Operation}` flips with the timezone and twice a year with daylight saving; use one kind on both sides - `DateTime.UtcNow` throughout, or `.ToUniversalTime()` on the local one."
                s.Range
                [])

[<EditorAnalyzer("DateTimeKindMix", "A local DateTime compared with a UTC one", HelpBase)>]
let dateTimeKindMixEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0165" "DateTimeKindMix" (fun () ->
        whenChecked ctx (dateTimeKindMixMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("DateTimeKindMix", "A local DateTime compared with a UTC one", HelpBase)>]
let dateTimeKindMixCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0165" "DateTimeKindMix" (fun () ->
        dateTimeKindMixMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0166 PrefixCompare ----

let private prefixCompareMessages
    (offerFixes: bool)
    (tolerantSlicing: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    PrefixCompare.find tolerantSlicing parseTree source checkResults
    |> List.map (fun (s: PrefixCompare.Suggestion) ->
        // a slice, or a Substring under a length guard, is the same answer
        // on every input and a sweep applies it; a bare Substring throws on
        // a short string where StartsWith answers false, so only the
        // editor offers that one (a capability fix either way: the
        // modern-framework gate is what admitted it)
        let fixes =
            if (s.Exact || offerFixes) && not (CapabilityFix.guardUnavailable ()) then
                [ CapabilityFix.make source s.Range s.OriginalText s.ReplacementText ]
            else
                []

        let tail =
            if s.Exact then
                ""
            else
                " (a string shorter than the literal throws here and answers false there - apply once that cannot happen, or guard with `.Length`)"

        hint
            "FR0166"
            $"'{s.OriginalText}' cuts a copy of the string only to compare it - `{s.ReplacementText}` compares in place (measured 4.5 => 1.9 ns, allocation-free; F#'s `=` on strings is ordinal, and so is the {s.Method}){tail}."
            s.Range
            fixes)

[<EditorAnalyzer("PrefixCompare",
                 "A prefix or suffix cut out to compare with a literal is StartsWith/EndsWith",
                 HelpBase)>]
let prefixCompareEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0166" "PrefixCompare" (fun () ->
        // a slice clamps only under FSharp.Core 5+ (FS-1077); under an older
        // one it throws like a Substring and needs the same guard
        whenChecked
            ctx
            (prefixCompareMessages
                true
                (fsharpCoreAtLeast 5 ctx.FileName ctx.ProjectOptions)
                ctx.ParseFileResults.ParseTree
                ctx.SourceText))

[<CliAnalyzer("PrefixCompare", "A prefix or suffix cut out to compare with a literal is StartsWith/EndsWith", HelpBase)>]
let prefixCompareCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0166" "PrefixCompare" (fun () ->
        prefixCompareMessages
            false
            (fsharpCoreAtLeast 5 ctx.FileName ctx.ProjectOptions)
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

// ---- FR0167 CharArrayCopy ----

/// `nonNull` is FSharp.Core 9's, and on a non-nullable `string` under
/// `--checknulls` it warns FS3262 ("You can remove this `nonNull`
/// assertion"): there the String twins stay the editor's offer.
let private checksNulls (options: AnalyzerProjectOptions) =
    options.OtherOptions
    |> List.exists (fun (arg: string) -> arg = "--checknulls" || arg = "--checknulls+")

let private charArrayCopyMessages
    (offerFixes: bool)
    (nonNullAvailable: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    CharArrayCopy.findWith nonNullAvailable parseTree source checkResults
    |> List.map (fun (s: CharArrayCopy.Suggestion) ->
        // the `for` throws on a null string on both sides, and so does a
        // String function over `nonNull s`: a sweep applies those; the bare
        // String functions treat null as empty where the copy threw, so
        // only the editor offers them
        let fixes =
            if (s.Exact || offerFixes) && not (CapabilityFix.guardUnavailable ()) then
                [ CapabilityFix.make source s.Range s.OriginalText s.ReplacementText ]
            else
                []

        let message =
            if s.Consumer = "for" then
                $"'{s.OriginalText}' copies the whole string into an array the loop reads once - a string is already a sequence of its characters, and `for c in {s.ReplacementText} do` walks it by index without the copy (measured 13.4 => 9.4 ns, 72 => 0 B)."
            elif s.Exact then
                $"'{s.OriginalText}' copies the whole string into an array that is read once - `{s.ReplacementText}` walks the string itself, by index, without the copy (measured 9.2 => 4.3 ns, 72 => 0 B); `nonNull` throws on a null string as the copy did."
            else
                $"'{s.OriginalText}' copies the whole string into an array that is read once - `{s.ReplacementText}` walks the string itself, by index, without the copy (measured 9.2 => 4.3 ns, 72 => 0 B); a null string throws here and reads as empty there, so apply once that cannot happen."

        hint "FR0167" message s.Range fixes)

[<EditorAnalyzer("CharArrayCopy", "A ToCharArray copy that is only read once", HelpBase)>]
let charArrayCopyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0167" "CharArrayCopy" (fun () ->
        whenChecked
            ctx
            (charArrayCopyMessages
                true
                (fsharpCoreAtLeast 9 ctx.FileName ctx.ProjectOptions
                 && not (checksNulls ctx.ProjectOptions))
                ctx.ParseFileResults.ParseTree
                ctx.SourceText))

[<CliAnalyzer("CharArrayCopy", "A ToCharArray copy that is only read once", HelpBase)>]
let charArrayCopyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0167" "CharArrayCopy" (fun () ->
        charArrayCopyMessages
            false
            (fsharpCoreAtLeast 9 ctx.FileName ctx.ProjectOptions
             && not (checksNulls ctx.ProjectOptions))
            ctx.ParseFileResults.ParseTree
            ctx.SourceText
            ctx.CheckFileResults)

// ---- FR0172 ListHeadPattern ----

let private listHeadPatternMessages (parseTree: ParsedInput) (source: ISourceText) : Message list =
    ListHeadPattern.find parseTree source
    |> List.map (fun (s: ListHeadPattern.Suggestion) ->
        // an earlier unguarded `[]` arm (and `[_]` for a second element)
        // already keeps the short lists out of this arm, so the cons
        // pattern matches exactly the lists the name did and a sweep
        // applies it
        hint
            "FR0172"
            $"'{s.Name}' binds the whole list and the arm reads it only by position - `| {s.Pattern} ->` names the elements the arm uses, and the compiler's exhaustiveness check stands in for the ArgumentException a list index raises on a shorter list."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ListHeadPattern", "A match arm indexing the list it bound is a cons pattern", HelpBase)>]
let listHeadPatternEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0172" "ListHeadPattern" (fun () ->
        listHeadPatternMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ListHeadPattern", "A match arm indexing the list it bound is a cons pattern", HelpBase)>]
let listHeadPatternCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0172" "ListHeadPattern" (fun () ->
        listHeadPatternMessages ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0173 RangeMap ----

let private rangeMapMessages
    (offerFixes: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    RangeMap.find parseTree source checkResults
    |> List.map (fun (s: RangeMap.Suggestion) ->
        // `[| 0 .. n - 1 |]` with a negative `n` is the empty range where
        // `init` raises ArgumentException; a count not proven non-negative
        // is spelled `max 0 n`, which gives the empty result back, so the
        // fix is exact for every count and the sweep applies it too
        ignore offerFixes
        let fixes = [ fix s.Range s.OriginalText s.ReplacementText ]

        let caveat =
            if s.CountProven then
                ""
            else
                " (`max 0` keeps a negative count's empty result, as the range gave)"

        hint
            "FR0173"
            $"This range is built only to be mapped over - it allocates a second collection the size of the result to have something to walk. `{s.ReplacementText}` builds the result and nothing else{caveat}."
            s.Range
            fixes)

// the rewrite discards the range's own text, so a comment written inside
// what it replaces would be deleted with it
[<EditorAnalyzer("RangeMap", "A range built only to be mapped over is init", HelpBase)>]
let rangeMapEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0173" "RangeMap" (fun () ->
        whenChecked ctx (rangeMapMessages true ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("RangeMap", "A range built only to be mapped over is init", HelpBase)>]
let rangeMapCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0173" "RangeMap" (fun () ->
        rangeMapMessages false ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0174 QueryCopy ----

let private queryCopyMessages
    (offerFixes: bool)
    (fileName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    checkResults
    : Message list =
    // the pipeline shape is the author's visible choice of where the rows
    // come into memory; a knob takes it too:
    //     { "FR0174": { "pipelines": true } }
    let pipelines =
        Configuration.parameterBool fileName "FR0174" "QueryCopy" "pipelines" false

    QueryCopy.find pipelines parseTree source checkResults
    |> List.map (fun (s: QueryCopy.Suggestion) ->
        // a string, decimal, date or nullable comparison is translated but
        // answered under the server's rules (collation, scale, NULL): the
        // editor offers the move, a sweep leaves the note
        // a chain whose new type (List where it was IEnumerable) could bind
        // differently is the editor's offer too
        let fixes =
            if s.Fixable && ((s.Fidelity = QueryCopy.Exact && s.TypeStable) || offerFixes) then
                [ fix s.Range s.OriginalText s.ReplacementText ]
            else
                []

        let caveat =
            (match s.Fidelity, s.Fixable with
             | QueryCopy.Near, _ ->
                 " The query compares a string, decimal, date or nullable column under its own rules (collation, scale, NULL), so check the translation first; a sweep leaves this one alone."
             | QueryCopy.Exact, false -> " (`open System.Linq` spells the query's `Where`/`Select`.)"
             | QueryCopy.Exact, true -> "")
            + (if s.TypeStable then
                   ""
               else
                   " The chain becomes a List where it was an IEnumerable, so check what it binds to; a sweep leaves this one alone.")

        hint
            "FR0174"
            $"'{s.CopyName}' loads every row of the query before '{s.Stages}' runs in memory: run it in the query and copy after, so the database filters and sends only what is asked for.{caveat}"
            s.Range
            fixes)

// the rewrite moves the stages' own text, so a comment inside the moved
// span would move with it - but one between the copy and the stages goes
[<EditorAnalyzer("QueryCopy", "A query copied before Where/Select runs them in the query", HelpBase)>]
let queryCopyEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0174" "QueryCopy" (fun () ->
        whenChecked ctx (queryCopyMessages true ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText)
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("QueryCopy", "A query copied before Where/Select runs them in the query", HelpBase)>]
let queryCopyCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0174" "QueryCopy" (fun () ->
        queryCopyMessages false ctx.FileName ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults
        |> commentSafeOnly ctx.ParseFileResults.ParseTree ctx.SourceText)

// ---- FR0169 SeqEnumeratedTwice ----

let private seqEnumeratedTwiceMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    SeqEnumeratedTwice.find parseTree source checkResults
    |> List.map (fun (s: SeqEnumeratedTwice.Suggestion) ->
        hint
            "FR0169"
            $"'{s.ParameterName}' is enumerated here and again at line {s.SecondLine}: a seq may be a query or a generator, run again from the start each time - materialise it once (`List.ofSeq`/`Array.ofSeq`) before the first use, or read it in one pass."
            s.Range
            [])

[<EditorAnalyzer("SeqEnumeratedTwice", "A seq parameter or local enumerated twice on one path", HelpBase)>]
let seqEnumeratedTwiceEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0169" "SeqEnumeratedTwice" (fun () ->
        whenChecked ctx (seqEnumeratedTwiceMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("SeqEnumeratedTwice", "A seq parameter or local enumerated twice on one path", HelpBase)>]
let seqEnumeratedTwiceCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0169" "SeqEnumeratedTwice" (fun () ->
        seqEnumeratedTwiceMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0170 DictKeysLoop ----

let private dictKeysLoopMessages (parseTree: ParsedInput) (source: ISourceText) checkResults : Message list =
    DictKeysLoop.find parseTree source checkResults
    |> List.map (fun (s: DictKeysLoop.Suggestion) ->
        hint
            "FR0170"
            $"This loop walks the keys and looks each one up again (`.[{s.KeyName}]` hashes and probes per iteration) for a value the enumerator already holds; `for KeyValue({s.KeyName}, {s.ValueName}) in ...` reads the pair, and every lookup in the body becomes `{s.ValueName}`."
            s.Range
            (s.Edits
             |> List.map (fun (r, original, replacement) -> fix r original replacement)))

[<EditorAnalyzer("DictKeysLoop", "A loop over a dictionary's keys that looks every key up again", HelpBase)>]
let dictKeysLoopEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0170" "DictKeysLoop" (fun () ->
        whenChecked ctx (dictKeysLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText))

[<CliAnalyzer("DictKeysLoop", "A loop over a dictionary's keys that looks every key up again", HelpBase)>]
let dictKeysLoopCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0170" "DictKeysLoop" (fun () ->
        dictKeysLoopMessages ctx.ParseFileResults.ParseTree ctx.SourceText ctx.CheckFileResults)

// ---- FR0171 ByteStringLiteral ----

let private byteStringLiteralMessages
    (check: FSharpCheckFileResults option)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Message list =
    ByteStringLiteral.findWith check parseTree source
    |> List.map (fun (s: ByteStringLiteral.Suggestion) ->
        hint
            "FR0171"
            $"Encoding.{s.EncodingName}.GetBytes runs the encoder over this ASCII literal on every call; `{s.ReplacementText}` is the same bytes as compiled data - no encoder, the same byte[]."
            s.Range
            [ fix s.Range s.OriginalText s.ReplacementText ])

[<EditorAnalyzer("ByteStringLiteral", "An ASCII literal encoded to bytes at run time is a byte string literal", HelpBase)>]
let byteStringLiteralEditorAnalyzer (ctx: EditorContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0171" "ByteStringLiteral" (fun () ->
        byteStringLiteralMessages ctx.CheckFileResults ctx.ParseFileResults.ParseTree ctx.SourceText)

[<CliAnalyzer("ByteStringLiteral", "An ASCII literal encoded to bytes at run time is a byte string literal", HelpBase)>]
let byteStringLiteralCliAnalyzer (ctx: CliContext) : Async<Message list> =
    whenEnabled ctx.FileName "FR0171" "ByteStringLiteral" (fun () ->
        byteStringLiteralMessages (Some ctx.CheckFileResults) ctx.ParseFileResults.ParseTree ctx.SourceText)
