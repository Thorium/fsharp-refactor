/// Regressions from the GitHub issues #1-#6 (a run over a ~370-file Fable
/// codebase, 0.8.33/0.8.34): FR0147 opening a namespace a partial path also
/// reaches, FR0162 on a cache that resets, rules whose .NET reasoning does
/// not hold under Fable, the analyzers `--codes` leaves out, FR0015's names,
/// FR0168's layout and Fantomas's call style. FR0006's stacked insertions
/// and the narrower later passes are the tool's, in the end-to-end test at
/// the bottom.
/// In the "ProjectSources" collection: some tests set the process-wide
/// analysis scope (Scope.set), which must not run beside another test's.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.GithubIssueTests

open System
open System.IO
open System.Text.RegularExpressions
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- #1: FR0147 and partial paths ----

/// FR0147's suggestions for B, compiled after A.
let private qualifiedIn (sourceA: string) (sourceB: string) =
    let tree, sourceText, checkResults = parseAndCheckSecond sourceA sourceB
    QualifiedNames.find 3 2 tree sourceText checkResults

[<Fact>]
let ``FR0147: a user namespace Core is not opened, since open Core also reaches Microsoft.FSharp.Core`` () =
    // `open Core` opens BOTH, re-opens Operators over the user's `tan`, and
    // FS0893 rejects the partial path
    let a =
        "module Core.Validation\n\nlet nonEmpty (s: string) = s <> \"\"\nlet short (s: string) = s.Length < 10\n"

    let b =
        "module App\n\nlet a = Core.Validation.nonEmpty \"x\"\nlet b = Core.Validation.short \"x\"\nlet c = Core.Validation.nonEmpty \"y\"\n"

    let s = qualifiedIn a b |> List.find (fun s -> s.Namespace = "Core")
    Assert.Empty s.Edits
    Assert.Contains("Microsoft.FSharp.Core", s.Reason.Value)

[<Fact>]
let ``FR0147: a user namespace IO is not opened under open System`` () =
    let a = "namespace IO\n\nmodule Files =\n    let one = 1\n    let two = 2\n"

    let b =
        "module App\n\nopen System\n\nlet a = IO.Files.one\nlet b = IO.Files.two\nlet c = IO.Files.one + IO.Files.two\n"

    let s = qualifiedIn a b |> List.find (fun s -> s.Namespace = "IO")
    Assert.Empty s.Edits
    Assert.Contains("System.IO", s.Reason.Value)

[<Fact>]
let ``FR0147: a user namespace no open can reach elsewhere still gets its open`` () =
    let a = "module Billing.Invoices\n\nlet total (x: int) = x * 2\n"

    let b =
        "module App\n\nopen System\n\nlet a = Billing.Invoices.total 1\nlet b = Billing.Invoices.total 2\nlet c = Billing.Invoices.total 3\n"

    let s = qualifiedIn a b |> List.find (fun s -> s.Namespace = "Billing")
    Assert.True(s.Reason.IsNone, $"%A{s.Reason}")
    Assert.NotEmpty s.Edits

// ---- a CLI context whose project also references Fable assemblies ----

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

let private freshDir (tag: string) =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", $"{tag}-{Guid.NewGuid():N}")

    Directory.CreateDirectory dir |> ignore
    dir

/// A script context typechecked as it stands, whose PROJECT OPTIONS also
/// carry the given references - which is all the Fable gates read, and
/// what a Fable project's MSBuild arguments hold (transitive packages
/// included).
let private contextIn (dir: string) (references: string list) (source: string) : CliContext =
    let fileName = Path.Combine(dir, "Code.fsx")
    File.WriteAllText(fileName, source)
    let sourceText = SourceText.ofString source

    let options, _ =
        checker.GetProjectOptionsFromScript(fileName, sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously

    let parseResults, answer =
        checker.ParseAndCheckFileInProject(fileName, 0, sourceText, options)
        |> Async.RunSynchronously

    let checkResults =
        match answer with
        | FSharpCheckFileAnswer.Succeeded r -> r
        | FSharpCheckFileAnswer.Aborted -> failwith $"typechecking aborted for {fileName}"

    let references =
        references
        |> List.map (fun r -> "-r:" + Path.Combine(dir, r + ".dll"))
        |> Array.ofList

    {
        FileName = fileName
        SourceText = sourceText
        ParseFileResults = parseResults
        CheckFileResults = checkResults
        TypedTree = checkResults.ImplementationFile
        CheckProjectResults = projectResults
        ProjectOptions =
            AnalyzerProjectOptions.BackgroundCompilerOptions
                { options with
                    OtherOptions = Array.append options.OtherOptions references
                }
        AnalyzerIgnoreRanges = Map.empty
    }

let private contextWith (references: string list) (source: string) =
    contextIn (freshDir "gh") references source

let private run (analyzer: CliContext -> Async<Message list>) (ctx: CliContext) = analyzer ctx |> Async.RunSynchronously

let private ofCode (code: string) (messages: Message list) =
    messages |> List.filter (fun m -> m.Code = code)

let private fableCore = [ "Fable.Core" ]

/// The ASSEMBLY names a browser project's compiler arguments carry: the
/// Fable.Browser.Dom package ships Browser.Dom.dll, without the prefix.
let private fableBrowser = [ "Fable.Core"; "Browser.Dom"; "Browser.Event" ]

// ---- #3: FR0162 on a cache that resets ----

[<Literal>]
let private inFlightSource =
    "module InFlight\n\nopen System.Threading.Tasks\n\nlet mutable private inFlight: Task<int> option = None\n\nlet ensure (start: unit -> Task<int>) : Task<int> =\n    match inFlight with\n    | Some t -> t\n    | None ->\n        let t = start ()\n        inFlight <- Some t\n        t.ContinueWith(fun (_: Task<int>) -> inFlight <- None) |> ignore\n        t\n"

[<Fact>]
let ``FR0162: a slot reset to None once the task settles is no Lazy`` () =
    let tree, source = parse inFlightSource
    Assert.Empty(LazyInit.find tree source)

[<Fact>]
let ``FR0162: a store inside a lambda under the None arm is not guarded by it`` () =
    let source =
        "module M\n\nopen System.Threading.Tasks\n\nlet mutable private cache: int option = None\n\nlet get (start: unit -> Task<int>) =\n    match cache with\n    | Some v -> v\n    | None ->\n        start().ContinueWith(fun (t: Task<int>) -> cache <- Some t.Result) |> ignore\n        0\n"

    let tree, text = parse source
    Assert.Empty(LazyInit.find tree text)

[<Literal>]
let private racingCacheSource =
    "module M\n\nlet mutable private cache: string option = None\n\nlet get () =\n    match cache with\n    | Some c -> c\n    | None ->\n        let c = \"loaded\"\n        cache <- Some c\n        c\n"

[<Fact>]
let ``FR0162: the plain check-then-assign still gets its note`` () =
    let tree, text = parse racingCacheSource
    Assert.Single(LazyInit.find tree text) |> ignore

[<Fact>]
let ``FR0162: a JavaScript-bound Fable project gets no note - one thread`` () =
    Assert.Empty(ofCode "FR0162" (run Analyzers.lazyInitCliAnalyzer (contextWith fableBrowser racingCacheSource)))

[<Fact>]
let ``FR0162: Fable.Core alone keeps the note - the Rust and Python targets have threads`` () =
    Assert.NotEmpty(ofCode "FR0162" (run Analyzers.lazyInitCliAnalyzer (contextWith fableCore racingCacheSource)))

// ---- #4: the rules whose .NET reasoning Fable changes ----

[<Fact>]
let ``FR0121: in a browser DateTime.Today is the user's own date`` () =
    let source =
        "module M\n\nopen System\n\nlet today () = DateTime.Today\nlet cut () = DateTime.UtcNow.Date\n"

    let messages =
        ofCode "FR0121" (run Analyzers.dateTimeCliAnalyzer (contextWith fableBrowser source))

    // the UTC cut is nobody's midnight in a browser too
    let only = Assert.Single messages
    Assert.Contains("UtcNow", only.Message)

[<Fact>]
let ``FR0121: a Fable project that is no browser keeps the Today note`` () =
    let source = "module M\n\nopen System\n\nlet today () = DateTime.Today\n"
    Assert.NotEmpty(ofCode "FR0121" (run Analyzers.dateTimeCliAnalyzer (contextWith fableCore source)))

[<Fact>]
let ``FR0055: JavaScript's async swallows no cancellation, and the note does not claim it`` () =
    let source =
        "module M\n\nlet tryRun (f: unit -> unit) =\n    try f () with _ -> ()\n"

    let fable =
        ofCode "FR0055" (run Analyzers.swallowedExceptionCliAnalyzer (contextWith fableBrowser source))

    let dotnet =
        ofCode "FR0055" (run Analyzers.swallowedExceptionCliAnalyzer (contextWith [] source))

    Assert.DoesNotContain("cancellation", (List.exactlyOne fable).Message)
    Assert.Contains("cancellation and programming errors", (List.exactlyOne dotnet).Message)

[<Fact>]
let ``FR0038: the culture note stays quiet under Fable, whose strings compare ordinally`` () =
    let source = "module M\n\nlet space (s: string) = s.IndexOf(\" \")\n"
    Assert.Empty(ofCode "FR0038" (run Analyzers.charOverloadCliAnalyzer (contextWith fableCore source)))
    Assert.NotEmpty(ofCode "FR0038" (run Analyzers.charOverloadCliAnalyzer (contextWith [] source)))

[<Fact>]
let ``FR0130: a Fable project's public value keeps its export`` () =
    let source =
        "module Consts\n\nlet maxItems = 25\nlet private minItems = 1\nlet total () = maxItems + minItems\n"

    let messages =
        ofCode "FR0130" (run Analyzers.literalConstCliAnalyzer (contextWith fableCore source))
        |> List.map (fun m -> m.Message)

    Assert.Contains(messages, fun m -> m.Contains "'minItems'")
    Assert.DoesNotContain(messages, fun m -> m.Contains "'maxItems'")

[<Fact>]
let ``FR0035: a two-element literal is probed faster than any set`` () =
    let source =
        "module M\n\nlet private kinds = [ \"a\"; \"b\" ]\n\nlet keep (xs: string list) = xs |> List.filter (fun x -> List.contains x kinds)\n"

    Assert.Empty(ofCode "FR0035" (run Analyzers.loopPerfCliAnalyzer (contextWith [] source)))

/// FR0035's fix texts for a private literal of `n` string elements.
let private containsFixes (n: int) =
    let items = [ for i in 1..n -> $"\"k{i}\"" ] |> String.concat "; "

    let source =
        $"module M\n\nlet private kinds = [ {items} ]\n\nlet keep (xs: string list) = xs |> List.filter (fun x -> List.contains x kinds)\n"

    ofCode "FR0035" (run Analyzers.loopPerfCliAnalyzer (contextWith [] source))
    |> List.collect (fun m -> m.Fixes |> List.map (fun f -> f.ToText))

[<Fact>]
let ``FR0035: seven elements stay a list, ten take the HashSet companion, sixteen convert to a Set`` () =
    // a HashSet pays from about eight elements, an F# Set from about twelve
    // to twenty
    Assert.Empty(containsFixes 7)

    let ten = containsFixes 10
    Assert.Contains(ten, fun t -> t.Contains "kindsProbeSet")
    Assert.DoesNotContain(ten, fun t -> t.Contains "Set.ofList")

    Assert.Contains(containsFixes 16, fun t -> t.Contains "Set.ofList")

[<Fact>]
let ``LoopPerf.literalSize counts written-out elements only`` () =
    let tree, _ =
        parse
            "module M\n\nlet a = [ 1; 2; 3 ]\nlet b: int list = [ 1; 2 ]\nlet c = [ 1..100 ]\nlet d = [ for i in 1..3 -> i ]\nlet e = [| \"x\" |]\n"

    Assert.Equal(Some 3, LoopPerf.literalSize tree "a")
    Assert.Equal(Some 2, LoopPerf.literalSize tree "b")
    Assert.Equal(None, LoopPerf.literalSize tree "c")
    Assert.Equal(None, LoopPerf.literalSize tree "d")
    Assert.Equal(Some 1, LoopPerf.literalSize tree "e")

// ---- #5: --codes / --categories keep the other analyzers from running ----

[<Fact>]
let ``a rule outside the run's allowed codes is off, so its analyzer never runs`` () =
    let source =
        "module M\n\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.FromResult 2\nlet c = System.Threading.Tasks.Task.FromResult 3\nlet d = System.Threading.Tasks.Task.FromResult 4\n"

    Scope.restrictTo (Some(set [ "FR0006"; "FR0072" ]))

    try
        Assert.False(Configuration.isRuleEnabled "Test.fs" "FR0147" "QualifiedNames")
        Assert.True(Configuration.isRuleEnabled "Test.fs" "FR0006" "ActivePattern")
        Assert.Empty(run Analyzers.qualifiedNamesCliAnalyzer (contextWith [] source))

        // the restriction is the run's own flow: work started in another one
        // - a test class running beside a test that drives the tool - keeps
        // every rule, while work this flow starts inherits it
        let enabledIn (flowing: bool) =
            let enabled = ref false

            let t =
                System.Threading.Thread(fun () ->
                    enabled.Value <- Configuration.isRuleEnabled "Test.fs" "FR0147" "QualifiedNames")

            if flowing then
                t.Start()
            else
                use _ = System.Threading.ExecutionContext.SuppressFlow()
                t.Start()

            t.Join()
            enabled.Value

        Assert.True(enabledIn false)
        Assert.False(enabledIn true)
    finally
        Scope.restrictTo None

    Assert.True(Configuration.isRuleEnabled "Test.fs" "FR0147" "QualifiedNames")

[<Fact>]
let ``the restriction reaches the deep-stack workers per call and does not outlive the run that set it`` () =
    // BooleanSimplify checks its codes inside the worker. The workers are
    // long-lived threads: before each job ran under its caller's context,
    // they kept the one of whichever run created them, and a `--codes` run
    // switched these rules off for every later run in the process
    let source = "module M\n\nlet f (x: bool) = x && true\n"

    let codes () =
        run Analyzers.booleanSimplifyCliAnalyzer (contextWith [] source)
        |> List.map (fun m -> m.Code)

    Scope.restrictTo (Some(set [ "FR0130" ]))

    try
        Assert.Empty(codes ())
    finally
        Scope.restrictTo None

    Assert.Contains("FR0108", codes ())

// ---- #6: FR0015's names, FR0168's layout, Fantomas's call style ----

[<Fact>]
let ``FR0015: the hoisted regex is named after the binding it serves`` () =
    let source =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nlet isPostcode (s: string) =\n    Regex.IsMatch(s, @\"^[A-Z]{1,2}\\d[A-Z\\d]? ?\\d[A-Z]{2}$\")\n\nlet collapseSpaces (s: string) = Regex.Replace(s, @\"\\s+\", \" \")\n"

    let tree, text = parse source

    let inserted =
        RegexUsage.find tree text
        |> List.collect (fun s -> s.Edits |> List.map (fun (_, _, t) -> t))
        |> String.concat "\n"

    Assert.Contains("postcodeRegex = Regex", inserted)
    Assert.Contains("collapseSpacesRegex = Regex", inserted)

/// FR0015's edits for a source, the inserted bindings and the call rewrites.
let private regexEdits (source: string) =
    let tree, text = parse source

    RegexUsage.find tree text
    |> List.collect (fun s -> s.Edits |> List.map (fun (_, _, t) -> t))

[<Fact>]
let ``FR0015: a taken name falls back to the function's whole name before the pattern's letters`` () =
    let source =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nlet postcodeRegex = 1\nlet isPostcode (s: string) = Regex.IsMatch(s, @\"^[A-Z]{2}\\d$\")\n"

    let edits = regexEdits source
    Assert.Contains(edits, fun t -> t.StartsWith "let private isPostcodeRegex = Regex")

[<Fact>]
let ``FR0015: one pattern at two sites becomes one binding, the second site reusing it`` () =
    let source =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nlet check (s: string) = Regex.IsMatch(s, @\"^\\d{5}$\")\nlet isZip (s: string) = Regex.IsMatch(s, @\"^\\d{5}$\")\n"

    // one pass: only the topmost site inserts a binding
    let first = regexEdits source
    Assert.Equal(1, first |> List.filter (fun t -> t.StartsWith "let private") |> List.length)
    Assert.Contains(first, fun t -> t.StartsWith "let private checkRegex = Regex")

    // the next pass: the second site takes the binding above over
    let afterFirst =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nlet private checkRegex = Regex @\"^\\d{5}$\"\nlet check (s: string) = checkRegex.IsMatch(s)\nlet isZip (s: string) = Regex.IsMatch(s, @\"^\\d{5}$\")\n"

    Assert.Equal<string list>([ "checkRegex.IsMatch(s)" ], regexEdits afterFirst)

[<Fact>]
let ``FR0015: two regexes of one function both hoist in one pass, the second numbered`` () =
    // each regex of a function derives the function's name; the second
    // used to be dropped as a collision and return a pass later under the
    // pattern's letters
    let source =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nlet check (s: string) = Regex.IsMatch(s, @\"^\\d+$\") || Regex.IsMatch(s, @\"^[a-z]+$\")\n"

    let inserted =
        regexEdits source |> List.filter (fun t -> t.StartsWith "let private")

    Assert.Equal(2, inserted.Length)
    Assert.Contains(inserted, fun t -> t.StartsWith "let private checkRegex = Regex")
    Assert.Contains(inserted, fun t -> t.StartsWith "let private checkRegex2 = Regex")

[<Fact>]
let ``FR0015: a binding the site's declaration shadows is not reused`` () =
    // a parameter named like the binding: reusing it would reach the
    // caller's value - a string does not compile, a Regex silently tests a
    // different pattern
    for parameterType in [ "string"; "Regex" ] do
        let source =
            $"module Forms\n\nopen System.Text.RegularExpressions\n\nlet private digitsRegex = Regex @\"^\\d+$\"\nlet allDigits (digitsRegex: {parameterType}) (xs: string list) = xs |> List.filter (fun x -> Regex.IsMatch(x, @\"^\\d+$\"))\n"

        let edits = regexEdits source
        Assert.DoesNotContain(edits, fun t -> t.StartsWith "digitsRegex.")

[<Fact>]
let ``FR0015: a binding of the same pattern in a SIBLING module is not reused`` () =
    let source =
        "module Forms\n\nopen System.Text.RegularExpressions\n\nmodule A =\n    let private zipRegex = Regex @\"^\\d{5}$\"\n    let check (s: string) = zipRegex.IsMatch(s)\n\nmodule B =\n    let isZip (s: string) = Regex.IsMatch(s, @\"^\\d{5}$\")\n"

    let edits = regexEdits source
    Assert.DoesNotContain(edits, fun t -> t = "zipRegex.IsMatch(s)")
    Assert.Contains(edits, fun t -> t.StartsWith "let private")

[<Fact>]
let ``FR0168: a try on the else line becomes a match on lines of its own, with a fresh binder`` () =
    let source =
        "open System\n\nlet parseDate (v: string) : DateTime option =\n    if v = \"\" then None else try Some(DateTime.Parse v) with _ -> None\n"

    let tree, text, check = parseAndCheck source

    let site =
        SwallowedException.findParseControlFlow tree text (Some check)
        |> List.exactlyOne

    let r, _, replacement = (List.exactlyOne site.Offers).Edits |> List.exactlyOne
    let patched = applyEdit source r replacement

    Assert.Equal(
        "open System\n\nlet parseDate (v: string) : DateTime option =\n    if v = \"\" then None else\n        match DateTime.TryParse v with\n        | true, parsed -> Some parsed\n        | false, _ -> None\n",
        patched
    )

    Assert.True(typechecksCleanly patched, patched)

/// Every offer of FR0168 applied to `source`, bottom-up.
let private tryParsePatched (source: string) =
    let tree, text, check = parseAndCheck source

    SwallowedException.findParseControlFlow tree text (Some check)
    |> List.collect (fun s -> s.Offers |> List.truncate 1 |> List.collect (fun o -> o.Edits))
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Theory>]
[<InlineData("let f (s: string) =\n    match s.Length with\n    | 0 -> 0\n    | _ -> try Int32.Parse s with _ -> -1\n")>]
[<InlineData("let f (s: string) =\n    let n = try Int32.Parse s with _ -> 0\n    n + 1\n")>]
[<InlineData("let f (s: string) =\n    if s <> \"\" then try Some(Int32.Parse s) with _ -> None else None\n")>]
[<InlineData("let f (s: string) =\n    if s <> \"\" then try Some(Int32.Parse s) with _ -> None\n    else None\n")>]
[<InlineData("let f (xs: string list) =\n    xs |> List.map (fun s -> try Int32.Parse s with _ -> 0)\n")>]
[<InlineData("let f: string -> int =\n    fun s -> try Int32.Parse s with _ -> 0\n")>]
[<InlineData("let f (xs: string list) =\n    xs |> List.map (fun s -> 1) |> ignore\n    List.map <| fun s -> try Int32.Parse s with _ -> 0\n")>]
[<InlineData("let f (xs: string list) =\n    xs\n    |> List.map (fun s ->\n        try Int32.Parse s with _ -> 0)\n")>]
[<InlineData("let f (s: string) =\n    let n = if s <> \"\" then try Int32.Parse s with _ -> 0 else 0\n    n\n")>]
[<InlineData("let f (s: string) =\n    let n =\n        if s <> \"\" then try Int32.Parse s with _ -> 0\n        else 0\n    n\n")>]
[<InlineData("let f (s: string) =\n    let n = if s = \"\" then 0 else try Int32.Parse s with _ -> 0\n    n\n")>]
[<InlineData("let f (xs: string list) =\n    xs |> List.map (fun s -> let n = try Int32.Parse s with _ -> 0 in n)\n")>]
[<InlineData("let f (s: string) =\n    match s with\n    | \"\" -> 0\n    | _ -> (fun () -> try Int32.Parse s with _ -> 0) ()\n")>]
[<InlineData("type T() =\n    member _.P(s: string) = try Int32.Parse s with _ -> 0\n")>]
[<InlineData("let f s =\n    try Int32.Parse s with _ -> 0\n")>]
[<InlineData("let f (xs: string list) =\n    xs |> List.map (fun s ->\n        try Int32.Parse s with _ -> 0)\n")>]
let ``FR0168: every layout the line break meets still typechecks, with nothing offside`` (body: string) =
    let source = "module M\n\nopen System\n\n" + body
    let patched = tryParsePatched source
    Assert.NotEqual<string>(source, patched)
    Assert.DoesNotContain("try ", patched)
    let _, _, check = parseAndCheck patched

    // an error, or FS0058 - a line the move left offside compiles with a
    // warning and may already read differently
    let problems =
        check.Diagnostics
        |> Array.filter (fun d ->
            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
            || d.ErrorNumber = 58)

    Assert.True(Array.isEmpty problems, $"%A{problems}\n{patched}")

[<Fact>]
let ``FR0168: only a parameter inferred late gets its argument annotated`` () =
    let patched =
        tryParsePatched
            "module M\n\nopen System\n\nlet f s =\n    try Int32.Parse s with _ -> 0\n\nlet g (s: string) =\n    try Int32.Parse s with _ -> 0\n\nlet h () =\n    let s = Console.ReadLine()\n    try Int32.Parse s with _ -> 0\n"

    // f's `s` is not a string yet where TryParse is resolved: `Parse` took
    // it, the several TryParse overloads cannot
    Assert.Contains("Int32.TryParse (s: string) with", patched)
    // annotated, or fixed by its right side: left as written
    Assert.Equal(2, Regex.Matches(patched, @"Int32\.TryParse s with").Count)
    Assert.True(typechecksCleanly patched, patched)

[<Fact>]
let ``EditorConfig: a section glob it cannot translate matches nothing instead of throwing`` () =
    let root = freshDir "editorconfig-bad"

    File.WriteAllText(
        Path.Combine(root, ".editorconfig"),
        "root = true\n\n[z-a]\nfsharp_space_before_lowercase_invocation = true\n\n[[z-a].fs]\nindent_size = 2\n\n[*.fs]\nfsharp_space_before_lowercase_invocation = false\n"
    )

    Assert.True(EditorConfig.keepsLowercaseCallParens (Path.Combine(root, "Code.fs")))

[<Fact>]
let ``EditorConfig: the nearest file wins, a root stops the walk, and brace globs match`` () =
    let root = freshDir "editorconfig"
    let sub = Path.Combine(root, "src", "App")
    Directory.CreateDirectory sub |> ignore

    File.WriteAllText(
        Path.Combine(root, ".editorconfig"),
        "root = true\n\n[*]\nindent_style = space\n\n[*.{fs,fsx}]\nfsharp_space_before_lowercase_invocation = false\n"
    )

    let file = Path.Combine(sub, "Code.fs")
    Assert.True(EditorConfig.keepsLowercaseCallParens file)
    Assert.False(EditorConfig.keepsLowercaseCallParens (Path.Combine(sub, "Code.cs")))

    File.WriteAllText(Path.Combine(sub, ".editorconfig"), "[*.fs]\nfsharp_space_before_lowercase_invocation = true\n")

    Assert.False(EditorConfig.keepsLowercaseCallParens file)
    // a key only the outer file sets is still read through the nearer one
    Assert.Equal(Some "space", EditorConfig.value file "indent_style")

[<Fact>]
let ``FR0013: Fantomas told to write f(x) keeps the parentheses, unless FR0013 is asked for by name`` () =
    let fantomasDir () =
        let dir = freshDir "fantomas"

        File.WriteAllText(
            Path.Combine(dir, ".editorconfig"),
            "root = true\n\n[*.{fs,fsx}]\nfsharp_space_before_lowercase_invocation = false\n"
        )

        dir

    let source = "let f x = x + 1\nlet b = f(1)\n"
    Assert.Empty(ofCode "FR0013" (run Analyzers.redundantParensCliAnalyzer (contextIn (fantomasDir ()) [] source)))

    // a directory of its own: config discovery is cached per directory
    let asked = fantomasDir ()
    File.WriteAllText(Path.Combine(asked, Configuration.ConfigFileName), """{ "rules": { "FR0013": true } }""")
    Assert.NotEmpty(ofCode "FR0013" (run Analyzers.redundantParensCliAnalyzer (contextIn asked [] source)))

// ---- #2 and #5 end to end: FR0006 in one pass, the second pass narrower ----

[<Fact>]
[<Trait("Category", "Slow")>]
let ``the tool applies every FR0006 guard of a match in one pass and re-sweeps only what it changed`` () =
    let dir = freshDir "fr0006-e2e"

    let write (name: string) (text: string) =
        File.WriteAllText(Path.Combine(dir, name), text)

    write
        "Guards.fsproj"
        "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net10.0</TargetFramework></PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Before.fs\" />\n    <Compile Include=\"Guards.fs\" />\n    <Compile Include=\"After.fs\" />\n  </ItemGroup>\n</Project>\n"

    write "Before.fs" "module Before\n\nlet answer = 42\n"

    write
        "Guards.fs"
        "module Guards\n\nopen System\n\nlet isArrayType (t: Type) = t.IsArray\nlet isEnumType (t: Type) = t.IsEnum\nlet isRecordLike (t: Type) = t.Name.StartsWith \"Anon\"\n\nlet rec describe (t: Type) : string =\n    match t with\n    | t when t = typeof<int> -> \"int4\"\n    | t when isArrayType t -> describe (t.GetElementType()) + \"[]\"\n    | t when isRecordLike t -> \"jsonb\"\n    | t when isEnumType t -> \"enum\"\n    | _ -> \"text\"\n"

    write "After.fs" "module After\n\nlet described = Guards.describe typeof<int[]>\n"

    use captured = new StringWriter()
    let oldOut = Console.Out
    let oldErr = Console.Error
    Console.SetOut captured
    Console.SetError captured

    try
        FSharp.Refactor.Tool.Program.main [| Path.Combine(dir, "Guards.fsproj"); "--codes"; "FR0006"; "--no-color" |]
        |> ignore
    finally
        Console.SetOut oldOut
        Console.SetError oldErr

    let output = captured.ToString()
    let guards = File.ReadAllText(Path.Combine(dir, "Guards.fs"))

    Assert.DoesNotContain("re-fired", output)

    for pattern in [ "(|IsArrayType|_|)"; "(|IsRecordLike|_|)"; "(|IsEnumType|_|)" ] do
        Assert.Contains(pattern, guards)

    // stacked at one point, they read in the order of their guards
    let at (pattern: string) = guards.IndexOf pattern
    Assert.True(at "(|IsArrayType|_|)" < at "(|IsRecordLike|_|)", guards)
    Assert.True(at "(|IsRecordLike|_|)" < at "(|IsEnumType|_|)", guards)

    // pass 1 changed Guards.fs, the second file: pass 2 sweeps it and the
    // file compiled after it, never Before.fs (pass 1 also sweeps the two
    // sources MSBuild generates ahead of the project's own)
    Assert.Matches(@"pass 1:\s+sweeping ([3-9]|\d\d+) file\(s\)", output)
    Assert.Matches(@"pass 2:\s+sweeping 2 file\(s\)", output)
    // one line per finding with its edit count, and the totals labelled
    Assert.Contains("(2 edits)", output)
    Assert.Contains("6 edit(s) applied, from 3 finding(s)", output)
