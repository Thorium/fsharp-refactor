/// Performance guardrail: every analyzer runs against a large synthetic
/// file, timed individually after a warmup round. A report with per-rule
/// timings lands in the temp directory; the assertion only catches
/// pathological blowups (quadratic scans and the like), not CI jitter.
module FSharp.Refactor.Tests.PerfTests

open System
open System.Diagnostics
open System.IO
open System.Reflection
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor.Tests.Parsing

/// A block exercising many syntactic shapes at once; repeated with unique
/// suffixes to build a file of realistic size.
let private blockTemplate (i: int) =
    $"""
type RecordN{i} = {{ AlphaN{i}: int; BetaN{i}: string option }}

type UnionN{i} =
    | CaseAN{i} of int
    | CaseBN{i}
    | CaseCN{i}

let funcAN{i} (x: int option) =
    match x with
    | Some v -> v * {i} + 1
    | None -> 0

let funcBN{i} (items: string list) (needle: string) =
    let mutable count = 0

    for item in items do
        let bonus = {i} + 1

        if item.Contains needle then
            count <- count + item.Length + bonus

    count

let funcCN{i} (r: RecordN{i}) =
    match r.BetaN{i} with
    | Some s -> sprintf "%%s-%%d" s r.AlphaN{i}
    | None -> string r.AlphaN{i}

let funcDN{i} (u: UnionN{i}) =
    match u with
    | CaseAN{i} n -> n
    | _ -> {i}

let funcEN{i} (xs: int[]) =
    try
        xs |> Array.map (fun v -> v + {i}) |> Array.sum
    with _ ->
        0
"""

let private bigSource =
    "module PerfCorpus\n" + (Seq.init 60 blockTemplate |> String.concat "\n")

[<Fact>]
let ``every analyzer stays fast on a large file`` () =
    let sourceText = SourceText.ofString bigSource
    // a dedicated checker: analyzers may read the typed tree
    let checker = FSharpChecker.Create(keepAssemblyContents = true)

    task {
        let! options, _ =
            checker.GetProjectOptionsFromScript("Test.fsx", sourceText, assumeDotNetFramework = false)
            |> Async.StartImmediateAsTask

        let! projectResults = checker.ParseAndCheckProject options |> Async.StartImmediateAsTask

        let! parseResults, answer =
            checker.ParseAndCheckFileInProject("Test.fsx", bigSource.GetHashCode(), sourceText, options)
            |> Async.StartImmediateAsTask

        let checkResults =
            match answer with
            | FSharpCheckFileAnswer.Succeeded r -> r
            | FSharpCheckFileAnswer.Aborted -> failwith "typechecking aborted"

        let context: CliContext =
            { FileName = "Test.fsx"
              SourceText = sourceText
              ParseFileResults = parseResults
              CheckFileResults = checkResults
              TypedTree = checkResults.ImplementationFile
              CheckProjectResults = projectResults
              ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
              AnalyzerIgnoreRanges = Map.empty }

        let analyzers =
            [ for t in typeof<FSharp.Refactor.RedundantParens.Suggestion>.Assembly.GetTypes() do
                  for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
                      if m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).Length > 0 then
                          m ]

        let runOne (m: MethodInfo) =
            m.Invoke(null, [| box context |]) :?> Async<Message list>
            |> Async.RunSynchronously

        // warmup: JIT + the shared AstIndex memoization
        for m in analyzers do
            runOne m |> ignore

        let timings =
            [ for m in analyzers do
                  let sw = Stopwatch.StartNew()
                  let messages = runOne m
                  sw.Stop()
                  m.Name, sw.Elapsed.TotalMilliseconds, messages.Length ]
            |> List.sortByDescending (fun (_, ms, _) -> ms)

        let report =
            [ yield $"lines: {sourceText.GetLineCount()}, analyzers: {analyzers.Length}"
              for name, ms, hits in timings do
                  yield $"%-45s{name} %8.1f{ms} ms  %d{hits} hits" ]
            |> String.concat "\n"

        do! File.WriteAllTextAsync(Path.Combine(Path.GetTempPath(), "fsref-perf.txt"), report)

        let runTail () =
            let slow = timings |> List.filter (fun (_, ms, _) -> ms > 2000.0)

            Assert.True(
                slow.IsEmpty,
                "Pathologically slow analyzers:\n"
                + String.concat "\n" (slow |> List.map (fun (n, ms, _) -> $"%s{n}: %.0f{ms} ms"))
            )

        runTail ()
    }
    :> System.Threading.Tasks.Task

// ---- FR0106 SubstringSpan ----

let private substringSpansIn (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    FSharp.Refactor.SubstringSpan.find tree sourceText checkResults

[<Fact>]
let ``a Substring fed to Parse becomes AsSpan`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

    match substringSpansIn source with
    | [ sug ] ->
        let patched = applyEdit source sug.Range "AsSpan"
        Assert.Contains("Int32.Parse(s.AsSpan(6, 5))", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one AsSpan suggestion, got %A" other

[<Fact>]
let ``a Substring fed to TryParse becomes AsSpan`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) =\n    match Int32.TryParse(s.Substring 6) with\n    | true, v -> v\n    | _ -> 0"

    match substringSpansIn source with
    | [ sug ] ->
        let patched = applyEdit source sug.Range "AsSpan"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one TryParse suggestion, got %A" other

[<Fact>]
let ``a bound Substring escapes and is left alone`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\nlet f (s: string) =\n    let part = s.Substring(6, 5)\n    Int32.Parse part"
    )

[<Fact>]
let ``a parser without a span overload is left alone`` () =
    // the availability gate: no ReadOnlySpan<char> overload proven in the
    // compilation, no suggestion — this is how netstandard2.0/net4x
    // compilations stay untouched without any TFM sniffing
    Assert.Empty(
        substringSpansIn
            "module Test\ntype Money =\n    static member Parse(text: string) = text.Length\nlet f (s: string) = Money.Parse(s.Substring(6, 5))"
    )

[<Fact>]
let ``a Substring on a non-string receiver is left alone`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\ntype Doc(t: string) =\n    member _.Substring(a: int, b: int) = t.Substring(a, b)\nlet f (d: Doc) = Int32.Parse(d.Substring(6, 5))"
    )

[<Fact>]
let ``byref TryParse spelling is deliberately untouched`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\nlet f (s: string) =\n    let mutable r = 0\n    Int32.TryParse(s.Substring(6, 5), &r) |> ignore\n    r"
    )

// ---- CapabilityFix dual-framework emission ----

let private withDualTfm (f: unit -> unit) =
    Environment.SetEnvironmentVariable("FSREF_DUAL_TFM", "NETSTANDARD21")

    try
        f ()
    finally
        Environment.SetEnvironmentVariable("FSREF_DUAL_TFM", null)

let private dualFixFor (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    match FSharp.Refactor.SubstringSpan.find tree sourceText checkResults with
    | [ s ] -> FSharp.Refactor.CapabilityFix.make sourceText s.Range "Substring" "AsSpan"
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a dual-framework run wraps the fix in an if-else pair`` () =
    withDualTfm (fun () ->
        let fix =
            dualFixFor
                "module Test\nopen System\n#if NETSTANDARD\nlet flag = 1\n#endif\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

        Assert.Contains("#if NETSTANDARD21", fix.ToText)
        Assert.Contains("Int32.Parse(s.AsSpan(6, 5))", fix.ToText)
        Assert.Contains("#else", fix.ToText)
        Assert.Contains("Int32.Parse(s.Substring(6, 5))", fix.ToText)
        Assert.Contains("#endif", fix.ToText))

[<Fact>]
let ``a file without conditionals keeps the plain fix even on a dual run`` () =
    withDualTfm (fun () ->
        let fix =
            dualFixFor "module Test\nopen System\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

        Assert.Equal("AsSpan", fix.ToText))

[<Fact>]
let ``a line already under a modern guard keeps the plain fix`` () =
    // the guard scan is textual, so drive CapabilityFix.make directly: a
    // test parse (empty defines) never enters the NET6_0_OR_GREATER branch
    withDualTfm (fun () ->
        let text =
            "module Test\nopen System\n#if NET6_0_OR_GREATER\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))\n#endif"

        let sourceText = SourceText.ofString text
        let line = sourceText.GetLineString 3
        let col = line.IndexOf "Substring"

        let r =
            FSharp.Compiler.Text.Range.mkRange
                "T.fs"
                (FSharp.Compiler.Text.Position.mkPos 4 col)
                (FSharp.Compiler.Text.Position.mkPos 4 (col + 9))

        let fix = FSharp.Refactor.CapabilityFix.make sourceText r "Substring" "AsSpan"
        Assert.Equal("AsSpan", fix.ToText))

[<Fact>]
let ``the negative branch of a modern guard still wraps`` () =
    // inside #else of the guard: this line IS what legacy compiles
    withDualTfm (fun () ->
        let fix =
            dualFixFor
                "module Test\nopen System\n#if NETSTANDARD21\nlet flag = 1\n#else\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))\n#endif"

        Assert.Contains("#if NETSTANDARD21", fix.ToText))

[<Fact>]
let ``without the dual signal the fix is always plain`` () =
    let fix =
        dualFixFor
            "module Test\nopen System\n#if NETSTANDARD\nlet flag = 1\n#endif\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

    Assert.Equal("AsSpan", fix.ToText)
