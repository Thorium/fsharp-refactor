/// Analyzer hot spots of the 2026-11-18 dotnet/fsharp sweep (FSharp.slnx),
/// each reduced to the synthetic shape that drives it. Each test types a
/// file at N and at 4N and times the analyzer's first (cold) run on fresh
/// check results, as a sweep pays it: a linear rule stays near 4x, a
/// per-candidate whole-file or whole-project walk climbs toward 16x.
/// Budgets are absolute where the cost is linear but too high per site.
/// In the "ProjectSources" collection: tests elsewhere set the process-wide
/// analysis scope (Scope.set), and FR0157 reads it.
///
/// Tagged `Category=Timing`: a clock is only as steady as the machine, so CI
/// runs these in a process of their own (`--filter "Category=Timing"`) after
/// the rest (`--filter "Category!=Timing"`).
[<Xunit.Collection("ProjectSources"); Xunit.Trait("Category", "Timing")>]
module FSharp.Refactor.Tests.DotnetSweepPerf1118Tests

open System
open System.Diagnostics
open System.IO
open System.Reflection
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

let private contextOf (fileName: string) (source: string) : CliContext =
    let sourceText = SourceText.ofString source

    let options, _ =
        checker.GetProjectOptionsFromScript(fileName, sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously

    let parseResults, answer =
        checker.ParseAndCheckFileInProject(fileName, source.GetHashCode(), sourceText, options)
        |> Async.RunSynchronously

    let checkResults =
        match answer with
        | FSharpCheckFileAnswer.Succeeded r -> r
        | FSharpCheckFileAnswer.Aborted -> failwith "typechecking aborted"

    {
        FileName = fileName
        SourceText = sourceText
        ParseFileResults = parseResults
        CheckFileResults = checkResults
        TypedTree = checkResults.ImplementationFile
        CheckProjectResults = projectResults
        ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
        AnalyzerIgnoreRanges = Map.empty
    }

let private analyzer (name: string) : MethodInfo =
    typeof<FSharp.Refactor.RedundantParens.Suggestion>.Assembly.GetTypes()
    |> Seq.collect (fun t -> t.GetMethods(BindingFlags.Static ||| BindingFlags.Public))
    |> Seq.find (fun m ->
        m.Name = name
        && m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).Length > 0)

let private run (m: MethodInfo) (ctx: CliContext) =
    m.Invoke(null, [| box ctx |]) :?> Async<Message list> |> Async.RunSynchronously

/// The analyzer's first run on fresh check results (the shared AstIndex is
/// built beforehand by a syntax-only analyzer, as in a sweep), in ms, and
/// how many messages it produced.
let private coldRun (name: string) (fileName: string) (source: string) =
    let ctx = contextOf fileName source
    run (analyzer "redundantParensCliAnalyzer") ctx |> ignore
    let sw = Stopwatch.StartNew()
    let messages = run (analyzer name) ctx
    sw.Stop()
    sw.Elapsed.TotalMilliseconds, messages.Length

/// Time at n and at 4n, after a JIT warm-up at 2: (small, large, ratio).
let private scaling (name: string) (fileName: string) (shape: int -> string) (n: int) =
    coldRun name fileName (shape 2) |> ignore

    // the best of three cold runs, each on fresh check results (the trailing
    // comment keeps the checker from handing back the last ones): a run of a
    // few milliseconds can take a gen-2 collection of the whole heap
    let bestOf (source: string) =
        List.init 3 (fun i -> coldRun name fileName $"{source}\n// run {i}\n")
        |> List.minBy fst

    let small, smallHits = bestOf (shape n)
    let large, largeHits = bestOf (shape (4 * n))
    small, large, large / max small 1.0, smallHits, largeHits

let private assertLinearWithin
    (maxRatio: float)
    (name: string)
    (fileName: string)
    (shape: int -> string)
    (n: int)
    (expectHits: bool)
    =
    let small, large, ratio, smallHits, largeHits = scaling name fileName shape n

    if expectHits then
        // the shape must reach the rule's per-site work, or the timing proves nothing
        Assert.True(smallHits > 0 && largeHits > smallHits, $"{name}: shape found {smallHits}/{largeHits} sites")

    // below 100 ms at 4N the ratio measures a collection or a JIT stall, not
    // the rule (the quadratic shapes took 170-2470 ms at 4N, at x7 to x17)
    Assert.True(
        ratio < maxRatio || large < 100.0,
        $"{name}: N={n} took %.0f{small} ms, 4N took %.0f{large} ms (x%.1f{ratio}); a linear rule stays near x4"
    )

let private assertLinear = assertLinearWithin 6.0

let private block (n: int) (f: int -> string) = Seq.init n f |> String.concat "\n"

/// A fixture module named Xunit, so `[<Fact>]` resolves under a namespace
/// the test rules trust without a framework package.
let private xunitHeader =
    "module Xunit\nopen System\ntype FactAttribute() =\n    inherit Attribute()\n"

// ---- FR0133 NameQuoting ----

// FSharp.Compiler.ComponentTests: 1,320,905 ms summed over 31 files in one
// pass. Each test-attributed camel-case name asks the PROJECT for the
// symbol's uses (FSharpCheckProjectResults.GetUsesOfSymbol) to prove they
// stay in the file: a walk of every file's uses per candidate. In a
// one-file project that is O(names x file); in a 533-file test project each
// call walks all 533, and a candidate the proof rejects is asked again on
// every pass.

let private camelCaseTests n =
    xunitHeader
    + block n (fun i ->
        $"""
[<Fact>]
let checkThatTheParserAcceptsInput{i} () =
    let value{i} = {i}
    if value{i} < 0 then failwith "negative"
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0133 cost grows linearly with the test names it renames`` () =
    // measured 2026-11-18: N=100 40 ms, N=400 697 ms (x17)
    assertLinear "nameQuotingCliAnalyzer" "Test.fsx" camelCaseTests 100 true

// ---- FR0157 StringUnion ----

// FSharp.Compiler.Service: 27-60 s per pass. A file of string-literal
// matches over private functions.

let private literalMatches n =
    "module Lib\n"
    + block n (fun i ->
        $"""
let private kind{i} (s: string) =
    match s with
    | "alpha" -> 1
    | "beta" -> 2
    | _ -> {i}
let private use{i} () = kind{i} "alpha" + kind{i} "beta"
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0157 cost grows linearly with string-literal matches`` () =
    // measured 2026-11-18: N=100 24 ms, N=400 170 ms (x7), N=1600 1333 ms (x7.8)
    assertLinear "stringUnionCliAnalyzer" "Lib.fsx" literalMatches 200 false

// ---- FR0169 SeqEnumeratedTwice ----

// FSharp.Compiler.Service: 18-40 s per pass. Functions binding a lazy
// sequence and consuming it twice: the cold run grows quadratically (the
// warm one is memoized and flat, so a sweep pays it once per file per pass).

let private twiceConsumedSeqs n =
    "module Lib\n"
    + block n (fun i ->
        $"""
let stats{i} (src: int list) =
    let xs = src |> Seq.map (fun v -> v + {i})
    let count = Seq.length xs
    let first = Seq.head xs
    count + first
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0169 cost grows linearly with the sequences it checks`` () =
    // measured 2026-11-18: N=100 104 ms, N=400 673 ms (x6.5), N=1600 7082 ms (x10.5).
    // At N=200 the fixed rule takes ~20 ms and the ratio swings with collections
    assertLinear "seqEnumeratedTwiceCliAnalyzer" "Lib.fsx" twiceConsumedSeqs 400 true

// ---- FR0147 QualifiedNames ----

// FSharp.Compiler.Service: 33-90 s per pass, the most consistent hot spot of
// the sweep. Namespaces spelled out at every use while the file already
// opens them: 8 ms per 6-line function even warm (a cached run is no
// cheaper), and superlinear beyond that.

let private qualifiedSpellings n =
    "module Lib\nopen System.Text\nopen System.IO\n"
    + block n (fun i ->
        $"""
let build{i} (s: string) =
    let sb = System.Text.StringBuilder()
    sb.Append(System.IO.Path.Combine(s, "{i}")) |> ignore
    sb.ToString()
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0147 reads a 2400-line file of qualified spellings within budget`` () =
    // measured 2026-11-18: N=100 2167 ms cold / 843 ms warm, N=400 4365 / 3432 ms,
    // N=1600 22193 / 23148 ms. The whole-file gate in PerfTests is 2000 ms
    coldRun "qualifiedNamesCliAnalyzer" "Lib.fsx" (qualifiedSpellings 2) |> ignore
    let ms, _ = coldRun "qualifiedNamesCliAnalyzer" "Lib.fsx" (qualifiedSpellings 400)
    // (N=150 against 600 stays under x6: the cost is mostly per spelling)
    Assert.True(ms < 1500.0, $"FR0147 took %.0f{ms} ms on 400 qualified functions (2400 lines)")

// ---- FR0142 TestReturnsTask ----

// Test projects: 36-40 s per pass. Linear, but ~9 ms of cold typed lookups
// per test even when no test blocks on anything (FSharp.Compiler.
// ComponentTests holds ~7000 tests). Warm, the same file costs 77 ms.

let private plainTests n =
    xunitHeader
    + block n (fun i ->
        $"""
[<Fact>]
let ``test number {i}`` () =
    let x = {i}
    let y = x + 1
    if y < 0 then failwith "negative"
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0142 passes over 400 non-blocking tests within budget`` () =
    // measured 2026-11-18: 400 tests 3529-4574 ms cold, 77-92 ms warm
    coldRun "testReturnsTaskCliAnalyzer" "Test.fsx" (plainTests 2) |> ignore
    let ms, hits = coldRun "testReturnsTaskCliAnalyzer" "Test.fsx" (plainTests 400)
    Assert.Equal(0, hits)
    Assert.True(ms < 1000.0, $"FR0142 took %.0f{ms} ms on 400 tests that block on nothing")

// ---- FR0092 FailwithContext ----

// FSharp.Compiler.Service: 178 s in one pass. Every finding asks
// Configuration.testFilesMentioning for its literal: a String.Contains over
// every test source of the repository (dotnet/fsharp: ~6000 files, ~29 MB),
// twice when no test pins it (the literal, then its core via
// embeddedInString). Cost = findings x corpus size.

let private constantFailwiths n =
    "module Lib\n"
    + block n (fun i ->
        $"""
let parse{i} (x: int) =
    if x < 0 then failwith "Negative input {i}." else x + {i}
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0092 does not rescan the test corpus for every finding`` () =
    // a throwaway repository: src/Lib.fsx beside a 10 MB tests/ corpus that
    // mentions none of the literals. measured 2026-11-18 with 20 MB:
    // 400 findings 3136 ms, against 391 ms with no corpus
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-perf1118-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory(Path.Combine(root, ".git")) |> ignore
    Directory.CreateDirectory(Path.Combine(root, "src")) |> ignore
    let tests = Directory.CreateDirectory(Path.Combine(root, "tests")).FullName

    let line =
        "let ``a test that says nothing in particular`` () = Assert.Equal(\"unrelated text\", compute 42)\n"

    let content = String.replicate 1000 line

    for i in 1..100 do
        File.WriteAllText(Path.Combine(tests, $"Spec{i}.Tests.fs"), content)

    try
        let file = Path.Combine(root, "src", "Lib.fsx")
        coldRun "failwithContextCliAnalyzer" file (constantFailwiths 2) |> ignore

        let withCorpus, hits =
            coldRun "failwithContextCliAnalyzer" file (constantFailwiths 400)

        Assert.Equal(400, hits)
        // the corpus is read once (cached per root) by the warm-up; what is left
        // is per-finding scanning, which an index of the corpus' literals avoids
        Assert.True(withCorpus < 1000.0, $"FR0092 took %.0f{withCorpus} ms for 400 findings beside a 10 MB test corpus")
    finally
        try
            Directory.Delete(root, true)
        with _ -> // best-effort temp cleanup; fsharpanalyzer: ignore-line FR0055
            ()

// ---- FR0058 RecursiveSeq ----

// FSharp.Core.UnitTests: 61-121 s per pass, 64 s cold on ComparersRegression.fs
// (58,630 lines) alone. Members are implicitly recursive, and each one
// scanned every expression of the file for enumerated self-calls before
// asking whether it held a `seq { }` at all.

let private membersBesideOneSeq n =
    "module Lib\nlet rec walk (n: int) = seq { if n > 0 then yield n; yield! walk (n - 1) }\n"
    + block n (fun i ->
        let values = Seq.init 100 string |> String.concat "; "

        $"""
type Holder{i}() =
    member _.Values = [| {values} |]
""" )

[<Fact>]
[<Trait("Category", "Sweep1118")>]
let ``FR0058 cost grows linearly with the members of a file`` () =
    // measured 2026-11-18 before the fix: N=500 168 ms, 4N 5258 ms (x31). Fixed:
    // under x6 alone, x6.8 under the full suite's parallel load (48 -> 324 ms,
    // the 4N file's index build included), hence x8
    assertLinearWithin 8.0 "recursiveSeqCliAnalyzer" "Lib.fsx" membersBesideOneSeq 500 false
