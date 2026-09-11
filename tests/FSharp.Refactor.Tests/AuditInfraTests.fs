/// Infrastructure audit fixes: the leaf-compilation scope gate against a
/// LATER file of the same executable (FR0035 in-place conversion, FR0011
/// struct return), one switch per code where an analyzer emits several
/// (FR0017/FR0149, FR0075/FR0150, FR0127/FR0153), the FR0105 scale-factor
/// note surviving every int32 spelling, and FR0092's test-source detection
/// no longer reading `Contest` as a test.
module FSharp.Refactor.Tests.AuditInfraTests

open System
open System.IO
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

let private freshDir (tag: string) =
    let id = Guid.NewGuid().ToString "N"
    let dir = Path.Combine(Path.GetTempPath(), "fsref-tests", $"{tag}-{id}")

    Directory.CreateDirectory dir |> ignore
    dir

/// The options of a real EXECUTABLE project over the given files, in the
/// order given, as MSBuild would hand them to fsc.
let private exeOptions (projectFile: string) (files: string list) =
    let probeOptions, _ =
        checker.GetProjectOptionsFromScript(
            Path.Combine(Path.GetDirectoryName projectFile, "probe.fsx"),
            SourceText.ofString "",
            assumeDotNetFramework = false
        )
        |> Async.RunSynchronously

    { probeOptions with
        ProjectFileName = projectFile
        SourceFiles = Array.ofList files
        OtherOptions =
            Array.append
                (probeOptions.OtherOptions
                 |> Array.filter (fun o -> not (o.StartsWith "--target:")))
                [| "--target:exe" |] }

/// A CLI context for one file of a project, typechecked in it.
let private cliContext (options: FSharpProjectOptions) (fileName: string) : CliContext =
    let source = File.ReadAllText fileName
    let sourceText = SourceText.ofString source

    let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously

    let errors =
        projectResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

    Assert.True(errors.Length = 0, $"the test project does not typecheck: %A{errors}")

    let parseResults, answer =
        checker.ParseAndCheckFileInProject(fileName, 0, sourceText, options)
        |> Async.RunSynchronously

    let checkResults =
        match answer with
        | FSharpCheckFileAnswer.Succeeded r -> r
        | FSharpCheckFileAnswer.Aborted -> failwith $"typechecking aborted for {fileName}"

    { FileName = fileName
      SourceText = sourceText
      ParseFileResults = parseResults
      CheckFileResults = checkResults
      TypedTree = checkResults.ImplementationFile
      CheckProjectResults = projectResults
      ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
      AnalyzerIgnoreRanges = Map.empty }

/// A CLI context for a SCRIPT written to `fileName`, so the configuration
/// beside it applies.
let private scriptContext (fileName: string) (source: string) : CliContext =
    File.WriteAllText(fileName, source)
    let sourceText = SourceText.ofString source

    let options, _ =
        checker.GetProjectOptionsFromScript(fileName, sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    cliContext options fileName

let private run (analyzer: CliContext -> Async<Message list>) (ctx: CliContext) = analyzer ctx |> Async.RunSynchronously

let private fixTexts (messages: Message list) =
    messages |> List.collect (fun m -> m.Fixes |> List.map (fun f -> f.ToText))

// ---- D2: a later file of the same executable ----

let private dataSource (modifier: string) =
    $"module Data\n\nlet {modifier}names = [ \"a\"; \"b\" ]\n\nlet check (xs: string list) =\n    for x in xs do\n        if List.contains x names then printfn \"%%s\" x\n"

let private loopPerfOnFirst (modifier: string) (programSource: string) =
    let dir = freshDir "exe-loopperf"
    let data = Path.Combine(dir, "Data.fs")
    let program = Path.Combine(dir, "Program.fs")
    File.WriteAllText(data, dataSource modifier)
    File.WriteAllText(program, programSource)
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data; program ]
    run Analyzers.loopPerfCliAnalyzer (cliContext options data)

[<Fact>]
let ``FR0035: a public list a LATER file of the executable reads keeps its type`` () =
    // Program.fs reads Data.names as a list: `|> Set.ofList` on the
    // binding would stop it compiling, and the CLI applies this fix
    let messages =
        loopPerfOnFirst "" "module Program\n\nlet count () = List.length Data.names\n"

    let fr0035 = messages |> List.filter (fun m -> m.Code = "FR0035")
    Assert.NotEmpty fr0035
    let texts = fixTexts fr0035
    Assert.DoesNotContain(texts, fun t -> t.Contains "Set.ofList")
    // the companion HashSet leaves the binding's type alone
    Assert.Contains(texts, fun t -> t.Contains "namesProbeSet")

[<Fact>]
let ``FR0035: a public list no later file mentions still converts in place`` () =
    let messages =
        loopPerfOnFirst "" "module Program\n\nlet count () = Data.check [ \"a\" ]\n"

    let texts = fixTexts (messages |> List.filter (fun m -> m.Code = "FR0035"))
    Assert.Contains(texts, fun t -> t.Contains "Set.ofList")

[<Fact>]
let ``FR0035: a private list converts in place whatever a later file says`` () =
    // a later file cannot reach a private binding; the mention below is a
    // different `names`
    let messages =
        loopPerfOnFirst "private " "module Program\n\nlet names = [ \"z\" ]\nlet count () = List.length names\n"

    let texts = fixTexts (messages |> List.filter (fun m -> m.Code = "FR0035"))
    Assert.Contains(texts, fun t -> t.Contains "Set.ofList")

[<Fact>]
let ``FR0035: the last file of the executable converts in place`` () =
    let dir = freshDir "exe-loopperf-last"
    let first = Path.Combine(dir, "First.fs")
    let data = Path.Combine(dir, "Data.fs")
    File.WriteAllText(first, "module First\n\nlet names = [ \"z\" ]\n")
    File.WriteAllText(data, dataSource "")
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ first; data ]
    let messages = run Analyzers.loopPerfCliAnalyzer (cliContext options data)
    let texts = fixTexts (messages |> List.filter (fun m -> m.Code = "FR0035"))
    Assert.Contains(texts, fun t -> t.Contains "Set.ofList")

let private parsingSource (modifier: string) =
    $"module Parsing\n\nlet {modifier}(|Int|_|) (s: string) =\n    match System.Int32.TryParse s with\n    | true, v -> Some v\n    | _ -> None\n"

let private structActivePatternOnFirst (modifier: string) (programSource: string) =
    let dir = freshDir "exe-structap"
    let parsing = Path.Combine(dir, "Parsing.fs")
    let program = Path.Combine(dir, "Program.fs")
    File.WriteAllText(parsing, parsingSource modifier)
    File.WriteAllText(program, programSource)
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ parsing; program ]
    run Analyzers.structActivePatternCliAnalyzer (cliContext options parsing)

[<Fact>]
let ``FR0011: a public active pattern a LATER file invokes as a function keeps its option`` () =
    // `List.choose (|Int|_|)` in Program.fs wants an option; a struct
    // return would stop that file compiling
    let messages =
        structActivePatternOnFirst
            ""
            "module Program\n\nopen Parsing\n\nlet count (args: string list) = args |> List.choose (|Int|_|) |> List.length\n"

    Assert.Empty(messages |> List.filter (fun m -> m.Code = "FR0011"))

[<Fact>]
let ``FR0011: a public active pattern a later file only MATCHES on still gets its struct return`` () =
    // a match site does not see the representation
    let messages =
        structActivePatternOnFirst
            ""
            "module Program\n\nopen Parsing\n\nlet value (s: string) =\n    match s with\n    | Int v -> v\n    | _ -> 0\n"

    let fr0011 = messages |> List.filter (fun m -> m.Code = "FR0011")
    Assert.Contains(fixTexts fr0011, fun t -> t.Contains "[<return: Struct>]")

[<Fact>]
let ``FR0011: a private active pattern gets its struct return whatever a later file says`` () =
    let messages =
        structActivePatternOnFirst
            "private "
            "module Program\n\nlet (|Int|_|) (s: string) = Some 1\nlet count (args: string list) = args |> List.choose (|Int|_|) |> List.length\n"

    let fr0011 = messages |> List.filter (fun m -> m.Code = "FR0011")
    Assert.Contains(fixTexts fr0011, fun t -> t.Contains "[<return: Struct>]")

[<Fact>]
let ``the later files of a compilation are the ones after the analysed file`` () =
    let files = [ "C:/p/A.fs"; "C:\\p\\B.fs"; "C:/p/C.fs" ]
    Assert.Equal<string list>([ "C:/p/C.fs" ], Visibility.laterSourceFiles "c:/P/b.FS" files)
    Assert.Empty(Visibility.laterSourceFiles "C:/p/C.fs" files)
    // a file the list does not carry gets every file back: the options and
    // the file disagree, and any of them may follow it
    Assert.Equal<string list>(files, Visibility.laterSourceFiles "C:/q/Z.fs" files)

// ---- D8: one switch per code ----

let private withConfig (json: string) (source: string) (analyzer: CliContext -> Async<Message list>) =
    let dir = freshDir "cfg"
    File.WriteAllText(Path.Combine(dir, Configuration.ConfigFileName), json)
    run analyzer (scriptContext (Path.Combine(dir, "Code.fsx")) source)

let private codes (messages: Message list) =
    messages |> List.map (fun m -> m.Code) |> List.distinct |> List.sort

let private secretsSource =
    "[<Literal>]\nlet designTime = \"Data Source=157.24.1.223;User Id=sa;Password=Password12!; Initial Catalog=sqlprovider;TrustServerCertificate=true;\"\nlet leaked = \"Data Source=db.corp.example.com;Initial Catalog=x;User Id=sa;Password=W3lf0rd9Prod\"\n"

[<Fact>]
let ``FR0153 and FR0127 both fire from one scan`` () =
    Assert.Equal<string list>(
        [ "FR0127"; "FR0153" ],
        codes (withConfig "{}" secretsSource Analyzers.secretsCliAnalyzer)
    )

[<Fact>]
let ``FR0153 false keeps the FR0127 leaks`` () =
    Assert.Equal<string list>(
        [ "FR0127" ],
        codes (withConfig """{ "rules": { "FR0153": false } }""" secretsSource Analyzers.secretsCliAnalyzer)
    )

[<Fact>]
let ``FR0127 false keeps the FR0153 design-time note`` () =
    Assert.Equal<string list>(
        [ "FR0153" ],
        codes (withConfig """{ "rules": { "FR0127": false } }""" secretsSource Analyzers.secretsCliAnalyzer)
    )

let private asyncSource =
    "let work () = async { return 1 }\nlet discard (comp: Async<int>) = comp |> ignore\nlet run () =\n    async {\n        while true do\n            let! _ = work ()\n            ()\n    }\n    |> Async.Start\n"

[<Fact>]
let ``FR0017 and FR0149 both fire from one scan`` () =
    Assert.Equal<string list>(
        [ "FR0017"; "FR0149" ],
        codes (withConfig "{}" asyncSource Analyzers.asyncIgnoreCliAnalyzer)
    )

[<Fact>]
let ``FR0017 false no longer takes FR0149 with it`` () =
    Assert.Equal<string list>(
        [ "FR0149" ],
        codes (withConfig """{ "rules": { "FR0017": false } }""" asyncSource Analyzers.asyncIgnoreCliAnalyzer)
    )

[<Fact>]
let ``FR0149 false keeps FR0017`` () =
    Assert.Equal<string list>(
        [ "FR0017" ],
        codes (withConfig """{ "rules": { "FR0149": false } }""" asyncSource Analyzers.asyncIgnoreCliAnalyzer)
    )

[<Fact>]
let ``--codes FR0149 brings FR0149 back on its own`` () =
    Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", "FR0149")

    try
        Assert.Equal<string list>(
            [ "FR0149" ],
            codes (
                withConfig
                    """{ "rules": { "FR0017": false, "FR0149": false } }"""
                    asyncSource
                    Analyzers.asyncIgnoreCliAnalyzer
            )
        )
    finally
        Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", null)

let private useSource =
    "open System.IO\nopen System.Threading\nopen System.Threading.Tasks\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    b + 1\nlet start () =\n    use cts = new CancellationTokenSource()\n\n    task {\n        do! Task.Delay(1000, cts.Token)\n        return 1\n    }\n"

[<Fact>]
let ``FR0075 and FR0150 both fire from one scan`` () =
    Assert.Equal<string list>([ "FR0075"; "FR0150" ], codes (withConfig "{}" useSource Analyzers.useBindingCliAnalyzer))

[<Fact>]
let ``FR0075 false no longer takes FR0150 with it`` () =
    Assert.Equal<string list>(
        [ "FR0150" ],
        codes (withConfig """{ "rules": { "FR0075": false } }""" useSource Analyzers.useBindingCliAnalyzer)
    )

[<Fact>]
let ``FR0150 false keeps FR0075`` () =
    Assert.Equal<string list>(
        [ "FR0075" ],
        codes (withConfig """{ "rules": { "FR0150": false } }""" useSource Analyzers.useBindingCliAnalyzer)
    )

// ---- D9: the FR0105 scale-factor note never throws ----

let private checkedNotes (source: string) =
    let dir = freshDir "checked"
    run Analyzers.checkedArithmeticCliAnalyzer (scriptContext (Path.Combine(dir, "Code.fsx")) source)

[<Fact>]
let ``FR0105: an int32 literal with the l suffix gets its note`` () =
    match checkedNotes "let x (n: int) = n * 1000000l\n" with
    | [ m ] ->
        Assert.Equal("FR0105", m.Code)
        Assert.Contains("passes 2147", m.Message)
        Assert.Contains("int64 x * 1000000L", m.Message)
    | other -> failwithf "Expected one scale-factor note, got %A" other

[<Fact>]
let ``FR0105: a negative suffixed scale factor gets its note`` () =
    // the int32 minimum itself is a NEAR-LIMIT constant (that arm is
    // asked first), so the scale-factor figure is only ever computed for a
    // magnitude below 2^30 - and now in int64, whatever the sign
    match checkedNotes "let x (n: int) = n * -1000000l\n" with
    | [ m ] ->
        Assert.Equal("FR0105", m.Code)
        Assert.Contains("passes 2147 ", m.Message)
        Assert.Contains("int64 x * -1000000L", m.Message)
    | other -> failwithf "Expected one scale-factor note, got %A" other

[<Fact>]
let ``FR0105: the int32 minimum is a near-limit note, built without throwing`` () =
    match checkedNotes "let x (n: int) = n * -2147483648\n" with
    | [ m ] ->
        Assert.Equal("FR0105", m.Code)
        Assert.Contains("near-limit constant -2147483648", m.Message)
    | other -> failwithf "Expected one near-limit note, got %A" other

[<Fact>]
let ``FR0105: the plain million still names its threshold`` () =
    match checkedNotes "let micros (seconds: int) = seconds * 1_000_000\n" with
    | [ m ] -> Assert.Contains("passes 2147 ", m.Message)
    | other -> failwithf "Expected one scale-factor note, got %A" other

// ---- E2: which files are tests ----

[<Theory>]
[<InlineData("tests/RulesTests.fs", true)>]
[<InlineData("tests/Rules.fs", true)>]
[<InlineData("src/Lib.Tests/Rules.fs", true)>]
[<InlineData("src/Foo.Tests.fs", true)>]
[<InlineData("src/Foo.Spec.fs", true)>]
[<InlineData("src/specs/Foo.fs", true)>]
[<InlineData("src/test_helpers.fs", true)>]
[<InlineData("src/TestHelpers.fs", true)>]
[<InlineData("src\\Lib\\MyTest.fs", true)>]
[<InlineData("src/Contest/Rules.fs", false)>]
[<InlineData("src/LatestPrices.fs", false)>]
[<InlineData("src/Attestation.fs", false)>]
[<InlineData("src/ProtestHandler.fs", false)>]
[<InlineData("src/Testing.fs", false)>]
[<InlineData("src/Rules.fs", false)>]
let ``a test source is named by a whole word, not a substring`` (path: string) (expected: bool) =
    Assert.Equal(expected, Configuration.isTestSourcePath path)

let private repository () =
    let root = freshDir "repo"
    Directory.CreateDirectory(Path.Combine(root, ".git")) |> ignore
    let contest = Path.Combine(root, "src", "Contest")
    Directory.CreateDirectory contest |> ignore
    let rules = Path.Combine(contest, "Rules.fs")
    File.WriteAllText(rules, "module Rules\n\nlet score (r: int) = if r < 0 then failwith \"negative\" else r\n")
    root, rules

[<Fact>]
let ``FR0092: a production file under Contest is not the test pinning its own text`` () =
    let root, rules = repository ()
    // a SIBLING production file throwing the same text is no test either:
    // `Contest` carried the substring, not the word
    File.WriteAllText(
        Path.Combine(root, "src", "Contest", "Other.fs"),
        "module Other\n\nlet check (r: int) = if r < 0 then failwith \"negative\" else r\n"
    )

    Assert.Empty(Configuration.testFilesMentioning rules "\"negative\"")

[<Fact>]
let ``FR0092: a real test asserting on the text still pins it`` () =
    let root, rules = repository ()
    let tests = Path.Combine(root, "tests")
    Directory.CreateDirectory tests |> ignore
    let testFile = Path.Combine(tests, "RulesTests.fs")

    File.WriteAllText(
        testFile,
        "module RulesTests\n\nlet check () =\n    let ex = Assert.Throws(fun () -> Rules.score -1 |> ignore)\n    Assert.Equal(\"negative\", ex.Message)\n"
    )

    match Configuration.testFilesMentioning rules "\"negative\"" with
    | [ (path, _) ] -> Assert.Equal(Path.GetFullPath testFile, Path.GetFullPath path)
    | other -> failwithf "Expected the one test file, got %A" other

    // and the Contest file is production code for the assertion side
    Assert.Contains("\"negative\"", Configuration.productionFailwithLiterals testFile)
