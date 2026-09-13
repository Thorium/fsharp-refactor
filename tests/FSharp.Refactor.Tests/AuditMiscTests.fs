/// Real-repo sweep fixes, round 2: FR0130's cross-file pattern veto
/// (A11 — FsToolkit's `let lat` vs `let! lat` in a sibling file), FR0111
/// flattening a whole else-if ladder in one pass (B15 — Giraffe's
/// five-deep chain), FR0023 refusing same-typed and churn-heavy reorders
/// (svg_path's `point y x`), and FR0101 naming the loop variable after the
/// alias it used to leave behind (Giraffe's `let mChar = item`). In the
/// "ProjectSources" collection: the cross-file parser is process-wide
/// state.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AuditMiscTests

open System
open System.IO
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

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

let private analyzerOptions (options: FSharpProjectOptions) =
    AnalyzerProjectOptions.BackgroundCompilerOptions options

/// Install the CLI's cross-file parser over `options` for the duration of
/// `body`, the way the sweep does per compilation.
let private withProjectParser (options: FSharpProjectOptions) (body: unit -> 'T) : 'T =
    let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

    ProjectSources.configure (
        Some(fun path ->
            let text = SourceText.ofString (File.ReadAllText path)
            let r = checker.ParseFile(path, text, parsingOptions) |> Async.RunSynchronously
            Some(r.ParseTree, text))
    )

    try
        body ()
    finally
        ProjectSources.configure None

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
      ProjectOptions = analyzerOptions options
      AnalyzerIgnoreRanges = Map.empty }

/// Every diagnostic of a fresh check of the project as it is on disk now.
let private projectDiagnostics (options: FSharpProjectOptions) =
    (checker.ParseAndCheckProject
        { options with
            Stamp = Some DateTime.UtcNow.Ticks }
     |> Async.RunSynchronously)
        .Diagnostics

let private projectErrors (options: FSharpProjectOptions) =
    projectDiagnostics options
    |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

// ---- A11: FR0130 and a pattern binder in ANOTHER file ----

/// FsToolkit's TestData.fs: public constants of a test executable, plus a
/// private one nobody outside the module can see.
[<Literal>]
let private testData =
    "module TestData\n\nlet lat = 13.067439\nlet lng = 80.237617\nlet private tolerance = 0.5\n"

/// A sibling that binds `lat` as a PATTERN and merely uses `lng`.
[<Literal>]
let private resultTests =
    "module ResultTests\n\nopen TestData\n\nlet describe (r: Result<float, string>) =\n    match r with\n    | Ok lat -> lat + lng\n    | Error _ -> lng\n"

let private siblingProject () =
    let dir = freshDir "literal-sibling"
    let data = Path.Combine(dir, "TestData.fs")
    let result = Path.Combine(dir, "ResultTests.fs")
    File.WriteAllText(data, testData)
    File.WriteAllText(result, resultTests)
    dir, data, result

[<Fact>]
let ``FR0130: a name another file binds as a pattern keeps its plain let`` () =
    let tree, sourceText = parse testData

    let names =
        LiteralConst.findWith (fun name -> name = "lat") true tree sourceText
        |> List.map (fun s -> s.Name)

    Assert.Equal<string list>([ "lng"; "tolerance" ], names)

[<Fact>]
let ``FR0130: a private constant never asks the other files`` () =
    // invisible outside its module, so no sibling pattern can clash with it
    let tree, sourceText = parse testData

    let names =
        LiteralConst.findWith (fun _ -> true) true tree sourceText
        |> List.map (fun s -> s.Name)

    Assert.Equal<string list>([ "tolerance" ], names)

[<Fact>]
let ``FR0130: under the cross-file parser the sibling's pattern binders are read exactly`` () =
    let dir, data, result = siblingProject ()
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data; result ]

    withProjectParser options (fun () ->
        let bound = Analyzers.patternBoundInSibling data (analyzerOptions options)
        Assert.True(bound "lat")
        // used in the sibling, never bound as a pattern there
        Assert.False(bound "lng")
        Assert.False(bound "tolerance"))

[<Fact>]
let ``FR0130: without a parser a lowercase mention in a sibling is the conservative answer`` () =
    // the editor's reading: text only, binder-shaped mentions (`let! lat`,
    // `| lat ->`, `fun lat ->`); `lng` is merely read there
    let dir, data, result = siblingProject ()
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data; result ]
    ProjectSources.configure None
    let bound = Analyzers.patternBoundInSibling data (analyzerOptions options)
    Assert.True(bound "lat")
    Assert.False(bound "lng")
    Assert.False(bound "tolerance")
    // an uppercase name's mentions are uses; `Ok` is all over the sibling
    Assert.False(bound "Ok")

[<Fact>]
let ``FR0130: a sibling that cannot be read counts as binding every name`` () =
    let dir, data, _ = siblingProject ()
    let missing = Path.Combine(dir, "Missing.fs")
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data; missing ]

    ProjectSources.configure None
    Assert.True(Analyzers.patternBoundInSibling data (analyzerOptions options) "lat")

    withProjectParser options (fun () ->
        Assert.True(Analyzers.patternBoundInSibling data (analyzerOptions options) "lat"))

[<Fact>]
let ``FR0130: the analyzed file is not its own sibling`` () =
    let dir, data, _ = siblingProject ()
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data ]
    ProjectSources.configure None
    Assert.False(Analyzers.patternBoundInSibling data (analyzerOptions options) "lat")

/// FsToolkit's Result.fs: `let! lat = ...` in a CE of a LATER file of the
/// same executable — FS3190 once `lat` is a literal.
[<Literal>]
let private program =
    "module Program\n\nopen TestData\n\nlet compute () =\n    async {\n        let! lat = async { return 1.0 }\n        return lat + lng\n    }\n\n[<EntryPoint>]\nlet main _ =\n    compute () |> Async.RunSynchronously |> ignore\n    0\n"

[<Fact>]
let ``FR0130: the sweep leaves lat alone and still annotates lng and the private constant`` () =
    let dir = freshDir "literal-sweep"
    let data = Path.Combine(dir, "TestData.fs")
    let programFile = Path.Combine(dir, "Program.fs")
    File.WriteAllText(data, testData)
    File.WriteAllText(programFile, program)
    let options = exeOptions (Path.Combine(dir, "App.fsproj")) [ data; programFile ]

    let messages =
        withProjectParser options (fun () ->
            Analyzers.literalConstCliAnalyzer (cliContext options data)
            |> Async.RunSynchronously)

    // lines: 3 lat, 4 lng, 5 tolerance
    Assert.Equal<int list>([ 4; 5 ], messages |> List.map (fun m -> m.Range.StartLine) |> List.sort)

    // the withheld fix would indeed have turned `let! lat` into a match
    // against the constant: FS3190 (a warning by default, an error under
    // FsToolkit's warnaserror — and a MatchFailureException at run time
    // either way)
    File.WriteAllText(data, testData.Replace("let lat", "[<Literal>]\nlet lat"))
    Assert.Contains(projectDiagnostics options, fun d -> d.ErrorNumber = 3190)

    // ...and the offered ones leave the project clean
    File.WriteAllText(
        data,
        testData
            .Replace("let lng", "[<Literal>]\nlet lng")
            .Replace("let private tolerance", "[<Literal>]\nlet private tolerance")
    )

    Assert.Empty(projectErrors options)
    Assert.DoesNotContain(projectDiagnostics options, fun d -> d.ErrorNumber = 3190)

// ---- B15: FR0111 flattens a whole else-if ladder at once ----

let private elseIfsIn (source: string) =
    let tree, sourceText = parse source
    IfRestructure.findElseIf tree sourceText

let private applyAll (source: string) (edits: (range * string) list) =
    edits
    |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``FR0111: a same-line else-if ladder flattens every link in one pass`` () =
    // Giraffe's ModelValidationTests: five links, one per pass before,
    // and "did not converge" after the fifth
    let source =
        "module Test\ntype Adult =\n    { FirstName: string\n      LastName: string\n      Age: int }\n\n    member this.HasErrors() =\n        if this.FirstName.Length < 3 then\n            Some \"First name is too short.\"\n        else if this.FirstName.Length > 50 then\n            Some \"First name is too long.\"\n        else if this.LastName.Length < 3 then\n            Some \"Last name is too short.\"\n        else if this.LastName.Length > 50 then\n            Some \"Last name is too long.\"\n        else if this.Age < 18 then\n            Some \"Person must be an adult (age >= 18).\"\n        else if this.Age > 150 then\n            Some \"Person must be a human being.\"\n        else\n            None"

    let found = elseIfsIn source
    Assert.Equal(5, found.Length)

    for s in found do
        Assert.Equal("else if", s.OriginalText)
        Assert.Equal("elif", s.ReplacementText)

    let patched =
        applyAll source (found |> List.map (fun s -> s.Range, s.ReplacementText))

    Assert.Equal(source.Replace("else if", "elif"), patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0111: an own-line ladder flattens as one fix with every block moved left`` () =
    let source =
        "module Test\nlet f (x: int) =\n    if x = 1 then\n        \"one\"\n    else\n        if x = 2 then\n            \"two\"\n        else\n            if x = 3 then\n                \"three\"\n            else\n                \"many\""

    match elseIfsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText

        Assert.Equal(
            "module Test\nlet f (x: int) =\n    if x = 1 then\n        \"one\"\n    elif x = 2 then\n        \"two\"\n    elif x = 3 then\n        \"three\"\n    else\n        \"many\"",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one elif suggestion for the whole ladder, got %A" other

[<Fact>]
let ``FR0111: a moved block carries its same-line link with it`` () =
    let source =
        "module Test\nlet f (x: int) =\n    if x = 1 then 0\n    else\n        if x = 2 then 1\n        else if x = 3 then 2\n        else 3"

    match elseIfsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText

        Assert.Equal(
            "module Test\nlet f (x: int) =\n    if x = 1 then 0\n    elif x = 2 then 1\n    elif x = 3 then 2\n    else 3",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one elif suggestion for the whole ladder, got %A" other

[<Fact>]
let ``FR0111: a link that stays ends the chain and the ladder below starts its own`` () =
    // a comment between `else` and `if` keeps that link (it would be
    // swallowed); the links above and below it still flatten, each at
    // the column of the chain it belongs to
    let source =
        "module Test\nlet f (x: int) =\n    if x = 1 then 0\n    else if x = 2 then 1\n    else // fall through\n        if x = 3 then 2\n        else if x = 4 then 3\n        else 4"

    let found = elseIfsIn source
    Assert.Equal<int list>([ 4; 7 ], found |> List.map (fun s -> s.Range.StartLine) |> List.sort)

    let patched =
        applyAll source (found |> List.map (fun s -> s.Range, s.ReplacementText))

    Assert.Equal(
        "module Test\nlet f (x: int) =\n    if x = 1 then 0\n    elif x = 2 then 1\n    else // fall through\n        if x = 3 then 2\n        elif x = 4 then 3\n        else 4",
        patched
    )

    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- FR0023: same-typed and churn-heavy reorders ----

let private paramOrderIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ParamOrder.find tree sourceText checkResults

[<Fact>]
let ``FR0023: two parameters of the same type are never swapped`` () =
    // svg_path's OverlapsTests: one lambda, and forty `point x y` literals
    // flipped into code that reads as vertical lines
    Assert.Empty(
        paramOrderIn
            "type Point = { X: float; Y: float }\nlet private point x y = { X = x; Y = y }\nlet private polyline (xs: float list) = xs |> List.map (fun x -> point x 0.0)\nlet baseLine = point 10.0 0.0"
    )

[<Fact>]
let ``FR0023: more direct calls flipped than lambdas collapsed is churn`` () =
    Assert.Empty(
        paramOrderIn
            "let private scale (x: float) (k: int) = x * float k\nlet a = scale 1.0 2\nlet b = scale 3.0 4\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
    )

[<Fact>]
let ``FR0023: distinct types and no more direct calls than lambdas still swap`` () =
    let source =
        "let private scale (x: float) (k: int) = x * float k\nlet a = scale 3.0 2\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"

    match paramOrderIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(
            "let private scale (k: int) (x: float) = x * float k\nlet a = scale 2 3.0\nlet doubled (xs: float list) = xs |> List.map (scale 2)",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one param-order suggestion, got %A" other

// ---- FR0101: the opening alias names the loop variable ----

let private indexedLoopsIn (source: string) =
    let tree, sourceText = parse source
    IndexedLoop.find tree sourceText

let private assertIndexedLoop (source: string) (expectedPatched: string) =
    match indexedLoopsIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one indexed-loop fix, got %A" other

[<Fact>]
let ``FR0101: an opening alias of the element names the loop variable`` () =
    // Giraffe's FormatExpressions: `for item in path do let mChar = item`
    assertIndexedLoop
        "module Test\nlet f (path: string) =\n    let mutable matchNext = false\n    for i in 0 .. path.Length - 1 do\n        let mChar = path.[i]\n\n        if matchNext then\n            printfn \"%c\" mChar\n            matchNext <- false\n        elif mChar = '%' then\n            matchNext <- true"
        "module Test\nlet f (path: string) =\n    let mutable matchNext = false\n    for mChar in path do\n        if matchNext then\n            printfn \"%c\" mChar\n            matchNext <- false\n        elif mChar = '%' then\n            matchNext <- true"

[<Fact>]
let ``FR0101: an alias beside another use of the index stays an alias`` () =
    assertIndexedLoop
        "module Test\nlet f (path: string) =\n    for i in 0 .. path.Length - 1 do\n        let mChar = path.[i]\n        printfn \"%c%c\" mChar path.[i]"
        "module Test\nlet f (path: string) =\n    for item in path do\n        let mChar = item\n        printfn \"%c%c\" mChar item"

[<Fact>]
let ``FR0101: an alias named like something bound around the loop stays an alias`` () =
    assertIndexedLoop
        "module Test\nlet f (mChar: char) (path: string) =\n    for i in 0 .. path.Length - 1 do\n        let mChar = path.[i]\n        printfn \"%c\" mChar"
        "module Test\nlet f (mChar: char) (path: string) =\n    for item in path do\n        let mChar = item\n        printfn \"%c\" mChar"

[<Fact>]
let ``FR0101: a comment between the alias and the body keeps the alias`` () =
    assertIndexedLoop
        "module Test\nlet f (path: string) =\n    for i in 0 .. path.Length - 1 do\n        let mChar = path.[i]\n        // the char under the cursor\n        printfn \"%c\" mChar"
        "module Test\nlet f (path: string) =\n    for item in path do\n        let mChar = item\n        // the char under the cursor\n        printfn \"%c\" mChar"

[<Fact>]
let ``FR0101: a typed alias keeps its annotation as an alias`` () =
    assertIndexedLoop
        "module Test\nlet f (path: string) =\n    for i in 0 .. path.Length - 1 do\n        let mChar: char = path.[i]\n        printfn \"%c\" mChar"
        "module Test\nlet f (path: string) =\n    for item in path do\n        let mChar: char = item\n        printfn \"%c\" mChar"
