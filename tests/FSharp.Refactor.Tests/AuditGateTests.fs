/// Round-2 real-repo sweep gates: FR0006 spells a nullness-annotated guard
/// parameter without `| null` (A9); FR0009 and FR0131 honour the LOWEST
/// FSharp.Core across a project's target frameworks and FR0009 leaves a
/// function that IS the FSharp.Core namesake alone (A10); FR0005 strips
/// `return! inner { return v }` only inside a builder known to pass the
/// result through (A12); FR0007 keeps a `mutable` whose comment says it
/// defeats inlining or folding (A13).
module FSharp.Refactor.Tests.AuditGateTests

open System
open System.IO
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

/// Typecheck a script with extra compiler options on top of the script
/// defaults — `--checknulls` reproduces a nullness-aware compilation.
let private parseAndCheckWith (extraOptions: string list) (source: string) =
    let sourceText = SourceText.ofString source

    let options, _ =
        checker.GetProjectOptionsFromScript("Test.fsx", sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    let options =
        { options with
            OtherOptions = Array.append options.OtherOptions (Array.ofList extraOptions)
        }

    let parseResults, answer =
        checker.ParseAndCheckFileInProject("Test.fsx", source.GetHashCode(), sourceText, options)
        |> Async.RunSynchronously

    match answer with
    | FSharpCheckFileAnswer.Succeeded c -> parseResults.ParseTree, sourceText, c
    | FSharpCheckFileAnswer.Aborted -> failwith $"typechecking aborted for:\n{source}"

let private errorsOf (check: FSharpCheckFileResults) =
    check.Diagnostics
    |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

/// Run a test with FSREF_MIN_FSHARP_CORE set, restoring it afterwards.
let private withMinCore (value: string) (body: unit -> 'T) =
    let before = Environment.GetEnvironmentVariable "FSREF_MIN_FSHARP_CORE"
    Environment.SetEnvironmentVariable("FSREF_MIN_FSHARP_CORE", value)

    try
        body ()
    finally
        Environment.SetEnvironmentVariable("FSREF_MIN_FSHARP_CORE", before)

// ---- A9: FR0006 drops the F# 9 nullness annotation ----

/// FsToolkit's tests/List.fs shape: the guard's parameter is
/// `String.IsNullOrEmpty`'s, which a nullness-aware check formats as
/// `string | null` — under the sibling net8.0 target's LangVersion 8 that
/// parses as an or-pattern (FS0018) and the whole pass was put back.
[<Literal>]
let private nullableGuardSource =
    "module Test\nopen System\nlet tryTweetOption x =\n    match x with\n    | x when String.IsNullOrEmpty x -> None\n    | _ -> Some x"

[<Fact>]
let ``FR0006 spells a nullness-annotated parameter as the plain type`` () =
    let tree, sourceText, check =
        parseAndCheckWith [ "--checknulls" ] nullableGuardSource

    // the scenario is real only when FCS formats the parameter with the
    // annotation — assert that first, so a silent change in FCS's output
    // cannot turn this test vacuous
    let lineText = sourceText.GetLineString 4

    let paramType =
        match check.GetSymbolUseAtLocation(5, 33, lineText, [ "IsNullOrEmpty" ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                v.CurriedParameterGroups.[0].[0].Type.Format symbolUse.DisplayContext
            | other -> failwithf "unexpected symbol %A" other
        | None -> failwith "IsNullOrEmpty did not resolve"

    Assert.Contains("| null", paramType)

    match ActivePattern.find true tree sourceText check with
    | [ s ] ->
        Assert.Contains("(input: string)", s.InsertText)
        Assert.DoesNotContain("null", s.InsertText)
        let patched = applyEdit nullableGuardSource s.ClauseRange s.ClauseText
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        // ... and under the nullness-aware compilation it came from
        let _, _, patchedCheck = parseAndCheckWith [ "--checknulls" ] patched
        Assert.Empty(errorsOf patchedCheck)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0006 still annotates an overloaded member's parameter`` () =
    let source =
        "module Test\nlet describe (p: string) =\n    match p with\n    | p when System.IO.Path.IsPathRooted p -> \"rooted\"\n    | p -> p"

    let tree, sourceText, check = parseAndCheck source

    match ActivePattern.find true tree sourceText check with
    | [ s ] ->
        Assert.Contains("(|IsPathRooted|_|) (input: string)", s.InsertText)
        let patched = applyEdit source s.ClauseRange s.ClauseText
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- A10: the project-minimum FSharp.Core gate ----

[<Fact>]
let ``minFSharpCoreMajor reads the leading major of the environment value`` () =
    let read (value: string) : int voption =
        withMinCore value (fun () ->
            CapabilityFix.minFSharpCoreMajor (Path.Combine(Path.GetTempPath(), "nowhere", "X.fsproj")))

    Assert.Equal(ValueNone, read null)
    Assert.Equal(ValueNone, read "")
    Assert.Equal(ValueSome 6, read "6.0.4")
    Assert.Equal(ValueSome 9, read "9.0.0.0")
    Assert.Equal(ValueNone, read "latest")

/// A project directory with a restore's `obj/project.assets.json` listing
/// the given FSharp.Core version per target framework.
let private projectWithAssets (cores: (string * string) list) =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", "assets-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory(Path.Combine(dir, "obj")) |> ignore

    let targets =
        cores
        |> List.map (fun (tfm, core) ->
            $"\"{tfm}\": {{ \"FSharp.Core/{core}\": {{ \"type\": \"package\" }}, \"Other.Lib/1.0.0\": {{ \"type\": \"package\" }} }}")
        |> String.concat ", "

    File.WriteAllText(
        Path.Combine(dir, "obj", "project.assets.json"),
        $"{{ \"version\": 3, \"targets\": {{ {targets} }}, \"libraries\": {{}} }}"
    )

    Path.Combine(dir, "Lib.fsproj")

[<Fact>]
let ``minFSharpCoreMajor reads the lowest FSharp.Core across the restore's targets`` () =
    // FsToolkit: netstandard2.0 on FSharp.Core 6, net9.0 on 9 — the file
    // compiles against both, so 6 is the floor
    let project =
        projectWithAssets [ "netstandard2.0", "6.0.4"; "net9.0", "9.0.300"; "net9.0/win-x64", "9.0.300" ]

    Assert.Equal(ValueSome 6, withMinCore null (fun () -> CapabilityFix.minFSharpCoreMajor project))

[<Fact>]
let ``minFSharpCoreMajor takes a single target's own resolution and tolerates a prerelease tag`` () =
    let project = projectWithAssets [ "net9.0", "9.0.300-beta.1" ]
    Assert.Equal(ValueSome 9, withMinCore null (fun () -> CapabilityFix.minFSharpCoreMajor project))

[<Fact>]
let ``minFSharpCoreMajor answers nothing without a restore and lets the environment override the restore`` () =
    let unrestored =
        Path.Combine(Path.GetTempPath(), "fsref-tests", "no-restore-" + Guid.NewGuid().ToString "N", "Lib.fsproj")

    Assert.Equal(ValueNone, withMinCore null (fun () -> CapabilityFix.minFSharpCoreMajor unrestored))

    let project = projectWithAssets [ "netstandard2.0", "6.0.4"; "net9.0", "9.0.300" ]
    Assert.Equal(ValueSome 8, withMinCore "8.0.100" (fun () -> CapabilityFix.minFSharpCoreMajor project))

/// A CLI context for a script written to a temp file, typechecked with the
/// script's own (current) FSharp.Core reference — what a wide framework
/// pass sees of its own compilation.
let private scriptContext (source: string) : CliContext =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", "gate-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore
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

    Assert.Empty(errorsOf checkResults)

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

let private fixTexts (messages: Message list) =
    messages |> List.collect (fun m -> m.Fixes |> List.map (fun f -> f.ToText))

/// FsToolkit's src Result.fs shapes, outside their defining module: an
/// `isOk` match (FSharp.Core 9's `Result.isOk`) beside a `map` match
/// (FSharp.Core 4.1's `Result.map`).
[<Literal>]
let private core9AndOlderSource =
    "let check (r: Result<int, string>) =\n    match r with\n    | Ok _ -> true\n    | Error _ -> false\n\nlet bump (r: Result<int, string>) =\n    match r with\n    | Ok v -> Ok (v + 1)\n    | Error e -> Error e\n"

[<Fact>]
let ``FR0009 offers the FSharp.Core 9 rewrite against the compilation's own reference`` () =
    let ctx = scriptContext core9AndOlderSource

    let fixes =
        withMinCore null (fun () -> Analyzers.resultModuleCliAnalyzer ctx |> Async.RunSynchronously |> fixTexts)

    Assert.Contains("r |> Result.isOk", fixes)
    Assert.Contains("r |> Result.map (fun v -> v + 1)", fixes)

[<Fact>]
let ``FR0009 withholds the FSharp.Core 9 rewrite when a narrower framework's FSharp.Core is older`` () =
    let ctx = scriptContext core9AndOlderSource

    let fixes =
        withMinCore "6.0.0.0" (fun () -> Analyzers.resultModuleCliAnalyzer ctx |> Async.RunSynchronously |> fixTexts)

    Assert.DoesNotContain("r |> Result.isOk", fixes)
    // the older rewrite is unaffected by the gate
    Assert.Contains("r |> Result.map (fun v -> v + 1)", fixes)

[<Fact>]
let ``FR0009 withholds the FSharp.Core 9 rewrite from the restore's own record of an older target`` () =
    // no environment: the assets file beside the compilation's project says
    // another target compiles this file against FSharp.Core 6 — the same
    // answer an editor gets, where no driver runs
    let ctx = scriptContext core9AndOlderSource
    let projectDir = Path.GetDirectoryName ctx.ProjectOptions.ProjectFileName
    Directory.CreateDirectory(Path.Combine(projectDir, "obj")) |> ignore

    File.WriteAllText(
        Path.Combine(projectDir, "obj", "project.assets.json"),
        "{ \"version\": 3, \"targets\": { \"netstandard2.0\": { \"FSharp.Core/6.0.4\": {} }, \"net9.0\": { \"FSharp.Core/9.0.300\": {} } } }"
    )

    let fixes =
        withMinCore null (fun () -> Analyzers.resultModuleCliAnalyzer ctx |> Async.RunSynchronously |> fixTexts)

    Assert.DoesNotContain("r |> Result.isOk", fixes)
    Assert.Contains("r |> Result.map (fun v -> v + 1)", fixes)

[<Fact>]
let ``FR0009 withholds Result.iter when a narrower framework's FSharp.Core predates 6.0.6`` () =
    // ResultModule.Iterate shipped with the rest of the Result/Option
    // parity set in FSharp.Core 6.0.6; 6.0.0-6.0.5 share its assembly
    // version 6.0.0.0 and have only map, bind and mapError
    let ctx =
        scriptContext
            "let show (r: Result<int, string>) =\n    match r with\n    | Ok v -> printfn \"%d\" v\n    | Error _ -> ()\n"

    let fixes =
        withMinCore "6.0.0.0" (fun () -> Analyzers.resultModuleCliAnalyzer ctx |> Async.RunSynchronously |> fixTexts)

    Assert.DoesNotContain(fixes, fun t -> t.Contains "Result.iter")

[<Literal>]
let private tailRecursiveSource =
    "module M\nlet rec sum (acc: int) (xs: int list) =\n    match xs with\n    | [] -> acc\n    | h :: t -> sum (acc + h) t"

[<Fact>]
let ``FR0131 withholds TailCall when a narrower framework's FSharp.Core predates it`` () =
    let tree, sourceText, check = parseAndCheck tailRecursiveSource

    Assert.Empty(withMinCore "6.0.4" (fun () -> RecTailCall.find tree sourceText check))

    Assert.Single(withMinCore "8.0.0" (fun () -> RecTailCall.find tree sourceText check))
    |> ignore

    Assert.Single(withMinCore null (fun () -> RecTailCall.find tree sourceText check))
    |> ignore

// ---- A10: FR0009 leaves the definition of the namesake alone ----

let private resultSuggestions (source: string) =
    let tree, sourceText, check = parseAndCheck source
    ResultModule.find tree sourceText check

[<Fact>]
let ``FR0009 does not rewrite a Result module's own isOk into Result.isOk`` () =
    // FsToolkit src/Result.fs: `module Result = let inline isOk ...`
    Assert.Empty(
        resultSuggestions
            "module Test\n[<RequireQualifiedAccess>]\nmodule Result =\n    let inline isOk (value: Result<'ok, 'error>) : bool =\n        match value with\n        | Ok _ -> true\n        | Error _ -> false"
    )

[<Fact>]
let ``FR0009 does not rewrite a Result module's own map into Result.map`` () =
    Assert.Empty(
        resultSuggestions
            "module Test\nmodule Result =\n    let inline map ([<InlineIfLambda>] mapper: 'a -> 'b) (input: Result<'a, 'e>) : Result<'b, 'e> =\n        match input with\n        | Ok x -> Ok(mapper x)\n        | Error e -> Error e"
    )

[<Fact>]
let ``FR0009 does not rewrite the namesake in a file-level Result module`` () =
    Assert.Empty(
        resultSuggestions
            "module Lib.Result\nlet inline defaultValue (ifError: 'ok) (result: Result<'ok, 'error>) : 'ok =\n    match result with\n    | Ok x -> x\n    | Error _ -> ifError"
    )

[<Fact>]
let ``FR0009 still rewrites a differently named function inside a Result module`` () =
    match
        resultSuggestions
            "module Test\nmodule Result =\n    let check (value: Result<int, string>) : bool =\n        match value with\n        | Ok _ -> true\n        | Error _ -> false"
    with
    | [ s ] -> Assert.Equal("Result.isOk", s.Target)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0009 still rewrites an isOk defined outside a Result module`` () =
    match
        resultSuggestions
            "module Test\nmodule Checks =\n    let isOk (value: Result<int, string>) : bool =\n        match value with\n        | Ok _ -> true\n        | Error _ -> false"
    with
    | [ s ] -> Assert.Equal("Result.isOk", s.Target)
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- A12: FR0005's return! strip needs a pass-through outer builder ----

let private returnBangStrips (source: string) =
    let tree, sourceText = parse source

    CeStrip.find tree sourceText
    |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ReturnBangIdentity)

[<Fact>]
let ``FR0005 withholds the return! strip inside a builder with its own Source conversion`` () =
    // FsToolkit IcedTasks tests: cancellableTaskResult's return! turns the
    // async's Choice into a Result; `return Choice1Of2 data` is a type error
    Assert.Empty(
        returnBangStrips
            "module Test\nlet f (data: int) =\n    let ctr = cancellableTaskResult { return! async { return Choice1Of2 data } }\n    ctr"
    )

[<Fact>]
let ``FR0005 withholds the return! strip inside any builder it does not know`` () =
    Assert.Empty(returnBangStrips "module Test\nlet f (data: int) = taskResult { return! task { return data } }")
    Assert.Empty(returnBangStrips "module Test\nlet f (data: int) = asyncResult { return! async { return data } }")
    Assert.Empty(returnBangStrips "module Test\nlet f (data: int) = valueTask { return! task { return data } }")

[<Fact>]
let ``FR0005 withholds the return! strip of a task inside async`` () =
    // async's return! takes no Task: not even the original compiles
    Assert.Empty(returnBangStrips "module Test\nlet f (data: int) = async { return! task { return data } }")

[<Fact>]
let ``FR0005 still strips an async returned from a task`` () =
    let source =
        "module Test\nlet f (data: int) = task { return! async { return data } }"

    match returnBangStrips source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal("module Test\nlet f (data: int) = task { return data }", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one strip, got %A" other

[<Fact>]
let ``FR0005 still strips an async returned from an async`` () =
    let source =
        "module Test\nlet f (data: int) = async { return! async { return data } }"

    match returnBangStrips source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal("module Test\nlet f (data: int) = async { return data }", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one strip, got %A" other

[<Fact>]
let ``FR0005 still strips a task returned from a backgroundTask`` () =
    let source =
        "module Test\nlet f (t: System.Threading.Tasks.Task<int>) = backgroundTask { return! task { return! t } }"

    match returnBangStrips source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal("module Test\nlet f (t: System.Threading.Tasks.Task<int>) = backgroundTask { return! t }", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one strip, got %A" other

// ---- A13: FR0007 respects a comment naming the reason ----

let private mutableSuggestions (source: string) =
    let tree, sourceText, check = parseAndCheck source
    MutableRemoval.find tree sourceText check

[<Fact>]
let ``FR0007 keeps a mutable whose comment above says it defeats inlining`` () =
    // SageFs LiveValueTreeTests.fs: immutable, the Release optimiser folds
    // the constant into the closure and the test's assertion fails
    Assert.Empty(
        mutableSuggestions
            "let f () =\n    // Use a non-constant capture so the compiler cannot inline it away.\n    let mutable captured = 42\n    let g = fun (x: int) -> x + captured\n    g 1"
    )

[<Fact>]
let ``FR0007 keeps a mutable whose trailing comment mentions folding`` () =
    Assert.Empty(
        mutableSuggestions
            "let f () =\n    let mutable captured = 7 // keeps the constant from being folded\n    captured + 1"
    )

[<Fact>]
let ``FR0007 keeps a mutable whose comment mentions the optimiser`` () =
    Assert.Empty(
        mutableSuggestions
            "let f () =\n    // the OPTIMIZER must not see through this\n    let mutable captured = 7\n    captured + 1"
    )

[<Fact>]
let ``FR0007 keeps a type-level mutable whose comment above says it defeats inlining`` () =
    Assert.Empty(
        mutableSuggestions
            "type T() =\n    // a real field, not an inlined constant\n    let mutable captured = 42\n    member _.Value = captured"
    )

[<Fact>]
let ``FR0007 still removes a mutable under an unrelated comment`` () =
    match mutableSuggestions "let f () =\n    // the answer\n    let mutable x = 42\n    x + 1" with
    | [ s ] -> Assert.Equal("x", s.Name)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0007 reads only the line directly above`` () =
    match mutableSuggestions "let f () =\n    // cannot inline this\n\n    let mutable x = 42\n    x + 1" with
    | [ s ] -> Assert.Equal("x", s.Name)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0007 ignores a fold in the binding's code`` () =
    match mutableSuggestions "let f (xs: int list) =\n    let mutable acc = List.fold (+) 0 xs\n    acc + 1" with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected one suggestion, got %A" other
