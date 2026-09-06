/// Test helpers: parse an F# source string with FCS (no project needed) and
/// apply a suggested edit back to the source so tests can verify the result
/// still parses.
module FSharp.Refactor.Tests.Parsing

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

let private checker = FSharpChecker.Create()

/// Parse under a chosen file name. A `.fsx` name makes FCS parse the text
/// as a script, which needs no leading namespace or module — parsing script
/// content as `.fs` fails with "Files in libraries or multiple-file
/// applications must begin with a namespace or module declaration".
let parseNamed (fileName: string) (source: string) : ParsedInput * ISourceText =
    let sourceText = SourceText.ofString source

    let parsingOptions =
        { FSharpParsingOptions.Default with
            SourceFiles = [| fileName |] }

    let result =
        checker.ParseFile(fileName, sourceText, parsingOptions)
        |> Async.RunSynchronously

    if result.ParseHadErrors then
        failwithf "Test input does not parse: %A" result.Diagnostics

    result.ParseTree, sourceText

/// Parse without failing on errors: returns the recovered tree and whether
/// the parser complained. Malformed input still yields a partial tree —
/// which is exactly what analyzers see in an editor mid-keystroke, so the
/// rules must survive it rather than throw.
let tryParseNamed (fileName: string) (source: string) : ParsedInput * bool * ISourceText =
    let sourceText = SourceText.ofString source

    let parsingOptions =
        { FSharpParsingOptions.Default with
            SourceFiles = [| fileName |] }

    let result =
        checker.ParseFile(fileName, sourceText, parsingOptions)
        |> Async.RunSynchronously

    result.ParseTree, result.ParseHadErrors, sourceText

/// True when the source string parses without errors under a chosen file name.
let parsesCleanlyNamed (fileName: string) (source: string) : bool =
    let sourceText = SourceText.ofString source

    let parsingOptions =
        { FSharpParsingOptions.Default with
            SourceFiles = [| fileName |] }

    let result =
        checker.ParseFile(fileName, sourceText, parsingOptions)
        |> Async.RunSynchronously

    not result.ParseHadErrors

/// Parse a standalone source string; fails the test on parse errors so a
/// broken test input is caught immediately.
let parse (source: string) : ParsedInput * ISourceText = parseNamed "Test.fs" source

/// True when the source string parses without errors.
let parsesCleanly (source: string) : bool = parsesCleanlyNamed "Test.fs" source

/// Parse and fully typecheck a source string as a script. Returns the parse
/// tree, source text, and check results (which may contain error diagnostics —
/// callers assert on them as needed).
let parseAndCheck (source: string) : ParsedInput * ISourceText * FSharpCheckFileResults =
    let sourceText = SourceText.ofString source

    let options, _ =
        // assumeDotNetFramework=false: resolve modern .NET references, so
        // APIs like Dictionary.TryAdd (absent from .NET Framework) typecheck
        checker.GetProjectOptionsFromScript("Test.fsx", sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    let parseResults, answer =
        checker.ParseAndCheckFileInProject("Test.fsx", source.GetHashCode(), sourceText, options)
        |> Async.RunSynchronously

    match answer with
    | FSharpCheckFileAnswer.Succeeded checkResults -> parseResults.ParseTree, sourceText, checkResults
    | FSharpCheckFileAnswer.Aborted -> failwith $"Typechecking was aborted, calling parseAndCheck with source: {source}"

/// True when the source typechecks as a script without errors.
let typechecksCleanly (source: string) : bool =
    let _, _, checkResults = parseAndCheck source

    checkResults.Diagnostics
    |> Array.forall (fun d -> d.Severity <> FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

/// Replace `range` in `source` with `newText` (ranges are 1-based lines,
/// 0-based columns).
let applyEdit (source: string) (range: range) (newText: string) : string =
    let lines = source.Replace("\r\n", "\n").Split '\n'

    let before = [ for i in 0 .. range.StartLine - 2 -> lines.[i] ]

    let after = [ for i in range.EndLine .. lines.Length - 1 -> lines.[i] ]

    let startLinePrefix = lines.[range.StartLine - 1].Substring(0, range.StartColumn)
    let endLineSuffix = lines.[range.EndLine - 1].Substring range.EndColumn

    let patchedMiddle = startLinePrefix + newText + endLineSuffix

    String.concat "\n" (before @ [ patchedMiddle ] @ after)

/// Typecheck a REAL two-file project in a temp directory — the harness for
/// cross-file migrations. Returns the first file's parse tree, source and
/// check results, the whole-project results, the two paths, and a recheck
/// function for the patched pair. ProjectSources is configured so rules
/// can classify uses in the sibling file.
let parseAndCheckPair (sourceA: string) (sourceB: string) =
    let dir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), "fsref-tests", System.Guid.NewGuid().ToString "N")

    System.IO.Directory.CreateDirectory dir |> ignore
    let pathA = System.IO.Path.Combine(dir, "A.fs")
    let pathB = System.IO.Path.Combine(dir, "B.fs")
    System.IO.File.WriteAllText(pathA, sourceA)
    System.IO.File.WriteAllText(pathB, sourceB)

    let probeOptions, _ =
        checker.GetProjectOptionsFromScript(
            System.IO.Path.Combine(dir, "probe.fsx"),
            SourceText.ofString "",
            assumeDotNetFramework = false
        )
        |> Async.RunSynchronously

    let options =
        { probeOptions with
            ProjectFileName = System.IO.Path.Combine(dir, "Pair.fsproj")
            SourceFiles = [| pathA; pathB |] }

    let projectResults = checker.ParseAndCheckProject options |> Async.RunSynchronously

    let sourceTextA = SourceText.ofString sourceA

    let parseResultsA, answerA =
        checker.ParseAndCheckFileInProject(pathA, 0, sourceTextA, options)
        |> Async.RunSynchronously

    let checkA =
        match answerA with
        | FSharpCheckFileAnswer.Succeeded c -> c
        | FSharpCheckFileAnswer.Aborted ->
            failwith $"pair typecheck aborted, calling parseAndCheckPair with sourceA: {sourceA}, sourceB: {sourceB}"

    let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

    FSharp.Refactor.ProjectSources.configure (
        Some(fun path ->
            let text = SourceText.ofString (System.IO.File.ReadAllText path)
            let r = checker.ParseFile(path, text, parsingOptions) |> Async.RunSynchronously
            Some(r.ParseTree, text))
    )

    let recheck (patchedA: string) (patchedB: string) =
        System.IO.File.WriteAllText(pathA, patchedA)
        System.IO.File.WriteAllText(pathB, patchedB)

        let results =
            checker.ParseAndCheckProject { options with Stamp = Some 1L }
            |> Async.RunSynchronously

        results.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

    parseResultsA.ParseTree, sourceTextA, checkA, projectResults, pathA, pathB, recheck

/// Like parseAndCheckPair, but the file under test is B: it sees A's
/// definitions the way a later file of a project sees the earlier ones.
let parseAndCheckSecond (sourceA: string) (sourceB: string) : ParsedInput * ISourceText * FSharpCheckFileResults =
    let dir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), "fsref-tests", System.Guid.NewGuid().ToString "N")

    System.IO.Directory.CreateDirectory dir |> ignore
    let pathA = System.IO.Path.Combine(dir, "A.fs")
    let pathB = System.IO.Path.Combine(dir, "B.fs")
    System.IO.File.WriteAllText(pathA, sourceA)
    System.IO.File.WriteAllText(pathB, sourceB)

    let probeOptions, _ =
        checker.GetProjectOptionsFromScript(
            System.IO.Path.Combine(dir, "probe.fsx"),
            SourceText.ofString "",
            assumeDotNetFramework = false
        )
        |> Async.RunSynchronously

    let options =
        { probeOptions with
            ProjectFileName = System.IO.Path.Combine(dir, "Second.fsproj")
            SourceFiles = [| pathA; pathB |] }

    let sourceTextB = SourceText.ofString sourceB

    let parseResultsB, answerB =
        checker.ParseAndCheckFileInProject(pathB, 0, sourceTextB, options)
        |> Async.RunSynchronously

    match answerB with
    | FSharpCheckFileAnswer.Succeeded c -> parseResultsB.ParseTree, sourceTextB, c
    | FSharpCheckFileAnswer.Aborted -> failwith $"second-file typecheck aborted for:\n{sourceB}"

/// Typecheck a REAL signature + implementation pair (`M.fsi`, `M.fs`) in a
/// temp directory: the harness for rules whose fixes must stay within a
/// signature's types. Returns the implementation's parse tree, source and
/// check results, and a recheck of a patched implementation returning the
/// project's error messages.
let parseAndCheckSigned (signature: string) (implementation: string) =
    let dir =
        System.IO.Path.Combine(System.IO.Path.GetTempPath(), "fsref-tests", System.Guid.NewGuid().ToString "N")

    System.IO.Directory.CreateDirectory dir |> ignore
    let pathSig = System.IO.Path.Combine(dir, "M.fsi")
    let pathImpl = System.IO.Path.Combine(dir, "M.fs")
    System.IO.File.WriteAllText(pathSig, signature)
    System.IO.File.WriteAllText(pathImpl, implementation)

    let probeOptions, _ =
        checker.GetProjectOptionsFromScript(
            System.IO.Path.Combine(dir, "probe.fsx"),
            SourceText.ofString "",
            assumeDotNetFramework = false
        )
        |> Async.RunSynchronously

    let options =
        { probeOptions with
            ProjectFileName = System.IO.Path.Combine(dir, "Signed.fsproj")
            SourceFiles = [| pathSig; pathImpl |] }

    let projectErrors (results: FSharpCheckProjectResults) =
        results.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
        |> Array.map (fun d -> $"FS{d.ErrorNumber:D4} {d.Message}")

    let baseline =
        checker.ParseAndCheckProject options |> Async.RunSynchronously |> projectErrors

    let sourceText = SourceText.ofString implementation

    let parseResults, answer =
        checker.ParseAndCheckFileInProject(pathImpl, 0, sourceText, options)
        |> Async.RunSynchronously

    let check =
        match answer with
        | FSharpCheckFileAnswer.Succeeded c -> c
        | FSharpCheckFileAnswer.Aborted -> failwith "signed typecheck aborted"

    let recheck (patched: string) =
        System.IO.File.WriteAllText(pathImpl, patched)

        checker.ParseAndCheckProject { options with Stamp = Some 1L }
        |> Async.RunSynchronously
        |> projectErrors

    parseResults.ParseTree, sourceText, check, baseline, recheck
