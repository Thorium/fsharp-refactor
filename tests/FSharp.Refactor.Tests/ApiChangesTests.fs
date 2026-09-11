/// Cross-file (API-changing) refactorings, the `--api-changes` pass of the
/// apply tool. A synthetic two-file project on disk stands in for a real
/// one: script-resolved framework references plus explicit SourceFiles.
module FSharp.Refactor.Tests.ApiChangesTests

open System
open System.IO
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor
open Xunit

let private checker = FSharpChecker.Create()

/// Project options over the given real files, with references borrowed
/// from a throwaway script (so FSharp.Core and the framework resolve).
let private optionsFor (dir: string) (files: string list) =
    let probe = Path.Combine(dir, "probe.fsx")

    let scriptOptions, _ =
        checker.GetProjectOptionsFromScript(probe, SourceText.ofString "", assumeDotNetFramework = false)
        |> Async.RunSynchronously

    { scriptOptions with
        ProjectFileName = Path.Combine(dir, "Test.fsproj")
        SourceFiles = Array.ofList files }

let private contextFor (options: FSharpProjectOptions) (file: string) : Text.FileContext =
    let sourceText = SourceText.ofString (File.ReadAllText file)
    let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

    let parsed =
        checker.ParseFile(file, sourceText, parsingOptions) |> Async.RunSynchronously

    { FileName = file
      Source = sourceText
      ParseTree = parsed.ParseTree }

let private checkFile (options: FSharpProjectOptions) (ctx: Text.FileContext) =
    let _, answer =
        checker.ParseAndCheckFileInProject(ctx.FileName, 0, ctx.Source, options)
        |> Async.RunSynchronously

    match answer with
    | FSharpCheckFileAnswer.Succeeded check -> check
    | FSharpCheckFileAnswer.Aborted ->
        failwith $"typechecking aborted, calling checkFile with options: {options}, ctx: {ctx}"

/// Write a definition file and a using file into a throwaway project, then
/// hand the scaffolding a project-wide rule needs to `body`.
let private withTwoFiles
    (defSource: string)
    (useSource: string)
    (body:
        Text.FileContext
            -> FSharpCheckFileResults
            -> FSharpCheckProjectResults
            -> (string -> Text.FileContext option)
            -> 'Result)
    : 'Result =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-api-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let fileA = Path.Combine(dir, "LibA.fs")
        let fileB = Path.Combine(dir, "LibB.fs")
        File.WriteAllText(fileA, defSource)
        File.WriteAllText(fileB, useSource)

        let options = optionsFor dir [ fileA; fileB ]
        let project = checker.ParseAndCheckProject options |> Async.RunSynchronously

        let contexts =
            System.Collections.Generic.Dictionary<string, Text.FileContext>(StringComparer.OrdinalIgnoreCase)

        contexts.[Path.GetFullPath fileA] <- contextFor options fileA
        contexts.[Path.GetFullPath fileB] <- contextFor options fileB

        let fileLookup (name: string) =
            match contexts.TryGetValue(Path.GetFullPath name) with
            | true, ctx -> Some ctx
            | false, _ -> None

        let check = checkFile options contexts.[fileA]

        body contexts.[Path.GetFullPath fileA] check project fileLookup
    finally
        Directory.Delete(dir, true)

/// FR0090, as (function name, [file, original, replacement]).
let private findAcrossTwoFiles (defSource: string) (useSource: string) =
    withTwoFiles defSource useSource (fun ctx check project fileLookup ->
        TupleParams.findApiChanges ctx check project fileLookup Visibility.unknownOutside
        |> List.map (fun s ->
            s.FunctionName,
            s.Edits
            |> List.map (fun e -> Path.GetFileName e.Range.FileName, e.Original, e.Replacement)))

/// FR0091, in the same shape.
let private findParamOrderAcrossTwoFiles (defSource: string) (useSource: string) =
    withTwoFiles defSource useSource (fun ctx check project fileLookup ->
        ParamOrder.findApiChanges ctx check project fileLookup Visibility.unknownOutside
        |> List.map (fun s ->
            s.FunctionName,
            s.Edits
            |> List.map (fun (r, original, replacement) -> Path.GetFileName r.FileName, original, replacement)))

[<Fact>]
let ``internal tupled function is curried with call sites in another file`` () =
    let found =
        findAcrossTwoFiles
            "module LibA\n\nlet internal add (a, b) = a + b\n"
            "module LibB\n\nlet total = LibA.add (1, 2)\nlet more = LibA.add (total, 4)\n"

    match found with
    | [ name, edits ] ->
        Assert.Equal("add", name)

        Assert.Equal<(string * string * string) list>(
            [ "LibA.fs", "(a, b)", "a b"
              "LibB.fs", "(1, 2)", "1 2"
              "LibB.fs", "(total, 4)", "total 4" ],
            edits
        )
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``a public function is never curried — its callers may be outside the project`` () =
    // from the corpus (SQLProvider): currying the public
    // QueryFactory.createRelated in SQLProvider.Common broke
    // SQLProvider.Runtime, a sibling project this scan cannot see —
    // "every use covered" passes vacuously for uses the checker never loads
    let found =
        findAcrossTwoFiles "module LibA\n\nlet add (a, b) = a + b\n" "module LibB\n\nlet total = LibA.add (1, 2)\n"

    Assert.Empty found

[<Fact>]
let ``a first-class use anywhere in the project suppresses the change`` () =
    let found =
        findAcrossTwoFiles
            "module LibA\n\nlet internal add (a, b) = a + b\n"
            "module LibB\n\nlet f = LibA.add\nlet total = f (1, 2)\n"

    Assert.Empty found

[<Fact>]
let ``self-nested call sites suppress the change`` () =
    // `add (add (1, 2), 3)`: the inner call edit nests inside the outer
    // call-tuple edit, so the suggestion cannot apply atomically
    let found =
        findAcrossTwoFiles
            "module LibA\n\nlet internal add (a, b) = a + b\n"
            "module LibB\n\nlet total = LibA.add (LibA.add (1, 2), 3)\n"

    Assert.Empty found

// ---- FR0091 ParamOrder, project-wide ----

[<Fact>]
let ``internal function is reordered with call sites in another file`` () =
    let found =
        findParamOrderAcrossTwoFiles
            "module LibA\n\nlet internal scale (x: int) (k: string) = string x + k\n"
            "module LibB\n\nlet labels (xs: int list) = xs |> List.map (fun x -> LibA.scale x \"m\")\nlet one = LibA.scale 3 \"cm\"\n"

    match found with
    | [ name, edits ] ->
        Assert.Equal("scale", name)

        Assert.Equal<(string * string * string) list>(
            [ "LibA.fs", "(x: int)", "(k: string)"
              "LibA.fs", "(k: string)", "(x: int)"
              // the lambda's own range, inside the parens List.map needs
              "LibB.fs", "fun x -> LibA.scale x \"m\"", "LibA.scale \"m\""
              "LibB.fs", "3", "\"cm\""
              "LibB.fs", "\"cm\"", "3" ],
            edits
        )
    | other -> failwithf "expected one reorder suggestion, got %A" other

[<Fact>]
let ``interchangeable parameter types block the reorder`` () =
    // an out-of-project caller would keep compiling and silently swap its
    // two string arguments; different types would fail the build instead
    let found =
        findParamOrderAcrossTwoFiles
            "module LibA\n\nlet internal join (x: string) (k: string) = x + k\n"
            "module LibB\n\nlet labels (xs: string list) = xs |> List.map (fun x -> LibA.join x \"m\")\n"

    Assert.Empty found

[<Fact>]
let ``generic parameters count as interchangeable`` () =
    let found =
        findParamOrderAcrossTwoFiles
            "module LibA\n\nlet internal pairUp (x: 'a) (k: 'b) = x, k\n"
            "module LibB\n\nlet labels (xs: int list) = xs |> List.map (fun x -> LibA.pairUp x \"m\")\n"

    Assert.Empty found

[<Fact>]
let ``a reorder with no eta-blocking lambda anywhere is churn`` () =
    let found =
        findParamOrderAcrossTwoFiles
            "module LibA\n\nlet internal scale (x: int) (k: string) = string x + k\n"
            "module LibB\n\nlet one = LibA.scale 3 \"cm\"\n"

    Assert.Empty found

[<Fact>]
let ``a first-class use in another file blocks the reorder`` () =
    let found =
        findParamOrderAcrossTwoFiles
            "module LibA\n\nlet internal scale (x: int) (k: string) = string x + k\n"
            "module LibB\n\nlet labels (xs: int list) = xs |> List.map (fun x -> LibA.scale x \"m\")\nlet f = LibA.scale\n"

    Assert.Empty found

[<Fact>]
let ``a private function is left to the single-file rule`` () =
    let found =
        findAcrossTwoFiles
            "module LibA\n\nlet private add (a, b) = a + b\nlet internal sum = add (1, 2)\n"
            "module LibB\n\nlet x = 1\n"

    Assert.Empty found

/// A definition file, a project file using it, and a SCRIPT that `#load`s
/// the definition — the shape --api-changes has to survive. The script is
/// a SEPARATE compilation, so its calls never appear in the project's
/// symbol tables; the tool supplies them through `Outside.Uses`, matched by
/// full name because the script's symbol is a different instance.
///
/// `registerScript` decides whether the script's parse tree is available.
/// It stands in for a call site the tool cannot render, which must make
/// the whole change stand down rather than reshape a definition whose
/// caller stays in the old shape.
let private withScriptCallSite (defSource: string) (useSource: string) (scriptSource: string) (registerScript: bool) =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-script-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let fileA = Path.Combine(dir, "LibA.fs")
        let fileB = Path.Combine(dir, "LibB.fs")
        let script = Path.Combine(dir, "use.fsx")
        File.WriteAllText(fileA, defSource)
        File.WriteAllText(fileB, useSource)
        File.WriteAllText(script, scriptSource)

        let options = optionsFor dir [ fileA; fileB ]
        let project = checker.ParseAndCheckProject options |> Async.RunSynchronously

        let scriptText = SourceText.ofString scriptSource

        let scriptOptions, _ =
            checker.GetProjectOptionsFromScript(script, scriptText, assumeDotNetFramework = false, useFsiAuxLib = true)
            |> Async.RunSynchronously

        let scriptProject =
            checker.ParseAndCheckProject scriptOptions |> Async.RunSynchronously

        // only uses IN THE SCRIPT: the #loaded file is part of this
        // compilation too, and the project pass already owns those
        let scriptUses =
            scriptProject.GetAllUsesOfAllSymbols()
            |> Array.filter (fun u ->
                not u.IsFromDefinition
                && String.Equals(
                    Path.GetFullPath u.Range.FileName,
                    Path.GetFullPath script,
                    StringComparison.OrdinalIgnoreCase
                ))

        let fullName (s: FSharp.Compiler.Symbols.FSharpSymbol) =
            try
                Some s.FullName
            with _ ->
                None

        let extraUses (symbol: FSharp.Compiler.Symbols.FSharpSymbol) =
            match fullName symbol with
            | Some name -> scriptUses |> Array.filter (fun u -> fullName u.Symbol = Some name)
            | None -> [||]

        let contexts =
            System.Collections.Generic.Dictionary<string, Text.FileContext>(StringComparer.OrdinalIgnoreCase)

        contexts.[Path.GetFullPath fileA] <- contextFor options fileA
        contexts.[Path.GetFullPath fileB] <- contextFor options fileB

        if registerScript then
            let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions scriptOptions

            let parsed =
                checker.ParseFile(script, scriptText, parsingOptions) |> Async.RunSynchronously

            contexts.[Path.GetFullPath script] <-
                { FileName = script
                  Source = scriptText
                  ParseTree = parsed.ParseTree }

        let fileLookup (name: string) =
            match contexts.TryGetValue(Path.GetFullPath name) with
            | true, ctx -> Some ctx
            | false, _ -> None

        let ctx = contexts.[Path.GetFullPath fileA]
        let check = checkFile options ctx

        TupleParams.findApiChanges
            ctx
            check
            project
            fileLookup
            { Visibility.unknownOutside with
                Uses = extraUses }
        |> List.map (fun s ->
            s.FunctionName,
            s.Edits
            |> List.map (fun e -> Path.GetFileName e.Range.FileName, e.Original, e.Replacement))
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``FR0090 rewrites the call site inside a #loading script`` () =
    let found =
        withScriptCallSite
            "module LibA\n\nlet internal add (a: int, b: int) = a + b\n"
            "module LibB\n\nlet run () = LibA.add (1, 2)\n"
            "#load \"LibA.fs\"\n\nprintfn \"%d\" (LibA.add (3, 4))\n"
            true

    let edits = found |> List.collect snd

    Assert.Contains(edits, (fun (file, _, _) -> file = "use.fsx"))
    Assert.Contains(edits, (fun (_, original, replacement) -> original = "(3, 4)" && replacement = "3 4"))

[<Fact>]
let ``FR0090 stands down when a script call site cannot be rendered`` () =
    // the script calls it, but its parse tree is unavailable: reshaping the
    // definition would leave the script calling the old shape
    let found =
        withScriptCallSite
            "module LibA\n\nlet internal add (a: int, b: int) = a + b\n"
            "module LibB\n\nlet run () = LibA.add (1, 2)\n"
            "#load \"LibA.fs\"\n\nprintfn \"%d\" (LibA.add (3, 4))\n"
            false

    Assert.Empty found

// ---- the world outside the compilation: sibling projects and friends ----

/// FR0090 over the two files, with the host's account of what lies
/// outside the compilation.
let private findWithOutside (outside: Visibility.Outside) (defSource: string) (useSource: string) =
    withTwoFiles defSource useSource (fun ctx check project fileLookup ->
        TupleParams.findApiChanges ctx check project fileLookup outside
        |> List.map (fun s ->
            s.FunctionName,
            s.Edits
            |> List.map (fun e -> Path.GetFileName e.Range.FileName, e.Original, e.Replacement)))

[<Fact>]
let ``a public tupled function is curried once every referencing compilation has been read`` () =
    // the host has enumerated the solution, typechecked every project
    // that references this one and indexed their uses: "every use
    // covered" is a statement about every use again
    let found =
        findWithOutside
            { Visibility.unknownOutside with
                PublicRead = (fun () -> true) }
            "module LibA\n\nlet add (a, b) = a + b\n"
            "module LibB\n\nlet total = LibA.add (1, 2)\n"

    match found with
    | [ name, edits ] ->
        Assert.Equal("add", name)

        Assert.Equal<(string * string * string) list>([ "LibA.fs", "(a, b)", "a b"; "LibB.fs", "(1, 2)", "1 2" ], edits)
    | other -> failwithf "expected the public function curried, got %A" other

[<Fact>]
let ``FR0091 reorders a public function once every referencing compilation has been read`` () =
    let found =
        withTwoFiles
            "module LibA\n\nlet scale (x: int) (k: string) = string x + k\n"
            "module LibB\n\nlet labels (xs: int list) = xs |> List.map (fun x -> LibA.scale x \"m\")\n"
            (fun ctx check project fileLookup ->
                ParamOrder.findApiChanges
                    ctx
                    check
                    project
                    fileLookup
                    { Visibility.unknownOutside with
                        PublicRead = (fun () -> true) }
                |> List.map (fun s -> s.FunctionName))

    Assert.Equal<string list>([ "scale" ], found)

[<Fact>]
let ``an internal function of an assembly with friends waits for every friend to be read`` () =
    // InternalsVisibleTo opens the internal declarations to Lib.Tests,
    // whose calls are in neither the project's symbol tables nor its
    // verification build; the change stands down until the host has read
    // that friend's compilation — and goes ahead once it has
    let source =
        "module LibA\n\nopen System.Runtime.CompilerServices\n\n[<assembly: InternalsVisibleTo(\"Lib.Tests, PublicKey=0024000004800000\")>]\ndo ()\n\nlet internal add (a, b) = a + b\n"

    let useSource = "module LibB\n\nlet total = LibA.add (1, 2)\n"

    Assert.Empty(findWithOutside Visibility.unknownOutside source useSource)

    Assert.Empty(
        findWithOutside
            { Visibility.unknownOutside with
                AssemblyRead = (fun name -> name = "Other.Tests") }
            source
            useSource
    )

    match
        findWithOutside
            { Visibility.unknownOutside with
                AssemblyRead = (fun name -> name = "Lib.Tests") }
            source
            useSource
    with
    | [ "add", _ ] -> ()
    | other -> failwithf "expected the internal function curried once its friend was read, got %A" other

/// A LIBRARY project and a TEST project that references it — as two
/// compilations wired the way the tool wires them: the test project's
/// options carry a `-r:` to the library's output, replaced by an in-memory
/// reference to the library's own options, so the test project's uses
/// resolve to the library's SOURCE declarations. The test project's uses
/// are then indexed by full name and matched by declaration, exactly the
/// channel `#load`ing scripts go through.
let private withSiblingProject
    (libSource: string)
    (testSource: string)
    (body:
        Text.FileContext
            -> FSharpCheckFileResults
            -> FSharpCheckProjectResults
            -> Visibility.Outside
            -> (string -> Text.FileContext option)
            -> 'Result)
    : 'Result =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-sibling-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory(Path.Combine(dir, "Lib")) |> ignore
    Directory.CreateDirectory(Path.Combine(dir, "Tests")) |> ignore

    try
        let libFile = Path.Combine(dir, "Lib", "Library.fs")
        let testFile = Path.Combine(dir, "Tests", "Tests.fs")
        File.WriteAllText(libFile, libSource)
        File.WriteAllText(testFile, testSource)

        let libOutput = Path.Combine(dir, "Lib", "bin", "Lib.dll")

        let libOptions =
            let plain = optionsFor (Path.Combine(dir, "Lib")) [ libFile ]

            { plain with
                ProjectFileName = Path.Combine(dir, "Lib", "Lib.fsproj")
                OtherOptions = Array.append plain.OtherOptions [| $"-o:{libOutput}" |] }

        let testOptions =
            let plain = optionsFor (Path.Combine(dir, "Tests")) [ testFile ]

            { plain with
                ProjectFileName = Path.Combine(dir, "Tests", "Tests.fsproj")
                OtherOptions = Array.append plain.OtherOptions [| $"-r:{libOutput}" |]
                ReferencedProjects = [| FSharpReferencedProject.FSharpReference(libOutput, libOptions) |] }

        let libProject = checker.ParseAndCheckProject libOptions |> Async.RunSynchronously
        let testProject = checker.ParseAndCheckProject testOptions |> Async.RunSynchronously

        let testErrors =
            testProject.Diagnostics
            |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

        Assert.True(Array.isEmpty testErrors, sprintf "the test project should typecheck: %A" testErrors)

        // the sibling's uses, in its own files only
        let siblingUses =
            testProject.GetAllUsesOfAllSymbols()
            |> Array.filter (fun u ->
                not u.IsFromDefinition
                && String.Equals(
                    Path.GetFullPath u.Range.FileName,
                    Path.GetFullPath testFile,
                    StringComparison.OrdinalIgnoreCase
                ))

        let fullName (s: FSharp.Compiler.Symbols.FSharpSymbol) =
            try
                Some s.FullName
            with _ ->
                None

        // matched by declaration POSITION, as the tool does: both
        // compilations read the same source file
        let sameDeclaration (a: FSharp.Compiler.Symbols.FSharpSymbol) (b: FSharp.Compiler.Symbols.FSharpSymbol) =
            match a.DeclarationLocation, b.DeclarationLocation with
            | Some ra, Some rb ->
                ra.StartLine = rb.StartLine
                && ra.StartColumn = rb.StartColumn
                && String.Equals(
                    Path.GetFullPath ra.FileName,
                    Path.GetFullPath rb.FileName,
                    StringComparison.OrdinalIgnoreCase
                )
            | _ -> false

        let outside: Visibility.Outside =
            { Uses =
                (fun symbol ->
                    match fullName symbol with
                    | Some name ->
                        siblingUses
                        |> Array.filter (fun u -> fullName u.Symbol = Some name && sameDeclaration symbol u.Symbol)
                    | None -> [||])
              PublicRead = (fun () -> true)
              AssemblyRead = (fun _ -> true) }

        let contexts =
            System.Collections.Generic.Dictionary<string, Text.FileContext>(StringComparer.OrdinalIgnoreCase)

        contexts.[Path.GetFullPath libFile] <- contextFor libOptions libFile
        contexts.[Path.GetFullPath testFile] <- contextFor testOptions testFile

        let fileLookup (name: string) =
            match contexts.TryGetValue(Path.GetFullPath name) with
            | true, ctx -> Some ctx
            | false, _ -> None

        let ctx = contexts.[Path.GetFullPath libFile]
        let check = checkFile libOptions ctx
        body ctx check libProject outside fileLookup
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``a sibling project's call site resolves to the library's source declaration and is rewritten`` () =
    let found =
        withSiblingProject
            "module Lib\n\nlet add (a: int, b: int) = a + b\n"
            "module Tests\n\nlet three () = Lib.add (1, 2)\n"
            (fun ctx check project outside fileLookup ->
                TupleParams.findApiChanges ctx check project fileLookup outside
                |> List.map (fun s ->
                    s.FunctionName,
                    s.Edits
                    |> List.map (fun e -> Path.GetFileName e.Range.FileName, e.Original, e.Replacement)))

    match found with
    | [ "add", edits ] ->
        Assert.Equal<(string * string * string) list>(
            [ "Library.fs", "(a: int, b: int)", "(a: int) (b: int)"
              "Tests.fs", "(1, 2)", "1 2" ],
            edits
        )
    | other -> failwithf "expected the definition and the sibling's call site rewritten, got %A" other

[<Fact>]
let ``a sibling project's first-class use blocks the change`` () =
    // `let f = Lib.add` in the test project: not a call, so the tuple
    // shape is observed there and the change stands down — the same
    // all-or-nothing rule the project's own files are under
    let found =
        withSiblingProject
            "module Lib\n\nlet add (a: int, b: int) = a + b\n"
            "module Tests\n\nlet f = Lib.add\nlet three () = f (1, 2)\n"
            (fun ctx check project outside fileLookup ->
                TupleParams.findApiChanges ctx check project fileLookup outside)

    Assert.Empty found

[<Fact>]
let ``a sibling's call site the host cannot render stands the change down`` () =
    // the sibling's uses are known but its file is not in the lookup: a
    // call site that cannot be rewritten is a call site left in the old
    // shape
    let found =
        withSiblingProject
            "module Lib\n\nlet add (a: int, b: int) = a + b\n"
            "module Tests\n\nlet three () = Lib.add (1, 2)\n"
            (fun ctx check project outside fileLookup ->
                let libOnly (name: string) =
                    if name.EndsWith("Library.fs", StringComparison.OrdinalIgnoreCase) then
                        fileLookup name
                    else
                        None

                TupleParams.findApiChanges ctx check project libOnly outside)

    Assert.Empty found
