module FSharp.Refactor.Tests.ScriptLoadsTests

open System.IO
open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor

// ---- FR0143 ScriptLoads ----

/// A project of three files on disk and a script that loads a subset,
/// checked the way the apply tool checks a script.
let private withProject
    (loads: string list)
    (scriptBody: string)
    (test: string -> ScriptLoads.Suggestion list -> unit)
    =
    let root =
        Path.Combine(Path.GetTempPath(), "fsharp-refactor-scriptloads-" + Path.GetRandomFileName())

    let src = Path.Combine(root, "src")
    let scripts = Path.Combine(root, "scripts")
    Directory.CreateDirectory src |> ignore
    Directory.CreateDirectory scripts |> ignore

    try
        File.WriteAllText(Path.Combine(src, "Helpers.fs"), "module Lib.Helpers\nlet one = 1\n")
        File.WriteAllText(Path.Combine(src, "FMatrix.fs"), "module Lib.FMatrix\nlet size = Helpers.one + 1\n")
        File.WriteAllText(Path.Combine(src, "Braiding.fs"), "module Lib.Braiding\nlet braid () = FMatrix.size * 2\n")

        File.WriteAllText(
            Path.Combine(src, "Lib.fsproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Helpers.fs\" />\n    <Compile Include=\"FMatrix.fs\" />\n    <Compile Include=\"Braiding.fs\" />\n  </ItemGroup>\n</Project>\n"
        )

        let script = Path.Combine(scripts, "Run.fsx")

        let text =
            (loads |> List.map (fun f -> $"#load \"../src/{f}\"") |> String.concat "\n")
            + "\n"
            + scriptBody

        File.WriteAllText(script, text)

        let checker = FSharpChecker.Create()
        let sourceText = SourceText.ofString text

        let options, _ =
            checker.GetProjectOptionsFromScript(script, sourceText, assumeDotNetFramework = false)
            |> Async.RunSynchronously

        let project = checker.ParseAndCheckProject options |> Async.RunSynchronously
        let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

        let parsed =
            checker.ParseFile(script, sourceText, parsingOptions) |> Async.RunSynchronously

        test text (ScriptLoads.find script parsed.ParseTree project.Diagnostics)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``a missing file of the loaded project is loaded before the file that needs it`` () =
    withProject [ "Helpers.fs"; "Braiding.fs" ] "printfn \"%d\" (Lib.Braiding.braid ())" (fun text suggestions ->
        match suggestions with
        | [ s ] ->
            Assert.Equal(Some "#load \"../src/FMatrix.fs\"\n", s.InsertText)
            // before the Braiding load, which is line 2
            Assert.Equal(2, s.InsertRange.StartLine)
            Assert.Contains("FMatrix.fs", s.Message)
        | other -> failwithf "Expected one suggestion, got %A" other)

[<Fact>]
let ``a complete load chain gets no suggestion`` () =
    withProject
        [ "Helpers.fs"; "FMatrix.fs"; "Braiding.fs" ]
        "printfn \"%d\" (Lib.Braiding.braid ())"
        (fun _ suggestions -> Assert.Empty suggestions)

[<Fact>]
let ``a name the project does not declare gets no suggestion`` () =
    withProject [ "Helpers.fs" ] "printfn \"%d\" Nowhere.value" (fun _ suggestions -> Assert.Empty suggestions)

[<Fact>]
let ``a lower-case missing name is a value, not something a load supplies`` () =
    // `'one' is not defined` must not load a file that happens to carry that
    // name: a #load runs the file's top-level code
    withProject [ "Helpers.fs" ] "printfn \"%d\" one" (fun _ suggestions -> Assert.Empty suggestions)

/// A referenced project declaring a namespace the loaded project opens,
/// with the given assembly files under its bin directory.
let private withReference (assemblies: string list) (test: ScriptLoads.Suggestion list -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsharp-refactor-scriptloads-" + Path.GetRandomFileName())

    let core = Path.Combine(root, "Core")
    let src = Path.Combine(root, "src")
    let scripts = Path.Combine(root, "scripts")

    for d in [ core; src; scripts ] do
        Directory.CreateDirectory d |> ignore

    try
        File.WriteAllText(Path.Combine(core, "Core.fs"), "namespace Lib.Core\ntype Marker = { Id: int }\n")

        File.WriteAllText(
            Path.Combine(core, "Core.fsproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  <ItemGroup><Compile Include=\"Core.fs\" /></ItemGroup>\n</Project>\n"
        )

        for a in assemblies do
            let path = Path.Combine(core, a.Replace('/', Path.DirectorySeparatorChar))
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, "")

        File.WriteAllText(Path.Combine(src, "Braiding.fs"), "module Lib.Braiding\nopen Lib.Core\nlet braid () = 2\n")

        File.WriteAllText(
            Path.Combine(src, "Lib.fsproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  <ItemGroup><Compile Include=\"Braiding.fs\" /></ItemGroup>\n  <ItemGroup><ProjectReference Include=\"../Core/Core.fsproj\" /></ItemGroup>\n</Project>\n"
        )

        let script = Path.Combine(scripts, "Run.fsx")
        let text = "#load \"../src/Braiding.fs\"\nprintfn \"%d\" (Lib.Braiding.braid ())\n"
        File.WriteAllText(script, text)

        let checker = FSharpChecker.Create()
        let sourceText = SourceText.ofString text

        let options, _ =
            checker.GetProjectOptionsFromScript(script, sourceText, assumeDotNetFramework = false)
            |> Async.RunSynchronously

        let project = checker.ParseAndCheckProject options |> Async.RunSynchronously
        let parsingOptions, _ = checker.GetParsingOptionsFromProjectOptions options

        let parsed =
            checker.ParseFile(script, sourceText, parsingOptions) |> Async.RunSynchronously

        test (ScriptLoads.find script parsed.ParseTree project.Diagnostics)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``a namespace of a referenced project gets a reference to its built assembly`` () =
    withReference [ "bin/Debug/net8.0/Core.dll" ] (fun suggestions ->
        match suggestions with
        | [ s ] ->
            Assert.Equal(Some "#r \"../Core/bin/Debug/net8.0/Core.dll\"\n", s.InsertText)
            Assert.Equal(1, s.InsertRange.StartLine)
        | other -> failwithf "Expected one suggestion, got %A" other)

[<Fact>]
let ``a reference assembly is not what a script can run against`` () =
    // bin\...\ref\Core.dll has no IL: a #r to it typechecks and fails under fsi
    withReference [ "bin/Debug/net8.0/ref/Core.dll" ] (fun suggestions ->
        match suggestions with
        | [ s ] ->
            Assert.Equal(None, s.InsertText)
            Assert.Contains("build it", s.Message)
        | other -> failwithf "Expected one advisory suggestion, got %A" other)

[<Fact>]
let ``a script whose own load names a missing file is stale and gets no suggestion`` () =
    // fsharp.formatting's Script.fsx: `#load "Library1.fs"` for a file long
    // gone; its FS0039s are not a missing #load
    withProject
        [ "Helpers.fs"; "Gone.fs"; "Braiding.fs" ]
        "printfn \"%d\" (Lib.Braiding.braid ())"
        (fun _ suggestions -> Assert.Empty suggestions)

[<Fact>]
let ``a script whose #r names an unbuilt dll gets no suggestion`` () =
    // fantomas's docs scripts: `#r` to an artifacts dll never built here made
    // every name of that project "not defined", and the rule answered with a
    // #load of a signature file
    withProject
        [ "Helpers.fs"; "Braiding.fs" ]
        "#r \"../src/bin/Nope.dll\"\nprintfn \"%d\" (Lib.Braiding.braid ())"
        (fun _ suggestions -> Assert.Empty suggestions)
