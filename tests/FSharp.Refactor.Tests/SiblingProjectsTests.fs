/// The api pass across the projects of a solution, end to end: the tool's
/// own `main` over a temporary two-project solution on disk, MSBuild and
/// all. A library exposes a PUBLIC tupled function and its test project
/// calls it; under --api-changes both the definition and the sibling's
/// call site must change together, or — when a project the pass cannot
/// read references the library — nothing may.
///
/// In the "ProjectSources" collection because `main` configures the
/// process-wide analyzer state (the api-changes flag above all) for the
/// duration of the run.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.SiblingProjectsTests

open System
open System.Diagnostics
open System.IO
open FSharp.Refactor.Tool
open Xunit

/// The framework the temporary projects target: the one this test host
/// runs on, which the machine therefore has an SDK for.
let private framework =
    let version = Environment.Version.Major
    $"net{version}.0"

/// A solution of a library and a test project (and, when asked, a C#
/// project referencing the library too), written under a fresh root.
let private writeSolution (root: string) (withCSharpConsumer: bool) =
    let write (relative: string) (content: string) =
        let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, content)

    write
        "src/Lib/Lib.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

    write
        "src/Lib/Library.fs"
        "module Lib\n\nlet add (a: int, b: int) = a + b\n\nlet internal twice (x: int) = add (x, x)\n"

    write
        "tests/Tests/Tests.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Tests.fs\" />\n  </ItemGroup>\n  <ItemGroup>\n    <ProjectReference Include=\"../../src/Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"

    write "tests/Tests/Tests.fs" "module Tests\n\nlet three () = Lib.add (1, 2)\n"

    let projects =
        [ "Lib", "src\\Lib\\Lib.fsproj"
          "Tests", "tests\\Tests\\Tests.fsproj"
          if withCSharpConsumer then
              "Consumer", "src\\Consumer\\Consumer.csproj" ]

    if withCSharpConsumer then
        write
            "src/Consumer/Consumer.csproj"
            $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <ProjectReference Include=\"../Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"

    let entries =
        projects
        |> List.map (fun (name, path) ->
            $"Project(\"{{F2A71F9B-5D33-465A-A702-920D77279786}}\") = \"{name}\", \"{path}\", \"{{{Guid.NewGuid()}}}\"\nEndProject")
        |> String.concat "\n"

    write "Probe.sln" $"Microsoft Visual Studio Solution File, Format Version 12.00\n{entries}\nGlobal\nEndGlobal\n"
    Path.Combine(root, "Probe.sln")

/// Run the tool's main in-process, capturing what it prints.
let private runTool (args: string[]) =
    use captured = new StringWriter()
    let oldOut = Console.Out
    let oldErr = Console.Error
    Console.SetOut captured
    Console.SetError captured

    let code =
        try
            Program.main args
        finally
            Console.SetOut oldOut
            Console.SetError oldErr

    code, captured.ToString()

/// `dotnet build` of the solution, as the developer would run it.
let private builds (solution: string) =
    let psi =
        ProcessStartInfo(
            "dotnet",
            $"build \"{solution}\" -nologo -v:q",
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            WorkingDirectory = Path.GetDirectoryName solution
        )

    use proc = Process.Start psi
    let output = proc.StandardOutput.ReadToEnd() + proc.StandardError.ReadToEnd()
    proc.WaitForExit()
    proc.ExitCode = 0, output

let private withSolution (withCSharpConsumer: bool) (body: string -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-siblings-" + Guid.NewGuid().ToString "N")

    try
        body (writeSolution root withCSharpConsumer)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``a public function is curried together with the call site in the sibling test project`` () : unit =
    withSolution false (fun solution ->
        let code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Lib", "Library.fs"))

        let tests =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "tests", "Tests", "Tests.fs"))

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("let add (a: int) (b: int) = a + b", library)
        Assert.Contains("add x x", library)
        Assert.Contains("Lib.add 1 2", tests)
        Assert.Contains("of them in referencing projects", output)

        let built, buildOutput = builds solution
        Assert.True(built, $"the rewritten solution should build:\n{buildOutput}\n\ntool output:\n{output}"))

[<Fact>]
let ``a C# project referencing the library keeps its public functions as they are`` () : unit =
    withSolution true (fun solution ->
        let code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Lib", "Library.fs"))

        let tests =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "tests", "Tests", "Tests.fs"))

        Assert.True((code = 0), $"exit {code}:\n{output}")
        // the public function keeps its tuple: the C# consumer's calls
        // cannot be read, so it might be calling it
        Assert.Contains("let add (a: int, b: int) = a + b", library)
        Assert.Contains("Lib.add (1, 2)", tests)
        Assert.Contains("Consumer.csproj references this project and cannot be read", output))

/// A solution where a second project compiles the library's source
/// DIRECTLY (a `<Compile Include="../Lib/Library.fs">` link, SQLProvider's
/// provider projects' shape) beside a file of its own that calls the
/// shared function; `broken` gives that own file a type error.
let private writeLinkedSolution (root: string) (broken: bool) =
    let write (relative: string) (content: string) =
        let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, content)

    write
        "src/Lib/Lib.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

    write "src/Lib/Library.fs" "module Lib\n\nlet add (a: int, b: int) = a + b\n"

    write
        "src/Provider/Provider.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"../Lib/Library.fs\" />\n    <Compile Include=\"Provider.fs\" />\n  </ItemGroup>\n</Project>\n"

    write
        "src/Provider/Provider.fs"
        (if broken then
             "module Provider\n\nlet four () : string = Lib.add (2, 2)\n"
         else
             "module Provider\n\nlet four () = Lib.add (2, 2)\n")

    let entries =
        [ "Lib", "src\Lib\Lib.fsproj"; "Provider", "src\Provider\Provider.fsproj" ]
        |> List.map (fun (name, path) ->
            $"Project(\"{{F2A71F9B-5D33-465A-A702-920D77279786}}\") = \"{name}\", \"{path}\", \"{{{Guid.NewGuid()}}}\"\nEndProject")
        |> String.concat "\n"

    write "Probe.sln" $"Microsoft Visual Studio Solution File, Format Version 12.00\n{entries}\nGlobal\nEndGlobal\n"
    Path.Combine(root, "Probe.sln")

let private withLinkedSolution (broken: bool) (body: string -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-linked-" + Guid.NewGuid().ToString "N")

    try
        body (writeLinkedSolution root broken)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``a project compiling the library's source directly has its own call site rewritten too`` () : unit =
    // the linker is another compilation of the same declaration: read like
    // a sibling, its file edited in the same group, nothing special
    withLinkedSolution false (fun solution ->
        let code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Lib", "Library.fs"))

        let provider =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Provider", "Provider.fs"))

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("let add (a: int) (b: int) = a + b", library)
        Assert.Contains("Lib.add 2 2", provider)
        Assert.Contains("Provider.fs(3,22) note: linked file", output)

        let built, buildOutput = builds solution
        Assert.True(built, $"the rewritten solution should build:\n{buildOutput}\n\ntool output:\n{output}"))

[<Fact>]
let ``a linking project that does not typecheck keeps the shared declarations as they are`` () : unit =
    // its call sites cannot be read, and they are the ones a reshaping
    // would break
    withLinkedSolution true (fun solution ->
        let code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Lib", "Library.fs"))

        let provider =
            File.ReadAllText(Path.Combine(Path.GetDirectoryName solution, "src", "Provider", "Provider.fs"))

        // the run exits non-zero on its own account: Provider does not build,
        // and the tool says so when that project's turn comes
        ignore code
        Assert.Contains("let add (a: int, b: int) = a + b", library)
        Assert.Contains("Lib.add (2, 2)", provider)
        Assert.Contains("Provider.fsproj cannot be read", output))
