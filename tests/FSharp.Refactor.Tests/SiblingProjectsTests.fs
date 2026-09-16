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
        [
            "Lib", "src\\Lib\\Lib.fsproj"
            "Tests", "tests\\Tests\\Tests.fsproj"
            if withCSharpConsumer then
                "Consumer", "src\\Consumer\\Consumer.csproj"
        ]

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
let ``a test project's own public functions reshape without --api-changes; the library's do not`` () : unit =
    // a test project exports no API: nothing links to it, so its tupled
    // helper is curried in a plain run, while the library's public `add`
    // - which the flag exists to protect - keeps its shape
    withSolution false (fun solution ->
        let root = Path.GetDirectoryName solution
        let testProject = Path.Combine(root, "tests", "Tests", "Tests.fsproj")

        File.WriteAllText(
            testProject,
            $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Tests.fs\" />\n  </ItemGroup>\n  <ItemGroup>\n    <PackageReference Include=\"xunit\" Version=\"2.9.3\" />\n    <ProjectReference Include=\"../../src/Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"
        )

        File.WriteAllText(
            Path.Combine(root, "tests", "Tests", "Tests.fs"),
            "module Tests\n\nlet helper (a: int, b: int) = a + b\n\nlet three () = Lib.add (1, 2) + helper (1, 2)\n"
        )

        let code, output = runTool [| solution; "--codes"; "FR0090"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(root, "src", "Lib", "Library.fs"))

        let tests = File.ReadAllText(Path.Combine(root, "tests", "Tests", "Tests.fs"))

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("a test project", output)
        Assert.Contains("let add (a: int, b: int) = a + b", library)
        Assert.Contains("let helper (a: int) (b: int) = a + b", tests)
        Assert.Contains("helper 1 2", tests)
        Assert.Contains("Lib.add (1, 2)", tests)

        let built, buildOutput = builds solution
        Assert.True(built, $"the rewritten solution should build:\n{buildOutput}\n\ntool output:\n{output}"))

[<Fact>]
let ``a function called inside an #if region keeps its shape: the other branch's call sites are in no parse tree``
    ()
    : unit =
    // the analysis sees the `#if DEBUG` branch; the `#else` call site is not
    // in the parse tree, so FR0090 would curry the definition and the one
    // call it can see. The name inside a directive region keeps it back up
    // front; the other-configuration build is the backstop behind that
    withSolution false (fun solution ->
        let root = Path.GetDirectoryName solution
        let library = Path.Combine(root, "src", "Lib", "Library.fs")
        let tests = Path.Combine(root, "tests", "Tests", "Tests.fs")

        File.WriteAllText(
            tests,
            "module Tests\n\nlet three () =\n#if DEBUG\n    Lib.add (1, 2)\n#else\n    Lib.add (2, 1)\n#endif\n"
        )

        let _code, output =
            runTool [| solution; "--codes"; "FR0090"; "--api-changes"; "--no-color" |]

        Assert.Contains("named inside an #if region", output)
        Assert.Contains("let add (a: int, b: int) = a + b", File.ReadAllText library)
        Assert.Contains("Lib.add (1, 2)", File.ReadAllText tests)
        Assert.Contains("Lib.add (2, 1)", File.ReadAllText tests)

        let built, buildOutput = builds solution
        Assert.True(built, $"the put-back solution should build:\n{buildOutput}\n\ntool output:\n{output}"))

[<Fact>]
let ``a function a string literal names keeps its shape: a template's calls are not in any symbol table`` () : unit =
    // SQLProvider.Fable's CodeGen writes `Row.text r "Name"` from a string;
    // FR0091 reordered Row.text and the generator kept emitting the old order
    withSolution false (fun solution ->
        let root = Path.GetDirectoryName solution
        let library = Path.Combine(root, "src", "Lib", "Library.fs")
        let tests = Path.Combine(root, "tests", "Tests", "Tests.fs")

        File.WriteAllText(
            tests,
            "module Tests\n\nlet three () = Lib.add (1, 2)\n\nlet template (name: string) = $\"let x = Lib.add ({name}, 2)\"\n"
        )

        let code, output =
            runTool [| solution; "--codes"; "FR0090"; "--api-changes"; "--no-color" |]

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("a string literal in the project names the function", output)
        Assert.Contains("let add (a: int, b: int) = a + b", File.ReadAllText library)
        Assert.Contains("Lib.add (1, 2)", File.ReadAllText tests))

[<Fact>]
let ``a project whose own sources branch on the configuration gets the other configuration's pass`` () : unit =
    // the same hazard inside one project keeps the migration back, and the
    // `#else` branch - invisible to the Debug pass - is swept by a Release
    // pass of its own, where the in-place rules reach it
    withSolution false (fun solution ->
        let root = Path.GetDirectoryName solution
        let library = Path.Combine(root, "src", "Lib", "Library.fs")

        File.WriteAllText(
            library,
            "module Lib\n\nlet add (a: int, b: int) = a + b\n\nlet internal three () =\n#if DEBUG\n    add (1, 2)\n#else\n    let flag = if 2 > 1 then true else false\n    if flag then add (2, 1) else 0\n#endif\n"
        )

        let project = Path.Combine(root, "src", "Lib", "Lib.fsproj")

        let _code, output =
            runTool [| project; "--codes"; "FR0090,FR0010"; "--api-changes"; "--no-color" |]

        Assert.Contains("analysing the Release branches too", output)
        Assert.Contains("[Release] ==", output)
        Assert.Contains("let flag = 2 > 1", File.ReadAllText library)
        Assert.Contains("let add (a: int, b: int) = a + b", File.ReadAllText library)
        Assert.Contains("add (2, 1)", File.ReadAllText library)

        let built, buildOutput = builds solution
        Assert.True(built, $"the put-back solution should build:\n{buildOutput}\n\ntool output:\n{output}"))

[<Fact>]
let ``a script leaves the #loaded sources of a project to that project`` () : unit =
    // Owin.Compression: Script.fsx `#load`s the net48 CompressionModule.fs,
    // and the script's sweep - typechecked as .NET Core - wrote
    // Convert.ToHexString into it. The sweep dedup did not help: the file
    // carries an `#if`, so it is keyed on defines, and a script's differ
    withSolution false (fun solution ->
        let root = Path.GetDirectoryName solution
        let library = Path.Combine(root, "src", "Lib", "Library.fs")
        let script = Path.Combine(root, "src", "Lib", "Probe.fsx")

        File.WriteAllText(
            library,
            "module Lib\n\n#if INTERACTIVE\nlet interactive = true\n#endif\n\nlet hex (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \"\")\n"
        )

        File.WriteAllText(
            script,
            "#load \"Library.fs\"\n\nlet hex2 (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \"\")\n\nprintfn \"%s %s\" (Lib.hex [| 1uy |]) (hex2 [| 2uy |])\n"
        )

        let code, output = runTool [| script; "--codes"; "FR0053"; "--no-color" |]

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("left to the project that compiles them", output)
        Assert.Contains("Library.fs (Lib.fsproj)", output)
        // the script's own body is still the script's to fix
        Assert.Contains("Convert.ToHexString", File.ReadAllText script)
        Assert.DoesNotContain("ToHexString", File.ReadAllText library))

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

// ---- a script that #r's the built assembly ----

/// A library alone, with a script beside it that `#r`s the library's built
/// dll and calls its public tupled function; `broken` gives the script a
/// type error of its own.
let private writeScriptSolution (root: string) (broken: bool) =
    let write (relative: string) (content: string) =
        let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, content)

    write
        "src/Lib/Lib.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

    write "src/Lib/Library.fs" "module Lib\n\nlet add (a: int, b: int) = a + b\n"

    let call =
        if broken then
            "Lib.add (1, 2) + \"x\""
        else
            "Lib.add (1, 2)"

    write
        "docs/faq.fsx"
        $"#r \"../src/Lib/bin/Debug/{framework}/Lib.dll\"\n\nlet three = {call}\nprintfn \"%%d\" three\n"

    Path.Combine(root, "src", "Lib", "Lib.fsproj")

let private withScriptSolution (broken: bool) (body: string -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-rscript-" + Guid.NewGuid().ToString "N")

    try
        body (writeScriptSolution root broken)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

/// `dotnet fsi` of a script, as the developer would run it.
let private runsScript (script: string) =
    let psi =
        ProcessStartInfo(
            "dotnet",
            $"fsi \"{script}\"",
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            WorkingDirectory = Path.GetDirectoryName script
        )

    use proc = Process.Start psi
    let output = proc.StandardOutput.ReadToEnd() + proc.StandardError.ReadToEnd()
    proc.WaitForExit()
    proc.ExitCode = 0, output

[<Fact>]
let ``a script that #r's the built assembly is rewritten together with the public function`` () : unit =
    // farmer's amortisationFaq.fsx: read against the sources through the
    // redirected reference, the script's calls match like a sibling's
    withScriptSolution false (fun project ->
        let root =
            Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName project))

        let code, output =
            runTool [| root; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(root, "src", "Lib", "Library.fs"))
        let script = Path.Combine(root, "docs", "faq.fsx")
        let scriptText = File.ReadAllText script

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("let add (a: int) (b: int) = a + b", library)
        Assert.Contains("Lib.add 1 2", scriptText)
        Assert.Contains("of them in scripts", output)

        // the dll is stale until the project is built again; then the
        // rewritten script runs against the rewritten library
        let built, buildOutput = builds project
        Assert.True(built, $"the rewritten project should build:\n{buildOutput}\n\ntool output:\n{output}")
        let ran, scriptOutput = runsScript script
        Assert.True(ran, $"the rewritten script should run:\n{scriptOutput}\n\ntool output:\n{output}")
        Assert.Contains("3", scriptOutput))

[<Fact>]
let ``a #r script that does not typecheck keeps the public function as it is`` () : unit =
    withScriptSolution true (fun project ->
        let root =
            Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName project))

        let code, output =
            runTool [| root; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(root, "src", "Lib", "Library.fs"))
        let scriptText = File.ReadAllText(Path.Combine(root, "docs", "faq.fsx"))

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("let add (a: int, b: int) = a + b", library)
        Assert.Contains("Lib.add (1, 2)", scriptText)
        Assert.Contains("could not be checked against its sources", output))
