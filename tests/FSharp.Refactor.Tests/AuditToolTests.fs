/// The tool driver's put-back of files it wrote OUTSIDE the project (a
/// sibling's call sites go back with a reverted definition), its
/// exception boundary around child processes, and FR0143's reading of a
/// `#r` by name. In the "ProjectSources" collection: the snapshot record
/// is process-wide state, and the end-to-end test runs `main`.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AuditToolTests

open System
open System.Diagnostics
open System.IO
open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tool

let private tempRoot (prefix: string) =
    let root = Path.Combine(Path.GetTempPath(), prefix + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory root |> ignore
    root

let private cleanup (root: string) =
    try
        Directory.Delete(root, true)
    with _ ->
        ()

// ---- D1: the snapshot covers what the run wrote outside the project ----

[<Fact>]
let ``restoreSnapshot puts back the files written outside the snapshot too`` () =
    let root = tempRoot "fsref-audit-snap-"

    try
        let own = Path.Combine(root, "Library.fs")
        let sibling = Path.Combine(root, "Tests.fs")
        File.WriteAllText(own, "let add (a: int, b: int) = a + b\n")
        File.WriteAllText(sibling, "let three () = Lib.add (1, 2)\n")

        let snapshot = Program.takeSnapshot [| own |]
        Assert.Equal(1, snapshot.Count)

        // the api pass writes the sibling: its pre-write text is recorded
        Program.recordExtra sibling (File.ReadAllText sibling)
        File.WriteAllText(own, "let add (a: int) (b: int) = a + b\n")
        File.WriteAllText(sibling, "let three () = Lib.add 1 2\n")

        let restored = Program.restoreSnapshot snapshot

        Assert.Equal(2, restored)
        Assert.Equal("let add (a: int, b: int) = a + b\n", File.ReadAllText own)
        Assert.Equal("let three () = Lib.add (1, 2)\n", File.ReadAllText sibling)
    finally
        Program.takeSnapshot [||] |> ignore
        cleanup root

[<Fact>]
let ``recordExtra keeps the first text only and ignores the snapshot's own files`` () =
    let root = tempRoot "fsref-audit-snap-"

    try
        let own = Path.Combine(root, "Library.fs")
        let sibling = Path.Combine(root, "Tests.fs")
        File.WriteAllText(own, "own\n")
        File.WriteAllText(sibling, "first\n")

        Program.takeSnapshot [| own |] |> ignore
        Program.recordExtra own "own\n"
        Assert.Empty Program.extraSnapshot

        Program.recordExtra sibling "first\n"
        // a second pass writing the same file again: the ORIGINAL stays
        Program.recordExtra sibling "second\n"
        Assert.Equal("first\n", Program.extraSnapshot.[Path.GetFullPath sibling])
    finally
        Program.takeSnapshot [||] |> ignore
        cleanup root

[<Fact>]
let ``without a snapshot nothing outside it is recorded either`` () =
    // --dry-run and a skipped compilation check take an empty snapshot,
    // and a put-back that covers nothing must not start covering siblings
    Program.takeSnapshot [||] |> ignore
    Program.recordExtra (Path.Combine(Path.GetTempPath(), "fsref-audit-never-written.fs")) "x"
    Assert.Empty Program.extraSnapshot

// ---- D3: a child that cannot start is a failed exit, not a crash ----

[<Fact>]
let ``runProcessIn reports an executable that cannot be started instead of throwing`` () =
    let code, out, err =
        Program.runProcessIn None (TimeSpan.FromSeconds 5.) "fsref-no-such-executable-3f2a1c.exe" "--version"

    Assert.Equal(-1, code)
    Assert.Equal("", out)
    Assert.Contains("could not be started", err)

// ---- D5: FR0143 and a `#r` by name ----

/// A project of two files (Core needs Util) and a script under `scripts/`
/// whose text is `directives` followed by a use of Core, typechecked the
/// way the apply tool checks a script.
let private withScriptAnd (setup: string -> unit) (directives: string) (test: ScriptLoads.Suggestion list -> unit) =
    let root = tempRoot "fsref-audit-scriptloads-"
    let src = Path.Combine(root, "src", "Lib")
    let scripts = Path.Combine(root, "scripts")
    Directory.CreateDirectory src |> ignore
    Directory.CreateDirectory scripts |> ignore

    try
        setup scripts

        File.WriteAllText(Path.Combine(src, "Util.fs"), "module Lib.Util\nlet one = 1\n")
        File.WriteAllText(Path.Combine(src, "Core.fs"), "module Lib.Core\nlet size = Util.one + 1\n")

        File.WriteAllText(
            Path.Combine(src, "Lib.fsproj"),
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Util.fs\" />\n    <Compile Include=\"Core.fs\" />\n  </ItemGroup>\n</Project>\n"
        )

        let script = Path.Combine(scripts, "build.fsx")
        let text = directives + "\nprintfn \"%d\" Lib.Core.size\n"
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
        cleanup root

let private withScript (directives: string) (test: ScriptLoads.Suggestion list -> unit) =
    withScriptAnd ignore directives test

let private expectUtilLoad (suggestions: ScriptLoads.Suggestion list) =
    match suggestions with
    | [ s ] -> Assert.Equal(Some "#load \"../src/Lib/Util.fs\"\n", s.InsertText)
    | other -> failwithf "Expected the missing #load of Util.fs, got %A" other

[<Fact>]
let ``a FAKE 4 script with an #I-resolved #r by name still gets its missing #load`` () =
    // `#I "packages/FAKE/tools"` + `#r "FakeLib.dll"`: the dll is not beside
    // the script, and treating that as a broken directive silenced the
    // rule on every FAKE 4 build script
    withScript "#I \"packages/FAKE/tools\"\n#r \"FakeLib.dll\"\n#load \"../src/Lib/Core.fs\"" expectUtilLoad

[<Fact>]
let ``a #r of an assembly by name is not a broken directive`` () =
    // resolved by the compiler from its reference set, not from the script's
    // directory
    withScript "#r \"System.Xml.Linq\"\n#load \"../src/Lib/Core.fs\"" expectUtilLoad

[<Fact>]
let ``a #r by name that an #I directory does hold is resolved there`` () =
    // the dll is in the #I directory, not beside the script
    withScriptAnd
        (fun scripts ->
            let tools = Path.Combine(scripts, "packages", "FAKE", "tools")
            Directory.CreateDirectory tools |> ignore
            File.WriteAllText(Path.Combine(tools, "FakeLib.dll"), ""))
        "#I \"packages/FAKE/tools\"\n#r \"FakeLib.dll\"\n#load \"../src/Lib/Core.fs\""
        expectUtilLoad

[<Fact>]
let ``a #r with a path into an #I directory is checked there too`` () =
    // a RELATIVE path is a path: it must exist beside the script or under
    // an #I directory, and here it does
    withScriptAnd
        (fun scripts ->
            let tools = Path.Combine(scripts, "packages", "FAKE", "tools")
            Directory.CreateDirectory tools |> ignore
            File.WriteAllText(Path.Combine(tools, "FakeLib.dll"), ""))
        "#I \"packages/FAKE\"\n#r \"tools/FakeLib.dll\"\n#load \"../src/Lib/Core.fs\""
        expectUtilLoad

[<Fact>]
let ``a #load of a file that is gone still makes the script stale`` () =
    withScript "#load \"../gone.fs\"\n#load \"../src/Lib/Core.fs\"" (fun suggestions -> Assert.Empty suggestions)

[<Fact>]
let ``a #r with a path that leads nowhere still makes the script stale`` () =
    withScript "#r \"../src/Lib/bin/Nope.dll\"\n#load \"../src/Lib/Core.fs\"" (fun suggestions ->
        Assert.Empty suggestions)

[<Fact>]
let ``a #load with nothing missing gets no suggestion`` () =
    withScript "#load \"../src/Lib/Util.fs\"\n#load \"../src/Lib/Core.fs\"" (fun suggestions ->
        Assert.Empty suggestions)

// ---- D1, end to end: a sibling's call site goes back with the definition ----

/// The framework the temporary projects target: the one this test host
/// runs on, which the machine therefore has an SDK for.
let private framework =
    let version = Environment.Version.Major
    $"net{version}.0"

/// A solution of a MULTI-TARGETED library and a test project calling it.
/// `Library.fs` has a call of `add` behind `#if NETSTANDARD` and another
/// behind `#else`: the narrowest round (netstandard2.0) curries `add`,
/// its visible call and the sibling's, and the other framework's build
/// then fails on the call it could not see — the arbiter's bisection
/// puts `Library.fs` back. `Other.fs` carries an innocent second
/// suggestion the bisection should keep.
let private writeMultiTargetSolution (root: string) =
    let write (relative: string) (content: string) =
        let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, content)

    write
        "src/Lib/Lib.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFrameworks>netstandard2.0;{framework}</TargetFrameworks>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n    <Compile Include=\"Other.fs\" />\n  </ItemGroup>\n</Project>\n"

    write
        "src/Lib/Library.fs"
        "module Lib\n\nlet add (a: int, b: int) = a + b\n\n#if NETSTANDARD\nlet three () = add (1, 2)\n#else\nlet three () = add (1, 2)\n#endif\n"

    write "src/Lib/Other.fs" "module Other\n\nlet mul (a: int, b: int) = a * b\n\nlet internal six () = mul (2, 3)\n"

    write
        "tests/Tests/Tests.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Tests.fs\" />\n  </ItemGroup>\n  <ItemGroup>\n    <ProjectReference Include=\"../../src/Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"

    write "tests/Tests/Tests.fs" "module Tests\n\nlet three () = Lib.add (1, 2)\n"

    let entries =
        [ "Lib", "src\\Lib\\Lib.fsproj"; "Tests", "tests\\Tests\\Tests.fsproj" ]
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

[<Fact>]
let ``a definition the all-frameworks arbiter puts back takes the sibling's rewritten call site with it`` () : unit =
    let root = tempRoot "fsref-audit-siblings-"

    try
        let solution = writeMultiTargetSolution root
        let dir = Path.GetDirectoryName solution

        let code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0090"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(dir, "src", "Lib", "Library.fs"))
        let other = File.ReadAllText(Path.Combine(dir, "src", "Lib", "Other.fs"))
        let tests = File.ReadAllText(Path.Combine(dir, "tests", "Tests", "Tests.fs"))

        // the run reports the put-back (exit 1); what matters is the tree
        // it leaves behind
        ignore code

        Assert.True(
            output.Contains "rewritten by the same suggestion",
            $"expected the bisection to put the sibling's file back with the definition:\n{output}"
        )
        // the definition went back...
        Assert.Contains("let add (a: int, b: int) = a + b", library)
        // ...and so did the sibling's call site, rewritten by the same suggestion
        Assert.Contains("Lib.add (1, 2)", tests)
        Assert.DoesNotContain("Lib.add 1 2", tests)
        // while the innocent suggestion in the other file was kept
        Assert.Contains("let mul (a: int) (b: int) = a * b", other)

        let built, buildOutput = builds solution
        Assert.True(built, $"the solution should build after the put-back:\n{buildOutput}\n\ntool output:\n{output}")
    finally
        cleanup root
