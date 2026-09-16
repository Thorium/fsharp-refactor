/// Driver fixes from the 0.8.11 real-repository sweep: a relative
/// strong-name key resolved against the project directory rather than the
/// tool's (B14, FsCheck), the innocent fixes of a pass surviving a rollback
/// whose culprit sat in a file the errors never named (A11, FsToolkit), a
/// project's outputs still on disk for the script that `#r`s them after
/// the compiler-argument query (B17, svg_path_fsharp), and an exit line
/// naming the compilation behind a non-zero exit (B16). In the
/// "ProjectSources" collection: the end-to-end tests run `main`, whose
/// per-run stores are process-wide.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AuditDriverTests

open System
open System.Diagnostics
open System.IO
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor.Tool

let private checker = FSharpChecker.Create()

/// A driver function called directly, with the prose it writes to stderr
/// (put-backs, rolled-back fixes) kept out of the test run's output.
let private quietly (f: unit -> 'T) : 'T =
    use captured = new StringWriter()
    let oldErr = Console.Error
    Console.SetError captured

    try
        f ()
    finally
        Console.SetError oldErr

let private tempRoot (prefix: string) =
    let root = Path.Combine(Path.GetTempPath(), prefix + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory root |> ignore
    root

let private cleanup (root: string) =
    try
        Directory.Delete(root, true)
    with _ ->
        ()

/// The options of a real library project over the given files, in the
/// order given, without MSBuild: the reference set of a probe script in
/// the same directory, as the other project-level tests build theirs.
let private projectOptions (projectFile: string) (files: string list) =
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
    }

let private errorsOf (results: FSharpCheckProjectResults) =
    results.Diagnostics
    |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)

/// The framework the temporary projects target: the one this test host
/// runs on, which the machine therefore has an SDK for.
let private framework =
    let version = Environment.Version.Major
    $"net{version}.0"

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

/// `dotnet build` of a project, as the developer would run it.
let private build (project: string) =
    let psi =
        ProcessStartInfo(
            "dotnet",
            $"build \"{project}\" -nologo -v:q",
            RedirectStandardOutput = true,
            RedirectStandardError = true,
            UseShellExecute = false,
            WorkingDirectory = Path.GetDirectoryName project
        )

    use proc = Process.Start psi
    let output = proc.StandardOutput.ReadToEnd() + proc.StandardError.ReadToEnd()
    proc.WaitForExit()
    proc.ExitCode = 0, output

// ---- B14: relative compiler-argument paths become absolute against the project ----

[<Fact>]
let ``absolutizeArgs rebases the path-carrying arguments against the project directory`` () =
    let projectDir = Path.Combine(Path.GetTempPath(), "fsref-proj", "src", "Lib")

    let args =
        [|
            "--keyfile:../../Key.snk"
            "--doc:bin\\Debug\\Lib.xml"
            "-r:..\\..\\packages\\A.dll"
            "--resource:res\\a.txt,Lib.a.txt,public"
            "--lib:..\\lib;C:\\absolute\\dir"
            "-o:obj\\Debug\\Lib.dll"
            "--target:library"
            "--define:DEBUG"
            "Library.fs"
        |]

    let rebased = Program.absolutizeArgs projectDir args

    let expect (relative: string) =
        Path.GetFullPath(Path.Combine(projectDir, relative))

    let key = expect "../../Key.snk"
    let doc = expect "bin\\Debug\\Lib.xml"
    let reference = expect "..\\..\\packages\\A.dll"
    let resource = expect "res\\a.txt"
    let lib = expect "..\\lib"
    let out = expect "obj\\Debug\\Lib.dll"

    Assert.Equal($"--keyfile:{key}", rebased.[0])
    Assert.Equal($"--doc:{doc}", rebased.[1])
    Assert.Equal($"-r:{reference}", rebased.[2])
    // only the file component of a resource, the name and visibility as given
    Assert.Equal($"--resource:{resource},Lib.a.txt,public", rebased.[3])
    // every directory of a --lib list, an absolute one untouched
    Assert.Equal($"--lib:{lib};C:\\absolute\\dir", rebased.[4])
    Assert.Equal($"-o:{out}", rebased.[5])
    // flags without a path, and the bare source names, pass through
    Assert.Equal("--target:library", rebased.[6])
    Assert.Equal("--define:DEBUG", rebased.[7])
    Assert.Equal("Library.fs", rebased.[8])

[<Fact>]
let ``absolutizeArgs leaves absolute paths as they are`` () =
    let projectDir = Path.Combine(Path.GetTempPath(), "fsref-proj")
    let absolute = Path.Combine(Path.GetTempPath(), "elsewhere", "FSharp.Core.dll")

    let rebased = Program.absolutizeArgs projectDir [| $"-r:{absolute}"; "--keyfile:" |]

    Assert.Equal($"-r:{absolute}", rebased.[0])
    Assert.Equal("--keyfile:", rebased.[1])

[<Fact>]
let ``a relative AssemblyKeyFile attribute resolves against the project directory, not the tool's`` () =
    // FsCheck: `[<assembly: AssemblyKeyFile("../../FsCheckKey.snk")>]` in
    // src/FsCheck/AssemblyInfo.fs, the key at the repository root. FCS
    // opens that path as spelled, from the process directory, and a run
    // from the root refused every library project with "The key file
    // '../../FsCheckKey.snk' could not be opened"
    let root = tempRoot "fsref-driver-keyfile-"

    try
        let projectDir = Path.Combine(root, "src", "Lib")
        Directory.CreateDirectory projectDir |> ignore

        // a real key pair in the .snk format (a CAPI PRIVATEKEYBLOB, which
        // is what `sn -k` writes)
        use rsa = new System.Security.Cryptography.RSACryptoServiceProvider(2048)
        File.WriteAllBytes(Path.Combine(root, "Key.snk"), rsa.ExportCspBlob true)

        let assemblyInfo = Path.Combine(projectDir, "AssemblyInfo.fs")
        let library = Path.Combine(projectDir, "Library.fs")

        File.WriteAllText(
            assemblyInfo,
            "namespace Lib\n\nopen System.Reflection\n\n[<assembly: AssemblyKeyFile(\"../../Key.snk\")>]\ndo ()\n"
        )

        File.WriteAllText(library, "module Lib.Library\n\nlet answer = 42\n")

        let options =
            projectOptions (Path.Combine(projectDir, "Lib.fsproj")) [ assemblyInfo; library ]

        // the control: checked from the test host's own directory, FCS
        // cannot open the key (the reason the tool refused FsCheck)
        let plain =
            checker.ParseAndCheckProject options |> Async.RunSynchronously |> errorsOf

        Assert.True(
            plain |> Array.exists (fun d -> d.Message.Contains "could not be opened"),
            $"expected the plain check to fail on the relative key file: %A{plain}"
        )

        // the tool's check runs from the project directory, as msbuild runs fsc
        let before = Environment.CurrentDirectory
        checker.InvalidateConfiguration options
        let fromProject = Program.checkProject checker options |> errorsOf

        Assert.True(fromProject.Length = 0, $"the check from the project directory reports errors: %A{fromProject}")
        // and puts the process directory back
        Assert.Equal(before, Environment.CurrentDirectory)
    finally
        cleanup root

// ---- A11 (driver half): innocent fixes survive a rollback whose culprit is elsewhere ----

let private fix (line: int) (startColumn: int) (endColumn: int) (fromText: string) (toText: string) : Fix =
    {
        FromRange = Range.mkRange "" (Position.mkPos line startColumn) (Position.mkPos line endColumn)
        FromText = fromText
        ToText = toText
    }

[<Fact>]
let ``a pass broken by a fix in a file the errors never name keeps every other fix`` () =
    // FsToolkit Tests [net8.0]: FR0130 put [<Literal>] on `let lat` in
    // TestData.fs; the errors (FS3190, a lowercase literal shadowed by a
    // pattern) landed in Result.fs, whose own fixes were innocent. Writing
    // Result.fs back did not clear them, and the pass rolled back and
    // suppressed all 155 fixes; the next pass applied 0 of the 152 innocent
    let root = tempRoot "fsref-driver-rollback-"

    try
        let testData = Path.Combine(root, "TestData.fs")
        let extra = Path.Combine(root, "Extra.fs")
        let result = Path.Combine(root, "Result.fs")

        let testDataBefore = "module TestData\n\nlet lat = 13.06\n"
        let testDataAfter = "module TestData\n\n[<Literal>]\nlet lat = 13.06\n"
        let extraBefore = "module Extra\n\nlet twice (n: int) = n + n\n"
        let extraAfter = "module Extra\n\nlet twice (n: int) = 2 * n\n"

        let resultBefore =
            "module Result\n\nopen TestData\n\nlet describe (x: float) =\n    match x with\n    | lat -> id lat\n"

        let resultAfter =
            "module Result\n\nopen TestData\n\nlet describe (x: float) =\n    match x with\n    | lat -> lat\n"

        // the tree as the pass left it
        File.WriteAllText(testData, testDataAfter)
        File.WriteAllText(extra, extraAfter)
        File.WriteAllText(result, resultAfter)

        // FS3190 is a warning on its own; FsToolkit builds with
        // TreatWarningsAsErrors, which is what made the pass fail
        let options =
            let plain =
                projectOptions (Path.Combine(root, "Tests.fsproj")) [ testData; extra; result ]

            { plain with
                OtherOptions = Array.append plain.OtherOptions [| "--warnaserror:3190" |]
            }

        let literalFix = fix 3 0 15 "let lat = 13.06" "[<Literal>]\nlet lat = 13.06"
        let extraFix = fix 3 21 26 "n + n" "2 * n"
        let resultFix = fix 7 13 19 "id lat" "lat"

        let changed: Program.AppliedFile list =
            [
                {
                    Path = testData
                    Before = testDataBefore
                    Fixes = [ 1, "FR0130", literalFix ]
                }
                {
                    Path = extra
                    Before = extraBefore
                    Fixes = [ 2, "FR0012", extraFix ]
                }
                {
                    Path = result
                    Before = resultBefore
                    Fixes = [ 3, "FR0095", resultFix ]
                }
            ]

        let suppressed = Collections.Generic.HashSet<string * string * string * string>()

        let clean =
            quietly (fun () -> Program.verifyPass checker options 0 suppressed changed)

        // the pass did introduce errors...
        Assert.False clean
        // ...and only the culprit went back and was suppressed
        Assert.Equal(testDataBefore, File.ReadAllText testData)
        Assert.Equal(extraAfter, File.ReadAllText extra)
        Assert.Equal(resultAfter, File.ReadAllText result)

        Assert.Contains(("FR0130", testData, literalFix.FromText, literalFix.ToText), suppressed)
        Assert.DoesNotContain(("FR0012", extra, extraFix.FromText, extraFix.ToText), suppressed)
        Assert.DoesNotContain(("FR0095", result, resultFix.FromText, resultFix.ToText), suppressed)

        // and the tree it leaves checks clean
        checker.InvalidateConfiguration options
        let after = Program.checkProject checker options |> errorsOf
        Assert.True(after.Length = 0, $"the kept fixes should check clean: %A{after}")
    finally
        cleanup root

[<Fact>]
let ``a pass whose error-site fixes are the culprits still rolls back only those`` () =
    // the positive control for the salvage that already existed: the
    // culprit sits in the file the errors name, and the bisection above
    // is never entered
    let root = tempRoot "fsref-driver-rollback-named-"

    try
        let a = Path.Combine(root, "A.fs")
        let b = Path.Combine(root, "B.fs")

        let aBefore = "module A\n\nlet twice (n: int) = n + n\n"
        let aAfter = "module A\n\nlet twice (n: int) = 2 * n\n"

        let bBefore =
            "module B\n\nlet four () = A.twice 2\n\nlet text (s: string) = s + \"\"\n"
        // the second fix is wrong: an int where a string is expected
        let bAfter = "module B\n\nlet four () = A.twice 2\n\nlet text (s: string) = s + 1\n"

        File.WriteAllText(a, aAfter)
        File.WriteAllText(b, bAfter)

        let options = projectOptions (Path.Combine(root, "Tests.fsproj")) [ a; b ]

        let aFix = fix 3 21 26 "n + n" "2 * n"
        let bFix = fix 5 27 31 "\"\"" "1"

        let changed: Program.AppliedFile list =
            [
                {
                    Path = a
                    Before = aBefore
                    Fixes = [ 1, "FR0012", aFix ]
                }
                {
                    Path = b
                    Before = bBefore
                    Fixes = [ 2, "FR0999", bFix ]
                }
            ]

        let suppressed = Collections.Generic.HashSet<string * string * string * string>()

        Assert.False(quietly (fun () -> Program.verifyPass checker options 0 suppressed changed))

        Assert.Equal(aAfter, File.ReadAllText a)
        Assert.Equal(bBefore, File.ReadAllText b)
        Assert.Contains(("FR0999", b, bFix.FromText, bFix.ToText), suppressed)
        Assert.DoesNotContain(("FR0012", a, aFix.FromText, aFix.ToText), suppressed)
    finally
        cleanup root

// ---- B17, end to end: a script's #r of a project's built dll resolves after the project's pass ----

[<Fact>]
let ``a script that #r's a project's output dll still resolves it after the project was swept`` () : unit =
    // svg_path_fsharp: `#r "../../src/SvgPath/bin/Debug/net9.0/SvgPath.dll"`
    // in examples/debug/*.fsx. The dll was there before the sweep; the
    // project's compiler-argument query (a Rebuild that skips the
    // compiler) cleaned it and, for an SDK-style project, nothing built
    // it back — so four of five scripts ran syntactic rules only
    let root = tempRoot "fsref-driver-script-r-"

    try
        let write (relative: string) (content: string) =
            let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, content)

        write
            "src/Lib/Lib.fsproj"
            $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

        write "src/Lib/Library.fs" "module Lib\n\nlet answer = 42\n"

        write
            "examples/check.fsx"
            $"#r \"../src/Lib/bin/Debug/{framework}/Lib.dll\"\n\nlet doubled = Lib.answer * 2\nprintfn \"%%d\" doubled\n"

        let project = Path.Combine(root, "src", "Lib", "Lib.fsproj")
        let dll = Path.Combine(root, "src", "Lib", "bin", "Debug", framework, "Lib.dll")

        // the developer's build, before the sweep: the dll the script names
        let built, buildOutput = build project
        Assert.True(built, $"the project should build:\n{buildOutput}")
        Assert.True(File.Exists dll, $"the developer's build should leave {dll}")

        let code, output = runTool [| root; "--no-color" |]

        Assert.True(File.Exists dll, $"the project's pass should leave its output dll for the script:\n{output}")

        Assert.False(
            output.Contains "unresolved-reference error(s) ignored",
            $"the script's #r should resolve after the project's pass:\n{output}"
        )

        Assert.DoesNotContain("'Lib' is not defined", output)
        Assert.True((code = 0), $"a clean sweep exits 0:\n{output}")
    finally
        cleanup root

// ---- B16, end to end: a non-zero exit is explained on its last line ----

[<Fact>]
let ``a run that exits non-zero says which compilation caused it and why`` () : unit =
    let root = tempRoot "fsref-driver-exit-"

    try
        let write (relative: string) (content: string) =
            let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, content)

        write
            "Broken/Broken.fsproj"
            $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

        // does not build: an int where a string is expected
        write "Broken/Library.fs" "module Broken\n\nlet text (s: string) = s + 1\n"

        let code, output =
            runTool [| Path.Combine(root, "Broken", "Broken.fsproj"); "--no-color" |]

        Assert.Equal(1, code)

        let lastLines =
            output.Split('\n') |> Array.map (fun l -> l.TrimEnd()) |> Array.filter ((<>) "")

        let exitLine = lastLines |> Array.tryFind (fun l -> l.StartsWith "exit 1:")

        Assert.True(exitLine.IsSome, $"expected an 'exit 1:' line naming the compilation:\n{output}")
        Assert.Contains("Broken.fsproj", exitLine.Value)
        Assert.Contains("does not build", exitLine.Value)
    finally
        cleanup root

// ---- the sweep dedup and #if INTERACTIVE ----

[<Fact>]
let ``a file whose only directives are INTERACTIVE or COMPILED sweeps once across frameworks`` () : unit =
    // `#if INTERACTIVE` / `#if !INTERACTIVE` is how a source is written to
    // serve as both a project file and a #load'ed script (skipping the
    // email send when run interactively); neither symbol varies between a
    // project's frameworks, so such a file needs one sweep, not one per
    // framework. Any other condition keeps the per-defines key
    let root = tempRoot "fsref-driver-interactive-"

    try
        let write (name: string) (content: string) =
            let path = Path.Combine(root, name)
            File.WriteAllText(path, content)
            path

        let interactiveOnly =
            write "A.fs" "module A\n\n#if INTERACTIVE\nlet send () = ()\n#else\nlet send () = Mail.send ()\n#endif\n"

        let negated =
            write "B.fs" "module B\n\n#if !INTERACTIVE && COMPILED // both spellings\nlet x = 1\n#endif\n"

        let framework =
            write "C.fs" "module C\n\n#if NET8_0_OR_GREATER\nlet x = 1\n#endif\n"

        let mixed = write "D.fs" "module D\n\n#if INTERACTIVE || DEBUG\nlet x = 1\n#endif\n"

        let plain = write "E.fs" "module E\n\nlet x = 1\n"

        Assert.True(Program.isDirectiveFree interactiveOnly)
        Assert.True(Program.isDirectiveFree negated)
        Assert.False(Program.isDirectiveFree framework)
        Assert.False(Program.isDirectiveFree mixed)
        Assert.True(Program.isDirectiveFree plain)
    finally
        cleanup root
