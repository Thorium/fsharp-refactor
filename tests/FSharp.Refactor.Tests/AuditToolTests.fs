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
let ``a later compilation's build failure puts back the files an earlier one rewrote`` () =
    // elmish: src/program.fs interpolated under Elmish.fsproj, then
    // Fable.Elmish.fsproj (FSharp.Core 4.7) would not build on it - the run
    // used to blame the tree; the file goes back to the run's original
    let root = tempRoot "fsref-audit-runedit-"

    try
        let shared = Path.Combine(root, "program.fs")
        let untouched = Path.Combine(root, "other.fs")
        File.WriteAllText(shared, "let s = sprintf \"%d\" 1\n")
        File.WriteAllText(untouched, "let t = 2\n")

        // the first compilation snapshots and rewrites the file
        Program.takeSnapshot [| shared |] |> ignore
        File.WriteAllText(shared, "let s = $\"%d{1}\"\n")

        // the second compilation snapshots its own files (afresh) and fails
        Program.takeSnapshot [| untouched |] |> ignore

        let message =
            $"dotnet build failed - fix the build before applying fixes:\n{shared}(1,9): error FS3349: Feature 'string interpolation' requires the F# library for language version 5.0 or greater.\n{untouched}(1,1): error FS0001: unrelated"

        Assert.Equal(1, (quietly (fun () -> Program.putBackRunEdits message "Fable.Elmish.fsproj")).Length)
        Assert.Equal("let s = sprintf \"%d\" 1\n", File.ReadAllText shared)
        Assert.Equal("let t = 2\n", File.ReadAllText untouched)
        // nothing left to put back
        Assert.Empty(Program.putBackRunEdits message "Fable.Elmish.fsproj")
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
    withScript "#load \"../gone.fs\"\n#load \"../src/Lib/Core.fs\"" Assert.Empty

[<Fact>]
let ``a #r with a path that leads nowhere still makes the script stale`` () =
    withScript "#r \"../src/Lib/bin/Nope.dll\"\n#load \"../src/Lib/Core.fs\"" Assert.Empty

[<Fact>]
let ``a #load with nothing missing gets no suggestion`` () =
    withScript "#load \"../src/Lib/Util.fs\"\n#load \"../src/Lib/Core.fs\"" Assert.Empty

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

// ---- D6: a verification build that never judged is not "pre-existing" ----

/// What `runProcessIn` hands back for a build stopped at the time cap: no
/// output, and one stderr line — the marker in front, no "error" in it.
let private timedOut =
    Program.TimeCapMark
    + " 'dotnet build \"Lib.fsproj\" --nologo -v q' had not finished after 15 minutes, so it was stopped."

[<Fact>]
let ``runProcessIn marks a child stopped at the cap, so the classifier need not read the prose`` () =
    // a 1 ms cap: no `dotnet --info` starts and finishes inside it
    let code, out, err =
        Program.runProcessIn None (TimeSpan.FromMilliseconds 1.) "dotnet" "--info"

    Assert.Equal(-1, code)
    Assert.Equal("", out)
    Assert.StartsWith(Program.TimeCapMark, err)
    Assert.True(Program.stoppedAtTimeCap (Program.buildFailureLines out err))

[<Fact>]
let ``only the marker says a build was stopped at the cap`` () =
    Assert.True(Program.stoppedAtTimeCap (Program.buildFailureLines "" timedOut))
    // the prose alone, quoted by something else, is not the cap
    Assert.False(Program.stoppedAtTimeCap [| "the build had not finished after 15 minutes, so it was stopped." |])
    Assert.False(Program.stoppedAtTimeCap [| "error MSB3073: The command \"sign.cmd\" exited with code 1." |])
    Assert.False(Program.stoppedAtTimeCap [||])

[<Fact>]
let ``a build failure without an error line keeps its reason instead of an empty list`` () =
    // the empty list was the defect: `Error [||]` read as "no compiler
    // error introduced", so a timed-out build kept every fix
    let lines = Program.buildFailureLines "" timedOut
    Assert.NotEmpty lines
    Assert.Contains(timedOut, lines)
    Assert.False(Program.hasCompilerErrors lines)

[<Fact>]
let ``only a compiler error line counts as a compiler error`` () =
    Assert.True(Program.hasCompilerErrors [| @"C:\src\Lib.fs(3,5): error FS0039: The value 'x' is not defined" |])
    // a referencing C# or VB project's compiler, built with the verification
    Assert.True(
        Program.hasCompilerErrors
            [|
                @"C:\src\Use.cs(9,40): error CS0426: The type name 'Circle' does not exist in the type 'Shape'"
            |]
    )

    Assert.True(
        Program.hasCompilerErrors [| @"C:\src\Use.vb(9,40): error BC30002: Type 'Shape.Circle' is not defined." |]
    )
    // tooling, not code
    Assert.False(Program.hasCompilerErrors [| "error NETSDK1005: Assets file doesn't have a target for 'net8.0'" |])
    Assert.False(Program.hasCompilerErrors [| "error MSB4019: The imported project was not found" |])
    Assert.False(Program.hasCompilerErrors [| "error MSB3073: The command \"sign.cmd\" exited with code 1." |])
    Assert.False(Program.hasCompilerErrors [||])

[<Fact>]
let ``a timed-out build with the fixes is not judged pre-existing, and no baseline is rebuilt for it`` () =
    let rebuilt = ref 0

    let verdict =
        Program.judgeAgainstBaseline
            (fun () ->
                rebuilt.Value <- rebuilt.Value + 1
                Ok())
            (Program.buildFailureLines "" timedOut)
            [| "Lib.fs(1,1): error FS0001: pre-existing" |]

    Assert.Equal(Program.Blame.NotVerified, verdict)
    Assert.Equal(0, rebuilt.Value)

[<Fact>]
let ``a timed-out baseline cannot clear the fixes either`` () =
    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> Ok())
            [| "Lib.fs(1,1): error FS0001: with the fixes" |]
            (Program.buildFailureLines "" timedOut)

    Assert.Equal(Program.Blame.NotVerified, verdict)

[<Fact>]
let ``a second baseline that times out is not verification`` () =
    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> Error(Program.buildFailureLines "" timedOut))
            [| "Lib.fs(1,1): error FS0001: old"; "Lib.fs(9,1): error FS0039: new" |]
            [| "Lib.fs(1,1): error FS0001: old" |]

    Assert.Equal(Program.Blame.NotVerified, verdict)

[<Fact>]
let ``the same compiler errors with and without the fixes are pre-existing`` () =
    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> failwith "no second baseline is needed when nothing was introduced")
            [| "Lib.fs(4,1): error FS0001: old" |]
            // the same error, moved by a fix above it
            [| "Lib.fs(1,1): error FS0001: old" |]

    Assert.Equal(Program.Blame.PreExisting, verdict)

[<Fact>]
let ``a compiler error seen only with the fixes, twice, is introduced`` () =
    let baseline = [| "Lib.fs(1,1): error FS0001: old" |]

    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> Error baseline)
            [| "Lib.fs(1,1): error FS0001: old"; "Lib.fs(9,1): error FS0039: new" |]
            baseline

    match verdict with
    | Program.Blame.Introduced errors -> Assert.Equal<Set<string>>(set [ "Lib.fs: error FS0039: new" ], errors)
    | other -> failwithf "expected Introduced, got %A" other

[<Fact>]
let ``a tooling failure identical with and without the fixes is pre-existing breakage, not the cap`` () =
    // a post-compile Exec target that fails in this checkout whatever the
    // sources say: reading every failure without a compiler error as the
    // cap restored the whole snapshot before the baseline was even built,
    // and such a repository could never keep a fix
    let exec =
        Program.buildFailureLines
            "C:\\src\\Lib.fsproj(40,5): error MSB3073: The command \"sign.cmd bin\\Lib.dll\" exited with code 1.\n"
            ""

    Assert.False(Program.hasCompilerErrors exec)
    Assert.False(Program.stoppedAtTimeCap exec)

    let rebuilt = ref 0

    let verdict =
        Program.judgeAgainstBaseline
            (fun () ->
                rebuilt.Value <- rebuilt.Value + 1
                Error exec)
            exec
            exec

    Assert.Equal(Program.Blame.PreExisting, verdict)
    Assert.Equal(0, rebuilt.Value)

[<Fact>]
let ``a targeting pack missing with and without the fixes is pre-existing too`` () =
    let pack =
        Program.buildFailureLines "" "error NETSDK1045: The current .NET SDK does not support targeting .NET 99.0."

    Assert.Equal(
        Program.Blame.PreExisting,
        Program.judgeAgainstBaseline (fun () -> failwith "no second baseline is needed") pack pack
    )

[<Fact>]
let ``a consumer's C# error seen only with the fixes, twice, is introduced`` () =
    // the referencing C# project built with the verification speaks in
    // CS errors, and they weigh like the F# compiler's
    let baseline =
        [|
            "Consumer/Other.cs(3,10): error CS0103: The name 'x' does not exist in the current context"
        |]

    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> Error baseline)
            [|
                baseline.[0]
                "Consumer/Use.cs(9,40): error CS0426: The type name 'Circle' does not exist in the type 'Shape'"
            |]
            baseline

    match verdict with
    | Program.Blame.Introduced errors ->
        Assert.Equal<Set<string>>(
            set
                [
                    "Consumer/Use.cs: error CS0426: The type name 'Circle' does not exist in the type 'Shape'"
                ],
            errors
        )
    | other -> failwithf "expected Introduced, got %A" other

// ---- D7: a typecheck given up on is given up on NOW ----

[<Fact>]
let ``awaitWithin gives up at the timeout even when the work never observes cancellation`` () =
    // `Async.RunSynchronously(_, timeout)` cancels and then waits for the
    // computation to quiesce, with no timeout of its own: a 6 s sleep came
    // back after 6 s against a 500 ms timeout. A type provider blocked in a
    // connection is that sleep.
    let sw = Stopwatch.StartNew()

    let raised =
        Assert.Throws<TimeoutException>(fun () ->
            Program.awaitWithin
                (TimeSpan.FromMilliseconds 300.)
                (fun () -> "the typecheck of Slow.fsproj had not finished")
                (async {
                    System.Threading.Thread.Sleep 4000
                    return 1
                })
            |> ignore)

    sw.Stop()
    Assert.Contains("Slow.fsproj", raised.Message)
    Assert.True(sw.ElapsedMilliseconds < 3000L, $"waited {sw.ElapsedMilliseconds} ms for a 300 ms timeout")

[<Fact>]
let ``awaitWithin returns the result of work that finishes in time`` () =
    Assert.Equal(42, Program.awaitWithin (TimeSpan.FromSeconds 10.) (fun () -> "unused") (async { return 42 }))

[<Fact>]
let ``awaitWithin rethrows the work's own exception, not an AggregateException`` () =
    Assert.Throws<InvalidOperationException>(fun () ->
        Program.awaitWithin
            (TimeSpan.FromSeconds 10.)
            (fun () -> "unused")
            (async { return invalidOp "the checker's own failure" })
        |> ignore)
    |> ignore

[<Fact>]
let ``awaitWithin cancels the work it gives up on`` () =
    // the abandoned typecheck used to run on to completion, rooting the
    // old checker and everything it had cached; work that observes the
    // token now stops as soon as the wait is over
    use observed = new System.Threading.ManualResetEventSlim(false)

    Assert.Throws<TimeoutException>(fun () ->
        Program.awaitWithin
            (TimeSpan.FromMilliseconds 200.)
            (fun () -> "gave up")
            (async {
                let! token = Async.CancellationToken
                token.Register(fun () -> observed.Set()) |> ignore
                do! Async.Sleep 20000
                return 1
            })
        |> ignore)
    |> ignore

    Assert.True(observed.Wait(TimeSpan.FromSeconds 5.), "the abandoned work was not cancelled")

// ---- the consumers the F# build check cannot see ----

/// A solution of a single-target F# library exposing a small PUBLIC union
/// and a C# class library that casts to one of the union's case classes —
/// FSharp.Azure.Quantum's shape. `[<Struct>]` (FR0016) on the union
/// compiles in every F# build and removes the nested case class the C#
/// names. `consumerFramework` lets a test make the consumer unbuildable.
let private writeConsumerSolution (root: string) (consumerFramework: string) =
    let write (relative: string) (content: string) =
        let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, content)

    write
        "src/Lib/Lib.fsproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"

    write
        "src/Lib/Library.fs"
        "module Lib\n\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float\n\nlet area (shape: Shape) =\n    match shape with\n    | Circle r -> 3.0 * r * r\n    | Square s -> s * s\n"

    write
        "src/Consumer/Consumer.csproj"
        $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{consumerFramework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <ProjectReference Include=\"../Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"

    write
        "src/Consumer/Use.cs"
        "namespace Consumer\n{\n    public static class Use\n    {\n        public static double Radius(Lib.Shape shape) => shape is Lib.Shape.Circle c ? c.radius : 0.0;\n    }\n}\n"

    let entries =
        [ "Lib", "src\\Lib\\Lib.fsproj"; "Consumer", "src\\Consumer\\Consumer.csproj" ]
        |> List.map (fun (name, path) ->
            $"Project(\"{{F2A71F9B-5D33-465A-A702-920D77279786}}\") = \"{name}\", \"{path}\", \"{{{Guid.NewGuid()}}}\"\nEndProject")
        |> String.concat "\n"

    write "Probe.sln" $"Microsoft Visual Studio Solution File, Format Version 12.00\n{entries}\nGlobal\nEndGlobal\n"
    Path.Combine(root, "Probe.sln")

[<Fact>]
let ``a fix that breaks the C# project referencing the library is put back, though every F# check passed`` () : unit =
    let root = tempRoot "fsref-audit-consumer-"

    try
        let solution = writeConsumerSolution root framework
        let dir = Path.GetDirectoryName solution

        let _code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0016"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(dir, "src", "Lib", "Library.fs"))

        // the consumer is named up front, built with the verification, and
        // its refusal puts the union's fix back
        Assert.True(
            output.Contains "Consumer.csproj references this project: built with it",
            $"expected the consumer to be announced:\n{output}"
        )

        Assert.True(
            output.Contains "verifying the referencing Consumer.csproj",
            $"expected the consumer's build:\n{output}"
        )

        Assert.True(output.Contains "put back", $"expected the fix to be put back:\n{output}")
        Assert.DoesNotContain("[<Struct>]", library)

        let built, buildOutput = builds solution
        Assert.True(built, $"the solution should build after the put-back:\n{buildOutput}\n\ntool output:\n{output}")
    finally
        cleanup root

[<Fact>]
let ``a consumer that cannot be built holds the library's public surface instead`` () : unit =
    let root = tempRoot "fsref-audit-consumer-held-"

    try
        // a framework no installed SDK targets: the consumer's build fails
        // before it compiles anything, so it can verify nothing
        let solution = writeConsumerSolution root "net99.0"
        let dir = Path.GetDirectoryName solution

        let _code, output =
            runTool [| solution; "--api-changes"; "--codes"; "FR0016"; "--no-color" |]

        let library = File.ReadAllText(Path.Combine(dir, "src", "Lib", "Library.fs"))

        Assert.True(
            output.Contains "Consumer.csproj references this project and does not build here",
            $"expected the unbuildable consumer to be reported:\n{output}"
        )

        Assert.Contains("public declarations keep their shape", output)
        // the public union keeps its class representation, --api-changes or not
        Assert.DoesNotContain("[<Struct>]", library)
        Assert.DoesNotContain("verifying the referencing", output)
    finally
        cleanup root

[<Fact>]
let ``a held public surface closes the api-changes gate whatever the flag says`` () =
    Scope.under
        { Scope.editor with
            ApiChanges = true
            PublicSurfaceHeld = true
        }
        (fun () -> Assert.False(Visibility.apiChangesAllowed ()))

    Scope.under { Scope.editor with ApiChanges = true } (fun () -> Assert.True(Visibility.apiChangesAllowed ()))
    Scope.under Scope.editor (fun () -> Assert.False(Visibility.apiChangesAllowed ()))

// ---- FR0130 and a library's public constants ----

[<Fact>]
let ``FR0130 leaves a library's public constants alone in a plain run and annotates them under --api-changes``
    ()
    : unit =
    // ClearBank.Net's WebhookTypes and CarmelNet's auth_server went
    // [<Literal>] in a plain sweep — a public const inlines its value into
    // every consumer — when the api-changes flag was still an environment
    // variable the test project set and the library then read. The gate
    // is Scope-scoped now; this pins it through the tool itself
    let root = tempRoot "fsref-audit-literal-"

    try
        let project = Path.Combine(root, "Lib", "Lib.fsproj")
        let library = Path.Combine(root, "Lib", "Library.fs")
        Directory.CreateDirectory(Path.GetDirectoryName project) |> ignore

        File.WriteAllText(
            project,
            $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <TargetFramework>{framework}</TargetFramework>\n  </PropertyGroup>\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n  </ItemGroup>\n</Project>\n"
        )

        File.WriteAllText(
            library,
            "module Lib\n\nlet ConnectionName = \"orders\"\n\nlet private Retries = 3\n\nlet describe () = ConnectionName + string Retries\n"
        )

        let normalised () =
            File.ReadAllText(library).Replace("\r\n", "\n")

        let code, output = runTool [| project; "--codes"; "FR0130"; "--no-color" |]
        Assert.True((code = 0), $"exit {code}:\n{output}")
        // the private constant is contained and gains the attribute...
        Assert.Contains("[<Literal>]\nlet private Retries", normalised ())
        // ...the public one is the library's API and keeps its getter
        Assert.DoesNotContain("[<Literal>]\nlet ConnectionName", normalised ())

        let code, output =
            runTool [| project; "--codes"; "FR0130"; "--api-changes"; "--no-color" |]

        Assert.True((code = 0), $"exit {code}:\n{output}")
        Assert.Contains("[<Literal>]\nlet ConnectionName", normalised ())
    finally
        cleanup root

[<Fact>]
let ``a tooling-only baseline and a clean rebuild blame the fixes, not the weather`` () =
    // the build with the fixes fails on a compiler error (a consumer's CS0426);
    // the first baseline fails on tooling alone (a file in use right after a
    // build); the rebuild passes. Both baselines agree the code without the
    // fixes compiles, so the error is the fixes' - not "the baselines disagree"
    let verdict =
        Program.judgeAgainstBaseline
            (fun () -> Ok())
            [| "Consumer.cs(614,5): error CS0426: nested type [Consumer.csproj]" |]
            [| "MSB3027: Could not copy Lib.dll: file in use [Consumer.csproj]" |]

    match verdict with
    | Program.Blame.Introduced errors -> Assert.Single errors |> ignore
    | other -> failwithf "Expected Introduced, got %A" other

[<Fact>]
let ``a framework list commented out of the project file is not one of its frameworks`` () =
    // welendus's WelendusLogic.fsproj: `<!-- <TargetFrameworks>netstandard2.0;net48</TargetFrameworks> -->`
    // above the live element made the run ask for a net48 pass (NETSDK1005)
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tfm-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory dir |> ignore

    try
        let project = Path.Combine(dir, "Lib.fsproj")

        File.WriteAllText(
            project,
            String.concat
                "\n"
                [
                    "<Project Sdk=\"Microsoft.NET.Sdk\">"
                    "  <PropertyGroup>"
                    "    <!-- <TargetFrameworks>netstandard2.0;net48</TargetFrameworks> -->"
                    "    <!--TargetFramework>net48</TargetFramework-->"
                    "    <TargetFrameworks>netstandard2.0;netstandard2.1</TargetFrameworks>"
                    "  </PropertyGroup>"
                    "</Project>"
                ]
        )

        Assert.Equal<string list>([ "netstandard2.0"; "netstandard2.1" ], Program.targetFrameworksOf project)
    finally
        try
            Directory.Delete(dir, true)
        with _ ->
            ()

[<Fact>]
let ``the configuration probe reads a compile item by the name the project spells`` () =
    // the item set is keyed by lowercased paths for membership; the READ
    // went through the key too, and on a case-sensitive file system
    // `library.fs` is not `Library.fs`: the unreadable file was taken to
    // branch on the configuration, and every project got the Release build
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-cfg-" + Guid.NewGuid().ToString("N"))

    Directory.CreateDirectory dir |> ignore

    try
        let project = Path.Combine(dir, "Lib.fsproj")

        File.WriteAllText(
            project,
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <ItemGroup>\n    <Compile Include=\"Library.fs\" />\n    <Compile Include=\"Branching.fs\" />\n  </ItemGroup>\n</Project>\n"
        )

        File.WriteAllText(Path.Combine(dir, "Library.fs"), "module Lib\n\nlet answer = 42\n")
        File.WriteAllText(Path.Combine(dir, "Branching.fs"), "module Other\n\nlet flag = 1\n")

        Assert.False(Program.hasConfigurationConditionals project, "no source branches on the configuration")

        // the probe is memoised per project path: a second project tells
        // the positive case apart from a stale answer
        let branching = Path.Combine(dir, "Branching.fsproj")

        File.WriteAllText(
            branching,
            "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <ItemGroup>\n    <Compile Include=\"Branching.fs\" />\n    <Compile Include=\"Debugging.fs\" />\n  </ItemGroup>\n</Project>\n"
        )

        File.WriteAllText(
            Path.Combine(dir, "Debugging.fs"),
            "module Debugging\n\n#if DEBUG\nlet verbose = true\n#else\nlet verbose = false\n#endif\n"
        )

        Assert.True(Program.hasConfigurationConditionals branching, "Debugging.fs branches on DEBUG")
    finally
        try
            Directory.Delete(dir, true)
        with _ ->
            ()
