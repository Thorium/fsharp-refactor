/// The tool driver when a run ends early: a failure or an interrupt puts
/// back the compilation in progress, and a flag or report path that cannot
/// work is refused before anything is written. In the "ProjectSources"
/// collection: the snapshot record and the interrupt flag are process-wide
/// state, and some tests run `main`.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.ReleaseAuditToolTests

open System
open System.IO
open Xunit
open FSharp.Refactor.Tool

/// A driver function called directly; returns its result and what it wrote
/// to stderr.
let private withStderr (f: unit -> 'T) : 'T * string =
    use captured = new StringWriter()
    let oldErr = Console.Error
    Console.SetError captured

    try
        let result = f ()
        result, captured.ToString()
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

/// A compilation mid-pass: its own file and a sibling's, both rewritten.
let private rewrittenPair (root: string) =
    let own = Path.Combine(root, "Library.fs")
    let sibling = Path.Combine(root, "Tests.fs")
    File.WriteAllText(own, "let add (a: int, b: int) = a + b\n")
    File.WriteAllText(sibling, "let three () = Lib.add (1, 2)\n")
    Program.takeSnapshot [| own |] |> ignore
    Program.recordExtra sibling (File.ReadAllText sibling)
    File.WriteAllText(own, "let add (a: int) (b: int) = a + b\n")
    File.WriteAllText(sibling, "let three () = Lib.add 1 2\n")
    own, sibling

let private assertOriginals (own: string) (sibling: string) =
    Assert.Equal("let add (a: int, b: int) = a + b\n", File.ReadAllText own)
    Assert.Equal("let three () = Lib.add (1, 2)\n", File.ReadAllText sibling)

// ---- a failure mid-pass puts the compilation back ----

[<Fact>]
let ``a source that cannot be written puts the compilation back and costs the target`` () =
    let root = tempRoot "fsref-release-fail-"

    try
        let own, sibling = rewrittenPair root

        let code, said =
            withStderr (fun () ->
                Program.restoringOnFailure (fun () ->
                    raise (UnauthorizedAccessException "Access to Other.fs is denied.")))

        Assert.Equal(1, code)
        Assert.Contains("Access to Other.fs is denied.", said)
        Assert.Contains("2 file(s)", said)
        assertOriginals own sibling
    finally
        Program.takeSnapshot [||] |> ignore
        lock Program.exitReasons Program.exitReasons.Clear
        cleanup root

[<Fact>]
let ``any other failure puts the compilation back and goes on to end the run`` () =
    let root = tempRoot "fsref-release-fail-"

    try
        let own, sibling = rewrittenPair root

        let thrown, _ =
            withStderr (fun () ->
                Assert.Throws<InvalidOperationException>(fun () ->
                    Program.restoringOnFailure (fun () -> raise (InvalidOperationException "a bug"))
                    |> ignore))

        Assert.Equal("a bug", thrown.Message)
        assertOriginals own sibling
    finally
        Program.takeSnapshot [||] |> ignore
        cleanup root

[<Fact>]
let ``a target that finishes keeps its fixes, and a later interrupt leaves them`` () =
    let root = tempRoot "fsref-release-fail-"

    try
        let own, sibling = rewrittenPair root

        Assert.Equal(0, Program.restoringOnFailure (fun () -> 0))
        Assert.Equal(0, Program.putBackOnInterrupt ())
        Assert.Equal("let add (a: int) (b: int) = a + b\n", File.ReadAllText own)
        Assert.Equal("let three () = Lib.add 1 2\n", File.ReadAllText sibling)
    finally
        Program.clearInterrupt ()
        Program.takeSnapshot [||] |> ignore
        cleanup root

// ---- Ctrl+C ----

[<Fact>]
let ``an interrupt puts the compilation in progress back and nothing is written after it`` () =
    let root = tempRoot "fsref-release-interrupt-"

    try
        let own, sibling = rewrittenPair root
        let snapshot = Map.ofList [ own, "let add (a: int, b: int) = a + b\n" ]

        Assert.Equal(2, Program.putBackOnInterrupt ())
        assertOriginals own sibling

        // the main thread, still running, reaches its next write
        File.WriteAllText(own, "let add (a: int) (b: int) = a + b\n")

        Assert.Throws<OperationCanceledException>(fun () -> Program.restoreSnapshot snapshot |> ignore)
        |> ignore

        Assert.Equal("let add (a: int) (b: int) = a + b\n", File.ReadAllText own)
    finally
        Program.clearInterrupt ()
        Program.takeSnapshot [||] |> ignore
        cleanup root

// ---- refused before any work ----

[<Fact>]
let ``--report followed by a flag is a usage error, not a report named after the flag`` () =
    let root = tempRoot "fsref-release-args-"
    let before = Directory.GetCurrentDirectory()

    try
        Directory.SetCurrentDirectory root

        let code, said =
            withStderr (fun () -> Program.main [| "Missing.fsproj"; "--report"; "--dry-run" |])

        Assert.Equal(2, code)
        Assert.Contains("'--report' needs a value after it", said)
        Assert.False(File.Exists(Path.Combine(root, "--dry-run")))
    finally
        Directory.SetCurrentDirectory before
        cleanup root

[<Fact>]
let ``--baseline followed by a flag is a usage error`` () =
    let code, said =
        withStderr (fun () -> Program.main [| "Missing.fsproj"; "--baseline"; "--dry-run" |])

    Assert.Equal(2, code)
    Assert.Contains("'--baseline' needs a value after it", said)

[<Fact>]
let ``a report into a directory that does not exist is refused before any work`` () =
    let root = tempRoot "fsref-release-report-"

    try
        let script = Path.Combine(root, "probe.fsx")
        File.WriteAllText(script, "let isEmpty (xs: int list) = List.length xs = 0\n")
        let report = Path.Combine(root, "artifacts", "findings.sarif")

        let code, said =
            withStderr (fun () -> Program.main [| script; "--report"; report; "--no-color" |])

        Assert.Equal(2, code)
        Assert.Contains("--report", said)
        Assert.Contains("does not exist", said)
        // nothing ran: the fix FR0010 offers was not applied
        Assert.Equal("let isEmpty (xs: int list) = List.length xs = 0\n", File.ReadAllText script)
    finally
        cleanup root

[<Fact>]
let ``a config that is no JSON refuses the run, where the analyzers alone read it as no config`` () =
    let root = tempRoot "fsref-release-config-"

    try
        // a repository of its own, so the search for a config stops here
        Directory.CreateDirectory(Path.Combine(root, ".git")) |> ignore
        let script = Path.Combine(root, "probe.fsx")
        let config = Path.Combine(root, FSharp.Refactor.Configuration.ConfigFileName)
        File.WriteAllText(script, "let isEmpty (xs: int list) = List.length xs = 0\n")
        // a missing comma: FR0010 was meant to be off
        File.WriteAllText(config, "{ \"FR0010\": false \"ignorePaths\": [] }")

        Assert.True((FSharp.Refactor.Configuration.problemFor script).IsSome)

        let code, said = withStderr (fun () -> Program.main [| script; "--no-color" |])

        Assert.Equal(2, code)
        Assert.Contains("cannot be read", said)
        Assert.Equal("let isEmpty (xs: int list) = List.length xs = 0\n", File.ReadAllText script)

        File.WriteAllText(config, "{ \"FR0010\": false, \"ignorePaths\": [] }")
        Assert.True((FSharp.Refactor.Configuration.problemFor script).IsNone)
    finally
        cleanup root

// ---- globs ----

[<Fact>]
let ``a glob searches the directories it names, not every directory under the first`` () =
    let root = tempRoot "fsref-release-glob-"

    try
        for relative in
            [
                "src/App/App.fsproj"
                "src/AppTests/AppTests.fsproj"
                "src/Lib/Lib.fsproj"
                "src/Lib/Nested/Deep.fsproj"
                "Top.fsproj"
            ] do
            let path = Path.Combine(root, relative)
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, "<Project />")

        let found (pattern: string) =
            FileWalk.glob (Path.Combine(root, pattern))
            |> List.map (fun f -> Path.GetRelativePath(root, f).Replace('\\', '/'))
            |> List.sort

        Assert.Equal<string list>([ "src/App/App.fsproj"; "src/AppTests/AppTests.fsproj" ], found "src/App*/*.fsproj")
        Assert.Equal<string list>([ "Top.fsproj" ], found "*.fsproj")
        Assert.Equal<string list>([ "src/Lib/Lib.fsproj" ], found "src/Li?/*.fsproj")
        Assert.Equal<string list>([ "src/Lib/Nested/Deep.fsproj" ], found "src/*/Nested/*.fsproj")

        Assert.Equal<string list>(
            [
                "src/App/App.fsproj"
                "src/AppTests/AppTests.fsproj"
                "src/Lib/Lib.fsproj"
                "src/Lib/Nested/Deep.fsproj"
            ],
            found "src/**/*.fsproj"
        )

        Assert.Equal(5, (found "**/*.fsproj").Length)
        // a `?` with no `*` is a glob too
        Assert.Equal<string list>([ "Top.fsproj" ], found "To?.fsproj")
    finally
        cleanup root

// ---- the command line's filters ----

[<Fact>]
let ``filters that leave no rule to run are refused`` () =
    let refusal (args: string list) =
        let code, said = withStderr (fun () -> Program.main (Array.ofList args))
        Assert.Equal(2, code)
        said

    Assert.Contains("names no rule code", refusal [ "Missing.fsproj"; "--codes"; "" ])
    // FR0010 is an idiom rule
    Assert.Contains(
        "leave no rule to run",
        refusal [ "Missing.fsproj"; "--codes"; "FR0010"; "--categories"; "cosmetic" ]
    )
