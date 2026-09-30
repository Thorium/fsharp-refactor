module FSharp.Refactor.Tests.FileWalkTests

open System.IO
open Xunit
open FSharp.Refactor.Tool

/// A throwaway tree under the temp directory, removed afterwards.
let private withTree (layout: (string * string) list) (body: string -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-walk-" + Path.GetRandomFileName())

    Directory.CreateDirectory root |> ignore

    try
        for relative, content in layout do
            let full = Path.Combine(root, relative)
            Directory.CreateDirectory(Path.GetDirectoryName full) |> ignore
            File.WriteAllText(full, content)

        body root
    finally
        try
            Directory.Delete(root, true)
        with
        | :? IOException
        | :? System.UnauthorizedAccessException -> ()

[<Fact>]
let ``walk finds files at every depth`` () =
    withTree [ "Top.fs", ""; "src/Middle.fs", ""; "src/deep/Bottom.fs", "" ] (fun root ->
        let found = FileWalk.files "*.fs" root |> Seq.map Path.GetFileName |> Set.ofSeq
        Assert.Equal<Set<string>>(set [ "Top.fs"; "Middle.fs"; "Bottom.fs" ], found))

[<Fact>]
let ``walk prunes build output and package caches`` () =
    withTree
        [
            "Real.fs", ""
            "obj/Generated.fs", ""
            "bin/Debug/Copied.fs", ""
            "node_modules/pkg/Vendored.fs", ""
            "packages/Restored.fs", ""
        ]
        (fun root ->
            let found = FileWalk.files "*.fs" root |> Seq.map Path.GetFileName |> List.ofSeq
            Assert.Equal<string list>([ "Real.fs" ], found))

[<Fact>]
let ``a missing root yields nothing rather than throwing`` () =
    let missing =
        Path.Combine(Path.GetTempPath(), "fsref-walk-does-not-exist-" + Path.GetRandomFileName())

    Assert.Empty(FileWalk.files "*.fs" missing)

/// The hazard this walk exists for. `Directory.EnumerateFiles` with
/// `SearchOption.AllDirectories` abandons the whole enumeration when it meets
/// a directory it cannot open — and it fails part-way through, so files
/// already found are lost too. A dangling symlink under a build output
/// directory is exactly such a directory.
[<Fact>]
let ``an unreadable directory is skipped, not fatal`` () =
    withTree [ "Before.fs", ""; "z-after/After.fs", "" ] (fun root ->
        // a directory entry that cannot be opened: a symlink to nowhere.
        // Creating one needs privileges we may not have, so the test asserts
        // the guarantee only when the setup actually succeeded.
        let dangling = Path.Combine(root, "m-broken")

        let created =
            try
                Directory.CreateSymbolicLink(dangling, Path.Combine(root, "no-such-target"))
                |> ignore

                true
            with _ ->
                false

        let found = FileWalk.files "*.fs" root |> Seq.map Path.GetFileName |> Set.ofSeq

        // sorted between the two real files either way, so a walk that gives
        // up at the bad entry loses "After.fs"
        Assert.Equal<Set<string>>(set [ "Before.fs"; "After.fs" ], found)

        if not created then
            // not a failure, but say so: this run proved less than it looks
            eprintfn "note: could not create a dangling symlink; the skip path went untested")

/// Exercises the guard itself, on every platform: enumerating a path that is
/// a file throws `DirectoryNotFoundException`, which the walk must swallow.
/// The symlink test above reproduces the real-world trigger but can only do so
/// where this process may create symlinks.
[<Fact>]
let ``a file given as the root yields nothing rather than throwing`` () =
    withTree [ "Lonely.fs", "" ] (fun root ->
        let asRoot = Path.Combine(root, "Lonely.fs")
        Assert.Empty(FileWalk.files "*.fs" asRoot))

/// The api pass's script guard reads the walk's gaps: a directory it could
/// not search may hold a script calling the declaration about to be
/// reshaped, so "skipped" must be said, not swallowed.
[<Fact>]
let ``filesNoting names the directory it could not read`` () =
    withTree [ "Lonely.fs", "" ] (fun root ->
        let asRoot = Path.Combine(root, "Lonely.fs")
        let skipped = ResizeArray<string>()
        let found = FileWalk.filesNoting "*.fs" asRoot skipped.Add |> List.ofSeq
        Assert.Empty found
        Assert.Equal<string list>([ asRoot ], List.ofSeq skipped))

[<Fact>]
let ``filesNoting reports nothing skipped over a readable tree`` () =
    withTree [ "Top.fs", ""; "src/Middle.fs", ""; "obj/Pruned.fs", "" ] (fun root ->
        let skipped = ResizeArray<string>()

        let found =
            FileWalk.filesNoting "*.fs" root skipped.Add
            |> Seq.map Path.GetFileName
            |> Set.ofSeq

        Assert.Equal<Set<string>>(set [ "Top.fs"; "Middle.fs" ], found)
        // a pruned directory is left out on purpose, not skipped
        Assert.Empty skipped)

/// A linked worktree nested inside its own repository is another checkout
/// of the same code: walking it builds and fixes every project twice. A
/// worktree beside its repository (a workspace of checkouts) and a
/// submodule are code of their own and are walked.
[<Fact>]
let ``walk prunes a worktree nested in its own repository only`` () =
    withTree
        [
            "Repo/Real.fs", ""
            "Repo/.claude/worktrees/agent-1/Copy.fs", ""
            "Repo/.claude/worktrees/agent-2/Copy2.fs", ""
            "Repo/vendor/lib/.git", "gitdir: ../../.git/modules/lib\n"
            "Repo/vendor/lib/Sub.fs", ""
            "Repo-branch/Branch.fs", ""
        ]
        (fun root ->
            let repo = Path.Combine(root, "Repo").Replace('\\', '/')
            // absolute, as `git worktree add` writes it by default
            File.WriteAllText(
                Path.Combine(root, "Repo/.claude/worktrees/agent-1/.git"),
                $"gitdir: {repo}/.git/worktrees/agent-1\n"
            )
            // relative, as worktree.useRelativePaths writes it
            File.WriteAllText(
                Path.Combine(root, "Repo/.claude/worktrees/agent-2/.git"),
                "gitdir: ../../../.git/worktrees/agent-2\n"
            )

            File.WriteAllText(Path.Combine(root, "Repo-branch/.git"), $"gitdir: {repo}/.git/worktrees/Repo-branch\n")

            let found = FileWalk.files "*.fs" root |> Seq.map Path.GetFileName |> Set.ofSeq
            Assert.Equal<Set<string>>(set [ "Real.fs"; "Sub.fs"; "Branch.fs" ], found)

            // the worktree itself, walked as the root, is walked
            let inside =
                FileWalk.files "*.fs" (Path.Combine(root, "Repo", ".claude", "worktrees", "agent-1"))
                |> Seq.map Path.GetFileName
                |> List.ofSeq

            Assert.Equal<string list>([ "Copy.fs" ], inside))

let private sourcesOf (root: string) (files: string list) =
    System.Collections.Generic.HashSet<string>(
        files |> List.map (fun f -> Path.GetFullPath(Path.Combine(root, f))),
        System.StringComparer.OrdinalIgnoreCase
    )

/// The script probe typechecks only what may #load a project source: a
/// typecheck restores the script's nuget references, and an examples tree
/// of hundreds of scripts loading their own helpers stalled a run on it.
[<Fact>]
let ``a script loading only its own helpers cannot reach the project`` () =
    withTree
        [
            "src/Lib/Types.fs", ""
            "examples/_common/Cli.fs", ""
            "examples/Demo/Run.fsx", "#r \"nuget: X\"\n#load \"../_common/Cli.fs\"\n"
        ]
        (fun root ->
            let sources = sourcesOf root [ "src/Lib/Types.fs" ]
            Assert.False(Program.mayLoadAny sources (Path.Combine(root, "examples/Demo/Run.fsx"))))

[<Fact>]
let ``a script reaching a project source through another script can`` () =
    withTree
        [
            "src/Lib/Types.fs", ""
            "examples/_common/Load.fsx", "#load @\"../../src/Lib/Types.fs\"\n"
            "examples/Demo/Run.fsx", "  #load \"../_common/Load.fsx\" \"../_common/Load.fsx\"\n"
        ]
        (fun root ->
            let sources = sourcesOf root [ "src/Lib/Types.fs" ]
            Assert.True(Program.mayLoadAny sources (Path.Combine(root, "examples/Demo/Run.fsx"))))

/// `#I` can make a path resolve that the script's own directory does not:
/// what the text cannot resolve is typechecked, not ruled out.
[<Fact>]
let ``a load the text cannot resolve counts as reaching`` () =
    withTree
        [
            "src/Lib/Types.fs", ""
            "scripts/Run.fsx", "#I \"../src/Lib\"\n#load \"Types.fs\"\n"
        ]
        (fun root ->
            let sources = sourcesOf root [ "src/Lib/Types.fs" ]
            Assert.True(Program.mayLoadAny sources (Path.Combine(root, "scripts/Run.fsx"))))
