/// Recursive file enumeration that survives the directories real
/// repositories actually contain.
module FSharp.Refactor.Tool.FileWalk

open System.Collections.Generic
open System.IO

/// Directories never worth descending into: build output and package caches
/// hold generated copies of sources, and `.git` holds no sources at all.
/// Pruning during the walk rather than filtering afterwards also keeps us out
/// of trees that are far larger than the code we came for.
let private pruned =
    set [ "obj"; "bin"; "packages"; "node_modules"; ".git"; ".vs"; ".fable"; ".fsdocs" ]

let private isPruned (directory: string) =
    pruned.Contains((Path.GetFileName directory).ToLowerInvariant())

/// One directory's own files and subdirectories, or None if it cannot be
/// read. Materialized inside the guard: enumeration is lazy, so a `seq` that
/// escaped the `try` would throw later, at the caller, unguarded.
let private listing (pattern: string) (directory: string) =
    try
        Some(
            Directory.EnumerateFiles(directory, pattern) |> List.ofSeq,
            Directory.EnumerateDirectories directory |> List.ofSeq
        )
    with
    | :? IOException
    | :? System.UnauthorizedAccessException
    | :? System.Security.SecurityException -> None

/// Files matching `pattern` anywhere under `root`, and — through `skipped`,
/// called as the walk goes — every directory it had to leave out: one it
/// could not read, or a reparse point it does not follow. A caller for whom
/// a missed directory changes the answer (the api pass's script guard: a
/// script it never saw may call the declaration it is about to reshape)
/// reads the walk's gaps here; `files` is for the ones that only want what
/// is there.
///
/// `Directory.EnumerateFiles(_, _, SearchOption.AllDirectories)` gives up the
/// entire walk the moment it meets a directory it cannot open — a junction, a
/// dead symlink, a permission this process lacks — and it fails part-way
/// through iteration, so the caller loses the results already produced along
/// with the ones still to come. Repositories do contain such directories (a
/// Fable checkout has one under its Beam build output), and pointing this tool
/// at a repository is the ordinary way to use it. Here an unreadable directory
/// is skipped, not fatal.
/// Iterative rather than recursive, and deliberately so: a `seq` that
/// re-enters itself per directory allocates an enumerator per level and makes
/// every element pay O(depth) `MoveNext`s — which our own FR0058 flags.
/// One `seq`, one explicit stack, one enumerator.
let filesNoting (pattern: string) (root: string) (skipped: string -> unit) : string seq =
    seq {
        let pending = Stack<string>()
        pending.Push root

        while pending.Count > 0 do
            let directory = pending.Pop()

            match listing pattern directory with
            | None -> skipped directory
            | Some(here, subdirectories) ->
                yield! here

                for subdirectory in subdirectories do
                    // a junction or symlink pointing at an ancestor loops this
                    // walk forever — reparse points are not followed
                    let isReparse =
                        try
                            File.GetAttributes(subdirectory).HasFlag System.IO.FileAttributes.ReparsePoint
                        with
                        | :? System.IO.IOException
                        | :? System.UnauthorizedAccessException -> true

                    if isReparse then
                        skipped subdirectory
                    elif not (isPruned subdirectory) then
                        pending.Push subdirectory
    }

/// Files matching `pattern` anywhere under `root`; a directory the walk
/// cannot read is skipped without a word (see `filesNoting`).
let files (pattern: string) (root: string) : string seq = filesNoting pattern root ignore
