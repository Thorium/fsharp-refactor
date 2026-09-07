/// Parse trees for OTHER files of the project under analysis.
///
/// Cross-file migrations (internal-visibility FR0069/FR0093, taskify)
/// classify every use of a symbol; uses in other files need that file's
/// parse tree and source. The HOST decides whether that is possible:
/// the CLI configures a parser callback per compilation (it owns the
/// checker and the project options), the editor leaves it unconfigured —
/// rules then degrade to their file-local behavior.
///
/// Results are cached per (path, defines-fingerprint set by the host at
/// configure time); the host reconfigures per compilation, which resets
/// the cache — a different framework's defines produce a different tree.
module FSharp.Refactor.ProjectSources

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

/// Does the assembly OPEN its internals to friends? InternalsVisibleTo
/// makes "internal ⇒ every caller is in this project's symbol uses"
/// FALSE — the test assembly's call sites are invisible to the scan and
/// to the verification build — so every cross-file internal migration
/// must stand down. Fail-safe: an unreadable signature counts as having
/// friends.
let hasInternalsVisibleTo (projectCheck: FSharpCheckProjectResults) =
    try
        projectCheck.AssemblySignature.Attributes
        |> Seq.exists (fun a ->
            try
                a.AttributeType.DisplayName.Contains "InternalsVisibleTo"
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                true)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        true

let mutable private parser: (string -> (ParsedInput * ISourceText) option) option =
    None

let private cache =
    System.Collections.Concurrent.ConcurrentDictionary<string, (ParsedInput * ISourceText) option>()

/// Install the host's parser for the CURRENT compilation and reset the
/// cache. Pass None to uninstall (editor hosts never install one).
let configure (parse: (string -> (ParsedInput * ISourceText) option) option) =
    parser <- parse
    cache.Clear()

/// Drop cached trees without changing the parser. The host MUST call this
/// between fix-apply passes: a pass-1 edit to a sibling file would
/// otherwise leave pass-2 computing edits against the stale tree.
let invalidate () = cache.Clear()

/// Whether cross-file classification is possible in this host.
let available () = parser.IsSome

/// The parse tree and source of a project file, by full path.
let tryParse (path: string) : (ParsedInput * ISourceText) option =
    match parser with
    | None -> None
    | Some parse ->
        cache.GetOrAdd(
            System.IO.Path.GetFullPath(path).ToLowerInvariant(),
            fun _ ->
                try
                    parse path
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    None
        )

// ---- Call sites OUTSIDE this compilation: `#load`ing scripts ----
//
// A script that `#load`s a project source compiles it INTO the script, so
// it sees the `internal` declarations the cross-file migrations are
// allowed to reshape — and its calls are absent from the project's symbol
// tables AND from the verification build, which compiles the project and
// not the scripts beside it. Every migration that rewrites uses
// project-wide therefore has to ask the same two questions: which uses
// live outside, and which files are unreadable because a script that
// loads them does not typecheck.
//
// FR0090/FR0091 answered them inside the apply tool's api pass. This is
// the same answer, on the channel the analyzers can reach, so the FR0069
// and FR0093 migrations share one probe rather than growing a second.
// Editors install nothing and every migration keeps its file-local
// behaviour, exactly as with `parser` above.

let mutable private outsideUses: (FSharpSymbol -> FSharpSymbolUse[]) option = None

let mutable private unreadable: Set<string> = Set.empty

/// Install the host's out-of-compilation call sites for the CURRENT
/// compilation. `uses` answers for one symbol; `unreadableFiles` are
/// project sources `#load`ed by a script that does not typecheck, whose
/// declarations must not be reshaped at all. Pass None to uninstall.
let configureOutside (uses: (FSharpSymbol -> FSharpSymbolUse[]) option) (unreadableFiles: string seq) =
    outsideUses <- uses

    unreadable <-
        unreadableFiles
        |> Seq.map (fun p -> System.IO.Path.GetFullPath(p).ToLowerInvariant())
        |> Set.ofSeq

/// Seed a file's already-parsed tree, so a use in a file the host's
/// `parser` would read with the wrong options — a script, parsed by the
/// script host rather than the project's — is classified against the tree
/// that was actually typechecked.
let seed (path: string) (tree: ParsedInput) (source: ISourceText) =
    cache.[System.IO.Path.GetFullPath(path).ToLowerInvariant()] <- Some(tree, source)

/// Uses of this symbol from outside the compilation. Empty where no host
/// installed any, which is every editor and every run without
/// `--api-changes`.
let outsideUsesOf (symbol: FSharpSymbol) : FSharpSymbolUse[] =
    match outsideUses with
    | None -> [||]
    | Some uses ->
        try
            uses symbol
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            [||]

/// Is this file `#load`ed by a script we could not read? Nothing declared
/// in it may be reshaped: the script's calls are invisible and no build
/// check covers them. Fail-safe by construction — a host that installs
/// nothing reports nothing unreadable, and its migrations stay file-local.
let isUnreadable (path: string) =
    not unreadable.IsEmpty
    && unreadable.Contains(System.IO.Path.GetFullPath(path).ToLowerInvariant())
