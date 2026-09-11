/// Shared scope gate for rules whose fix changes a declaration's COMPILED
/// SHAPE rather than just the code inside it — `[<Struct>]` on a type,
/// `[<return: Struct>]` on an active pattern, field names on a union case.
///
/// Such a rewrite is invisible to F# pattern matching but not to everything
/// else: explicit invocations, first-class uses, reflection, and serializers
/// all see the change. Inside the assembly the compiler (and the apply
/// tool's verification build) catches any breakage; outside it, nothing
/// does. So these rules only fire on declarations that cannot be seen
/// outside this assembly — unless the caller explicitly opted into API
/// changes with `fsharp-refactor --api-changes`.
module FSharp.Refactor.Visibility

open System
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax

/// True when the apply tool was started with --api-changes, which opts into
/// rewrites that change the assembly's public surface. Never set in editors,
/// so the editor channel always sees the narrow, always-safe rules.
let apiChangesAllowed () =
    Environment.GetEnvironmentVariable "FSREF_API_CHANGES" = "1"

/// Does this modifier hide the declaration from outside the assembly?
let private isNonPublic (accessibility: SynAccess option) =
    match accessibility with
    | Some(SynAccess.Private _ | SynAccess.Internal _) -> true
    | _ -> false

/// Is the declaration invisible outside this assembly — declared
/// private/internal itself, or nested in a private/internal module or
/// namespace? `accessibilities` carries every modifier that hides the part
/// being rewritten; a rule passes the type's modifier, the union
/// representation's, or both, depending on what its edit changes.
let isConfined (path: SyntaxNode list) (accessibilities: SynAccess option list) =
    accessibilities |> List.exists isNonPublic
    || path
       |> List.exists (fun node ->
           match node with
           | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(accessibility = acc))) ->
               isNonPublic acc
           | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(accessibility = acc)) -> isNonPublic acc
           | _ -> false)

/// Is the declaration private — by its own modifier, or a private module
/// around it? NOTE: a signature file CAN mention a private declaration
let isPrivate (path: SyntaxNode list) (accessibilities: SynAccess option list) =
    let isPrivateModifier (accessibility: SynAccess option) =
        match accessibility with
        | Some(SynAccess.Private _) -> true
        | _ -> false

    accessibilities |> List.exists isPrivateModifier
    || path
       |> List.exists (fun node ->
           match node with
           | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(accessibility = acc))) ->
               isPrivateModifier acc
           | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(accessibility = acc)) -> isPrivateModifier acc
           | _ -> false)

/// Does a companion .fsi govern the file this declaration sits in?
///
/// A signature must agree with the implementation on the compiled shape —
/// `[<Struct>]` on the type, an active pattern's return type, a union case's
/// field names — for everything it declares, and it declares every internal
/// declaration as well as every public one. Only private escapes it.
/// FR0022, FR0069, FR0093 and FR0130 each found this separately on
/// fcs-fable, which carries 176 signature files; the gate they share now
/// asks once, so FR0011, FR0016 and FR0134 need not find it a fifth time.
let private signatureBound (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(range = r)) -> Some r.FileName
        | _ -> None)
    |> Option.exists Text.hasSignatureFile

/// Does this compilation produce an EXECUTABLE rather than a library?
///
/// It settles the question the scope gate is really asking. An
/// application has no external linker: nothing outside it can reference
/// its public declarations, so `public` there is F#'s default showing
/// through rather than an exported surface, and reshaping such a
/// declaration in place changes nothing anyone can see. A library cannot
/// say the same, which is why the gate exists at all.
///
/// `--target:exe` / `--target:winexe` is what MSBuild passes fsc for an
/// `Exe`/`WinExe` OutputType; fsc accepts the single-dash spelling too. A
/// library says `--target:library`, and an absent flag reads as a
/// library — the conservative answer, and what a host that supplies no
/// target flag at all gets.
/// Deliberately allocation-free: this runs against every compiler
/// argument, and a project carries hundreds of `-r:` references. The
/// obvious `option.Trim().TrimStart('-').ToLowerInvariant()` allocates
/// three strings per argument, and the caller memoizes this per
/// compilation precisely because even that adds up.
let private targetIsExecutable (otherOptions: string seq) =
    let isTarget (option: string) (value: string) =
        let option = option.AsSpan().Trim().TrimStart '-'
        option.Equals(value.AsSpan(), StringComparison.OrdinalIgnoreCase)

    otherOptions
    |> Seq.exists (fun option -> isTarget option "target:exe" || isTarget option "target:winexe")

/// Is a file a script rather than a compiled source?
let isScriptFile (path: string) =
    not (isNull path)
    && (path.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)
        || path.EndsWith(".fsscript", StringComparison.OrdinalIgnoreCase))

/// Is this whole compilation an assembly nothing outside can link
/// against? See `targetIsExecutable` for why that settles the scope
/// question.
///
/// A compilation containing a SCRIPT is not one assembly's worth of
/// source, and answers `false` here so that `isApplication` can decide it
/// file by file instead: `#load` is a walkable tree, but it is the
/// SCRIPT's tree, not the loaded file's assembly.
///
/// Scans every source file and every compiler argument, so callers hold
/// the answer per compilation rather than asking per rule per file.
let compilationIsLeaf (sourceFiles: string seq) (otherOptions: string seq) =
    not (sourceFiles |> Seq.exists isScriptFile) && targetIsExecutable otherOptions

/// Is the file being analyzed part of an assembly nothing outside can
/// link against? `compilationIsLeaf` is the compilation's own answer,
/// which the caller has memoized.
///
/// The script itself is the ultimate leaf: it links to nothing and
/// nothing links to it. A `#load`ed .fs is not — it belongs to whatever
/// project owns it, quite possibly a library, and a script reading it
/// says nothing about who else compiles it. So a script opens the gate,
/// and the sources it loads fall back to their compilation's answer,
/// which for a script compilation is no.
let isApplication (analyzedFile: string) (compilationIsLeaf: bool) =
    isScriptFile analyzedFile || compilationIsLeaf

/// The sources compiled AFTER this file in its compilation — the ones that
/// can see what it declares.
///
/// "Nothing outside the assembly can see it" is true of an executable, but
/// a later file of the SAME executable can, and it consumes a declaration
/// at the shape it has today. A rule whose in-place rewrite changes a
/// binding's type — FR0035's `|> Set.ofList` on a module value, FR0011's
/// struct return on an active pattern — checks its own file's uses; these
/// are the files it must ask about as well. Paths are compared in full,
/// ignoring case and separator spelling. A file the list does not carry
/// gets EVERY other source back: the host's options and the file do not
/// agree, and the safe reading is that any of them may follow it.
let laterSourceFiles (analyzedFile: string) (sourceFiles: string seq) : string list =
    let full (p: string) =
        try
            System.IO.Path.GetFullPath p
        with _ -> // fsharpanalyzer: ignore-line FR0055
            p

    let analyzed = full analyzedFile

    let same (p: string) =
        String.Equals(full p, analyzed, StringComparison.OrdinalIgnoreCase)

    let files = List.ofSeq sourceFiles

    if files |> List.exists same then
        files |> List.skipWhile (same >> not) |> List.skip 1
    else
        files

/// The gate itself: fire on contained declarations always, on any
/// declaration when the caller opted into API changes — except beside a
/// signature file, where only a private declaration can change shape
/// without the .fsi disagreeing.
let isInScope (allowApiChanges: bool) (path: SyntaxNode list) (accessibilities: SynAccess option list) =
    if signatureBound path then
        isPrivate path accessibilities
    else
        allowApiChanges || isConfined path accessibilities

/// The same gate for a rule that knows the DECLARATION'S NAME, which is
/// the only way to be sure beside a signature file.
///
/// "Private is the one visibility a signature file never mentions" is what
/// the plain gate assumes, and it is not true: `val private` is legal, and
/// Deedle's vendored FSharp.Data writes it. A private active pattern
/// declared in the .fsi took FR0011's `[<return: Struct>]` on the
/// implementation alone and stopped the project compiling. Rules that can
/// name what they are about should use this one; the plain gate remains
/// for the rules whose subject has no single name to look for.
let isInScopeNamed
    (allowApiChanges: bool)
    (path: SyntaxNode list)
    (accessibilities: SynAccess option list)
    (name: string)
    =
    if signatureBound path then
        isPrivate path accessibilities
        && not (
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(range = r)) -> Some r.FileName
                | _ -> None)
            |> Option.exists (fun file -> Text.signatureMentions file name)
        )
    else
        allowApiChanges || isConfined path accessibilities

/// `isInScopeNamed` for a declaration named by a dotted path: the LAST
/// segment is the name a signature writes. An empty path yields an empty
/// name, which `signatureMentions` reads as "not mentioned" - the same
/// answer the plain gate would have given.
let isInScopeNamedPath
    (allowApiChanges: bool)
    (path: SyntaxNode list)
    (accessibilities: SynAccess option list)
    (ids: Ident list)
    =
    isInScopeNamed
        allowApiChanges
        path
        accessibilities
        (ids |> List.tryLast |> Option.map (fun i -> i.idText) |> Option.defaultValue "")

/// The gate for a rule that edits the signature IN STEP (see
/// SignatureFile): the signature is no reason to stand down, because the
/// rule carries it along, so only the visibility question remains.
let isInScopeWithSignatureEdits
    (allowApiChanges: bool)
    (path: SyntaxNode list)
    (accessibilities: SynAccess option list)
    =
    allowApiChanges || isConfined path accessibilities

/// Which DEFINITIONS a scan may touch, for the rules that rewrite a
/// function's signature and every one of its call sites.
///
/// Private is the always-safe editor rule: a private module-level binding
/// has all its call sites in the one file, so the file's own typed results
/// enumerate them. Assembly is the wider project-wide variant, driven only
/// by the apply tool's --api-changes, where call sites are found through
/// the checked project's symbol uses — which is exactly why it stops at
/// effectively-internal declarations. A PUBLIC function's callers can sit
/// in a sibling project of the same repository, or in another repository
/// entirely; the scan cannot see them, so "every use covered" would pass
/// vacuously and the edit would break them (found the hard way: currying
/// SQLProvider.Common's public QueryFactory.createRelated broke
/// SQLProvider.Runtime).
///
/// Exported is the public remainder, and it is not a scan the analyzer
/// may open on its own: the host opens it only after READING every
/// compilation that can see this one — the sibling projects of the same
/// solution, typechecked and their uses indexed (see `Outside`) — so
/// that "every use covered" is once more a statement about every use.
[<RequireQualifiedAccess>]
type Scope =
    | Private
    | Assembly
    | Exported

/// Does a definition with this accessibility, at this path, belong to the
/// given scan?
let scopeMatches (scope: Scope) (path: SyntaxNode list) (accessibility: SynAccess option) =
    match scope with
    | Scope.Private ->
        match accessibility with
        | Some(SynAccess.Private _) -> true
        | _ -> false
    | Scope.Assembly ->
        // a directly-private binding is the single-file rule's territory;
        // this scan takes the rest of the assembly-confined ones
        (match accessibility with
         | Some(SynAccess.Private _) -> false
         | _ -> true)
        && isConfined path [ accessibility ]
    | Scope.Exported -> not (isConfined path [ accessibility ])

/// What the HOST knows about the compilations OUTSIDE the one being
/// analyzed, for the rules that rewrite a declaration and every one of its
/// call sites (FR0090/FR0091).
///
/// A declaration's callers are not all in its own project. A `#load`ing
/// script compiles the file into itself and sees its internals; a sibling
/// project of the same solution — the test project, typically — sees its
/// public declarations, and its internal ones too once InternalsVisibleTo
/// names it. None of those calls appear in the project's own symbol
/// tables, and the per-project verification build does not compile the
/// caller either (a solution's projects are processed in turn, not in
/// dependency order), so a definition reshaped behind such a caller's back
/// broke it with nothing to say so. The host that can read those
/// compilations says here what it read; a rule reshapes a declaration only
/// as far as the reading reaches, and withholds the rest.
type Outside =
    {
        /// Uses of a symbol in those other compilations, matched to the
        /// declaration rather than the name (a referenced assembly can
        /// carry the same full name). Their files must be renderable
        /// through the rule's file lookup, or the rule stands down.
        Uses: FSharpSymbol -> FSharpSymbolUse[]
        /// Has every compilation that can reach this assembly's PUBLIC
        /// declarations been read — every referencing project of the run
        /// an F# project that typechecked, no script `#r`ing the built
        /// assembly? False whenever the host cannot say: a run with no
        /// solution to enumerate, a referencing C# project, a sibling with
        /// errors. Public declarations then keep their shape. A thunk: the
        /// answer costs the host a reading of every referencing project,
        /// asked only once a candidate exists.
        PublicRead: unit -> bool
        /// Has the compilation of the assembly with this name — a friend the
        /// project names in InternalsVisibleTo — been read? Internal
        /// declarations of an assembly with friends are reshaped only when
        /// every friend answers yes.
        AssemblyRead: string -> bool
    }

/// The host that has read nothing beyond the compilation itself, which is
/// every editor host and a script target: internal declarations reshape
/// as before, public ones never.
let unknownOutside =
    { Uses = (fun _ -> [||])
      PublicRead = (fun () -> false)
      AssemblyRead = (fun _ -> false) }
