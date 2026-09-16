/// FR0155 (performance): `[<Sealed>]` on a class nothing inherits.
///
///     type internal Node(v: int) =        [<Sealed>]
///         member _.Value = v          →   type internal Node(v: int) =
///                                             member _.Value = v
///
/// The JIT treats a class it knows has no subclasses differently in two
/// places, both measured in benchmarks/PerfClaims (.NET 10, x64): a store
/// into a `Node[]` needs no covariance check, since the array cannot
/// really be a `Sub[]` (2.1 → 1.0 ns per element), and `:? Node` is one
/// method-table compare instead of a walk up the hierarchy (0.88 → 0.35
/// ns per object). A virtual call on a `Node`-typed receiver does NOT
/// move — dynamic PGO already guards and devirtualizes it — so calls are
/// not a reason to seal, and this rule only speaks where one of the two
/// sites that pay exists somewhere in the project: a `Node[]` / `Node
/// array` spelling, or a `:? Node` / `:?> Node` test.
///
/// Sealing is a promise about the whole program, so the guards are typed
/// and project-wide, and every unknown stands the rule down:
///
///   - the type is a plain class: not abstract, no abstract or default
///     member (a dispatch slot on a sealed class is an error), not a
///     record, union, struct, interface, exception, delegate or enum, not
///     already sealed;
///   - nothing in the project inherits it — every entity's base type is
///     read from the project's typed signature — and no object expression
///     `{ new Node() with ... }` builds on it, read at every typed use of
///     the class across the project's files;
///   - no `'T :> Node` constraint names it (with a sealed bound the
///     constraint collapses to `'T = Node`, which the compiler warns on);
///   - the class is internal or private (its own modifier or an enclosing
///     module's), or the shape-scope gate stands open — a public class of
///     a library is inherited by whoever links it, and an assembly with
///     InternalsVisibleTo opens its internal ones too;
///   - the project's typed results are in hand; an editor without them
///     says nothing.
///
/// The fix is the attribute on its own line above `type`, below any doc
/// comment; a definition in `and` position, or one whose attributes sit on
/// the `type` line itself, keeps the note without the edit.
module FSharp.Refactor.SealedClass

open System
open System.IO
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The type name's range, where the message is reported.
        Range: range
        TypeName: string
        /// What pays for the seal: "a Node[]", ":? Node", or both.
        Reason: string
        /// Where `[<Sealed>]` goes and the text to insert, when placement is safe.
        Fix: (range * string) option
    }

/// Every symbol use of the project, read once per project results: the
/// walk over every file's typed tree is the expensive part, and a file
/// with several candidate classes would otherwise pay it per class.
let private projectUsesCache =
    System.Runtime.CompilerServices.ConditionalWeakTable<FSharpCheckProjectResults, FSharpSymbolUse[]>()

let private projectUses (project: FSharpCheckProjectResults) =
    projectUsesCache.GetValue(
        project,
        fun p ->
            try
                p.GetAllUsesOfAllSymbols()
            with _ -> // no uses known: every candidate stands down below; fsharpanalyzer: ignore-line FR0055
                [||]
    )

/// Every entity of the project's own assembly, nested ones included.
let rec private allEntities (entities: FSharpEntity seq) : FSharpEntity seq =
    seq {
        for e in entities do
            yield e
            yield! allEntities e.NestedEntities
    }

let private attributeNamed (name: string) (attrs: SynAttributes) =
    attrs
    |> List.exists (fun l ->
        l.Attributes
        |> List.exists (fun a ->
            match List.tryLast a.TypeName.LongIdent with
            | Some id -> id.idText = name || id.idText = name + "Attribute"
            | None -> false))

/// The text of a line of any file of the project: this file's from the
/// source in hand (an editor's buffer may differ from disk), the others
/// from disk. An unreadable file reads as None, which stands the rule down.
let private lineReader (thisFile: string) (source: ISourceText) =
    let files =
        Collections.Generic.Dictionary<string, string[] option>(StringComparer.OrdinalIgnoreCase)

    fun (file: string) (line: int) ->
        if String.Equals(Path.GetFullPath file, Path.GetFullPath thisFile, StringComparison.OrdinalIgnoreCase) then
            if line >= 1 && line <= source.GetLineCount() then
                Some(source.GetLineString(line - 1))
            else
                None
        else
            let lines =
                match files.TryGetValue file with
                | true, l -> l
                | _ ->
                    let l =
                        try
                            Some(File.ReadAllLines file)
                        with _ -> // unreadable: unknown, and unknown stands the rule down; fsharpanalyzer: ignore-line FR0055
                            None

                    files.[file] <- l
                    l

            lines
            |> Option.bind (fun l ->
                if line >= 1 && line <= l.Length then
                    Some l.[line - 1]
                else
                    None)

/// A dotted qualifier before the use (`Some.Namespace.`) — the use's own
/// range may or may not cover it, so it is stripped either way.
let private stripQualifier (before: string) =
    Text.RegularExpressions.Regex.Replace(before, @"(\w|`)+(\.(\w|`)+)*\.\s*$", "")

/// What one typed use of the class says: a veto, a trigger, or nothing.
type private UseVerdict =
    | Veto
    | ArrayOf
    | TypeTest
    | Neutral

let private judgeUse (readLine: string -> int -> string option) (u: FSharpSymbolUse) : UseVerdict option =
    let r = u.Range

    match readLine r.FileName r.StartLine with
    | None -> None
    | Some lineText ->
        if
            r.StartColumn > lineText.Length
            || r.EndLine <> r.StartLine
            || r.EndColumn > lineText.Length
        then
            None
        else
            let before = stripQualifier (lineText.Substring(0, r.StartColumn).TrimEnd())
            let after = lineText.Substring(r.EndColumn).TrimStart()

            let previousNonBlank () =
                let mutable line = r.StartLine - 1
                let mutable found = None

                while found.IsNone && line >= 1 do
                    match readLine r.FileName line with
                    | Some t when t.Trim() <> "" -> found <- Some(t.TrimEnd())
                    | Some _ -> line <- line - 1
                    | None -> line <- 0

                found

            if before.EndsWith "new" then
                // `{ new Node() with ... }` — an object expression over the
                // class; a plain `new Node()` construction is fine
                let beforeNew = before.Substring(0, before.Length - 3).TrimEnd()

                if
                    beforeNew.EndsWith "{"
                    || (beforeNew = ""
                        && (previousNonBlank () |> Option.exists (fun t -> t.EndsWith "{")))
                then
                    Some Veto
                else
                    Some Neutral
            elif before.EndsWith "inherit" then
                Some Veto
            elif Text.RegularExpressions.Regex.IsMatch(before, @"['^]\w+\s*:>$") then
                Some Veto // 'T :> Node, ^T :> Node
            elif before.EndsWith ":?" || before.EndsWith ":?>" then
                Some TypeTest
            elif
                after.StartsWith "[]"
                || Text.RegularExpressions.Regex.IsMatch(after, @"^array\b")
            then
                Some ArrayOf
            else
                Some Neutral

/// Does any F# source in the repository, OUTSIDE this compilation, inherit
/// the class or build an object expression on it?
///
/// The project's typed results answer for the project alone. A test
/// project that references it — the ordinary shape for an executable,
/// whose public classes the shape-scope gate opens — may subclass a
/// service to stub it, or write `{ new Service() with ... }` for a test
/// double; a script that `#load`s the file may do the same, and the
/// project's symbol tables see none of it. So the repository's other
/// sources are read as text for `inherit Name` and `{ new Name`, the
/// conservative way: a match anywhere is a veto, whatever it turns out to
/// mean. Read once per repository root and kept for a short while — an
/// editor host lives long, and a subclass written a minute ago must count.
let private repositoryRoot (file: string) =
    let rec climb (dir: string) (depth: int) =
        if isNull dir || depth > 12 then
            None
        elif
            Directory.Exists(Path.Combine(dir, ".git"))
            || File.Exists(Path.Combine(dir, ".git"))
        then
            Some dir
        else
            climb (Path.GetDirectoryName dir) (depth + 1)

    climb (Path.GetDirectoryName(Path.GetFullPath file)) 0

let private repositorySourcesCache =
    Collections.Concurrent.ConcurrentDictionary<string, DateTime * (string * string)[]>(
        StringComparer.OrdinalIgnoreCase
    )

/// (path, text) of every .fs / .fsx under the root that is not an ignored
/// path (bin, obj, packages, paket-files, node_modules ...).
let private repositorySources (root: string) =
    let fresh () =
        try
            // C# too: a C# project of the repository may subclass a public
            // class of an executable it references (`class Sub : Node`)
            Seq.append
                (Directory.EnumerateFiles(root, "*.fs*", SearchOption.AllDirectories))
                (Directory.EnumerateFiles(root, "*.cs", SearchOption.AllDirectories))
            |> Seq.filter (fun p ->
                (p.EndsWith(".fs", StringComparison.OrdinalIgnoreCase)
                 || p.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)
                 || p.EndsWith(".cs", StringComparison.OrdinalIgnoreCase))
                && not (Configuration.isIgnoredPath p))
            |> Seq.choose (fun p ->
                try
                    Some(p, File.ReadAllText p)
                with _ -> // an unreadable file is skipped here and its project's typed results still answer; fsharpanalyzer: ignore-line FR0055
                    None)
            |> Array.ofSeq
        with _ -> // fsharpanalyzer: ignore-line FR0055
            [||]

    match repositorySourcesCache.TryGetValue root with
    | true, (at, sources) when DateTime.UtcNow - at < TimeSpan.FromSeconds 30. -> sources
    | _ ->
        let sources = fresh ()
        repositorySourcesCache.[root] <- (DateTime.UtcNow, sources)
        sources

let private extendedOutside (projectFiles: Set<string>) (thisFile: string) (name: string) =
    match repositoryRoot thisFile with
    | None -> false
    | Some root ->
        let escaped = Text.RegularExpressions.Regex.Escape name

        // F# `inherit Node`, or C# `class Sub : Node` / `class Sub<T> : Ns.Node`
        let inherits =
            Text.RegularExpressions.Regex(
                $@"(\binherit\s+(\w+\.)*{escaped}\b)|(\bclass\s+\w+\s*(<[^>]*>)?\s*:\s*(\w+\.)*{escaped}\b)"
            )

        let objectExpression =
            Text.RegularExpressions.Regex(
                $@"(\{{[^\n]*\bnew\s+(\w+\.)*{escaped}\b)|(^\s*new\s+(\w+\.)*{escaped}\b)",
                Text.RegularExpressions.RegexOptions.Multiline
            )

        repositorySources root
        |> Array.exists (fun (path, text) ->
            not (projectFiles.Contains(Path.GetFullPath(path).ToLowerInvariant()))
            && text.Contains name
            && (inherits.IsMatch text || objectExpression.IsMatch text))

/// The typed entity behind a type definition's name, when FCS has one.
let private entityAt (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange

    try
        match
            check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, source.GetLineString(r.EndLine - 1), [ id.idText ])
        with
        | Some u ->
            match u.Symbol with
            | :? FSharpEntity as e -> Some e
            | _ -> None
        | None -> None
    with _ -> // an unresolvable name is no candidate; fsharpanalyzer: ignore-line FR0055
        None

let private isPlainClass (e: FSharpEntity) =
    try
        e.IsClass
        && not e.IsAbstractClass
        && not e.IsInterface
        && not e.IsValueType
        && not e.IsFSharpRecord
        && not e.IsFSharpUnion
        && not e.IsFSharpExceptionDeclaration
        && not e.IsDelegate
        && not e.IsEnum
        && not e.IsFSharpAbbreviation
        && not e.IsArrayType
        && not e.IsMeasure
        && not (
            e.Attributes
            |> Seq.exists (fun a ->
                a.AttributeType.DisplayName = "SealedAttribute"
                || a.AttributeType.DisplayName = "Sealed")
        )
        && not (e.MembersFunctionsAndValues |> Seq.exists (fun m -> m.IsDispatchSlot))
    with _ -> // what cannot be read is not sealed; fsharpanalyzer: ignore-line FR0055
        false

let find
    (allowApiChanges: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (project: FSharpCheckProjectResults option)
    : Suggestion list =
    match project with
    | None -> []
    | Some project ->
        // a friend assembly may inherit an internal class as freely as this one
        if ProjectSources.hasInternalsVisibleTo project then
            []
        else
            let index = AstIndex.ofTree parseTree
            let readLine = lineReader parseTree.FileName source

            // the project's typed uses and base types, read only once a
            // syntactic candidate asks for them
            let uses = lazy (projectUses project)

            // this compilation's own files: the typed results answer for
            // those, the repository scan for everything else
            let projectFiles =
                lazy
                    (try
                        check.ProjectContext.ProjectOptions.SourceFiles
                        |> Array.map (fun f -> Path.GetFullPath(f).ToLowerInvariant())
                        |> Set.ofArray
                     with _ -> // fsharpanalyzer: ignore-line FR0055
                         Set.empty)

            let baseTypes =
                lazy
                    (try
                        allEntities project.AssemblySignature.Entities
                        |> Seq.choose (fun e ->
                            try
                                e.BaseType
                                |> Option.filter (fun t -> t.HasTypeDefinition)
                                |> Option.map (fun t -> t.TypeDefinition)
                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                None)
                        |> List.ofSeq
                     with _ -> // fsharpanalyzer: ignore-line FR0055
                         [])

            let same (entity: FSharpEntity) (other: FSharpEntity) =
                try
                    other.IsEffectivelySameAs entity
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false

            // the class's uses: the entity itself, and its constructors
            // (`new Node()` resolves to those)
            let ofClass (entity: FSharpEntity) (u: FSharpSymbolUse) =
                not u.IsFromDefinition
                && (match u.Symbol with
                    | :? FSharpEntity as e -> same entity e
                    | :? FSharpMemberOrFunctionOrValue as m ->
                        (try
                            m.IsConstructor && (m.DeclaringEntity |> Option.exists (same entity))
                         with _ -> // fsharpanalyzer: ignore-line FR0055
                             false)
                    | _ -> false)

            // the attribute on its own line above `type`, or above the
            // attributes already there; an `and` definition or attributes on
            // the type line itself keep the advice without the edit
            let placement (attrs: SynAttributes) (trivia: SynTypeDefnTrivia) (fileName: string) =
                match trivia.LeadingKeyword with
                | SynTypeDefnLeadingKeyword.Type kwRange ->
                    let anchor =
                        match attrs with
                        | [] -> Some kwRange
                        | first :: _ when first.Range.StartLine < kwRange.StartLine -> Some first.Range
                        | _ -> None

                    anchor
                    |> Option.filter (fun a ->
                        (source.GetLineString(a.StartLine - 1)).Substring(0, a.StartColumn).Trim() = "")
                    |> Option.map (fun a ->
                        let at = Position.mkPos a.StartLine 0
                        let indent = String.replicate a.StartColumn " "
                        Range.mkRange fileName at at, $"{indent}[<Sealed>]\n")
                | _ -> None

            /// One type definition's suggestion, when every guard passes.
            let candidate (path: SyntaxNode list) (decl: SynModuleDecl) (defn: SynTypeDefn) =
                let (SynTypeDefn(typeInfo = info; typeRepr = repr; trivia = defnTrivia)) = defn

                let (SynComponentInfo(attributes = attrs; longId = typeIds; accessibility = access)) =
                    info

                match repr, List.tryLast typeIds with
                | SynTypeDefnRepr.ObjectModel(
                    kind = SynTypeDefnKind.Class | SynTypeDefnKind.Unspecified; members = members),
                  Some nameId when
                    not (attributeNamed "Sealed" attrs)
                    && not (attributeNamed "AbstractClass" attrs)
                    && not (attributeNamed "Struct" attrs)
                    && not (attributeNamed "Interface" attrs)
                    && members
                       |> List.forall (fun m ->
                           match m with
                           | SynMemberDefn.AbstractSlot _ -> false
                           | _ -> true)
                    && Visibility.isInScopeNamed allowApiChanges path [ access ] nameId.idText
                    ->
                    match entityAt check source nameId with
                    | Some entity when isPlainClass entity && not (baseTypes.Value |> List.exists (same entity)) ->
                        let verdicts =
                            uses.Value |> Array.filter (ofClass entity) |> Array.map (judgeUse readLine)

                        let unknown = verdicts |> Array.exists Option.isNone
                        let vetoed = verdicts |> Array.exists (fun v -> v = Some Veto)
                        let arrays = verdicts |> Array.exists (fun v -> v = Some ArrayOf)
                        let tests = verdicts |> Array.exists (fun v -> v = Some TypeTest)
                        let name = nameId.idText

                        if
                            not unknown
                            && not vetoed
                            && (arrays || tests)
                            && not (extendedOutside projectFiles.Value parseTree.FileName name)
                        then
                            let reason =
                                match arrays, tests with
                                | true, true -> $"a {name}[] and a :? {name} test"
                                | true, false -> $"a {name}[]"
                                | _ -> $"a :? {name} test"

                            Some
                                {
                                    Range = nameId.idRange
                                    TypeName = name
                                    Reason = reason
                                    Fix = placement attrs defnTrivia decl.Range.FileName
                                }
                        else
                            None
                    | _ -> None
                | _ -> None

            index.Decls
            |> Seq.collect (fun (path, decl) ->
                match decl with
                | SynModuleDecl.Types(typeDefns = defns) -> defns |> List.choose (candidate path decl)
                | _ -> [])
            |> List.ofSeq
