/// Refactoring (idiom, FR0147): a namespace spelled out at every use is an
/// `open` the file forgot.
///
///     let t = System.Threading.Tasks.Task.FromResult 1
///     let d = System.Threading.Tasks.Task.Delay 10          open System.Threading.Tasks
///     let w = System.Threading.Tasks.Task.WhenAll [| t |]   let t = Task.FromResult 1 ...
///
/// NAMESPACES only, never types: the symbol at each qualified name says
/// which entity it is and which namespace that entity lives in, and only
/// the namespace part of the spelling is removed — `System.IO.File.Exists`
/// becomes `File.Exists` under `open System.IO`, never `Exists` under an
/// `open type`. Because the namespace comes from the entity, the longest
/// one wins by construction: `System.Threading.Tasks.Task` belongs to
/// System.Threading.Tasks, not to System, so no shorter open ever claims
/// it first.
///
/// A namespace is worth an open when the file spells it six times, or four
/// when it is three segments deep — `"FR0147": { "uses": 6, "deepUses": 4 }`
/// in fsharprefactor.json moves both. The fix inserts the `open` among the
/// file's top-level opens in alphabetical order within its family (`open
/// System.Collections.Generic` after `open System.Collections`, `open
/// System` above both), else after the last open, else under the module or
/// namespace header, and shortens every use. A namespace the file already opens only
/// gets its uses shortened.
///
/// Opening a namespace can shadow a name (`open System.Collections.Generic`
/// brings a `List` type beside the F# List module), so the fix is offered
/// only when it cannot: every name the namespace exports is checked against
/// what this file defines and against every name it already uses
/// unqualified for something else, and a clash leaves a note with no fix —
/// the same answer in the tool and in an editor, no compile needed. The
/// file's own namespace, and namespaces a `[<RequireQualified
/// Access>]`-style convention keeps long (Microsoft.FSharp.*), are left
/// alone.
module FSharp.Refactor.QualifiedNames

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The first use, where the hint anchors.
        Range: range
        /// The namespace to open.
        Namespace: string
        /// How many uses the file spells out.
        Uses: int
        /// (range, original, replacement): the `open` insertion (empty
        /// when the file already opens the namespace) and every prefix
        /// removal.
        Edits: (range * string * string) list
        /// Why the open is NOT offered: the clashing names and where they
        /// come from, or the place the open cannot take. None when the
        /// edits are offered.
        Reason: string option
    }

/// The namespace an entity lives in, walking out of nested modules.
let rec private namespaceOf (entity: FSharpEntity) =
    try
        match entity.Namespace with
        | Some ns when ns <> "" -> Some ns
        | _ ->
            match entity.DeclaringEntity with
            | Some parent -> namespaceOf parent
            | None -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// The namespace a symbol belongs to: its own for an entity, its
/// declaring entity's for a member.
let private symbolNamespace (symbol: FSharpSymbol) =
    match symbol with
    | :? FSharpEntity as e -> namespaceOf e
    | :? FSharpMemberOrFunctionOrValue as v ->
        (try
            v.DeclaringEntity |> Option.bind namespaceOf
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             None)
    | :? FSharpUnionCase as c ->
        (try
            namespaceOf c.DeclaringEntity
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             None)
    | :? FSharpField as f ->
        (try
            f.DeclaringEntity |> Option.bind namespaceOf
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             None)
    | _ -> None

/// Where an entity lives: its namespace and the chain of entities from the
/// namespace down to it — `Toro`, [Toro] for the module `Toro` declared
/// inside `namespace Toro`.
let rec private located (entity: FSharpEntity) : (string * string list) option =
    try
        match entity.DeclaringEntity with
        | Some parent when not parent.IsNamespace ->
            located parent
            |> Option.map (fun (ns, chain) -> ns, chain @ [ entity.DisplayName ])
        | _ ->
            match entity.Namespace with
            | Some ns when ns <> "" -> Some(ns, [ entity.DisplayName ])
            | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// The namespace a symbol belongs to and the full spelling that reaches it
/// from that namespace: `System.Threading.Tasks`, [System; Threading;
/// Tasks; Task; FromResult]. A qualified name in source shortens only when
/// it IS this spelling — a name-by-name prefix match mistook toro's
/// `Toro.noGrad` (the module Toro of namespace Toro, already open) for a
/// namespace-qualified value and left a bare `noGrad`.
let private symbolPath (symbol: FSharpSymbol) =
    let ofEntity (e: FSharpEntity) = located e

    let path =
        match symbol with
        | :? FSharpEntity as e -> ofEntity e
        | :? FSharpMemberOrFunctionOrValue as v ->
            (try
                v.DeclaringEntity
                |> Option.bind ofEntity
                |> Option.map (fun (ns, chain) ->
                    // a constructor is spelled as its type
                    if v.IsConstructor then
                        ns, chain
                    else
                        ns, chain @ [ v.DisplayName ])
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 None)
        | :? FSharpUnionCase as c ->
            (try
                ofEntity c.DeclaringEntity
                |> Option.map (fun (ns, chain) -> ns, chain @ [ c.DisplayName ])
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 None)
        | :? FSharpField as f ->
            (try
                f.DeclaringEntity
                |> Option.bind ofEntity
                |> Option.map (fun (ns, chain) -> ns, chain @ [ f.DisplayName ])
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 None)
        | _ -> None

    path |> Option.map (fun (ns, chain) -> ns, List.ofArray (ns.Split '.') @ chain)

/// The referenced assemblies of the project a file belongs to, held for the
/// project currently being swept: they cannot change while one project is
/// analysed, so asking FCS again for every file is 129 redundant round-trips
/// out of 130.
///
/// It does NOT make a sweep faster, and the reason is worth keeping: a
/// stopwatch around the call reports ~28 ms per file, but that is a thread
/// BLOCKING on FCS's internal locks, not work being done — 20 threads against
/// a service that serialises them (a sweep gets 1.68x on 20 cores). Remove the
/// calls and the same wait reappears elsewhere; measured before and after,
/// three runs each, the rule's time did not move. Kept anyway because the
/// redundancy is real and the single-file IDE path has no contention to hide
/// it. Do not read a per-thread stopwatch here as a measure of work.
///
/// One slot rather than a dictionary: a sweep moves project by project, so a
/// slot hits on every file after the first, while keeping every project's list
/// alive would pin its assembly signatures for the rest of a run that can last
/// hours. Interleaved projects merely miss, never answer wrongly. The pair is
/// swapped as one reference so a reader cannot see a new key beside an old
/// list.
let mutable private cachedAssemblies: (string * FSharpAssembly list) option = None

let private referencedAssemblies (check: FSharpCheckFileResults) =
    let read () =
        try
            check.ProjectContext.GetReferencedAssemblies()
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            []

    let key =
        try
            check.ProjectContext.ProjectOptions.ProjectFileName
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            ""

    if key = "" then
        read ()
    else
        match cachedAssemblies with
        | Some(cachedKey, assemblies) when cachedKey = key -> assemblies
        | _ ->
            let assemblies = read ()
            cachedAssemblies <- Some(key, assemblies)
            assemblies

/// Namespaces conventionally spelled out. What an open may do to the code
/// already in the file is a mechanism's property, not a namespace's, and
/// `clashes` below checks the mechanism against every namespace alike.
let private keptLong (ns: string) =
    ns.StartsWith "Microsoft.FSharp" || ns.StartsWith "FSharp.Core"

/// The top-level names a namespace exports, per namespace and reference set.
/// Worth caching — a sweep asks the same question in every file — but NOT the
/// rule's bottleneck, whatever its cost looks like: enumerating every
/// referenced assembly's entities and bucketing all 502 scopes of this
/// project's reference set measures 143 ms once, against ~7 s of FR0147 in the
/// same sweep. The time is in the per-file work, so measure there before
/// rewriting anything here.
let private exportedNamesCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, Map<string, bool>>()

/// `minUses`: spellings of a namespace before an open is worth it; `minDeepUses`:
/// the same for a namespace three or more segments deep.
let find
    (minUses: int)
    (minDeepUses: int)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    if OptionModule.hasErrors check || parseTree.IsSigFile then
        []
    else
        let index = AstIndex.ofTree parseTree

        // every top-level module or namespace of the file, each with its own
        // opens and its own place for a new one: an open in the first
        // `namespace A` block covers nothing in the `namespace B` below it
        let blocks =
            match parseTree with
            | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
                modules
                |> List.map (fun (SynModuleOrNamespace(longId = ids; kind = kind; decls = decls; range = r)) ->
                    let opens =
                        decls
                        |> List.choose (fun d ->
                            match d with
                            | SynModuleDecl.Open(SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = oids)),
                                                 orange) -> Some(identText oids, orange)
                            | _ -> None)

                    let own = identText ids

                    // every prefix of the own name is "own" too: a file in
                    // Company.Product.Data need not open Company.Product
                    let ownPrefixes = [ for k in 1 .. ids.Length -> ids |> List.take k |> identText ]

                    // where an open goes when the file has none: under the
                    // module or namespace line — and in a file without one
                    // (the implicit module of a last file, a script) before
                    // the first declaration, since the "header" range there
                    // is the first declaration's own line
                    let insertAt =
                        match kind with
                        | SynModuleOrNamespaceKind.AnonModule ->
                            decls |> List.tryHead |> Option.map (fun d -> r.FileName, d.Range.StartLine)
                        // under the `module`/`namespace` line itself, which doc
                        // comments and attributes above it push down the range
                        | _ when not ids.IsEmpty -> Some(r.FileName, (List.last ids).idRange.EndLine + 1)
                        | _ -> Some(r.FileName, r.StartLine + 1)

                    {| Range = r
                       InsertAt = insertAt
                       Opened = opens
                       Own = Set.ofList (own :: ownPrefixes) |})
            | _ -> []

        let blockOf (r: range) =
            blocks
            |> List.tryFindIndex (fun b -> Range.rangeContainsRange b.Range r)
            |> Option.defaultValue 0

        let openedSet =
            blocks |> List.collect (fun b -> b.Opened |> List.map fst) |> Set.ofList

        // every open of the file at any level: the other namespaces and
        // modules whose names a shortened spelling would compete with
        let allOpened =
            index.Decls
            |> Array.choose (fun (_, d) ->
                match d with
                | SynModuleDecl.Open(SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = oids)), _) ->
                    Some(identText oids)
                | _ -> None)
            |> Set.ofArray

        // every qualified spelling in expressions and types
        let spellings =
            [ for _, e in index.Exprs do
                  match e with
                  | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 -> yield ids
                  | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when ids.Length >= 2 ->
                      yield ids
                  // an assignment target is a spelling too: fsharp.formatting's
                  // `System.Diagnostics.Trace.AutoFlush <- true` kept its prefix
                  // while the reads beside it lost theirs
                  | SynExpr.LongIdentSet(SynLongIdent(id = ids), _, _) when ids.Length >= 2 -> yield ids
                  | _ -> ()
              for _, t in index.Types do
                  match t with
                  | SynType.LongIdent(SynLongIdent(id = ids)) when ids.Length >= 2 -> yield ids
                  | _ -> () ]
            |> List.distinctBy (fun ids -> (List.head ids).idRange)

        // early-out before the typed check, which is the expensive part: a
        // namespace can only qualify when its first segment recurs at least
        // as often as the smaller threshold, so a spelling whose first
        // segment is rarer than that resolves to nothing worth opening
        let firstSegmentCounts =
            spellings |> List.countBy (fun ids -> (List.head ids).idText) |> Map.ofList

        // a namespace the file already opens shortens at any count, so its
        // family always resolves
        let openedFamilies = openedSet |> Set.map (fun name -> name.Split('.').[0])

        let worthResolving =
            spellings
            |> List.filter (fun ids ->
                let first = (List.head ids).idText

                firstSegmentCounts.[first] >= min minUses minDeepUses
                || openedFamilies.Contains first)

        // the namespace of each spelling, when the spelling starts with it
        // the same spelling resolves the same way everywhere in the file:
        // one typed lookup per distinct spelling, not per occurrence
        let namespaceOfSpelling =
            System.Collections.Generic.Dictionary<string, (string * string list) option>()

        let resolveSpelling (ids: Ident list) (names: string list) =
            let key = String.concat "." names

            match namespaceOfSpelling.TryGetValue key with
            | true, ns -> ns
            | _ ->
                let last = List.last ids
                let r = last.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                let ns =
                    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, names) with
                    | Some symbolUse -> symbolPath symbolUse.Symbol
                    | None -> None

                namespaceOfSpelling.[key] <- ns
                ns

        let resolved =
            worthResolving
            |> List.choose (fun ids ->
                let names = ids |> List.map (fun i -> i.idText)

                match resolveSpelling ids names with
                | Some(ns, fullPath) when
                    not (keptLong ns)
                    && not (blocks.[blockOf (List.head ids).idRange].Own.Contains ns)
                    ->
                    let segments = ns.Split '.'

                    // the spelling must be the symbol's own full path — the
                    // namespace, then the entities down to the member — so
                    // that what follows the namespace still reaches it
                    if names = fullPath && segments.Length < ids.Length then
                        let first = List.head ids
                        let afterNamespace = ids.[segments.Length]

                        let prefixRange =
                            Range.mkRange first.idRange.FileName first.idRange.Start afterNamespace.idRange.Start

                        Some(ns, prefixRange)
                    else
                        None
                | _ -> None)

        // where the open goes: after the last open that shares the
        // namespace's first segment (System.* beside the other System.*
        // opens), else after the last open, else after the header line
        // the `#if` region a line sits in: the line number of the innermost
        // open `#if` (or `#else`, a different condition) above it, 0 when
        // none. An open and the uses it serves must share a region: the F#
        // compiler's TypedTreeOps.ExprOps.fs had its last open inside
        // `#if !NO_TYPEPROVIDERS`, the inserted `open FSComp` followed it
        // there while the uses were unconditional, and the Proto build no
        // longer compiled. Uses that are all under one condition get their
        // open under the same one — a namespace needed only there must not
        // become a dependency of every build
        let conditionalRegion (line: int) =
            let stack = System.Collections.Generic.Stack<int>()

            for l in 0 .. min (line - 2) (source.GetLineCount() - 1) do
                let text = source.GetLineString(l).TrimStart()

                if text.StartsWith "#if" then
                    stack.Push(l + 1)
                elif text.StartsWith "#else" then
                    if stack.Count > 0 then
                        stack.Pop() |> ignore

                    stack.Push(l + 1)
                elif text.StartsWith "#endif" then
                    if stack.Count > 0 then
                        stack.Pop() |> ignore

            if stack.Count = 0 then 0 else stack.Peek()

        let insertionPoint (block: int) (ns: string) (firstUseLine: int) (region: int) =
            let family = ns.Split('.').[0]

            // an open scopes from its own line down: one below the first
            // use is no neighbour to land beside, nor a last open to follow;
            // and only an open of the uses' own region is an anchor
            let opened =
                blocks.[block].Opened
                |> List.filter (fun (_, r) -> r.EndLine < firstUseLine && conditionalRegion r.StartLine = region)

            let familyOpens =
                opened
                |> List.filter (fun (name, _) -> name = family || name.StartsWith(family + "."))

            // alphabetical within the family, which is also depth order:
            // `open System.Collections.Generic` follows `open
            // System.Collections`, and `open System` goes above both
            let ordinal (name: string) = System.String.CompareOrdinal(name, ns)

            let after =
                familyOpens |> List.filter (fun (name, _) -> ordinal name < 0) |> List.tryLast

            let before = familyOpens |> List.tryFind (fun (name, _) -> ordinal name > 0)

            match after, before, List.tryLast opened, blocks.[block].InsertAt with
            | Some(_, r), _, _, _ ->
                let at = Position.mkPos (r.EndLine + 1) 0
                Some(Range.mkRange r.FileName at at, String.replicate r.StartColumn " ")
            | None, Some(_, r), _, _ ->
                let at = Position.mkPos r.StartLine 0
                Some(Range.mkRange r.FileName at at, String.replicate r.StartColumn " ")
            | None, None, Some(_, lastOpen), _ ->
                let at = Position.mkPos (lastOpen.EndLine + 1) 0
                Some(Range.mkRange lastOpen.FileName at at, String.replicate lastOpen.StartColumn " ")
            // no open in the uses' `#if` region: right below its `#if` line,
            // at the indentation of the first line there
            | None, None, None, _ when region > 0 ->
                let indent =
                    seq { region .. source.GetLineCount() - 1 }
                    |> Seq.map source.GetLineString
                    |> Seq.tryFind (fun l -> not (System.String.IsNullOrWhiteSpace l))
                    |> Option.map (fun l -> l.Substring(0, l.Length - l.TrimStart().Length))
                    |> Option.defaultValue ""

                let at = Position.mkPos (region + 1) 0
                let fileName = (List.head (List.head spellings)).idRange.FileName
                Some(Range.mkRange fileName at at, indent)
            | None, None, None, Some(fileName, line) ->
                let at = Position.mkPos line 0
                Some(Range.mkRange fileName at at, "")
            | None, None, None, None -> None

        // ---- clash detection: the fix must be right without a compile ----
        //
        // an open brings every top-level name of the namespace into scope.
        // A name the file already uses UNQUALIFIED for something else — its
        // own type, another library's type, a function — would then be
        // ambiguous or silently re-bound. Such a namespace stays a note.

        // the entities name lookups see: the referenced assemblies' (cached
        // for the run — enumerating them is the expensive step, and a sweep
        // asks the same question in every file) and this project's own, up
        // to this file (FsAutoComplete's Utils.Utils.Expect beside
        // Expecto.Expect: that clash lived in the project itself)
        let assemblies = referencedAssemblies check

        let assemblyKey =
            assemblies |> List.map (fun a -> a.SimpleName) |> String.concat ";"

        let projectEntities =
            lazy
                (try
                    check.PartialAssemblySignature.Entities |> List.ofSeq
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     [])

        let rec flatten (e: FSharpEntity) : FSharpEntity list =
            try
                if e.IsNamespace then
                    e.NestedEntities |> Seq.collect flatten |> List.ofSeq
                else
                    [ e ]
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                [ e ]

        let autoOpen (e: FSharpEntity) =
            try
                e.Attributes
                |> Seq.exists (fun a -> a.AttributeType.DisplayName = "AutoOpenAttribute")
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false

        // the names a MODULE brings when opened: its nested types and
        // modules, its values, and the case names of its active patterns
        // (`|Ident|_|` reaches expressions as `Ident`)
        let contentsOf (e: FSharpEntity) =
            try
                let entities =
                    e.NestedEntities
                    |> Seq.map (fun n -> n.DisplayName, n.IsFSharpModule)
                    |> List.ofSeq

                let values =
                    e.MembersFunctionsAndValues
                    |> Seq.collect (fun v ->
                        // an active pattern displays as `(|Ident|_|)`
                        let name = v.DisplayName.TrimStart('(').TrimEnd ')'

                        if name.StartsWith '|' then
                            name.Split '|' |> Array.filter (fun p -> p <> "" && p <> "_") |> Array.toList
                        else
                            [ name ])
                    |> Seq.map (fun name -> name, false)
                    |> List.ofSeq

                entities @ values
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                []

        // a union type in an opened namespace brings its case names
        let casesOf (e: FSharpEntity) =
            try
                if e.IsFSharpUnion then
                    e.UnionCases |> Seq.map (fun c -> c.DisplayName, false) |> List.ofSeq
                else
                    []
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                []

        // what an `open X` brings into scope, as name → "is a module": the
        // types and modules of namespace X, the contents of its [<AutoOpen>]
        // modules, and — X being a module itself — its nested entities. A
        // name that is both a type and a module (List) counts as a module
        let broughtBy (openedName: string) (entities: FSharpEntity seq) =
            entities
            |> Seq.collect flatten
            |> Seq.collect (fun e ->
                try
                    if e.IsFSharpModule && e.TryFullName = Some openedName then
                        contentsOf e
                    elif e.Namespace = Some openedName then
                        (e.DisplayName, e.IsFSharpModule) :: casesOf e
                        @ (if e.IsFSharpModule && autoOpen e then contentsOf e else [])
                    else
                        // a namespace BENEATH X is a name `open X` brings too:
                        // `open System.Diagnostics` makes `Metrics.Meter` reach
                        // System.Diagnostics.Metrics.Meter, and a module named
                        // Metrics elsewhere (the F# compiler's
                        // FSharp.Compiler.Diagnostics.Metrics) loses to it
                        match e.Namespace with
                        | Some n when n.StartsWith(openedName + ".") ->
                            let rest = n.Substring(openedName.Length + 1)

                            let child =
                                match rest.IndexOf '.' with
                                | -1 -> rest
                                | i -> rest.Substring(0, i)

                            [ child, false ]
                        | _ -> []
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    [])
            |> Seq.fold
                (fun (acc: Map<string, bool>) (name, isModule) ->
                    Map.add name (isModule || (Map.tryFind name acc |> Option.defaultValue false)) acc)
                Map.empty

        let scopeNames (openedName: string) : Map<string, bool> =
            let fromAssemblies =
                exportedNamesCache.GetOrAdd(
                    $"{openedName}|{assemblyKey}",
                    fun _ ->
                        try
                            assemblies
                            |> Seq.collect (fun a ->
                                try
                                    a.Contents.Entities |> List.ofSeq
                                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                    [])
                            |> broughtBy openedName
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            Map.empty
                )

            broughtBy openedName projectEntities.Value
            |> Map.fold (fun acc name isModule -> Map.add name isModule acc) fromAssemblies

        // a MODULE spelled exactly like the namespace — Nu's
        // `[<RequireQualifiedAccess>] module OpenGL` beside `namespace
        // Nu.OpenGL` — is what `open Nu.OpenGL` would resolve to, and a
        // qualified-access module refuses the open outright; the namespace
        // then stays spelled out
        // by display name: a module beside a namespace of its name compiles
        // with a `Module` suffix, which TryFullName reports and no source
        // spells
        let moduleFullName (e: FSharpEntity) =
            match e.Namespace with
            | Some p when p <> "" -> $"{p}.{e.DisplayName}"
            | _ -> e.DisplayName

        let moduleNamed (ns: string) =
            let key = $"module:{ns}|{assemblyKey}"

            let fromAssemblies =
                exportedNamesCache.GetOrAdd(
                    key,
                    fun _ ->
                        try
                            assemblies
                            |> Seq.collect (fun a ->
                                try
                                    a.Contents.Entities |> List.ofSeq
                                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                    [])
                            |> Seq.collect flatten
                            |> Seq.filter (fun e -> e.IsFSharpModule && moduleFullName e = ns)
                            |> Seq.map (fun e -> e.DisplayName, true)
                            |> Map.ofSeq
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            Map.empty
                )

            not fromAssemblies.IsEmpty
            || projectEntities.Value
               |> List.collect flatten
               |> List.exists (fun e ->
                   try
                       e.IsFSharpModule && e.TryFullName = Some ns
                   with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                       false)

        let exportedNames (ns: string) =
            scopeNames ns |> Map.toSeq |> Seq.map fst |> Set.ofSeq

        let exportedModules (ns: string) =
            scopeNames ns
            |> Map.filter (fun _ isModule -> isModule)
            |> Map.toSeq
            |> Seq.map fst
            |> Set.ofSeq

        // names this file defines at any level: types, modules, values
        let definedHere =
            [ for _, decl in index.Decls do
                  match decl with
                  | SynModuleDecl.Types(typeDefns = defns) ->
                      for SynTypeDefn(typeInfo = SynComponentInfo(longId = ids)) in defns do
                          yield (List.last ids).idText
                  | SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = ids)) ->
                      yield (List.last ids).idText
                  | SynModuleDecl.Let(bindings = bindings) ->
                      for SynBinding(headPat = p) in bindings do
                          yield! patBoundNames p
                  | _ -> () ]
            |> Set.ofList

        // names the file uses unqualified, with what they resolve to: a type
        // annotation, a construction, or the head of a dotted expression
        let unqualifiedUses =
            [ for _, e in index.Exprs do
                  match e with
                  | SynExpr.LongIdent(longDotId = SynLongIdent(id = head :: _ :: _)) -> yield head
                  // a bare construction or call: fsharplint's `Byte('x'B)` is
                  // its own union case until `open System` makes it the
                  // System.Byte constructor
                  | SynExpr.App(funcExpr = SynExpr.Ident head) when
                      head.idText.Length > 0 && System.Char.IsUpper head.idText.[0]
                      ->
                      yield head
                  | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = [ id ]))) -> yield id
                  | SynExpr.New(targetType = SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = [ id ])))) ->
                      yield id
                  | _ -> ()
              for _, t in index.Types do
                  match t with
                  | SynType.LongIdent(SynLongIdent(id = [ id ])) -> yield id
                  | _ -> () ]

        // the methods the file calls with a parenthesised tuple — `x.M (a, b)`
        // — by name. F# hands that tuple over as TWO arguments the moment a
        // two-parameter overload of M is in scope, and an open can bring one:
        // SQLProvider's `seen.Contains (entity, ct)` was the tuple argument
        // of `List<T>.Contains` until `open System.Linq` arrived, then became
        // `entity` against `Enumerable.Contains(value, comparer)` and stopped
        // compiling sixty lines from the edit. The same happens under any
        // namespace that exports an extension member of the name: the check
        // is on the mechanism, not on System.Linq
        let tupledMethodCalls =
            lazy
                (set
                    [ for _, e in index.Exprs do
                          match e with
                          | SynExpr.App(
                              funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                              argExpr = SynExpr.Paren(expr = SynExpr.Tuple(isStruct = false))) when ids.Length >= 2 ->
                              yield (List.last ids).idText
                          | SynExpr.App(
                              funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = ids))
                              argExpr = SynExpr.Paren(expr = SynExpr.Tuple(isStruct = false))) ->
                              yield (List.last ids).idText
                          | _ -> () ])

        // the extension members a namespace exports, by name: F# type
        // extensions and `[<Extension>]` functions in its modules, C#
        // extension methods in its static classes. Cached like the names —
        // the same enumeration, asked once per namespace and reference set
        let extensionMembersIn (ns: string) : Set<string> =
            let isExtension (m: FSharpMemberOrFunctionOrValue) =
                try
                    m.IsExtensionMember
                    || m.Attributes
                       |> Seq.exists (fun a -> a.AttributeType.DisplayName = "ExtensionAttribute")
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    false

            // an `[<AutoOpen>]` module of the namespace opens with it, and an
            // F#-style extension (`type List<'T> with member xs.Contains(a,
            // b)`) lives in exactly such a module - reproduced: the identical
            // FS0001 through an AutoOpen module
            let rec withAutoOpened (e: FSharpEntity) =
                seq {
                    yield e

                    let nested =
                        try
                            if e.IsFSharpModule && autoOpen e then
                                e.NestedEntities |> List.ofSeq
                            else
                                []
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            []

                    yield! nested |> Seq.collect withAutoOpened
                }

            let ofEntities (entities: FSharpEntity seq) =
                entities
                |> Seq.collect flatten
                |> Seq.filter (fun e ->
                    try
                        e.Namespace = Some ns
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        false)
                |> Seq.collect withAutoOpened
                |> Seq.collect (fun e ->
                    try
                        e.MembersFunctionsAndValues
                        |> Seq.filter isExtension
                        |> Seq.map (fun m -> m.DisplayName)
                        |> List.ofSeq
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        [])

            let fromAssemblies =
                exportedNamesCache.GetOrAdd(
                    $"extensions:{ns}|{assemblyKey}",
                    fun _ ->
                        try
                            assemblies
                            |> Seq.collect (fun a ->
                                try
                                    a.Contents.Entities |> List.ofSeq
                                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                    [])
                            |> ofEntities
                            |> Seq.map (fun name -> name, true)
                            |> Map.ofSeq
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            Map.empty
                )

            fromAssemblies
            |> Map.toSeq
            |> Seq.map fst
            |> Set.ofSeq
            |> Set.union (ofEntities projectEntities.Value |> Set.ofSeq)

        // would the open re-bind this unqualified name? A head that resolves
        // to an F# MODULE merges with a TYPE of that name from the namespace
        // — `String.concat` keeps meaning the F# String module under `open
        // System`, `List.map` the List module under `open
        // System.Collections.Generic` — but a MODULE of that name from the
        // namespace would shadow it (Expecto.Expect over Utils.Utils.Expect)
        // ... and if so, where the name resolves today: the namespace, or
        // "" for a symbol with none
        let resolvesOutsideTo (ns: string) (id: Ident) : string option =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpEntity as e when
                    (try
                        e.IsFSharpModule
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                    && not ((exportedModules ns).Contains id.idText)
                    ->
                    None
                | symbol ->
                    match symbolNamespace symbol with
                    | Some other when other = ns -> None
                    | Some other -> Some other
                    | None -> Some ""
            | None -> None

        // FSharp.Core is open in every file before any `open` of its own, and
        // a later open shadows it — except that a type ABBREVIATION does not
        // win against FSharp.Core's real type of the same name: the F#
        // compiler's `Tagged.Map<_, _>` (an abbreviation of the
        // three-parameter Map) shortened to `Map<_, _>` under `open Tagged`
        // reached FSharp.Core's Map, which has no FromList
        let fsharpCoreNames =
            lazy
                ([ "Microsoft.FSharp.Core"
                   "Microsoft.FSharp.Collections"
                   "Microsoft.FSharp.Control"
                   "Microsoft.FSharp.Text"
                   "Microsoft.FSharp.Linq" ]
                 |> Seq.collect (fun ns -> scopeNames ns |> Map.toSeq |> Seq.map fst)
                 |> Set.ofSeq)

        let abbreviationsIn (ns: string) =
            let ofEntities (entities: FSharpEntity seq) =
                entities
                |> Seq.collect flatten
                |> Seq.choose (fun e ->
                    try
                        if e.Namespace = Some ns && e.IsFSharpAbbreviation then
                            Some e.DisplayName
                        else
                            None
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        None)

            let fromAssemblies =
                exportedNamesCache.GetOrAdd(
                    $"abbreviations:{ns}|{assemblyKey}",
                    fun _ ->
                        try
                            assemblies
                            |> Seq.collect (fun a ->
                                try
                                    a.Contents.Entities |> List.ofSeq
                                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                    [])
                            |> ofEntities
                            |> Seq.map (fun name -> name, true)
                            |> Map.ofSeq
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            Map.empty
                )

            fromAssemblies
            |> Map.toSeq
            |> Seq.map fst
            |> Set.ofSeq
            |> Set.union (ofEntities projectEntities.Value |> Set.ofSeq)

        let quoted (names: seq<string>) =
            names
            |> Seq.sort
            |> Seq.truncate 4
            |> Seq.map (sprintf "'%s'")
            |> String.concat ", "

        /// Why an open would clash — the names and where they come from —
        /// or None when it would not.
        let clashes (ns: string) (introduced: Set<string>) (alreadyOpen: bool) : string option =
            let exported = exportedNames ns

            // for a namespace already open only the names the shortening
            // introduces are new; a fresh open brings every export
            let arriving =
                if alreadyOpen then
                    introduced
                else
                    Set.union introduced exported

            // a name we introduce, or any name the open brings, that the file
            // defines itself
            let ownDefinitions = Set.intersect arriving definedHere

            // a name we introduce that another open of the file also brings:
            // whichever open is nearer wins, and the qualified spelling was
            // the author's way of choosing
            let fromOtherOpens =
                allOpened
                |> Set.remove ns
                |> Seq.collect (fun opened ->
                    scopeNames opened
                    |> Map.toSeq
                    |> Seq.map fst
                    |> Seq.filter introduced.Contains
                    |> Seq.map (fun name -> name, opened))
                |> List.ofSeq

            // an abbreviation we introduce that FSharp.Core spells too
            let coreAbbreviations =
                let abbreviated = Set.intersect introduced (abbreviationsIn ns)

                if abbreviated.IsEmpty then
                    Set.empty
                else
                    Set.intersect abbreviated fsharpCoreNames.Value

            // a name the open brings that the file already uses unqualified
            // for something from elsewhere — checked on the first three
            // occurrences of each such name, not on every one: a shadowing
            // binding is visible in the first uses it covers
            let usedForElse () =
                unqualifiedUses
                |> List.filter (fun id -> arriving.Contains id.idText)
                |> List.groupBy (fun id -> id.idText)
                |> List.choose (fun (name, ids) ->
                    ids
                    |> List.truncate 3
                    |> List.tryPick (resolvesOutsideTo ns)
                    |> Option.map (fun other -> name, other))

            // a method the file calls with a tupled argument that the open
            // would give a same-named extension member: the tuple would
            // split into separate arguments against it. Only a FRESH open
            // changes what is in scope; the file's calls are collected once,
            // and the namespace's extensions only when there is a call to
            // match them against
            let reboundCalls () =
                if alreadyOpen || tupledMethodCalls.Value.IsEmpty then
                    Set.empty
                else
                    Set.intersect tupledMethodCalls.Value (extensionMembersIn ns)

            if not ownDefinitions.IsEmpty then
                Some $"this file defines {quoted ownDefinitions} itself"
            elif not fromOtherOpens.IsEmpty then
                let described =
                    fromOtherOpens
                    |> List.map (fun (name, opened) -> $"'{name}' (open {opened})")
                    |> List.truncate 4
                    |> String.concat ", "

                let come = if fromOtherOpens.Length = 1 then "comes" else "come"
                Some $"{described} already {come} from another open of this file"
            elif not coreAbbreviations.IsEmpty then
                Some $"{quoted coreAbbreviations} would shorten to an abbreviation that FSharp.Core spells too"
            else
                let rebound = reboundCalls ()

                if not rebound.IsEmpty then
                    let call = if rebound.Count = 1 then "a call" else "calls"

                    Some
                        $"it brings extension member(s) {quoted rebound} beside {call} this file makes with a tupled argument, which would then split into separate arguments"
                else
                    match usedForElse () with
                    | [] -> None
                    | uses ->
                        let described =
                            uses
                            |> List.truncate 4
                            |> List.map (fun (name, other) ->
                                if other = "" then
                                    $"'{name}'"
                                else
                                    $"'{name}' (from {other})")
                            |> String.concat ", "

                        Some $"this file already uses {described} unqualified for something else"

        resolved
        |> List.groupBy (fun (ns, r) -> ns, blockOf r)
        |> List.choose (fun ((ns, block), uses) ->
            let depth = (ns.Split '.').Length
            let count = uses.Length
            let firstUseLine = uses |> List.map (fun (_, r) -> r.StartLine) |> List.min

            // open for every use only when the open precedes them all
            let alreadyOpen =
                blocks.[block].Opened
                |> List.exists (fun (name, r) ->
                    name = ns
                    && r.EndLine < firstUseLine
                    // an open under `#if` serves only uses under the same
                    // condition; the unconditional ones would break elsewhere
                    && (let openRegion = conditionalRegion r.StartLine

                        openRegion = 0
                        || uses |> List.forall (fun (_, u) -> conditionalRegion u.StartLine = openRegion)))

            if count >= minUses || (depth >= 3 && count >= minDeepUses) || alreadyOpen then
                let removals = uses |> List.map (fun (_, r) -> r, textOfRange source r, "")

                // the short names the shortening introduces
                let introduced =
                    uses
                    |> List.choose (fun (_, r) ->
                        // the segment right after the removed prefix
                        let lineText = source.GetLineString(r.EndLine - 1)
                        let rest = lineText.Substring(min r.EndColumn lineText.Length)
                        let m = System.Text.RegularExpressions.Regex.Match(rest, @"^[A-Za-z_][\w']*")
                        if m.Success then Some m.Value else None)
                    |> Set.ofList

                // the `#if` region the uses share: 0 when any use is
                // unconditional (the namespace resolves in every build, so
                // the open may too), the region when all sit under one, and
                // none when they are split across conditions
                let region =
                    let regions =
                        uses |> List.map (fun (_, r) -> conditionalRegion r.StartLine) |> List.distinct

                    if List.contains 0 regions then Some 0
                    elif regions.Length = 1 then Some regions.Head
                    else None

                let insertion =
                    match region |> Option.bind (insertionPoint block ns firstUseLine) with
                    | Some(at, indent) when not alreadyOpen -> [ at, "", $"{indent}open {ns}\n" ]
                    | _ -> []

                // nowhere to put the open: the shortenings alone would break
                // the file, so the namespace is only noted
                // inside `namespace Nu`, `open OpenGL` resolves to `Nu.OpenGL` first —
                // Nu keeps an empty [<RequireQualifiedAccess>] module there to say
                // so — and only then to the global namespace; a relative shadow
                // of any kind leaves the spelling as it is
                let relativeShadow =
                    blocks.[block].Own
                    |> Seq.tryFind (fun own ->
                        own <> ""
                        && (moduleNamed (own + "." + ns) || not (Map.isEmpty (scopeNames (own + "." + ns)))))

                // a name an ENCLOSING namespace already provides — the F#
                // compiler's every file sits under `FSharp.Compiler`, whose
                // own `SR` module is in scope unqualified; `open FSComp` to
                // spell `FSComp.SR.x` as `SR.x` made `SR` mean two modules,
                // one convention in ten files and another in the rest
                let enclosingShadow =
                    blocks.[block].Own
                    |> Seq.tryPick (fun own ->
                        if own = "" then
                            None
                        else
                            let shadowed = Set.intersect introduced (exportedNames own)

                            if shadowed.IsEmpty then None else Some(own, shadowed))

                // why the open has no place, when it has none
                let noPlace =
                    if alreadyOpen then
                        None
                    elif insertion.IsEmpty then
                        Some "its uses sit under different #if conditions, so no one open serves them all"
                    elif moduleNamed ns then
                        Some $"a module spelled '{ns}' is what the open would resolve to, and it refuses to be opened"
                    else
                        match relativeShadow, enclosingShadow with
                        | Some own, _ -> Some $"inside '{own}' the open would resolve to '{own}.{ns}' first"
                        | None, Some(own, shadowed) ->
                            // the enclosing module is this file's own: the
                            // name is the file's own definition
                            let ownDefinitions = Set.intersect shadowed definedHere

                            if not ownDefinitions.IsEmpty then
                                Some $"this file defines {quoted ownDefinitions} itself"
                            else
                                let reach = if shadowed.Count = 1 then "reaches" else "reach"
                                Some $"{quoted shadowed} already {reach} this file from the enclosing '{own}'"
                        | None, None -> None

                if alreadyOpen && removals.IsEmpty then
                    None
                elif alreadyOpen && (enclosingShadow.IsSome || (clashes ns introduced true).IsSome) then
                    // the namespace is open and the author still qualified:
                    // the short name means something else here
                    None
                else
                    // an open namespace never gets a "would clash" note: the names
                    // it brings are in scope already, accepted by the compiler
                    let reason =
                        if alreadyOpen then
                            None
                        else
                            match noPlace with
                            | Some _ -> noPlace
                            | None -> clashes ns introduced false

                    match reason with
                    | Some _ ->
                        // worth an open, but the open would clash: say so, fix
                        // nothing
                        Some
                            { Range = snd uses.Head
                              Namespace = ns
                              Uses = count
                              Edits = []
                              Reason = reason }
                    | None ->
                        Some
                            { Range = snd uses.Head
                              Namespace = ns
                              Uses = count
                              Edits = insertion @ removals
                              Reason = None }
            else
                None)
        |> List.sortByDescending (fun s -> (s.Namespace.Split '.').Length)
