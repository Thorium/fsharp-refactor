/// Refactoring (the ReSharper "implement missing members" action): an
/// object expression that implements only part of its interface does not
/// compile (FS0366); the fix stubs every missing member with
/// NotImplementedException so the code builds and the TODOs are explicit.
///
///     { new IDbConnection with                { new IDbConnection with
///         member _.Open() = ... }        →        member _.Open() = ...
///                                                 member _.Close() = raise (System.NotImplementedException())
///                                                 ... }
///
/// UNLIKE every other rule, this one runs on files WITH type errors —
/// that is the whole point.
///
/// Safety rules:
///   - the object expression's type resolves (typed check results) to an
///     INTERFACE; missing members come from it and its inherited
///     interfaces, minus everything already implemented (main block and
///     `interface X with` sections both count)
///   - inherited-interface members stub inside their own
///     `interface Base with` section, as F# requires
///   - events and indexers bail out entirely (their stub shapes are not
///     worth guessing); so does an object expression with no members yet
///     (no anchor to copy indentation from)
module FSharp.Refactor.ImplementMissing

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Insertion point (an empty range after the last member).
        Range: range
        /// Every missing member stubbed with NotImplementedException.
        InsertText: string
        /// The same members returning the empty value of their types —
        /// `()`, `None`, `[]`, zeros, `Unchecked.defaultof<_>` — the
        /// editor's second offer: a stub that stays quiet instead of one
        /// that reports itself.
        EmptyInsertText: string
        InterfaceName: string
        MissingNames: string list
    }

/// F# keywords that need escaping when used as parameter names.
let private keywords =
    set
        [
            "type"
            "member"
            "val"
            "end"
            "begin"
            "open"
            "module"
            "done"
            "function"
            "process"
            "method"
            "params"
            "base"
            "default"
            "to"
            "fixed"
        ]

let private paramName (i: int) (p: FSharpParameter) =
    let name = p.Name |> Option.defaultValue $"arg{i}"
    if keywords.Contains name then $"``{name}``" else name

/// One member's stub requirements, grouped per property, with the type
/// its body must produce — what the empty-value stub returns.
type private Required =
    | Method of name: string * paramNames: string list * returns: FSharpType option
    | Property of name: string * hasGetter: bool * hasSetter: bool * propertyType: FSharpType option

/// The abstract members an entity requires, or None when something we do
/// not stub (an event, an indexer) is involved.
let private requiredMembers (entity: FSharpEntity) : (string * Required list) option =
    try

        let properties =
            System.Collections.Generic.Dictionary<string, bool * bool * FSharpType option>()

        let mutable bail = false

        let returnType (m: FSharpMemberOrFunctionOrValue) =
            try
                Some m.ReturnParameter.Type
            with _ -> // a type FCS cannot name: the empty stub falls back to defaultof; fsharpanalyzer: ignore-line FR0055
                None

        let methods: Required list =
            [
                for m in entity.MembersFunctionsAndValues do
                    if m.IsDispatchSlot && not bail then
                        if m.IsEventAddMethod || m.IsEventRemoveMethod || m.IsEvent then
                            bail <- true
                        elif m.IsPropertyGetterMethod || m.IsPropertySetterMethod then
                            let name = m.LogicalName.Substring 4

                            let hasParams =
                                m.CurriedParameterGroups |> Seq.sumBy Seq.length >
                                    (if m.IsPropertySetterMethod then 1 else 0)

                            if hasParams then
                                bail <- true // an indexer
                            else
                                let g, s, t =
                                    match properties.TryGetValue name with
                                    | true, (g, s, t) -> g, s, t
                                    | false, _ -> false, false, None

                                // the getter's return type is the property's type
                                let t = if m.IsPropertyGetterMethod then returnType m else t

                                properties.[name] <- (g || m.IsPropertyGetterMethod, s || m.IsPropertySetterMethod, t)
                        elif m.IsProperty then
                            () // covered by the accessor entries
                        else
                            let names =
                                m.CurriedParameterGroups |> Seq.collect id |> Seq.mapi paramName |> List.ofSeq

                            Method(m.DisplayName, names, returnType m)
            ]

        if bail then
            None
        else
            let props =
                [
                    for kv in properties ->
                        let g, s, t = kv.Value
                        Property(kv.Key, g, s, t)
                ]

            Some(entity.DisplayName, methods @ props)
    with OptionModule.FcsSymbolFailure ->
        None

/// How a stub's body is spelled: a NotImplementedException, or the empty
/// value of the member's type (`()` for a setter and a unit method).
type private Body =
    | Raise
    | Empty

let private stubFor (niPrefix: string) (body: Body) (required: Required) =
    let ni = $"raise ({niPrefix}NotImplementedException())"

    let valueOf (t: FSharpType option) =
        match body, t with
        | Raise, _ -> ni
        | Empty, Some t -> TypeDefaults.emptyValue t
        | Empty, None -> "Unchecked.defaultof<_>"

    let unit' = if body = Raise then ni else "()"

    match required with
    | Method(name, [], t) -> $"member _.{name}() = {valueOf t}"
    | Method(name, names, t) ->
        let args = String.concat ", " names
        $"member _.{name}({args}) = {valueOf t}"
    | Property(name, true, false, t) -> $"member _.{name} = {valueOf t}"
    | Property(name, false, true, _) -> $"member _.{name} with set _v = {unit'}"
    | Property(name, _, true, t) -> $"member _.{name} with get () = {valueOf t} and set _v = {unit'}"
    | Property(name, _, _, t) -> $"member _.{name} = {valueOf t}"

/// The member/property names a member-definition list implements.
let private implementedNames (members: SynMemberDefn list) =
    members
    |> List.collect (fun m ->
        match m with
        | SynMemberDefn.Member(memberDefn = SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)))) when
            not ids.IsEmpty
            ->
            [ (List.last ids).idText ]
        | SynMemberDefn.GetSetMember(memberDefnForGet = g; memberDefnForSet = s) ->
            [ g; s ]
            |> List.choose id
            |> List.choose (fun (SynBinding(headPat = p)) ->
                match p with
                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    Some (List.last ids).idText
                | _ -> None)
        | _ -> [])
    |> Set.ofList

let private nameOf (required: Required) =
    match required with
    | Method(name, _, _) -> name
    | Property(name, _, _, _) -> name

/// Find object expressions with missing interface members. Runs on files
/// WITH errors by design — and ONLY on files with errors: a file that
/// type-checks cleanly has no missing members, whatever this rule's
/// name-matching heuristics conclude about it.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if not (OptionModule.hasErrors check) then
        []
    else

        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.ObjExpr(objType = objType; members = members; extraImpls = impls; newExprRange = newExprRange) when
                    not members.IsEmpty
                    ->
                    // the interface's name ident, e.g. IDbConnection in
                    // `IDbConnection` or `IEnumerable<int>`
                    let typeIdent =
                        match objType with
                        | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
                        | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
                            Some(List.last ids)
                        | _ -> None

                    match typeIdent with
                    | Some typeIdent ->
                        let r = typeIdent.idRange
                        let lineText = source.GetLineString(r.EndLine - 1)

                        let entity =
                            match
                                OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ typeIdent.idText ])
                            with
                            | Some symbolUse ->
                                match symbolUse.Symbol with
                                | :? FSharpEntity as e when e.IsInterface -> Some e
                                | _ -> None
                            | None -> None

                        match entity with
                        | Some entity ->
                            let implementedMain = implementedNames members

                            let implementedPerInterface =
                                impls
                                |> List.map (fun (SynInterfaceImpl(interfaceTy = t; members = ms)) ->
                                    (match t with
                                     | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                         (List.last ids).idText
                                     | _ -> ""),
                                    implementedNames ms)

                            // the main interface's own missing members
                            let mainMissing =
                                match requiredMembers entity with
                                | Some(_, required) ->
                                    required |> List.filter (nameOf >> implementedMain.Contains >> not) |> Some
                                | None -> None

                            // inherited interfaces stub in their own sections
                            let inheritedMissing =
                                try
                                    [
                                        for baseType in entity.AllInterfaces do
                                            // AllInterfaces includes the entity itself
                                            if
                                                baseType.HasTypeDefinition
                                                && not (baseType.TypeDefinition.IsEffectivelySameAs entity)
                                            then
                                                let baseEntity = baseType.TypeDefinition

                                                // members implemented in the MAIN block satisfy inherited
                                                // interfaces too: `{ new IDbConnection with ...
                                                // member _.Dispose() = ... }` compiles, Dispose covering
                                                // IDisposable — stubbing it again would double-implement
                                                let implemented =
                                                    implementedPerInterface
                                                    |> List.tryPick (fun (n, ns) ->
                                                        if n = baseEntity.DisplayName then Some ns else None)
                                                    |> Option.defaultValue Set.empty
                                                    |> Set.union implementedMain

                                                match requiredMembers baseEntity with
                                                | Some(baseName, required) ->
                                                    let missing =
                                                        required |> List.filter (nameOf >> implemented.Contains >> not)

                                                    if not missing.IsEmpty then
                                                        yield Some(baseName, missing)
                                                | None -> yield None
                                    ]
                                with OptionModule.FcsSymbolFailure ->
                                    [ None ]

                            match mainMissing with
                            | Some mainMissing when inheritedMissing |> List.forall Option.isSome ->
                                let inherited = inheritedMissing |> List.choose id

                                if not (mainMissing.IsEmpty && inherited.IsEmpty) then
                                    // anchors: main-member stubs at the members'
                                    // indentation; `interface Base with` sections
                                    // dedent to the `new` keyword's column, as the
                                    // object-expression grammar requires
                                    let lastMember = List.last members
                                    let memberIndent = System.String(' ', lastMember.Range.StartColumn)
                                    let interfaceIndent = System.String(' ', newExprRange.StartColumn)

                                    let niPrefix = if opensSystemNamespace source then "" else "System."

                                    let textWith (body: Body) =
                                        [
                                            for m in mainMissing -> $"\n{memberIndent}{stubFor niPrefix body m}"
                                            for baseName, missing in inherited do
                                                yield $"\n{interfaceIndent}interface {baseName} with"

                                                for m in missing do
                                                    yield $"\n{interfaceIndent}    {stubFor niPrefix body m}"
                                        ]
                                        |> String.concat ""

                                    let insertAt =
                                        Range.mkRange expr.Range.FileName lastMember.Range.End lastMember.Range.End

                                    {
                                        Range = insertAt
                                        InsertText = textWith Raise
                                        EmptyInsertText = textWith Empty
                                        InterfaceName = entity.DisplayName
                                        MissingNames =
                                            (mainMissing |> List.map nameOf)
                                            @ (inherited |> List.collect (fun (_, ms) -> ms |> List.map nameOf))
                                    }
                            | _ -> ()
                        | None -> ()
                    | None -> ()
                | _ -> ()
        ]
