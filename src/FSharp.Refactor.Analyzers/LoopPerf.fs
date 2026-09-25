/// Two loop-performance notes (advice only — both remedies change types
/// or structure, which is the author's call):
///
/// 1. Linear probe per iteration (FR0035): `List.contains x ys` inside a
///    loop — or inside a callback given to a List/Seq/Array function —
///    scans `ys` linearly every time. Building a Set once outside makes
///    each probe O(log n):
///
///        let ySet = Set.ofList ys
///        xs |> List.filter (fun x -> ySet.Contains x)
///
/// 2. Expensive construction per iteration (FR0037): some types are
///    expensive by design and meant to be built once — ConcurrentDictionary
///    (its documentation recommends few, long-lived instances),
///    JsonSerializerOptions (CA1869: caching it is the single biggest
///    System.Text.Json perf lever), and SearchValues.Create (CA1870: the
///    whole point is amortizing the precomputation). Constructing one
///    inside a loop defeats them; hoist it outside or make it static.
///
/// Both only fire when the probed collection / constructed value is
/// loop-invariant as far as the syntax shows: a probe of the loop variable
/// itself is never flagged.
module FSharp.Refactor.LoopPerf

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// Does a value of this type satisfy the `comparison` constraint - what a
/// `Set` demands of its elements, where `List.contains` asked only for
/// `equality`? Read the way the compiler decides it: a record or union
/// compares structurally unless `[<NoComparison>]` says otherwise (or a
/// field cannot compare: a function, a class without IComparable), a
/// `[<CustomComparison>]` type by its own code, a tuple, list, array,
/// option, Set or Map by its parts, anything else by IComparable. A
/// generic parameter is unknown, and unknown is no. Fail-safe: any lookup
/// FCS refuses reads as not comparable.
let rec private supportsComparison (depth: int) (t: FSharpType) : bool =
    depth <= 4
    && (try
            let t = OptionModule.stripAbbreviations t

            if t.IsGenericParameter || t.IsFunctionType then
                false
            elif t.IsTupleType || t.IsStructTupleType then
                t.GenericArguments |> Seq.forall (supportsComparison (depth + 1))
            elif not t.HasTypeDefinition then
                false
            else
                let d = t.TypeDefinition

                let has (attribute: string) =
                    d.Attributes |> Seq.exists (fun a -> a.AttributeType.DisplayName = attribute)

                let partsComparable () =
                    t.GenericArguments |> Seq.forall (supportsComparison (depth + 1))

                if has "NoComparisonAttribute" then
                    false
                elif has "CustomComparisonAttribute" then
                    true
                elif d.IsEnum || d.IsArrayType then
                    d.IsEnum || partsComparable ()
                elif d.IsFSharpRecord then
                    d.FSharpFields
                    |> Seq.forall (fun f -> supportsComparison (depth + 1) f.FieldType)
                elif d.IsFSharpUnion then
                    d.UnionCases
                    |> Seq.forall (fun c ->
                        c.Fields |> Seq.forall (fun f -> supportsComparison (depth + 1) f.FieldType))
                elif d.IsFSharpExceptionDeclaration then
                    false
                else
                    match d.TryFullName with
                    | Some n when
                        n.StartsWith "Microsoft.FSharp.Collections.FSharpList`"
                        || n.StartsWith "Microsoft.FSharp.Core.FSharpOption`"
                        || n.StartsWith "Microsoft.FSharp.Core.FSharpValueOption`"
                        || n.StartsWith "Microsoft.FSharp.Collections.FSharpSet`"
                        || n.StartsWith "Microsoft.FSharp.Collections.FSharpMap`"
                        ->
                        partsComparable ()
                    | _ ->
                        d.AllInterfaces
                        |> Seq.exists (fun i ->
                            i.HasTypeDefinition && i.TypeDefinition.TryFullName = Some "System.IComparable")
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false)

/// The value types whose `.Equals` is what F#'s `=` computes. Double and
/// Single are absent on purpose: `nan = nan` is false, `nan.Equals nan`
/// is true.
let private equalsAgreeingTypes =
    set
        [
            "System.String"
            "System.Boolean"
            "System.Char"
            "System.Byte"
            "System.SByte"
            "System.Int16"
            "System.UInt16"
            "System.Int32"
            "System.UInt32"
            "System.Int64"
            "System.UInt64"
            "System.IntPtr"
            "System.UIntPtr"
            "System.Decimal"
            "System.Guid"
            "System.DateTime"
            "System.DateTimeOffset"
            "System.TimeSpan"
            "System.DateOnly"
            "System.TimeOnly"
            "System.Numerics.BigInteger"
        ]

/// Does `.Equals` - what a HashSet probes with - agree with the structural
/// `=` that `List.contains` used? Not for an array (`=` compares elements,
/// `.Equals` references: a `byte[] list` probed through a HashSet finds
/// nothing), nor a float (NaN), nor a function or generic parameter; a
/// tuple, list, option, Set or Map by its parts, a record or union by its
/// fields, a `[<CustomEquality>]` type by its own code (both spellings call
/// it), and otherwise only the primitives above. Fail-safe: any lookup FCS
/// refuses reads as disagreeing.
let rec private equalsAgrees (depth: int) (t: FSharpType) : bool =
    depth <= 4
    && (try
            let t = OptionModule.stripAbbreviations t

            if t.IsGenericParameter || t.IsFunctionType then
                false
            elif t.IsTupleType || t.IsStructTupleType then
                t.GenericArguments |> Seq.forall (equalsAgrees (depth + 1))
            elif not t.HasTypeDefinition then
                false
            else
                let d = t.TypeDefinition

                let has (attribute: string) =
                    d.Attributes |> Seq.exists (fun a -> a.AttributeType.DisplayName = attribute)

                if d.IsArrayType || has "NoEqualityAttribute" then
                    false
                elif has "CustomEqualityAttribute" || has "ReferenceEqualityAttribute" then
                    true
                elif d.IsEnum then
                    true
                elif d.IsFSharpRecord then
                    d.FSharpFields |> Seq.forall (fun f -> equalsAgrees (depth + 1) f.FieldType)
                elif d.IsFSharpUnion then
                    d.UnionCases
                    |> Seq.forall (fun c -> c.Fields |> Seq.forall (fun f -> equalsAgrees (depth + 1) f.FieldType))
                else
                    match d.TryFullName with
                    | Some n when equalsAgreeingTypes.Contains n -> true
                    | Some n when
                        n.StartsWith "Microsoft.FSharp.Collections.FSharpList`"
                        || n.StartsWith "Microsoft.FSharp.Core.FSharpOption`"
                        || n.StartsWith "Microsoft.FSharp.Core.FSharpValueOption`"
                        || n.StartsWith "Microsoft.FSharp.Collections.FSharpSet`"
                        || n.StartsWith "Microsoft.FSharp.Collections.FSharpMap`"
                        ->
                        t.GenericArguments |> Seq.forall (equalsAgrees (depth + 1))
                    | _ -> false
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false)

/// The element type of the list, array or seq a module binding holds,
/// judged by `holds`: None where the typed tree cannot say.
let private elementSatisfies
    (holds: FSharpType -> bool)
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (id: Ident)
    : bool option =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    try
        match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                let t = OptionModule.stripAbbreviations v.FullType

                if t.HasTypeDefinition && t.GenericArguments.Count = 1 then
                    Some(holds t.GenericArguments.[0])
                else
                    None
            | _ -> None
        | None -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// Whether the element compares (a Set's demand).
let private elementComparable = elementSatisfies (supportsComparison 0)

/// Whether the element's `.Equals` agrees with `=` (a HashSet's demand).
let private elementEquatable = elementSatisfies (equalsAgrees 0)

/// Can a value of this type carry a float (Double or Single) - itself, or a
/// part of a tuple, record, union, list, option, array, Set or Map? Such a
/// value can carry a NaN, and NaN splits the two probes: `List.contains`
/// asks `=`, where `nan = nan` is false, and a `Set` asks the comparison,
/// where NaN sorts equal to itself - `List.contains nan [ nan ]` is false,
/// `(Set.ofList [ nan ]).Contains nan` is true. Fail-safe: unknown is yes.
let rec private mayHoldFloat (depth: int) (t: FSharpType) : bool =
    depth > 4
    || (try
            let t = OptionModule.stripAbbreviations t

            let parts () =
                t.GenericArguments |> Seq.exists (mayHoldFloat (depth + 1))

            if t.IsGenericParameter || t.IsFunctionType then
                false
            elif t.IsTupleType || t.IsStructTupleType then
                parts ()
            elif not t.HasTypeDefinition then
                true
            else
                let d = t.TypeDefinition

                match d.TryFullName with
                | Some("System.Double" | "System.Single") -> true
                | _ when d.IsEnum -> false
                | _ when d.IsFSharpRecord ->
                    d.FSharpFields |> Seq.exists (fun f -> mayHoldFloat (depth + 1) f.FieldType)
                | _ when d.IsFSharpUnion ->
                    d.UnionCases
                    |> Seq.exists (fun c -> c.Fields |> Seq.exists (fun f -> mayHoldFloat (depth + 1) f.FieldType))
                | _ -> parts ()
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            true)

/// Whether the element can carry a NaN.
let private elementMayHoldFloat = elementSatisfies (mayHoldFloat 0)

/// An element written out in full, with no NaN in it: a constant (a
/// numeric literal is never NaN, save a bit-pattern float like
/// `0x7FF8000000000000LF`), a negated one, and tuples and records of
/// those. `nan`, `Double.NaN`, `infinity - infinity`, a named value or any
/// other computation is not proven.
let rec private nanFreeLiteral (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Unit, _) -> false
    | SynExpr.Const(SynConst.Double v, _) -> not (System.Double.IsNaN v)
    | SynExpr.Const(SynConst.Single v, _) -> not (System.Single.IsNaN v)
    | SynExpr.Const(SynConst.Measure(constant = inner), r) -> nanFreeLiteral (SynExpr.Const(inner, r))
    | SynExpr.Const _ -> true
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> nanFreeLiteral inner
    | SynExpr.App(isInfix = false; funcExpr = SingleIdent neg; argExpr = SynExpr.Const _ as inner) when
        neg.idText = "op_UnaryNegation"
        ->
        nanFreeLiteral inner
    | SynExpr.Tuple(exprs = exprs) -> exprs |> List.forall nanFreeLiteral
    | SynExpr.Record(baseInfo = None; copyInfo = None; recordFields = fields) ->
        fields
        |> List.forall (fun (SynExprRecordField(expr = value)) -> value |> Option.exists nanFreeLiteral)
    | _ -> false

/// Every element of a list or array literal is `nanFreeLiteral`.
let private nanFreeCollection (rhs: SynExpr) =
    let rec elements (e: SynExpr) =
        match e with
        | SynExpr.Sequential(expr1 = a; expr2 = b) -> elements a @ elements b
        | e -> [ e ]

    match rhs with
    | SynExpr.ArrayOrList(exprs = exprs) -> exprs |> List.forall nanFreeLiteral
    | SynExpr.ArrayOrListComputed(expr = inner) -> elements inner |> List.forall nanFreeLiteral
    | _ -> false

type ContainsSuggestion =
    {
        Range: range
        /// The linearly probed collection, for the message.
        CollectionName: string
        /// "List", "Array", or "Seq", for the message.
        ModuleName: string
        /// When the collection is a MODULE-LEVEL immutable binding in this
        /// file (startup-built, never shadowed or reassigned), the fix:
        /// insert a private HashSet companion right after it, and rewrite
        /// every loop probe of it in this file. All-or-nothing. Guards: the
        /// binding is a list or array literal (a ResizeArray or seq is not
        /// what a snapshot saw), an array only private and with no use but
        /// the probes (an element write), and the element's `.Equals`
        /// agrees with `=` (no array, float or function inside), proven by
        /// the typed tree. The in-place `Set` conversion asks `comparison`
        /// of the element, and of an element that can carry a float (a
        /// float, or a tuple/record/union holding one) that every element
        /// of the literal is a written-out constant, none a NaN: the Set
        /// finds a NaN that `List.contains` never did.
        Fix: (range * string * string) list
    }

type ConstructionSuggestion =
    {
        Range: range
        /// The constructed type's name, for the message.
        TypeName: string
    }

/// A bare identifier path — `x`, `xs.Length`, `Some.Module.value`.
let private atomicIdent =
    System.Text.RegularExpressions.Regex(@"^[A-Za-z_][\w'.]*$", System.Text.RegularExpressions.RegexOptions.Compiled)

let private collectionModules = set [ "List"; "Array"; "Seq" ]

/// Types whose construction inside a loop is expensive by design.
///
/// `Regex` belongs here as much as the others: constructing one parses and
/// compiles the pattern, which is the whole cost. FR0015 covers the STATIC
/// calls — `Regex.IsMatch(s, "...")` in a loop — but a `Regex` bound to a
/// value inside a loop went unnoticed by either rule.
let private expensiveTypes =
    set [ "ConcurrentDictionary"; "HttpClient"; "JsonSerializerOptions"; "Regex" ]

/// Static factories with the same build-once intent (Type, method).
let private expensiveFactories = [ "SearchValues", "Create" ]

/// A probed collection: a bare name or a dotted path (config.Excluded,
/// this.samples — collections routinely live in a record or object field).
/// The ROOT identifier is what loop-invariance is judged on: a dotted path
/// varies per iteration exactly when its root does.
[<return: Struct>]
let private (|CollPath|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome(id, id.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.head ids, identText ids)
    | _ -> ValueNone

/// `<m>.contains item coll` and `coll |> <m>.contains item` — the probed
/// ITEM comes back too, for the HashSet rewrite.
[<return: Struct>]
let private (|ContainsCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(
            isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = item)
        argExpr = CollPath(root, text)) when collectionModules.Contains m.idText && f.idText = "contains" ->
        ValueSome(m.idText, root, text, item)
    | PipeApp(CollPath(root, text),
              SynExpr.App(
                  isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = item)) when
        collectionModules.Contains m.idText && f.idText = "contains"
        ->
        ValueSome(m.idText, root, text, item)
    | _ -> ValueNone

/// `new ConcurrentDictionary<...>(...)` / `ConcurrentDictionary<...>(...)`
/// / `ConcurrentDictionary(...)` — the constructed expensive type's name.
[<return: Struct>]
let private (|ExpensiveCtor|_|) (e: SynExpr) =
    let typeNameOf (t: SynType) =
        match t with
        | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)))
        | SynType.LongIdent(SynLongIdent(id = ids)) when
            not ids.IsEmpty && expensiveTypes.Contains (List.last ids).idText
            ->
            ValueSome (List.last ids).idText
        | _ -> ValueNone

    let ctorNameOf (inner: SynExpr) =
        match inner with
        | SynExpr.Ident id when expensiveTypes.Contains id.idText -> ValueSome id.idText
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
            not ids.IsEmpty && expensiveTypes.Contains (List.last ids).idText
            ->
            ValueSome (List.last ids).idText
        | _ -> ValueNone

    let factoryNameOf (inner: SynExpr) =
        match inner with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
            let typeId = ids.[ids.Length - 2].idText
            let methodId = (List.last ids).idText

            if expensiveFactories |> List.contains (typeId, methodId) then
                ValueSome typeId
            else
                ValueNone
        | _ -> ValueNone

    match e with
    | SynExpr.New(targetType = t) -> typeNameOf t
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.TypeApp(expr = inner)) -> ctorNameOf inner
    | SynExpr.App(isInfix = false; funcExpr = (SynExpr.Ident _ | SynExpr.LongIdent _) as inner) ->
        match ctorNameOf inner with
        | ValueSome name -> ValueSome name
        | ValueNone -> factoryNameOf inner
    | _ -> ValueNone

/// The loop-context binders along the path: Some names when the node sits
/// inside a loop or a collection-function callback, None otherwise.
/// Shared with the other loop-context rules (ListIndexing).
let loopBinders (path: SyntaxNode list) =
    let mutable insideLoop = false
    let binders = ResizeArray<string>()
    let mutable sawLambda = false

    for node in path do
        match node with
        | SyntaxNode.SynExpr(SynExpr.ForEach(pat = p)) ->
            insideLoop <- true
            binders.AddRange(patBoundNames p)
        | SyntaxNode.SynExpr(SynExpr.For(ident = loopVar)) ->
            insideLoop <- true
            binders.Add loopVar.idText
        | SyntaxNode.SynExpr(SynExpr.While _) -> insideLoop <- true
        // a let between the loop and the probe may rebind the collection
        // per iteration — its bindings are loop-local, not loop-invariant
        | SyntaxNode.SynExpr(LetOrUseE lou) ->
            for SynBinding(headPat = p) in lou.Bindings do
                binders.AddRange(patBoundNames p)
        // so may a match arm's pattern: `| Item.AnonRecdField(_, tys, idx,
        // _) -> tys[idx]` (FCS) binds a fresh `tys` per element
        | SyntaxNode.SynMatchClause(SynMatchClause(pat = p)) -> binders.AddRange(patBoundNames p)
        | SyntaxNode.SynExpr(SynExpr.Lambda(parsedData = parsedData)) ->
            sawLambda <- true

            match parsedData with
            | Some(pats, _) ->
                for p in pats do
                    binders.AddRange(patBoundNames p)
            | None -> ()
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = m :: _)))) when
            sawLambda && collectionModules.Contains m.idText
            ->
            // the lambda is a callback of a collection function: it runs
            // once per element, which is a loop
            insideLoop <- true
        | _ -> ()

    if insideLoop then
        ValueSome(Set.ofSeq binders)
    else
        ValueNone

/// Find per-iteration linear probes and expensive constructions.
///
/// `allowApiChanges`: the in-place conversion (`|> Set.ofList`) changes
/// the binding's TYPE — `string list` becomes `Set<string>` — which is an
/// API change on a public module value. Without the opt-in, only a
/// private/internal binding converts in place; a public one gets the
/// private HashSet companion beside it instead, which leaves its type
/// alone (fsharplint's public `testMethodAttributes` list, in a NuGet
/// library, was converted to a Set without `--api-changes`).
///
/// `seenByLaterFile`: when the opt-in is not the caller's own but the
/// host's leaf-compilation heuristic — an executable, whose public surface
/// is no API — a LATER file of the same executable can still read the
/// binding at its list type. This answers, by name, whether one does; a
/// binding that is not private then converts in place only when nothing
/// after it mentions it. `find` passes the constant "no", which is the
/// right answer for a real `--api-changes` and moot for a closed gate.
let findWith
    (seenByLaterFile: string -> bool)
    (allowApiChanges: bool)
    (check: FSharpCheckFileResults option)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : ContainsSuggestion list * ConstructionSuggestion list =
    let index = AstIndex.ofTree parseTree
    let constructions = ResizeArray<ConstructionSuggestion>()

    // module-level immutable single-name bindings: the startup-built
    // collections a HashSet companion can shadow-probe; `confined` says
    // whether the binding's type may change (its own modifier, an
    // enclosing private/internal module, or the --api-changes opt-in)
    let moduleBindings =
        [
            for path, decl in index.Decls do
                match decl with
                | SynModuleDecl.Let(
                    isRecursive = false
                    bindings = [ SynBinding(isMutable = false; accessibility = bindingAcc; headPat = pat; expr = rhs) ]) ->
                    match pat with
                    | SynPat.Named(ident = SynIdent(ident = id); accessibility = patAcc)
                    | SynPat.LongIdent(
                        longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []; accessibility = patAcc) ->
                        let confined =
                            Visibility.isInScopeNamed allowApiChanges path [ bindingAcc; patAcc ] id.idText
                            // the opt-in covers this file's own uses (the
                            // `strayUse` scan below) - a later file's, only a
                            // private binding is sure to have none
                            && (Visibility.isPrivate path [ bindingAcc; patAcc ]
                                || not (seenByLaterFile id.idText))

                        let isPrivate = Visibility.isPrivate path [ bindingAcc; patAcc ]
                        yield id.idText, (id, decl.Range, rhs, confined, isPrivate)
                    | _ -> ()
                | _ -> ()
        ]
        |> List.distinctBy fst
        |> dict

    // any OTHER binder of the same name anywhere (a parameter, a loop
    // local, a lambda argument) makes the name resolution ambiguous to a
    // parse-only scan — no fix then
    let shadowed (name: string) (moduleIdent: Ident) =
        index.Pats
        |> Array.exists (fun (_, p) ->
            match p with
            | SynPat.Named(ident = SynIdent(ident = id))
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                id.idText = name && not (Range.equals id.idRange moduleIdent.idRange)
            | _ -> false)

    // never reassigned either
    let reassigned (name: string) =
        index.Exprs
        |> Array.exists (fun (_, e) ->
            match e with
            | SynExpr.LongIdentSet(SynLongIdent(id = ids), _, _) when not ids.IsEmpty -> (List.last ids).idText = name
            | _ -> false)

    let opensCollectionsGeneric =
        seq { 0 .. source.GetLineCount() - 1 }
        |> Seq.exists (fun l -> source.GetLineString(l).Trim() = "open System.Collections.Generic")

    let hashSetSpelling =
        if opensCollectionsGeneric then
            "HashSet"
        else
            "System.Collections.Generic.HashSet"

    // (collection name, loop probe) pairs, grouped afterwards
    let rawProbes = ResizeArray<string * Ident * range * SynExpr>()

    for path, expr in index.Exprs do
        match expr with
        | ContainsCall(moduleName, root, collText, item) ->
            match loopBinders path with
            | ValueSome binders when not (binders.Contains root.idText) ->
                rawProbes.Add(collText, root, expr.Range, item)
                ignore moduleName
            | _ -> ()
        | ExpensiveCtor typeName ->
            match loopBinders path with
            | ValueSome _ ->
                constructions.Add
                    {
                        Range = expr.Range
                        TypeName = typeName
                    }
            | ValueNone -> ()
        | _ -> ()

    // second walk for the messages (module name is per probe)
    let contains =
        [
            for path, expr in index.Exprs do
                match expr with
                | ContainsCall(moduleName, root, collText, item) ->
                    match loopBinders path with
                    | ValueSome binders when not (binders.Contains root.idText) ->
                        // the fix: only for a BARE module-level immutable name
                        // (a dotted path's storage is not this file's to
                        // shadow), unshadowed and never reassigned — then all
                        // probes of it convert together with one companion
                        let fix =
                            match moduleBindings.TryGetValue collText with
                            | true, (moduleIdent, declRange, declRhs, confined, isPrivate) when
                                collText = root.idText
                                && not (shadowed collText moduleIdent)
                                && not (reassigned collText)
                                ->
                                let siblings =
                                    rawProbes |> Seq.filter (fun (c, _, _, _) -> c = collText) |> Seq.toList

                                // one companion binding for the whole group;
                                // emitted identically from every probe of the
                                // group, and identical fixes coalesce at the
                                // apply layer via the overlap guard — but only
                                // the FIRST probe carries the edit set, so the
                                // group applies once
                                let isFirst =
                                    match siblings with
                                    | (_, _, firstRange, _) :: _ -> Range.equals firstRange expr.Range
                                    | [] -> false

                                let probeArg (itemExpr: SynExpr) =
                                    let itemText = textOfRange source itemExpr.Range

                                    let atomic = atomicIdent.IsMatch itemText

                                    if atomic then itemText else $"({itemText})"

                                // in-place conversion: when EVERY use of the
                                // name is one of these probes, the binding
                                // itself becomes the set — no companion, the
                                // module value stays immutable, and Set's own
                                // Contains member takes the probes (measured
                                // 2.5x over the list scan even at five
                                // elements; the companion HashSet remains the
                                // spelling when other uses need the original)
                                // A `seq { ... }` is no candidate: it re-runs
                                // on every probe, over state that may have
                                // changed since, and a set is a snapshot
                                let literalIsArray =
                                    match declRhs with
                                    | SynExpr.ArrayOrListComputed(isArray = isArray)
                                    | SynExpr.ArrayOrList(isArray = isArray) -> Some isArray
                                    | _ -> None

                                let setOfFunction =
                                    literalIsArray
                                    |> Option.map (fun isArray -> if isArray then "Set.ofArray" else "Set.ofList")

                                let probeRanges = siblings |> List.map (fun (_, _, r, _) -> r)

                                let strayUse =
                                    index.Exprs
                                    |> Array.exists (fun (_, e) ->
                                        match e with
                                        | SynExpr.Ident id when id.idText = collText ->
                                            not (
                                                probeRanges
                                                |> List.exists (fun pr -> Range.rangeContainsRange pr id.idRange)
                                            )
                                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _ :: _)) when
                                            first.idText = collText
                                            ->
                                            not (
                                                probeRanges
                                                |> List.exists (fun pr -> Range.rangeContainsRange pr e.Range)
                                            )
                                        | _ -> false)

                                if not isFirst then
                                    []
                                // the in-place conversion changes the
                                // binding's type: only where nothing outside
                                // the assembly can see it (or --api-changes)
                                // ...and `Set` asks `comparison` of the
                                // element where `List.contains` asked only
                                // `equality`: a [<NoComparison>] record, or
                                // one with a function field, takes the
                                // HashSet companion below instead. Without
                                // the typed tree (an editor's parse-only
                                // pass) the answer is unknown, and unknown
                                // is the companion too
                                elif
                                    setOfFunction.IsSome
                                    && not strayUse
                                    && confined
                                    && (check
                                        |> Option.bind (fun c -> elementComparable c source moduleIdent)
                                        |> Option.defaultValue false)
                                    // a float element compares NaN equal to
                                    // itself in the Set where `=` never did:
                                    // only a literal of written-out numbers,
                                    // none a NaN, converts
                                    && (nanFreeCollection declRhs
                                        || not (
                                            check
                                            |> Option.bind (fun c -> elementMayHoldFloat c source moduleIdent)
                                            |> Option.defaultValue true
                                        ))
                                then
                                    let convert =
                                        Range.mkRange declRange.FileName declRhs.Range.End declRhs.Range.End,
                                        "",
                                        $" |> {setOfFunction.Value}"

                                    let rewrites =
                                        siblings
                                        |> List.map (fun (_, _, r, itemExpr) ->
                                            r, textOfRange source r, $"{collText}.Contains {probeArg itemExpr}")

                                    convert :: rewrites
                                // the companion is a SNAPSHOT of the binding
                                // probed with `.Equals`: only an F# list (or
                                // an array nothing else in this file or any
                                // other can reach to write an element into)
                                // stays what the snapshot saw — a ResizeArray
                                // grown later, a written array element or a
                                // seq over mutable state would not — and only
                                // an element whose `.Equals` is `=` (a
                                // `byte[]` element compares by reference in a
                                // HashSet). Unknown, without the typed tree,
                                // is no
                                elif
                                    not (
                                        (match literalIsArray with
                                         | Some false -> true
                                         | Some true -> not strayUse && isPrivate
                                         | None -> false)
                                        && (check
                                            |> Option.bind (fun c -> elementEquatable c source moduleIdent)
                                            |> Option.defaultValue false)
                                    )
                                then
                                    []
                                elif not (source.GetLineString(declRange.StartLine - 1).Contains "ProbeSet") then
                                    let setName = collText + "ProbeSet"

                                    let taken =
                                        seq { 0 .. source.GetLineCount() - 1 }
                                        |> Seq.exists (fun l -> source.GetLineString(l).Contains setName)

                                    if taken then
                                        []
                                    else
                                        let indent = String.replicate declRange.StartColumn " "

                                        let insertAt =
                                            Range.mkRange
                                                declRange.FileName
                                                (Position.mkPos (declRange.EndLine + 1) 0)
                                                (Position.mkPos (declRange.EndLine + 1) 0)

                                        let binding = $"{indent}let private {setName} = {hashSetSpelling}({collText})\n"

                                        // the companion serves the probes: probes
                                        // all under one `#if` get a companion
                                        // under that same `#if`, probes under
                                        // different conditions get none (a
                                        // binding under one condition cannot
                                        // serve the other)
                                        let probeConditions =
                                            siblings
                                            |> List.map (fun (_, _, r: range, _) -> conditionAt source r.StartLine)
                                            |> List.distinct

                                        let insertText =
                                            match probeConditions with
                                            | [ Some c ] when conditionAt source insertAt.StartLine <> Some c ->
                                                Some $"#if {c}\n{binding}#endif\n"
                                            | [ _ ] -> Some binding
                                            | _ -> None

                                        match insertText with
                                        | None -> []
                                        | Some insertText ->
                                            let insert = insertAt, "", insertText

                                            let rewrites =
                                                siblings
                                                |> List.map (fun (_, _, r, itemExpr) ->
                                                    let itemText = textOfRange source itemExpr.Range

                                                    let atomic = atomicIdent.IsMatch itemText

                                                    let arg = if atomic then itemText else $"({itemText})"
                                                    r, textOfRange source r, $"{setName}.Contains {arg}")

                                            insert :: rewrites
                                else
                                    []
                            | _ -> []

                        {
                            Range = expr.Range
                            CollectionName = collText
                            ModuleName = moduleName
                            Fix = fix
                        }
                    | _ -> ()
                | _ -> ()
        ]

    contains, List.ofSeq constructions

/// `findWith` for a caller whose opt-in is its own: `--api-changes`, or no
/// opt-in at all. No later file is consulted.
let find (allowApiChanges: bool) (check: FSharpCheckFileResults option) (parseTree: ParsedInput) (source: ISourceText) =
    findWith (fun _ -> false) allowApiChanges check parseTree source
