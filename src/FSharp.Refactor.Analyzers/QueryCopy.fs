/// FR0174 (performance, fix), CR0178's twin: in C#-style LINQ over
/// `open System.Linq`, a copy of a query ahead of `Where`/`Select` loads
/// every row and filters in memory; the query takes the stages.
///
///     db.Orders.ToList().Where(fun o -> o.Total > 0).Select(fun o -> o.Id)
///       →  db.Orders.Where(fun o -> o.Total > 0).Select(fun o -> o.Id).ToList()
///
/// The LINQ method chain, by default. A `query { }` expression says where
/// the query ends by its shape, and a pipeline (`q |> Seq.toList |>
/// List.filter f`) is the F# collection modules' — the author chose where
/// the rows come into memory, visibly. The `pipelines` knob (default off)
/// takes the pipeline too:
///
///     db.Orders |> Seq.toList |> List.filter (fun o -> o.State = 0)
///       →  db.Orders.Where(fun o -> o.State = 0) |> Seq.toList
///
/// `Seq.toList`/`List.ofSeq` followed by `List.filter`/`List.map`, or
/// `Seq.toArray`/`Array.ofSeq` by `Array.filter`/`Array.map`, so the
/// result keeps its type; the rewrite spells `.Where`, so without
/// `open System.Linq` it is a note. `query { }` is never touched. The
/// copy — `ToList`/`ToArray`/`AsEnumerable` — sits on a receiver the typed
/// tree proves is an `IQueryable`; the stages after it are
/// `Enumerable.Where`/`Select`, each with a one-parameter lambda, and move
/// before the copy only while every lambda is one a provider translates
/// exactly:
/// - filter: `&&`, `||`, `not` over comparisons (`=`, `<>`, `<`, `<=`,
///   `>`, `>=`) and `bool` columns; a comparison has a column on one side
///   and a column, a literal, an immutable value or an enum case on the
///   other;
/// - projection: a column;
/// - a column is a record field of the lambda's parameter, a compiled
///   auto-property (a C# entity's), or a `member val` of this file, not
///   `[<NotMapped>]`.
/// A sweep moves only comparisons SQL answers as .NET does: integers,
/// `bool`, enums and `Guid`, and `= null`/`<> null`. A string compares
/// under the column's collation, a decimal or a date is rounded to the
/// column's scale, a float is the server's, a nullable column is
/// NULL-unknown where .NET may say true: those the editor offers and a
/// sweep leaves as a note. The one nullable comparison that is exact: a
/// `Nullable<T>` column of one of the exact types against a value proven
/// non-null (a literal, or a value or enum case whose own type is no
/// Nullable), by `=`, `<`, `<=`, `>`, `>=`, under no `not` - SQL's unknown
/// and .NET's false both drop the NULL row. Under an odd number of `not`s
/// SQL still drops it where .NET keeps it, and `<>` keeps it in .NET too. F# captures only immutable values, so what the lambda
/// reads is the same whenever the query runs.
module FSharp.Refactor.QueryCopy

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// How faithfully a provider answers a translated lambda: as .NET does,
/// or only nearly (collation, rounding, NULL logic).
type Fidelity =
    | Exact
    | Near

type Suggestion =
    {
        /// The span the rewrite replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The copy as spelled: `ToList()`, `Seq.toList`.
        CopyName: string
        /// The moved stages as spelled: `Where/Select`, `List.filter`.
        Stages: string
        Fidelity: Fidelity
        /// False where the rewrite would spell a name the file cannot see
        /// (a pipeline's `.Where` without `open System.Linq`): a note only.
        Fixable: bool
        /// The chain keeps its meaning with its new type. `ToList()` moved
        /// to the end makes an `IEnumerable<T>` a `List<T>`: a `let` would
        /// carry the new type on, an overload taking `List<T>` would win,
        /// `.Reverse()` would bind to `List<T>.Reverse()`. True where the
        /// value goes on into an Enumerable call, a `for ... in`, or a
        /// `Seq`/`List`/`Array` function; else the editor offers it.
        TypeStable: bool
    }

let private weaker (a: Fidelity) (b: Fidelity) =
    if a = Near || b = Near then Near else Exact

let private combine (a: Fidelity option) (b: Fidelity option) =
    match a, b with
    | Some a, Some b -> Some(weaker a b)
    | _ -> None

[<return: Struct>]
let private (|Infix|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName op; argExpr = l); argExpr = r) ->
        ValueSome(op, l, r)
    | _ -> ValueNone

let private comparisons =
    set
        [
            "op_Equality"
            "op_Inequality"
            "op_LessThan"
            "op_LessThanOrEqual"
            "op_GreaterThan"
            "op_GreaterThanOrEqual"
        ]

[<TailCall>]
let rec private unparen (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner) -> unparen inner
    | e -> e

/// `fun o -> body` / `fun (o: Order) -> body`: the parameter and the body.
let private lambda1 (e: SynExpr) =
    let rec named (p: SynPat) =
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
        | SynPat.Paren(pat = inner)
        | SynPat.Typed(pat = inner) -> named inner
        | _ -> None

    match unparen e with
    | SynExpr.Lambda(parsedData = Some([ pat ], body)) -> named pat |> Option.map (fun p -> p, body)
    | _ -> None

let private exactNames =
    set
        [
            "System.Boolean"
            "System.Byte"
            "System.SByte"
            "System.Int16"
            "System.UInt16"
            "System.Int32"
            "System.UInt32"
            "System.Int64"
            "System.UInt64"
            "System.Guid"
        ]

let private nearNames =
    set
        [
            "System.String"
            "System.Char"
            "System.Decimal"
            "System.Double"
            "System.Single"
            "System.DateTime"
            "System.DateTimeOffset"
            "System.DateOnly"
            "System.TimeOnly"
            "System.TimeSpan"
        ]

let rec private typeFidelity (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        if not t.HasTypeDefinition then
            None
        else
            let d = t.TypeDefinition

            match d.TryFullName with
            | _ when d.IsEnum -> Some Exact
            | Some "System.Nullable`1" when t.GenericArguments.Count = 1 ->
                typeFidelity t.GenericArguments.[0] |> Option.map (fun _ -> Near)
            | Some name when exactNames.Contains name -> Some Exact
            | Some name when nearNames.Contains name -> Some Near
            | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

let private isNullable (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t
        t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Nullable`1"
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        true

/// `Nullable<T>` of a T SQL compares as .NET does (integers, bool, enums,
/// Guid): its only difference is the NULL row.
let private nullableOfExact (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        isNullable t
        && t.GenericArguments.Count = 1
        && typeFidelity t.GenericArguments.[0] = Some Exact
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// A column holding a value, not an entity: a navigation property
/// (`o.Customer`) is a column too, but in memory it is whatever the copy
/// loaded - null without an `Include` - where the query joins it, so
/// `o.Customer = null` and `Select(fun o -> o.Customer)` answer differently.
let private scalar (t: FSharpType) =
    (typeFidelity t).IsSome
    || (try
            let t = OptionModule.stripAbbreviations t

            t.HasTypeDefinition
            && t.TypeDefinition.IsArrayType
            && t.GenericArguments.Count = 1
            && (OptionModule.stripAbbreviations t.GenericArguments.[0]).TypeDefinition.TryFullName = Some "System.Byte"
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false)

let private isBool (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t
        t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Boolean"
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

let private hasAttribute (name: string) (attributes: seq<FSharpAttribute>) =
    attributes
    |> Seq.exists (fun a ->
        try
            a.AttributeType.DisplayName = name
            || a.AttributeType.DisplayName = name + "Attribute"
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false)

/// Is the value an IQueryable (or an implementation of one)?
let private isQueryable (t: FSharpType) =
    let queryable (name: string option) =
        name |> Option.exists (fun n -> n.StartsWith "System.Linq.IQueryable")

    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (queryable t.TypeDefinition.TryFullName
            || t.TypeDefinition.AllInterfaces
               |> Seq.exists (fun i -> i.HasTypeDefinition && queryable i.TypeDefinition.TryFullName))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

let private declaringName (v: FSharpMemberOrFunctionOrValue) =
    try
        v.DeclaringEntity
        |> Option.bind (fun e -> e.TryFullName)
        |> Option.defaultValue ""
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        ""

let private copyMethods = set [ "ToList"; "ToArray"; "AsEnumerable" ]

/// The pipeline copies, and the collection module whose stages follow them.
let private copyFunctions =
    Map
        [
            ("Seq", "toList"), "List"
            ("List", "ofSeq"), "List"
            ("Seq", "toArray"), "Array"
            ("Array", "ofSeq"), "Array"
        ]

let private moduleNames =
    Map
        [
            "Seq", "Microsoft.FSharp.Collections.SeqModule"
            "List", "Microsoft.FSharp.Collections.ListModule"
            "Array", "Microsoft.FSharp.Collections.ArrayModule"
        ]

/// `pipelines`: take the `|> Seq.toList |> List.filter` shape as well.
let find
    (pipelines: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let symbolAt (ident: Ident) =
            let r = ident.idRange

            OptionModule.symbolUseAt
                check
                (r.EndLine, r.EndColumn, source.GetLineString(r.EndLine - 1), [ ident.idText ])
            |> Option.map (fun u -> u.Symbol)

        // `member val` properties of this file, by name and declaring line
        let autoProperties =
            let found = System.Collections.Generic.HashSet<string * int>()

            let rec walkMembers (members: SynMemberDefn list) =
                for m in members do
                    match m with
                    | SynMemberDefn.AutoProperty(ident = id) -> found.Add((id.idText, id.idRange.StartLine)) |> ignore
                    | _ -> ()

            let rec walkDecls (decls: SynModuleDecl list) =
                for d in decls do
                    match d with
                    | SynModuleDecl.Types(typeDefns = types) ->
                        for SynTypeDefn(typeRepr = repr; members = members) in types do
                            walkMembers members

                            match repr with
                            | SynTypeDefnRepr.ObjectModel(members = inner) -> walkMembers inner
                            | _ -> ()
                    | SynModuleDecl.NestedModule(decls = inner) -> walkDecls inner
                    | _ -> ()

            match parseTree with
            | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
                for SynModuleOrNamespace(decls = decls) in modules do
                    walkDecls decls
            | _ -> ()

            found

        let autoProperty (v: FSharpMemberOrFunctionOrValue) =
            try
                (v.HasGetterMethod && hasAttribute "CompilerGenerated" v.GetterMethod.Attributes)
                || autoProperties.Contains((v.DisplayName, v.DeclarationLocation.StartLine))
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false

        /// `o.P`: a column of the lambda's parameter, and its type.
        let column (param: Ident) (e: SynExpr) : FSharpType option =
            let prop =
                match unparen e with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ p; prop ])) when p.idText = param.idText ->
                    Some prop
                | SynExpr.DotGet(expr = SynExpr.Ident p; longDotId = SynLongIdent(id = [ prop ])) when
                    p.idText = param.idText
                    ->
                    Some prop
                | _ -> None

            prop
            |> Option.bind (fun prop ->
                match symbolAt prop with
                | Some(:? FSharpField as f) when
                    not f.IsStatic
                    && not (hasAttribute "NotMapped" f.PropertyAttributes)
                    && not (hasAttribute "NotMapped" f.FieldAttributes)
                    ->
                    Some f.FieldType
                | Some(:? FSharpMemberOrFunctionOrValue as v) when
                    v.IsProperty
                    && v.IsInstanceMember
                    && autoProperty v
                    && not (hasAttribute "NotMapped" v.Attributes)
                    ->
                    Some(resultTypeOf v)
                | _ -> None)

        /// A literal, an immutable value other than the parameter, an enum case.
        let value (param: Ident) (e: SynExpr) =
            match unparen e with
            | SynExpr.Const(constant = SynConst.Unit) -> false
            | SynExpr.Const _ -> true
            | SynExpr.Ident id when id.idText = param.idText -> false
            | SynExpr.Ident id ->
                match symbolAt id with
                | Some(:? FSharpMemberOrFunctionOrValue as v) ->
                    not v.IsMutable
                    && (v.LiteralValue.IsSome || (v.IsValue && not v.FullType.IsFunctionType))
                | _ -> false
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                not ids.IsEmpty && ids.Head.idText <> param.idText
                ->
                match symbolAt (List.last ids) with
                | Some(:? FSharpField as f) -> f.LiteralValue.IsSome
                | Some(:? FSharpMemberOrFunctionOrValue as v) -> v.LiteralValue.IsSome
                | _ -> false
            | _ -> false

        let typeOfName (ident: Ident) =
            match symbolAt ident with
            | Some(:? FSharpMemberOrFunctionOrValue as v) -> Some(resultTypeOf v)
            | Some(:? FSharpField as f) -> Some f.FieldType
            | _ -> None

        /// The value (already `value`) is not null: a literal, or a name
        /// whose own type is no Nullable - an `int` converted to the
        /// column's `Nullable<int>` on the way in, an enum case.
        let nonNullValue (e: SynExpr) =
            let ownType =
                match unparen e with
                | SynExpr.Const _ -> Some None
                | SynExpr.Ident id -> Some(typeOfName id)
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    Some(typeOfName (List.last ids))
                | _ -> None

            match ownType with
            | Some None -> true
            | Some(Some t) -> not (isNullable t)
            | None -> false

        /// `negated`: under an odd number of `not`s. A Nullable column of an
        /// exact type compared by `=`, `<`, `<=`, `>`, `>=` with a non-null
        /// value drops the NULL row in SQL (unknown) and in .NET (false)
        /// alike; negated, SQL still drops it (NOT unknown is unknown) where
        /// .NET keeps it, and so does `<>` - those stay Near.
        let comparison (negated: bool) (param: Ident) (op: string) (l: SynExpr) (r: SynExpr) =
            let isNullLiteral (e: SynExpr) =
                match unparen e with
                | SynExpr.Null _ -> true
                | _ -> false

            let againstValue (t: FSharpType) (v: SynExpr) =
                if not negated && op <> "op_Inequality" && nullableOfExact t && nonNullValue v then
                    Some Exact
                else
                    typeFidelity t

            match column param l, column param r with
            | Some t, None when isNullLiteral r && scalar t -> Some Exact
            | None, Some t when isNullLiteral l && scalar t -> Some Exact
            | Some lt, Some rt -> combine (typeFidelity lt) (typeFidelity rt)
            | Some t, None when value param r -> againstValue t r
            | None, Some t when value param l -> againstValue t l
            | _ -> None

        let rec predicate (negated: bool) (param: Ident) (e: SynExpr) =
            match unparen e with
            | Infix(("op_BooleanAnd" | "op_BooleanOr"), l, r) ->
                combine (predicate negated param l) (predicate negated param r)
            | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = inner) ->
                predicate (not negated) param inner
            | Infix(op, l, r) when comparisons.Contains op -> comparison negated param op l r
            | e ->
                match column param e with
                | Some t when isBool t -> Some Exact
                | _ -> None

        /// A value column: a projected value is the row's either way; a
        /// projected entity is not.
        let projection (param: Ident) (e: SynExpr) =
            match column param e with
            | Some t when scalar t -> Some Exact
            | _ -> None

        /// A stage's lambda: its fidelity as a filter or a projection, and
        /// its text without the argument's parentheses.
        let stage (isFilter: bool) (arg: SynExpr) =
            lambda1 arg
            |> Option.bind (fun (param, body) ->
                (if isFilter then
                     predicate false param body
                 else
                     projection param body)
                |> Option.map (fun f -> f, textOfRange source (unparen arg).Range))

        let resolvesToEnumerable (name: Ident) =
            match symbolAt name with
            | Some(:? FSharpMemberOrFunctionOrValue as v) -> declaringName v = "System.Linq.Enumerable"
            | _ -> false

        let isUnitArg (e: SynExpr) =
            match e with
            | SynExpr.Const(constant = SynConst.Unit) -> true
            | _ -> false

        /// Is the expression at `r` walked as a sequence and nothing else:
        /// the source of a `for ... in`, or piped into / applied to a
        /// `Seq`/`List`/`Array` module function?
        let consumedAsSequence (r: range) =
            let collectionFunction (e: SynExpr) =
                let rec head (e: SynExpr) =
                    match e with
                    | SynExpr.App(isInfix = false; funcExpr = inner) -> head inner
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; _ ])) ->
                        m.idText = "Seq" || m.idText = "List" || m.idText = "Array"
                    | _ -> false

                head e

            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.ForEach(enumExpr = src) -> unparen src |> fun s -> s.Range = r
                | PipeApp(lhs, rhs) -> (unparen lhs).Range = r && collectionFunction rhs
                | SynExpr.App(isInfix = false; funcExpr = fn; argExpr = arg) ->
                    (unparen arg).Range = r && collectionFunction fn
                | _ -> false)

        // ---- the method chain: `q.ToList().Where(f).Select(g)` ----

        /// A call of the chain: the method's name, its argument, the call's
        /// range, and where its receiver ends.
        let rec unroll (e: SynExpr) : (Ident option * range) * (Ident * SynExpr * range * pos) list =
            match e with
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ name ]))
                argExpr = arg) ->
                let b, calls = unroll recv
                b, calls @ [ name, arg, e.Range, recv.Range.End ]
            | SynExpr.App(
                isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                ids.Length >= 2
                ->
                let prefix = List.take (ids.Length - 1) ids
                let prefixRange = Range.unionRanges prefix.Head.idRange (List.last prefix).idRange
                (Some(List.last prefix), prefixRange), [ List.last ids, arg, e.Range, prefixRange.End ]
            | SynExpr.Ident id -> (Some id, e.Range), []
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                (Some(List.last ids), e.Range), []
            | e -> (None, e.Range), []

        let chainCandidates =
            [
                for _, expr in index.Exprs do
                    match unroll expr with
                    | (baseIdent, _), calls when calls.Length >= 2 ->
                        let calls = Array.ofList calls

                        for k in 0 .. calls.Length - 2 do
                            let name, arg, copyRange, receiverEnd = calls.[k]

                            let receiverType =
                                if k = 0 then
                                    baseIdent |> Option.bind typeOfName
                                else
                                    let previous, _, _, _ = calls.[k - 1]
                                    typeOfName previous

                            if
                                copyMethods.Contains name.idText
                                && isUnitArg arg
                                && receiverType |> Option.exists isQueryable
                                && resolvesToEnumerable name
                            then
                                // the run of translatable stages after the copy
                                let stages =
                                    calls.[k + 1 ..]
                                    |> Array.takeWhile (fun (n, a, _, _) ->
                                        (n.idText = "Where" || n.idText = "Select")
                                        && resolvesToEnumerable n
                                        && (stage (n.idText = "Where") a).IsSome)

                                if stages.Length > 0 then
                                    let lastIndex = k + stages.Length
                                    let _, _, lastRange, _ = calls.[lastIndex]

                                    let fidelity =
                                        stages
                                        |> Array.choose (fun (n, a, _, _) -> stage (n.idText = "Where") a)
                                        |> Array.map fst
                                        |> Array.reduce weaker

                                    // a copy of the same kind right after the stages is the one kept
                                    let copiedAfter =
                                        lastIndex + 1 < calls.Length
                                        && (let n, a, _, _ = calls.[lastIndex + 1]
                                            n.idText = name.idText && isUnitArg a)

                                    let range = Range.mkRange copyRange.FileName receiverEnd lastRange.End

                                    let moved =
                                        textOfRange
                                            source
                                            (Range.mkRange copyRange.FileName copyRange.End lastRange.End)

                                    let replacement = if copiedAfter then moved else moved + $".{name.idText}()"

                                    let names =
                                        stages
                                        |> Array.map (fun (n, _, _, _) -> n.idText)
                                        |> Array.distinct
                                        |> String.concat "/"

                                    // `AsEnumerable()` keeps the chain an IEnumerable; a copy kept
                                    // after the stages is the one it already ended in; a further
                                    // Enumerable call binds the same on a List; else the value must
                                    // go into a `for ... in` or a collection-module function
                                    let typeStable =
                                        name.idText = "AsEnumerable"
                                        || copiedAfter
                                        || (lastIndex + 1 < calls.Length
                                            && (let n, _, _, _ = calls.[lastIndex + 1]
                                                n.idText <> "Reverse" && resolvesToEnumerable n))
                                        || consumedAsSequence lastRange

                                    yield
                                        {
                                            Range = range
                                            OriginalText = textOfRange source range
                                            ReplacementText = replacement
                                            CopyName = name.idText + "()"
                                            Stages = names
                                            Fidelity = fidelity
                                            Fixable = true
                                            TypeStable = typeStable
                                        }
                    | _ -> ()
            ]

        // ---- the pipeline, behind the knob: `q |> Seq.toList |> List.filter f |> List.map g` ----

        let rec flatten (e: SynExpr) =
            match e with
            | PipeApp(lhs, rhs) ->
                let s, fs = flatten lhs
                s, fs @ [ rhs ]
            | e -> e, []

        let moduleFunction (e: SynExpr) =
            match e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) -> Some(m, f)
            | _ -> None

        let resolvesToModule (m: Ident) (f: Ident) =
            match moduleNames.TryFind m.idText, symbolAt f with
            | Some full, Some(:? FSharpMemberOrFunctionOrValue as v) -> OptionModule.enclosingFullName v = full
            | _ -> false

        let linqOpen = opensNamespace source "System.Linq"

        let pipelineCandidates =
            [
                if pipelines then
                    for _, expr in index.Exprs do
                        match flatten expr with
                        | src, copy :: stages when not stages.IsEmpty ->
                            let srcType =
                                match unparen src with
                                | SynExpr.Ident id -> typeOfName id
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                    typeOfName (List.last ids)
                                | _ -> None

                            match moduleFunction copy with
                            | Some(m, f) when
                                copyFunctions.ContainsKey((m.idText, f.idText))
                                && resolvesToModule m f
                                && srcType |> Option.exists isQueryable
                                ->
                                let collection = copyFunctions.[(m.idText, f.idText)]

                                // every stage of THIS pipeline node qualifies; a
                                // longer node whose extra stage does not is not a
                                // candidate, and the shorter one is
                                let judged =
                                    stages
                                    |> List.map (fun s ->
                                        match s with
                                        | SynExpr.App(isInfix = false; funcExpr = fn; argExpr = arg) ->
                                            match moduleFunction fn with
                                            | Some(sm, sf) when
                                                sm.idText = collection
                                                && (sf.idText = "filter" || sf.idText = "map")
                                                && resolvesToModule sm sf
                                                ->
                                                stage (sf.idText = "filter") arg
                                                |> Option.map (fun (fid, text) ->
                                                    fid,
                                                    (if sf.idText = "filter" then "Where" else "Select"),
                                                    text,
                                                    $"{sm.idText}.{sf.idText}")
                                            | _ -> None
                                        | _ -> None)

                                if judged |> List.forall Option.isSome then
                                    let judged = judged |> List.choose id
                                    let fidelity = judged |> List.map (fun (f, _, _, _) -> f) |> List.reduce weaker

                                    let calls =
                                        judged |> List.map (fun (_, m, t, _) -> $".{m}({t})") |> String.concat ""

                                    let srcText = textOfRange source src.Range
                                    let copyText = textOfRange source copy.Range

                                    // a pipeline laid out across lines keeps the copy on its own line
                                    let separator =
                                        if expr.Range.StartLine = expr.Range.EndLine then
                                            " "
                                        else
                                            let line = source.GetLineString(copy.Range.StartLine - 1)
                                            "\n" + line.Substring(0, line.Length - line.TrimStart().Length)

                                    yield
                                        {
                                            Range = expr.Range
                                            OriginalText = textOfRange source expr.Range
                                            ReplacementText = $"{srcText}{calls}{separator}|> {copyText}"
                                            CopyName = copyText
                                            Stages =
                                                judged
                                                |> List.map (fun (_, _, _, n) -> n)
                                                |> List.distinct
                                                |> String.concat "/"
                                            Fidelity = fidelity
                                            Fixable = linqOpen
                                            // the copy stays the last step: a list stays a list
                                            TypeStable = true
                                        }
                            | _ -> ()
                        | _ -> ()
            ]

        // the widest candidate of a chain: a pipeline node or a call nested
        // in a longer qualifying one is that one's part
        let all = chainCandidates @ pipelineCandidates

        all
        |> List.filter (fun s ->
            not (
                all
                |> List.exists (fun o -> o.Range <> s.Range && Range.rangeContainsRange o.Range s.Range)
            ))
        |> List.distinctBy (fun s -> s.Range)
