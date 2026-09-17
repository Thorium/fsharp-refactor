/// FR0156 (idiom): a ResizeArray that loops fill one `Add` at a time and
/// the rest of the scope only reads is a list expression.
///
///     let ranges = ResizeArray<range>()          let ranges =
///                                                    [
///     for _, e in index.Exprs do                         for _, e in index.Exprs do
///         match e with                                       match e with
///         | SynExpr.Record _ -> ranges.Add e.Range           | SynExpr.Record _ -> e.Range
///         | _ -> ()                                          | _ -> ()
///     for _, p in index.Pats do                          for _, p in index.Pats do
///         if isList p then ranges.Add p.Range                if isList p then p.Range
///                                                    ]
///     List.ofSeq ranges                          ranges
///
/// The loops move into the brackets as they are — guards, matches, nested
/// loops, `let`s and the statements around each `Add` included — and each
/// `Add` becomes the implicit yield of its argument. An `AddRange` loop is
/// FR0030's, and a ResizeArray handed to a walker's callback or read
/// between its loops has no sequence to write, and stays.
///
/// A LIST is what comes out: `List.ofSeq acc` becomes `acc`, and
/// `Array.ofSeq acc`, `for x in acc`, an upcast to seq and every function
/// taking a `seq<_>` keep working on it. Measured in PerfClaims (.NET 10,
/// 1000 ints, two thirds kept): the list expression collects through
/// FSharp.Core's ListCollector, no growth-doubling copies and no final
/// `List.ofSeq` copy, 20% faster on 30% less allocation than the loop. A
/// drain that wants an ARRAY - an index, `Count`, `ToArray()`,
/// `Array.ofSeq` - stands the rule down: the array expression's
/// ArrayCollector measured 1.6x the loop's time on the same allocation,
/// and `Array.choose` the same time on twice the allocation (a Some per
/// kept element), so the ResizeArray plus `ToArray()` is the fastest
/// spelling of that and keeps it.
///
/// Safety rules:
///   - `acc` is a local `let` of an EMPTY `ResizeArray`/`List<T>`, alone
///     on its line; `Add` resolves to List`1.Add (typed)
///   - every `Add` sits in statement position of a `for` loop that is a
///     statement of the same block, under nothing but `if`, `match`,
///     `let`, nested loops and `;` — not in a lambda, an object
///     expression, a `try`, a condition or an argument
///   - the feeding loops are consecutive statements; what stands between
///     the `let` and the first loop does not mention `acc`
///   - the loops hold no other collection's `Add`, and none of the
///     computation-expression forms a list expression cannot host
///   - every later use is a list-shaped drain — `List.ofSeq`, `Seq.toList`,
///     `for x in acc`, an upcast to seq, or an argument to a FUNCTION
///     whose parameter is `seq<_>` (typed); an array-shaped one (an index,
///     `Count`, `ToArray()`, `Array.ofSeq`), a method call, a binding, a
///     return of the ResizeArray itself, or any mutation stands the rule
///     down
///   - the element type is closed — a value type, a record, a union, a
///     tuple, a string, a function or a `[<Sealed>]` class: the `Add`
///     method upcast its argument to an interface or base class where a
///     yield does not
///   - the loops span no `#if` and no multi-line literal
module FSharp.Refactor.AccumulatorLoop

open System
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Edit =
    {
        Range: range
        Original: string
        Replacement: string
    }

type Suggestion =
    {
        Name: string
        /// The `let` that declares the accumulator.
        Range: range
        Edits: Edit list
    }

/// `recv.Add arg` — the receiver's identifiers, the Add identifier and the
/// argument.
[<return: Struct>]
let private (|AddCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) as recv; argExpr = arg) when
        ids.Length >= 2 && (List.last ids).idText = "Add" && isSingleLine recv.Range
        ->
        ValueSome(List.take (ids.Length - 1) ids, List.last ids, arg)
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.DotGet(expr = SynExpr.Ident receiver; longDotId = SynLongIdent(id = [ addIdent ]))
        argExpr = arg) when addIdent.idText = "Add" -> ValueSome([ receiver ], addIdent, arg)
    | _ -> ValueNone

/// `ResizeArray()`, `ResizeArray<T>()`, `List<T>()`, `new ResizeArray<T>()`:
/// an empty one. A copy-constructed `ResizeArray(xs)` starts full, and the
/// list expression would start empty.
let private isEmptyConstruction (e: SynExpr) =
    let rec constructorName (f: SynExpr) =
        match f with
        | SynExpr.Ident id -> id.idText = "ResizeArray" || id.idText = "List"
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
            (match List.tryLast ids with
             | Some id -> id.idText = "ResizeArray" || id.idText = "List"
             | None -> false)
        | SynExpr.TypeApp(expr = inner) -> constructorName inner
        | _ -> false

    match e with
    | SynExpr.App(funcExpr = f; argExpr = SynExpr.Const(SynConst.Unit, _)) -> constructorName f
    | SynExpr.New(expr = SynExpr.Const(SynConst.Unit, _)) -> true
    | _ -> false

/// The type argument the declaration spelled — `ResizeArray<int64>()`,
/// `new List<string option>()` — as an annotation for the list: the `Add`
/// method converted its argument to it (an `int` literal to `int64`, an F#
/// 6 type-directed conversion), and a yield with no expected type would
/// not. A non-atomic type is parenthesised, since `int * string list` is a
/// tuple of a list. None for an inferred `ResizeArray()` or a `<_>`.
let private declaredElementType (source: ISourceText) (construction: SynExpr) =
    let rec typeArg (f: SynExpr) =
        match f with
        | SynExpr.TypeApp(typeArgs = [ t ]) -> Some t
        | SynExpr.App(funcExpr = inner) -> typeArg inner
        | SynExpr.New(targetType = SynType.App(typeArgs = [ t ])) -> Some t
        | _ -> None

    typeArg construction
    |> Option.filter (fun t -> isSingleLine t.Range)
    |> Option.map (fun t -> textOfRange source t.Range)
    |> Option.filter (fun text -> text <> "_")
    |> Option.map (fun text ->
        if text |> Seq.exists (fun c -> c = ' ' || c = '*' || c = '-') then
            $"({text})"
        else
            text)

let private symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)
    check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])

let private sameSpan (a: range) (b: range) = a.Start = b.Start && a.End = b.End

/// The defining entity's full name without a generic arity suffix — FCS
/// spells `List<T>` as "System.Collections.Generic.List" through
/// `FSharpSymbol.FullName` and as "...List`1" through `TryFullName`.
let private entityName (t: FSharpType) =
    if t.HasTypeDefinition then
        let name = OptionModule.fullNameOf t.TypeDefinition

        match name.IndexOf '`' with
        | -1 -> name
        | i -> name.Substring(0, i)
    else
        ""

/// The element type of a `List<T>` local, when the local is one.
let private elementType (check: FSharpCheckFileResults) (source: ISourceText) (acc: Ident) =
    match symbolAt check source acc with
    | Some u ->
        match u.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v ->
            try
                let t = OptionModule.stripAbbreviations v.FullType

                if
                    t.HasTypeDefinition
                    && entityName t = "System.Collections.Generic.List"
                    && t.GenericArguments.Count = 1
                then
                    Some(u.Symbol, t.GenericArguments.[0])
                else
                    None
            with _ -> // an unresolved type stands the rule down; fsharpanalyzer: ignore-line FR0055
                None
        | _ -> None
    | None -> None

/// Can a yield of the element stand in for the `Add`? `Add` takes its
/// argument through a method call, which upcasts to an interface or a base
/// class; a yield fixes the list's type at the first element and rejects
/// the second. Closed types have no subtypes to upcast from.
let private closedElementType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        if t.IsGenericParameter || t.IsTupleType || t.IsFunctionType || t.IsAnonRecordType then
            true
        elif t.HasTypeDefinition then
            let e = t.TypeDefinition

            e.IsValueType
            || e.IsFSharpRecord
            || e.IsFSharpUnion
            || e.IsEnum
            || e.IsDelegate
            || e.IsFSharpExceptionDeclaration
            || (OptionModule.fullNameOf e = "System.String")
            || e.Attributes
               |> Seq.exists (fun a ->
                   a.AttributeType.DisplayName = "SealedAttribute"
                   || a.AttributeType.DisplayName = "Sealed")
        else
            false
    with _ -> // what cannot be read is not closed; fsharpanalyzer: ignore-line FR0055
        false

/// Does the Add identifier resolve to List<'T>.Add?
let private resolvesToListAdd (check: FSharpCheckFileResults) (source: ISourceText) (addIdent: Ident) =
    match symbolAt check source addIdent with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            (OptionModule.enclosingFullName value).StartsWith "System.Collections.Generic.List`"
        | _ -> false
    | None -> false

/// The statements of a block, in order: `a; b; c` and the `let`s between
/// them, each a `let` counting as a statement of its own.
type private Statement =
    | Loop of SynExpr
    | Binding of range
    | Other of SynExpr

let rec private statementsOf (e: SynExpr) : Statement list =
    match e with
    | SynExpr.Sequential(expr1 = a; expr2 = b) -> statementsOf a @ statementsOf b
    | LetOrUseE lou ->
        let bindings = lou.Bindings
        let body = lou.Body

        let r =
            match bindings with
            | [] -> e.Range
            | _ ->
                Range.unionRanges (List.head bindings).RangeOfBindingWithRhs (List.last bindings).RangeOfBindingWithRhs

        Binding r :: statementsOf body
    | SynExpr.Do(expr = inner) -> statementsOf inner
    | SynExpr.ForEach _
    | SynExpr.For _
    // `[ while cond do ... ]` is a list expression too, its condition
    // and the mutable it steps read and assigned inline: the expression
    // compiles to a loop over a collector, not to a closure
    | SynExpr.While _ -> [ Loop e ]
    | other -> [ Other other ]

let private rangeOfStatement (s: Statement) =
    match s with
    | Loop e
    | Other e -> e.Range
    | Binding r -> r

/// The computation-expression forms a list expression cannot host, and
/// the `try` forms that need F# 8 inside one.
let private hostileToListExpr (e: SynExpr) =
    match e with
    | LetOrUseE lou when lou.IsBang || lou.IsUse -> true
    | SynExpr.DoBang _
    | SynExpr.YieldOrReturn _
    | SynExpr.YieldOrReturnFrom _
    | SynExpr.MatchBang _
    | SynExpr.TryWith _
    | SynExpr.TryFinally _ -> true
    | _ -> false

/// Is `useRange` in statement position under `loop`: reached from the loop's
/// body through nothing but `;`, `if` branches, match arms, `let` bodies
/// and nested loop bodies? A condition, a scrutinee, a guard, a binding's
/// value, a lambda or an argument is not a statement.
let private inStatementPosition (loop: SynExpr) (useRange: range) =
    let contains (e: SynExpr) =
        Range.rangeContainsRange e.Range useRange

    let rec walk (e: SynExpr) =
        if sameSpan e.Range useRange then
            true
        else
            match e with
            | SynExpr.Sequential(expr1 = a; expr2 = b) -> (contains a && walk a) || (contains b && walk b)
            | SynExpr.IfThenElse(thenExpr = t; elseExpr = el) ->
                (contains t && walk t)
                || (match el with
                    | Some el -> contains el && walk el
                    | None -> false)
            | SynExpr.Match(clauses = clauses) ->
                clauses
                |> List.exists (fun (SynMatchClause(resultExpr = body)) -> contains body && walk body)
            | LetOrUseE lou -> contains lou.Body && walk lou.Body
            | SynExpr.ForEach(bodyExpr = body)
            | SynExpr.For(doBody = body)
            | SynExpr.While(doExpr = body)
            | SynExpr.Do(expr = body)
            | SynExpr.Paren(expr = body) -> contains body && walk body
            | _ -> false

    match loop with
    | SynExpr.ForEach(bodyExpr = body)
    | SynExpr.For(doBody = body)
    | SynExpr.While(doExpr = body) -> contains body && walk body
    | _ -> false

/// How a use of the accumulator after the loops reads it.
type private Drain =
    /// `List.ofSeq acc`, `Seq.toList acc`, piped or applied: the whole
    /// expression becomes `acc` when the result is a list.
    | ToList of range
    /// `Array.ofSeq acc`, `Seq.toArray acc`, `acc.ToArray()`: wants an array,
    /// which stands the rule down.
    | ToArray of range
    /// `acc.Count`: an O(1) read the list has not got; stands the rule down.
    | Count of range
    /// `acc.[i]` / `acc[i]`: wants an array; stands the rule down.
    | Indexed
    /// A read the list and the array both satisfy as they are.
    | AsSeq

/// The `f`, the whole application and the argument's position, for `f acc`
/// (position counted from the first argument) and `acc |> f` (-1: the
/// last parameter), given the use's ancestors.
let private applicationOf (path: SyntaxNode list) (useRange: range) =
    // the whole application, or the parentheses wrapping exactly it:
    // `(List.ofSeq acc)` becomes `acc`, not `(acc)`
    let whole (app: SynExpr) (rest: SyntaxNode list) =
        match rest with
        | SyntaxNode.SynExpr(SynExpr.Paren(expr = inner) as p) :: _ when sameSpan inner.Range app.Range -> p.Range
        | _ -> app.Range

    match path with
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = arg) as app) :: rest when
        sameSpan arg.Range useRange
        ->
        // `f a b acc`: the Apps inside `f` are the arguments before
        let rec before (e: SynExpr) (n: int) =
            match e with
            | SynExpr.App(isInfix = false; funcExpr = inner) -> before inner (n + 1)
            | SynExpr.TypeApp(expr = inner) -> before inner n
            | _ -> n

        Some(f, whole app rest, before f 0)
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = IdentName "op_PipeRight"; argExpr = lhs)) :: SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; argExpr = f) as app) :: rest when sameSpan lhs.Range useRange -> Some(f, whole app rest, -1)
    | _ -> None

/// The FUNCTION an application's head resolves to: `String.concat ", " acc`
/// applies `String.concat ", "`, whose own head names the function. A
/// method, whose overloads the argument type would choose between, is None.
let private headFunction (check: FSharpCheckFileResults) (source: ISourceText) (f: SynExpr) =
    let rec ident (f: SynExpr) =
        match f with
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> List.tryLast ids
        | SynExpr.TypeApp(expr = inner)
        | SynExpr.App(isInfix = false; funcExpr = inner) -> ident inner
        | _ -> None

    match ident f |> Option.bind (symbolAt check source) with
    | Some u ->
        match u.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v when not v.IsMember -> Some v
        | _ -> None
    | None -> None

/// Does the function's parameter at this position take a `seq<_>`? The one
/// question that makes a list or an array as welcome as the ResizeArray.
let private seqParameter (check: FSharpCheckFileResults) (source: ISourceText) (f: SynExpr) (position: int) : bool =
    match headFunction check source f with
    | Some v ->
        (try
            let groups = v.CurriedParameterGroups

            let position = if position < 0 then groups.Count - 1 else position

            position >= 0
            && position < groups.Count
            && groups.[position].Count = 1
            && (let t = OptionModule.stripAbbreviations groups.[position].[0].Type

                entityName t = "System.Collections.Generic.IEnumerable")
         with _ -> // an unreadable signature is no seq parameter; fsharpanalyzer: ignore-line FR0055
             false)
    | None -> false

let private coreListConversions = set [ "List.ofSeq"; "Seq.toList" ]
let private coreArrayConversions = set [ "Array.ofSeq"; "Seq.toArray" ]

/// Is this FSharp.Core's own conversion, not a `List` module of the project's
/// that happens to spell `ofSeq`?
let private coreConversion (check: FSharpCheckFileResults) (source: ISourceText) (f: SynExpr) =
    match headFunction check source f with
    | Some v -> (OptionModule.fullNameOf v).StartsWith "Microsoft.FSharp.Collections."
    | None -> false

let private functionText (f: SynExpr) =
    match f with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> identText ids
    | SynExpr.Ident id -> id.idText
    | _ -> ""

/// Classify a read of the accumulator after its loops. `node` is the
/// expression the use is: the bare identifier, or the `acc.Member` path it
/// heads. None: a use the rewrite cannot keep — the rule stands down.
let rec private classifyDrain
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (path: SyntaxNode list)
    (node: SynExpr)
    : Drain option =
    match node with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; m ])) ->
        match m.idText, path with
        | "Count", _ -> Some(Count m.idRange)
        | "ToArray", SyntaxNode.SynExpr(SynExpr.App(argExpr = SynExpr.Const(SynConst.Unit, _)) as call) :: _ ->
            Some(ToArray call.Range)
        | _ -> None
    | SynExpr.LongIdent _ -> None
    | _ ->
        let useRange = node.Range

        match path with
        | SyntaxNode.SynExpr(SynExpr.Paren(expr = e) as paren) :: rest when sameSpan e.Range useRange ->
            // `(acc)` reads as `acc` wherever it stands
            classifyDrain check source rest paren
        | SyntaxNode.SynExpr(SynExpr.DotIndexedGet(objectExpr = recv)) :: _ when sameSpan recv.Range useRange ->
            Some Indexed
        // acc[i] — F# 6 indexing parses as an atomic application
        | SyntaxNode.SynExpr(SynExpr.App(
            flag = ExprAtomicFlag.Atomic; funcExpr = recv; argExpr = SynExpr.ArrayOrListComputed(isArray = false))) :: _ when
            sameSpan recv.Range useRange
            ->
            Some Indexed
        | SyntaxNode.SynExpr(SynExpr.ForEach(enumExpr = e)) :: _ when sameSpan e.Range useRange -> Some AsSeq
        | SyntaxNode.SynExpr(SynExpr.Upcast(expr = e)) :: _
        | SyntaxNode.SynExpr(SynExpr.InferredUpcast(expr = e)) :: _ when sameSpan e.Range useRange -> Some AsSeq
        | _ ->
            match applicationOf path useRange with
            | Some(f, whole, position) ->
                let name = functionText f

                if coreListConversions.Contains name && coreConversion check source f then
                    Some(ToList whole)
                elif coreArrayConversions.Contains name && coreConversion check source f then
                    Some(ToArray whole)
                elif seqParameter check source f position then
                    Some AsSeq
                else
                    None
            | None -> None

/// The yield that stands in for `acc.Add arg`, placed where the call stood:
/// the argument, its outer parentheses dropped where the bare expression
/// reads the same at statement level, and an argument written on the lines
/// below the `Add` moved up to the call's own column — left where it was,
/// a record standing deeper than a `let` above it reads as that let's
/// continuation. None where a line cannot move (a multi-line literal, or
/// a line that would land left of the statement).
let private yieldText (explicitYield: bool) (source: ISourceText) (call: range) (arg: SynExpr) =
    let rec bare (arg: SynExpr) =
        match arg with
        | SynExpr.Paren(expr = inner) ->
            match inner with
            | SynExpr.Paren _ -> bare inner
            | SynExpr.Ident _
            | SynExpr.LongIdent _
            | SynExpr.Const _
            | SynExpr.App _
            | SynExpr.DotGet _
            | SynExpr.DotIndexedGet _
            | SynExpr.Record _
            | SynExpr.AnonRecd _
            | SynExpr.ArrayOrList _
            | SynExpr.ArrayOrListComputed _
            | SynExpr.New _
            | SynExpr.Upcast _
            | SynExpr.TypeApp _
            | SynExpr.InterpolatedString _ -> inner
            | _ -> arg
        | _ -> arg

    let bare = bare arg
    let column = call.StartColumn

    reindentBlock column bare.Range.StartColumn (textOfRange source bare.Range)
    |> Option.filter (fun moved ->
        moved.Split '\n'
        |> Array.skip 1
        |> Array.forall (fun l -> String.IsNullOrWhiteSpace l || l.Length - l.TrimStart().Length >= column))
    // `yield e` for a compiler older than F# 4.7's implicit yields; the
    // keyword pushes a continuation line no further than its own width
    // requires, since those lines keep their columns
    |> Option.map (fun moved -> (if explicitYield then "yield " else "") + moved.Substring column)

/// The region's lines with the `Add` calls replaced by their yields, as one
/// text starting at the region's first column. An edit may span lines and
/// its text may hold line breaks: the lines are rebuilt from the bottom up.
let private regionWithYields (source: ISourceText) (region: range) (adds: (range * string) list) =
    let mutable lines =
        [|
            for line in region.StartLine .. region.EndLine -> source.GetLineString(line - 1)
        |]

    let last = lines.Length - 1
    lines.[last] <- lines.[last].Substring(0, min lines.[last].Length region.EndColumn)

    for r, text in adds |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn) do
        let startLine = r.StartLine - region.StartLine
        let endLine = r.EndLine - region.StartLine
        let prefix = lines.[startLine].Substring(0, r.StartColumn)

        let suffix =
            if endLine < lines.Length then
                lines.[endLine].Substring(min lines.[endLine].Length r.EndColumn)
            else
                ""

        let merged = (prefix + text + suffix).Split '\n'

        let after =
            if endLine < lines.Length then
                lines.[endLine + 1 ..]
            else
                [||]

        lines <- Array.concat [ lines.[.. startLine - 1]; merged; after ]

    lines.[0] <- lines.[0].Substring region.StartColumn
    String.concat "\n" lines

/// `let acc = ResizeArray()` with nothing else on the line: the line can go.
let private aloneOnItsLine (source: ISourceText) (binding: SynBinding) =
    let r = binding.RangeOfBindingWithRhs
    let line = (source.GetLineString(r.StartLine - 1)).Trim()

    line.StartsWith "let "
    && line.Substring(4).TrimStart() = (textOfRange source r).Trim()

/// Find the accumulators whose loops are a list expression. Requires typed
/// check results.
/// The suggestion for one candidate accumulator, when its loops and drains
/// allow one.
let private suggestionFor
    (index: AstIndex.Index)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (acc: Ident)
    (binding: SynBinding)
    (construction: SynExpr)
    (body: SynExpr)
    (arrays: bool)
    (explicitYield: bool)
    : Suggestion option =
    // the expression a use IS — the identifier, or the `acc.Member` path
    // it heads — with its ancestors
    let nodeAt (r: range) =
        index.Exprs
        |> Array.tryFind (fun (_, e) ->
            match e with
            | SynExpr.Ident id -> sameSpan id.idRange r
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> sameSpan first.idRange r
            | _ -> false)

    // `acc.Add arg` whose receiver is exactly this use
    let addCallAt (r: range) =
        index.Exprs
        |> Array.tryPick (fun (_, e) ->
            match e with
            | AddCall([ recv ], addIdent, arg) when sameSpan recv.idRange r -> Some(e, addIdent, arg)
            | _ -> None)

    match elementType check source acc with
    | Some(symbol, element) when closedElementType element ->
        let uses =
            check.GetUsesOfSymbolInFile symbol
            |> Array.filter (fun u -> not u.IsFromDefinition)
            |> Array.map (fun u -> u.Range)
            |> Array.sortBy (fun r -> r.StartLine, r.StartColumn)

        let addCalls = uses |> Array.map (fun r -> r, addCallAt r)
        let statements = statementsOf body

        // the loops that feed the accumulator: a `for` statement with an
        // `Add` on it inside
        let feeding =
            statements
            |> List.indexed
            |> List.choose (fun (i, s) ->
                match s with
                | Loop loop when
                    addCalls
                    |> Array.exists (fun (r, call) -> call.IsSome && Range.rangeContainsRange loop.Range r)
                    ->
                    Some(i, loop)
                | _ -> None)

        let contiguous =
            match feeding with
            | [] -> false
            | (first, _) :: _ -> feeding |> List.map fst = [ first .. first + feeding.Length - 1 ]

        if not contiguous then
            None
        else
            let region =
                Range.unionRanges (snd feeding.Head).Range (snd (List.last feeding)).Range

            let loopOf (r: range) =
                feeding |> List.tryFind (fun (_, loop) -> Range.rangeContainsRange loop.Range r)

            // every use inside a feeding loop is a statement-position
            // `acc.Add arg` whose argument leaves `acc` alone: its yield.
            // Every use before the loops stands the rule down; the rest
            // are drains
            let inLoops, outside =
                addCalls |> Array.toList |> List.partition (fun (r, _) -> (loopOf r).IsSome)

            let yields =
                inLoops
                |> List.map (fun (r, call) ->
                    match call, loopOf r with
                    | Some(e, addIdent, arg), Some(_, loop) when
                        inStatementPosition loop e.Range
                        && resolvesToListAdd check source addIdent
                        && not (uses |> Array.exists (fun v -> Range.rangeContainsRange arg.Range v))
                        ->
                        yieldText explicitYield source e.Range arg
                        |> Option.map (fun text -> e.Range, text)
                    | _ -> None)

            let quietBefore =
                outside |> List.forall (fun (r, _) -> Position.posGeq r.Start region.End)

            let hostile =
                index.Exprs
                |> Array.exists (fun (_, e) ->
                    Range.rangeContainsRange region e.Range
                    && (hostileToListExpr e
                        // another collection filled by the same loop would
                        // have to move with it
                        || (match e with
                            | AddCall(recv :: _, _, _) -> recv.idText <> acc.idText
                            | _ -> false)))

            if
                not quietBefore
                || hostile
                || not (yields |> List.forall Option.isSome)
                || spansDirective source region
            then
                None
            else
                let drains =
                    outside
                    |> List.map (fun (r, _) ->
                        match nodeAt r with
                        | Some(path, node) -> classifyDrain check source path node
                        | None -> None)

                // What the drains ask for decides the shape, and PerfClaims decides
                // whether the shape is worth writing (.NET 10, 1000 ints):
                //   - a `List.ofSeq` drain: the list expression beats the fill
                //     plus the copy (20% faster, 30% less allocation) - the one
                //     rewrite that wins, and the default
                //   - an index, `Count` (whose list spelling `Length` walks the
                //     list) or `ToArray()`: the array expression runs 1.6x the
                //     fill, the ResizeArray plus `ToArray()` IS the fastest
                //     spelling of an array built one element at a time
                //   - a seq-only drain: nothing converted the ResizeArray, so the
                //     bare fill is the baseline and both expressions lose to it
                //     (the list 2.4x on 2.5x the allocation, the array 2x)
                // `{ "FR0156": { "arrays": true } }` buys the array shape for the
                // last two at that price; a lazy `seq { }` is never written
                let wantsArray =
                    drains
                    |> List.exists (fun d ->
                        match d with
                        | Some Indexed
                        | Some(ToArray _)
                        | Some(Count _) -> true
                        | _ -> false)

                let wantsList =
                    drains
                    |> List.exists (fun d ->
                        match d with
                        | Some(ToList _) -> true
                        | _ -> false)

                let shape =
                    if not (drains |> List.forall Option.isSome) then
                        None
                    elif wantsArray || not wantsList then
                        (if arrays then Some true else None)
                    else
                        Some false

                match shape with
                | None -> None
                | Some wantsArray ->
                    let drains = drains |> List.map Option.get
                    let indent = region.StartColumn
                    let opening, closing = if wantsArray then "[|", "|]" else "[", "]"

                    regionWithYields source region (yields |> List.map Option.get)
                    |> reindentBlock (indent + 8) indent
                    |> Option.map (fun moved ->
                        let pad n = String(' ', n)

                        let annotation =
                            match declaredElementType source construction with
                            | Some t when wantsArray -> $": {t}[]"
                            | Some t -> $": {t} list"
                            | None -> ""

                        let replacement =
                            String.concat
                                "\n"
                                [
                                    $"let {acc.idText}{annotation} ="
                                    $"{pad (indent + 4)}{opening}"
                                    moved
                                    $"{pad (indent + 4)}{closing}"
                                ]

                        let declLine = binding.RangeOfBindingWithRhs.StartLine

                        let declRange =
                            Range.mkRange region.FileName (Position.mkPos declLine 0) (Position.mkPos (declLine + 1) 0)

                        let edit (r: range) (replacement: string) =
                            {
                                Range = r
                                Original = textOfRange source r
                                Replacement = replacement
                            }

                        let drainEdits =
                            drains
                            |> List.choose (fun d ->
                                match d with
                                | ToList r when not wantsArray -> Some(edit r acc.idText)
                                | ToArray r when wantsArray -> Some(edit r acc.idText)
                                | Count r when wantsArray -> Some(edit r "Length")
                                | _ -> None)

                        {
                            Name = acc.idText
                            Range = binding.RangeOfBindingWithRhs
                            Edits = edit declRange "" :: edit region replacement :: drainEdits
                        })
    | _ -> None

/// Find the accumulators whose loops are a list expression. Requires typed
/// check results.
/// `arrays`: also rewrite an accumulator drained as an array, into an array
/// expression - slower than the ResizeArray it replaces, off by default.
/// `explicitYield`: spell each yield `yield e`, for a compiler older than F#
/// 4.7's implicit yields.
let findWith
    (arrays: bool)
    (explicitYield: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | LetOrUseE lou when not lou.IsRecursive && not lou.IsBang && not lou.IsUse ->
                    match lou.Bindings with
                    | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = acc)); expr = construction) as binding ] when
                        isEmptyConstruction construction
                        && binding.RangeOfBindingWithRhs.StartLine = binding.RangeOfBindingWithRhs.EndLine
                        // the declaration alone on its line: the line goes — and not
                        // from between two directives
                        && aloneOnItsLine source binding
                        && not (
                            spansDirective
                                source
                                (Range.mkRange
                                    binding.RangeOfBindingWithRhs.FileName
                                    (Position.mkPos (max 1 (binding.RangeOfBindingWithRhs.StartLine - 1)) 0)
                                    (Position.mkPos (binding.RangeOfBindingWithRhs.StartLine + 1) 0))
                        )
                        ->
                        match
                            suggestionFor index source check acc binding construction lou.Body arrays explicitYield
                        with
                        | Some s -> s
                        | None -> ()
                    | _ -> ()
                | _ -> ()
        ]

/// The default: list expressions only.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    findWith false false parseTree source check
