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
///     yield does not; a delegate is not closed either, since `Add`
///     converted a lambda argument to it where a yield does not
///   - every other statement of the loops is unit (typed): a discarded
///     non-unit call in statement position would become a yield
///   - the loops read no byref-like value (a Span): the list expression
///     may not capture one
///   - the loops span no `#if` and no multi-line literal
///
/// The `let mutable` LIST is the same shape with the copy made per
/// element instead of once:
///
///     let mutable xs = []                        let xs =
///     for i in ys do                                 [
///         let r = f i                                    for i in ys do
///         xs <- List.append xs [ r ]                         let r = f i
///     xs                                                     r
///                                                    ]
///                                                xs
///
/// `xs <- xs @ [ e ]` and `xs <- List.append xs [ e ]` (FSharp.Core's,
/// typed) are the feeds, each yielding its one element; `xs <- e :: xs`
/// feeds the front and comes out reversed, so that direction qualifies
/// only when every later read is FSharp.Core's `List.rev xs`, which
/// becomes `xs` - the expression yields in loop order. A list fed at both
/// ends has no order to yield in. The result is a list already, so every
/// later read stays as it is; an assignment after the loops (the result
/// is immutable), a `&xs`, or a read of `xs` inside its own loops stands
/// the rule down, and an annotation (`let mutable xs: T list = []`) is
/// kept on the result, since it typed the elements. `[]`, `List.empty`
/// and `List.Empty` start it. Measured in PerfClaims (1000 ints, two
/// thirds kept): 250x faster on 0.3% of the allocation for the append,
/// 1.5x on half for the cons-and-reverse. FR0050 leaves this shape to
/// this rule (a fold would keep the copy), and FR0051 notes it wherever
/// this rule cannot rewrite it.
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
        /// A `let mutable` list fed by appends (or conses read through
        /// `List.rev`), rather than a ResizeArray filled by `Add`.
        Mutable: bool
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

/// What a list feed's typed proof must resolve: `@` to FSharp.Core's
/// operator, `List.append` to its ListModule; `::` is syntax.
type private Proof =
    | Operator of Ident
    | ListModule of Ident
    | Syntax

/// `acc <- acc @ [ e ]`, `acc <- List.append acc [ e ]` and `acc <- e :: acc`:
/// the accumulator, the element, whether it went on the FRONT (a cons,
/// which leaves the list reversed) and the proof to resolve.
[<return: Struct>]
let private (|ListFeed|_|) (e: SynExpr) =
    // `[ e ]`: one element - not a range, a comprehension or a sequence
    let singleton (l: SynExpr) =
        match l with
        | SynExpr.ArrayOrList(isArray = false; exprs = [ elem ]) -> ValueSome elem
        | SynExpr.ArrayOrListComputed(isArray = false; expr = elem) ->
            match elem with
            | SynExpr.Sequential _
            | SynExpr.ForEach _
            | SynExpr.For _
            | SynExpr.While _
            | SynExpr.IndexRange _
            | SynExpr.IfThenElse _
            | SynExpr.Match _
            | SynExpr.YieldOrReturn _
            | SynExpr.YieldOrReturnFrom _
            | LetOrUseE _ -> ValueNone
            | _ -> ValueSome elem
        | _ -> ValueNone

    match e with
    | SynExpr.LongIdentSet(SynLongIdent(id = [ acc ]), rhs, _) ->
        match rhs with
        | SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = SynExpr.Ident lhs)
            argExpr = list) when op.idText = "op_Append" && lhs.idText = acc.idText ->
            singleton list |> ValueOption.map (fun elem -> acc, elem, false, Operator op)
        | SynExpr.App(
            funcExpr = SynExpr.App(
                funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = SynExpr.Ident lhs)
            argExpr = list) when m.idText = "List" && f.idText = "append" && lhs.idText = acc.idText ->
            singleton list |> ValueOption.map (fun elem -> acc, elem, false, ListModule f)
        // `::` is syntax, and nothing can redefine it
        | SynExpr.App(
            isInfix = true
            funcExpr = IdentName "op_ColonColon"
            argExpr = SynExpr.Tuple(exprs = [ elem; SynExpr.Ident rhsAcc ])) when rhsAcc.idText = acc.idText ->
            ValueSome(acc, elem, true, Syntax)
        | _ -> ValueNone
    | _ -> ValueNone

/// `[]`, `List.empty`, `List.Empty` (under an annotation or not): the empty
/// list a list expression starts from too.
[<TailCall>]
let rec private isEmptyList (e: SynExpr) =
    match e with
    | SynExpr.Typed(expr = inner)
    | SynExpr.Paren(expr = inner) -> isEmptyList inner
    | SynExpr.ArrayOrList(isArray = false; exprs = []) -> true
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) ->
        m.idText = "List" && (f.idText = "empty" || f.idText = "Empty")
    | _ -> false

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

/// Does a list feed's `@` or `List.append` resolve to FSharp.Core's? A
/// project's own `@` or `List` module would not append.
let private feedResolves (check: FSharpCheckFileResults) (source: ISourceText) (proof: Proof) =
    match proof with
    | Syntax -> true
    | Operator op -> OptionModule.resolvesToCoreOperator check source op
    | ListModule f ->
        let r = f.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ "List"; f.idText ]) with
        | Some u ->
            match u.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                // the module's logical name is `List`, its compiled one `ListModule`
                let name = OptionModule.fullNameOf v

                name = "Microsoft.FSharp.Collections.List.append"
                || name = "Microsoft.FSharp.Collections.ListModule.append"
            | _ -> false
        | None -> false

/// The symbol of a `let mutable` local whose type is an F# list.
let private listSymbol (check: FSharpCheckFileResults) (source: ISourceText) (acc: Ident) =
    match symbolAt check source acc with
    | Some u ->
        match u.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v ->
            try
                let t = OptionModule.stripAbbreviations v.FullType

                if
                    t.HasTypeDefinition
                    && t.TypeDefinition.TryFullName = Some "Microsoft.FSharp.Collections.FSharpList`1"
                then
                    Some u.Symbol
                else
                    None
            with _ -> // an unresolved type stands the rule down; fsharpanalyzer: ignore-line FR0055
                None
        | _ -> None
    | None -> None

/// Can a yield of the element stand in for the `Add`? `Add` takes its
/// argument through a method call, which upcasts to an interface or a base
/// class; a yield fixes the list's type at the first element and rejects
/// the second. Closed types have no subtypes to upcast from. A delegate
/// has none either, but the method call converted a lambda argument to it
/// (`acc.Add(fun () -> ...)` into a `ResizeArray<Action>`) where a yield
/// does not (FS0002), so it is not closed here.
let private closedElementType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        if t.IsGenericParameter || t.IsTupleType || t.IsFunctionType || t.IsAnonRecordType then
            true
        elif t.HasTypeDefinition then
            let e = t.TypeDefinition

            not e.IsDelegate
            && (e.IsValueType
                || e.IsFSharpRecord
                || e.IsFSharpUnion
                || e.IsEnum
                || e.IsFSharpExceptionDeclaration
                || (OptionModule.fullNameOf e = "System.String")
                || e.Attributes
                   |> Seq.exists (fun a ->
                       a.AttributeType.DisplayName = "SealedAttribute"
                       || a.AttributeType.DisplayName = "Sealed"))
        else
            false
    with _ -> // what cannot be read is not closed; fsharpanalyzer: ignore-line FR0055
        false

let private isUnitType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.TryFullName
            |> Option.exists (fun n -> n = "Microsoft.FSharp.Core.Unit" || n = "Microsoft.FSharp.Core.unit"))
    with _ -> // an unreadable type is not known to be unit; fsharpanalyzer: ignore-line FR0055
        false

/// Is this application (or bare value) in statement position provably
/// unit? Its head identifier's symbol gives the function's or member's
/// type, instantiated as this use instantiates it (`printfn "%d" x` is a
/// `TextWriterFormat<int -> unit> -> int -> unit` here), and one arrow is
/// peeled per argument applied. Anything the typed tree cannot name, or
/// names as anything but unit, is not: a discarded `d.TryAdd(x, x)` in the
/// loop would become a yield of its bool.
let private applicationIsUnit (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) =
    let rec head (e: SynExpr) (args: int) =
        match e with
        // `a + b` is `App(App(op, a), b)`, the inner one infix: both count
        | SynExpr.App(funcExpr = f) -> head f (args + 1)
        | SynExpr.TypeApp(expr = f)
        | SynExpr.Paren(expr = f) -> head f args
        | SynExpr.Ident id -> Some(id, args)
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids, args)
        | _ -> None

    let rec peel (t: FSharpType) (n: int) =
        if n <= 0 then
            Some t
        else
            let t = OptionModule.stripAbbreviations t

            if t.IsFunctionType && t.GenericArguments.Count = 2 then
                peel t.GenericArguments.[1] (n - 1)
            else
                None

    match head e 0 with
    | Some(id, args) ->
        match symbolAt check source id with
        | Some u ->
            match u.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                try
                    // a method's return type stands for its one argument
                    // group; a property's for none; a function's whole type
                    // loses one arrow per argument
                    let declared, arrows =
                        if v.IsProperty then
                            Some v.ReturnParameter.Type, args
                        elif v.IsMember then
                            (if args >= 1 then Some v.ReturnParameter.Type else None), args - 1
                        else
                            Some v.FullType, args

                    declared
                    |> Option.map (fun t ->
                        match u.GenericArguments with
                        | [] -> t
                        | inst -> t.Instantiate inst)
                    |> Option.bind (fun t -> peel t arrows)
                    |> Option.exists isUnitType
                with _ -> // an unreadable symbol is not known to be unit; fsharpanalyzer: ignore-line FR0055
                    false
            | _ -> false
        | None -> false
    | None -> false

/// Is every statement of the loop body unit, `acc`'s own `Add` calls
/// aside? In a list expression every statement-position expression that
/// is not unit is an implicit yield, where the loop merely discarded it:
/// the syntax settles an assignment, a nested loop, `()` and the branches
/// of `if` and `match`, and the typed tree the applications and values.
let private bodyStatementsAreUnit (check: FSharpCheckFileResults) (source: ISourceText) (acc: Ident) (loop: SynExpr) =
    let rec unit (e: SynExpr) =
        match e with
        | AddCall(recv :: _, _, _) when recv.idText = acc.idText -> true
        | SynExpr.Sequential(expr1 = a; expr2 = b) -> unit a && unit b
        | LetOrUseE lou -> unit lou.Body
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = el) -> unit t && (el |> Option.forall unit)
        | SynExpr.Match(clauses = clauses) ->
            clauses |> List.forall (fun (SynMatchClause(resultExpr = body)) -> unit body)
        | SynExpr.ForEach(bodyExpr = body)
        | SynExpr.For(doBody = body)
        | SynExpr.While(doExpr = body)
        | SynExpr.Do(expr = body)
        | SynExpr.Paren(expr = body) -> unit body
        | SynExpr.Const(SynConst.Unit, _)
        | SynExpr.Set _
        | SynExpr.LongIdentSet _
        | SynExpr.DotSet _
        | SynExpr.DotIndexedSet _
        | SynExpr.NamedIndexedPropertySet _
        | SynExpr.DotNamedIndexedPropertySet _
        | SynExpr.Assert _ -> true
        | SynExpr.App _
        | SynExpr.Ident _
        | SynExpr.LongIdent _
        | SynExpr.DotGet _
        | SynExpr.TypeApp _ -> applicationIsUnit check source e
        | _ -> false

    match loop with
    | SynExpr.ForEach(bodyExpr = body)
    | SynExpr.For(doBody = body)
    | SynExpr.While(doExpr = body) -> unit body
    | _ -> false

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
    /// `List.rev acc` / `acc |> List.rev` on a consed list accumulator: the
    /// list expression yields in loop order, and the whole becomes `acc`.
    | Reversed of range
    /// A read of a list accumulator that stays as it is.
    | Kept

/// What is accumulated.
[<RequireQualifiedAccess>]
type private Kind =
    /// `let acc = ResizeArray()` filled by `acc.Add e`.
    | ResizeArray
    /// `let mutable acc = []` fed by `acc <- acc @ [ e ]` (or `List.append`),
    /// or by `acc <- e :: acc` and read through `List.rev` alone.
    | List

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

        ValueSome(f, whole app rest, before f 0)
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = IdentName "op_PipeRight"; argExpr = lhs)) :: SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; argExpr = f) as app) :: rest when sameSpan lhs.Range useRange ->
        ValueSome(f, whole app rest, -1)
    | _ -> ValueNone

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
        | :? FSharpMemberOrFunctionOrValue as v when not v.IsMember -> ValueSome v
        | _ -> ValueNone
    | None -> ValueNone

/// Does the function's parameter at this position take a `seq<_>`? The one
/// question that makes a list or an array as welcome as the ResizeArray.
let private seqParameter (check: FSharpCheckFileResults) (source: ISourceText) (f: SynExpr) (position: int) : bool =
    match headFunction check source f with
    | ValueSome v ->
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
    | ValueNone -> false

let private coreListConversions = set [ "List.ofSeq"; "Seq.toList" ]
let private coreArrayConversions = set [ "Array.ofSeq"; "Seq.toArray" ]

/// Is this FSharp.Core's own conversion, not a `List` module of the project's
/// that happens to spell `ofSeq`?
let private coreConversion (check: FSharpCheckFileResults) (source: ISourceText) (f: SynExpr) =
    match headFunction check source f with
    | ValueSome v -> (OptionModule.fullNameOf v).StartsWith "Microsoft.FSharp.Collections."
    | ValueNone -> false

let private functionText (f: SynExpr) =
    match f with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> identText ids
    | SynExpr.Ident id -> id.idText
    | _ -> ""

/// Classify a read of the accumulator after its loops. `node` is the
/// expression the use is: the bare identifier, or the `acc.Member` path it
/// heads. None: a use the rewrite cannot keep — the rule stands down.
[<TailCall>]
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
            | ValueSome(f, whole, position) ->
                let name = functionText f

                if coreListConversions.Contains name && coreConversion check source f then
                    Some(ToList whole)
                elif coreArrayConversions.Contains name && coreConversion check source f then
                    Some(ToArray whole)
                elif seqParameter check source f position then
                    Some AsSeq
                else
                    None
            | ValueNone -> None

/// Classify a read of a LIST accumulator after its loops. The list is
/// already what the expression builds, so a read stays as it is; the consed
/// direction reads only through FSharp.Core's `List.rev`, which becomes the
/// bare name. An assignment's target is no expression node and never
/// reaches here (the caller stands down on it); a byref of the mutable
/// cannot be taken of the immutable result.
[<TailCall>]
let rec private classifyListDrain
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (cons: bool)
    (path: SyntaxNode list)
    (node: SynExpr)
    : Drain option =
    let useRange = node.Range

    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren(expr = e) as paren) :: rest when sameSpan e.Range useRange ->
        classifyListDrain check source cons rest paren
    | SyntaxNode.SynExpr(SynExpr.AddressOf _) :: _ -> None
    | _ when not cons -> Some Kept
    | _ ->
        match node with
        | SynExpr.LongIdent _ -> None
        | _ ->
            match applicationOf path useRange with
            | ValueSome(f, whole, _) when functionText f = "List.rev" && coreConversion check source f ->
                Some(Reversed whole)
            | _ -> None

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

    // `let mutable acc = []` too: the keyword sits before the binding's range
    let afterMutable (text: string) =
        let text = text.TrimStart()

        if text.StartsWith "mutable " then
            text.Substring(8).TrimStart()
        else
            text

    line.StartsWith "let "
    && afterMutable (line.Substring 4) = afterMutable ((textOfRange source r).Trim())

/// Find the accumulators whose loops are a list expression. Requires typed
/// check results.
/// The suggestion for one candidate accumulator, when its loops and drains
/// allow one.
let private suggestionFor
    (kind: Kind)
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

    // the feed whose receiver or target is exactly this use: the statement's
    // range, the element it adds, whether it consed it to the front, and
    // the typed proof it is the feed it looks like (deferred: a resolution
    // per call is the expensive step)
    let feedAt (r: range) =
        index.Exprs
        |> Array.tryPick (fun (_, e) ->
            match kind, e with
            | Kind.ResizeArray, AddCall([ recv ], addIdent, arg) when sameSpan recv.idRange r ->
                Some(e.Range, arg, false, (fun () -> resolvesToListAdd check source addIdent))
            | Kind.List, ListFeed(target, elem, cons, proof) when sameSpan target.idRange r ->
                Some(e.Range, elem, cons, (fun () -> feedResolves check source proof))
            | _ -> None)

    let accumulator =
        match kind with
        | Kind.ResizeArray ->
            match elementType check source acc with
            | Some(symbol, element) when closedElementType element -> Some symbol
            | _ -> None
        | Kind.List -> listSymbol check source acc

    match accumulator with
    | Some symbol ->
        let uses =
            check.GetUsesOfSymbolInFile symbol
            |> Array.filter (fun u -> not u.IsFromDefinition)
            |> Array.map (fun u -> u.Range)
            |> Array.sortBy (fun r -> r.StartLine, r.StartColumn)

        let feeds = uses |> Array.choose (fun r -> feedAt r |> Option.map (fun f -> r, f))

        // `acc <- acc @ [ e ]` reads `acc` once on its right: that read is
        // the feed's own, not a use of its own - unless it sits in the
        // element, which the feed check below must still see
        let uses =
            uses
            |> Array.filter (fun r ->
                not (
                    feeds
                    |> Array.exists (fun (target, (call, elem, _, _)) ->
                        not (sameSpan target r)
                        && Range.rangeContainsRange call r
                        && not (Range.rangeContainsRange elem.Range r))
                ))

        let addCalls = uses |> Array.map (fun r -> r, feedAt r)
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
                    | Some(call, arg, _, resolves), Some(_, loop) when
                        inStatementPosition loop call
                        && resolves ()
                        && not (uses |> Array.exists (fun v -> Range.rangeContainsRange arg.Range v))
                        ->
                        yieldText explicitYield source call arg |> Option.map (fun text -> call, text)
                    | _ -> None)

            // a list fed at the front comes out reversed and is read through
            // `List.rev`; fed at both ends it has no loop order to yield in
            let consed =
                inLoops
                |> List.choose (fun (_, call) -> call |> Option.map (fun (_, _, cons, _) -> cons))
                |> List.distinct

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
                            | ListFeed(target, _, _, _) -> target.idText <> acc.idText
                            | _ -> false)))

            if
                not quietBefore
                || consed.Length <> 1
                || hostile
                || not (yields |> List.forall Option.isSome)
                || spansDirective source region
                // a discarded non-unit statement would become a yield
                || not (
                    feeding
                    |> List.forall (fun (_, loop) -> bodyStatementsAreUnit check source acc loop)
                )
                // a Span read in the loops cannot move into the list
                // expression (FS0406)
                || OptionModule.readsByRefLike check index source region
            then
                None
            else
                let drains =
                    outside
                    |> List.map (fun (r, _) ->
                        match nodeAt r, kind with
                        | Some(path, node), Kind.ResizeArray -> classifyDrain check source path node
                        | Some(path, node), Kind.List -> classifyListDrain check source consed.Head path node
                        // an assignment's target, `acc <- ...` after the
                        // loops, is no expression node: the list is not
                        // done being built, and the result is immutable
                        | None, _ -> None)

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
                    // a list accumulator is a list already: the expression
                    // builds it once where the appends copied it per
                    // element, and no drain asks for anything else
                    elif kind = Kind.List then
                        Some false
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
                            match kind with
                            | Kind.ResizeArray ->
                                match declaredElementType source construction with
                                | Some t when wantsArray -> $": {t}[]"
                                | Some t -> $": {t} list"
                                | None -> ""
                            // `let mutable acc: T list = []` keeps its
                            // annotation: it is what typed the elements
                            | Kind.List ->
                                match binding with
                                | SynBinding(returnInfo = Some(SynBindingReturnInfo(typeName = t))) when
                                    isSingleLine t.Range
                                    ->
                                    $": {textOfRange source t.Range}"
                                | _ -> ""

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

                        // a drain whose wrapping parentheses were an application's
                        // own - `Some(List.ofSeq acc)`, `f(Seq.toList acc)` - keeps a
                        // pair, or the name would glue to the function: `Someacc`
                        let drainName (r: range) =
                            let line = source.GetLineString(r.StartLine - 1)

                            let glued =
                                r.StartColumn > 0
                                && (textOfRange source r).StartsWith "("
                                && (let c = line.[r.StartColumn - 1]
                                    Char.IsLetterOrDigit c || c = '_' || c = '\'' || c = '`')

                            if glued then $"({acc.idText})" else acc.idText

                        let drainEdits =
                            drains
                            |> List.choose (fun d ->
                                match d with
                                | ToList r when not wantsArray -> Some(edit r (drainName r))
                                | ToArray r when wantsArray -> Some(edit r (drainName r))
                                | Count r when wantsArray -> Some(edit r "Length")
                                | Reversed r -> Some(edit r (drainName r))
                                | _ -> None)

                        {
                            Name = acc.idText
                            Mutable = (kind = Kind.List)
                            Range = binding.RangeOfBindingWithRhs
                            Edits = edit declRange "" :: edit region replacement :: drainEdits
                        })
    | None -> None

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
                | LetOrUseE lou when not (lou.IsRecursive || lou.IsBang || lou.IsUse) ->
                    match lou.Bindings with
                    | [ SynBinding(
                            isMutable = isMutable
                            headPat = SynPat.Named(ident = SynIdent(ident = acc))
                            expr = construction) as binding ] when
                        // `let acc = ResizeArray()`, or `let mutable acc = []`
                        ((not isMutable && isEmptyConstruction construction)
                         || (isMutable && isEmptyList construction))
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
                        let kind = if isMutable then Kind.List else Kind.ResizeArray

                        match
                            suggestionFor kind index source check acc binding construction lou.Body arrays explicitYield
                        with
                        | Some s -> s
                        | None -> ()
                    | _ -> ()
                | _ -> ()
        ]

/// The default: list expressions only.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    findWith false false parseTree source check
