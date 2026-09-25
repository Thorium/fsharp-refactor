/// Refactoring (performance): a binding inside a loop or collection lambda
/// whose value cannot change between iterations is re-evaluated every pass.
///
///     for x = 0 to 100 do          let c = a + 3
///         let c = a + 3       →    for x = 0 to 100 do
///         sink (x + c)                 sink (x + c)
///
/// Also `while`, `for ... in`, and lambdas handed to List/Array/Seq
/// operations.
///
/// Hoisting changes how many times the right-hand side runs (n iterations
/// become exactly one, and an empty loop still runs it once), so the
/// safety rules make that unobservable:
///   - the RHS is PURE: constants, identifiers, tuples, LIST literals
///     (an array literal is a fresh mutable buffer every iteration, and
///     hoisting makes every iteration share one), and a whitelist of
///     core operators that are pure and total
///     on their operands (typed-gated against shadowed operators) — no
///     calls, no property reads, and none of the operators that APPLY
///     something (`|>`, `>>`, `!`, `:=`): `reader |> readLine` is a call;
///     `/` and `%` only over a literal, non-zero divisor that is no signed
///     integral -1 (`Int32.MinValue / -1` throws OverflowException)
///   - no checked arithmetic: a file opening `Checked` (or
///     `Microsoft.FSharp.Core.Operators.Checked`) stands down, and so does
///     any operator the typed tree resolves to the Checked module - `+`,
///     `-`, `*` there throw on overflow where the empty loop did not
///   - the RHS references no loop variable, no name bound earlier in the
///     loop body, and no name assigned in the loop's own statement
///   - a RHS reading a `let mutable` (typed): besides an assignment in the
///     statement's own text, whatever the statement CALLS may write it — a
///     local `let mutable` included, since F# 4.0 a closure captures one
///     silently (it becomes a ref cell): `let bump () = total <- total + 1`
///     beside the loop writes the local. So every function the statement
///     names must be FSharp.Core's or declared in this file with a body
///     that assigns it nowhere (three declarations deep) — `advance ()`
///     with `offset <- offset + 1` in its body, a method, a property
///     getter, a function held in a field, an active pattern, a
///     constructor or a callee from another file stand it down. The text
///     scanned is the whole anchor statement: the pipeline head and every
///     argument of a collection operation run between the hoisted binding
///     and the lambda
///   - in a `Seq.*` lambda, no `let mutable` read at all: the lambda runs
///     at ENUMERATION, possibly after a later `scale <- 5` the statement
///     scan never sees, where the hoisted binding read the old value
///   - the binding is a plain single-line `let` of a simple name (no
///     mutable, no use, no functions)
///   - the bound name appears nowhere in the file outside the loop body:
///     the hoisted binding's wider scope can shadow or collide otherwise
///   - the insertion anchor (the statement carrying the loop) starts its
///     own line, and no edit crosses a compiler directive
module FSharp.Refactor.LoopInvariant

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The invariant binding, where the hint anchors.
        Range: range
        Name: string
        /// (range, original, replacement) edits: remove the inner let,
        /// insert it above the loop's statement.
        Edits: (range * string * string) list
    }

/// Module functions whose lambda argument runs per element.
let private collectionModules = set [ "List"; "Array"; "Seq" ]

/// The operators a hoisted expression may apply: pure and TOTAL on their
/// operands, so evaluating them once instead of n times (or once instead
/// of never, for an empty loop) is unobservable. Arithmetic (with `/` and
/// `%` admitted separately, over a literal non-zero divisor only, since a
/// division by zero would throw where the empty loop did not),
/// comparison, boolean and bitwise. Every operator that applies or
/// mutates something is out — `|>`, `<|`, `>>`, `<<`, `!`, `:=` — since
/// `reader |> readLine` is a call spelled as an operator: hoisted above a
/// `while reader.Peek() >= 0` loop it read one line and the loop spun on
/// it. The typed gate still checks each one resolves to FSharp.Core.
let private hoistableOperators =
    set
        [
            "op_Addition"
            "op_Subtraction"
            "op_Multiply"
            "op_UnaryNegation"
            "op_UnaryPlus"
            "op_Equality"
            "op_Inequality"
            "op_LessThan"
            "op_GreaterThan"
            "op_LessThanOrEqual"
            "op_GreaterThanOrEqual"
            "op_BooleanAnd"
            "op_BooleanOr"
            "op_BitwiseAnd"
            "op_BitwiseOr"
            "op_ExclusiveOr"
            "op_LogicalNot"
            "op_LeftShift"
            "op_RightShift"
        ]

/// A numeric literal other than zero.
[<TailCall>]
let rec private nonZeroConst (c: SynConst) =
    match c with
    | SynConst.SByte v -> v <> 0y
    | SynConst.Byte v -> v <> 0uy
    | SynConst.Int16 v -> v <> 0s
    | SynConst.UInt16 v -> v <> 0us
    | SynConst.Int32 v -> v <> 0
    | SynConst.UInt32 v -> v <> 0u
    | SynConst.Int64 v -> v <> 0L
    | SynConst.UInt64 v -> v <> 0UL
    | SynConst.IntPtr v -> v <> 0L
    | SynConst.UIntPtr v -> v <> 0UL
    | SynConst.Single v -> v <> 0.0f
    | SynConst.Double v -> v <> 0.0
    | SynConst.Decimal v -> v <> 0M
    | SynConst.Measure(constant = inner) -> nonZeroConst inner
    | _ -> false

/// The value of a SIGNED integral literal, where one: `MinValue / -1` and
/// `MinValue % -1` overflow (OverflowException), so -1 is no safe divisor
/// for these. An unsigned, float or decimal literal has no such value.
[<TailCall>]
let rec private signedIntegral (c: SynConst) : int64 voption =
    match c with
    | SynConst.SByte v -> ValueSome(int64 v)
    | SynConst.Int16 v -> ValueSome(int64 v)
    | SynConst.Int32 v -> ValueSome(int64 v)
    | SynConst.Int64 v -> ValueSome v
    | SynConst.IntPtr v -> ValueSome v
    | SynConst.Measure(constant = inner) -> signedIntegral inner
    | _ -> ValueNone

/// A divisor that makes `/` and `%` total: a numeric literal, negated or
/// parenthesised or not, other than zero - and other than a signed
/// integral -1 (`Int32.MinValue / -1` throws OverflowException). `a / 2`
/// and `a % 4` are total; `a / b` may throw on a divisor the loop never
/// met. A float's -1 is fine: float division never throws.
[<return: Struct>]
let private (|NonZeroLiteral|_|) (e: SynExpr) =
    let rec safe (negated: bool) (e: SynExpr) =
        match e with
        | SynExpr.Const(c, _) ->
            nonZeroConst c
            && (match signedIntegral c with
                | ValueSome v -> (if negated then -v else v) <> -1L
                | ValueNone -> true)
        | SynExpr.Paren(expr = inner) -> safe negated inner
        | SynExpr.App(funcExpr = SingleIdent neg; argExpr = inner) when neg.idText = "op_UnaryNegation" ->
            safe (not negated) inner
        | _ -> false

    if safe false e then ValueSome() else ValueNone

/// Purity walk: succeeds only for expression shapes that always yield the
/// same value. Collects every identifier read and every operator ident —
/// the (expensive) typed core-operator resolution runs LATER, once the
/// cheap gates have already filtered most candidates out.
[<TailCall>]
let rec private pureIdentsLoop
    (acc: Ident list)
    (ops: Ident list)
    (pending: SynExpr list)
    : (Ident list * Ident list) voption =
    match pending with
    | [] -> ValueSome(acc, ops)
    | e :: rest ->
        match e with
        | SynExpr.Const _ -> pureIdentsLoop acc ops rest
        | SynExpr.Ident id -> pureIdentsLoop (id :: acc) ops rest
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner) -> pureIdentsLoop acc ops (inner :: rest)
        | SynExpr.Tuple(exprs = exprs) -> pureIdentsLoop acc ops (exprs @ rest)
        // A LIST literal is immutable: n allocations become one and nothing
        // can tell. An ARRAY literal is a fresh mutable buffer per
        // iteration — hoisted, every iteration shares one, so
        // `let buf = [| a + 1 |]` above a `buf.[0] <- x` quietly changes
        // what the loop does. Same for anything else handed the buffer.
        | SynExpr.ArrayOrListComputed(isArray = false; expr = inner) -> pureIdentsLoop acc ops (inner :: rest)
        | SynExpr.ArrayOrList(isArray = false; exprs = exprs) -> pureIdentsLoop acc ops (exprs @ rest)
        // infix operator: App(App(op, lhs), rhs)
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
            hoistableOperators.Contains op.idText
            ->
            pureIdentsLoop acc (op :: ops) (lhs :: rhs :: rest)
        // `/` and `%`: total over a divisor that is a non-zero literal
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = NonZeroLiteral) when
            op.idText = "op_Division" || op.idText = "op_Modulus"
            ->
            pureIdentsLoop acc (op :: ops) (lhs :: rest)
        // unary operator, e.g. -a
        | SynExpr.App(funcExpr = SingleIdent op; argExpr = arg) when hoistableOperators.Contains op.idText ->
            pureIdentsLoop acc (op :: ops) (arg :: rest)
        | _ -> ValueNone

/// What the typed tree says about an identifier the hoisted binding reads.
[<RequireQualifiedAccess>]
type private ReadKind =
    /// An immutable value: nothing changes it between iterations.
    | Immutable
    /// A `let mutable` at any level, a mutable field, a byref, or an
    /// identifier that does not resolve: whatever the statement calls may
    /// assign it. A LOCAL `let mutable` is no exception — since F# 4.0 a
    /// closure captures one silently (the compiler turns it into a ref
    /// cell), so `let bump () = total <- total + 1` declared beside the
    /// loop writes it from inside a call.
    | Mutable

/// Classify a read.
let private readKind (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) : ReadKind =
    match OptionModule.symbolOfIdent check source id with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            let t = value.FullType

            if t.HasTypeDefinition && t.TypeDefinition.IsByRef then
                ReadKind.Mutable
            elif not value.IsMutable then
                ReadKind.Immutable
            else
                ReadKind.Mutable
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             ReadKind.Mutable)
    | Some(:? FSharpUnionCase) -> ReadKind.Immutable
    | Some(:? FSharpField as field) ->
        (try
            if field.IsMutable then
                ReadKind.Mutable
            else
                ReadKind.Immutable
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             ReadKind.Mutable)
    | _ -> ReadKind.Mutable

/// The insertion point: the nearest enclosing expression (the loop itself,
/// or e.g. the pipeline feeding a lambda) that starts its own line. Only
/// expression ancestors are considered, so the hoisted binding never
/// leaves the scope whose values it reads.
let private insertionAnchor (source: ISourceText) (path: SyntaxNode list) (loopExpr: SynExpr) =
    let startsItsLine (r: range) =
        let line = source.GetLineString(r.StartLine - 1)

        r.StartColumn <= line.Length && line.Substring(0, r.StartColumn).Trim() = ""

    let ancestors =
        path
        |> List.takeWhile (fun n ->
            match n with
            | SyntaxNode.SynExpr _ -> true
            | _ -> false)
        |> List.choose (fun n ->
            match n with
            | SyntaxNode.SynExpr e -> Some e
            | _ -> None)

    loopExpr :: ancestors
    |> List.tryFind (fun e -> startsItsLine e.Range)
    |> Option.map (fun e -> e.Range)

/// The leading `let` bindings of a loop body, with the continuation each
/// one wraps.
[<TailCall>]
let rec private leadingLets (acc: (SynBinding * SynExpr) list) (body: SynExpr) =
    match body with
    | LetOrUseE lou when not (lou.IsUse || lou.IsBang || lou.IsRecursive) ->
        match lou.Bindings with
        | [ binding ] -> leadingLets ((binding, lou.Body) :: acc) lou.Body
        | _ -> List.rev acc
    | _ -> List.rev acc

/// Under `open Checked`, `+`, `-`, `*` and unary `-` throw
/// OverflowException: hoisted above a loop that never ran, they would
/// throw where nothing did. The whole file stands down.
let private opensChecked (source: ISourceText) =
    [
        "Checked"
        "Operators.Checked"
        "Microsoft.FSharp.Core.Operators.Checked"
        "FSharp.Core.Operators.Checked"
    ]
    |> List.exists (opensNamespace source)

/// An operator that resolves to the Checked module however it got in scope.
let private resolvesToChecked (check: FSharpCheckFileResults) (source: ISourceText) (op: Ident) =
    match OptionModule.symbolOfIdent check source op with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        OptionModule.enclosingFullName value = "Microsoft.FSharp.Core.Operators.Checked"
        || (OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp.Core.Operators.Checked"
    | _ -> false

/// Find hoistable invariant bindings. Requires typed check results for the
/// operator-purity gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check || opensChecked source then
        []
    else
        let index = AstIndex.ofTree parseTree

        // (loop node, loop-bound names, body, lazy) for every loop-like
        // shape; `lazy` marks a Seq lambda, which runs at ENUMERATION —
        // possibly long after the statement, past any later assignment
        let candidates =
            [
                for path, expr in index.Exprs do
                    match expr with
                    | SynExpr.For(ident = loopVar; doBody = body) ->
                        path, expr, Set.singleton loopVar.idText, body, false
                    | SynExpr.ForEach(pat = pat; bodyExpr = body) ->
                        path, expr, Set.ofList (patBoundNames pat), body, false
                    | SynExpr.While(doExpr = body) -> path, expr, Set.empty, body, false
                    // xs |> List.map (fun x -> ...) — the lambda's params are
                    // the per-element names
                    | SynExpr.App(
                        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; _ ]))
                        argExpr = SynExpr.Paren(expr = SynExpr.Lambda(parsedData = Some(pats, _); body = body))) when
                        collectionModules.Contains m.idText
                        ->
                        path, expr, Set.ofList (pats |> List.collect patBoundNames), body, m.idText = "Seq"
                    | _ -> ()
            ]

        // one pass of every mention (read or assigned) keyed by name; the
        // per-candidate scans below become dictionary lookups
        let mentionIndex =
            System.Collections.Generic.Dictionary<string, ResizeArray<range>>()

        let assignIndex =
            System.Collections.Generic.Dictionary<string, ResizeArray<range>>()

        let addTo (d: System.Collections.Generic.Dictionary<string, ResizeArray<range>>) name r =
            match d.TryGetValue name with
            | true, existing -> existing.Add r
            | false, _ ->
                let fresh = ResizeArray()
                fresh.Add r
                d.[name] <- fresh

        for _, e in index.Exprs do
            match e with
            | SynExpr.Ident id -> addTo mentionIndex id.idText id.idRange
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) ->
                addTo mentionIndex firstId.idText firstId.idRange
            | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) ->
                addTo mentionIndex firstId.idText e.Range
                addTo assignIndex firstId.idText e.Range
            | SynExpr.Set(targetExpr = SynExpr.Ident id) -> addTo assignIndex id.idText e.Range
            | _ -> ()

        // is `name` assigned (`<-`) anywhere inside `r`?
        let assignedWithin (r: range) (name: string) =
            match assignIndex.TryGetValue name with
            | true, ranges -> ranges |> Seq.exists (Range.rangeContainsRange r)
            | false, _ -> false

        // the functions the text in `r` names outside `excluded` (the
        // hoisted binding's own operator applications), applied or passed
        // on: each as its symbol, or None for a callee no symbol stands
        // for or none this scan can follow — a constructor, an object
        // expression, an identifier that does not resolve, a property
        // getter declared outside FSharp.Core and the BCL (its body runs),
        // an extension member on a BCL type (a user body behind a BCL
        // owner), a function held in a record or class field (`ops.Bump ()`
        // with `Bump: unit -> unit`), an active pattern
        let calleesIn (r: range) (excluded: range option) : FSharpMemberOrFunctionOrValue option list =
            let functionAt (ids: Ident list) =
                match OptionModule.symbolOfIdent check source (List.last ids) with
                | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                    (try
                        if value.IsProperty || value.IsPropertyGetterMethod then
                            // a BCL or FSharp.Core getter cannot reach a
                            // mutable of this file; a user's (or an
                            // extension's) getter runs whatever it likes
                            let owner = OptionModule.enclosingFullName value

                            if
                                not value.IsExtensionMember
                                && (owner.StartsWith "System." || owner.StartsWith "Microsoft.FSharp.")
                            then
                                []
                            else
                                [ None ]
                        elif value.IsActivePattern then
                            [ None ]
                        elif value.FullType.IsFunctionType then
                            [ Some value ]
                        else
                            []
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         [ None ])
                | Some(:? FSharpField as field) ->
                    (try
                        if (OptionModule.stripAbbreviations field.FieldType).IsFunctionType then
                            [ None ]
                        else
                            []
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         [ None ])
                | Some(:? FSharpActivePatternCase) -> [ None ]
                | Some _ -> []
                | None -> [ None ]

            [
                for _, e in AstIndex.exprsWithin index r do
                    if
                        Range.rangeContainsRange r e.Range
                        && not (excluded |> Option.exists (fun x -> Range.rangeContainsRange x e.Range))
                    then
                        match e with
                        | SynExpr.Ident id -> yield! functionAt [ id ]
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                            yield! functionAt ids
                        | SynExpr.New _
                        | SynExpr.ObjExpr _ -> yield None
                        | _ -> ()

                // an active pattern matched in the text runs its body too
                // (`| Bumped n ->`), and no expression names it
                for _, p in AstIndex.patsWithin index r do
                    if Range.rangeContainsRange r p.Range then
                        match p with
                        | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                            match OptionModule.symbolOfIdent check source (List.last ids) with
                            | Some(:? FSharpActivePatternCase) -> yield None
                            | Some(:? FSharpMemberOrFunctionOrValue as value) when
                                (try
                                    value.IsActivePattern
                                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                     true)
                                ->
                                yield None
                            | _ -> ()
                        | _ -> ()
            ]

        // may something the text in `r` calls assign `name`? FSharp.Core's
        // functions cannot (a lambda they run is in the loop's own text);
        // a function this file declares does when its body assigns the
        // name or calls one that does, three declarations deep; a callee
        // declared elsewhere, a method, a constructor, an object
        // expression or an unresolved identifier may
        let rec calleesMayAssign
            (depth: int)
            (visited: Set<int * int>)
            (name: string)
            (r: range)
            (excluded: range option)
            =
            calleesIn r excluded
            |> List.exists (fun callee ->
                match callee with
                | None -> true
                | Some value ->
                    // an extension member's owner is the type it extends
                    // (FSharp.Core's or the BCL's), its body a user's
                    (value.IsExtensionMember
                     || not ((OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp."))
                    && (match OptionModule.bindingDeclaredAt index value with
                        | Some(head, body) ->
                            let key = head.idRange.StartLine, head.idRange.StartColumn

                            not (visited.Contains key)
                            && (depth >= 3
                                || assignedWithin body.Range name
                                || calleesMayAssign (depth + 1) (visited.Add key) name body.Range None)
                        | None -> true))

        // does this name appear (read or assigned) anywhere outside `r`?
        let usedOutside (r: range) (name: string) =
            match mentionIndex.TryGetValue name with
            | true, ranges -> ranges |> Seq.exists (Range.rangeContainsRange r >> not)
            | false, _ -> false

        let suggestions: Suggestion list =
            [
                for path, loopExpr, loopVars, body, isLazy in candidates do
                    match insertionAnchor source path loopExpr with
                    | Some anchor ->
                        let mutable boundEarlier = Set.empty

                        for binding, continuation in leadingLets [] body do
                            match binding with
                            | SynBinding(
                                isMutable = false
                                isInline = false
                                headPat = SynPat.Named(ident = SynIdent(ident = name); accessibility = None)
                                expr = rhs) when
                                isSingleLine binding.RangeOfBindingWithRhs
                                && binding.RangeOfBindingWithRhs.EndLine < continuation.Range.StartLine
                                ->
                                let forbidden = loopVars + boundEarlier |> Set.add name.idText

                                // the text whose calls could write a mutable the
                                // binding reads: the whole anchor statement. The
                                // hoisted binding lands above it, so everything
                                // in it runs between the hoisted read and the
                                // loop's reads — a pipeline's head (`produce ()
                                // |> List.map (fun x -> ..)`) and every other
                                // argument of the collection operation included,
                                // where a scan of the lambda's body alone let
                                // `produce` write the mutable unseen
                                let scanRange = anchor

                                match pureIdentsLoop [] [] [ rhs ] with
                                | ValueSome(reads, ops) when
                                    // only an invariant that DOES WORK is worth
                                    // hoisting: an operator expression (`a + 3`).
                                    // A bare identifier, constant or literal
                                    // copy costs nothing per iteration, and
                                    // hoisting `let ny = sinPhi` out of Mibo's
                                    // Primitive3D inner loop only separated it
                                    // from the `nx`/`nz` it belongs with
                                    not ops.IsEmpty
                                    // an assignment in the loop's own statement
                                    // (the anchor wraps the loop) changes the
                                    // value between iterations
                                    && reads
                                       |> List.forall (fun rd ->
                                           not (forbidden.Contains rd.idText || assignedWithin anchor rd.idText))
                                    // the hoisted binding's wider scope must collide
                                    // with nothing: the name may live only in the loop
                                    && not (usedOutside loopExpr.Range name.idText)
                                    // a shadowed operator can have arbitrary
                                    // semantics; the typed gate runs last
                                    && ops |> List.forall (OptionModule.resolvesToCoreOperator check source)
                                    // a checked operator throws on overflow
                                    && not (ops |> List.exists (resolvesToChecked check source))
                                    // a `let mutable` the binding reads, local or
                                    // shared, may be written by what the statement
                                    // calls (a closure captures a local one too)
                                    && reads
                                       |> List.forall (fun rd ->
                                           match readKind check source rd with
                                           | ReadKind.Immutable -> true
                                           // a Seq lambda runs at enumeration,
                                           // after code no scan of the statement
                                           // sees (`scale <- 5` below it): the
                                           // hoisted read would see the old value
                                           | ReadKind.Mutable when isLazy -> false
                                           | ReadKind.Mutable ->
                                               not (calleesMayAssign 0 Set.empty rd.idText scanRange (Some rhs.Range)))
                                    ->
                                    let letLine = binding.RangeOfBindingWithRhs.StartLine
                                    // the binding range starts at the pattern; the
                                    // `let` keyword lives before it on the same line
                                    let bindingText = textOfRange source binding.RangeOfBindingWithRhs

                                    let removeRange =
                                        Range.mkRange
                                            binding.RangeOfBindingWithRhs.FileName
                                            (Position.mkPos letLine 0)
                                            (Position.mkPos (letLine + 1) 0)

                                    let indent = System.String(' ', anchor.StartColumn)

                                    // a binding lifted out of the loop keeps the `#if`
                                    // it was written under; a directive has to open its
                                    // own line, so that form is inserted at column 0 of
                                    // the anchor's line, ahead of its indentation
                                    let insert =
                                        match conditionToKeep source letLine anchor.StartLine with
                                        | Some condition ->
                                            Range.mkRange
                                                anchor.FileName
                                                (Position.mkPos anchor.StartLine 0)
                                                (Position.mkPos anchor.StartLine 0),
                                            "",
                                            $"#if {condition}\n{indent}let {bindingText}\n#endif\n"
                                        | None ->
                                            Range.mkRange anchor.FileName anchor.Start anchor.Start,
                                            "",
                                            $"let {bindingText}\n{indent}"

                                    let edits = [ insert; removeRange, textOfRange source removeRange, "" ]

                                    if
                                        not (edits |> List.exists (fun (r, _, _) -> spansDirective source r))
                                        // the let must own its whole line, so the
                                        // line delete removes exactly the binding
                                        && (source.GetLineString(letLine - 1)).Trim() = $"let {bindingText}"
                                    then
                                        {
                                            Range = binding.RangeOfBindingWithRhs
                                            Name = name.idText
                                            Edits = edits
                                        }
                                | _ -> ()
                            | _ -> ()

                            boundEarlier <-
                                boundEarlier
                                + Set.ofList (
                                    match binding with
                                    | SynBinding(headPat = p) -> patBoundNames p
                                )
                    | None -> ()
            ]

        suggestions
