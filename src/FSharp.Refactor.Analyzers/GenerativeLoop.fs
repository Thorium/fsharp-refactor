/// FR0141 (note): a while loop that carries STATE forward by mutation and
/// leaves through a boolean flag is a tail-recursive function written
/// inside out.
///
///     let mutable stopped = false
///     while not stopped && generated.Count < limit do
///         let next = sample model cache      // depends on the last round
///         cache <- cache'
///         if next = stop then stopped <- true
///         else generated.Add next
///
/// The state lives in mutables the loop reaches back into, and the exit
/// is a flag the condition re-reads: raising it is not a `break`, so the
/// rest of that iteration still runs and the loop leaves only at the next
/// condition check. A tail-recursive function would take that state as
/// parameters and return where the decision is made, leaving no flag, no
/// mutables, and no tail to run.
///
/// NOTE ONLY. The rewrite reorders the whole body into a function and
/// names its parameters; that is the author's to write.
///
/// This is deliberately NOT the search loop:
///
///     while not found && i < xs.Length do
///         if p xs.[i] then found <- true
///         i <- i + 1
///
/// There the only carried value is an index walking a collection, the
/// loop already short-circuits, and it allocates nothing — measured
/// against Array.exists it is 12x FASTER on an early hit, so a pipeline
/// would be a regression dressed as a cleanup. A carried value whose
/// every assignment is `x <- x + <literal>` is an index, and the loop is
/// left alone.
module FSharp.Refactor.GenerativeLoop

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// The flag the loop leaves through.
        Flag: string
        /// The state carried forward, in source order.
        Carried: string list
        /// Statements that still run in the iteration that raised the
        /// flag. Raising it is not a `break`: the body finishes, and the
        /// loop leaves only at the NEXT condition check. Zero of these
        /// means the tail is empty and the message must not claim one.
        TailAfterFlag: int
    }

/// The bare identifiers of an `a || b || c` disjunction.
let rec private orIdents (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> [ id.idText ]
    | SynExpr.Paren(expr = inner) -> orIdents inner
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = l); argExpr = r) when
        op.idText = "op_BooleanOr"
        ->
        orIdents l @ orIdents r
    | _ -> []

/// `not x` anywhere in the condition names a candidate flag — and
/// `not (terminated || eof)` names two.
let rec private negatedIdents (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident op; argExpr = SynExpr.Ident flag) when op.idText = "not" ->
        [ flag.idText ]
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident op; argExpr = SynExpr.Paren(expr = inner)) when
        op.idText = "not"
        ->
        orIdents inner
    | SynExpr.App(funcExpr = f; argExpr = a) -> negatedIdents f @ negatedIdents a
    | SynExpr.Paren(expr = inner) -> negatedIdents inner
    | _ -> []

/// Simple `name <- rhs` assignments anywhere inside, paired with their rhs.
let rec private assignments (e: SynExpr) =
    match e with
    | SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), rhs, _) -> [ target.idText, rhs ]
    | SynExpr.Set(SynExpr.Ident target, rhs, _) -> [ target.idText, rhs ]
    | _ ->
        // walk the statement structure; anything else contributes nothing
        match e with
        | SynExpr.Sequential(expr1 = a; expr2 = b) -> assignments a @ assignments b
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = els) ->
            assignments t @ (els |> Option.map assignments |> Option.defaultValue [])
        | LetOrUseE lou ->
            (lou.Bindings |> List.collect (fun (SynBinding(expr = be)) -> assignments be))
            @ assignments lou.Body
        | SynExpr.Match(clauses = clauses) ->
            clauses |> List.collect (fun (SynMatchClause(resultExpr = r)) -> assignments r)
        | SynExpr.For(doBody = b) -> assignments b
        | SynExpr.ForEach(bodyExpr = b) -> assignments b
        | SynExpr.While(doExpr = b) -> assignments b
        | SynExpr.TryWith(tryExpr = t) -> assignments t
        | SynExpr.TryFinally(tryExpr = t; finallyExpr = f) -> assignments t @ assignments f
        | SynExpr.Paren(expr = inner) -> assignments inner
        | SynExpr.Do(expr = inner) -> assignments inner
        | _ -> []

/// Names bound by a `let mutable` INSIDE the body: those die each round
/// and are not carried anywhere.
let rec private locallyBound (e: SynExpr) =
    match e with
    | LetOrUseE lou ->
        let here =
            lou.Bindings
            |> List.collect (fun b ->
                match b with
                | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = n))) -> [ n.idText ]
                | _ -> [])

        here @ locallyBound lou.Body
    | SynExpr.Sequential(expr1 = a; expr2 = b) -> locallyBound a @ locallyBound b
    | SynExpr.IfThenElse(thenExpr = t; elseExpr = els) ->
        locallyBound t @ (els |> Option.map locallyBound |> Option.defaultValue [])
    | SynExpr.Do(expr = inner) -> locallyBound inner
    | SynExpr.Paren(expr = inner) -> locallyBound inner
    | _ -> []

/// The body's top-level statements, in order. A `let` contributes its
/// right-hand side and then whatever follows it: `let x = e` followed by
/// two statements is three, not one, or the tail count would read zero
/// for every body that opens with a binding.
let rec private statements (e: SynExpr) =
    match e with
    | SynExpr.Sequential(expr1 = a; expr2 = b) -> statements a @ statements b
    | SynExpr.Do(expr = inner) -> statements inner
    | LetOrUseE lou ->
        (lou.Bindings |> List.map (fun (SynBinding(expr = be)) -> be))
        @ statements lou.Body
    | other -> [ other ]

/// How many statements still run after the one that raises the flag?
/// Raising it is not a `break` — the body finishes and the loop leaves at
/// the next condition check, so whatever follows runs one more time than
/// the author's "stop here" suggests.
let private tailAfterFlag (flag: string) (body: SynExpr) =
    let stmts = statements body

    let raisesFlag (s: SynExpr) =
        assignments s |> List.exists (fun (n, _) -> n = flag)

    match stmts |> List.tryFindIndexBack raisesFlag with
    | Some i -> stmts.Length - i - 1
    | None -> 0

/// The asynchronous builders, where this advice does not belong.
///
/// In a `task` recursion is not even available: it compiles to a
/// resumable state machine and a recursive `return!` grows the stack,
/// which is why FSharp.Azure.Quantum's polling loop carries the reason
/// in a comment above it — "Iterative polling loop (task CE does not
/// support tail-call recursion)". In an `async` the rewrite stops being
/// local: the recursive function has to return `Async<_>`, so the change
/// reaches the signature rather than the loop.
///
/// Other builders are NOT excluded. A `while` inside a `seq { }` is
/// ordinary code with an ordinary rewrite.
let private asyncBuilders =
    set [ "task"; "vtask"; "valueTask"; "backgroundTask"; "async" ]

let private computationBuilderRanges (index: AstIndex.Index) =
    index.Exprs
    |> Array.choose (fun (_, e) ->
        match e with
        | SynExpr.App(funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
            asyncBuilders.Contains builder.idText
            ->
            Some body.Range
        | _ -> None)

/// `x <- x + 1` and friends: an index walking a collection, not state.
/// `x <- x + stride` and a binary search's `low <- mid + 1` are the same
/// index arithmetic.
let private isCounterBump (name: string) (rhs: SynExpr) =
    match rhs with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident lhs)
        argExpr = (SynExpr.Const(SynConst.Int32 _, _) | SynExpr.Ident _)) ->
        (op.idText = "op_Addition" || op.idText = "op_Subtraction") && lhs.idText = name
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident _)
        argExpr = SynExpr.Const(SynConst.Int32 _, _)) -> op.idText = "op_Addition" || op.idText = "op_Subtraction"
    | _ -> false

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let inAsyncBuilder = computationBuilderRanges index

    [
        for _, expr in index.Exprs do
            match expr with
            | SynExpr.While(whileExpr = cond; doExpr = body) when
                not (inAsyncBuilder |> Array.exists (fun r -> Range.rangeContainsRange r expr.Range))
                ->
                let flags = negatedIdents cond
                let sets = assignments body
                let bound = set (locallyBound body)

                // a name only WRITTEN in the loop is a result being filled
                // in, not state the next round depends on
                let readInLoop =
                    index.Exprs
                    |> Array.choose (fun (_, e) ->
                        match e with
                        | SynExpr.Ident id when
                            Range.rangeContainsRange cond.Range id.idRange
                            || Range.rangeContainsRange body.Range id.idRange
                            ->
                            Some id.idText
                        | _ -> None)
                    |> Set.ofArray

                for flag in List.distinct flags do
                    // the flag has to be RAISED in the body, or the loop is
                    // waiting on something else entirely
                    if sets |> List.exists (fun (n, _) -> n = flag) then
                        let carried =
                            sets
                            |> List.filter (fun (n, rhs) ->
                                n <> flag
                                && not (bound.Contains n)
                                && not (isCounterBump n rhs)
                                && readInLoop.Contains n)
                            |> List.map fst
                            |> List.distinct

                        if not carried.IsEmpty then
                            {
                                Range = cond.Range
                                Flag = flag
                                Carried = carried
                                TailAfterFlag = tailAfterFlag flag body
                            }
            | _ -> ()
    ]
