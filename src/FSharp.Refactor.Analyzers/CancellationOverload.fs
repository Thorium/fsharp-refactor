/// FR0118 (fix): a call omits the CancellationToken its target offers
/// while a token sits unused in scope — cancellation stops propagating
/// exactly one call too early.
///
///     let fetch (client: HttpClient) (ct: CancellationToken) = task {
///         let! s = client.GetStringAsync(url)          // ct exists...
///     }                                                // ...pass it:
///         let! s = client.GetStringAsync(url, ct)
///
/// Typed gates, all must hold:
///   - the resolved method has a same-name overload with EXACTLY one more
///     parameter, a trailing System.Threading.CancellationToken, and the
///     shared prefix of parameter types identical — or the method itself
///     carries a trailing OPTIONAL CancellationToken the call omits
///   - the enclosing binding has EXACTLY one parameter annotated as a
///     CancellationToken (two tokens make the choice a human call)
///   - the call uses .NET tupled shape (`M()`, `M(a)`, `M(a, b)`) — the
///     edit appends the token inside the parentheses
///   - the call is not CLEANUP: not in a `finally`, a `with` handler or
///     a callback handed to the token's own `Register` (which runs because
///     the token is already cancelled)
///   - the token's name is not rebound (`for ct in ...`, `let ct = ...`)
///     inside the binding ahead of the call: `ct` there may be anything
///   - the call is not SHARED WORK made under the token's binding: not in a
///     `lazy`, a `Lazy` constructor or the arguments of `GetOrAdd` /
///     `AddOrUpdate`. Their value goes to every caller, so one caller's
///     token there fails the others when that caller cancels
///   - the call does not SCHEDULE work: not `Task.Run`, `StartNew`,
///     `ContinueWith`, `ContinueWhenAll` or `ContinueWhenAny`, waited for or
///     not, whose token decides whether the work runs at all
///
/// A `CancellationToken.None` argument is replaced under the same gates,
/// and only where the work it starts is waited for: `|> ignore`, a bare
/// statement or a store detaches that work from the caller on purpose.
///
/// The loop note (findUnobservedLoops): a loop awaiting inside, under the
/// token's binding, that never mentions the token — nor a local built
/// with it (`let enumerator = source.GetAsyncEnumerator ct`) — cannot be
/// cancelled. Outside `async { }` only, which observes the token at every
/// bind by itself; quiet where the fix above already hands the token to a
/// call in the loop, inside cleanup (finally, with handlers, Register
/// callbacks) or shared work, and under a rebinding of the token's name.
module FSharp.Refactor.CancellationOverload

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type TokenGap =
    /// The call omits the token an overload (or optional parameter) takes.
    | Omitted
    /// The call passes `CancellationToken.None` although a real token is
    /// in scope — cancellation is explicitly cut instead of propagated.
    | NonePassed

type Suggestion =
    {
        /// The edit: replace `()`, append `, token` before the `)`, or
        /// replace the `CancellationToken.None` argument.
        Range: range
        Original: string
        Replacement: string
        MethodName: string
        TokenName: string
        Kind: TokenGap
    }

let private isCancellationTokenType (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText = "CancellationToken"
    | _ -> false

/// The last identifier of a member-call function expression.
[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// `name = expr` in argument position is a NAMED argument: it may well BE
/// the token (`cancellationToken = ct`), and positional arity counting is
/// meaningless around it — appending `, token` after one is a syntax error.
let private isNamedArg (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = op; argExpr = SynExpr.Ident _)) ->
        (match op with
         | SynExpr.Ident i -> i.idText = "op_Equality"
         | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ i ])) -> i.idText = "op_Equality"
         | _ -> false)
    | _ -> false

let private typeFullName (t: FSharpType) =
    try
        match t.StripAbbreviations().TypeDefinition.TryFullName with
        | Some full -> full
        | None -> ""
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        ""

let private isCancellationToken (t: FSharpType) =
    typeFullName t = "System.Threading.CancellationToken"

/// Parameter types rendered for a pairwise prefix comparison.
let private parameterShapes (displayContext: FSharpDisplayContext) (mfv: FSharpMemberOrFunctionOrValue) =
    try
        match mfv.CurriedParameterGroups |> List.ofSeq with
        | [ group ] -> Some [ for p in group -> p.Type.Format displayContext ]
        | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// Task.Run, Task.Factory.StartNew and the continuations (ContinueWith,
/// ContinueWhenAll, ContinueWhenAny) take the token as a SCHEDULING
/// condition, not as an operation to interrupt: with an already-cancelled
/// token the delegate never runs at all, so the side effects in its body
/// silently never happen — binding a listening socket, say, or completing
/// a cell, or a continuation's cleanup. An I/O method's token only cancels the
/// call it was passed to; these change whether the work starts, and that is
/// the author's decision. The overloads with a scheduler or options demand a
/// token, so a `None` there is also how the call reaches them.
let private schedulesDelegate (mfv: FSharpMemberOrFunctionOrValue) =
    ((mfv.DisplayName = "Run"
      || mfv.DisplayName = "StartNew"
      || mfv.DisplayName = "ContinueWith"
      || mfv.DisplayName = "ContinueWhenAll"
      || mfv.DisplayName = "ContinueWhenAny")
     && (OptionModule.enclosingFullName mfv).StartsWith "System.Threading.Tasks.Task")
    || ((mfv.DisplayName = "Start" || mfv.DisplayName = "StartImmediate")
        && (OptionModule.enclosingFullName mfv).StartsWith "Microsoft.FSharp.Control.FSharpAsync")

/// The CLEANUP zones of a file: every `finally` block, every `with`
/// handler, and the callbacks handed to a CancellationToken's `Register`
/// (`ct.Register(fun () -> ...)` runs BECAUSE the token was cancelled).
/// A token handed to a call there, or a cancellation check placed there,
/// throws OperationCanceledException on the way out instead of cleaning
/// up — `tx.RollbackAsync()` after a cancelled `CommitAsync ct`.
let private cleanupZones (index: AstIndex.Index) (source: ISourceText) (check: FSharpCheckFileResults) =
    index.Exprs
    |> Array.collect (fun (_, e) ->
        match e with
        | SynExpr.TryFinally(finallyExpr = f) -> [| f.Range |]
        | SynExpr.TryWith(withCases = cases) ->
            cases
            |> List.map (fun (SynMatchClause(resultExpr = result)) -> result.Range)
            |> Array.ofList
        | SynExpr.App(isInfix = false; funcExpr = CallIdent methodId; argExpr = args) when
            methodId.idText = "Register" || methodId.idText = "UnsafeRegister"
            ->
            let lineText = source.GetLineString(methodId.idRange.EndLine - 1)

            let onToken =
                match
                    OptionModule.symbolUseAt
                        check
                        (methodId.idRange.EndLine, methodId.idRange.EndColumn, lineText, [ methodId.idText ])
                with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as mfv ->
                        OptionModule.enclosingFullName mfv = "System.Threading.CancellationToken"
                    | _ -> false
                | None -> false

            if onToken then [| args.Range |] else [||]
        | _ -> [||])

/// The last name of a callee (`Lazy`, `GetOrAdd`), through parens and type
/// applications; empty for anything else.
[<TailCall>]
let rec private lastCalleeName (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.TypeApp(expr = inner) -> lastCalleeName inner
    | SynExpr.Ident pid
    | CallIdent pid -> pid.idText
    | _ -> ""

let private isLazyType (t: SynType) =
    match t with
    | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)))
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText = "Lazy"
    | _ -> false

/// The SHARED-WORK zones of a file: a `lazy` body, the arguments of a `Lazy`
/// constructor, and the arguments of `GetOrAdd`/`AddOrUpdate`. What runs there
/// produces one value for every caller. With a caller's token in it, that
/// caller cancelling fails the others too, for as long as the value is held;
/// a `CancellationToken.None` there keeps the work independent of any one
/// caller. A synchronous factory would be safe (it throws and stores nothing),
/// but telling it apart needs the value's type, so it is refused with the rest.
let private sharedWorkZones (index: AstIndex.Index) =
    index.Exprs
    |> Array.choose (fun (_, e) ->
        match e with
        | SynExpr.Lazy(expr = body) -> Some body.Range
        | SynExpr.New(targetType = t; expr = args) when isLazyType t -> Some args.Range
        | SynExpr.App(isInfix = false; funcExpr = callee; argExpr = args) ->
            match lastCalleeName callee with
            | "Lazy"
            | "GetOrAdd"
            | "AddOrUpdate" -> Some args.Range
            | _ -> None
        | _ -> None)

/// Is `r` in shared work made under the token's binding? A binding inside the
/// zone receives its own token, which the value's other callers never see.
let private inSharedWork (zones: range[]) (bindingRange: range) (r: range) =
    zones
    |> Array.exists (fun z -> Range.rangeContainsRange z r && Range.rangeContainsRange bindingRange z)

/// Is the token's NAME rebound between its parameter and `r` — `[ for ct
/// in names -> ... ]`, a `let ct = ...`, a lambda or match variable — so
/// that `ct` at `r` may be something else entirely? Any pattern binding
/// the name inside the token's binding, ahead of `r`, counts: an
/// over-approximation of scope that only ever withholds a fix. A lambda's
/// parameters are not among the index's patterns: `lambdaParams` holds
/// them, (name, lambda range), and a lambda enclosing `r` that binds the
/// name counts too.
let private shadowedBefore
    (index: AstIndex.Index)
    (lambdaParams: (string * range) list)
    (name: string)
    (paramId: range)
    (bindingRange: range)
    (r: range)
    =
    (lambdaParams
     |> List.exists (fun (n, lambda) ->
         n = name
         && Range.rangeContainsRange bindingRange lambda
         && Range.rangeContainsRange lambda r))
    || (index.Pats
        |> Array.exists (fun (_, pat) ->
            let bound =
                match pat with
                | SynPat.Named(ident = SynIdent(ident = pid)) -> Some pid
                | SynPat.LongIdent(longDotId = SynLongIdent(id = [ pid ]); argPats = SynArgPats.Pats []) -> Some pid
                | _ -> None

            match bound with
            | Some id ->
                id.idText = name
                && not (Range.equals id.idRange paramId)
                && Range.rangeContainsRange bindingRange id.idRange
                && Position.posLt id.idRange.Start r.Start
            | None -> false))

/// Every lambda parameter named like one of `names`, with its lambda's range.
let private lambdaParamsNamed (index: AstIndex.Index) (names: Set<string>) =
    if names.IsEmpty then
        []
    else
        [
            for _, e in index.Exprs do
                match e with
                | SynExpr.Lambda(parsedData = Some(pats, _)) ->
                    for n in pats |> List.collect patBoundNames do
                        if names.Contains n then
                            yield n, e.Range
                | _ -> ()
        ]

/// Result types that are work which may still be running after the call.
let private pendingTypes =
    set
        [
            "System.Threading.Tasks.Task"
            "System.Threading.Tasks.Task`1"
            "System.Threading.Tasks.ValueTask"
            "System.Threading.Tasks.ValueTask`1"
            "System.Collections.Generic.IAsyncEnumerable`1"
            "Microsoft.FSharp.Control.FSharpAsync`1"
        ]

let private returnsPending (mfv: FSharpMemberOrFunctionOrValue) =
    try
        let t = OptionModule.stripAbbreviations mfv.ReturnParameter.Type

        t.HasTypeDefinition
        && (match t.TypeDefinition.TryFullName with
            | Some n -> pendingTypes.Contains n
            | None -> false)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The last two segments of a callee (`Async.AwaitTask`, `ignore`),
/// through parens and type applications; empty for anything else.
[<TailCall>]
let rec private calleeName (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.TypeApp(expr = inner) -> calleeName inner
    | SynExpr.Ident pid -> pid.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
        ids
        |> List.map (fun i -> i.idText)
        |> List.rev
        |> List.truncate 2
        |> List.rev
        |> String.concat "."
    | _ -> ""

/// The head of an application spine: `f` of `f a b`.
[<TailCall>]
let rec private spineHead (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = f) -> spineHead f
    | _ -> e

let private isPipe (op: SynExpr) =
    match op with
    | SynExpr.Ident id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> id.idText = "op_PipeRight"
    | _ -> false

let private isEquals (op: SynExpr) =
    match op with
    | SynExpr.Ident id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> id.idText = "op_Equality"
    | _ -> false

/// Is what sits at `r` left running: `|> ignore`, `|> Async.Start`, a bare
/// statement, a store, or the same around a `Task.Run` of it? Anything this
/// can't read isn't.
let rec private leftRunning (r: range) (path: SyntaxNode list) =
    let consumer (name: string) (outer: range) (rest: SyntaxNode list) =
        match name with
        | "ignore"
        | "Async.Start"
        | "Async.StartImmediate" -> true
        | "Task.Run"
        | "Factory.StartNew"
        | "Async.StartAsTask"
        | "Async.StartImmediateAsTask"
        | "Async.AwaitTask"
        | "Async.Ignore" -> leftRunning outer rest
        | _ -> false

    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren(range = outer) | SynExpr.Typed(range = outer) | SynExpr.Tuple(range = outer) | SynExpr.Lambda(
        range = outer)) :: rest -> leftRunning outer rest
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op; argExpr = a)) :: SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; argExpr = callee; range = outer)) :: rest when isPipe op && a.Range = r ->
        consumer (calleeName callee) outer rest
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a; range = outer)) :: rest when
        Range.rangeContainsRange a.Range r
        ->
        consumer (calleeName f) outer rest
    | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = a)) :: _ -> a.Range = r
    | SyntaxNode.SynExpr(SynExpr.Set _ | SynExpr.DotSet _ | SynExpr.LongIdentSet _) :: _ -> true
    | _ -> false

/// Is the nearest computation expression around these ancestors left running?
/// A bang inside it waits only for that expression, not for the caller.
[<TailCall>]
let rec private inWorkLeftRunning (path: SyntaxNode list) =
    match path with
    // awaited by the expression around it: what happens to that one decides
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App _) :: (SyntaxNode.SynExpr(SynExpr.DoBang _ | SynExpr.YieldOrReturnFrom _ | SynExpr.MatchBang _) :: above) ->
        inWorkLeftRunning above
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App _) :: (SyntaxNode.SynExpr(LetOrUseE lou) :: above) when
        lou.IsBang
        ->
        inWorkLeftRunning above
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App _) :: (SyntaxNode.SynBinding _ :: SyntaxNode.SynExpr(LetOrUseE lou) :: above) when
        lou.IsBang
        ->
        inWorkLeftRunning above
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App(range = outer)) :: rest ->
        leftRunning outer rest
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: _ -> false
    | _ :: rest -> inWorkLeftRunning rest
    | [] -> false

/// Is the work a call starts (at `r`, `path` its ancestors, nearest first)
/// waited for, here or by the caller - `do!`/`let!`/`return!`/`match!`,
/// returned as the binding's value, blocked on (`.Result`, `.Wait()`,
/// `Async.RunSynchronously`), combined into something that is (`|>
/// Async.AwaitTask`, `Task.WhenAll`, a `List.map` of such calls), or bound
/// to a local that is? Anything else - `|> ignore`, `Async.Start`, a bare
/// statement, a store, an argument elsewhere - may be fire-and-forget: work
/// meant to outlive the caller, which the caller's token would cancel when
/// the caller is done. FR0075 reads the same shapes for `use`.
let rec private waitedFor (index: AstIndex.Index) (depth: int) (r: range) (path: SyntaxNode list) : bool =
    let consumer (name: string) (outer: range) (rest: SyntaxNode list) =
        match name with
        | "Async.RunSynchronously"
        | "Task.WaitAll"
        | "Task.WaitAny" -> true
        // still pending: what happens to the combined value decides
        | "Async.AwaitTask"
        | "Async.AwaitValueTask"
        | "Async.Ignore"
        | "Async.Catch"
        | "Async.StartAsTask"
        | "Async.StartImmediateAsTask"
        | "Async.StartChild"
        | "Async.Parallel"
        | "Async.Sequential"
        | "Task.WhenAll"
        | "Task.WhenAny"
        | "List.map"
        | "Array.map"
        | "Seq.map"
        | "List.mapi"
        | "Array.mapi"
        | "Seq.mapi" -> waitedFor index depth outer rest
        // `ignore`, `Async.Start`, and anything this rule cannot read
        | _ -> false

    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren(range = pr) | SynExpr.Typed(range = pr) | SynExpr.Tuple(range = pr) | SynExpr.ArrayOrList(
        range = pr) | SynExpr.ArrayOrListComputed(range = pr)) :: rest -> waitedFor index depth pr rest
    | SyntaxNode.SynExpr(SynExpr.DoBang _ | SynExpr.YieldOrReturnFrom _ | SynExpr.MatchBang _) :: rest ->
        not (inWorkLeftRunning rest)
    // `.Result`, `.Wait()`, `.GetAwaiter().GetResult()`
    | SyntaxNode.SynExpr(SynExpr.DotGet(expr = e; longDotId = SynLongIdent(id = first :: _))) :: _ when e.Range = r ->
        first.idText = "Result" || first.idText = "Wait" || first.idText = "GetAwaiter"
    // `e |> f`: the pipe hands e to f
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op; argExpr = a)) :: SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; argExpr = callee; range = outer)) :: rest when isPipe op && a.Range = r ->
        consumer (calleeName callee) outer rest
    // `xs |> f` where f's result is e: the pipe's value is e
    | SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = op); argExpr = a; range = outer)) :: rest when
        isPipe op && a.Range = r
        ->
        waitedFor index depth outer rest
    // `f e`, `f (a, e)`
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a; range = outer)) :: rest when
        Range.rangeContainsRange a.Range r
        ->
        consumer (calleeName f) outer rest
    // a lambda returning it: what happens to the lambda decides (a `List.map`)
    | SyntaxNode.SynExpr(SynExpr.Lambda(range = lr)) :: rest -> waitedFor index depth lr rest
    // a statement drops it; the last expression is the sequence's value
    | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = a; expr2 = b; range = sr)) :: rest ->
        // `[| a; b |]` spells its elements as a sequence: an element, not a statement
        let rec listElement (p: SyntaxNode list) =
            match p with
            | SyntaxNode.SynExpr(SynExpr.Sequential _) :: more -> listElement more
            | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed(range = lr)) :: more -> Some(lr, more)
            | _ -> None

        match listElement rest with
        | Some(lr, more) -> waitedFor index depth lr more
        | None -> a.Range <> r && b.Range = r && waitedFor index depth sr rest
    | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = c; range = ir)) :: rest when c.Range <> r ->
        waitedFor index depth ir rest
    | SyntaxNode.SynMatchClause _ :: SyntaxNode.SynExpr m :: rest -> waitedFor index depth m.Range rest
    // `let! x = call`: the walker gives a bang's right-hand side the `let!` as parent
    | SyntaxNode.SynExpr(LetOrUseE lou) :: rest when lou.IsBang && not (Range.rangeContainsRange lou.Body.Range r) ->
        not (inWorkLeftRunning rest)
    | SyntaxNode.SynBinding(SynBinding(headPat = headPat)) :: rest ->
        match rest with
        | SyntaxNode.SynExpr(LetOrUseE lou) :: above when lou.IsBang -> not (inWorkLeftRunning above)
        | SyntaxNode.SynExpr(LetOrUseE lou) :: _ ->
            // `let t = client.SendAsync m` then `do! t`: the local's uses decide
            match headPat with
            | SynPat.Named(ident = SynIdent(ident = local)) when depth < 3 ->
                index.Exprs
                |> Array.exists (fun (p, e) ->
                    match e with
                    | SynExpr.Ident id when
                        id.idText = local.idText && Range.rangeContainsRange lou.Body.Range id.idRange
                        ->
                        waitedFor index (depth + 1) id.idRange p
                    | _ -> false)
            | _ -> false
        // a member's or a module function's body: returned to the caller
        | _ -> true
    | _ -> false

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let resolveMember (id: Ident) =
            let lineText = source.GetLineString(id.idRange.EndLine - 1)

            match
                OptionModule.symbolUseAt check (id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ])
            with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv -> Some(symbolUse, mfv)
                | _ -> None
            | None -> None

        // every binding parameter annotated `: CancellationToken`, with the
        // binding it belongs to — the scope a call must sit inside
        let tokenParams =
            [
                for path, pat in index.Pats do
                    match pat with
                    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)); targetType = t) when
                        isCancellationTokenType t
                        ->
                        let binding =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                                | _ -> None)

                        match binding with
                        | Some bindingRange -> yield id.idText, bindingRange, id.idRange
                        | None -> ()
                    | _ -> ()
            ]

        // the `with` handlers and `finally` blocks of every try: a call
        // there is CLEANUP — `tx.RollbackAsync()` after a cancelled
        // `CommitAsync ct`. Handing it the same token makes the rollback
        // throw OperationCanceledException on the way out instead of
        // rolling back, so the transaction is left hanging. No token is
        // ever injected into one (the same exclusion FR0079 applies to its
        // bridge sites), nor into a token's Register callback
        let cleanupRanges = cleanupZones index source check

        let inCleanup (callRange: range) =
            cleanupRanges |> Array.exists (fun z -> Range.rangeContainsRange z callRange)

        let sharedZones = sharedWorkZones index

        let lambdaParams =
            lambdaParamsNamed index (tokenParams |> List.map (fun (name, _, _) -> name) |> Set.ofList)

        // the single in-scope token for a call site, if there is exactly one
        let tokenFor (callRange: range) =
            let inScope =
                tokenParams
                |> List.filter (fun (_, bindingRange, _) -> Range.rangeContainsRange bindingRange callRange)

            match inScope |> List.map (fun (name, _, _) -> name) |> List.distinct with
            | [ name ] when
                not (inCleanup callRange)
                && not (
                    inScope
                    |> List.exists (fun (_, bindingRange, _) -> inSharedWork sharedZones bindingRange callRange)
                )
                // `ct` at the call must still BE the parameter
                && not (
                    inScope
                    |> List.exists (fun (n, bindingRange, paramId) ->
                        shadowedBefore index lambdaParams n paramId bindingRange callRange)
                )
                ->
                Some name
            | _ -> None

        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = CallIdent methodId; argExpr = args) ->
                    // .NET tupled call shapes only — the edit appends inside
                    // the parentheses
                    let callArity =
                        match args with
                        | SynExpr.Const(SynConst.Unit, _) -> Some 0
                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) when not (es |> List.exists isNamedArg) ->
                            Some es.Length
                        | SynExpr.Paren(expr = SynExpr.Tuple _) -> None
                        | SynExpr.Paren(expr = inner) when not (isNamedArg inner) -> Some 1
                        | _ -> None

                    // the token may already BE one of the arguments —
                    // `CreateLinkedTokenSource(ct)` takes the token as its
                    // PAYLOAD, and a params/two-token sibling overload would
                    // happily compile `(ct, ct)`
                    let alreadyPassed token =
                        let isToken (a: SynExpr) =
                            match stripParens a with
                            | SynExpr.Ident i -> i.idText = token
                            | _ -> false

                        match args with
                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> es |> List.exists isToken
                        | SynExpr.Paren(expr = inner) -> isToken inner
                        | _ -> false

                    match callArity, tokenFor expr.Range with
                    | Some arity, Some token when not (alreadyPassed token) ->
                        match resolveMember methodId with
                        | Some(symbolUse, mfv) ->
                            match mfv with
                            | mfv when
                                mfv.IsMember
                                && not mfv.IsProperty
                                && not (schedulesDelegate mfv)
                                // work started and not waited for is the author's to detach
                                && (not (returnsPending mfv) || waitedFor index 0 expr.Range path)
                                ->
                                let shapes = parameterShapes symbolUse.DisplayContext mfv

                                let tokenAccepted =
                                    match shapes with
                                    | Some ps when ps.Length = arity ->
                                        // is there a sibling overload with the
                                        // same prefix plus a trailing token?
                                        (try
                                            match mfv.DeclaringEntity with
                                            | Some entity ->
                                                entity.MembersFunctionsAndValues
                                                |> Seq.exists (fun m ->
                                                    m.DisplayName = mfv.DisplayName
                                                    && (match parameterShapes symbolUse.DisplayContext m with
                                                        | Some mps when mps.Length = arity + 1 ->
                                                            List.truncate arity mps = ps
                                                            // a `ValueTask` sibling doesn't fit `Async.AwaitTask` or a `Task` return
                                                            && m.ReturnParameter.Type.Format symbolUse.DisplayContext =
                                                                mfv.ReturnParameter.Type.Format
                                                                    symbolUse.DisplayContext
                                                            && (m.CurriedParameterGroups
                                                                |> Seq.collect id
                                                                |> Seq.tryLast
                                                                |> Option.map (fun p -> isCancellationToken p.Type)
                                                                |> Option.defaultValue false)
                                                        | _ -> false))
                                            | None -> false
                                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                             false)
                                    | Some ps when ps.Length = arity + 1 ->
                                        // the method itself has a trailing
                                        // OPTIONAL token the call omits
                                        (try
                                            let last = mfv.CurriedParameterGroups |> Seq.collect id |> Seq.last
                                            last.IsOptionalArg && isCancellationToken last.Type
                                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                             false)
                                    | _ -> false

                                if tokenAccepted then
                                    match args with
                                    | SynExpr.Const(SynConst.Unit, unitRange) ->
                                        {
                                            Range = unitRange
                                            Original = "()"
                                            Replacement = $"({token})"
                                            MethodName = methodId.idText
                                            TokenName = token
                                            Kind = TokenGap.Omitted
                                        }
                                    | SynExpr.Paren(expr = inner) ->
                                        // a trailing lambda, match or if runs
                                        // to the closing parenthesis: `, ct`
                                        // appended bare joins its BODY as a
                                        // tuple —
                                        // `Then(fun (_: Task) -> (), ct)`
                                        // returns `unit * CancellationToken`.
                                        // Such an argument is wrapped first
                                        let lastElement =
                                            match inner with
                                            | SynExpr.Tuple(exprs = es) -> List.last es
                                            | e -> e

                                        let openEnded =
                                            match lastElement with
                                            | SynExpr.Lambda _
                                            | SynExpr.MatchLambda _
                                            | SynExpr.Match _
                                            | SynExpr.IfThenElse _
                                            | SynExpr.TryWith _
                                            | SynExpr.TryFinally _
                                            | SynExpr.Sequential _
                                            | SynExpr.LetOrUse _ -> true
                                            | _ -> false

                                        if openEnded then
                                            {
                                                Range = lastElement.Range
                                                Original = textOfRange source lastElement.Range
                                                Replacement = $"({textOfRange source lastElement.Range}), {token}"
                                                MethodName = methodId.idText
                                                TokenName = token
                                                Kind = TokenGap.Omitted
                                            }
                                        else
                                            let at = Range.mkRange expr.Range.FileName inner.Range.End inner.Range.End

                                            {
                                                Range = at
                                                Original = ""
                                                Replacement = $", {token}"
                                                MethodName = methodId.idText
                                                TokenName = token
                                                Kind = TokenGap.Omitted
                                            }
                                    | _ -> ()
                            | _ -> ()
                        | None -> ()
                    | _ -> ()
                | _ -> ()

                // propagation: `CancellationToken.None` as an ARGUMENT while
                // the enclosing binding receives a real token — the chain is
                // cut one call too early on purpose-by-accident
                match expr with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when pathEndsWith "CancellationToken" "None" ids ->
                    match tokenFor expr.Range with
                    | Some token ->
                        // only as an argument: replacing a stored binding's
                        // RHS would rewrite intent this scan cannot see
                        let callHolding (r: range) =
                            index.Exprs
                            |> Array.tryPick (fun (callPath, e) ->
                                match e with
                                | SynExpr.App(funcExpr = callee; argExpr = a) when
                                    Range.equals a.Range r
                                    || (match a with
                                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) ->
                                            es |> List.exists (fun x -> Range.equals x.Range r)
                                        | SynExpr.Paren(expr = inner) -> Range.equals inner.Range r
                                        | _ -> false)
                                    ->
                                    Some(callPath, e, callee)
                                | _ -> None)

                        let parametersOf (mfv: FSharpMemberOrFunctionOrValue) =
                            try
                                mfv.CurriedParameterGroups |> Seq.collect id |> List.ofSeq
                            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                []

                        let takesParameterNamed (callee: SynExpr) (name: string) =
                            match spineHead callee with
                            | SynExpr.Ident calleeId
                            | CallIdent calleeId ->
                                match resolveMember calleeId with
                                | Some(_, mfv) -> parametersOf mfv |> List.exists (fun p -> p.Name = Some name)
                                | None -> false
                            | _ -> false

                        // `M(cancellationToken = None)` is an argument of M; `x = None` is an operand, not an argument
                        let enclosingCall =
                            match callHolding expr.Range with
                            | Some(_,
                                   comparison,
                                   SynExpr.App(isInfix = true; funcExpr = op; argExpr = SynExpr.Ident named)) when
                                isEquals op
                                ->
                                match callHolding comparison.Range with
                                | Some(_, _, callee) as call when takesParameterNamed callee named.idText -> call
                                | _ -> None
                            | Some(_, _, SynExpr.App(isInfix = true; funcExpr = op)) when not (isPipe op) -> None
                            | Some(_, SynExpr.App(isInfix = true; funcExpr = op), _) when not (isPipe op) -> None
                            | call -> call

                        let isArgument = enclosingCall.IsSome

                        // the function at the head of `f a b`, or the member
                        // of `x.M(a, b)`; a function value resolves to no
                        // pending return, and keeps the fix
                        let calleeSymbol =
                            enclosingCall
                            |> Option.bind (fun (_, _, callee) ->
                                match spineHead callee with
                                | SynExpr.Ident calleeId
                                | CallIdent calleeId -> resolveMember calleeId
                                | _ -> None)

                        // the callee's parameter holds a token: `Some None`,
                        // `defaultArg o None` and `x.Equals None` keep their value
                        let takesToken =
                            let isTokenParameter (p: FSharpParameter) =
                                isCancellationToken p.Type
                                || (p.IsOptionalArg
                                    && p.Type.GenericArguments.Count = 1
                                    && isCancellationToken p.Type.GenericArguments[0])

                            let constructsUnionCase (callee: SynExpr) =
                                match spineHead callee with
                                | SynExpr.Ident id ->
                                    let lineText = source.GetLineString(id.idRange.EndLine - 1)

                                    match
                                        OptionModule.symbolUseAt
                                            check
                                            (id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ])
                                    with
                                    | Some symbolUse -> symbolUse.Symbol :? FSharpUnionCase
                                    | None -> false
                                | _ -> false

                            match enclosingCall, calleeSymbol with
                            | _, Some(_, mfv) ->
                                let parameters = parametersOf mfv

                                mfv.DisplayName <> "Equals"
                                && (parameters.IsEmpty || parameters |> List.exists isTokenParameter)
                            | Some(_, _, callee), None -> not (constructsUnionCase callee)
                            | None, None -> false

                        // an explicit None on Task.Run / StartNew / a
                        // continuation is the author choosing to always start
                        // the work
                        let schedulesWork =
                            calleeSymbol |> Option.exists (fun (_, mfv) -> schedulesDelegate mfv)

                        // so is one on work left running: `|> ignore`, a bare
                        // statement, a store other callers read
                        let detached =
                            match enclosingCall, calleeSymbol with
                            | Some(callPath, call, _), Some(_, mfv) ->
                                returnsPending mfv && not (waitedFor index 0 call.Range callPath)
                            | _ -> false

                        let typedGate =
                            let noneId = List.last ids
                            let lineText = source.GetLineString(noneId.idRange.EndLine - 1)

                            match
                                OptionModule.symbolUseAt
                                    check
                                    (noneId.idRange.EndLine, noneId.idRange.EndColumn, lineText, [ noneId.idText ])
                            with
                            | Some symbolUse ->
                                match symbolUse.Symbol with
                                | :? FSharpMemberOrFunctionOrValue as p ->
                                    (try
                                        p.DeclaringEntity
                                        |> Option.bind (fun e -> e.TryFullName)
                                        |> Option.map (fun n -> n.StartsWith "System.Threading.CancellationToken")
                                        |> Option.defaultValue false
                                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                         false)
                                | _ -> false
                            | None -> false

                        if isArgument && takesToken && typedGate && not schedulesWork && not detached then
                            {
                                Range = expr.Range
                                Original = textOfRange source expr.Range
                                Replacement = token
                                MethodName = "CancellationToken.None"
                                TokenName = token
                                Kind = TokenGap.NonePassed
                            }
                    | None -> ()
                | _ -> ()
        ]

// ---- the loop that never observes the token ----

/// A loop awaiting inside, in a binding that receives a CancellationToken
/// and never reads it in the loop: no call in the body takes it, nothing
/// checks `IsCancellationRequested`, no local built with it is stepped,
/// so cancellation cannot stop the loop. Outside `async { }`, which
/// observes the token at every bind by itself; `task { }` does not.
type LoopSuggestion =
    {
        /// The whole loop.
        Range: range
        TokenName: string
        /// `token.ThrowIfCancellationRequested()` as the body's first
        /// statement (CR0170's fix), where the body starts on its own line
        /// below the loop header; a one-line body stays a note.
        Fix: (range * string * string) option
    }

/// `findUnobservedLoops` over call suggestions `find` already produced for
/// this file: the analyzer reports both, so it runs `find` once.
let findUnobservedLoopsWith
    (calls: Suggestion list)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : LoopSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let tokenParams =
            [
                for path, pat in index.Pats do
                    match pat with
                    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)); targetType = t) when
                        isCancellationTokenType t
                        ->
                        let binding =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                                | _ -> None)

                        match binding with
                        | Some bindingRange -> yield id.idText, bindingRange, id.idRange
                        | None -> ()
                    | _ -> ()
            ]

        let lambdaParams =
            lambdaParamsNamed index (tokenParams |> List.map (fun (name, _, _) -> name) |> Set.ofList)

        let sharedZones = sharedWorkZones index

        // the one token in scope, as `find` reads it
        let tokenFor (r: range) =
            let inScope =
                tokenParams
                |> List.filter (fun (_, bindingRange, _) -> Range.rangeContainsRange bindingRange r)

            match inScope |> List.map (fun (name, _, _) -> name) |> List.distinct with
            | [ name ] when
                // a check there would let one caller fail the value's others
                not (
                    inScope
                    |> List.exists (fun (_, bindingRange, _) -> inSharedWork sharedZones bindingRange r)
                )
                && not (
                    inScope
                    |> List.exists (fun (n, bindingRange, paramId) ->
                        shadowedBefore index lambdaParams n paramId bindingRange r)
                )
                ->
                Some name
            | _ -> None

        // the binding the token belongs to
        let scopeOf (token: string) (r: range) =
            tokenParams
            |> List.tryPick (fun (name, bindingRange, _) ->
                if name = token && Range.rangeContainsRange bindingRange r then
                    Some bindingRange
                else
                    None)

        // locals of that binding built WITH the token — `let enumerator =
        // source.GetAsyncEnumerator ct`, `let reader = open ct`: a
        // loop stepping one of them observes the token through it
        let carriers (token: string) (scope: range) =
            AstIndex.exprsWithin index scope
            |> Array.collect (fun (_, e) ->
                match e with
                | LetOrUseE lou when Range.rangeContainsRange scope e.Range ->
                    // a value, or a local function whose body reads the
                    // token (`let step () = task { do! Task.Delay(10, ct) }`)
                    lou.Bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = rhs)
                        | SynBinding(
                            headPat = SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))); expr = rhs)
                        | SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])); expr = rhs) when
                            System.Text.RegularExpressions.Regex.IsMatch(
                                textOfRange source rhs.Range,
                                identifierPattern token
                            )
                            ->
                            Some id.idText
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])

        let mentionsAny (names: string seq) (text: string) =
            names
            |> Seq.exists (fun n -> System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern n))

        // a loop that `find` already offers a token inside needs no second
        // message: the fix makes the loop observe it
        let offeredInside =
            calls
            |> List.filter (fun s -> s.Kind = TokenGap.Omitted)
            |> List.map (fun s -> s.Range)

        let underAsync (path: SyntaxNode list) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr _)) ->
                    builder.idText.StartsWith "async"
                | _ -> false)

        // a loop in a `finally`, a `with` handler or a token's Register
        // callback is cleanup: nothing should throw there, a cancellation
        // check least of all (as CR0170 draws it)
        let cleanupRanges = cleanupZones index source check

        let underFinally (_: SyntaxNode list) (r: range) =
            cleanupRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

        let bindsInside (r: range) =
            AstIndex.exprsWithin index r
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (match e with
                    | LetOrUseE lou -> lou.IsBang
                    | SynExpr.DoBang _
                    | SynExpr.MatchBang _ -> true
                    | _ -> false))

        // the fix: a zero-width insert at the body's first statement, the
        // statement itself moving to the next line at its own indentation
        let checkAtTop (token: string) (loop: SynExpr) =
            let body =
                match loop with
                | SynExpr.While(doExpr = b)
                | SynExpr.ForEach(bodyExpr = b)
                | SynExpr.For(doBody = b) -> Some b
                | _ -> None

            match body with
            | Some b when
                b.Range.StartLine > loop.Range.StartLine
                // the body heads its line: nothing before it to move
                && (source.GetLineString(b.Range.StartLine - 1)).Substring(0, b.Range.StartColumn).Trim() = ""
                ->
                let at = Range.mkRange loop.Range.FileName b.Range.Start b.Range.Start
                let indent = String.replicate b.Range.StartColumn " "
                Some(at, "", $"{token}.ThrowIfCancellationRequested()\n{indent}")
            | _ -> None

        let unobserved =
            [
                for path, e in index.Exprs do
                    // an AWAITING loop: one that runs long enough for
                    // cancellation to matter, and whose binds are where a
                    // token would be observed. A synchronous `while` draining
                    // a buffer (`while reader.TryRead(&tok) do`) is bounded
                    // by what is already there
                    let loop =
                        match e with
                        | SynExpr.While _
                        | SynExpr.ForEach _
                        | SynExpr.For _ -> bindsInside e.Range
                        | _ -> false

                    if loop && not (underAsync path) && not (underFinally path e.Range) then
                        match tokenFor e.Range with
                        | Some token ->
                            let text = textOfRange source e.Range

                            let observed =
                                System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern token)
                                || (match scopeOf token e.Range with
                                    | Some scope -> mentionsAny (carriers token scope) text
                                    | None -> false)

                            if
                                not observed
                                && not (offeredInside |> List.exists (fun r -> Range.rangeContainsRange e.Range r))
                            then
                                {
                                    Range = e.Range
                                    TokenName = token
                                    Fix = checkAtTop token e
                                }
                        | None -> ()
            ]

        // the outermost loop carries the note; a check at its top covers
        // the loops nested in it
        unobserved
        |> List.filter (fun s ->
            not (
                unobserved
                |> List.exists (fun outer ->
                    not (Range.equals outer.Range s.Range)
                    && Range.rangeContainsRange outer.Range s.Range)
            ))

/// Unobserved loops, with `find` run here.
let findUnobservedLoops (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) =
    findUnobservedLoopsWith (find parseTree source check) parseTree source check
