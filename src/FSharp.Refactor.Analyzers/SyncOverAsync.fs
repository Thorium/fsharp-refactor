/// Refactoring (correctness/perf, CA1849 + the VSTHRD family): blocking
/// waits inside an async or task computation expression.
///
///     task {
///         let x = t.Result                      // blocks the thread
///         other.Wait()                          // blocks
///         let y = (f ()).GetAwaiter().GetResult()   // blocks
///         let z = comp |> Async.RunSynchronously    // blocks
///         Thread.Sleep 100                      // blocks
///         ...
///     }
///
/// Sync-over-async inside a CE holds a thread-pool thread while awaiting
/// work that wants those same threads — the classic starvation/deadlock
/// recipe. The bind forms (`let!`, `do!`, `Async.AwaitTask`) release the
/// thread instead.
///
/// `Thread.Sleep n` in statement position gets a fix (`do! Async.Sleep n`
/// in async, `do! Task.Delay n` in task), and so do a statement-position
/// `t.Wait()` (`do! t`) and `Task.WaitAll(...)` (`do! Task.WhenAll(...)`);
/// a `let x = <blocking>` directly under the builder becomes a `let!`. A
/// blocking call inside `Assert.Throws<E>(fun () -> ...)` moves with the
/// assert to the framework's async spelling. The other shapes are advice —
/// rewriting them to binds restructures the surrounding code. The shapes
/// and their awaitables are shared with FR0142 through BlockingSites.
///
/// All receivers/methods are typed-gated (Task.Result, Task.Wait, an
/// awaiter's GetResult, FSharp.Core's RunSynchronously, Thread.Sleep), so
/// a user type with a `Result` property never matches. Only the innermost
/// enclosing CE reports a site, and no fix is offered inside a lambda
/// (where `do!` would not compile) - with one exception, the fix that
/// removes the lambda: `Task.Run(fun () -> c |> Async.RunSynchronously)`
/// becomes `c |> Async.StartAsTask`.
module FSharp.Refactor.SyncOverAsync

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type BlockKind =
    | TaskResult
    | TaskWait
    | AwaiterGetResult
    | RunSynchronously
    | ThreadSleep
    /// A synchronisation primitive's blocking wait inside a CE —
    /// `ManualResetEventSlim.Wait()`, `SemaphoreSlim.Wait()`,
    /// `WaitHandle.WaitOne()`, `Barrier.SignalAndWait()`, `Thread.Join()`,
    /// `Monitor.Wait(o)` — named as `Type.Method()` for the message. Not
    /// task-typed, so no bind exists; outside a CE it is ordinary
    /// synchronous code and never reported.
    | PrimitiveWait of string
    /// `.Result` read on the antecedent inside its own `ContinueWith`
    /// continuation: complete by definition, so nothing blocks — but a
    /// FAULTED antecedent throws its exception wrapped in an
    /// AggregateException there (the compiler's AsyncMemoize stored the
    /// wrapper and rethrew it to every awaiter). The continuation is a
    /// bind: the plain shape becomes `task { let! r = t; return ... }`,
    /// which gets the exception itself; only where a task builder exists
    /// (FSharp.Core 6+, not Fable) — before that ContinueWith IS the bind
    /// and the read is not reported.
    | AntecedentResult

type Suggestion =
    {
        Range: range
        Kind: BlockKind
        /// The enclosing builder ("async"/"task"/"backgroundTask"), or None
        /// when the site is outside any CE (GetResult only — it is an
        /// antipattern everywhere).
        Builder: string option
        /// (range, original, replacement) edits: Thread.Sleep in statement
        /// position, or a GetResult binding becoming a let! bind. These
        /// move code TOWARD async and auto-apply.
        Fixes: (range * string * string) list
        /// The sync-sibling swap for a boundary GetResult — offered in
        /// editors and behind the `"FR0049": { "syncSwap": 1 }` config
        /// knob only, never auto-applied: async-in-sync is usually a
        /// waypoint toward a full-async refactor, and swapping to the
        /// sync API walks the code the other way.
        AlternativeFixes: (range * string * string) list
        /// For a BOUNDARY site (Builder = None): the task-typed receiver
        /// being drained, when the shape exposes one — `t.Result` gives
        /// `t`, `t.GetAwaiter().GetResult()` gives `t`. The taskify fix
        /// binds this with let!/return!.
        Receiver: range voption
        /// For a CE site: the call sits inside a lambda within the
        /// computation (a callback, a Func), where the builder's bind
        /// cannot reach it — the lambda's signature is the sync boundary.
        InLambda: bool
        /// For a CE site: the call sits in a `finally` block of the
        /// computation, where no `let!`/`do!` may appear at all — the
        /// wait has to move out of the handler before it can become a
        /// bind, so the note names that and offers nothing.
        InFinally: bool
    }

let private ceBuilders = set [ "async"; "task"; "backgroundTask" ]

/// Does the identifier's enclosing entity satisfy the predicate?
/// Task and ValueTask both block on .Result/.Wait — the BCL's async I/O
/// returns ValueTask everywhere post-core, so a Task-only prefix test
/// missed most modern blocking sites.
let private taskFamily (entity: string) =
    entity.StartsWith "System.Threading.Tasks.Task"
    || entity.StartsWith "System.Threading.Tasks.ValueTask"

let private enclosingEntityOf (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> OptionModule.enclosingFullName value
        | _ -> ""
    | None -> ""

let private fullNameOf (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> OptionModule.fullNameOf value
        | _ -> ""
    | None -> ""

/// The last identifier of a member-call function expression.
[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = [ id ])) -> ValueSome id
    | _ -> ValueNone

/// `RECV.GetAwaiter()` — the expression whose awaiter is being drained.
[<return: Struct>]
let private (|AwaiterReceiver|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ aw ]))
        argExpr = UnitConst) when aw.idText = "GetAwaiter" -> ValueSome recv
    | _ -> ValueNone

/// The range of a dotted path minus its last segment: `t.tail.Result`
/// gives `t.tail`.
let private prefixRangeOf (e: SynExpr) (ids: Ident list) =
    let prefix = ids |> List.take (ids.Length - 1)
    Range.mkRange e.Range.FileName (List.head prefix).idRange.Start (List.last prefix).idRange.End

/// The receiver's source range, covering both parse shapes: a DotGet on a
/// call result, and the flat LongIdent path `t.GetAwaiter` a simple
/// identifier receiver parses to.
[<return: Struct>]
let private (|AwaiterReceiverRange|_|) (e: SynExpr) =
    match e with
    | AwaiterReceiver recv -> ValueSome recv.Range
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = UnitConst) when
        ids.Length >= 2 && (List.last ids).idText = "GetAwaiter"
        ->
        ValueSome(prefixRangeOf e ids)
    | _ -> ValueNone

/// A full `Async.RunSynchronously` application whose only argument is the
/// computation: the pipe form, or direct application of a single plain
/// argument. A tuple argument carries timeout/cancellation and cannot
/// become a bind.
[<return: Struct>]
let private (|RunSyncApplication|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        funcExpr = SynExpr.App(isInfix = true; funcExpr = pipeOp; argExpr = comp)
        argExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        (match pipeOp with
         | SynExpr.Ident op -> op.idText = "op_PipeRight"
         | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) -> op.idText = "op_PipeRight"
         | _ -> false)
        && pathEndsWith "Async" "RunSynchronously" ids
        ->
        ValueSome comp
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = comp) when
        pathEndsWith "Async" "RunSynchronously" ids
        && (match stripParens comp with
            | SynExpr.Tuple _ -> false
            | _ -> true)
        ->
        ValueSome comp
    | _ -> ValueNone

let private isPipeRight (e: SynExpr) =
    match e with
    | SynExpr.Ident op -> op.idText = "op_PipeRight"
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) -> op.idText = "op_PipeRight"
    | _ -> false

/// `Task.Run(fun () -> <comp> |> Async.RunSynchronously)`, with or without a
/// trailing `|> ignore` (the flag says which). Task.Run queues the lambda to
/// the thread pool and hands back its Task, which is exactly what
/// `Async.StartAsTask` does - except StartAsTask does not park a pool thread
/// on the result. (`Async.StartImmediateAsTask` would be the wrong twin: it
/// runs on the CALLING thread until the first await, which Task.Run never
/// does.) Only the plain shape qualifies - one `fun () ->` lambda, no
/// cancellation token or scheduler, and a body that is nothing but the
/// blocking call - because anything else in the lambda has to keep running
/// on the pool.
///
/// One behaviour does change, in the rare non-happy path. A cancelled
/// computation gives a CANCELLED task here, where Task.Run gives one
/// FAULTED with the OperationCanceledException (TPL only reports Canceled
/// when the exception matches the task's own token, and Task.Run has none).
/// `let!` therefore raises TaskCanceledException instead of the original.
/// That is the more semantically correct of the two - a cancelled
/// computation did not fail - and no handler has to move for it, because
/// TaskCanceledException DERIVES from OperationCanceledException: anything
/// that caught the old exception catches the new one. The only flip runs
/// the other way, and only for a handler written as `:? TaskCanceledException`
/// specifically, which now catches a cancellation it used to let past.
let private taskRunOfRunSync (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        pathEndsWith "Task" "Run" ids
        && (enclosingEntityOf check source (List.last ids)).StartsWith "System.Threading.Tasks.Task"
        ->
        match stripParens arg with
        | SynExpr.Lambda(args = lambdaArgs; body = lambdaBody; parsedData = parsed) when
            // `fun () ->` and nothing else: unit erases to an empty simple-pat
            // list, and the parsed form spells it either bare or parenthesised
            (match lambdaArgs with
             | SynSimplePats.SimplePats(pats = []) -> true
             | _ -> false)
            && (match parsed with
                | Some([ SynPat.Const(SynConst.Unit, _) ], _)
                | Some([ SynPat.Paren(SynPat.Const(SynConst.Unit, _), _) ], _) -> true
                | None -> true
                | _ -> false)
            ->
            let body =
                match parsed with
                | Some(_, parsedBody) -> parsedBody
                | None -> lambdaBody

            match stripParens body with
            | RunSyncApplication comp -> ValueSome(comp, false)
            | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = pipeOp; argExpr = inner)
                          argExpr = SynExpr.Ident ign) when isPipeRight pipeOp && ign.idText = "ignore" ->
                match stripParens inner with
                | RunSyncApplication comp -> ValueSome(comp, true)
                | _ -> ValueNone
            | _ -> ValueNone
        | _ -> ValueNone
    | _ -> ValueNone

/// Wrap an expression's text in parentheses unless it is a bare
/// identifier path — `Async.AwaitTask client.GetAsync(u)` would apply to
/// the wrong thing.
let private asArgument (text: string) =
    // one pair of parentheses around the whole text is atomic already
    let parenthesized =
        text.StartsWith "("
        && text.EndsWith ")"
        && (let mutable depth = 0
            let mutable closedEarly = false

            for i in 0 .. text.Length - 2 do
                if text.[i] = '(' then
                    depth <- depth + 1
                elif text.[i] = ')' then
                    depth <- depth - 1

                    if depth = 0 then
                        closedEarly <- true

            not closedEarly)

    if parenthesized || Regex.IsMatch(text, @"^[A-Za-z_][\w'.]*$") then
        text
    else
        $"({text})"

/// Is a type Task/ValueTask/Async — i.e. still asynchronous?
let private isAwaitableType (t: FSharpType) =
    try
        match t.StripAbbreviations().TypeDefinition.TryFullName with
        | Some full ->
            full.StartsWith "System.Threading.Tasks.Task"
            || full.StartsWith "System.Threading.Tasks.ValueTask"
            || full.StartsWith "Microsoft.FSharp.Control.FSharpAsync"
        | None -> false
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// A boundary `RECV.SomethingAsync(args).GetAwaiter().GetResult()` whose
/// declaring entity provably offers a synchronous `Something` with the
/// same argument count: the call swaps to the sibling and the awaiter
/// chain drops. Verified against the typed tree, never guessed from the
/// name alone.
let private syncSiblingFix
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (recv: SynExpr)
    (whole: SynExpr)
    : (range * string * string) list =
    let callIdent =
        match recv with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = ids)); argExpr = arg)
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
            not ids.IsEmpty
            ->
            Some(List.last ids, arg)
        | _ -> None

    match callIdent with
    | Some(id, arg) when id.idText.EndsWith "Async" && id.idText.Length > "Async".Length ->
        let trimmed = id.idText.Substring(0, id.idText.Length - "Async".Length)

        let argCount =
            match stripParens arg with
            | SynExpr.Const(SynConst.Unit, _) -> 0
            | SynExpr.Tuple(exprs = es) -> es.Length
            | _ -> 1

        let r = id.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        let hasSibling =
            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    match mfv.DeclaringEntity with
                    | Some entity ->
                        entity.MembersFunctionsAndValues
                        |> Seq.exists (fun m ->
                            m.DisplayName = trimmed
                            // a PROPERTY named like the sibling would turn
                            // `x.Foo(args)` into applying unit to a value
                            && not m.IsProperty
                            && not m.IsPropertyGetterMethod
                            && (m.CurriedParameterGroups |> Seq.sumBy Seq.length) = argCount
                            && not (isAwaitableType m.ReturnParameter.Type))
                    | None -> false
                | _ -> false
            | None -> false

        if hasSibling then
            let dropRange = Range.mkRange whole.Range.FileName recv.Range.End whole.Range.End

            [ id.idRange, id.idText, trimmed; dropRange, textOfRange source dropRange, "" ]
        else
            []
    | _ -> []

/// The completion probes a `.Result` read is legitimately guarded by: the
/// ValueTask synchronous fast path (`if vt.IsCompletedSuccessfully then
/// vt.Result else task { let! r = vt ... }`) never blocks.
let private completionTestNames = set [ "IsCompleted"; "IsCompletedSuccessfully" ]

/// Blocking waits on synchronisation primitives, by method name and the
/// entity that declares the method (`WaitOne` lives on WaitHandle, so
/// every event, mutex and semaphore resolves there).
let private primitiveWaits =
    Map
        [ "Wait",
          set
              [ "System.Threading.ManualResetEventSlim"
                "System.Threading.SemaphoreSlim"
                "System.Threading.CountdownEvent"
                "System.Threading.Monitor" ]
          "WaitOne", set [ "System.Threading.WaitHandle" ]
          "SignalAndWait", set [ "System.Threading.Barrier" ]
          "Join", set [ "System.Threading.Thread" ] ]

[<return: Struct>]
let private (|BoolAnd|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_BooleanAnd"; argExpr = l); argExpr = r) ->
        ValueSome(l, r)
    | _ -> ValueNone

[<return: Struct>]
let private (|BoolOr|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_BooleanOr"; argExpr = l); argExpr = r) ->
        ValueSome(l, r)
    | _ -> ValueNone

/// The value a binding body ends in.
[<TailCall>]
let rec private terminalOf (e: SynExpr) =
    match e with
    | LetOrUseE lou -> terminalOf lou.Body
    | SynExpr.Sequential(expr2 = b) -> terminalOf b
    | SynExpr.Typed(expr = inner)
    | SynExpr.Paren(expr = inner) -> terminalOf inner
    | t -> t

/// A binding that defines a function or member, as opposed to a value.
let private isFunctionBinding (SynBinding(headPat = pat)) =
    match pat with
    | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))
    | SynPat.LongIdent(argPats = SynArgPats.NamePatPairs _) -> true
    | _ -> false

/// Find blocking calls inside async/task CEs. Requires typed check results.
/// `taskAvailable`: FSharp.Core 6 or newer on a non-Fable target, where a
/// `task { }` can be written; without it a ContinueWith reading its
/// antecedent's `.Result` is not reported at all — there ContinueWith IS
/// the bind (very old F# has no task builder).
let findWith
    (taskAvailable: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let isScript =
            parseTree.FileName.EndsWith(".fsx", System.StringComparison.OrdinalIgnoreCase)

        // every async/task CE body, for innermost-attribution
        let ces =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                    ceBuilders.Contains builder
                    ->
                    Some(builder, body.Range)
                | _ -> None)

        let innermostCe (r: range) =
            ces
            |> Array.filter (fun (_, ceRange) -> Range.rangeContainsRange ceRange r)
            |> Array.sortBy (fun (_, ceRange) -> ceRange.EndLine - ceRange.StartLine, ceRange.EndColumn)
            |> Array.tryHead

        let lambdaRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.Lambda _
                | SynExpr.MatchLambda _ -> Some e.Range
                | _ -> None)

        let insideLambdaWithin (ceRange: range) (r: range) =
            lambdaRanges
            |> Array.exists (fun l -> Range.rangeContainsRange ceRange l && Range.rangeContainsRange l r)

        // every CE body of ANY builder (seq { }, query { }, custom ones) and
        // every comprehension. A `do!` fix landing in statement position of
        // one of those nested inside the async/task would call a Bind the
        // builder does not have — a compile error, not a fix.
        let otherCeRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.ComputationExpr(expr = body) -> Some body.Range
                | SynExpr.ArrayOrListComputed(expr = body) -> Some body.Range
                | _ -> None)

        let insideOtherCeWithin (ceRange: range) (r: range) =
            otherCeRanges
            |> Array.exists (fun other ->
                Range.rangeContainsRange ceRange other
                && not (Range.equals other ceRange)
                && Range.rangeContainsRange other r)

        // `let!`/`do!` cannot appear inside a finally block or an exception
        // handler — no bind-shaped fix may land in one
        let noBindRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.TryFinally(finallyExpr = f) -> [| f.Range |]
                | SynExpr.TryWith(withCases = cases) ->
                    cases
                    |> List.map (fun (SynMatchClause(resultExpr = result)) -> result.Range)
                    |> Array.ofList
                | _ -> [||])

        let inNoBindZone (r: range) =
            noBindRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

        let finallyRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.TryFinally(finallyExpr = f) -> Some f.Range
                | _ -> None)

        let inFinally (r: range) =
            finallyRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

        // the receiver a site drains: `t` of `t.Result`, `t.Wait()` and
        // `t.GetAwaiter().GetResult()`, in either parse shape
        let siteReceiverRange (kind: BlockKind) (e: SynExpr) : range voption =
            match kind, e with
            | BlockKind.AwaiterGetResult, SynExpr.App(funcExpr = SynExpr.DotGet(expr = AwaiterReceiverRange recvRange)) ->
                ValueSome recvRange
            | BlockKind.TaskResult, SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                ValueSome(prefixRangeOf e ids)
            | BlockKind.TaskResult, SynExpr.DotGet(expr = recv) -> ValueSome recv.Range
            | BlockKind.TaskWait, SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                ids.Length >= 2 && (List.last ids).idText = "Wait"
                ->
                ValueSome(prefixRangeOf e ids)
            | BlockKind.TaskWait,
              SynExpr.App(funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ w ]))) when
                w.idText = "Wait"
                ->
                ValueSome recv.Range
            | _ -> ValueNone

        // the receivers a condition proves complete — in its then branch,
        // and in its else branch: `vt.IsCompletedSuccessfully`, conjoined
        // with anything, or negated
        let rec completionTests (cond: SynExpr) : string list * string list =
            match stripParens cond with
            | BoolAnd(l, r) ->
                let tl, _ = completionTests l
                let tr, _ = completionTests r
                tl @ tr, []
            | BoolOr(l, r) ->
                let _, el = completionTests l
                let _, er = completionTests r
                [], el @ er
            | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = inner) ->
                let t, e = completionTests inner
                e, t
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) as e when
                ids.Length >= 2 && completionTestNames.Contains (List.last ids).idText
                ->
                [ textOfRange source (prefixRangeOf e ids) ], []
            | SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ p ])) when
                completionTestNames.Contains p.idText
                ->
                [ textOfRange source recv.Range ], []
            | _ -> [], []

        let underCompletionTest (path: SyntaxNode list) (recvText: string) (r: range) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenExpr; elseExpr = elseExpr)) ->
                    let thenTests, elseTests = completionTests cond

                    (Range.rangeContainsRange thenExpr.Range r && List.contains recvText thenTests)
                    || (elseExpr |> Option.exists (fun e -> Range.rangeContainsRange e.Range r)
                        && List.contains recvText elseTests)
                | _ -> false)

        // a task complete from birth: `Task.FromResult x`, `Task.CompletedTask`,
        // `ValueTask.FromResult x` and their exception/cancellation siblings
        // — a test fixture's stand-in, drained without a wait
        let completedByConstruction (e: SynExpr) =
            let factory (ids: Ident list) =
                ids.Length >= 2
                && (let m = List.last ids

                    (m.idText = "FromResult"
                     || m.idText = "FromException"
                     || m.idText = "FromCanceled"
                     || m.idText = "CompletedTask")
                    && (enclosingEntityOf check source m) |> taskFamily)

            match stripParens e with
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
                factory ids
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))) -> factory ids
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> factory ids
            | _ -> false

        // `let t = Task.FromResult 1` in scope of the site — a local let
        // whose body holds it, or a module-level value
        let boundToCompleted (recvText: string) (r: range) =
            let namedCompleted (b: SynBinding) =
                match b with
                | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = rhs) ->
                    id.idText = recvText && completedByConstruction rhs
                | _ -> false

            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | LetOrUseE lou when not lou.IsBang ->
                    Range.rangeContainsRange lou.Range r
                    && lou.Bindings |> List.exists namedCompleted
                | _ -> false)
            || index.Decls
               |> Array.exists (fun (_, d) ->
                   match d with
                   | SynModuleDecl.Let(bindings = bindings) -> bindings |> List.exists namedCompleted
                   | _ -> false)

        // the parameter each `.ContinueWith(...)` continuation receives — a
        // lambda's, or a named function's — and the range it is in scope:
        // the antecedent is complete by definition when the continuation
        // runs, so draining it never waits
        let antecedentScopes: (string list * range) list =
            let namedFunction (name: string) =
                let ofBindings (bindings: SynBinding list) =
                    bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(
                            headPat = SynPat.LongIdent(
                                longDotId = SynLongIdent(id = [ f ]); argPats = SynArgPats.Pats [ p ])) when
                            f.idText = name
                            ->
                            Some(patNames p, b.RangeOfBindingWithRhs)
                        | _ -> None)

                [ for _, e in index.Exprs do
                      match e with
                      | LetOrUseE lou when not lou.IsBang -> yield! ofBindings lou.Bindings
                      | _ -> ()
                  for _, d in index.Decls do
                      match d with
                      | SynModuleDecl.Let(bindings = bindings) -> yield! ofBindings bindings
                      | _ -> () ]

            [ for _, e in index.Exprs do
                  match e with
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent cw; argExpr = arg) when
                      cw.idText = "ContinueWith" && (enclosingEntityOf check source cw) |> taskFamily
                      ->
                      let continuation =
                          match stripParens arg with
                          | SynExpr.Tuple(exprs = first :: _) -> stripParens first
                          | a -> a

                      match continuation with
                      | SynExpr.Lambda(parsedData = Some(pats, _)) as l ->
                          yield (pats |> List.collect patNames, l.Range)
                      | SynExpr.Ident f -> yield! namedFunction f.idText
                      | _ -> ()
                  | _ -> () ]

        let isAntecedent (recvText: string) (r: range) =
            antecedentScopes
            |> List.exists (fun (names, scope) -> List.contains recvText names && Range.rangeContainsRange scope r)

        // the console's blocking point: a wait on the spine of an
        // `[<EntryPoint>]` main, of a command runner that ends in an exit
        // code, or at the top level of a script — the one place synchronous
        // code has to meet the asynchronous world, and no `task { }` can
        // wrap it. Anything behind a lambda or a nested function is a
        // boundary of its own
        let consoleBlockingPoint (path: SyntaxNode list) =
            let rec walk (nodes: SyntaxNode list) =
                match nodes with
                | [] -> isScript
                | SyntaxNode.SynExpr(SynExpr.Lambda _ | SynExpr.MatchLambda _ | SynExpr.ObjExpr _ | SynExpr.ComputationExpr _) :: _ ->
                    false
                | SyntaxNode.SynBinding(SynBinding(valData = SynValData(memberFlags = Some _))) :: _ -> false
                | SyntaxNode.SynBinding(SynBinding(attributes = attrs; expr = body) as b) :: rest ->
                    if hasAttributeNamed "EntryPoint" attrs then
                        true
                    elif isFunctionBinding b then
                        match terminalOf body with
                        | SynExpr.Const(SynConst.Int32 _, _) -> true
                        | _ -> false
                    else
                        walk rest
                | SyntaxNode.SynMemberDefn _ :: _
                | SyntaxNode.SynTypeDefn _ :: _ -> false
                | _ :: rest -> walk rest

            walk path

        // a wait in a function choreographed around a thread (a signal,
        // a Thread, Interlocked): "wrap it in task { }" is the advice
        // FR0142 refuses for the same body, and the note must not give
        // it either — Mibo's thread-affine tests earned 40 boundary notes
        // the moment FR0142 correctly left them alone
        let threadBoundScope (path: SyntaxNode list) =
            path
            |> List.rev
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynBinding(SynBinding(expr = body)) -> Some body
                | _ -> None)
            |> Option.exists (BlockingSites.threadBound source)

        // `Task.WaitAll(tasks, timeout)` / `(tasks, token)`: the final
        // argument is proven not a task, so the pair is not params-style
        let isTaskLike (t: FSharpType) =
            BlockingSites.isTaskType t
            || (try
                    t.HasTypeDefinition
                    && t.TypeDefinition.IsArrayType
                    && BlockingSites.isTaskType t.GenericArguments.[0]
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false)

        let provablyNotTask (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const _ -> true
            | e ->
                BlockingSites.receiverIdent e
                |> Option.bind (BlockingSites.valueTypeOf check source)
                |> Option.exists (fun t -> not (isTaskLike t))

        [ for path, expr in index.Exprs do
              let blocking =
                  match expr with
                  // t.Result — a bare property path or a dot-get
                  | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                      ids.Length >= 2 && (List.last ids).idText = "Result"
                      ->
                      let id = List.last ids

                      if (enclosingEntityOf check source id) |> taskFamily then
                          Some(BlockKind.TaskResult, None, Some id)
                      else
                          None
                  | SynExpr.DotGet(longDotId = SynLongIdent(id = [ id ])) when
                      id.idText = "Result" && (enclosingEntityOf check source id) |> taskFamily
                      ->
                      Some(BlockKind.TaskResult, None, Some id)
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent id) when
                      (id.idText = "Wait" || id.idText = "WaitAll" || id.idText = "WaitAny")
                      && (enclosingEntityOf check source id) |> taskFamily
                      ->
                      Some(BlockKind.TaskWait, None, Some id)
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent id; argExpr = UnitConst) when
                      id.idText = "GetResult"
                      && (enclosingEntityOf check source id).Contains "Awaiter"
                      ->
                      Some(BlockKind.AwaiterGetResult, None, Some id)
                  // a synchronisation primitive's wait: `signal.Wait()`,
                  // `handle.WaitOne()`, `barrier.SignalAndWait()`,
                  // `thread.Join()`, `Monitor.Wait o` — the declaring
                  // entity names it for the message
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent id & funcExpr) when
                      primitiveWaits.ContainsKey id.idText
                      ->
                      let entity = enclosingEntityOf check source id

                      if primitiveWaits.[id.idText].Contains entity then
                          // the receiver's own type where it resolves
                          // (`ManualResetEvent`, not the `WaitHandle` that
                          // declares WaitOne); the declaring entity for a
                          // static `Monitor.Wait`
                          let receiverType =
                              (match funcExpr with
                               | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                   Some ids.[ids.Length - 2]
                               | SynExpr.DotGet(expr = recv) -> BlockingSites.receiverIdent recv
                               | _ -> None)
                              |> Option.bind (BlockingSites.valueTypeOf check source)
                              |> Option.bind (fun t ->
                                  try
                                      if t.HasTypeDefinition then
                                          Some t.TypeDefinition.DisplayName
                                      else
                                          None
                                  with _ -> // fsharpanalyzer: ignore-line FR0055
                                      None)

                          let shortName =
                              receiverType
                              |> Option.defaultValue (entity.Substring(entity.LastIndexOf '.' + 1))

                          Some(BlockKind.PrimitiveWait $"{shortName}.{id.idText}()", None, Some id)
                      else
                          None
                  | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                      pathEndsWith "Async" "RunSynchronously" ids
                      && (fullNameOf check source (List.last ids)).StartsWith "Microsoft.FSharp.Control"
                      ->
                      Some(BlockKind.RunSynchronously, None, Some(List.last ids))
                  | SynExpr.App(
                      isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                      pathEndsWith "Thread" "Sleep" ids
                      && (enclosingEntityOf check source (List.last ids)) = "System.Threading.Thread"
                      ->
                      Some(BlockKind.ThreadSleep, Some arg, None)
                  | _ -> None

              // outside any CE two shapes are the documented synchronous idiom,
              // not a deadlock: `t.Wait(timeout)` is a bounded wait, and a
              // `.Result` read after `proc.WaitForExit()` in the same body
              // drains a task that already completed (the Process stdout
              // pattern; prismatic's scripts, forty times over)
              let boundedWait =
                  match expr with
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent id; argExpr = arg) when id.idText = "Wait" ->
                      (match arg with
                       | UnitConst -> false
                       | _ -> true)
                  | SynExpr.App(isInfix = false; funcExpr = CallIdent id; argExpr = arg) when
                      id.idText = "WaitAll" || id.idText = "WaitAny"
                      ->
                      (match stripParens arg with
                       | SynExpr.Tuple(exprs = es) when es.Length >= 2 -> provablyNotTask (List.last es)
                       | _ -> false)
                  | _ -> false

              let bindingRange =
                  path
                  |> List.tryPick (fun node ->
                      match node with
                      | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                      | _ -> None)

              let earlierInBody (e: SynExpr) =
                  match bindingRange with
                  | Some r -> Range.rangeContainsRange r e.Range && e.Range.StartLine < expr.Range.StartLine
                  | None -> false

              let afterWaitForExit () =
                  index.Exprs
                  |> Array.exists (fun (_, e) ->
                      match e with
                      | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                          not ids.IsEmpty && (List.last ids).idText = "WaitForExit"
                          ->
                          earlierInBody e
                      | _ -> false)

              // `t.Wait(timeout)` above, then `t.Result`: the wait already
              // happened — the read drains, and the earlier line carries
              // whatever note the wait itself deserves
              let afterOwnWait (recvText: string) =
                  index.Exprs
                  |> Array.exists (fun (_, e) ->
                      match e with
                      | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                          ids.Length >= 2 && (List.last ids).idText = "Wait"
                          ->
                          earlierInBody e && textOfRange source (prefixRangeOf e ids) = recvText
                      | SynExpr.App(
                          isInfix = false; funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ w ]))) when
                          w.idText = "Wait"
                          ->
                          earlierInBody e && textOfRange source recv.Range = recvText
                      | _ -> false)

              match blocking with
              | Some(kind, sleepArg, blockIdent) ->
                  let receiverRange = siteReceiverRange kind expr

                  // the task behind the site is complete before it is
                  // drained: under its own completion probe, complete from
                  // birth, the antecedent of a continuation, or already
                  // waited for above
                  let knownComplete =
                      match receiverRange with
                      | ValueSome r ->
                          let recvText = textOfRange source r

                          underCompletionTest path recvText expr.Range
                          || completedByConstruction (
                              match expr with
                              | SynExpr.DotGet(expr = recv) -> recv
                              | SynExpr.App(funcExpr = SynExpr.DotGet(expr = AwaiterReceiver recv)) -> recv
                              | _ -> expr
                          )
                          || boundToCompleted recvText expr.Range
                          || isAntecedent recvText expr.Range
                          || (kind <> BlockKind.TaskWait && afterOwnWait recvText)
                      | ValueNone -> false

                  let idiomatic =
                      (kind = BlockKind.TaskWait && boundedWait)
                      || (kind = BlockKind.TaskResult && afterWaitForExit ())
                      || knownComplete

                  let boundaryKind =
                      match kind with
                      | BlockKind.ThreadSleep
                      | BlockKind.RunSynchronously
                      | BlockKind.PrimitiveWait _ -> false
                      | _ -> true

                  // `.Result` on the antecedent inside its own continuation:
                  // complete, so nothing blocks, but a fault arrives wrapped
                  // in AggregateException. The continuation IS a bind: the
                  // same `task { let! }` FR0049 writes everywhere else gets
                  // the value, the exception itself, and no ContinueWith
                  let antecedentRead =
                      match kind, receiverRange with
                      | BlockKind.TaskResult, ValueSome r -> isAntecedent (textOfRange source r) expr.Range
                      | _ -> false

                  match innermostCe expr.Range with
                  // without a task builder (FSharp.Core before 6, Fable)
                  // ContinueWith IS the bind, and the read stays quiet
                  | _ when antecedentRead && taskAvailable ->
                      let antecedentName =
                          match receiverRange with
                          | ValueSome r -> textOfRange source r
                          | ValueNone -> ""

                      // the plain shape only: `t.ContinueWith(fun a -> body)`
                      // — one lambda, no scheduler or options, a single-line
                      // body whose every use of the antecedent is `a.Result`
                      // (a body that tests IsFaulted or Status handles the
                      // antecedent itself), the call closing its line, and a
                      // continuation returning a value (a `Task` from an
                      // Action continuation has no `task { return }` twin)
                      let continueWithFix =
                          index.Exprs
                          |> Array.tryPick (fun (_, e) ->
                              match e with
                              | SynExpr.App(isInfix = false; funcExpr = (CallIdent cw as callee); argExpr = arg) when
                                  cw.idText = "ContinueWith"
                                  && Range.rangeContainsRange e.Range expr.Range
                                  && isSingleLine e.Range
                                  ->
                                  let recv =
                                      match callee with
                                      | SynExpr.DotGet(expr = recv) -> Some(textOfRange source recv.Range)
                                      | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                          Some(textOfRange source (prefixRangeOf callee ids))
                                      | _ -> None

                                  let returnsValue =
                                      (fullNameOf check source cw).Length > 0
                                      && (match
                                              check.GetSymbolUseAtLocation(
                                                  cw.idRange.EndLine,
                                                  cw.idRange.EndColumn,
                                                  source.GetLineString(cw.idRange.EndLine - 1),
                                                  [ cw.idText ]
                                              )
                                          with
                                          | Some su ->
                                              match su.Symbol with
                                              | :? FSharpMemberOrFunctionOrValue as m ->
                                                  (try
                                                      let t = m.ReturnParameter.Type.StripAbbreviations()
                                                      t.HasTypeDefinition && t.GenericArguments.Count = 1
                                                   with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                                       false)
                                              | _ -> false
                                          | None -> false)

                                  let lineText = source.GetLineString(e.Range.StartLine - 1)
                                  let closesLine = lineText.Substring(e.Range.EndColumn).Trim() = ""

                                  let lineIndent =
                                      lineText.Substring(0, lineText.Length - lineText.TrimStart().Length)

                                  match stripParens arg, recv with
                                  | SynExpr.Lambda(parsedData = Some([ p ], body)), Some recvText when
                                      returnsValue && closesLine && isSingleLine body.Range
                                      ->
                                      let bodyText = textOfRange source body.Range

                                      let mentions = Regex.Matches(bodyText, identifierPattern antecedentName).Count

                                      let reads =
                                          Regex
                                              .Matches(bodyText, identifierPattern antecedentName + @"\.Result\b")
                                              .Count

                                      // a name the body does not already use;
                                      // no candidate free, no rewrite
                                      let binder =
                                          if
                                              patNames p = [ antecedentName ]
                                              && mentions > 0
                                              && mentions = reads
                                              && not (spansDirective source e.Range)
                                          then
                                              [ "r"; "result"; antecedentName + "Value" ]
                                              |> List.tryFind (fun b ->
                                                  not (Regex.IsMatch(bodyText, identifierPattern b)))
                                          else
                                              None

                                      match binder with
                                      | Some binder ->
                                          let bound =
                                              Regex.Replace(
                                                  bodyText,
                                                  identifierPattern antecedentName + @"\.Result\b",
                                                  binder
                                              )

                                          let inner = lineIndent + "    "

                                          Some(
                                              e.Range,
                                              textOfRange source e.Range,
                                              $"task {{\n{inner}let! {binder} = {recvText}\n{inner}return {bound}\n{lineIndent}}}"
                                          )
                                      | None -> None
                                  | _ -> None
                              | _ -> None)

                      { Range = expr.Range
                        Kind = BlockKind.AntecedentResult
                        Builder = None
                        Fixes = Option.toList continueWithFix
                        AlternativeFixes = []
                        Receiver = ValueNone
                        InLambda = false
                        InFinally = false }
                  | None when
                      boundaryKind
                      && not idiomatic
                      && not (consoleBlockingPoint path)
                      && not (threadBoundScope path)
                      ->
                      // sync-over-async at a boundary: an antipattern even
                      // outside CEs — either the caller becomes async (wrap
                      // in task { } and bind) or the synchronous API should
                      // be used. Thread.Sleep in sync code is legitimate,
                      // and Async.RunSynchronously outside a CE IS F#'s
                      // intended sync-boundary runner.
                      let alternatives =
                          match kind, expr with
                          | BlockKind.AwaiterGetResult,
                            SynExpr.App(funcExpr = SynExpr.DotGet(expr = AwaiterReceiver recv)) ->
                              syncSiblingFix check source recv expr
                          | _ -> []

                      let receiver =
                          match kind, expr with
                          | BlockKind.AwaiterGetResult,
                            SynExpr.App(funcExpr = SynExpr.DotGet(expr = AwaiterReceiverRange recvRange)) ->
                              ValueSome recvRange
                          | BlockKind.TaskResult, SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                              ids.Length >= 2
                              ->
                              ValueSome(prefixRangeOf expr ids)
                          | BlockKind.TaskResult, SynExpr.DotGet(expr = recv) -> ValueSome recv.Range
                          | _ -> ValueNone

                      { Range = expr.Range
                        Kind = kind
                        Builder = None
                        Fixes = []
                        AlternativeFixes = alternatives
                        Receiver = receiver
                        InLambda = false
                        InFinally = false }
                  | Some(builder, ceRange) when not knownComplete ->
                      let taskBuilder = builder = "task" || builder = "backgroundTask"

                      // the plain `let` whose entire RHS is `target`
                      // — found structurally, not via the walker's
                      // path conventions
                      let bindingKeywordFor (target: range) =
                          index.Exprs
                          |> Array.tryPick (fun (_, e) ->
                              match e with
                              | LetOrUseE lou when not (lou.IsBang || lou.IsUse || lou.IsRecursive) ->
                                  match lou.Bindings with
                                  // simple named pattern, no type
                                  // annotation: `let! x : T = ..` is
                                  // not a shape to gamble on
                                  | [ SynBinding(
                                          isMutable = false
                                          returnInfo = None
                                          headPat = SynPat.Named _
                                          expr = rhs
                                          trivia = btrivia) ] when Range.equals rhs.Range target ->
                                      Some btrivia.LeadingKeyword.Range
                                  | _ -> None
                              | _ -> None)

                      let bindingRewrite (target: range) (bound: string) =
                          match bindingKeywordFor target with
                          | Some kw when textOfRange source kw = "let" ->
                              [ kw, "let", "let!"; target, textOfRange source target, bound ]
                          | _ -> []

                      // statement position: a sequential element, the CE
                      // body itself, a let-continuation, or `do ...`
                      let statementTarget =
                          match path with
                          | SyntaxNode.SynExpr(SynExpr.Do _ as doExpr) :: _ -> Some doExpr.Range
                          | SyntaxNode.SynExpr(SynExpr.Sequential _) :: _
                          | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: _
                          | SyntaxNode.SynExpr(SynExpr.LetOrUse _) :: _ -> Some expr.Range
                          | _ -> None

                      // a statement with a successor can end in a `let! _ =`;
                      // the last one cannot, a block does not end on a bind
                      let notLast =
                          let afterDo =
                              match path with
                              | SyntaxNode.SynExpr(SynExpr.Do _) :: rest -> rest
                              | p -> p

                          match afterDo with
                          | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = first)) :: _ ->
                              Range.rangeContainsRange first.Range expr.Range
                          | _ -> false

                      let insideFixableSpine =
                          not (insideLambdaWithin ceRange expr.Range)
                          && not (insideOtherCeWithin ceRange expr.Range)
                          && not (inNoBindZone expr.Range)

                      // the awaitable behind a blocking site, as the
                      // builder's own bind operand: a Task binds directly in
                      // task { }, behind Async.AwaitTask in async { }
                      let bindOperand (text: string) =
                          if taskBuilder then
                              Some text
                          elif builder = "async" then
                              Some $"Async.AwaitTask {asArgument text}"
                          else
                              None

                      // The one fix offered INSIDE a lambda, because it deletes
                      // the lambda: `Task.Run(fun () -> c |> Async.RunSynchronously)`
                      // is `c |> Async.StartAsTask` written the long way, minus
                      // the parked pool thread. The `|> ignore` spelling returns
                      // a non-generic Task and `do!` will not take a `Task<'T>`,
                      // so that one keeps its shape through an upcast.
                      // Held apart from `fixes` because it survives the
                      // thread-bound veto below: it rewrites neither the bind
                      // nor where the bind resumes, only what it waits on.
                      let taskRunFixes =
                          if
                              kind = BlockKind.RunSynchronously
                              && taskBuilder
                              && insideLambdaWithin ceRange expr.Range
                              && not (insideOtherCeWithin ceRange expr.Range)
                          then
                              index.Exprs
                              |> Array.tryPick (fun (_, e) ->
                                  if Range.rangeContainsRange e.Range expr.Range then
                                      match taskRunOfRunSync check source e with
                                      | ValueSome(comp, ignored) -> Some(e.Range, comp, ignored)
                                      | ValueNone -> None
                                  else
                                      None)
                              |> Option.map (fun (runRange, comp, ignored) ->
                                  let started = $"{textOfRange source comp.Range} |> Async.StartAsTask"

                                  let replacement =
                                      if ignored then
                                          $"({started}) :> System.Threading.Tasks.Task"
                                      else
                                          started

                                  [ runRange, textOfRange source runRange, replacement ])
                              |> Option.defaultValue []
                          else
                              []

                      let fixes =
                          match kind, sleepArg with
                          | BlockKind.RunSynchronously, _ when not (List.isEmpty taskRunFixes) -> taskRunFixes
                          | BlockKind.ThreadSleep, Some arg when
                              not (insideLambdaWithin ceRange expr.Range)
                              && not (insideOtherCeWithin ceRange expr.Range)
                              && not (inNoBindZone expr.Range)
                              ->
                              let target = statementTarget

                              let waiter =
                                  if builder = "async" then
                                      "Async.Sleep"
                                  else
                                      "System.Threading.Tasks.Task.Delay"

                              target
                              |> Option.map (fun r ->
                                  r, textOfRange source r, $"do! {waiter} {argumentText source (stripParens arg)}")
                              |> Option.toList
                          | (BlockKind.AwaiterGetResult | BlockKind.TaskResult | BlockKind.RunSynchronously), _ when
                              not (insideLambdaWithin ceRange expr.Range)
                              && not (insideOtherCeWithin ceRange expr.Range)
                              && not (inNoBindZone expr.Range)
                              ->
                              // `let x = <blocking>` as a direct CE statement
                              // becomes `let! x = <computation>` — the
                              // builder's own bind releases the thread. The
                              // adapter matrix is asymmetric: task { } binds
                              // both Tasks and Asyncs with a plain let!,
                              // async { } binds Asyncs natively but needs
                              // Async.AwaitTask for a Task — and ValueTask
                              // has no AwaitTask overload at all, so those
                              // stay advice in async
                              // a TASK receiver: direct in task { }, behind
                              // Async.AwaitTask in async { } (real Task only)
                              let bindTaskReceiver (recvRange: range) =
                                  let text = textOfRange source recvRange

                                  if taskBuilder then
                                      Some text
                                  elif builder = "async" then
                                      let entity =
                                          blockIdent
                                          |> Option.map (enclosingEntityOf check source)
                                          |> Option.defaultValue ""

                                      if
                                          entity.StartsWith "System.Threading.Tasks.Task"
                                          || entity.StartsWith "System.Runtime.CompilerServices.TaskAwaiter"
                                      then
                                          Some $"Async.AwaitTask {asArgument text}"
                                      else
                                          None
                                  else
                                      None

                              match kind, expr with
                              | BlockKind.AwaiterGetResult,
                                SynExpr.App(funcExpr = SynExpr.DotGet(expr = AwaiterReceiverRange recvRange)) ->
                                  bindTaskReceiver recvRange
                                  |> Option.map (bindingRewrite expr.Range)
                                  |> Option.defaultValue []
                              | BlockKind.TaskResult, SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                  ids.Length >= 2
                                  ->
                                  bindTaskReceiver (prefixRangeOf expr ids)
                                  |> Option.map (bindingRewrite expr.Range)
                                  |> Option.defaultValue []
                              | BlockKind.TaskResult, SynExpr.DotGet(expr = recv) ->
                                  bindTaskReceiver recv.Range
                                  |> Option.map (bindingRewrite expr.Range)
                                  |> Option.defaultValue []
                              | BlockKind.RunSynchronously, _ ->
                                  // the flagged node is the ident; the
                                  // binding RHS is the surrounding
                                  // application — an Async binds natively in
                                  // BOTH builders
                                  index.Exprs
                                  |> Array.tryPick (fun (_, e) ->
                                      match e with
                                      | RunSyncApplication comp when Range.rangeContainsRange e.Range expr.Range ->
                                          Some(e.Range, comp)
                                      | _ -> None)
                                  |> Option.map (fun (rhsRange, comp) ->
                                      bindingRewrite rhsRange (textOfRange source comp.Range))
                                  |> Option.defaultValue []
                              | _ -> []
                          // `t.Wait()` / `Task.WaitAll(...)` as a statement:
                          // `do! t` / `do! Task.WhenAll(...)` — a `let! _ =`
                          // when the joined tasks carry values and a
                          // statement follows
                          | BlockKind.TaskWait, _ when insideFixableSpine ->
                              match statementTarget, BlockingSites.blockingOf check source expr with
                              | Some target, Some b when not b.NoBind ->
                                  match bindOperand b.DoText, bindOperand b.Awaitable with
                                  | Some operand, _ when b.UnitResult ->
                                      [ target, textOfRange source target, $"do! {operand}" ]
                                  | _, Some operand when notLast ->
                                      [ target, textOfRange source target, $"let! _ = {operand}" ]
                                  | _ -> []
                              | _ -> []
                          // a blocking call inside the delegate of
                          // `Assert.Throws<E>(fun () -> ...)`: the assert has
                          // an async spelling, and the `let ex =` it feeds
                          // becomes a `let!` (xUnit, MSTest) or stays (NUnit)
                          | _ when
                              insideLambdaWithin ceRange expr.Range
                              && not (insideOtherCeWithin ceRange expr.Range)
                              && not (inNoBindZone expr.Range)
                              ->
                              path
                              |> List.tryPick (fun node ->
                                  match node with
                                  | SyntaxNode.SynExpr(SynExpr.App _ as app) when
                                      Range.rangeContainsRange ceRange app.Range
                                      && not (insideLambdaWithin ceRange app.Range)
                                      && not (insideOtherCeWithin ceRange app.Range)
                                      ->
                                      BlockingSites.assertThrows check source app |> Option.map (fun b -> app, b)
                                  | _ -> None)
                              |> Option.map (fun (app, b) ->
                                  if b.NoBind then
                                      [ app.Range, textOfRange source app.Range, b.Awaitable ]
                                  else
                                      match bindOperand b.Awaitable with
                                      | Some bound ->
                                          match bindingRewrite app.Range bound with
                                          | [] ->
                                              // `Assert.Throws<E>(...) |> ignore` with a
                                              // successor: `let! _ = ...`
                                              index.Exprs
                                              |> Array.tryPick (fun (ipath, e) ->
                                                  match e, ipath with
                                                  | BlockingSites.Ignored inner,
                                                    SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = first)) :: _ when
                                                      Range.equals inner.Range app.Range
                                                      && Range.rangeContainsRange first.Range e.Range
                                                      ->
                                                      Some
                                                          [ e.Range, textOfRange source e.Range, $"let! _ = {bound}" ]
                                                  | _ -> None)
                                              |> Option.defaultValue []
                                          | edits -> edits
                                      | None -> [])
                              |> Option.defaultValue []
                          | _ -> []

                      { Range = expr.Range
                        Kind = kind
                        Builder = Some builder
                        // inside a thread-choreographed body a bind moves the
                        // continuation off the thread the wait was keeping
                        // it on: the site is still noted, the fix withheld
                        Fixes = (if threadBoundScope path then taskRunFixes else fixes)
                        AlternativeFixes = []
                        Receiver = ValueNone
                        InLambda = insideLambdaWithin ceRange expr.Range
                        InFinally = inFinally expr.Range }
                  | _ -> ()
              | None -> () ]

/// The modern-target form of `findWith`: tests and the taskify fix, which
/// only runs where a `task { }` can be written anyway.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    findWith true parseTree source check
