/// Blocking sites and the awaitable each one hides — shared by FR0049
/// (a blocking call inside a computation) and FR0142 (a test that blocks):
/// the same `t.Wait()` becomes the same `do! t` whether the enclosing
/// code is a task { } body or a test method about to become one.
///
///     comp |> Async.RunSynchronously      comp |> Async.StartImmediateAsTask
///     Async.RunSynchronously comp         comp |> Async.StartImmediateAsTask
///     t.Result / t.GetAwaiter().GetResult()   t
///     t.Wait()                            t   (a Task<T> upcast for `do!`)
///     Task.WaitAll(a, b) / (tasks)        Task.WhenAll(a, b) / (tasks)
///     Task.WaitAny(...)                   Task.WhenAny(...)
///     Assert.Throws<E>(fun () -> <blocking>)
///                                         Assert.ThrowsAsync<E>(fun () -> <awaitable> :> Task)
///
/// Every receiver is proven by the typed tree: FSharp.Core's
/// RunSynchronously, a Task/ValueTask-typed receiver, Task's own WaitAll,
/// the Assert of xUnit, NUnit or MSTest. `Task.WaitAll(tasks, timeout)` and
/// `Task.WaitAll(tasks, token)` carry a contract WhenAll has no spelling
/// for and stay as written.
module FSharp.Refactor.BlockingSites

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

let symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    try
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ])
        |> Option.map (fun u -> u.Symbol)
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

/// The value, function or member an identifier resolves to, if any.
let valueAt (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match symbolAt check source ident with
    | Some(:? FSharpMemberOrFunctionOrValue as v) -> Some v
    | _ -> None

/// The full name of the entity declaring what an identifier names.
let declaringEntityName (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    valueAt check source ident
    |> Option.bind (fun v ->
        try
            v.DeclaringEntity |> Option.bind (fun e -> e.TryFullName)
        with _ -> // fsharpanalyzer: ignore-line FR0055
            None)

/// FSharp.Core's `Async.<name>`, not a same-named member of some other
/// `Async` type in scope.
let isCoreAsyncMember (name: string) (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match valueAt check source ident with
    | Some v ->
        (try
            v.DisplayName = name
            && (v.DeclaringEntity
                |> Option.bind (fun e -> e.TryFullName)
                |> Option.exists (fun n -> n = "Microsoft.FSharp.Control.FSharpAsync"))
         with _ -> // fsharpanalyzer: ignore-line FR0055
             false)
    | None -> false

let private taskTypeNames =
    [ "System.Threading.Tasks.Task"; "System.Threading.Tasks.ValueTask" ]

let isTaskType (t: FSharpType) =
    try
        t.HasTypeDefinition
        && (t.TypeDefinition.TryFullName
            |> Option.exists (fun n -> taskTypeNames |> List.exists (fun tn -> n = tn || n.StartsWith(tn + "`"))))
    with _ -> // fsharpanalyzer: ignore-line FR0055
        false

/// The identifier that decides a receiver's type: `t` in `t`, `x.T` in
/// `x.T`, `M` in `M()` / `x.M(a)`.
[<TailCall>]
let rec receiverIdent (e: SynExpr) =
    match e with
    | SynExpr.Ident pid -> Some pid
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
    | SynExpr.App(funcExpr = f) -> receiverIdent f
    | SynExpr.TypeApp(expr = inner)
    | SynExpr.Paren(expr = inner) -> receiverIdent inner
    | _ -> None

let rec isUnitType (t: FSharpType) =
    try
        if t.IsAbbreviation then
            isUnitType t.AbbreviatedType
        else
            t.HasTypeDefinition
            && (t.TypeDefinition.TryFullName
                |> Option.exists (fun n -> n = "Microsoft.FSharp.Core.Unit" || n = "Microsoft.FSharp.Core.unit"))
    with _ -> // fsharpanalyzer: ignore-line FR0055
        false

/// The type of the value an identifier names — for a function or member,
/// what it returns.
let valueTypeOf (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    match valueAt check source id with
    | Some v ->
        (try
            Some(
                if v.IsMember || v.IsFunction then
                    v.ReturnParameter.Type
                else
                    v.FullType
            )
         with _ -> // fsharpanalyzer: ignore-line FR0055
             None)
    | None -> None

/// Is the value this identifier names typed as a Task or ValueTask — or,
/// for a function or member, does it return one? Yields the number of
/// type arguments: 0 for a plain `Task`, 1 for `Task<T>`.
let taskArity check source id =
    valueTypeOf check source id
    |> Option.bind (fun t -> if isTaskType t then Some t.GenericArguments.Count else None)

let isTaskTyped check source id = (taskArity check source id).IsSome

/// Is the value this identifier names a `ValueTask`/`ValueTask<T>` (or
/// does the function or member return one)? A struct unrelated to Task:
/// `vt :> Task` does not compile, `vt.AsTask()` is the spelling.
let isValueTaskTyped check source id =
    valueTypeOf check source id
    |> Option.exists (fun t ->
        try
            t.HasTypeDefinition
            && (t.TypeDefinition.TryFullName
                |> Option.exists (fun n -> n.StartsWith "System.Threading.Tasks.ValueTask"))
        with _ -> // fsharpanalyzer: ignore-line FR0055
            false)

/// A plain `Task` or a `Task<unit>` — something `do!` binds as it is.
let taskResultIsUnit check source id =
    match valueTypeOf check source id with
    | Some t when isTaskType t -> t.GenericArguments.Count = 0 || isUnitType t.GenericArguments.[0]
    | _ -> false

/// Is this computation provably an `Async<unit>`? Only what the typed tree
/// can name: a value, a call. An `async { }` literal is not, and gets the
/// `Async.Ignore` a `do!` needs regardless.
let computationResultIsUnit check source (comp: SynExpr) =
    receiverIdent comp
    |> Option.bind (valueTypeOf check source)
    |> Option.exists (fun t ->
        try
            t.HasTypeDefinition
            && t.TypeDefinition.TryFullName = Some "Microsoft.FSharp.Control.FSharpAsync`1"
            && isUnitType t.GenericArguments.[0]
        with _ -> // fsharpanalyzer: ignore-line FR0055
            false)

/// `recv.M` in either parse shape: an expression receiver — `(f ()).M`,
/// a DotGet — or a dotted name — `t.M`, `x.t.M`, one LongIdent. Yields the
/// receiver's text, the identifier that decides its type, and the member.
let dotMember (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ])) ->
        receiverIdent recv
        |> Option.map (fun rid -> textOfRange source recv.Range, rid, m)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
        let m = List.last ids
        let prefix = ids |> List.take (ids.Length - 1)

        let receiverRange =
            Range.unionRanges (List.head prefix).idRange (List.last prefix).idRange

        Some(textOfRange source receiverRange, List.last prefix, m)
    | _ -> None

/// `recv.M()` — a member call with a unit argument, in either shape.
[<return: Struct>]
let (|UnitCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = SynExpr.Const(SynConst.Unit, _)) -> ValueSome f
    | _ -> ValueNone

/// A blocking expression and the awaitable to bind instead.
type Blocking =
    {
        /// The whole blocking expression.
        Site: range
        /// Text of the awaitable: `load () |> Async.StartImmediateAsTask`, or the task itself.
        Awaitable: string
        /// The awaitable as a `do!` operand: the same text, except a
        /// `Task<T>` that was only waited on is upcast to a plain `Task`,
        /// since `do!` needs a unit result.
        DoText: string
        /// True when the result is unit by construction (`.Wait()`).
        UnitResult: bool
        /// False for `.Wait()`: the site yields no value, so `let x =
        /// t.Wait()` has no `let!` form — binding `t` would retype `x`.
        BindsValue: bool
        /// True when the awaitable is provably a non-generic `Task`, so it
        /// needs no upcast where a `Func<Task>` is expected.
        PlainTask: bool
        /// True when the awaitable is not awaitable at all: NUnit's
        /// `Assert.ThrowsAsync` returns the exception itself, so the
        /// rewrite is a plain replacement, never a bind.
        NoBind: bool
        /// True when the site surfaces a fault WRAPPED: `.Wait()`,
        /// `.Result` and `Task.WaitAll` throw an AggregateException
        /// holding the failure(s), where a bind on the awaitable throws
        /// the first inner exception itself. Code that asserts or
        /// catches the wrapper cannot keep doing so after the rewrite.
        WrapsFaults: bool
        /// True when the awaitable is a `ValueTask`/`ValueTask<T>` — a
        /// struct unrelated to `Task`, with no upcast to it: where a
        /// `Task` is expected the spelling is `.AsTask()`.
        ValueTask: bool
    }

[<return: Struct>]
let (|AsyncModule|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when m.idText = "Async" -> ValueSome f
    | _ -> ValueNone

let private blocking site awaitable =
    {
        Site = site
        Awaitable = awaitable
        DoText = awaitable
        UnitResult = false
        BindsValue = true
        PlainTask = false
        NoBind = false
        WrapsFaults = false
        ValueTask = false
    }

/// `<blocking> |> ignore` — the result was thrown away.
[<return: Struct>]
let (|Ignored|_|) (e: SynExpr) =
    match stripParens e with
    | PipeApp(inner, SynExpr.Ident pid) when pid.idText = "ignore" -> ValueSome inner
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident pid; argExpr = inner) when pid.idText = "ignore" ->
        ValueSome inner
    | _ -> ValueNone

/// The text of `whole` with each (range, replacement) spliced in; the
/// ranges lie inside `whole` and do not overlap.
let private splice (source: ISourceText) (whole: range) (edits: (range * string) list) =
    let parts = System.Text.StringBuilder()
    let mutable at = whole.Start

    for r, replacement in edits |> List.sortBy (fun (r, _) -> r.StartLine, r.StartColumn) do
        parts.Append(textOfRange source (Range.mkRange whole.FileName at r.Start)).Append replacement
        |> ignore

        at <- r.End

    parts.Append(textOfRange source (Range.mkRange whole.FileName at whole.End)).ToString()

/// The blocking (`WaitAll`/`WaitAny`) and awaiting (`WhenAll`/`WhenAny`)
/// spellings of Task's static waits.
let private taskWaits = Map [ "WaitAll", "WhenAll"; "WaitAny", "WhenAny" ]

/// The elements of a `WaitAll` argument, params-style or one array.
let private waitElements (arg: SynExpr) =
    match stripParens arg with
    | SynExpr.Tuple(exprs = es) -> es
    | e -> [ e ]

/// The arity of the task(s) an element carries — 0 for `Task`, 1 for
/// `Task<T>` — when the typed tree can say; an array-typed value counts
/// by its element type.
let private elementTaskArity check source (e: SynExpr) =
    match receiverIdent (stripParens e) |> Option.bind (valueTypeOf check source) with
    | Some t when isTaskType t -> Some t.GenericArguments.Count
    | Some t when
        (try
            t.HasTypeDefinition
            && t.TypeDefinition.IsArrayType
            && isTaskType t.GenericArguments.[0]
         with _ -> // fsharpanalyzer: ignore-line FR0055
             false)
        ->
        Some t.GenericArguments.[0].GenericArguments.Count
    | _ -> None

let private bAggregateExRegex = Regex @"\bAggregateException\b"

/// `Assert.Throws<E>(fun () -> <blocking>)` and its siblings: the async
/// spelling with the lambda returning the awaitable as a `Task`.
/// xUnit's and MSTest's async asserts return a `Task<E>` to bind; NUnit's
/// returns the exception outright, so its rewrite never binds.
let rec assertThrows (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) : Blocking option =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = arg) ->
        match receiverIdent f with
        | Some m when m.idText = "Throws" || m.idText = "ThrowsAny" || m.idText = "ThrowsException" ->
            let framework =
                match declaringEntityName check source m with
                | Some "Xunit.Assert"
                | Some "Microsoft.VisualStudio.TestTools.UnitTesting.Assert" -> Some false
                | Some "NUnit.Framework.Assert" -> Some true
                | _ -> None

            let lambda =
                match stripParens arg with
                | SynExpr.Lambda _ as l -> Some l
                | SynExpr.Tuple(exprs = es) when not es.IsEmpty ->
                    match stripParens (List.last es) with
                    | SynExpr.Lambda _ as l -> Some l
                    | _ -> None
                | _ -> None

            match framework, lambda with
            | Some noBind, Some(SynExpr.Lambda(parsedData = Some(_, lambdaBody)) as lambda) ->
                let inner =
                    match lambdaBody with
                    | Ignored i -> i
                    | b -> b

                // the assert's head — everything before the lambda: the
                // type argument `<AggregateException>` or the
                // `typeof<AggregateException>` of the non-generic overload
                let assertsAggregate =
                    bAggregateExRegex.IsMatch(
                        textOfRange source (Range.mkRange e.Range.FileName e.Range.Start lambda.Range.Start)
                    )

                match blockingOf check source inner with
                // `Assert.Throws<AggregateException>(fun () -> t.Wait())`
                // asserts the WRAPPER `.Wait()` throws; the awaited delegate
                // throws the inner exception and the assertion fails at
                // runtime — that assert stays as written
                | Some b when not (b.NoBind || b.WrapsFaults && assertsAggregate) ->
                    let asTask =
                        // a ValueTask has no upcast to Task: `.AsTask()`,
                        // then the upcast for the generic one
                        if b.ValueTask then
                            if b.PlainTask then
                                $"{b.Awaitable}.AsTask()"
                            else
                                $"{b.Awaitable}.AsTask() :> System.Threading.Tasks.Task"
                        elif b.PlainTask then
                            b.Awaitable
                        else
                            $"{b.Awaitable} :> System.Threading.Tasks.Task"

                    let head =
                        textOfRange
                            source
                            (Range.mkRange lambda.Range.FileName lambda.Range.Start lambdaBody.Range.Start)

                    let text =
                        splice source e.Range [ m.idRange, m.idText + "Async"; lambda.Range, head + asTask ]

                    Some
                        { blocking e.Range text with
                            NoBind = noBind
                        }
                | _ -> None
            | _ -> None
        | _ -> None
    | _ -> None

and blockingOf (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) : Blocking option =
    match stripParens e with
    // `comp |> Async.RunSynchronously`
    | PipeApp(comp, (AsyncModule f as rhs)) when
        f.idText = "RunSynchronously"
        && isCoreAsyncMember "RunSynchronously" check source f
        ->
        match stripParens comp with
        // `task { ... } |> Async.AwaitTask |> Async.RunSynchronously`: the
        // task was awaitable all along — both pipes go
        | PipeApp(inner, AsyncModule aw) when aw.idText = "AwaitTask" && isCoreAsyncMember "AwaitTask" check source aw ->
            let arity = receiverIdent inner |> Option.bind (taskArity check source)

            Some
                { blocking e.Range (textOfRange source inner.Range) with
                    UnitResult = receiverIdent inner |> Option.exists (taskResultIsUnit check source)
                    PlainTask = arity = Some 0
                }
        | _ ->
            // everything up to the operand — the pipe and its line break,
            // if the pipe opened a new line — stays as written
            let upToOperand =
                textOfRange source (Range.mkRange comp.Range.FileName comp.Range.Start rhs.Range.Start)

            Some
                { blocking e.Range $"{upToOperand}Async.StartImmediateAsTask" with
                    UnitResult = computationResultIsUnit check source comp
                }
    // `Async.RunSynchronously comp` / `Async.RunSynchronously(comp)` — a
    // timeout or cancellation argument is a different contract, left alone
    | SynExpr.App(isInfix = false; funcExpr = AsyncModule f; argExpr = arg) when
        f.idText = "RunSynchronously"
        && isCoreAsyncMember "RunSynchronously" check source f
        ->
        match stripParens arg with
        | SynExpr.Tuple _ -> None
        | comp ->
            Some
                { blocking e.Range $"{atomicText source comp} |> Async.StartImmediateAsTask" with
                    UnitResult = computationResultIsUnit check source comp
                }
    // `t.Wait()` — unit by construction — and `t.GetAwaiter().GetResult()`
    | UnitCall f ->
        match dotMember source f with
        | Some(recvText, rid, m) when m.idText = "Wait" ->
            match taskArity check source rid with
            | Some arity ->
                Some
                    { blocking e.Range recvText with
                        DoText =
                            if arity = 0 then
                                recvText
                            else
                                $"({recvText} :> System.Threading.Tasks.Task)"
                        UnitResult = true
                        BindsValue = false
                        PlainTask = arity = 0
                        WrapsFaults = true
                    }
            | None -> None
        | Some(_, _, gr) when gr.idText = "GetResult" ->
            match f with
            | SynExpr.DotGet(expr = UnitCall inner) ->
                match dotMember source inner with
                | Some(recvText, rid, ga) when ga.idText = "GetAwaiter" ->
                    match taskArity check source rid with
                    // a plain Task's GetResult() is unit: a `do!` site
                    | Some arity ->
                        Some
                            { blocking e.Range recvText with
                                UnitResult = taskResultIsUnit check source rid
                                PlainTask = arity = 0
                                ValueTask = isValueTaskTyped check source rid
                            }
                    | None -> None
                | _ -> None
            | _ -> None
        | _ -> None
    // `Task.WaitAll(a, b)` / `Task.WaitAll tasks` → `Task.WhenAll(...)`:
    // params-style arguments must each prove to be a task, or the pair
    // could be the (tasks, timeout) overload
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = arg) as app when
        (match receiverIdent f with
         | Some m -> taskWaits.ContainsKey m.idText
         | None -> false)
        ->
        let m = (receiverIdent f).Value

        if declaringEntityName check source m <> Some "System.Threading.Tasks.Task" then
            None
        else
            let elements = waitElements arg
            let arities = elements |> List.map (elementTaskArity check source)

            let paramsProven = elements.Length = 1 || arities |> List.forall Option.isSome

            if not paramsProven then
                None
            else
                let text = splice source app.Range [ m.idRange, taskWaits.[m.idText] ]
                let allPlain = arities |> List.forall (fun a -> a = Some 0)

                if m.idText = "WaitAll" then
                    // WaitAll throws ONE AggregateException carrying every
                    // failure; awaiting WhenAll throws the first alone
                    Some
                        { blocking e.Range text with
                            UnitResult = allPlain
                            PlainTask = allPlain
                            BindsValue = false
                            WrapsFaults = true
                        }
                else
                    // WhenAny yields the finished task, WaitAny its index:
                    // a bound value would change type, so only a discarded
                    // call moves
                    Some
                        { blocking e.Range text with
                            BindsValue = false
                        }
    // `t.Result`
    | other ->
        match dotMember source other with
        | Some(recvText, rid, p) when p.idText = "Result" && isTaskTyped check source rid ->
            Some
                { blocking e.Range recvText with
                    UnitResult = taskResultIsUnit check source rid
                    WrapsFaults = true
                    ValueTask = isValueTaskTyped check source rid
                }
        | _ -> assertThrows check source other

let private bThreadRegex = Regex @"\bThread\."
let private bThreadsRegex = Regex @"\bThread\s*\("

/// Is this body choreographed around a THREAD? Code that hands work to a
/// thread and waits on a signal continues on the same thread after the
/// wait; `do!` resumes wherever the scheduler posts, so "make it async"
/// is the wrong advice there, in a test (FR0142: tests of thread-affine
/// code fail or turn flaky when converted) and at a boundary alike (FR0049). Read off the text: the
/// names are unmistakable and a false "bound" only costs a note.
let threadBound (source: ISourceText) (body: SynExpr) =
    // `Thread.Sleep` is a pause, not choreography — and the site FR0049's
    // `do! Async.Sleep` fix exists for
    let text = (textOfRange source body.Range).Replace("Thread.Sleep", "")

    [
        "Monitor."
        "Mutex"
        "ReaderWriterLock"
        "ThreadStatic"
        "ThreadLocal"
        "WaitOne"
        "ManualResetEvent"
        "CountdownEvent"
        "Barrier"
        "SemaphoreSlim"
        "CurrentManagedThreadId"
        "SynchronizationContext"
        "Interlocked."
    ]
    |> List.exists text.Contains
    // The two Thread spellings need a word boundary, which a substring test
    // cannot give them: plain "Thread(" also reads ThrowIfNotOnUIThread(),
    // SwitchToMainThread( and every other name ENDING in Thread - the VS
    // threading helpers are called that, and a match would withhold a
    // whole file's fixes. `\bThread` matches the type and nothing built on
    // its name (ThreadHelper, ThreadPool, ThreadStatic keep their own
    // entries above where they belong).
    || bThreadsRegex.IsMatch text
    || bThreadRegex.IsMatch text

let private configuredBindRegex = Regex(@"\.ConfigureAwait\s*\(\s*false\s*\)\s*$")

/// Should a bind that FR0049 or FR0119 inserts into this CE body carry
/// `.ConfigureAwait(false)`? Where the body's own binds (`let!`, `use!`,
/// `do!`, `return!`, `match!`, `while!`, not those of a lambda or CE inside it) all
/// await that way and there is at least one: a bare bind among them would
/// resume on the context the rest refuse. Only `task { }`: `async { }`
/// bridges with `Async.AwaitTask`, `backgroundTask { }` has no context to
/// capture. Never in a test file.
let configureAwaitWanted (index: AstIndex.Index) (source: ISourceText) (builder: string) (ceBody: range) =
    builder = "task"
    && not (AstIndex.isTestFile index source)
    && (let nested =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.Lambda _
                | SynExpr.MatchLambda _ -> Some e.Range
                | SynExpr.ComputationExpr(expr = body) when not (Range.equals body.Range ceBody) -> Some body.Range
                | _ -> None)
            |> Array.filter (fun r -> Range.rangeContainsRange ceBody r && not (Range.equals r ceBody))

        let own (r: range) =
            Range.rangeContainsRange ceBody r
            && not (nested |> Array.exists (fun n -> Range.rangeContainsRange n r))

        let awaited =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | LetOrUseE lou when lou.IsBang ->
                    lou.Bindings |> List.map (fun (SynBinding(expr = rhs)) -> rhs) |> Array.ofList
                | SynExpr.DoBang(expr = x)
                | SynExpr.YieldOrReturnFrom(expr = x)
                | SynExpr.MatchBang(expr = x)
                | SynExpr.WhileBang(whileExpr = x) -> [| x |]
                | _ -> [||])
            |> Array.filter (fun x -> own x.Range)

        awaited.Length > 0
        && awaited
           |> Array.forall (fun x -> configuredBindRegex.IsMatch(textOfRange source x.Range)))

let private simpleReceiverRegex = Regex(@"^[A-Za-z_][\w.]*(\([^()]*\))?$")

let private anyConfiguredRegex = Regex(@"\.ConfigureAwait\s*\([^()]*\)\s*$")

/// `text.ConfigureAwait(false)`, the text parenthesised unless it is a name,
/// a dotted path or one call on one (`reader.ReadLineAsync()`). A text that
/// ends in a `ConfigureAwait` call already stays as it is.
let configured (text: string) =
    let t = text.Trim()

    if anyConfiguredRegex.IsMatch t then
        t
    elif simpleReceiverRegex.IsMatch t then
        t + ".ConfigureAwait(false)"
    else
        $"({t}).ConfigureAwait(false)"

let private dualFlagNames =
    set [ "async"; "isasync"; "useasync"; "runasync"; "doasync"; "asynchronous" ]

let private bindKeywordRegex =
    Regex(@"(\blet!|\bdo!|\breturn!|\bmatch!|\buse!|\byield!|Async\.AwaitTask)")

/// The site is one branch of a dual sync/async body: an `if` whose other
/// branch binds what `awaited` accepts on a line of its own (`let!`, `do!`,
/// `return!`, `match!`, `use!`, `Async.AwaitTask`: FR0119 passes the twin's
/// name, FR0049 the drained task), or whose condition is a flag named for the
/// choice (`async`, `isAsync`, `useAsync`, `runAsync`):
/// `if isAsync then do! x.FlushAsync() else x.Flush()`. The synchronous
/// branch is the point: binding there runs async work under the synchronous
/// API. An unrelated bind in the other branch is not this.
let dualPathBranch (source: ISourceText) (path: SyntaxNode list) (site: range) (awaited: string -> bool) =
    let rec flagCondition (c: SynExpr) =
        match c with
        | SynExpr.Paren(expr = e) -> flagCondition e
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident n; argExpr = e) when n.idText = "not" -> flagCondition e
        | SynExpr.Ident pid -> dualFlagNames.Contains(pid.idText.TrimStart('_').ToLowerInvariant())
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
            dualFlagNames.Contains((List.last ids).idText.TrimStart('_').ToLowerInvariant())
        | _ -> false

    let bindsHere (branch: SynExpr) =
        (textOfRange source branch.Range).Split '\n'
        |> Array.exists (fun line -> bindKeywordRegex.IsMatch line && awaited line)

    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenE; elseExpr = elseE)) ->
            let inThen = Range.rangeContainsRange thenE.Range site

            let inElse = elseE |> Option.exists (fun e -> Range.rangeContainsRange e.Range site)

            (inThen || inElse)
            && (flagCondition cond
                || (inThen && elseE |> Option.exists bindsHere)
                || (inElse && bindsHere thenE))
        | _ -> false)

let private syncCommentRegex =
    let word = @"(sync|synchronous|synchronously)"

    let decision =
        @"(on purpose|by design|deliberately|intentionally|purposely|is intended|is fine)"

    Regex($@"^\s*(//+|\(\*+)\s*{word}\b|\b{word}\s+{decision}\b|\b{decision}\s+{word}\b", RegexOptions.IgnoreCase)

// the author wants it changed
let private syncRequestRegex =
    Regex(
        @"\b(todo|fixme|hack|xxx|fix\s+(me|this|it|later)|for now|temporar(y|ily)|(should|must|needs?\s+to|has\s+to)\s+be\s+(made\s+)?(async|asynchronous|awaited)|make\s+(this\s+|it\s+)?(async|asynchronous))\b",
        RegexOptions.IgnoreCase
    )

/// A comment on the site's line or the line above it that says the call is
/// synchronous on purpose: one opening with the word (`// Sync, it's already
/// buffered`) or pairing it with a decision (`sync on purpose`, `by design`).
/// `// keep in sync with X` is not one, nor is a comment that asks for the
/// change (`// sync over async here, fix later`, a `TODO`, `should be async`).
let syncByComment (source: ISourceText) (site: range) =
    let comment (line: string) =
        let i = line.IndexOf "//"

        if i >= 0 then
            Some(line.Substring i)
        elif line.TrimStart().StartsWith "(*" then
            Some(line.TrimStart())
        else
            None

    let lineAt (n: int) =
        if n >= 1 && n <= source.GetLineCount() then
            source.GetLineString(n - 1)
        else
            ""

    let own = comment (lineAt site.StartLine)

    let above =
        let l = lineAt (site.StartLine - 1)

        if l.TrimStart().StartsWith "//" || l.TrimStart().StartsWith "(*" then
            Some(l.TrimStart())
        else
            None

    [ own; above ]
    |> List.exists (fun c ->
        c
        |> Option.exists (fun text -> syncCommentRegex.IsMatch text && not (syncRequestRegex.IsMatch text)))

let private raisingFunctions =
    set
        [
            "failwith"
            "failwithf"
            "raise"
            "invalidOp"
            "invalidArg"
            "nullArg"
            "reraise"
        ]

/// The expression ends by raising: its last statement is `failwith …`,
/// `raise …`, `invalidOp …`, `invalidArg …`, `nullArg …` or `reraise ()`.
[<TailCall>]
let rec raisesAtEnd (e: SynExpr) =
    match e with
    | SynExpr.Sequential(expr2 = rest) -> raisesAtEnd rest
    | SynExpr.Paren(expr = inner) -> raisesAtEnd inner
    | LetOrUseE lou -> raisesAtEnd lou.Body
    | SynExpr.App(isInfix = false; funcExpr = f) ->
        let rec head (x: SynExpr) =
            match x with
            | SynExpr.App(isInfix = false; funcExpr = g) -> head g
            | SynExpr.Ident pid -> Some pid.idText
            | _ -> None

        head f |> Option.exists raisingFunctions.Contains
    | _ -> false

/// The site sits in a NON-final element of this statement chain. The walker
/// records only a chain's outermost `Sequential` (`a; b; c` arrives as one
/// node whose `expr2` holds the rest), so a test of the recorded node's
/// `expr1` alone sees the first statement and misses every later one.
let rec inChainBeforeEnd (chain: SynExpr) (site: range) =
    match chain with
    | SynExpr.Sequential(expr1 = first; expr2 = rest) ->
        Range.rangeContainsRange first.Range site || inChainBeforeEnd rest site
    | _ -> false

/// A statement of this chain with a successor: exactly one of its non-final
/// elements (the chain's last expression is its value, not a statement).
let rec isChainStatement (chain: SynExpr) (target: range) =
    match chain with
    | SynExpr.Sequential(expr1 = first; expr2 = rest) -> Range.equals first.Range target || isChainStatement rest target
    | _ -> false

/// The chain's final element: its value, not a statement.
[<TailCall>]
let rec isChainFinal (chain: SynExpr) (target: range) =
    match chain with
    | SynExpr.Sequential(expr2 = rest) -> isChainFinal rest target
    | last -> Range.equals last.Range target

/// What follows the statement at `target` in this chain: the rest of the
/// sequence after it, or None when it is not one of the chain's statements.
[<TailCall>]
let rec afterInChain (chain: SynExpr) (target: range) : SynExpr option =
    match chain with
    | SynExpr.Sequential(expr1 = first; expr2 = rest) ->
        if Range.equals first.Range target then
            Some rest
        else
            afterInChain rest target
    | _ -> None
