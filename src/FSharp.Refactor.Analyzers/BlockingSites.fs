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

        check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ])
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
    | SynExpr.Ident id -> Some id
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
    { Site = site
      Awaitable = awaitable
      DoText = awaitable
      UnitResult = false
      BindsValue = true
      PlainTask = false
      NoBind = false
      WrapsFaults = false
      ValueTask = false }

/// `<blocking> |> ignore` — the result was thrown away.
[<return: Struct>]
let (|Ignored|_|) (e: SynExpr) =
    match stripParens e with
    | PipeApp(inner, SynExpr.Ident id) when id.idText = "ignore" -> ValueSome inner
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id; argExpr = inner) when id.idText = "ignore" ->
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
                    Regex.IsMatch(
                        textOfRange source (Range.mkRange e.Range.FileName e.Range.Start lambda.Range.Start),
                        @"\bAggregateException\b"
                    )

                match blockingOf check source inner with
                // `Assert.Throws<AggregateException>(fun () -> t.Wait())`
                // asserts the WRAPPER `.Wait()` throws; the awaited delegate
                // throws the inner exception and the assertion fails at
                // runtime — that assert stays as written
                | Some b when not b.NoBind && not (b.WrapsFaults && assertsAggregate) ->
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
                            NoBind = noBind }
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
                    PlainTask = arity = Some 0 }
        | _ ->
            // everything up to the operand — the pipe and its line break,
            // if the pipe opened a new line — stays as written
            let upToOperand =
                textOfRange source (Range.mkRange comp.Range.FileName comp.Range.Start rhs.Range.Start)

            Some
                { blocking e.Range $"{upToOperand}Async.StartImmediateAsTask" with
                    UnitResult = computationResultIsUnit check source comp }
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
                    UnitResult = computationResultIsUnit check source comp }
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
                        WrapsFaults = true }
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
                                ValueTask = isValueTaskTyped check source rid }
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
                            WrapsFaults = true }
                else
                    // WhenAny yields the finished task, WaitAny its index:
                    // a bound value would change type, so only a discarded
                    // call moves
                    Some
                        { blocking e.Range text with
                            BindsValue = false }
    // `t.Result`
    | other ->
        match dotMember source other with
        | Some(recvText, rid, p) when p.idText = "Result" && isTaskTyped check source rid ->
            Some
                { blocking e.Range recvText with
                    UnitResult = taskResultIsUnit check source rid
                    WrapsFaults = true
                    ValueTask = isValueTaskTyped check source rid }
        | _ -> assertThrows check source other

/// Is this body choreographed around a THREAD? Code that hands work to a
/// thread and waits on a signal continues on the same thread after the
/// wait; `do!` resumes wherever the scheduler posts, so "make it async"
/// is the wrong advice there, in a test (FR0142: Mibo's thread-affine
/// adaptive graphs — four tests failed, eleven turned flaky when
/// converted) and at a boundary alike (FR0049). Read off the text: the
/// names are unmistakable and a false "bound" only costs a note.
let threadBound (source: ISourceText) (body: SynExpr) =
    // `Thread.Sleep` is a pause, not choreography — and the site FR0049's
    // `do! Async.Sleep` fix exists for
    let text = (textOfRange source body.Range).Replace("Thread.Sleep", "")

    [ "Monitor."
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
      "Interlocked." ]
    |> List.exists text.Contains
    // The two Thread spellings need a word boundary, which a substring test
    // cannot give them: plain "Thread(" also reads ThrowIfNotOnUIThread(),
    // SwitchToMainThread( and every other name ENDING in Thread â€” the VS
    // threading helpers are called that, and a whole file's fixes were
    // withheld over it. `\bThread` matches the type and nothing built on
    // its name (ThreadHelper, ThreadPool, ThreadStatic keep their own
    // entries above where they belong).
    || Regex.IsMatch(text, @"\bThread\s*\(")
    || Regex.IsMatch(text, @"\bThread\.")
