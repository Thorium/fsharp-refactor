/// Audit fixes for the async rules: FR0049 (SyncOverAsync), FR0142
/// (TestReturnsTask, through the shared BlockingSites.assertThrows) and
/// FR0079 (SingleAwaitable). Each finding gets its repro (no fix, or the
/// corrected fix) and a positive shape the fix was designed for.
module FSharp.Refactor.Tests.AuditAsyncTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private blockingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SyncOverAsync.find tree sourceText checkResults

let private testsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TestReturnsTask.find tree sourceText checkResults

/// No FR0142 suggestion — and the fixture typechecks, so the silence is
/// the rule's decision rather than a broken scaffold's.
let private assertNoTestRewrite (source: string) =
    Assert.True(typechecksCleanly source, $"Fixture does not typecheck:\n%s{source}")
    Assert.Empty(testsIn source)

let private singlesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SingleAwaitable.find tree sourceText checkResults

let private applyFixes (source: string) (fixes: (FSharp.Compiler.Text.range * string * string) list) =
    fixes
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

/// The one FR0049 site of a source and its fixes.
let private singleSite (source: string) =
    match blockingIn source with
    | [ s ] -> s
    | other -> failwithf "Expected exactly one blocking site, got %A" other

let private assertPatchedTypechecks (source: string) (fixes: (FSharp.Compiler.Text.range * string * string) list) =
    let patched = applyFixes source fixes
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    patched

/// An xUnit-shaped Assert declared in the fixture (the module is named
/// `Xunit` so the rules trust its Assert and its Fact).
[<Literal>]
let private xunitScaffold =
    "module Xunit\nopen System\nopen System.Threading.Tasks\ntype FactAttribute() =\n    inherit Attribute()\ntype Assert =\n    static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>\n    static member Throws(t: Type, f: Action) : exn = null\n    static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>\n    static member ThrowsAsync(t: Type, f: Func<Task>) : Task<exn> = Task.FromResult null\n"

// ---- A3: Assert.Throws<AggregateException> asserts the wrapper a bind unwraps ----

[<Fact>]
let ``A3 FR0142: an Assert.Throws over AggregateException around a Wait is not converted`` () =
    // `t.Wait()` throws the AggregateException the test asserts; the
    // awaited delegate of ThrowsAsync throws the inner exception and the
    // assertion would fail at runtime — every spelling of the type stays
    for head in
        [
            "Assert.Throws<AggregateException>"
            "Assert.Throws<System.AggregateException>"
            "Assert.Throws(typeof<AggregateException>, "
        ] do
        let call =
            if head.EndsWith ", " then
                head + "fun () -> t.Wait())"
            else
                head + "(fun () -> t.Wait())"

        let source =
            xunitScaffold
            + "let failing () : Task = Task.FromException(InvalidOperationException())\n[<Fact>]\nlet ``faults`` () =\n    let t = failing ()\n    let ex = "
            + call
            + "\n    ignore ex.InnerException"

        assertNoTestRewrite source

[<Fact>]
let ``A3 FR0142: the Result and WaitAll shapes under an AggregateException assert stay too`` () =
    let resultShape =
        xunitScaffold
        + fsharp
            """
            let failing () : Task<int> = Task.FromException<int>(InvalidOperationException())
            [<Fact>]
            let ``faults`` () =
                let t = failing ()
                let ex = Assert.Throws<AggregateException>(fun () -> t.Result |> ignore)
                ignore ex.InnerException
            """

    assertNoTestRewrite resultShape

    let waitAllShape =
        xunitScaffold
        + fsharp
            """
            let failing () : Task = Task.FromException(InvalidOperationException())
            [<Fact>]
            let ``faults`` () =
                let a = failing ()
                let b = failing ()
                let ex = Assert.Throws<AggregateException>(fun () -> Task.WaitAll(a, b))
                ignore ex.InnerExceptions.Count
            """

    assertNoTestRewrite waitAllShape

[<Fact>]
let ``A3 FR0142: a Wait asserted with the inner exception type still moves`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let failing () : Task = Task.FromException(InvalidOperationException())
            [<Fact>]
            let ``faults`` () =
                let t = failing ()
                let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                ignore ex.Message
            """

    match testsIn source with
    | [ s ] ->
        Assert.Contains("let! ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> t)", s.ReplacementText)

        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``A3 FR0049: an Assert.Throws over AggregateException inside a task keeps its Wait`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let f (t: Task<int>) = task {
                let ex = Assert.Throws<AggregateException>(fun () -> t.Wait())
                return ex.Message
            }
            """

    let s = singleSite source
    Assert.True s.InLambda
    Assert.Empty s.Fixes

    let qualified =
        xunitScaffold
        + fsharp
            """
            let f (t: Task<int>) = task {
                let ex = Assert.Throws<System.AggregateException>(fun () -> t.Result |> ignore)
                return ex.Message
            }
            """

    Assert.Empty (singleSite qualified).Fixes

[<Fact>]
let ``A3 FR0049: GetResult under an AggregateException assert already unwraps, so it still moves`` () =
    // GetAwaiter().GetResult() throws the inner exception exactly as the
    // awaited delegate will: whatever the assert meant, nothing changes
    let source =
        xunitScaffold
        + fsharp
            """
            let f (t: Task<int>) = task {
                let ex = Assert.Throws<AggregateException>(fun () -> t.GetAwaiter().GetResult() |> ignore)
                return ex.Message
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, _, replacement) ] ->
        Assert.Equal("Assert.ThrowsAsync<AggregateException>(fun () -> t :> System.Threading.Tasks.Task)", replacement)
        assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let!-bind pair, got %A" other

[<Fact>]
let ``A3 FR0049: a WaitAll in the try body of an AggregateException handler keeps its wait`` () =
    // WaitAll throws one AggregateException holding every failure; `do!
    // Task.WhenAll` throws the first alone and the handler goes dead
    let source =
        fsharp
            """
            open System
            open System.Threading.Tasks
            let f (a: Task) (b: Task) = task {
                try
                    Task.WaitAll(a, b)
                    return 0
                with :? AggregateException as ae ->
                    return ae.InnerExceptions.Count
            }
            """

    Assert.Empty (singleSite source).Fixes

[<Fact>]
let ``A3 FR0049: a Wait and a Result under an AggregateException handler keep their shape`` () =
    let wait =
        fsharp
            """
            open System
            open System.Threading.Tasks
            let f (t: Task) = task {
                try
                    t.Wait()
                    return 0
                with
                | :? AggregateException as ae -> return ae.InnerExceptions.Count
                | _ -> return -1
            }
            """

    Assert.Empty (singleSite wait).Fixes

    let result =
        fsharp
            """
            open System
            open System.Threading.Tasks
            let f (t: Task<int>) = task {
                try
                    let x = t.Result
                    return x
                with :? AggregateException as ae ->
                    return ae.InnerExceptions.Count
            }
            """

    Assert.Empty (singleSite result).Fixes

[<Fact>]
let ``A3 FR0049: a Wait under a handler for the inner exception type still becomes do-bang`` () =
    let source =
        fsharp
            """
            open System
            open System.Threading.Tasks
            let f (t: Task) = task {
                try
                    t.Wait()
                    return 0
                with :? InvalidOperationException ->
                    return 1
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "t.Wait()", "do! t") ] -> assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the do! fix, got %A" other

[<Fact>]
let ``A3 FR0049: GetResult under an AggregateException handler still binds`` () =
    // the awaiter already unwraps — the handler was dead before the fix
    let source =
        fsharp
            """
            open System
            open System.Threading.Tasks
            let f (t: Task<int>) = task {
                try
                    let x = t.GetAwaiter().GetResult()
                    return x
                with :? AggregateException ->
                    return -1
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, _, "t") ] -> assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let! fix, got %A" other

// ---- B5: let!/do! only on the CE's own statement spine ----

[<Fact>]
let ``B5 FR0049: a Result let nested in another binding's RHS is not a let-bang site`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                let pair =
                    let x = t.Result
                    x, x + 1
                return pair
            }
            """

    let s = singleSite source
    Assert.Equal(SyncOverAsync.BlockKind.TaskResult, s.Kind)
    Assert.Empty s.Fixes

[<Fact>]
let ``B5 FR0049: a Wait inside a local function is not a do-bang site`` () =
    let source =
        fsharp
            """
            let g (t: System.Threading.Tasks.Task) = task {
                let helper () =
                    t.Wait()
                    1
                return helper ()
            }
            """

    let s = singleSite source
    Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    Assert.Empty s.Fixes

[<Fact>]
let ``B5 FR0049: the other blocking shapes off the spine stay advice too`` () =
    // WaitAll, GetResult, RunSynchronously, Thread.Sleep, Assert.Throws —
    // each nested in a local function or another binding's RHS
    let shapes =
        [
            fsharp
                """
                open System.Threading.Tasks
                let f (a: Task) (b: Task) = task {
                    let helper () =
                        Task.WaitAll(a, b)
                        1
                    return helper ()
                }
                """
            fsharp
                """
                let f (t: System.Threading.Tasks.Task<int>) = task {
                    let v =
                        let x = t.GetAwaiter().GetResult()
                        x + 1
                    return v
                }
                """
            fsharp
                """
                let comp = async { return 1 }
                let f () = task {
                    let v =
                        let r = comp |> Async.RunSynchronously
                        r + 1
                    return v
                }
                """
            fsharp
                """
                let f () = task {
                    let helper () =
                        System.Threading.Thread.Sleep 10
                        1
                    return helper ()
                }
                """
            xunitScaffold
            + fsharp
                """
                let f (t: Task<int>) = task {
                    let helper () =
                        let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                        ex.Message
                    return helper ()
                }
                """
        ]

    for source in shapes do
        let s = singleSite source
        Assert.True(List.isEmpty s.Fixes, $"Expected no fix for:\n%s{source}\ngot %A{s.Fixes}")

[<Fact>]
let ``B5 FR0049: a Wait inside an object expression member is not a do-bang site`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task) = task {
                let d =
                    { new System.IDisposable with
                        member _.Dispose() =
                            t.Wait()
                            () }
                d.Dispose()
                return 1
            }
            """

    let s = singleSite source
    Assert.Empty s.Fixes

[<Fact>]
let ``B5 FR0049: a Result let on the spine still becomes let-bang`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                let x = t.Result
                return x + 1
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, "t.Result", "t") ] -> assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let! fix, got %A" other

[<Fact>]
let ``B5 FR0049: a match arm and a non-final if branch are spine positions`` () =
    // control flow on the spine keeps its statement positions: a bind is as
    // legal in an arm or a branch as at the top of the block
    let arm =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) (c: bool) = task {
                match c with
                | true ->
                    let x = t.Result
                    return x
                | false -> return 0
            }
            """

    let s = singleSite arm

    match s.Fixes with
    | [ (_, "let", "let!"); (_, "t.Result", "t") ] -> assertPatchedTypechecks arm s.Fixes |> ignore
    | other -> failwithf "Expected the let! fix in the arm, got %A" other

    let branch =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task) (c: bool) = task {
                let mutable n = 0
                if c then
                    t.Wait()
                    n <- 1
                return n
            }
            """

    let s = singleSite branch

    match s.Fixes with
    | [ (_, "t.Wait()", "do! t") ] -> assertPatchedTypechecks branch s.Fixes |> ignore
    | other -> failwithf "Expected the do! fix in the branch, got %A" other

// ---- B6: a ValueTask receiver has no upcast to Task ----

[<Fact>]
let ``B6 FR0049: an Assert.Throws over a generic ValueTask receiver spells AsTask`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let f (vt: ValueTask<int>) = task {
                let ex = Assert.Throws<InvalidOperationException>(fun () -> vt.Result |> ignore)
                return ex.Message
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, _, replacement) ] ->
        Assert.Equal(
            "Assert.ThrowsAsync<InvalidOperationException>(fun () -> vt.AsTask() :> System.Threading.Tasks.Task)",
            replacement
        )

        assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let!-bind pair, got %A" other

[<Fact>]
let ``B6 FR0049: a non-generic ValueTask receiver needs AsTask and no upcast`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let f (vt: ValueTask) = task {
                let ex = Assert.Throws<InvalidOperationException>(fun () -> vt.GetAwaiter().GetResult())
                return ex.Message
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, _, replacement) ] ->
        Assert.Equal("Assert.ThrowsAsync<InvalidOperationException>(fun () -> vt.AsTask())", replacement)
        assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let!-bind pair, got %A" other

[<Fact>]
let ``B6 FR0142: the ValueTask receiver spells AsTask in a test too`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let fetch () = ValueTask<int>(2)
            [<Fact>]
            let ``throws`` () =
                let vt = fetch ()
                let ex = Assert.Throws<InvalidOperationException>(fun () -> vt.Result |> ignore)
                ignore ex.Message
            """

    match testsIn source with
    | [ s ] ->
        Assert.Contains(
            "let! ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> vt.AsTask() :> System.Threading.Tasks.Task)",
            s.ReplacementText
        )

        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``B6 FR0049: a real Task receiver keeps the plain upcast`` () =
    let source =
        xunitScaffold
        + fsharp
            """
            let f (t: Task<int>) = task {
                let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Result |> ignore)
                return ex.Message
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, "let", "let!"); (_, _, replacement) ] ->
        Assert.Equal(
            "Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)",
            replacement
        )

        assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the let!-bind pair, got %A" other

// ---- B7: the Task.Run rewrite is an infix pipe — parenthesised under a tighter parent ----

[<Fact>]
let ``B7 FR0049: a Task.Run that is a ConfigureAwait receiver gets parentheses`` () =
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let! x = System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously).ConfigureAwait(false)
                return x
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, _, "(comp |> Async.StartAsTask)") ] ->
        let patched = assertPatchedTypechecks source s.Fixes
        Assert.Contains("let! x = (comp |> Async.StartAsTask).ConfigureAwait(false)", patched)
    | other -> failwithf "Expected the parenthesised StartAsTask fix, got %A" other

[<Fact>]
let ``B7 FR0049: the ignored Task.Run under a DotGet wraps the upcast as well`` () =
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                do! System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously |> ignore).ConfigureAwait(false)
                return 1
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, _, "((comp |> Async.StartAsTask) :> System.Threading.Tasks.Task)") ] ->
        assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the doubly wrapped fix, got %A" other

[<Fact>]
let ``B7 FR0049: a Task.Run inside a caller's own parentheses stays bare`` () =
    // (an unparenthesised `describe Task.Run(...)` is FS0597 and never
    // reaches the rule; the parenthesised argument is the shape that does)
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let describe (t: System.Threading.Tasks.Task<int>) = t.Id
            let f () = task {
                let id = describe (System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously))
                return id
            }
            """

    let s = singleSite source

    match s.Fixes with
    | [ (_, _, "comp |> Async.StartAsTask") ] -> assertPatchedTypechecks source s.Fixes |> ignore
    | other -> failwithf "Expected the bare fix inside the parentheses, got %A" other

[<Fact>]
let ``B7 FR0049: a bare let-bang and a pipe source stay unwrapped`` () =
    let plain =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let! x = System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously)
                return x
            }
            """

    let s = singleSite plain

    match s.Fixes with
    | [ (_, _, "comp |> Async.StartAsTask") ] -> assertPatchedTypechecks plain s.Fixes |> ignore
    | other -> failwithf "Expected the bare StartAsTask fix, got %A" other

    let piped =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let! x = System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously) |> id
                return x
            }
            """

    let s = singleSite piped

    match s.Fixes with
    | [ (_, _, "comp |> Async.StartAsTask") ] -> assertPatchedTypechecks piped s.Fixes |> ignore
    | other -> failwithf "Expected the bare StartAsTask fix as a pipe source, got %A" other

// ---- C5: FR0079's WaitAll unwrap must keep the wait ----

[<Fact>]
let ``C5 FR0079: WaitAll over one task becomes a Wait on it, not the bare task`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let run (t: Task) =
                Task.WaitAll [| t |]
                1
            """

    match singlesIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, original, replacement) ->
            Assert.Equal("Task.WaitAll [| t |]", original)
            Assert.Equal("t.Wait()", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the Wait offer"
    | other -> failwithf "Expected one single-awaitable finding, got %A" other

[<Fact>]
let ``C5 FR0079: a non-identifier element is parenthesised before the Wait`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let make () : Task = Task.CompletedTask
            let run () =
                Task.WaitAll [| make () |]
                1
            """

    match singlesIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.Equal("(make ()).Wait()", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the Wait offer"
    | other -> failwithf "Expected one single-awaitable finding, got %A" other

[<Fact>]
let ``C5 FR0079: WhenAll and Async.Parallel keep the unwrap to the element`` () =
    match
        singlesIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let run (t: Task<int>) = Task.WhenAll [| t |]
                """
        )
    with
    | [ s ] ->
        match s.Fix with
        | Some(_, _, replacement) -> Assert.Equal("t", replacement)
        | None -> failwith "Expected the unwrap offer"
    | other -> failwithf "Expected one single-awaitable finding, got %A" other

    match
        singlesIn (
            fsharp
                """
                module Test
                let run (comp: Async<int>) = Async.Parallel [ comp ]
                """
        )
    with
    | [ s ] ->
        match s.Fix with
        | Some(_, _, replacement) -> Assert.Equal("comp", replacement)
        | None -> failwith "Expected the unwrap offer"
    | other -> failwithf "Expected one single-awaitable finding, got %A" other
