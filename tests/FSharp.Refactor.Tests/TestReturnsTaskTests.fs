module FSharp.Refactor.Tests.TestReturnsTaskTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0142 TestReturnsTask ----

/// A test attribute declared in the fixture itself, so no framework
/// package is needed to typecheck it. The module is named `Xunit` so the
/// attributes resolve under a namespace the rule trusts to await a Task.
[<Literal>]
let private scaffold =
    "module Xunit\nopen System\nopen System.Threading.Tasks\ntype FactAttribute() =\n    inherit Attribute()\ntype TestAttribute() =\n    inherit Attribute()\ntype R = { X: int }\nlet load () = async { return { X = 1 } }\nlet work () = async { return () }\nlet fetch () = Task.FromResult { X = 2 }\nlet run () : Task = Task.CompletedTask\n"

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TestReturnsTask.find tree sourceText checkResults

let private assertRewrite (source: string) (expectedBody: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedBody, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``RunSynchronously in a test becomes a task-returning test`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``reads`` () =\n    let res = load () |> Async.RunSynchronously\n    if res.X <> 1 then failwith \"wrong\"")
        "task {\n        let! res = load () |> Async.StartImmediateAsTask\n        if res.X <> 1 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``Result on a task becomes a bind`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``fetches`` () =\n    let res = (fetch ()).Result\n    if res.X <> 2 then failwith \"wrong\"")
        "task {\n        let! res = (fetch ())\n        if res.X <> 2 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a final Wait becomes do-bang`` () =
    assertRewrite
        (scaffold + "[<Fact>]\nlet ``runs`` () =\n    let t = run ()\n    t.Wait()")
        "task {\n        let t = run ()\n        do! t\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a discarded blocking call becomes let-bang underscore`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``discards`` () =\n    load () |> Async.RunSynchronously |> ignore\n    ()")
        "task {\n        let! _ = load () |> Async.StartImmediateAsTask\n        ()\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a test without a blocking site is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``plain`` () =\n    let r = { X = 1 }\n    if r.X <> 1 then failwith \"wrong\""
        )
    )

[<Fact>]
let ``a function without a test attribute is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "let helper () =\n    let res = load () |> Async.RunSynchronously\n    res.X"
        )
    )

[<Fact>]
let ``a blocking site nested in a lambda does not move`` () =
    // only the spine moves; a bind inside a lambda would not compile
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``nested`` () =\n    let f () = load () |> Async.RunSynchronously\n    if (f ()).X <> 1 then failwith \"wrong\""
        )
    )

[<Fact>]
let ``a test that already returns a task is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``already`` () =\n    task {\n        let! r = load () |> Async.StartImmediateAsTask\n        if r.X <> 1 then failwith \"wrong\"\n    } :> Task"
        )
    )

[<Fact>]
let ``a RunSynchronously with a timeout is a different contract`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``timed`` () =\n    let res = Async.RunSynchronously(load (), 1000)\n    if res.X <> 1 then failwith \"wrong\""
        )
    )

[<Fact>]
let ``Result on a task-typed local becomes a bind`` () =
    // `t.Result` on a plain identifier parses as one dotted name, not a
    // DotGet — both shapes must be seen
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``local`` () =\n    let t = fetch ()\n    let res = t.Result\n    if res.X <> 2 then failwith \"wrong\"")
        "task {\n        let t = fetch ()\n        let! res = t\n        if res.X <> 2 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a whole-body async block piped to RunSynchronously is the test itself`` () =
    // no task block: the awaitable becomes the test, upcast to Task
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``whole`` () =\n    async {\n        let! r = load ()\n        if r.X <> 1 then failwith \"wrong\"\n    } |> Async.RunSynchronously")
        "async {\n        let! r = load ()\n        if r.X <> 1 then failwith \"wrong\"\n    } |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task"

[<Fact>]
let ``a final blocking statement of a unit test becomes do-bang`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``final`` () =\n    let res = load () |> Async.RunSynchronously\n    if res.X <> 1 then failwith \"wrong\"\n    work () |> Async.RunSynchronously")
        "task {\n        let! res = load () |> Async.StartImmediateAsTask\n        if res.X <> 1 then failwith \"wrong\"\n        do! work () |> Async.StartImmediateAsTask\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``Wait on a generic task is upcast before do-bang`` () =
    // `do!` needs a unit result; `Task<T>` only has one as a plain `Task`
    assertRewrite
        (scaffold + "[<Fact>]\nlet ``waits`` () =\n    let t = fetch ()\n    t.Wait()")
        "task {\n        let t = fetch ()\n        do! (t :> System.Threading.Tasks.Task)\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a final discarded site gets the unit the ignore supplied`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``discardsLast`` () =\n    let t = fetch ()\n    load () |> Async.RunSynchronously |> ignore")
        "task {\n        let t = fetch ()\n        let! _ = load () |> Async.StartImmediateAsTask\n        ()\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``an NUnit-style member test is rewritten too`` () =
    assertRewrite
        (scaffold
         + "type Fixture() =\n    [<Test>]\n    member _.``reads`` () =\n        let res = load () |> Async.RunSynchronously\n        if res.X <> 1 then failwith \"wrong\"")
        "task {\n            let! res = load () |> Async.StartImmediateAsTask\n            if res.X <> 1 then failwith \"wrong\"\n        } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a value-returning final site has no bind shape`` () =
    // the test returns R, not unit — nothing to `do!`
    Assert.Empty(findIn (scaffold + "[<Fact>]\nlet ``value`` () =\n    let t = fetch ()\n    t.Result"))


[<Fact>]
let ``a whole-body async block on its own line is the test itself`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``whole2`` () =\n    async {\n        let! r = load ()\n        if r.X <> 1 then failwith \"wrong\"\n    }\n    |> Async.RunSynchronously")
        "async {\n        let! r = load ()\n        if r.X <> 1 then failwith \"wrong\"\n    }\n    |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task"

[<Fact>]
let ``a task awaited then run synchronously drops both pipes`` () =
    // `task { } |> Async.AwaitTask |> Async.RunSynchronously`: the task was
    // awaitable all along
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``viaAwait`` () =\n    task {\n        let! r = fetch ()\n        if r.X <> 2 then failwith \"wrong\"\n    } |> Async.AwaitTask |> Async.RunSynchronously")
        "task {\n        let! r = fetch ()\n        if r.X <> 2 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a match on a blocking scrutinee becomes match-bang`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``matches`` () =\n    match load () |> Async.RunSynchronously with\n    | { X = 1 } -> ()\n    | _ -> failwith \"wrong\"")
        "task {\n        match! load () |> Async.StartImmediateAsTask with\n        | { X = 1 } -> ()\n        | _ -> failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``GetResult on a plain task is a do-bang site`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``awaiter`` () =\n    (run ()).GetAwaiter().GetResult()\n    let t = fetch ()\n    if t.Result.X <> 2 then failwith \"wrong\"")
        "task {\n        do! (run ())\n        let t = fetch ()\n        if t.Result.X <> 2 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a discarded site whose pipe opens a new line keeps the pipe in line`` () =
    // `let! _ = ` moves the first line right; the continuation must follow,
    // or the operator lands offside (Fuuga's EvalTests)
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``captures`` () =\n    let mutable seen = \"\"\n    load ()\n    |> Async.RunSynchronously |> ignore\n    seen <- \"x\"")
        "task {\n        let mutable seen = \"\"\n        let! _ = load ()\n                 |> Async.StartImmediateAsTask\n        seen <- \"x\"\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a final unit site whose pipe opens a new line keeps the pipe in line`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``finalPiped`` () =\n    let t = fetch ()\n    work ()\n    |> Async.RunSynchronously")
        "task {\n        let t = fetch ()\n        do! work ()\n            |> Async.StartImmediateAsTask\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a discarded result the typed tree proves unit becomes do-bang`` () =
    // `work ()` is Async<unit>: nothing to discard, so `do!` — while a
    // value-bearing site keeps `let! _ =` rather than gaining Async.Ignore
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``unitDiscard`` () =\n    work () |> Async.RunSynchronously |> ignore\n    load () |> Async.RunSynchronously |> ignore\n    ()")
        "task {\n        do! work () |> Async.StartImmediateAsTask\n        let! _ = load () |> Async.StartImmediateAsTask\n        ()\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a final discarded unit result ends the block on do-bang`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``unitLast`` () =\n    let t = fetch ()\n    work () |> Async.RunSynchronously |> ignore")
        "task {\n        let t = fetch ()\n        do! work () |> Async.StartImmediateAsTask\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a body holding a string literal that spans lines is left alone`` () =
    // re-indenting the block would re-indent the literal's content too, and
    // that compiles — with a different expected value
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``multi`` () =\n    let expected = \"\"\"a\nb\"\"\"\n    let res = load () |> Async.RunSynchronously\n    if string res.X <> expected then failwith \"wrong\""
        )
    )

[<Fact>]
let ``a same-named attribute outside a known framework is not a test`` () =
    // a home-grown [<Test>] with a reflection runner would get a Task
    // nobody awaits, and every failure inside it would vanish
    Assert.Empty(
        findIn (
            scaffold.Replace("module Xunit", "module Homegrown")
            + "[<Fact>]\nlet ``reads`` () =\n    let res = load () |> Async.RunSynchronously\n    if res.X <> 1 then failwith \"wrong\""
        )
    )

[<Fact>]
let ``a body holding a lock across the work is left alone`` () =
    // after a bind the rest may run on another thread; Monitor.Exit there throws
    Assert.Empty(
        findIn (
            scaffold
            + "let gate = obj ()\n[<Fact>]\nlet ``locked`` () =\n    System.Threading.Monitor.Enter gate\n    let res = load () |> Async.RunSynchronously\n    System.Threading.Monitor.Exit gate\n    if res.X <> 1 then failwith \"wrong\""
        )
    )

[<Fact>]
let ``a Wait bound to a name has no let-bang form`` () =
    // `let x = t.Wait()` binds unit; `let! x = t` would retype x
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``waitBound`` () =\n    let t = fetch ()\n    let x = t.Wait()\n    x"
        )
    )

[<Fact>]
let ``a continuation aligned with the bound expression follows the bang`` () =
    // `let` → `let!` moves the expression one column right
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``aligned`` () =\n    let res = load ()\n              |> Async.RunSynchronously\n    if res.X <> 1 then failwith \"wrong\"")
        "task {\n        let! res = load ()\n                   |> Async.StartImmediateAsTask\n        if res.X <> 1 then failwith \"wrong\"\n    } :> System.Threading.Tasks.Task"

// ---- placement shapes: namespaces, nested modules, fixture classes ----

/// The attribute in a real `Xunit` namespace, the tests in another
/// namespace, so nested modules and classes can be laid out as projects do.
[<Literal>]
let private namespaced =
    "namespace Xunit\ntype FactAttribute() =\n    inherit System.Attribute()\nnamespace Tests\nopen Xunit\ntype R = { X: int }\nmodule Support =\n    let load () = async { return { X = 1 } }\n"

[<Fact>]
let ``a test two modules deep inside a namespace is rewritten`` () =
    assertRewrite
        (namespaced
         + "module Outer =\n    module Inner =\n        open Support\n        [<Fact>]\n        let ``reads`` () =\n            let res = load () |> Async.RunSynchronously\n            if res.X <> 1 then failwith \"wrong\"")
        "task {\n                let! res = load () |> Async.StartImmediateAsTask\n                if res.X <> 1 then failwith \"wrong\"\n            } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a fixture class member with a constructor argument is rewritten`` () =
    assertRewrite
        (namespaced
         + "open Support\ntype ``Compress internals fixture``(tag: string) =\n    [<Fact>]\n    member test.``Compress file test`` () =\n        let res = load () |> Async.RunSynchronously\n        if res.X <> 1 then failwith tag")
        "task {\n            let! res = load () |> Async.StartImmediateAsTask\n            if res.X <> 1 then failwith tag\n        } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a fixture class inside a nested module is rewritten`` () =
    assertRewrite
        (namespaced
         + "module Suite =\n    open Support\n    type Fixture() =\n        [<Fact>]\n        member _.``reads`` () =\n            let res = load () |> Async.RunSynchronously\n            if res.X <> 1 then failwith \"wrong\"")
        "task {\n                let! res = load () |> Async.StartImmediateAsTask\n                if res.X <> 1 then failwith \"wrong\"\n            } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a static member test and a whole-body member are rewritten`` () =
    assertRewrite
        (namespaced
         + "open Support\ntype Fixture() =\n    [<Fact>]\n    static member ``whole`` () =\n        async {\n            let! r = load ()\n            if r.X <> 1 then failwith \"wrong\"\n        } |> Async.RunSynchronously")
        "async {\n            let! r = load ()\n            if r.X <> 1 then failwith \"wrong\"\n        } |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task"

// ---- attribute variants across the three frameworks ----

/// The attribute types the rule trusts, each in its real namespace.
[<Literal>]
let private frameworks =
    "namespace Xunit\ntype FactAttribute() =\n    inherit System.Attribute()\n    member val Skip = \"\" with get, set\ntype TheoryAttribute() =\n    inherit System.Attribute()\ntype InlineDataAttribute(n: int) =\n    inherit System.Attribute()\nnamespace NUnit.Framework\ntype TestAttribute() =\n    inherit System.Attribute()\ntype TestCaseAttribute(n: int) =\n    inherit System.Attribute()\nnamespace Microsoft.VisualStudio.TestTools.UnitTesting\ntype TestClassAttribute() =\n    inherit System.Attribute()\ntype TestMethodAttribute() =\n    inherit System.Attribute()\nnamespace Tests\ntype R = { X: int }\nmodule Support =\n    let load () = async { return { X = 1 } }\n"

let private body =
    "\n        let res = load () |> Async.RunSynchronously\n        if res.X <> 1 then failwith \"wrong\""

let private expectedMember =
    "task {\n            let! res = load () |> Async.StartImmediateAsTask\n            if res.X <> 1 then failwith \"wrong\"\n        } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a qualified Fact with a Skip argument is a test`` () =
    assertRewrite
        (frameworks
         + "module T =\n    open Support\n    [<Xunit.Fact(Skip = \"slow\")>]\n    let ``reads`` () ="
         + body)
        expectedMember

[<Fact>]
let ``a Theory with InlineData and a parameter is a test`` () =
    assertRewrite
        (frameworks
         + "module T =\n    open Support\n    open Xunit\n    [<Theory>]\n    [<InlineData(1)>]\n    let ``reads`` (n: int) ="
         + body)
        expectedMember

[<Fact>]
let ``an NUnit Test and TestCase member in a fixture is a test`` () =
    assertRewrite
        (frameworks
         + "open Support\nopen NUnit.Framework\ntype Fixture() =\n    [<Test; TestCase(2)>]\n    member _.``reads`` () ="
         + body)
        expectedMember

[<Fact>]
let ``an MSTest TestMethod in a TestClass is a test`` () =
    assertRewrite
        (frameworks
         + "open Support\nopen Microsoft.VisualStudio.TestTools.UnitTesting\n[<TestClass>]\ntype Fixture() =\n    [<TestMethod>]\n    member _.``reads`` () ="
         + body)
        expectedMember

// ---- FR0142: Task.WaitAll and Assert.Throws move too ----

[<Fact>]
let ``WaitAll on plain tasks becomes do-bang WhenAll`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``joins`` () =\n    let a = run ()\n    let b = run ()\n    Task.WaitAll(a, b)")
        "task {\n        let a = run ()\n        let b = run ()\n        do! Task.WhenAll(a, b)\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``WaitAll on generic tasks binds and discards`` () =
    // WhenAll of Task<T> params yields the results: `do!` has no unit to
    // bind, `let! _ =` does
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``joinsValues`` () =\n    Task.WaitAll(fetch (), fetch ())\n    ()")
        "task {\n        let! _ = Task.WhenAll(fetch (), fetch ())\n        ()\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``WaitAll on a task array value becomes do-bang WhenAll`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``joinsArray`` () =\n    let ts = [| run (); run () |]\n    Task.WaitAll ts")
        "task {\n        let ts = [| run (); run () |]\n        do! Task.WhenAll ts\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``WaitAll with a timeout is a different contract`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``timedJoin`` () =\n    let a = run ()\n    Task.WaitAll([| a |], 1000) |> ignore"
        )
    )

/// xUnit's Assert with the sync and async throw asserts, declared in the
/// fixture under the `Xunit` module so the rule trusts it.
[<Literal>]
let private assertScaffold =
    "type Assert =\n    static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>\n    static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>\n"

[<Fact>]
let ``a blocking call inside Assert.Throws moves to ThrowsAsync and binds`` () =
    assertRewrite
        (scaffold
         + assertScaffold
         + "[<Fact>]\nlet ``throws`` () =\n    let t = fetch ()\n    let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())\n    ignore ex.Message")
        "task {\n        let t = fetch ()\n        let! ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)\n        ignore ex.Message\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a discarded Assert.Throws with a successor binds to underscore`` () =
    assertRewrite
        (scaffold
         + assertScaffold
         + "[<Fact>]\nlet ``throwsIgnored`` () =\n    Assert.Throws<InvalidOperationException>(fun () -> load () |> Async.RunSynchronously |> ignore) |> ignore\n    ()")
        "task {\n        let! _ = Assert.ThrowsAsync<InvalidOperationException>(fun () -> load () |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task)\n        ()\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``NUnit's ThrowsAsync returns the exception, so the let stays a let`` () =
    assertRewrite
        "namespace NUnit.Framework\nopen System\nopen System.Threading.Tasks\ntype TestAttribute() =\n    inherit Attribute()\ntype Assert =\n    static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>\n    static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : 'E = Unchecked.defaultof<'E>\nmodule Tests =\n    let fetch () = Task.FromResult 1\n    [<Test>]\n    let ``throws`` () =\n        let t = fetch ()\n        let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())\n        ignore ex.Message"
        "task {\n            let t = fetch ()\n            let ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)\n            ignore ex.Message\n        } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a test choreographing threads with a signal keeps its blocking waits`` () =
    // Mibo's adaptive-graph tests: work handed to a thread, a signal waited
    // on, and the rest of the test expected on the SAME thread; `do!`
    // resumed elsewhere and the graph refused the caller
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``worker`` () =\n    let signal = new System.Threading.ManualResetEventSlim(false)\n    let worker = Task.Run(fun () -> signal.Set())\n    signal.Wait()\n    worker.Wait()"
        )
    )

[<Fact>]
let ``a comment trailing the last line stays on that line inside the block`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``reads`` () =\n    let res = load () |> Async.RunSynchronously\n    if res.X <> 1 then failwith \"wrong\" // drained by then")
        "task {\n        let! res = load () |> Async.StartImmediateAsTask\n        if res.X <> 1 then failwith \"wrong\" // drained by then\n    } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a comment trailing a bare awaitable test survives the upcast`` () =
    assertRewrite
        (scaffold
         + "[<Fact>]\nlet ``bare`` () =\n    work () |> Async.RunSynchronously // one shot")
        "work () |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task // one shot"

// ---- state that outlives a test ----

[<Fact>]
let ``a test assigning a module-level mutable is left alone`` () =
    // the shape the maintainer named: a global testContext each test sets
    // its own way. Freeing the thread lets collections that always COULD
    // have raced actually do so
    Assert.Empty(
        findIn (
            scaffold
            + "let mutable testContext = 0\n\n[<Fact>]\nlet ``t`` () =\n    testContext <- 1\n    let r = load () |> Async.RunSynchronously\n    ignore r\n"
        )
    )

[<Fact>]
let ``a test merely reading a module-level mutable is left alone`` () =
    // a reader races a writer just as a writer races a writer
    Assert.Empty(
        findIn (
            scaffold
            + "let mutable testContext = 0\n\n[<Fact>]\nlet ``t`` () =\n    let r = load () |> Async.RunSynchronously\n    ignore (r, testContext)\n"
        )
    )

[<Fact>]
let ``a test assigning its OWN mutable still converts`` () =
    // a local dies with the test; nothing outside can observe it
    match
        findIn (
            scaffold
            + "[<Fact>]\nlet ``t`` () =\n    let mutable seen = 0\n    let r = load () |> Async.RunSynchronously\n    seen <- r.X\n    ignore seen\n"
        )
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected the rewrite, got %A" other

[<Fact>]
let ``a file that installs global state by reflection converts nothing`` () =
    // MpDataTests: a harness swaps a library's private static holders and
    // puts them back on Dispose. There is no assignment to find and no name
    // this file declares — the state lives in another assembly, reached
    // through a string — and the tests never mention the machinery, so the
    // question is asked of the whole file
    Assert.Empty(
        findIn (
            scaffold
            + "open System.Reflection\n\ntype Mock() =\n    do typeof<R>.GetProperty(\"x\", BindingFlags.NonPublic ||| BindingFlags.Static) |> ignore\n\n[<Fact>]\nlet ``t`` () =\n    let r = load () |> Async.RunSynchronously\n    ignore r\n"
        )
    )

[<Fact>]
let ``a test setting an environment variable is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + "[<Fact>]\nlet ``t`` () =\n    Environment.SetEnvironmentVariable(\"K\", \"v\")\n    let r = load () |> Async.RunSynchronously\n    ignore r\n"
        )
    )
