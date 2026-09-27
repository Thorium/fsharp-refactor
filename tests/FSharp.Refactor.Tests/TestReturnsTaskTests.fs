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
         + fsharp
             """
             [<Fact>]
             let ``reads`` () =
                 let res = load () |> Async.RunSynchronously
                 if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    let! res = load () |> Async.StartImmediateAsTask
                    if res.X <> 1 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``Result on a task becomes a bind`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``fetches`` () =
                 let res = (fetch ()).Result
                 if res.X <> 2 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    let! res = (fetch ())
                    if res.X <> 2 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a final Wait becomes do-bang`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``runs`` () =
                 let t = run ()
                 t.Wait()
             """)
        (fsharp
            """
            task {
                    let t = run ()
                    do! t
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a discarded blocking call becomes let-bang underscore`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``discards`` () =
                 load () |> Async.RunSynchronously |> ignore
                 ()
             """)
        (fsharp
            """
            task {
                    let! _ = load () |> Async.StartImmediateAsTask
                    ()
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a test without a blocking site is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``plain`` () =
                    let r = { X = 1 }
                    if r.X <> 1 then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``a function without a test attribute is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                let helper () =
                    let res = load () |> Async.RunSynchronously
                    res.X
                """
        )
    )

[<Fact>]
let ``a blocking site nested in a lambda does not move`` () =
    // only the spine moves; a bind inside a lambda would not compile
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``nested`` () =
                    let f () = load () |> Async.RunSynchronously
                    if (f ()).X <> 1 then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``a test holding a Span is left synchronous`` () =
    // a byref-like local cannot be a field of the task's state machine
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``spanned`` () =
                    let buf = Span<byte>(Array.zeroCreate 4)
                    let res = load () |> Async.RunSynchronously
                    if res.X <> buf.Length then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``a test that already returns a task is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``already`` () =
                    task {
                        let! r = load () |> Async.StartImmediateAsTask
                        if r.X <> 1 then failwith "wrong"
                    } :> Task
                """
        )
    )

[<Fact>]
let ``a RunSynchronously with a timeout is a different contract`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``timed`` () =
                    let res = Async.RunSynchronously(load (), 1000)
                    if res.X <> 1 then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``Result on a task-typed local becomes a bind`` () =
    // `t.Result` on a plain identifier parses as one dotted name, not a
    // DotGet — both shapes must be seen
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``local`` () =
                 let t = fetch ()
                 let res = t.Result
                 if res.X <> 2 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    let! res = t
                    if res.X <> 2 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a whole-body async block piped to RunSynchronously is the test itself`` () =
    // no task block: the awaitable becomes the test, upcast to Task
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``whole`` () =
                 async {
                     let! r = load ()
                     if r.X <> 1 then failwith "wrong"
                 } |> Async.RunSynchronously
             """)
        (fsharp
            """
            async {
                    let! r = load ()
                    if r.X <> 1 then failwith "wrong"
                } |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a final blocking statement of a unit test becomes do-bang`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``final`` () =
                 let res = load () |> Async.RunSynchronously
                 if res.X <> 1 then failwith "wrong"
                 work () |> Async.RunSynchronously
             """)
        (fsharp
            """
            task {
                    let! res = load () |> Async.StartImmediateAsTask
                    if res.X <> 1 then failwith "wrong"
                    do! work () |> Async.StartImmediateAsTask
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``Wait on a generic task is upcast before do-bang`` () =
    // `do!` needs a unit result; `Task<T>` only has one as a plain `Task`
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``waits`` () =
                 let t = fetch ()
                 t.Wait()
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    do! (t :> System.Threading.Tasks.Task)
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a final discarded site gets the unit the ignore supplied`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``discardsLast`` () =
                 let t = fetch ()
                 load () |> Async.RunSynchronously |> ignore
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    let! _ = load () |> Async.StartImmediateAsTask
                    ()
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``an NUnit-style member test is rewritten too`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             type Fixture() =
                 [<Test>]
                 member _.``reads`` () =
                     let res = load () |> Async.RunSynchronously
                     if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                        let! res = load () |> Async.StartImmediateAsTask
                        if res.X <> 1 then failwith "wrong"
                    } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a value-returning final site has no bind shape`` () =
    // the test returns R, not unit — nothing to `do!`
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``value`` () =
                    let t = fetch ()
                    t.Result
                """
        )
    )


[<Fact>]
let ``a whole-body async block on its own line is the test itself`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``whole2`` () =
                 async {
                     let! r = load ()
                     if r.X <> 1 then failwith "wrong"
                 }
                 |> Async.RunSynchronously
             """)
        (fsharp
            """
            async {
                    let! r = load ()
                    if r.X <> 1 then failwith "wrong"
                }
                |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a task awaited then run synchronously drops both pipes`` () =
    // `task { } |> Async.AwaitTask |> Async.RunSynchronously`: the task was
    // awaitable all along
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``viaAwait`` () =
                 task {
                     let! r = fetch ()
                     if r.X <> 2 then failwith "wrong"
                 } |> Async.AwaitTask |> Async.RunSynchronously
             """)
        (fsharp
            """
            task {
                    let! r = fetch ()
                    if r.X <> 2 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a match on a blocking scrutinee becomes match-bang`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``matches`` () =
                 match load () |> Async.RunSynchronously with
                 | { X = 1 } -> ()
                 | _ -> failwith "wrong"
             """)
        (fsharp
            """
            task {
                    match! load () |> Async.StartImmediateAsTask with
                    | { X = 1 } -> ()
                    | _ -> failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``GetResult on a plain task is a do-bang site`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``awaiter`` () =
                 (run ()).GetAwaiter().GetResult()
                 let t = fetch ()
                 if t.Result.X <> 2 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    do! (run ())
                    let t = fetch ()
                    if t.Result.X <> 2 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a discarded site whose pipe opens a new line keeps the pipe in line`` () =
    // `let! _ = ` moves the first line right; the continuation must follow,
    // or the operator lands offside (Fuuga's EvalTests)
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``captures`` () =
                 let mutable seen = ""
                 load ()
                 |> Async.RunSynchronously |> ignore
                 seen <- "x"
             """)
        (fsharp
            """
            task {
                    let mutable seen = ""
                    let! _ = load ()
                             |> Async.StartImmediateAsTask
                    seen <- "x"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a final unit site whose pipe opens a new line keeps the pipe in line`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``finalPiped`` () =
                 let t = fetch ()
                 work ()
                 |> Async.RunSynchronously
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    do! work ()
                        |> Async.StartImmediateAsTask
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a discarded result the typed tree proves unit becomes do-bang`` () =
    // `work ()` is Async<unit>: nothing to discard, so `do!` — while a
    // value-bearing site keeps `let! _ =` rather than gaining Async.Ignore
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``unitDiscard`` () =
                 work () |> Async.RunSynchronously |> ignore
                 load () |> Async.RunSynchronously |> ignore
                 ()
             """)
        (fsharp
            """
            task {
                    do! work () |> Async.StartImmediateAsTask
                    let! _ = load () |> Async.StartImmediateAsTask
                    ()
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a final discarded unit result ends the block on do-bang`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``unitLast`` () =
                 let t = fetch ()
                 work () |> Async.RunSynchronously |> ignore
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    do! work () |> Async.StartImmediateAsTask
                } :> System.Threading.Tasks.Task
            """)

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
            + fsharp
                """
                [<Fact>]
                let ``reads`` () =
                    let res = load () |> Async.RunSynchronously
                    if res.X <> 1 then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``a body holding a lock across the work is left alone`` () =
    // after a bind the rest may run on another thread; Monitor.Exit there throws
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                let gate = obj ()
                [<Fact>]
                let ``locked`` () =
                    System.Threading.Monitor.Enter gate
                    let res = load () |> Async.RunSynchronously
                    System.Threading.Monitor.Exit gate
                    if res.X <> 1 then failwith "wrong"
                """
        )
    )

[<Fact>]
let ``a Wait bound to a name has no let-bang form`` () =
    // `let x = t.Wait()` binds unit; `let! x = t` would retype x
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``waitBound`` () =
                    let t = fetch ()
                    let x = t.Wait()
                    x
                """
        )
    )

[<Fact>]
let ``a continuation aligned with the bound expression follows the bang`` () =
    // `let` → `let!` moves the expression one column right
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``aligned`` () =
                 let res = load ()
                           |> Async.RunSynchronously
                 if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    let! res = load ()
                               |> Async.StartImmediateAsTask
                    if res.X <> 1 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``an expression starting on the line below its let keeps its indentation`` () =
    // FunStripe's tests: the `!` moves nothing on a line below the `let`,
    // whose lines stand relative to the `let` column, not to the `=` - the
    // body came out one column deeper than its block's first line
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``below`` () =
                 let res =
                     async {
                         let! r = load ()
                         return r
                     }
                     |> Async.RunSynchronously
                 if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                    let! res =
                        async {
                            let! r = load ()
                            return r
                        }
                        |> Async.StartImmediateAsTask
                    if res.X <> 1 then failwith "wrong"
                } :> System.Threading.Tasks.Task
            """)

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
         + fsharp
             """
             module Outer =
                 module Inner =
                     open Support
                     [<Fact>]
                     let ``reads`` () =
                         let res = load () |> Async.RunSynchronously
                         if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                            let! res = load () |> Async.StartImmediateAsTask
                            if res.X <> 1 then failwith "wrong"
                        } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a fixture class member with a constructor argument is rewritten`` () =
    assertRewrite
        (namespaced
         + fsharp
             """
             open Support
             type ``Compress internals fixture``(tag: string) =
                 [<Fact>]
                 member test.``Compress file test`` () =
                     let res = load () |> Async.RunSynchronously
                     if res.X <> 1 then failwith tag
             """)
        (fsharp
            """
            task {
                        let! res = load () |> Async.StartImmediateAsTask
                        if res.X <> 1 then failwith tag
                    } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a fixture class inside a nested module is rewritten`` () =
    assertRewrite
        (namespaced
         + fsharp
             """
             module Suite =
                 open Support
                 type Fixture() =
                     [<Fact>]
                     member _.``reads`` () =
                         let res = load () |> Async.RunSynchronously
                         if res.X <> 1 then failwith "wrong"
             """)
        (fsharp
            """
            task {
                            let! res = load () |> Async.StartImmediateAsTask
                            if res.X <> 1 then failwith "wrong"
                        } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a static member test and a whole-body member are rewritten`` () =
    assertRewrite
        (namespaced
         + fsharp
             """
             open Support
             type Fixture() =
                 [<Fact>]
                 static member ``whole`` () =
                     async {
                         let! r = load ()
                         if r.X <> 1 then failwith "wrong"
                     } |> Async.RunSynchronously
             """)
        (fsharp
            """
            async {
                        let! r = load ()
                        if r.X <> 1 then failwith "wrong"
                    } |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task
            """)

// ---- attribute variants across the three frameworks ----

/// The attribute types the rule trusts, each in its real namespace.
[<Literal>]
let private frameworks =
    "namespace Xunit\ntype FactAttribute() =\n    inherit System.Attribute()\n    member val Skip = \"\" with get, set\ntype TheoryAttribute() =\n    inherit System.Attribute()\ntype InlineDataAttribute(n: int) =\n    inherit System.Attribute()\nnamespace NUnit.Framework\ntype TestAttribute() =\n    inherit System.Attribute()\ntype TestCaseAttribute(n: int) =\n    inherit System.Attribute()\nnamespace Microsoft.VisualStudio.TestTools.UnitTesting\ntype TestClassAttribute() =\n    inherit System.Attribute()\ntype TestMethodAttribute() =\n    inherit System.Attribute()\nnamespace Tests\ntype R = { X: int }\nmodule Support =\n    let load () = async { return { X = 1 } }\n"

[<Literal>]
let private body =
    "\n        let res = load () |> Async.RunSynchronously\n        if res.X <> 1 then failwith \"wrong\""

[<Literal>]
let private expectedMember =
    "task {\n            let! res = load () |> Async.StartImmediateAsTask\n            if res.X <> 1 then failwith \"wrong\"\n        } :> System.Threading.Tasks.Task"

[<Fact>]
let ``a qualified Fact with a Skip argument is a test`` () =
    assertRewrite
        (frameworks
         + fsharp
             """
             module T =
                 open Support
                 [<Xunit.Fact(Skip = "slow")>]
                 let ``reads`` () =
             """
         + body)
        expectedMember

[<Fact>]
let ``a Theory with InlineData and a parameter is a test`` () =
    assertRewrite
        (frameworks
         + fsharp
             """
             module T =
                 open Support
                 open Xunit
                 [<Theory>]
                 [<InlineData(1)>]
                 let ``reads`` (n: int) =
             """
         + body)
        expectedMember

[<Fact>]
let ``an NUnit Test and TestCase member in a fixture is a test`` () =
    assertRewrite
        (frameworks
         + fsharp
             """
             open Support
             open NUnit.Framework
             type Fixture() =
                 [<Test; TestCase(2)>]
                 member _.``reads`` () =
             """
         + body)
        expectedMember

[<Fact>]
let ``an MSTest TestMethod in a TestClass is a test`` () =
    assertRewrite
        (frameworks
         + fsharp
             """
             open Support
             open Microsoft.VisualStudio.TestTools.UnitTesting
             [<TestClass>]
             type Fixture() =
                 [<TestMethod>]
                 member _.``reads`` () =
             """
         + body)
        expectedMember

// ---- FR0142: Task.WaitAll and Assert.Throws move too ----

[<Fact>]
let ``WaitAll on plain tasks becomes do-bang WhenAll`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``joins`` () =
                 let a = run ()
                 let b = run ()
                 Task.WaitAll(a, b)
             """)
        (fsharp
            """
            task {
                    let a = run ()
                    let b = run ()
                    do! Task.WhenAll(a, b)
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``WaitAll on generic tasks binds and discards`` () =
    // WhenAll of Task<T> params yields the results: `do!` has no unit to
    // bind, `let! _ =` does
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``joinsValues`` () =
                 Task.WaitAll(fetch (), fetch ())
                 ()
             """)
        (fsharp
            """
            task {
                    let! _ = Task.WhenAll(fetch (), fetch ())
                    ()
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``WaitAll on a task array value becomes do-bang WhenAll`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``joinsArray`` () =
                 let ts = [| run (); run () |]
                 Task.WaitAll ts
             """)
        (fsharp
            """
            task {
                    let ts = [| run (); run () |]
                    do! Task.WhenAll ts
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``WaitAll with a timeout is a different contract`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``timedJoin`` () =
                    let a = run ()
                    Task.WaitAll([| a |], 1000) |> ignore
                """
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
         + fsharp
             """
             [<Fact>]
             let ``throws`` () =
                 let t = fetch ()
                 let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                 ignore ex.Message
             """)
        (fsharp
            """
            task {
                    let t = fetch ()
                    let! ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)
                    ignore ex.Message
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a discarded Assert.Throws with a successor binds to underscore`` () =
    assertRewrite
        (scaffold
         + assertScaffold
         + fsharp
             """
             [<Fact>]
             let ``throwsIgnored`` () =
                 Assert.Throws<InvalidOperationException>(fun () -> load () |> Async.RunSynchronously |> ignore) |> ignore
                 ()
             """)
        (fsharp
            """
            task {
                    let! _ = Assert.ThrowsAsync<InvalidOperationException>(fun () -> load () |> Async.StartImmediateAsTask :> System.Threading.Tasks.Task)
                    ()
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``NUnit's ThrowsAsync returns the exception, so the let stays a let`` () =
    assertRewrite
        (fsharp
            """
            namespace NUnit.Framework
            open System
            open System.Threading.Tasks
            type TestAttribute() =
                inherit Attribute()
            type Assert =
                static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>
                static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : 'E = Unchecked.defaultof<'E>
            module Tests =
                let fetch () = Task.FromResult 1
                [<Test>]
                let ``throws`` () =
                    let t = fetch ()
                    let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                    ignore ex.Message
            """)
        (fsharp
            """
            task {
                        let t = fetch ()
                        let ex = Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)
                        ignore ex.Message
                    } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a test choreographing threads with a signal keeps its blocking waits`` () =
    // Mibo's adaptive-graph tests: work handed to a thread, a signal waited
    // on, and the rest of the test expected on the SAME thread; `do!`
    // resumed elsewhere and the graph refused the caller
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``worker`` () =
                    let signal = new System.Threading.ManualResetEventSlim(false)
                    let worker = Task.Run(fun () -> signal.Set())
                    signal.Wait()
                    worker.Wait()
                """
        )
    )

[<Fact>]
let ``a comment trailing the last line stays on that line inside the block`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``reads`` () =
                 let res = load () |> Async.RunSynchronously
                 if res.X <> 1 then failwith "wrong" // drained by then
             """)
        (fsharp
            """
            task {
                    let! res = load () |> Async.StartImmediateAsTask
                    if res.X <> 1 then failwith "wrong" // drained by then
                } :> System.Threading.Tasks.Task
            """)

[<Fact>]
let ``a comment trailing a bare awaitable test survives the upcast`` () =
    assertRewrite
        (scaffold
         + fsharp
             """
             [<Fact>]
             let ``bare`` () =
                 work () |> Async.RunSynchronously // one shot
             """)
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
            + fsharp
                """
                let mutable testContext = 0

                [<Fact>]
                let ``t`` () =
                    testContext <- 1
                    let r = load () |> Async.RunSynchronously
                    ignore r

                """
        )
    )

[<Fact>]
let ``a test merely reading a module-level mutable is left alone`` () =
    // a reader races a writer just as a writer races a writer
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                let mutable testContext = 0

                [<Fact>]
                let ``t`` () =
                    let r = load () |> Async.RunSynchronously
                    ignore (r, testContext)

                """
        )
    )

[<Fact>]
let ``a class's own static mutable does not hold its tests back`` () =
    // CarmelNet: one test writes a payment id into `static let mutable`,
    // the next reads it. Tests of one class run one after another in xUnit,
    // NUnit and MSTest whatever they return, so both convert
    let source =
        scaffold
        + fsharp
            """
            type Fixture() =
                static let mutable created = 0
                [<Fact>]
                member _.``creates`` () =
                    let r = load () |> Async.RunSynchronously
                    created <- r.X
                [<Fact>]
                member _.``reads back`` () =
                    let r = load () |> Async.RunSynchronously
                    if r.X <> created then failwith "wrong"

            """

    Assert.Equal(2, (findIn source).Length)

[<Fact>]
let ``a class opted into parallel tests keeps its static state shared`` () =
    // NUnit's Parallelizable(ParallelScope.All) runs one class's tests
    // beside each other: the class-local exemption no longer holds
    let source =
        scaffold
        + fsharp
            """
            type ParallelizableAttribute(scope: int) =
                inherit Attribute()
            [<Parallelizable(2)>]
            type Fixture() =
                static let mutable created = 0
                [<Fact>]
                member _.``creates`` () =
                    let r = load () |> Async.RunSynchronously
                    created <- r.X

            """

    Assert.Empty(findIn source)

[<Fact>]
let ``another class's state still holds a test back`` () =
    // a write into a holder class is an assignment beyond the test's own
    // class, whichever class runs beside it
    let source =
        scaffold
        + fsharp
            """
            type Holder() =
                static let mutable created = 0
                static member Created
                    with get () = created
                    and set v = created <- v
            type Fixture() =
                [<Fact>]
                member _.``writes`` () =
                    let r = load () |> Async.RunSynchronously
                    Holder.Created <- r.X

            """

    Assert.Empty(findIn source)

[<Fact>]
let ``a test assigning its OWN mutable still converts`` () =
    // a local dies with the test; nothing outside can observe it
    match
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``t`` () =
                    let mutable seen = 0
                    let r = load () |> Async.RunSynchronously
                    seen <- r.X
                    ignore seen

                """
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
            + fsharp
                """
                open System.Reflection

                type Mock() =
                    do typeof<R>.GetProperty("x", BindingFlags.NonPublic ||| BindingFlags.Static) |> ignore

                [<Fact>]
                let ``t`` () =
                    let r = load () |> Async.RunSynchronously
                    ignore r

                """
        )
    )

[<Fact>]
let ``a test setting an environment variable is left alone`` () =
    Assert.Empty(
        findIn (
            scaffold
            + fsharp
                """
                [<Fact>]
                let ``t`` () =
                    Environment.SetEnvironmentVariable("K", "v")
                    let r = load () |> Async.RunSynchronously
                    ignore r

                """
        )
    )
