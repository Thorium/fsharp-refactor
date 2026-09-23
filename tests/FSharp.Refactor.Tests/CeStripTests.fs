module FSharp.Refactor.Tests.CeStripTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    CeStrip.find tree sourceText

let private assertSingleSuggestion (source: string) (expectedReplacement: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``return-bang of identifier is stripped`` () =
    assertSingleSuggestion "module Test\nlet f (comp: Async<int>) = async { return! comp }" "comp"

[<Fact>]
let ``a tail thunk called where it is defined collapses to its body`` () =
    assertSingleSuggestion
        "module Test\nlet f (xs: ResizeArray<int>) v =\n    let x =\n        let runTail () =\n            xs.Clear()\n            v\n        runTail ()\n    x"
        "xs.Clear()\n        v"

[<Fact>]
let ``a returned tail thunk collapses with the return reseated on its terminal`` () =
    let source =
        "module Test\nlet f (xs: ResizeArray<int>) v =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail () =\n            xs.Clear()\n            v\n        return runTail ()\n    }"

    match findIn source |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity) with
    | [ s ] ->
        Assert.Equal("xs.Clear()\n        return v", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one thunk collapse, got %A" other

[<Fact>]
let ``numbered wrappers collapse one layer per pass`` () =
    // the live three-deep damage: each layer is its own suggestion, the
    // applier takes the innermost, and the next pass takes the next
    let source =
        "module Test\nlet f (xs: ResizeArray<int>) v =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail3 () =\n            let runTail2 () =\n                let runTail () =\n                    xs.Clear()\n                    v\n                runTail ()\n            runTail2 ()\n        return runTail3 ()\n    }"

    let collapses =
        findIn source |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity)

    Assert.Equal(3, collapses.Length)

[<Fact>]
let ``a thunk with a four-line body is the wrap FR0029 meant to make`` () =
    // collapsing a justified wrap would hand FR0029 and FR0005 an eternal
    // wrap/unwrap oscillation
    Assert.Empty(
        findIn
            "module Test\nlet f (xs: ResizeArray<int>) v =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail () =\n            let a = v + 1\n            let b = a + 1\n            xs.Clear()\n            a + b\n        return runTail ()\n    }"
    )

[<Fact>]
let ``a body that starts with a thunk but carries more statements is a justified wrap`` () =
    // collapsing here would strand the tail back in the machine and let
    // FR0029 wrap it again — the other side of the oscillation
    Assert.Empty(
        findIn
            "module Test\nlet f (xs: ResizeArray<int>) v =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail2 () =\n            let runTail () =\n                xs.Clear()\n                v\n            let extra = runTail ()\n            extra + 1\n        return runTail2 ()\n    }"
        |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity && s.OriginalText.Contains "runTail2")
    )

[<Fact>]
let ``a triple-quoted string inside a collapsed thunk keeps its indentation`` () =
    // the dedent must not strip leading whitespace that is string CONTENT
    let source =
        "module Test\nlet f (emit: string -> string) =\n    let x =\n        let runTail () =\n            emit \"\"\"\n            payload\n\"\"\"\n        runTail ()\n    x"

    match findIn source |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity) with
    | [ s ] -> Assert.Contains("\n            payload", s.ReplacementText)
    | other -> failwithf "Expected exactly one thunk collapse, got %A" other

[<Fact>]
let ``a thunk with a human name is left alone`` () =
    Assert.Empty(
        findIn
            "module Test\nlet f (xs: ResizeArray<int>) v =\n    let x =\n        let cleanup () =\n            xs.Clear()\n            v\n        cleanup ()\n    x"
    )

[<Fact>]
let ``a returned thunk with a branching terminal is left alone`` () =
    Assert.Empty(
        findIn
            "module Test\nlet f (xs: ResizeArray<int>) c =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail () =\n            xs.Clear()\n            if c then 1 else 2\n        return runTail ()\n    }"
    )

[<Fact>]
let ``let-bang rewrap identity is stripped`` () =
    assertSingleSuggestion "module Test\nlet f (comp: Async<int>) = async { let! v = comp in return v }" "comp"

[<Fact>]
let ``multi-line let-bang rewrap identity is stripped`` () =
    assertSingleSuggestion
        "module Test\nlet f (comp: Async<int>) =\n    async {\n        let! v = comp\n        return v\n    }"
        "comp"

[<Fact>]
let ``wrap piped to RunSynchronously is stripped and parenthesized`` () =
    assertSingleSuggestion "module Test\nlet f x = async { return x + 1 } |> Async.RunSynchronously" "(x + 1)"

[<Fact>]
let ``wrap applied to RunSynchronously is stripped and parenthesized`` () =
    assertSingleSuggestion "module Test\nlet f x = Async.RunSynchronously (async { return x + 1 })" "(x + 1)"

[<Fact>]
let ``atomic returned value stays unparenthesized`` () =
    assertSingleSuggestion "module Test\nlet f x = async { return x } |> Async.RunSynchronously" "x"

[<Fact>]
let ``tuple return inside a tuple context keeps its grouping`` () =
    // review regression: `(1, 2, "tag")` would silently flatten the pair
    assertSingleSuggestion "module Test\nlet pair = (async { return 1, 2 } |> Async.RunSynchronously, \"tag\")" "(1, 2)"

[<Fact>]
let ``runner strip as an operand keeps precedence`` () =
    // review regression: bare `a + b * 2` would compute a + (b*2)
    assertSingleSuggestion "module Test\nlet f a b = Async.RunSynchronously (async { return a + b }) * 2" "(a + b)"

[<Fact>]
let ``dotted path computation is not stripped`` () =
    // a dotted path can be a property getter; stripping would move its
    // evaluation from per-run to construction time
    assertNoSuggestion "module Test\ntype S = { Comp: Async<int> }\nlet f (s: S) = async { return! s.Comp }"

[<Fact>]
let ``plain return without runner is not stripped`` () =
    // stripping would change the type from Async<'T> to 'T
    assertNoSuggestion "module Test\nlet f x = async { return x + 1 }"

[<Fact>]
let ``return-bang of application is not stripped`` () =
    // evaluating `g x` early could run construction-time side effects
    assertNoSuggestion "module Test\nlet f g x = async { return! g x }"

[<Fact>]
let ``use-bang is never stripped`` () =
    assertNoSuggestion "module Test\nlet f (comp: Async<System.IDisposable>) = async { use! v = comp in return v }"

[<Fact>]
let ``let-bang with different returned value is not stripped`` () =
    assertNoSuggestion "module Test\nlet f (comp: Async<int>) (w: int) = async { let! v = comp in return w }"

[<Fact>]
let ``let-bang with transformed result is not stripped`` () =
    assertNoSuggestion "module Test\nlet f (comp: Async<int>) = async { let! v = comp in return v + 1 }"

[<Fact>]
let ``binding computation is not stripped`` () =
    assertNoSuggestion "module Test\nlet f (a: Async<int>) (g: int -> Async<int>) = async { let! v = a in return! g v }"

[<Fact>]
let ``task return-bang is not touched`` () =
    // task's return! also accepts Async<'T>; stripping could change the type
    assertNoSuggestion "module Test\nlet f (comp: System.Threading.Tasks.Task<int>) = task { return! comp }"

[<Fact>]
let ``task wrapping a constant becomes Task-FromResult`` () =
    assertSingleSuggestion "module Test\nopen System.Threading.Tasks\nlet f () = task { return 3 }" "Task.FromResult(3)"

[<Fact>]
let ``task wrapping an identifier becomes Task-FromResult`` () =
    assertSingleSuggestion "module Test\nopen System.Threading.Tasks\nlet f x = task { return x }" "Task.FromResult(x)"

[<Fact>]
let ``task wrapping without the open is not rewritten`` () =
    // Task.FromResult would not resolve
    assertNoSuggestion "module Test\nlet f x = task { return x }"

[<Fact>]
let ``task wrapping an expression that could throw is not rewritten`` () =
    // task { return e } yields a faulted task on throw; Task.FromResult e throws synchronously
    assertNoSuggestion "module Test\nopen System.Threading.Tasks\nlet f (x: int) = task { return x + 1 }"

[<Fact>]
let ``a plain closure owning a use collapses back — the CURE for older damage`` () =
    // FR0029 refuses to build this shape now, but prevention cannot reach a
    // change an older version already committed: this rule undoes it
    let source =
        "module Test\nlet f (v: int) =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail () =\n            use r = new System.IO.MemoryStream()\n            let a = v + 1\n            let b = a + 1\n            a + b + int r.Length\n        return runTail ()\n    }"

    match findIn source |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity) with
    | [ s ] ->
        Assert.Contains("use r = new System.IO.MemoryStream()", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.DoesNotContain("let runTail ()", patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected one thunk collapse, got %A" other

[<Fact>]
let ``the cure does not fight the prevention`` () =
    // the task-RETURNING variant is the shape FR0029 builds for a tail with
    // a `use`; collapsing that would oscillate, so it must be left alone
    Assert.Empty(
        findIn
            "module Test\nlet f (v: int) =\n    task {\n        do! System.Threading.Tasks.Task.Delay 1\n        let runTail () = task {\n            use r = new System.IO.MemoryStream()\n            let a = v + 1\n            let b = a + 1\n            return a + b + int r.Length\n        }\n        return! runTail ()\n    }"
        |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ThunkIdentity)
    )

[<Fact>]
let ``return-bang of a mutable identifier keeps its wrapper`` () =
    // the wrapper reads `current` each time the computation RUNS; stripped,
    // the value is read once, where the expression is evaluated
    assertNoSuggestion
        "module Test\nlet mutable current : Async<int> = async { return 1 }\nlet next () = async { return! current }"

    assertNoSuggestion
        "module Test\ntype Holder() =\n    let mutable current : Async<int> = async { return 1 }\n    member _.Next = async { return! current }\n    member _.Set v = current <- v"

    assertNoSuggestion
        "module Test\nlet f () =\n    let mutable current : Async<int> = async { return 1 }\n    let run = async { let! v = current in return v }\n    current <- async { return 2 }\n    run"

    // typed: a mutable declared outside the file reads the same way
    let source =
        "module Test\nmodule State =\n    let mutable current : Async<int> = async { return 1 }\nopen State\nlet next () = async { return! current }"

    let tree, sourceText, check = parseAndCheck source
    Assert.Empty(CeStrip.findWith (Some check) tree sourceText)
