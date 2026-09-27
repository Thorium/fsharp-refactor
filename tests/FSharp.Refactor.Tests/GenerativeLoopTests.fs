module FSharp.Refactor.Tests.GenerativeLoopTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0141 GenerativeLoop ----

let private genLoopIn (source: string) =
    let tree, sourceText = parse source
    GenerativeLoop.find tree sourceText

[<Fact>]
let ``state carried forward through a flag loop is noted`` () =
    // the VisionInference shape: cache feeds the next round
    let source =
        fsharp
            """
            module Test
            let f (model: int) (limit: int) =
                let generated = ResizeArray<int>()
                let mutable cache = 0
                let mutable stopped = false
                while not stopped && generated.Count < limit do
                    let next = model + cache
                    cache <- next
                    if next = 0 then stopped <- true
                    else generated.Add next
                generated
            """

    match genLoopIn source with
    | [ s ] ->
        Assert.Equal("stopped", s.Flag)
        Assert.Equal<string list>([ "cache" ], s.Carried)
    | other -> failwithf "Expected exactly one note, got %A" other

[<Fact>]
let ``a search loop carrying only an index is left alone`` () =
    // already short-circuits, allocates nothing, and measured 12x faster
    // than Array.exists on an early hit — a pipeline would be a regression
    let source =
        fsharp
            """
            module Test
            let f (xs: int[]) =
                let mutable found = false
                let mutable i = 0
                while not found && i < xs.Length do
                    if xs.[i] > 2 then found <- true
                    i <- i + 1
                found
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``a decrementing index is still just an index`` () =
    let source =
        fsharp
            """
            module Test
            let f (xs: int[]) =
                let mutable found = false
                let mutable i = xs.Length - 1
                while not found && i >= 0 do
                    if xs.[i] > 2 then found <- true
                    i <- i - 1
                found
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``a mutable declared INSIDE the body is not carried`` () =
    let source =
        fsharp
            """
            module Test
            let f (n: int) =
                let mutable stopped = false
                let mutable i = 0
                while not stopped && i < n do
                    let mutable scratch = 0
                    scratch <- i * 2
                    if scratch > 10 then stopped <- true
                    i <- i + 1
                stopped
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``a loop whose flag is never raised is waiting on something else`` () =
    let source =
        fsharp
            """
            module Test
            let f (ready: bool) (n: int) =
                let mutable acc = 0
                let mutable i = 0
                while not ready && i < n do
                    acc <- acc + i
                    i <- i + 1
                acc
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``the tail after the flag is counted`` () =
    // two statements still run in the iteration that raised the flag
    let source =
        fsharp
            """
            module Test
            let f (n: int) =
                let acc = ResizeArray<int>()
                let mutable cache = 0
                let mutable stopped = false
                let mutable i = 0
                while not stopped && i < n do
                    let next = cache + i
                    if next > 10 then stopped <- true
                    cache <- next
                    i <- i + 1
                acc
            """

    match genLoopIn source with
    | [ s ] ->
        Assert.Equal(2, s.TailAfterFlag)
        Assert.Contains("cache", s.Carried)
    | other -> failwithf "Expected exactly one note, got %A" other

[<Fact>]
let ``a flag raised last has no tail to claim`` () =
    let source =
        fsharp
            """
            module Test
            let f (n: int) =
                let acc = ResizeArray<int>()
                let mutable cache = 0
                let mutable stopped = false
                while not stopped && acc.Count < n do
                    let next = cache + 1
                    cache <- next
                    if next > 10 then stopped <- true
                    else acc.Add next
                acc
            """

    match genLoopIn source with
    | [ s ] -> Assert.Equal(0, s.TailAfterFlag)
    | other -> failwithf "Expected exactly one note, got %A" other

[<Fact>]
let ``a loop inside a task CE is left alone - no tail calls there`` () =
    // FSharp.Azure.Quantum's polling loop carries this reason in a comment
    // above it: a task compiles to a state machine and recursive return!
    // grows the stack, so the advice would be wrong
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let f (n: int) =
                task {
                    let mutable cache = 0
                    let mutable finished = false
                    while not finished do
                        let next = cache + 1
                        cache <- next
                        if next > n then finished <- true
                    return cache
                }
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``a loop inside an async CE is left alone too`` () =
    // the recursive function would have to return Async<_>, so the rewrite
    // reaches the signature rather than the loop
    let source =
        fsharp
            """
            module Test
            let f (n: int) =
                async {
                    let mutable cache = 0
                    let mutable finished = false
                    while not finished do
                        let next = cache + 1
                        cache <- next
                        if next > n then finished <- true
                    return cache
                }
            """

    Assert.Empty(genLoopIn source)

[<Fact>]
let ``a loop inside a seq CE is ordinary code and still gets the advice`` () =
    // only the asynchronous builders are excluded
    let source =
        fsharp
            """
            module Test
            let f (n: int) =
                seq {
                    let mutable cache = 0
                    let mutable finished = false
                    while not finished do
                        let next = cache + 1
                        cache <- next
                        if next > n then finished <- true
                    yield cache
                }
            """

    match genLoopIn source with
    | [ s ] -> Assert.Equal("finished", s.Flag)
    | other -> failwithf "Expected exactly one note, got %A" other
