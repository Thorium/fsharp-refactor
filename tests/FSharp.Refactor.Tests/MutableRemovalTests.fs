module FSharp.Refactor.Tests.MutableRemovalTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MutableRemoval.find tree sourceText checkResults

let private assertSingleSuggestion (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range ""
        Assert.Equal(expectedPatched, patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``never-assigned mutable int is flagged`` () =
    assertSingleSuggestion
        (fsharp
            """
            let f () =
                let mutable x = 0
                x + 1
            """)
        (fsharp
            """
            let f () =
                let x = 0
                x + 1
            """)

[<Fact>]
let ``never-assigned mutable string is flagged`` () =
    assertSingleSuggestion
        (fsharp
            """
            let f (s: string) =
                let mutable name = s
                name.Length
            """)
        (fsharp
            """
            let f (s: string) =
                let name = s
                name.Length
            """)

[<Fact>]
let ``whitelisted struct is flagged`` () =
    assertSingleSuggestion
        (fsharp
            """
            let f () =
                let mutable g = System.Guid.NewGuid()
                g.ToString()
            """)
        (fsharp
            """
            let f () =
                let g = System.Guid.NewGuid()
                g.ToString()
            """)

[<Fact>]
let ``assigned binding is not flagged`` () =
    assertNoSuggestion (
        fsharp
            """
            let f () =
                let mutable x = 0
                x <- 1
                x
            """
    )

[<Fact>]
let ``assignment inside a closure is not flagged`` () =
    assertNoSuggestion (
        fsharp
            """
            let f () =
                let mutable x = 0
                let bump () = x <- x + 1
                bump ()
                x
            """
    )

[<Fact>]
let ``address-of use is not flagged`` () =
    assertNoSuggestion (
        fsharp
            """
            let f () =
                let mutable x = 0
                System.Threading.Interlocked.Increment(&x) |> ignore
                x
            """
    )

[<Fact>]
let ``property assignment through the binding is not flagged`` () =
    assertNoSuggestion (
        fsharp
            """
            type C() = member val P = 0 with get, set
            let f () =
                let mutable c = C()
                c.P <- 1
                c
            """
    )

[<Fact>]
let ``non-whitelisted struct is not flagged`` () =
    // removing mutable would introduce defensive copies for member calls
    assertNoSuggestion (
        fsharp
            """
            [<Struct>] type S = { A: int }
            let f () =
                let mutable s = { A = 1 }
                s.A
            """
    )

[<Fact>]
let ``module-level mutable is not flagged`` () =
    assertNoSuggestion (
        fsharp
            """
            module M
            let mutable counter = 0
            let read () = counter
            """
    )
