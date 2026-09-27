module FSharp.Refactor.Tests.TupleParamsTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TupleParams.find tree sourceText checkResults

/// Apply all edits (bottom-up so earlier ranges stay valid) and verify the
/// patched source against the expectation and the typechecker.
let private assertSingleSuggestion (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
            |> List.fold (fun acc e -> applyEdit acc e.Range e.Replacement) source

        Assert.Equal(expectedPatched, patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``tupled private function and its calls are curried`` () =
    assertSingleSuggestion
        "let private add (a, b) = a + b\nlet total = add (1, 2)"
        "let private add a b = a + b\nlet total = add 1 2"

[<Fact>]
let ``annotated tuple elements keep their annotations`` () =
    assertSingleSuggestion
        (fsharp
            """
            let private describe (name: string, count: int) = sprintf "%s: %d" name count
            let d = describe ("x", 3)
            """)
        (fsharp
            """
            let private describe (name: string) (count: int) = sprintf "%s: %d" name count
            let d = describe "x" 3
            """)

[<Fact>]
let ``complex call arguments are parenthesized`` () =
    assertSingleSuggestion
        "let private add (a, b) = a + b\nlet f x = add (x + 1, x * 2)"
        "let private add a b = a + b\nlet f x = add (x + 1) (x * 2)"

[<Fact>]
let ``negative literal arguments are parenthesized`` () =
    assertSingleSuggestion
        "let private add (a, b) = a + b\nlet total = add (-1, 2)"
        "let private add a b = a + b\nlet total = add (-1) 2"

[<Fact>]
let ``call without space keeps valid syntax`` () =
    assertSingleSuggestion
        "let private add (a, b) = a + b\nlet total = add(1, 2)"
        "let private add a b = a + b\nlet total = add 1 2"

[<Fact>]
let ``a call nested inside another call's tuple suppresses the suggestion`` () =
    // the inner `(1, 2)` edit sits inside the outer call-tuple edit, so the
    // two range edits cannot apply together atomically
    assertNoSuggestion (
        fsharp
            """
            let private add (a, b) = a + b
            let total = add (add (1, 2), 3)
            """
    )

[<Fact>]
let ``recursive self-call is rewritten too`` () =
    assertSingleSuggestion
        (fsharp
            """
            let rec private count (n, acc) =
                if n = 0 then acc else count (n - 1, acc + 1)
            let c = count (10, 0)
            """)
        (fsharp
            """
            let rec private count n acc =
                if n = 0 then acc else count (n - 1) (acc + 1)
            let c = count 10 0
            """)

[<Fact>]
let ``three-element tuples work`` () =
    assertSingleSuggestion
        (fsharp
            """
            let private volume (x, y, z) = x * y * z
            let v = volume (2, 3, 4)
            """)
        (fsharp
            """
            let private volume x y z = x * y * z
            let v = volume 2 3 4
            """)

[<Fact>]
let ``function passed as a value is not rewritten`` () =
    assertNoSuggestion (
        fsharp
            """
            let private add (a, b) = a + b
            let sums (pairs: (int * int) list) = pairs |> List.map add
            """
    )

[<Fact>]
let ``tuple piped into the function is not rewritten`` () =
    assertNoSuggestion "let private add (a, b) = a + b\nlet total = (1, 2) |> add"

[<Fact>]
let ``call with a tuple-valued variable is not rewritten`` () =
    assertNoSuggestion (
        fsharp
            """
            let private add (a, b) = a + b
            let f (pair: int * int) = add pair
            """
    )

[<Fact>]
let ``non-private function is not rewritten`` () =
    // other files could call it
    assertNoSuggestion "let add (a, b) = a + b\nlet total = add (1, 2)"

[<Fact>]
let ``destructuring tuple pattern elements are not rewritten`` () =
    assertNoSuggestion "let private f ((a, b), c) = a + b + c\nlet r = f ((1, 2), 3)"

[<Fact>]
let ``definition without a space before the tuple keeps its name`` () =
    // review regression: `adda b` merged the name and first parameter
    assertSingleSuggestion
        "let private add(a, b) = a + b\nlet total = add(1, 2)"
        "let private add a b = a + b\nlet total = add 1 2"

[<Fact>]
let ``call with a projection continuation is not rewritten`` () =
    // review regression: `key 1 2.Length` loses the atomic grouping
    assertNoSuggestion (
        fsharp
            """
            let private key (a, b) = sprintf "%d-%d" a b
            let n = key(1, 2).Length
            """
    )

[<Fact>]
let ``an attributed function keeps its tuple`` () =
    // Feliz's [<ReactComponent>] derives the props object from the tuple;
    // what a plugin makes of the curried form cannot be checked here
    assertNoSuggestion (
        fsharp
            """
            type MarkAttribute() =
                inherit System.Attribute()
            [<Mark>]
            let private add (a, b) = a + b
            let total = add (1, 2)
            """
    )
