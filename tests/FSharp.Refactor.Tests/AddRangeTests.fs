module FSharp.Refactor.Tests.AddRangeTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private addRangeIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AddRange.find tree sourceText checkResults

let private assertAddRange (source: string) (expectedReplacement: string) =
    match addRangeIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one AddRange suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``plain element accumulation becomes AddRange`` () =
    assertAddRange
        (fsharp
            """
            let f (acc: ResizeArray<int>) (xs: int list) =
                for x in xs do
                    acc.Add x
            """)
        "acc.AddRange xs"

[<Fact>]
let ``a projected element keeps its loop`` () =
    // the Seq.map spelling allocates an enumerator and a closure, and
    // AddRange still enumerates item by item: no gain over the loop
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (xs: int list) =
                    for x in xs do
                        acc.Add(x * 2)
                """
        )
    )

[<Fact>]
let ``a projected tuple pattern keeps its loop too`` () =
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (ps: (int * int) list) =
                    for (a, b) in ps do
                        acc.Add(a + b)
                """
        )
    )

[<Fact>]
let ``property receiver keeps its path`` () =
    assertAddRange
        (fsharp
            """
            type Holder() =
                member val Items = ResizeArray<int>() with get
            let f (h: Holder) (xs: int list) =
                for x in xs do
                    h.Items.Add x
            """)
        "h.Items.AddRange xs"

[<Fact>]
let ``extra statements in the body are left alone`` () =
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (xs: int list) =
                    for x in xs do
                        printfn "%d" x
                        acc.Add x
                """
        )
    )

[<Fact>]
let ``HashSet Add is a different beast`` () =
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: System.Collections.Generic.HashSet<int>) (xs: int list) =
                    for x in xs do
                        acc.Add x |> ignore
                """
        )
    )

[<Fact>]
let ``loop over an expression source is parenthesized`` () =
    assertAddRange
        (fsharp
            """
            let f (acc: ResizeArray<int>) (xs: int list) =
                for x in List.rev xs do
                    acc.Add x
            """)
        "acc.AddRange (List.rev xs)"

[<Fact>]
let ``an element reading a mutable local keeps its loop`` () =
    // the element would move into a fabricated Seq.map lambda, where
    // capturing a mutable local was FS0407 before F# 10
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    let mutable offset = 1
                    for x in xs do
                        acc.Add(x + offset)
                    acc
                """
        )
    )

[<Fact>]
let ``a range source becomes an array literal`` () =
    // `acc.AddRange (a .. b)` does not parse (FS0751 indexer syntax), and
    // `seq { a .. b }` parses but measures 4-6x SLOWER than the loop. An
    // array literal is ICollection, so AddRange sizes once and copies:
    // measured 1.7x faster than the loop, allocating less.
    assertAddRange
        (fsharp
            """
            let f (acc: ResizeArray<int>) (a: int) (b: int) =
                for x in a + 1 .. b do
                    acc.Add x
            """)
        "acc.AddRange [| a + 1 .. b |]"

[<Fact>]
let ``a PROJECTED range source is left alone`` () =
    // measured: the Seq.map form is 3-8x slower than the loop, and the
    // Array.map form only matches it while allocating 44% more
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (a: int) (b: int) =
                    for x in a .. b do
                        acc.Add(x * 2)
                """
        )
    )

[<Fact>]
let ``a STEPPED range source is handled or left alone, never mis-emitted`` () =
    // `for x in a .. 2 .. b` — whatever the rule decides, the result must
    // parse and typecheck
    match
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (a: int) (b: int) =
                    for x in a .. 2 .. b do
                        acc.Add x
                """
        )
    with
    | [] -> ()
    | [ s ] ->
        let patched =
            applyEdit
                (fsharp
                    """
                    let f (acc: ResizeArray<int>) (a: int) (b: int) =
                        for x in a .. 2 .. b do
                            acc.Add x
                    """)
                s.Range
                s.ReplacementText

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a receiver chosen per element keeps its loop`` () =
    // Nu's Twenty 48: `columns[tile.Position.X].Add tile` picks a list PER
    // element; `columns[tile.Position.X].AddRange tiles` has no `tile`
    let tree, sourceText, checkResults =
        parseAndCheck (
            fsharp
                """
                module Test
                type Tile = { X: int }
                let f (tiles: Tile list) =
                    let columns = List.init 4 (fun _ -> ResizeArray<Tile>())
                    for tile in tiles do columns[tile.X].Add tile
                    columns
                """
        )

    Assert.Empty(AddRange.find tree sourceText checkResults)

// ---- only the loop variable itself collapses (suave) ----

[<Fact>]
let ``a call result per element keeps its loop`` () =
    // suave: `for f in xs do acc.Add(f())` came out as
    // `acc.AddRange((List.rev xs) |> Seq.map (fun f -> f()))` — no gain,
    // and doubly parenthesised
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (acc: ResizeArray<int>) (xs: (unit -> int) list) =
                    for f in List.rev xs do
                        acc.Add(f())
                """
        )
    )

[<Fact>]
let ``a parenthesised loop variable still collapses`` () =
    assertAddRange
        (fsharp
            """
            let f (acc: ResizeArray<int>) (xs: int list) =
                for x in xs do
                    acc.Add(x)
            """)
        "acc.AddRange xs"

[<Fact>]
let ``an already parenthesised source is not wrapped again`` () =
    assertAddRange
        (fsharp
            """
            let f (acc: ResizeArray<int>) (xs: int list) =
                for x in (List.rev xs) do
                    acc.Add x
            """)
        "acc.AddRange (List.rev xs)"

[<Fact>]
let ``a source whose element type differs from the list's is left alone`` () =
    // `acc.Add n` upcasts each string to obj; `acc.AddRange names` wants a
    // seq<obj> and a string list is not one (FS0001)
    Assert.Empty(
        addRangeIn (
            fsharp
                """
                let f (names: string list) =
                    let acc = ResizeArray<obj>()
                    for n in names do
                        acc.Add n
                    acc
                """
        )
    )
