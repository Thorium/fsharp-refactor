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
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one AddRange suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``plain element accumulation becomes AddRange`` () =
    assertAddRange
        "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in xs do\n        acc.Add x"
        "acc.AddRange xs"

[<Fact>]
let ``a projected element keeps its loop`` () =
    // the Seq.map spelling allocates an enumerator and a closure, and
    // AddRange still enumerates item by item: no gain over the loop
    Assert.Empty(
        addRangeIn "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in xs do\n        acc.Add(x * 2)"
    )

[<Fact>]
let ``a projected tuple pattern keeps its loop too`` () =
    Assert.Empty(
        addRangeIn
            "let f (acc: ResizeArray<int>) (ps: (int * int) list) =\n    for (a, b) in ps do\n        acc.Add(a + b)"
    )

[<Fact>]
let ``property receiver keeps its path`` () =
    assertAddRange
        "type Holder() =\n    member val Items = ResizeArray<int>() with get\nlet f (h: Holder) (xs: int list) =\n    for x in xs do\n        h.Items.Add x"
        "h.Items.AddRange xs"

[<Fact>]
let ``extra statements in the body are left alone`` () =
    Assert.Empty(
        addRangeIn
            "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in xs do\n        printfn \"%d\" x\n        acc.Add x"
    )

[<Fact>]
let ``HashSet Add is a different beast`` () =
    Assert.Empty(
        addRangeIn
            "let f (acc: System.Collections.Generic.HashSet<int>) (xs: int list) =\n    for x in xs do\n        acc.Add x |> ignore"
    )

[<Fact>]
let ``loop over an expression source is parenthesized`` () =
    assertAddRange
        "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in List.rev xs do\n        acc.Add x"
        "acc.AddRange (List.rev xs)"

[<Fact>]
let ``an element reading a mutable local keeps its loop`` () =
    // the element would move into a fabricated Seq.map lambda, where
    // capturing a mutable local was FS0407 before F# 10
    Assert.Empty(
        addRangeIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    let mutable offset = 1\n    for x in xs do\n        acc.Add(x + offset)\n    acc"
    )

[<Fact>]
let ``a range source becomes an array literal`` () =
    // `acc.AddRange (a .. b)` does not parse (FS0751 indexer syntax), and
    // `seq { a .. b }` parses but measures 4-6x SLOWER than the loop. An
    // array literal is ICollection, so AddRange sizes once and copies:
    // measured 1.7x faster than the loop, allocating less.
    assertAddRange
        "let f (acc: ResizeArray<int>) (a: int) (b: int) =\n    for x in a + 1 .. b do\n        acc.Add x"
        "acc.AddRange [| a + 1 .. b |]"

[<Fact>]
let ``a PROJECTED range source is left alone`` () =
    // measured: the Seq.map form is 3-8x slower than the loop, and the
    // Array.map form only matches it while allocating 44% more
    Assert.Empty(
        addRangeIn "let f (acc: ResizeArray<int>) (a: int) (b: int) =\n    for x in a .. b do\n        acc.Add(x * 2)"
    )

[<Fact>]
let ``a STEPPED range source is handled or left alone, never mis-emitted`` () =
    // `for x in a .. 2 .. b` — whatever the rule decides, the result must
    // parse and typecheck
    match
        addRangeIn "let f (acc: ResizeArray<int>) (a: int) (b: int) =\n    for x in a .. 2 .. b do\n        acc.Add x"
    with
    | [] -> ()
    | [ s ] ->
        let patched =
            applyEdit
                "let f (acc: ResizeArray<int>) (a: int) (b: int) =\n    for x in a .. 2 .. b do\n        acc.Add x"
                s.Range
                s.ReplacementText

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a receiver chosen per element keeps its loop`` () =
    // Nu's Twenty 48: `columns[tile.Position.X].Add tile` picks a list PER
    // element; `columns[tile.Position.X].AddRange tiles` has no `tile`
    let tree, sourceText, checkResults =
        parseAndCheck
            "module Test\ntype Tile = { X: int }\nlet f (tiles: Tile list) =\n    let columns = List.init 4 (fun _ -> ResizeArray<Tile>())\n    for tile in tiles do columns[tile.X].Add tile\n    columns"

    Assert.Empty(AddRange.find tree sourceText checkResults)

// ---- only the loop variable itself collapses (suave) ----

[<Fact>]
let ``a call result per element keeps its loop`` () =
    // suave: `for f in xs do acc.Add(f())` came out as
    // `acc.AddRange((List.rev xs) |> Seq.map (fun f -> f()))` — no gain,
    // and doubly parenthesised
    Assert.Empty(
        addRangeIn
            "let f (acc: ResizeArray<int>) (xs: (unit -> int) list) =\n    for f in List.rev xs do\n        acc.Add(f())"
    )

[<Fact>]
let ``a parenthesised loop variable still collapses`` () =
    assertAddRange
        "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in xs do\n        acc.Add(x)"
        "acc.AddRange xs"

[<Fact>]
let ``an already parenthesised source is not wrapped again`` () =
    assertAddRange
        "let f (acc: ResizeArray<int>) (xs: int list) =\n    for x in (List.rev xs) do\n        acc.Add x"
        "acc.AddRange (List.rev xs)"
