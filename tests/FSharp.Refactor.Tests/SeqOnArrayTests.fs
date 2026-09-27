module FSharp.Refactor.Tests.SeqOnArrayTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0139 SeqOnArray ----

let private seqOnArrayIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SeqOnArray.find tree sourceText checkResults

let private assertRewrite (source: string) (expectedFunction: string) =
    match seqOnArrayIn source with
    | [ s ] ->
        Assert.Equal(expectedFunction, s.FunctionName)
        let patched = applyEdit source s.Range "Array"
        Assert.Contains("Array." + expectedFunction, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``a piped Seq call on an array becomes Array`` () =
    assertRewrite "module Test\nlet f (xs: int[]) = xs |> Seq.length" "length"

[<Fact>]
let ``a direct Seq call on an array becomes Array`` () =
    assertRewrite
        (fsharp
            """
            module Test
            let f (xs: string[]) = Seq.forall (fun x -> x <> "") xs
            """)
        "forall"

[<Fact>]
let ``a curried predicate call still resolves the array`` () =
    assertRewrite
        (fsharp
            """
            module Test
            let f (xs: int[]) = xs |> Seq.exists (fun x -> x > 2)
            """)
        "exists"

[<Fact>]
let ``a record field typed as an array is rewritten too`` () =
    assertRewrite
        (fsharp
            """
            module Test
            type S = { Buffer: int[] }
            let f (s: S) = s.Buffer |> Seq.isEmpty
            """)
        "isEmpty"

[<Fact>]
let ``a LIST is left alone — Seq there can be deliberate`` () =
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: int list) = xs |> Seq.length")

[<Fact>]
let ``a lazy seq is left alone`` () =
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: int seq) = xs |> Seq.length")

[<Fact>]
let ``numeric aggregates are left to FR0041 and its LINQ advice`` () =
    // .NET vectorises the LINQ aggregates over span-backed sources; this
    // rule must not argue with FR0041 over the same line
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: int[]) = xs |> Seq.sum")
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: int[]) = xs |> Seq.max")
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: float[]) = xs |> Seq.average")

[<Fact>]
let ``item keeps its Seq spelling — the exception types differ`` () =
    // Array.item throws IndexOutOfRangeException, Seq.item ArgumentException
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: int[]) = xs |> Seq.item 2")

[<Fact>]
let ``a collection-returning function would change the type`` () =
    // Seq.map returns seq<'b>, Array.map returns 'b[]
    Assert.Empty(
        seqOnArrayIn (
            fsharp
                """
                module Test
                let f (xs: int[]) = xs |> Seq.map (fun x -> x + 1)
                """
        )
    )

[<Fact>]
let ``contains on an int array defaults to LINQ, with Array offered beside it`` () =
    // case (b): two better answers, so the CLI takes the idiomatic one and
    // an editor offers the vectorised one as a second action
    match seqOnArrayIn "module Test\nlet f (xs: int[]) = xs |> Seq.contains 3" with
    | [ s ] ->
        Assert.Equal("contains", s.FunctionName)

        match s.LinqSpelling with
        | Some(_, linq) -> Assert.Equal("System.Linq.Enumerable.Contains(xs, 3)", linq)
        | None -> failwith "expected the LINQ alternative"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``an open System.Linq shortens the alternative`` () =
    match
        seqOnArrayIn (
            fsharp
                """
                module Test
                open System.Linq
                let f (xs: int[]) = xs |> Seq.contains 3
                """
        )
    with
    | [ s ] ->
        match s.LinqSpelling with
        | Some(_, linq) -> Assert.Equal("Enumerable.Contains(xs, 3)", linq)
        | None -> failwith "expected the LINQ alternative"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``contains on a STRING array gets no rule at all`` () =
    // case (c): Seq.contains 938ns actually beats Array.contains 1024ns on
    // .NET 10, and LINQ is worse still — no clear win, so no rule
    Assert.Empty(seqOnArrayIn "module Test\nlet f (xs: string[]) = xs |> Seq.contains \"a\"")

[<Fact>]
let ``iter is left alone — measured a wash on .NET 10`` () =
    // 236.6 against 235.4 ns: half a percent is not a refactoring
    Assert.Empty(
        seqOnArrayIn (
            fsharp
                """
                module Test
                let f (xs: int[]) = xs |> Seq.iter (printfn "%d")
                """
        )
    )

[<Fact>]
let ``a user-defined Seq module is not the FSharp.Core one`` () =
    // swapping this to Array would name a function nobody wrote
    Assert.Empty(
        seqOnArrayIn (
            fsharp
                """
                module Test
                module Seq =
                    let describe (_: int[]) = 1
                let f (xs: int[]) = Seq.describe xs
                """
        )
    )
