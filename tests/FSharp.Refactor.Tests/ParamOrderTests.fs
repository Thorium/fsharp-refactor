module FSharp.Refactor.Tests.ParamOrderTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private paramOrderIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ParamOrder.find tree sourceText checkResults

/// Apply a suggestion's edits bottom-up and verify the patched text.
let private assertParamOrder (source: string) (expectedPatched: string) =
    match paramOrderIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one param-order suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``eta-blocking lambda swaps the definition and collapses the lambda`` () =
    assertParamOrder
        (fsharp
            """
            let private scale (x: float) (k: int) = x * float k
            let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
            """)
        (fsharp
            """
            let private scale (k: int) (x: float) = x * float k
            let doubled (xs: float list) = xs |> List.map (scale 2)
            """)

[<Fact>]
let ``direct call sites are swapped along with the definition`` () =
    assertParamOrder
        (fsharp
            """
            let private scale x (k: int) = x * float k
            let a = scale 3.0 2
            let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
            """)
        (fsharp
            """
            let private scale (k: int) x = x * float k
            let a = scale 2 3.0
            let doubled (xs: float list) = xs |> List.map (scale 2)
            """)

[<Fact>]
let ``captured identifier argument is allowed`` () =
    assertParamOrder
        (fsharp
            """
            let private scale (x: float) (k: int) = x * float k
            let doubled (factor: int) (xs: float list) = xs |> List.map (fun x -> scale x factor)
            """)
        (fsharp
            """
            let private scale (k: int) (x: float) = x * float k
            let doubled (factor: int) (xs: float list) = xs |> List.map (scale factor)
            """)

[<Fact>]
let ``no eta-blocking lambda means no suggestion`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let a = scale 3.0 2
                """
        )
    )

[<Fact>]
let ``partial application suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let triple = scale 3.0
                let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
                """
        )
    )

[<Fact>]
let ``use as a value suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let folded (xs: int list) = List.fold scale 1.0 xs
                let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
                """
        )
    )

[<Fact>]
let ``impure captured argument is not an eta-blocking site`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let doubled (xs: float list) = xs |> List.map (fun x -> scale x (System.Random.Shared.Next()))
                """
        )
    )

[<Fact>]
let ``public function is left alone`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let scale (x: float) (k: int) = x * float k
                let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
                """
        )
    )

[<Fact>]
let ``pipe into the function suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let b (n: int) = n |> scale 4.0
                let doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)
                """
        )
    )

[<Fact>]
let ``a captured mutable is read per call and keeps its lambda`` () =
    // `fun x -> scale x factor` reads `factor` on every call; `scale factor`
    // reads it once, where the partial application is built
    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                let private scale (x: float) (k: int) = x * float k
                let mutable factor = 2
                let doubled (xs: float list) = xs |> Seq.map (fun x -> scale x factor)
                """
        )
    )

    Assert.Empty(
        paramOrderIn (
            fsharp
                """
                module M
                let private scale (x: float) (k: int) = x * float k
                type Scaler() =
                    let mutable factor = 2
                    member _.Set v = factor <- v
                    member _.Apply(xs: float list) = xs |> Seq.map (fun x -> scale x factor)
                """
        )
    )
