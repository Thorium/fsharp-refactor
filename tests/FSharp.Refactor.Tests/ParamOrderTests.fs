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
        "let private scale (x: float) (k: int) = x * float k\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
        "let private scale (k: int) (x: float) = x * float k\nlet doubled (xs: float list) = xs |> List.map (scale 2)"

[<Fact>]
let ``direct call sites are swapped along with the definition`` () =
    assertParamOrder
        "let private scale x (k: int) = x * float k\nlet a = scale 3.0 2\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
        "let private scale (k: int) x = x * float k\nlet a = scale 2 3.0\nlet doubled (xs: float list) = xs |> List.map (scale 2)"

[<Fact>]
let ``captured identifier argument is allowed`` () =
    assertParamOrder
        "let private scale (x: float) (k: int) = x * float k\nlet doubled (factor: int) (xs: float list) = xs |> List.map (fun x -> scale x factor)"
        "let private scale (k: int) (x: float) = x * float k\nlet doubled (factor: int) (xs: float list) = xs |> List.map (scale factor)"

[<Fact>]
let ``no eta-blocking lambda means no suggestion`` () =
    Assert.Empty(paramOrderIn "let private scale (x: float) (k: int) = x * float k\nlet a = scale 3.0 2")

[<Fact>]
let ``partial application suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn
            "let private scale (x: float) (k: int) = x * float k\nlet triple = scale 3.0\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
    )

[<Fact>]
let ``use as a value suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn
            "let private scale (x: float) (k: int) = x * float k\nlet folded (xs: int list) = List.fold scale 1.0 xs\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
    )

[<Fact>]
let ``impure captured argument is not an eta-blocking site`` () =
    Assert.Empty(
        paramOrderIn
            "let private scale (x: float) (k: int) = x * float k\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x (System.Random.Shared.Next()))"
    )

[<Fact>]
let ``public function is left alone`` () =
    Assert.Empty(
        paramOrderIn
            "let scale (x: float) (k: int) = x * float k\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
    )

[<Fact>]
let ``pipe into the function suppresses the suggestion`` () =
    Assert.Empty(
        paramOrderIn
            "let private scale (x: float) (k: int) = x * float k\nlet b (n: float) = n |> scale 4\nlet doubled (xs: float list) = xs |> List.map (fun x -> scale x 2)"
    )
