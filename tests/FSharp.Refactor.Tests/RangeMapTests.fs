/// FR0173: a range built only to be mapped over is `init`.
module FSharp.Refactor.Tests.RangeMapTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// Enough declarations for the cases to typecheck on their own.
let private header =
    "let f (i: int) = i * 2\nlet xs = [| 1; 2; 3 |]\nlet dimension = 8\n"

let private found (body: string) =
    let tree, source, check = parseAndCheck (header + body)
    RangeMap.find tree source check

let private assertRewrites (body: string) (expected: string) (expectedProven: bool) =
    match found body with
    | [ s ] ->
        Assert.Equal(expected, s.ReplacementText)
        Assert.Equal(expectedProven, s.CountProven)
        // the standing rule: the produced text must be right on its own,
        // never rescued by a compile check afterwards
        let patched = applyEdit (header + body) s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a range mapped over becomes Array.init`` () =
    assertRewrites
        "let r = [| 0 .. dimension - 1 |] |> Array.map (fun i -> f i)"
        "Array.init dimension (fun i -> f i)"
        false

[<Fact>]
let ``a Length count is proven non-negative, so a sweep may apply it`` () =
    assertRewrites
        "let r = [| 0 .. xs.Length - 1 |] |> Array.map (fun i -> f i)"
        "Array.init xs.Length (fun i -> f i)"
        true

[<Fact>]
let ``a literal upper bound folds to the count`` () =
    // `0 .. 9` is ten elements, not nine
    assertRewrites "let r = [| 0 .. 9 |] |> Array.map (fun i -> f i)" "Array.init 10 (fun i -> f i)" true

[<Fact>]
let ``the direct application is the same rewrite`` () =
    assertRewrites
        "let r = Array.map (fun i -> f i) [| 0 .. dimension - 1 |]"
        "Array.init dimension (fun i -> f i)"
        false

[<Fact>]
let ``a list range becomes List.init`` () =
    assertRewrites
        "let r = [ 0 .. dimension - 1 ] |> List.map (fun i -> f i)"
        "List.init dimension (fun i -> f i)"
        false

[<Fact>]
let ``Seq.map over a range becomes Seq.init`` () =
    assertRewrites
        "let r = [| 0 .. dimension - 1 |] |> Seq.map (fun i -> f i)"
        "Seq.init dimension (fun i -> f i)"
        false

[<Fact>]
let ``a named function carries over unchanged`` () =
    assertRewrites "let r = [| 0 .. dimension - 1 |] |> Array.map f" "Array.init dimension f" false

[<Fact>]
let ``a compound count keeps its own parentheses`` () =
    // the count becomes an ARGUMENT: `Array.init n * 2 f` would parse as
    // `(Array.init n) * (2 f)`
    assertRewrites
        "let r = [| 0 .. dimension * 2 - 1 |] |> Array.map (fun i -> f i)"
        "Array.init (dimension * 2) (fun i -> f i)"
        false

[<Fact>]
let ``a call as the count keeps its parentheses too`` () =
    assertRewrites
        "let g (a: int) (b: int) = a + b\nlet r = [| 0 .. g 2 3 - 1 |] |> Array.map (fun i -> f i)"
        "Array.init (g 2 3) (fun i -> f i)"
        false

[<Fact>]
let ``only the framework's Count proves a non-negative count`` () =
    // a property somebody wrote can answer anything, so its NAME is no
    // proof - the sweep must not apply this one
    let source =
        "type T() =\n    member _.Count = -1\n\nlet t = T()\nlet r = [| 0 .. t.Count - 1 |] |> Array.map (fun i -> i * 2)\n"

    let tree, text, check = parseAndCheck source

    match RangeMap.find tree text check with
    | [ s ] -> Assert.False(s.CountProven, "a user-declared Count must not count as proof")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a shadowing Array-length is not a proof either`` () =
    let source =
        "module Array =\n    let length (_: int) = -1\n\nlet r = [| 0 .. Array.length 3 - 1 |] |> Array.map (fun i -> i * 2)\n"

    let tree, text, check = parseAndCheck source

    match RangeMap.find tree text check with
    | [ s ] -> Assert.False(s.CountProven, "a shadowing Array.length must not count as proof")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a compiler directive inside the expression stands it down`` () =
    Assert.Empty(
        found
            "let r =\n    [| 0 .. dimension - 1 |]\n#if DEBUG\n    |> Array.map (fun i -> f i)\n#else\n    |> Array.map (fun i -> f i + 1)\n#endif"
    )

[<Fact>]
let ``a range that does not start at zero stays`` () =
    // the function would have to be shifted; this rule does not invent that
    Assert.Empty(found "let r = [| 1 .. dimension |] |> Array.map (fun i -> f i)")

[<Fact>]
let ``a stepped range stays`` () =
    Assert.Empty(found "let r = [| 0 .. 2 .. dimension |] |> Array.map (fun i -> f i)")

[<Fact>]
let ``a map over a real collection stays`` () =
    Assert.Empty(found "let r = xs |> Array.map (fun i -> f i)")

[<Fact>]
let ``a function other than map stays`` () =
    Assert.Empty(found "let r = [| 0 .. dimension - 1 |] |> Array.filter (fun i -> i > 0)")

[<Fact>]
let ``a shadowing Array module stays`` () =
    // the project's own `Array.map` has no `init` to rewrite to
    let source =
        "module Array =\n    let map g (xs: int[]) = Array.map g xs\n\nlet dimension = 8\nlet r = [| 0 .. dimension - 1 |] |> Array.map (fun i -> i * 2)\n"

    let tree, text, check = parseAndCheck source
    Assert.Empty(RangeMap.find tree text check)

[<Fact>]
let ``a multi-line mapper stays, since its text is spliced`` () =
    Assert.Empty(
        found "let r =\n    [| 0 .. dimension - 1 |]\n    |> Array.map (fun i ->\n        let d = f i\n        d + 1)"
    )

[<Fact>]
let ``the rewrite keeps what the program does`` () =
    // `init` applies the function for 0, 1, ... n-1 in that order, which is
    // the order the map walked the range in
    let before = [| 0 .. 5 - 1 |] |> Array.map (fun i -> i * 3)
    let after = Array.init 5 (fun i -> i * 3)
    Assert.Equal<int[]>(before, after)

[<Fact>]
let ``a negative count is why the sweep waits for a proof`` () =
    // the premise of CountProven: the two shapes genuinely differ there
    let n = -1
    Assert.Empty([| 0 .. n - 1 |] |> Array.map id)

    Assert.Throws<System.ArgumentException>(fun () -> Array.init n id |> ignore)
    |> ignore
