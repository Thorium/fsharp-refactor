module FSharp.Refactor.Tests.MapFusionTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    MapFusion.find tree sourceText

/// Expect one suggestion; verify the fully patched source text and that it
/// still parses.
let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``consecutive Array maps over fst fuse into a composition`` () =
    assertPatched
        "module Test\nlet f g xs = xs |> Array.map fst |> Array.map g"
        "module Test\nlet f g xs = xs |> Array.map (fst >> g)"

[<Fact>]
let ``the parenthesized juxtaposed spelling fuses the same way`` () =
    // the shape from the field: xs |> Array.map(fst) |> Array.map(fun x -> ...)
    assertPatched
        "module Test\nlet f xs = xs |> Seq.toArray |> Array.map(fst) |> Array.map(fun x -> x + 1)"
        "module Test\nlet f xs = xs |> Seq.toArray |> Array.map (fst >> fun x -> x + 1)"

[<Fact>]
let ``snd fuses on List`` () =
    assertPatched
        "module Test\nlet f g xs = xs |> List.map snd |> List.map g"
        "module Test\nlet f g xs = xs |> List.map (snd >> g)"

[<Fact>]
let ``a leading map id disappears entirely`` () =
    assertPatched "module Test\nlet f g xs = xs |> Seq.map id |> Seq.map g" "module Test\nlet f g xs = xs |> Seq.map g"

[<Fact>]
let ``multi-line pipeline stages fuse onto one line`` () =
    assertPatched
        "module Test\nlet f g xs =\n    xs\n    |> Array.map fst\n    |> Array.map g"
        "module Test\nlet f g xs =\n    xs\n    |> Array.map (fst >> g)"

[<Fact>]
let ``an arbitrary first mapper is not fused — interleaving would reorder its effects`` () =
    assertNoSuggestion "module Test\nlet f g h xs = xs |> Array.map h |> Array.map g"

[<Fact>]
let ``maps of different modules never fuse`` () =
    // Seq.map fst |> Array.map g does not even typecheck; the boundary
    // shape Seq.toArray in between belongs to FR0004
    assertNoSuggestion "module Test\nlet f g xs = xs |> Seq.map fst |> List.map g"

[<Fact>]
let ``a second stage spanning lines is left alone`` () =
    assertNoSuggestion "module Test\nlet f xs = xs |> Array.map fst |> Array.map (fun x ->\n    x + 1)"

[<Fact>]
let ``a composed second mapper folds into one chain`` () =
    assertPatched
        "module Test\nlet f g h xs = xs |> List.map fst |> List.map (g >> h)"
        "module Test\nlet f g h xs = xs |> List.map (fst >> g >> h)"

[<Fact>]
let ``a backward composition keeps its parentheses`` () =
    // `fst >> f << g` is `(fst >> f) << g`: a different function
    assertPatched
        "module Test\nlet f g h xs = xs |> List.map fst |> List.map (g << h)"
        "module Test\nlet f g h xs = xs |> List.map (fst >> (g << h))"
