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
        "Array.init (FSharp.Core.Operators.max 0 dimension) (fun i -> f i)"
        false

[<Fact>]
let ``the clamp is FSharp.Core's max whatever the project calls max`` () =
    // a `max` of the project's own - here one that answers its first
    // argument, so a bare `max 0 n` would be 0 and the array empty - binds
    // the bare name, and a module named Operators defining one takes
    // `Operators.max`; the full name is FSharp.Core's
    let body =
        "let max (a: int) (_: int) = a\nmodule Operators =\n    let max (_: int) (b: int) = b\nlet r = [| 0 .. dimension - 1 |] |> Array.map (fun i -> f i)"

    assertRewrites body "Array.init (FSharp.Core.Operators.max 0 dimension) (fun i -> f i)" false

    // the name binds to FSharp.Core's, not to either helper
    match found body with
    | [ s ] ->
        let patched = applyEdit (header + body) s.Range s.ReplacementText
        let _, patchedText, patchedCheck = parseAndCheck patched
        let line = patched.Split('\n').Length
        let lineText = patchedText.GetLineString(line - 1)
        let column = lineText.IndexOf "max 0" + "max".Length

        match patchedCheck.GetSymbolUseAtLocation(line, column, lineText, [ "FSharp"; "Core"; "Operators"; "max" ]) with
        | Some u -> Assert.StartsWith("Microsoft.FSharp.Core.Operators", u.Symbol.FullName)
        | None -> failwith "max did not resolve"
    | other -> failwithf "Expected exactly one suggestion, got %A" other

    Assert.Equal(8, Array.length (Array.init (FSharp.Core.Operators.max 0 8) id))

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
        "Array.init (FSharp.Core.Operators.max 0 dimension) (fun i -> f i)"
        false

[<Fact>]
let ``a list range becomes List.init`` () =
    assertRewrites
        "let r = [ 0 .. dimension - 1 ] |> List.map (fun i -> f i)"
        "List.init (FSharp.Core.Operators.max 0 dimension) (fun i -> f i)"
        false

[<Fact>]
let ``Seq.map over a range becomes Seq.init`` () =
    assertRewrites
        "let r = [| 0 .. dimension - 1 |] |> Seq.map (fun i -> f i)"
        "Seq.init (FSharp.Core.Operators.max 0 dimension) (fun i -> f i)"
        false

[<Fact>]
let ``a named function carries over unchanged`` () =
    assertRewrites
        "let r = [| 0 .. dimension - 1 |] |> Array.map f"
        "Array.init (FSharp.Core.Operators.max 0 dimension) f"
        false

[<Fact>]
let ``an inclusive upper bound counts one more`` () =
    // `[ 0 .. n ]` holds n + 1 elements; a negative n (n < -1) is clamped empty
    assertRewrites
        "let r = [ 0 .. dimension ] |> List.map (fun i -> f i)"
        "List.init (FSharp.Core.Operators.max 0 (dimension + 1)) (fun i -> f i)"
        false

    assertRewrites
        "let r = [| 0 .. xs.Length |] |> Array.map (fun i -> f i)"
        "Array.init (xs.Length + 1) (fun i -> f i)"
        true

    let triple (i: int) = i * 3
    Assert.Equal<int list>([ 0 .. -3 ] |> List.map triple, List.init (max 0 (-3 + 1)) triple)
    Assert.Equal<int list>([ 0..4 ] |> List.map triple, List.init (max 0 (4 + 1)) triple)

[<Fact>]
let ``a compound count keeps its own parentheses`` () =
    // the count becomes an ARGUMENT: `Array.init n * 2 f` would parse as
    // `(Array.init n) * (2 f)`
    assertRewrites
        "let r = [| 0 .. dimension * 2 - 1 |] |> Array.map (fun i -> f i)"
        "Array.init (FSharp.Core.Operators.max 0 (dimension * 2)) (fun i -> f i)"
        false

[<Fact>]
let ``a call as the count keeps its parentheses too`` () =
    assertRewrites
        "let g (a: int) (b: int) = a + b\nlet r = [| 0 .. g 2 3 - 1 |] |> Array.map (fun i -> f i)"
        "Array.init (FSharp.Core.Operators.max 0 (g 2 3)) (fun i -> f i)"
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
let ``a multi-line mapper under the range moves with its lines into Array.init`` () =
    // FSharp.Azure.Quantum's AmplitudeAmplification: a 2^n amplitude array
    // built by mapping over a 2^n array of ints
    assertRewrites
        "let r =\n    [| 0 .. dimension - 1 |]\n    |> Array.map (fun i ->\n        let d = f i\n        d + 1)"
        "Array.init (FSharp.Core.Operators.max 0 dimension) (fun i ->\n        let d = f i\n        d + 1)"
        false

[<Fact>]
let ``a multi-line mapper whose body hangs left of the range keeps the map`` () =
    // spliced where the range stood, the body would sit left of `Array.init`
    let body =
        "let r = [| 0 .. dimension - 1 |] |> Array.map (fun i ->\n    let d = f i\n    d + 1)"

    Assert.True(typechecksCleanly (header + body), "the fixture itself must typecheck")
    Assert.Empty(found body)

/// Every later line aligned under the first line's token after the arrow.
let private alignedUnder (first: string) (later: string list) =
    let pad = String.replicate (first.LastIndexOf "-> " + 3) " "
    String.concat "\n" (first :: (later |> List.map (fun l -> pad + l)))

[<Fact>]
let ``match arms aligned to a match after the arrow keep the map`` () =
    // `Array.init (FSharp.Core.Operators.max 0 (dimension + 1)) (fun i ->` is longer than the range
    // and map, so the `match` moves right and the arms fall offside (FS0058)
    let arms =
        "let r =\n"
        + alignedUnder "    [| 0 .. dimension |] |> Array.map (fun i -> match i with" [ "| 0 -> f 0"; "| _ -> i)" ]

    Assert.True(typechecksCleanly (header + arms), "the fixture itself must typecheck")
    Assert.Empty(found arms)

[<Fact>]
let ``a second statement aligned to a first one after the arrow keeps the map`` () =
    // a second statement aligned to a first one on the arrow's line: moved
    // left, the first leaves the second indented past it, and the second
    // becomes its argument - `tap i i` - with no error at all
    let statements =
        "let tap (x: int) = ignore x; fun (y: int) -> y * 100\nlet r =\n"
        + alignedUnder "    [| 0 .. dimension - 1 |] |> Array.map (fun i -> tap i |> ignore" [ "i)" ]

    Assert.True(typechecksCleanly (header + statements), "the fixture itself must typecheck")
    Assert.Empty(found statements)

[<Fact>]
let ``the rewrite keeps what the program does`` () =
    // `init` applies the function for 0, 1, ... n-1 in that order, which is
    // the order the map walked the range in
    let before = [| 0 .. 5 - 1 |] |> Array.map (fun i -> i * 3)
    let after = Array.init 5 (fun i -> i * 3)
    Assert.Equal<int[]>(before, after)

[<Fact>]
let ``a negative count is why an unproven count is clamped`` () =
    // the bare `init` differs from the range there; `max 0 n` does not
    let n = -1
    let triple (i: int) = i * 3
    Assert.Empty([| 0 .. n - 1 |] |> Array.map triple)

    Assert.Throws<System.ArgumentException>(fun () -> Array.init n triple |> ignore)
    |> ignore

    Assert.Empty(Array.init (max 0 n) triple)
