module FSharp.Refactor.Tests.PythonSmellTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0101 IndexedLoop ----

let private indexedLoopsIn (source: string) =
    let tree, sourceText = parse source
    IndexedLoop.find tree sourceText

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

let private assertIndexedLoop (source: string) (expectedPatched: string) =
    match indexedLoopsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one indexed-loop fix, got %A" other

[<Fact>]
let ``the canonical range-over-length loop iterates directly`` () =
    assertIndexedLoop
        "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%d\" xs.[i]"
        "module Test\nlet f (xs: int[]) =\n    for item in xs do\n        printfn \"%d\" item"

[<Fact>]
let ``the F#6 indexer spelling converts too`` () =
    assertIndexedLoop
        "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%d\" xs[i]"
        "module Test\nlet f (xs: int[]) =\n    for item in xs do\n        printfn \"%d\" item"

[<Fact>]
let ``the module-length spelling converts too`` () =
    assertIndexedLoop
        "module Test\nlet f (xs: int[]) =\n    for i in 0 .. Array.length xs - 1 do\n        printfn \"%d\" xs.[i]"
        "module Test\nlet f (xs: int[]) =\n    for item in xs do\n        printfn \"%d\" item"

[<Fact>]
let ``an index also used as a value is the author's call`` () =
    // iteri would fit, but that changes shape — stay quiet
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%d %d\" i xs.[i]"
    )

[<Fact>]
let ``element writes need the index`` () =
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        xs.[i] <- xs.[i] + 1"
    )

[<Fact>]
let ``a bound over a different collection is left alone`` () =
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) (ys: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%d\" ys.[i]"
    )

// ---- FR0102 ListIndexing ----

let private listIndexingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ListIndexing.find tree sourceText checkResults

[<Fact>]
let ``indexing a list inside a loop is quadratic and noted`` () =
    let suggestions =
        listIndexingIn
            "let f (names: string list) (count: int) =\n    for i in 0 .. count - 1 do\n        printfn \"%s\" names.[i]"

    match suggestions with
    | [ s ] -> Assert.Equal("names", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``indexing an array is what arrays are for`` () =
    Assert.Empty(
        listIndexingIn
            "let f (names: string[]) (count: int) =\n    for i in 0 .. count - 1 do\n        printfn \"%s\" names.[i]"
    )

[<Fact>]
let ``List.item in a collection callback is a loop too`` () =
    let suggestions =
        listIndexingIn
            "let f (names: string list) (idxs: int list) =\n    idxs |> List.iter (fun i -> printfn \"%s\" (List.item i names))"

    match suggestions with
    | [ s ] -> Assert.Equal("names", s.CollectionText)
    | other -> failwithf "Expected exactly one List.item note, got %A" other

[<Fact>]
let ``a single indexed access outside any loop is fine`` () =
    Assert.Empty(listIndexingIn "let f (names: string list) (i: int) = names.[i]")

[<Fact>]
let ``FR0102: a receiver bound by a match arm's pattern inside the loop is per-element`` () =
    // FCS SemanticClassification: `| Item.AnonRecdField(_, tys, idx, _) ->
    // tys[idx]` inside a per-element callback binds a fresh `tys` each time
    let source =
        "module Test\ntype Item =\n    | Field of int list * int\n    | Other\nlet f (items: Item list) =\n    items\n    |> List.map (fun item ->\n        match item with\n        | Field(tys, idx) -> tys[idx]\n        | Other -> 0)"

    Assert.Empty(listIndexingIn source)

[<Fact>]
let ``FR0102: a list's length read per iteration walks the list every time`` () =
    // Mibo Terrain: `count / (points.Length - 1)` per segment
    let source =
        "module Test\nlet f (points: int list) (count: int) =\n    let mutable total = 0\n    for i in 0 .. count - 1 do\n        total <- total + count / (points.Length + 1)\n    total"

    match listIndexingIn source with
    | [ s ] ->
        Assert.Equal("points", s.CollectionText)
        Assert.Equal(ListIndexing.AccessKind.Length, s.Kind)
    | other -> failwithf "Expected one length note, got %A" other

[<Fact>]
let ``FR0102: List.length in a callback and a while condition count too`` () =
    let source =
        "module Test\nlet f (xs: int list) (ys: int list) =\n    let a = ys |> List.map (fun y -> y + List.length xs)\n    let mutable i = 0\n    while i < xs.Length do\n        i <- i + 1\n    a"

    match listIndexingIn source with
    | [ a; b ] ->
        Assert.Equal("xs", a.CollectionText)
        Assert.Equal("xs", b.CollectionText)
    | other -> failwithf "Expected two length notes, got %A" other

[<Fact>]
let ``FR0102: a loop header's length bound evaluates once and an array's length is free`` () =
    Assert.Empty(
        listIndexingIn
            "module Test\nlet f (xs: int list) (arr: int[]) =\n    let mutable total = 0\n    for i in 0 .. xs.Length - 1 do\n        total <- total + arr.Length\n    total"
    )

// ---- FR0103 TypeTestChain ----

let private typeTestsIn (source: string) =
    let tree, sourceText = parse source
    TypeTestChain.find tree sourceText

let private assertTypeTestFix (source: string) (expectedReplacement: string) =
    match typeTestsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one type-test-chain fix, got %A" other

[<Fact>]
let ``the isinstance ladder becomes a match`` () =
    assertTypeTestFix
        "module Test\ntype Circle() = member _.R = 1.0\ntype Rect() = member _.W = 2.0\nlet f (shape: obj) =\n    if (shape :? Circle) then (shape :?> Circle).R\n    elif (shape :? Rect) then (shape :?> Rect).W\n    else 0.0"
        "match shape with | :? Circle as v -> v.R | :? Rect as v -> v.W | _ -> 0.0"

[<Fact>]
let ``a branch without a cast just drops the as-binder`` () =
    assertTypeTestFix
        "module Test\ntype Circle() = member _.R = 1.0\ntype Rect() = member _.W = 2.0\nlet f (shape: obj) =\n    if (shape :? Circle) then 1.0\n    elif (shape :? Rect) then (shape :?> Rect).W\n    else 0.0"
        "match shape with | :? Circle -> 1.0 | :? Rect as v -> v.W | _ -> 0.0"

[<Fact>]
let ``a compound condition needs a when guard and stays`` () =
    Assert.Empty(
        typeTestsIn
            "module Test\ntype Circle() = member _.R = 1.0\ntype Rect() = member _.W = 2.0\nlet f (shape: obj) (big: bool) =\n    if (shape :? Circle) && big then 1.0\n    elif (shape :? Rect) then 2.0\n    else 0.0"
    )

[<Fact>]
let ``a cast to a different type means the author knows more`` () =
    Assert.Empty(
        typeTestsIn
            "module Test\ntype Circle() = member _.R = 1.0\ntype Rect() = member _.W = 2.0\nlet f (shape: obj) =\n    if (shape :? Circle) then (shape :?> Rect).W\n    elif (shape :? Rect) then 2.0\n    else 0.0"
    )

[<Fact>]
let ``a single type test reads fine as an if`` () =
    Assert.Empty(
        typeTestsIn
            "module Test\ntype Circle() = member _.R = 1.0\nlet f (shape: obj) =\n    if (shape :? Circle) then 1.0 else 0.0"
    )

// ---- FR0104 RecursiveAppend ----

let private recursiveAppendsIn (source: string) =
    let tree, sourceText = parse source
    RecursiveAppend.find tree sourceText

[<Fact>]
let ``a singleton append per recursive call is noted`` () =
    let suggestions =
        recursiveAppendsIn
            "module Test\nlet rec collect (keep: int -> bool) acc xs =\n    match xs with\n    | [] -> acc\n    | x :: rest when keep x -> collect keep (acc @ [ x ]) rest\n    | _ :: rest -> collect keep acc rest"

    match suggestions with
    | [ s ] ->
        Assert.Equal("collect", s.FunctionName)
        Assert.Equal("acc", s.AccumulatorName)
    | other -> failwithf "Expected exactly one recursive-append note, got %A" other

[<Fact>]
let ``the List.append spelling is noted too`` () =
    let suggestions =
        recursiveAppendsIn
            "module Test\nlet rec collect acc xs =\n    match xs with\n    | [] -> acc\n    | x :: rest -> collect (List.append acc [ x ]) rest"

    match suggestions with
    | [ s ] -> Assert.Equal("acc", s.AccumulatorName)
    | other -> failwithf "Expected exactly one List.append note, got %A" other

[<Fact>]
let ``cons is the fix, not a finding`` () =
    Assert.Empty(
        recursiveAppendsIn
            "module Test\nlet rec collect acc xs =\n    match xs with\n    | [] -> List.rev acc\n    | x :: rest -> collect (x :: acc) rest"
    )

[<Fact>]
let ``a general merge may be exactly what the author wants`` () =
    Assert.Empty(
        recursiveAppendsIn
            "module Test\nlet rec collect acc xs =\n    match xs with\n    | [] -> acc\n    | x :: rest -> collect (acc @ expand x) rest\nand expand (x: int) : int list = [ x; x ]"
    )

[<Fact>]
let ``a nested loop rebinding the index keeps the outer loop`` () =
    // the inner `i` shadows: rewriting `xs.[i]` to the OUTER element would
    // silently change behavior
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        for i in 0 .. 2 do\n            printfn \"%d\" xs.[i]"
    )

[<Fact>]
let ``a match pattern rebinding the index keeps the loop`` () =
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) (q: int) =\n    for i in 0 .. xs.Length - 1 do\n        match q with\n        | i -> printfn \"%d\" xs.[i]"
    )

[<Fact>]
let ``an index used as a value inside an F#6 indexer-set is seen`` () =
    // from Fuuga's EvalTests: the SDK walker skips BOTH sides of
    // `logits[...] <- v` (SynExpr.Set), so `int64 pos` was invisible and
    // the loop got rewritten with `pos` still referenced. The AstIndex
    // graft now lifts Set's children.
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (tokens: int[]) (logits: int64[,,]) =\n    for pos in 0 .. tokens.Length - 1 do\n        let nextToken = min 31 (tokens.[pos] + 1)\n        logits[0L, int64 pos, int64 nextToken] <- 100L"
    )

[<Fact>]
let ``an F#6 element write needs the index too`` () =
    Assert.Empty(
        indexedLoopsIn
            "module Test\nlet f (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        xs[i] <- xs[i] + 1"
    )

// Both index spellings must behave alike — `.[ ]` and the F# 6 `[ ]` are
// the same operation, and a rule that sees only one silently half-works.

[<Fact>]
let ``the F#6 index spelling is noted too`` () =
    let suggestions =
        listIndexingIn
            "let f (names: string list) (count: int) =\n    for i in 0 .. count - 1 do\n        printfn \"%s\" names[i]"

    match suggestions with
    | [ s ] -> Assert.Equal("names", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``a bound taken from the list's own Length still notes - legacy spelling`` () =
    let suggestions =
        listIndexingIn
            "let f (names: string list) =\n    for i in 0 .. names.Length - 1 do\n        printfn \"%s\" names.[i]"

    match suggestions with
    | [ s ] -> Assert.Equal("names", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``a bound taken from the list's own Length still notes - F#6 spelling`` () =
    let suggestions =
        listIndexingIn
            "let f (names: string list) =\n    for i in 0 .. names.Length - 1 do\n        printfn \"%s\" names[i]"

    match suggestions with
    | [ s ] -> Assert.Equal("names", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``chained member access off the index - legacy spelling`` () =
    let suggestions =
        listIndexingIn
            "let f (xs: string list) =\n    let mutable n = 0\n    for i in 0 .. xs.Length - 1 do\n        n <- n + xs.[i].Length\n    n"

    match suggestions with
    | [ s ] -> Assert.Equal("xs", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``chained member access off the index - F#6 spelling`` () =
    let suggestions =
        listIndexingIn
            "let f (xs: string list) =\n    let mutable n = 0\n    for i in 0 .. xs.Length - 1 do\n        n <- n + xs[i].Length\n    n"

    match suggestions with
    | [ s ] -> Assert.Equal("xs", s.CollectionText)
    | other -> failwithf "Expected exactly one list-indexing note, got %A" other

[<Fact>]
let ``an indexed loop that takes the element's address keeps its index`` () =
    // Nu's Renderer2d: `let sprite = &sprites[index]` wants an inref into
    // the array; a `for sprite in sprites` element is a copy, and every
    // `&sprite.Field` after it mismatches ByRefKinds.In
    let tree, sourceText =
        parse
            "module Test\n[<Struct>]\ntype S = { mutable V: int }\nlet bump (v: inref<int>) = v + 1\nlet f (sprites: S[]) =\n    for index in 0 .. sprites.Length - 1 do\n        let sprite = &sprites[index]\n        bump &sprite.V |> ignore"

    Assert.Empty(IndexedLoop.find tree sourceText)

[<Fact>]
let ``FR0102: an index bounded by a small modulus or a small literal loop is a constant walk`` () =
    // Kasino: `Cards.allRanks[i % 13]` in a card builder, and short fixed loops
    Assert.Empty(
        listIndexingIn
            "module Test\nlet ranks = [ 1 .. 13 ]\nlet cards (n: int) = [ for i in 0 .. n - 1 do ranks[i % 13] ]\nlet firstFour (xs: int list) =\n    for i in 0 .. 3 do\n        printfn \"%d\" xs[i]\n    for i = 0 to 3 do\n        printfn \"%d\" xs.[i]"
    )

[<Fact>]
let ``FR0102: a large modulus still walks the list`` () =
    Assert.NotEmpty(
        listIndexingIn
            "module Test\nlet f (xs: int list) (n: int) =\n    for i in 0 .. n - 1 do\n        printfn \"%d\" xs[i % 1000]"
    )

[<Fact>]
let ``FR0101: the element is item, never a name bound around the loop`` () =
    // Mibo's Spatial2DTests: `for x in 0 .. 4 do` around the loop, and the
    // `x` the rewrite chose shadowed it; the outer loop variable is not
    // mentioned inside the loop, so only the scope walk can see it
    assertIndexedLoop
        "module Test\nlet g (xs: int[]) =\n    for x in 0 .. 4 do\n        for i in 0 .. xs.Length - 1 do\n            printfn \"%d\" xs.[i]"
        "module Test\nlet g (xs: int[]) =\n    for x in 0 .. 4 do\n        for item in xs do\n            printfn \"%d\" item"

[<Fact>]
let ``FR0101: a taken item counts up rather than shadowing`` () =
    // `item` is a parameter and `item2` a let on the path: neither is read
    // in the loop, and neither may be shadowed
    assertIndexedLoop
        "module Test\nlet f (item: int) (xs: int[]) =\n    let item2 = item\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%d\" xs.[i]\n    item2"
        "module Test\nlet f (item: int) (xs: int[]) =\n    let item2 = item\n    for item3 in xs do\n        printfn \"%d\" item3\n    item2"
