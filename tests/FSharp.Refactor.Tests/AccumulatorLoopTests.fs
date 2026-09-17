module FSharp.Refactor.Tests.AccumulatorLoopTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AccumulatorLoop.find tree sourceText checkResults

let private applyEdits (source: string) (edits: AccumulatorLoop.Edit list) =
    let lines = source.Split '\n'

    let offsetOf (line: int) (col: int) =
        (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

    edits
    |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
    |> List.fold
        (fun (acc: string) e ->
            let s = offsetOf e.Range.StartLine e.Range.StartColumn
            let en = offsetOf e.Range.EndLine e.Range.EndColumn
            acc.Substring(0, s) + e.Replacement + acc.Substring en)
        source

/// One suggestion, applied: the patched source typechecks and reads as
/// expected.
let private assertRewrite (source: string) (expected: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdits source s.Edits
        Assert.Equal(expected, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        s
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``a guarded loop into a ResizeArray drained by List.ofSeq is a list expression`` () =
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n\n    for x in xs do\n        if x > 1 then\n            acc.Add(x * 2)\n\n    List.ofSeq acc"
        "let f (xs: int list) =\n\n    let acc: int list =\n        [\n            for x in xs do\n                if x > 1 then\n                    x * 2\n        ]\n\n    acc"
    |> ignore

[<Fact>]
let ``several loops and a match move together`` () =
    assertRewrite
        "let f (xs: int list) (ys: string list) =\n    let acc = ResizeArray<string>()\n    for x in xs do\n        match x with\n        | 1 -> acc.Add \"one\"\n        | _ -> ()\n    for y in ys do\n        acc.Add y\n    String.concat \", \" (List.ofSeq acc)"
        "let f (xs: int list) (ys: string list) =\n    let acc: string list =\n        [\n            for x in xs do\n                match x with\n                | 1 -> \"one\"\n                | _ -> ()\n            for y in ys do\n                y\n        ]\n    String.concat \", \" acc"
    |> ignore

[<Fact>]
let ``an indexed or ToArray drain wants an array, which the ResizeArray builds fastest`` () =
    // measured: the array expression runs 1.6x the fill's time, so the
    // rule stands down rather than trade time for a shape
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add(x + 1)\n    let arr = acc.ToArray()\n    acc.[0] + arr.Length + acc.Count"
    )

[<Fact>]
let ``a record added on the lines below moves up to the call's column`` () =
    // left where it stood, deeper than a `let` above it, the record would
    // read as that let's continuation
    assertRewrite
        "type R = { A: int; B: string }\nlet f (xs: int list) =\n    let acc = ResizeArray<R>()\n    for x in xs do\n        if x > 0 then\n            let y = x\n            acc.Add\n                {\n                    A = y\n                    B = string x\n                }\n    Seq.toList acc"
        "type R = { A: int; B: string }\nlet f (xs: int list) =\n    let acc: R list =\n        [\n            for x in xs do\n                if x > 0 then\n                    let y = x\n                    {\n                        A = y\n                        B = string x\n                    }\n        ]\n    acc"
    |> ignore

[<Fact>]
let ``statements before the loops that leave the accumulator alone let it move down`` () =
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    let limit = 3\n    printfn \"start\"\n    for x in xs do\n        if x < limit then acc.Add x\n    acc |> List.ofSeq |> List.rev"
        "let f (xs: int list) =\n    let limit = 3\n    printfn \"start\"\n    let acc: int list =\n        [\n            for x in xs do\n                if x < limit then x\n        ]\n    acc |> List.rev"
    |> ignore

[<Fact>]
let ``a read between the let and the loops stands the rule down`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    printfn \"%d\" acc.Count\n    for x in xs do\n        acc.Add x\n    List.ofSeq acc"
    )

[<Fact>]
let ``a read inside the loop is not a fill`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        if acc.Count < 3 then acc.Add x\n    List.ofSeq acc"
    )

[<Fact>]
let ``an Add inside a lambda is a walker's, not a loop's`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        [ 1; 2 ] |> List.iter (fun y -> acc.Add(x + y))\n    List.ofSeq acc"
    )

[<Fact>]
let ``a mutation after the loops stands the rule down`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    acc.Add 0\n    List.ofSeq acc"
    )

[<Fact>]
let ``the ResizeArray returned as itself stands the rule down`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    acc"
    )

[<Fact>]
let ``a method call on the accumulator stands the rule down`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    acc.Contains 3"
    )

[<Fact>]
let ``a loop that also fills another collection stays`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    let other = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n        other.Add(-x)\n    List.ofSeq acc @ List.ofSeq other"
    )

[<Fact>]
let ``a copy-constructed ResizeArray starts full and stays`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) (seed: int list) =\n    let acc = ResizeArray<int>(seed)\n    for x in xs do\n        acc.Add x\n    List.ofSeq acc"
    )

[<Fact>]
let ``an interface element type upcast by Add stays`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<System.IComparable>()\n    for x in xs do\n        acc.Add x\n    List.ofSeq acc"
    )

[<Fact>]
let ``a let-bang in the loop cannot live in a list expression`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    async {\n        let acc = ResizeArray<int>()\n        for x in xs do\n            let! y = async { return x }\n            acc.Add y\n        return List.ofSeq acc\n    }"
    )

[<Fact>]
let ``a loop between the feeding loops that reads the accumulator breaks the run`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    for a in acc do\n        printfn \"%d\" a\n    for x in xs do\n        acc.Add(-x)\n    List.ofSeq acc"
    )

[<Fact>]
let ``a drain loop after the fills is fine`` () =
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    for a in acc do\n        printfn \"%d\" a\n    List.ofSeq acc"
        "let f (xs: int list) =\n    let acc: int list =\n        [\n            for x in xs do\n                x\n        ]\n    for a in acc do\n        printfn \"%d\" a\n    acc"
    |> ignore

[<Fact>]
let ``an argument to a function taking anything but a seq stands the rule down`` () =
    Assert.Empty(
        findIn
            "let g (r: ResizeArray<int>) = r.Count\nlet f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    g acc"
    )

[<Fact>]
let ``an inferred ResizeArray gets no annotation`` () =
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray()\n    for x in xs do\n        acc.Add(string x)\n    String.concat \"\" (Seq.toList acc)"
        "let f (xs: int list) =\n    let acc =\n        [\n            for x in xs do\n                string x\n        ]\n    String.concat \"\" acc"
    |> ignore

[<Fact>]
let ``a tuple element type is parenthesised in the annotation`` () =
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray<int * string>()\n    for x in xs do\n        acc.Add((x, string x))\n    List.ofSeq acc"
        "let f (xs: int list) =\n    let acc: (int * string) list =\n        [\n            for x in xs do\n                (x, string x)\n        ]\n    acc"
    |> ignore

[<Fact>]
let ``the declared type carries the Add's conversion into the yields`` () =
    // `acc.Add 1` converted the int literal to int64 through the method
    // call; the annotation lets the list expression do the same
    assertRewrite
        "let f (xs: int list) =\n    let acc = ResizeArray<int64>()\n    for x in xs do\n        if x > 0 then acc.Add 1\n    List.ofSeq acc"
        "let f (xs: int list) =\n    let acc: int64 list =\n        [\n            for x in xs do\n                if x > 0 then 1\n        ]\n    acc"
    |> ignore

[<Fact>]
let ``a Count drain is an O(1) read the list has not got`` () =
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    for y in xs do\n        printfn \"%d %d\" y acc.Count\n    Seq.sum acc"
    )

[<Fact>]
let ``a use binding in the loop stands the rule down`` () =
    Assert.Empty(
        findIn
            "let f (xs: string list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        use r = new System.IO.StringReader(x)\n        acc.Add(r.Read())\n    List.ofSeq acc"
    )

[<Fact>]
let ``a project's own List module spelling ofSeq is a seq-taking function, not the conversion`` () =
    // it keeps its call — a list is as good a seq as the ResizeArray was —
    // where FSharp.Core's ofSeq would have collapsed to `acc`
    assertRewrite
        "module List =\n    let ofSeq (xs: seq<int>) = Seq.sum xs\nlet f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    List.ofSeq acc + (Seq.toList acc).Length"
        "module List =\n    let ofSeq (xs: seq<int>) = Seq.sum xs\nlet f (xs: int list) =\n    let acc: int list =\n        [\n            for x in xs do\n                x\n        ]\n    List.ofSeq acc + acc.Length"
    |> ignore

[<Fact>]
let ``a seq-only drain keeps the ResizeArray, whose bare fill is the fastest`` () =
    // measured: nothing converted the ResizeArray, so both expressions
    // lose to the fill it already has
    Assert.Empty(
        findIn
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add x\n    Seq.sum acc"
    )

[<Fact>]
let ``the arrays knob buys the array expression for an indexed drain`` () =
    let tree, sourceText, checkResults =
        parseAndCheck
            "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add(x + 1)\n    let arr = acc.ToArray()\n    acc.[0] + arr.Length + acc.Count"

    match AccumulatorLoop.findWith true false tree sourceText checkResults with
    | [ s ] ->
        let patched =
            applyEdits
                "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        acc.Add(x + 1)\n    let arr = acc.ToArray()\n    acc.[0] + arr.Length + acc.Count"
                s.Edits

        Assert.Equal(
            "let f (xs: int list) =\n    let acc: int[] =\n        [|\n            for x in xs do\n                x + 1\n        |]\n    let arr = acc\n    acc.[0] + arr.Length + acc.Length",
            patched
        )

        Assert.True(typechecksCleanly patched, patched)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``the explicitYield knob spells every yield for an older compiler`` () =
    let source =
        "let f (xs: int list) =\n    let acc = ResizeArray<int>()\n    for x in xs do\n        if x > 1 then\n            acc.Add(x * 2)\n    List.ofSeq acc"

    let tree, sourceText, checkResults = parseAndCheck source

    match AccumulatorLoop.findWith false true tree sourceText checkResults with
    | [ s ] ->
        let patched = applyEdits source s.Edits

        Assert.Equal(
            "let f (xs: int list) =\n    let acc: int list =\n        [\n            for x in xs do\n                if x > 1 then\n                    yield x * 2\n        ]\n    acc",
            patched
        )

        Assert.True(typechecksCleanly patched, patched)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a while loop stepping a mutable index feeds a list expression`` () =
    // the mutable is read in the condition and assigned in the body: a
    // list expression compiles inline, so both are allowed there
    assertRewrite
        "let merge (arr: string[]) (first: string) (second: string) =\n    let merged = ResizeArray<string>()\n    let mutable i = 0\n    while i < arr.Length do\n        if i < arr.Length - 1 && arr.[i] = first && arr.[i + 1] = second then\n            merged.Add(first + second)\n            i <- i + 2\n        else\n            merged.Add arr.[i]\n            i <- i + 1\n    List.ofSeq merged"
        "let merge (arr: string[]) (first: string) (second: string) =\n    let mutable i = 0\n    let merged: string list =\n        [\n            while i < arr.Length do\n                if i < arr.Length - 1 && arr.[i] = first && arr.[i + 1] = second then\n                    first + second\n                    i <- i + 2\n                else\n                    arr.[i]\n                    i <- i + 1\n        ]\n    merged"
    |> ignore

[<Fact>]
let ``a loop that also assigns an outer mutable is still a list expression`` () =
    assertRewrite
        "let f (xs: int list) =\n    let ys = ResizeArray<int>()\n    let mutable total = 0\n    for x in xs do\n        ys.Add(x * 2)\n        total <- total + x\n    List.ofSeq ys, total"
        "let f (xs: int list) =\n    let mutable total = 0\n    let ys: int list =\n        [\n            for x in xs do\n                x * 2\n                total <- total + x\n        ]\n    ys, total"
    |> ignore
