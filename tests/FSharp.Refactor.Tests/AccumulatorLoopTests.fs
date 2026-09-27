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
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int>()

                for x in xs do
                    if x > 1 then
                        acc.Add(x * 2)

                List.ofSeq acc
            """)
        (fsharp
            """
            let f (xs: int list) =

                let acc: int list =
                    [
                        for x in xs do
                            if x > 1 then
                                x * 2
                    ]

                acc
            """)
    |> ignore

[<Fact>]
let ``several loops and a match move together`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) (ys: string list) =
                let acc = ResizeArray<string>()
                for x in xs do
                    match x with
                    | 1 -> acc.Add "one"
                    | _ -> ()
                for y in ys do
                    acc.Add y
                String.concat ", " (List.ofSeq acc)
            """)
        (fsharp
            """
            let f (xs: int list) (ys: string list) =
                let acc: string list =
                    [
                        for x in xs do
                            match x with
                            | 1 -> "one"
                            | _ -> ()
                        for y in ys do
                            y
                    ]
                String.concat ", " acc
            """)
    |> ignore

[<Fact>]
let ``an indexed or ToArray drain wants an array, which the ResizeArray builds fastest`` () =
    // measured: the array expression runs 1.6x the fill's time, so the
    // rule stands down rather than trade time for a shape
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add(x + 1)
                    let arr = acc.ToArray()
                    acc.[0] + arr.Length + acc.Count
                """
        )
    )

[<Fact>]
let ``a record added on the lines below moves up to the call's column`` () =
    // left where it stood, deeper than a `let` above it, the record would
    // read as that let's continuation
    assertRewrite
        (fsharp
            """
            type R = { A: int; B: string }
            let f (xs: int list) =
                let acc = ResizeArray<R>()
                for x in xs do
                    if x > 0 then
                        let y = x
                        acc.Add
                            {
                                A = y
                                B = string x
                            }
                Seq.toList acc
            """)
        (fsharp
            """
            type R = { A: int; B: string }
            let f (xs: int list) =
                let acc: R list =
                    [
                        for x in xs do
                            if x > 0 then
                                let y = x
                                {
                                    A = y
                                    B = string x
                                }
                    ]
                acc
            """)
    |> ignore

[<Fact>]
let ``statements before the loops that leave the accumulator alone let it move down`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int>()
                let limit = 3
                printfn "start"
                for x in xs do
                    if x < limit then acc.Add x
                acc |> List.ofSeq |> List.rev
            """)
        (fsharp
            """
            let f (xs: int list) =
                let limit = 3
                printfn "start"
                let acc: int list =
                    [
                        for x in xs do
                            if x < limit then x
                    ]
                acc |> List.rev
            """)
    |> ignore

[<Fact>]
let ``a read between the let and the loops stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    printfn "%d" acc.Count
                    for x in xs do
                        acc.Add x
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a read inside the loop is not a fill`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        if acc.Count < 3 then acc.Add x
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``an Add inside a lambda is a walker's, not a loop's`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        [ 1; 2 ] |> List.iter (fun y -> acc.Add(x + y))
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a mutation after the loops stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    acc.Add 0
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``the ResizeArray returned as itself stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    acc
                """
        )
    )

[<Fact>]
let ``a method call on the accumulator stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    acc.Contains 3
                """
        )
    )

[<Fact>]
let ``a loop that also fills another collection stays`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    let other = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                        other.Add(-x)
                    List.ofSeq acc @ List.ofSeq other
                """
        )
    )

[<Fact>]
let ``a copy-constructed ResizeArray starts full and stays`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) (seed: int list) =
                    let acc = ResizeArray<int>(seed)
                    for x in xs do
                        acc.Add x
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``an interface element type upcast by Add stays`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<System.IComparable>()
                    for x in xs do
                        acc.Add x
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a let-bang in the loop cannot live in a list expression`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    async {
                        let acc = ResizeArray<int>()
                        for x in xs do
                            let! y = async { return x }
                            acc.Add y
                        return List.ofSeq acc
                    }
                """
        )
    )

[<Fact>]
let ``a loop between the feeding loops that reads the accumulator breaks the run`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    for a in acc do
                        printfn "%d" a
                    for x in xs do
                        acc.Add(-x)
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a drain loop after the fills is fine`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int>()
                for x in xs do
                    acc.Add x
                for a in acc do
                    printfn "%d" a
                List.ofSeq acc
            """)
        (fsharp
            """
            let f (xs: int list) =
                let acc: int list =
                    [
                        for x in xs do
                            x
                    ]
                for a in acc do
                    printfn "%d" a
                acc
            """)
    |> ignore

[<Fact>]
let ``an argument to a function taking anything but a seq stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let g (r: ResizeArray<int>) = r.Count
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    g acc
                """
        )
    )

[<Fact>]
let ``an inferred ResizeArray gets no annotation`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray()
                for x in xs do
                    acc.Add(string x)
                String.concat "" (Seq.toList acc)
            """)
        (fsharp
            """
            let f (xs: int list) =
                let acc =
                    [
                        for x in xs do
                            string x
                    ]
                String.concat "" acc
            """)
    |> ignore

[<Fact>]
let ``a tuple element type is parenthesised in the annotation`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int * string>()
                for x in xs do
                    acc.Add((x, string x))
                List.ofSeq acc
            """)
        (fsharp
            """
            let f (xs: int list) =
                let acc: (int * string) list =
                    [
                        for x in xs do
                            (x, string x)
                    ]
                acc
            """)
    |> ignore

[<Fact>]
let ``the declared type carries the Add's conversion into the yields`` () =
    // `acc.Add 1` converted the int literal to int64 through the method
    // call; the annotation lets the list expression do the same
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int64>()
                for x in xs do
                    if x > 0 then acc.Add 1
                List.ofSeq acc
            """)
        (fsharp
            """
            let f (xs: int list) =
                let acc: int64 list =
                    [
                        for x in xs do
                            if x > 0 then 1
                    ]
                acc
            """)
    |> ignore

[<Fact>]
let ``a Count drain is an O(1) read the list has not got`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    for y in xs do
                        printfn "%d %d" y acc.Count
                    Seq.sum acc
                """
        )
    )

[<Fact>]
let ``a use binding in the loop stands the rule down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: string list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        use r = new System.IO.StringReader(x)
                        acc.Add(r.Read())
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a project's own List module spelling ofSeq is a seq-taking function, not the conversion`` () =
    // it keeps its call — a list is as good a seq as the ResizeArray was —
    // where FSharp.Core's ofSeq would have collapsed to `acc`
    assertRewrite
        (fsharp
            """
            module List =
                let ofSeq (xs: seq<int>) = Seq.sum xs
            let f (xs: int list) =
                let acc = ResizeArray<int>()
                for x in xs do
                    acc.Add x
                List.ofSeq acc + (Seq.toList acc).Length
            """)
        (fsharp
            """
            module List =
                let ofSeq (xs: seq<int>) = Seq.sum xs
            let f (xs: int list) =
                let acc: int list =
                    [
                        for x in xs do
                            x
                    ]
                List.ofSeq acc + acc.Length
            """)
    |> ignore

[<Fact>]
let ``a seq-only drain keeps the ResizeArray, whose bare fill is the fastest`` () =
    // measured: nothing converted the ResizeArray, so both expressions
    // lose to the fill it already has
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add x
                    Seq.sum acc
                """
        )
    )

[<Fact>]
let ``the arrays knob buys the array expression for an indexed drain`` () =
    let tree, sourceText, checkResults =
        parseAndCheck (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        acc.Add(x + 1)
                    let arr = acc.ToArray()
                    acc.[0] + arr.Length + acc.Count
                """
        )

    match AccumulatorLoop.findWith true false tree sourceText checkResults with
    | [ s ] ->
        let patched =
            applyEdits
                (fsharp
                    """
                    let f (xs: int list) =
                        let acc = ResizeArray<int>()
                        for x in xs do
                            acc.Add(x + 1)
                        let arr = acc.ToArray()
                        acc.[0] + arr.Length + acc.Count
                    """)
                s.Edits

        Assert.Equal(
            fsharp
                """
                let f (xs: int list) =
                    let acc: int[] =
                        [|
                            for x in xs do
                                x + 1
                        |]
                    let arr = acc
                    acc.[0] + arr.Length + acc.Length
                """,
            patched
        )

        Assert.True(typechecksCleanly patched, patched)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``the explicitYield knob spells every yield for an older compiler`` () =
    let source =
        fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int>()
                for x in xs do
                    if x > 1 then
                        acc.Add(x * 2)
                List.ofSeq acc
            """

    let tree, sourceText, checkResults = parseAndCheck source

    match AccumulatorLoop.findWith false true tree sourceText checkResults with
    | [ s ] ->
        let patched = applyEdits source s.Edits

        Assert.Equal(
            fsharp
                """
                let f (xs: int list) =
                    let acc: int list =
                        [
                            for x in xs do
                                if x > 1 then
                                    yield x * 2
                        ]
                    acc
                """,
            patched
        )

        Assert.True(typechecksCleanly patched, patched)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a while loop stepping a mutable index feeds a list expression`` () =
    // the mutable is read in the condition and assigned in the body: a
    // list expression compiles inline, so both are allowed there
    assertRewrite
        (fsharp
            """
            let merge (arr: string[]) (first: string) (second: string) =
                let merged = ResizeArray<string>()
                let mutable i = 0
                while i < arr.Length do
                    if i < arr.Length - 1 && arr.[i] = first && arr.[i + 1] = second then
                        merged.Add(first + second)
                        i <- i + 2
                    else
                        merged.Add arr.[i]
                        i <- i + 1
                List.ofSeq merged
            """)
        (fsharp
            """
            let merge (arr: string[]) (first: string) (second: string) =
                let mutable i = 0
                let merged: string list =
                    [
                        while i < arr.Length do
                            if i < arr.Length - 1 && arr.[i] = first && arr.[i + 1] = second then
                                first + second
                                i <- i + 2
                            else
                                arr.[i]
                                i <- i + 1
                    ]
                merged
            """)
    |> ignore

[<Fact>]
let ``a loop that also assigns an outer mutable is still a list expression`` () =
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let ys = ResizeArray<int>()
                let mutable total = 0
                for x in xs do
                    ys.Add(x * 2)
                    total <- total + x
                List.ofSeq ys, total
            """)
        (fsharp
            """
            let f (xs: int list) =
                let mutable total = 0
                let ys: int list =
                    [
                        for x in xs do
                            x * 2
                            total <- total + x
                    ]
                ys, total
            """)
    |> ignore

[<Fact>]
let ``a drain wrapped in an application's own parentheses keeps a pair`` () =
    // `Some(List.ofSeq acc)`: dropping the parentheses would glue the name
    // to the function - `Someacc` (the tool's own StructOption.fs)
    assertRewrite
        (fsharp
            """
            let f (xs: int list) =
                let acc = ResizeArray<int>()
                for x in xs do
                    acc.Add(x * 2)
                Some(List.ofSeq acc)
            """)
        (fsharp
            """
            let f (xs: int list) =
                let acc: int list =
                    [
                        for x in xs do
                            x * 2
                    ]
                Some(acc)
            """)
    |> ignore

[<Fact>]
let ``a discarded non-unit statement in the loop would become a yield`` () =
    // `d.TryAdd(x, x)` returns a bool the loop discards; in the list
    // expression it is an implicit yield, and the list doubles in length
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                open System.Collections.Generic
                let f (xs: int list) (d: Dictionary<int,int>) =
                    let acc = ResizeArray<bool>()
                    for x in xs do
                        d.TryAdd(x, x)
                        acc.Add(x > 0)
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a discarded non-unit value in a branch of the loop would become a yield`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ResizeArray<int>()
                    for x in xs do
                        if x > 0 then
                            x.ToString()
                            acc.Add x
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``unit statements beside the Add still move`` () =
    // a printf, a method returning void, an indexed set and an assignment
    // are unit: none of them yields
    assertRewrite
        (fsharp
            """
            module T
            open System.Collections.Generic
            let f (xs: int list) (d: Dictionary<int,int>) =
                let acc = ResizeArray<bool>()
                let mutable n = 0
                for x in xs do
                    printfn "%d" x
                    System.Console.WriteLine x
                    d.[x] <- x
                    n <- n + 1
                    acc.Add(x > 0)
                List.ofSeq acc
            """)
        (fsharp
            """
            module T
            open System.Collections.Generic
            let f (xs: int list) (d: Dictionary<int,int>) =
                let mutable n = 0
                let acc: bool list =
                    [
                        for x in xs do
                            printfn "%d" x
                            System.Console.WriteLine x
                            d.[x] <- x
                            n <- n + 1
                            x > 0
                    ]
                acc
            """)
    |> ignore

[<Fact>]
let ``a loop over a Span cannot move into the list expression`` () =
    // the list expression may not capture the ReadOnlySpan: FS0406
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let chars (s: System.ReadOnlySpan<char>) =
                    let acc = ResizeArray<char>()
                    for c in s do
                        acc.Add c
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a loop indexing a Span cannot move into the list expression either`` () =
    // the indexer is an inref property FCS cannot place a declaration for:
    // that must not empty the file's byref-like uses and let the Span through
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let upper (s: System.ReadOnlySpan<char>) =
                    let acc = ResizeArray<char>()
                    for i in 0 .. s.Length - 1 do
                        acc.Add(System.Char.ToUpperInvariant s.[i])
                    List.ofSeq acc
                """
        )
    )

[<Fact>]
let ``a delegate element type converted the lambda where a yield does not`` () =
    // `acc.Add(fun () -> ...)` made an Action of the lambda through the
    // method call; a yield of the lambda into an `Action list` is FS0002
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                open System
                let f (xs: int list) =
                    let acc = ResizeArray<Action>()
                    for x in xs do
                        acc.Add(fun () -> printfn "%d" x)
                    List.ofSeq acc
                """
        )
    )

// ---- a `let mutable` list fed by appends ----

[<Fact>]
let ``a mutable list appended one element per iteration is a list expression`` () =
    let s =
        assertRewrite
            (fsharp
                """
                let f (i: int) = i * 2
                let build (ys: int list) =
                    let mutable xs = []

                    for i in ys do
                        let r = f i
                        xs <- List.append xs [ r ]

                    xs
                """)
            (fsharp
                """
                let f (i: int) = i * 2
                let build (ys: int list) =

                    let xs =
                        [
                            for i in ys do
                                let r = f i
                                r
                        ]

                    xs
                """)

    Assert.True s.Mutable

[<Fact>]
let ``the (at) spelling, a guard and an annotation keep their shape`` () =
    assertRewrite
        (fsharp
            """
            let build (ys: int list) =
                let mutable xs: int64 list = []
                for i in ys do
                    if i > 0 then
                        xs <- xs @ [ int64 i ]
                List.sum xs
            """)
        (fsharp
            """
            let build (ys: int list) =
                let xs: int64 list =
                    [
                        for i in ys do
                            if i > 0 then
                                int64 i
                    ]
                List.sum xs
            """)
    |> ignore

[<Fact>]
let ``a consed list read through List.rev yields in loop order`` () =
    assertRewrite
        (fsharp
            """
            let build (ys: int list) =
                let mutable xs = []
                for i in ys do
                    xs <- i * 2 :: xs
                List.rev xs
            """)
        (fsharp
            """
            let build (ys: int list) =
                let xs =
                    [
                        for i in ys do
                            i * 2
                    ]
                xs
            """)
    |> ignore

    // read without the reverse, the consed list is backwards: FR0051's
    // note, not a rewrite
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- i * 2 :: xs
                    xs
                """
        )
    )

    // fed at both ends there is no loop order to yield in
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- i :: xs
                        xs <- xs @ [ i ]
                    List.rev xs
                """
        )
    )

[<Fact>]
let ``two loops and any later read of the list`` () =
    assertRewrite
        (fsharp
            """
            let build (ys: int list) (zs: int list) =
                let mutable xs = []
                for i in ys do
                    xs <- List.append xs [ i + 1 ]
                for z in zs do
                    xs <- xs @ [ z * 2 ]
                printfn "%d" xs.Length
                xs |> List.map string
            """)
        (fsharp
            """
            let build (ys: int list) (zs: int list) =
                let xs =
                    [
                        for i in ys do
                            i + 1
                        for z in zs do
                            z * 2
                    ]
                printfn "%d" xs.Length
                xs |> List.map string
            """)
    |> ignore

[<Fact>]
let ``a list read in its loop, reassigned after, or built two at a time stays`` () =
    // read while building: the expression has no partial list to read
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        if xs.Length < 3 then
                            xs <- xs @ [ i ]
                    xs
                """
        )
    )

    // assigned after the loops: the result is immutable
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- xs @ [ i ]
                    if xs.Length > 5 then
                        xs <- []
                    xs
                """
        )
    )

    // two elements per step, or a whole list
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- xs @ [ i; i + 1 ]
                    xs
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- xs @ i
                    xs
                """
        )
    )

    // the element reads the accumulator
    Assert.Empty(
        findIn (
            fsharp
                """
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- xs @ [ i + xs.Length ]
                    xs
                """
        )
    )

[<Fact>]
let ``a project's own (at) or List module is not FSharp.Core's append`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let (@) (a: int list) (b: int list) = a
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- xs @ [ i ]
                    xs
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                module List =
                    let append (a: int list) (b: int list) = a
                let build (ys: int list) =
                    let mutable xs = []
                    for i in ys do
                        xs <- List.append xs [ i ]
                    xs
                """
        )
    )
