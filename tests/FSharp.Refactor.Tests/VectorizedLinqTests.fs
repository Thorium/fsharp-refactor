module FSharp.Refactor.Tests.VectorizedLinqTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private vectorizedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    VectorizedLinq.find tree sourceText checkResults

[<Fact>]
let ``Array sum on an int array is noted`` () =
    match vectorizedIn "let f (values: int[]) = Array.sum values" with
    | [ s ] ->
        Assert.Equal("sum", s.FunctionName)
        Assert.Equal("values", s.ArrayName)
    | other -> failwithf "Expected exactly one vectorization note, got %A" other

[<Fact>]
let ``piped Array max on an int64 array is noted`` () =
    match vectorizedIn "let f (values: int64[]) = values |> Array.max" with
    | [ s ] -> Assert.Equal("max", s.FunctionName)
    | other -> failwithf "Expected exactly one piped note, got %A" other

[<Fact>]
let ``Seq sum over an int array is the same scalar loop`` () =
    match vectorizedIn "let f (values: int[]) = values |> Seq.sum" with
    | [ s ] ->
        Assert.Equal("Seq", s.ModuleName)
        Assert.Equal("sum", s.FunctionName)
    | other -> failwithf "Expected exactly one Seq-over-array note, got %A" other

[<Fact>]
let ``Seq sum over a list has no vectorized sibling`` () =
    Assert.Empty(vectorizedIn "let f (values: int list) = values |> Seq.sum")

[<Fact>]
let ``float arrays are excluded for NaN semantics`` () =
    Assert.Empty(vectorizedIn "let f (values: float[]) = Array.sum values")

[<Fact>]
let ``lists are not arrays`` () =
    Assert.Empty(vectorizedIn "let f (values: int list) = List.sum values")

[<Fact>]
let ``Array sum of a non-primitive is left alone`` () =
    Assert.Empty(vectorizedIn "let f (values: decimal[]) = Array.sum values")

[<Fact>]
let ``a record-field array aggregation is noted`` () =
    // the field resolves as FSharpField, not a member-or-value
    let suggestions =
        vectorizedIn "type State = { Buffer: int[] }\nlet f (state: State) = state.Buffer |> Array.sum"

    match suggestions with
    | [ s ] -> Assert.Equal("state.Buffer", s.ArrayName)
    | other -> failwithf "Expected exactly one vectorized note, got %A" other

[<Fact>]
let ``piped Array contains on an int array is noted`` () =
    match vectorizedIn "let f (values: int[]) = values |> Array.contains 42" with
    | [ s ] ->
        Assert.Equal("contains", s.FunctionName)
        Assert.Equal("values", s.ArrayName)
    | other -> failwithf "Expected exactly one contains note, got %A" other

[<Fact>]
let ``direct Array contains on an int array is noted`` () =
    match vectorizedIn "let f (values: int[]) = Array.contains 42 values" with
    | [ s ] -> Assert.Equal("contains", s.FunctionName)
    | other -> failwithf "Expected exactly one direct contains note, got %A" other

[<Fact>]
let ``Array contains on a list stays quiet`` () =
    Assert.Empty(vectorizedIn "let f (values: int list) = values |> List.contains 42")

[<Fact>]
let ``Array contains on a float array stays quiet`` () =
    // NaN: Enumerable.Contains uses EqualityComparer, F# contains uses (=)
    Assert.Empty(vectorizedIn "let f (values: float[]) = values |> Array.contains 4.2")

[<Fact>]
let ``a contains inside a query expression stays quiet`` () =
    // inside query { } this is a quotation for a provider's translator:
    // SQLProvider turns Array.contains into SQL IN, and the Enumerable
    // spelling may not translate at all
    Assert.Empty(
        vectorizedIn
            "let f (values: int[]) (xs: int list) =\n    query {\n        for x in xs do\n            where (values |> Array.contains x)\n            select x\n    }"
    )

[<Fact>]
let ``a sum inside a query expression stays quiet too`` () =
    Assert.Empty(
        vectorizedIn
            "let f (values: int[]) (xs: int list) =\n    query {\n        for x in xs do\n            select (Array.sum values + x)\n    }"
    )

[<Fact>]
let ``FR0041: a blocked-account lookup over an int array is swept to Enumerable.Contains`` () =
    // a payment gate probes a blocked-account list on every transaction:
    // Enumerable.Contains gives the same answer (int equality agrees with
    // EqualityComparer.Default) and the same ArgumentNullException on a null
    // array, vectorised - so the sweep applies it
    let cases =
        [
            "let isBlocked (blocked: int[]) (account: int) = Array.contains account blocked",
            "System.Linq.Enumerable.Contains(blocked, account)"
            "open System.Linq\nlet isBlocked (blocked: int64[]) (account: int64) = blocked |> Array.contains account",
            "Enumerable.Contains(blocked, account)"
            "let isBlocked (blocked: int[]) (account: int) = not (Array.contains (account + 1) blocked)",
            "not (System.Linq.Enumerable.Contains(blocked, (account + 1)))"
        ]

    for source, expected in cases do
        match vectorizedIn source with
        | [ s ] ->
            Assert.True(s.ReplacementText.IsSome, "Array.contains on an int array carries a fix")
            let patched = applyEdit source s.Range s.ReplacementText.Value
            Assert.Contains(expected, patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected exactly one contains suggestion, got %A" other

    // the direct form read the probe before the array: a call probed against
    // a property path would swap the order of two reads
    match
        vectorizedIn
            "type Book = { Blocked: int[] }\nlet isBlocked (book: Book) (next: unit -> int) = Array.contains (next ()) book.Blocked"
    with
    | [ s ] -> Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one contains note, got %A" other

    // the aggregations stay notes: LINQ Sum throws on overflow, Min/Max on empty
    match vectorizedIn "let total (amounts: int[]) = Array.sum amounts" with
    | [ s ] -> Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one sum note, got %A" other

    // Seq.contains over an array is FR0139's fix, not a second one here
    match vectorizedIn "let isBlocked (blocked: int[]) (account: int) = Seq.contains account blocked" with
    | [ s ] -> Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one Seq.contains note, got %A" other
