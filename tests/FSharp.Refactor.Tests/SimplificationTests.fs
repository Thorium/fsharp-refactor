module FSharp.Refactor.Tests.SimplificationTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// Parse-only rules (booleans, emptiness): no check results needed.
let private findParsed (source: string) =
    let tree, sourceText = parse source
    Simplification.find tree sourceText None

/// All rules including the typed None-comparison gate.
let private findChecked (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Simplification.find tree sourceText (Some checkResults)

let private assertSuggestion
    (suggestions: Simplification.Suggestion list)
    (source: string)
    (expectedReplacement: string)
    =
    match suggestions with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

/// Like assertSuggestion but for headerless script sources: verifies the
/// patched source by typechecking it as a script.
let private assertCheckedSuggestion
    (suggestions: Simplification.Suggestion list)
    (source: string)
    (expectedReplacement: string)
    =
    match suggestions with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one checked suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``if-then-true-else-false returns the condition`` () =
    let src = "module Test\nlet f (x: int) = if x > 3 then true else false"
    assertSuggestion (findParsed src) src "x > 3"

[<Fact>]
let ``if-then-false-else-true negates the condition`` () =
    let src = "module Test\nlet f (x: int) = if x > 3 then false else true"
    assertSuggestion (findParsed src) src "not (x > 3)"

[<Fact>]
let ``atomic negated condition needs no parens`` () =
    let src = "module Test\nlet f (b: bool) = if b then false else true"
    assertSuggestion (findParsed src) src "not b"

[<Fact>]
let ``same constant branches are not simplified`` () =
    Assert.Empty(findParsed "module Test\nlet f (x: int) = if x > 3 then true else true")

[<Fact>]
let ``length equals zero becomes isEmpty`` () =
    let src = "module Test\nlet f (xs: int list) = List.length xs = 0"
    assertSuggestion (findParsed src) src "List.isEmpty xs"

[<Fact>]
let ``piped length equals zero becomes piped isEmpty`` () =
    let src = "module Test\nlet f (xs: seq<int>) = xs |> Seq.length = 0"
    assertSuggestion (findParsed src) src "xs |> Seq.isEmpty"

[<Fact>]
let ``length greater than zero becomes not isEmpty`` () =
    let src = "module Test\nlet f (xs: int[]) = Array.length xs > 0"
    assertSuggestion (findParsed src) src "not (Array.isEmpty xs)"

[<Fact>]
let ``piped length not equal to zero becomes piped not`` () =
    let src = "module Test\nlet f (xs: int list) = xs |> List.length <> 0"
    assertSuggestion (findParsed src) src "xs |> List.isEmpty |> not"

[<Fact>]
let ``set count equals zero becomes Set isEmpty`` () =
    let src = "module Test\nlet f (s: Set<int>) = Set.count s = 0"
    assertSuggestion (findParsed src) src "Set.isEmpty s"

[<Fact>]
let ``zero less than length becomes not isEmpty`` () =
    let src = "module Test\nlet f (xs: int list) = 0 < List.length xs"
    assertSuggestion (findParsed src) src "not (List.isEmpty xs)"

[<Fact>]
let ``length compared with nonzero is not touched`` () =
    Assert.Empty(findParsed "module Test\nlet f (xs: int list) = List.length xs = 1")

[<Fact>]
let ``equals None becomes Option isNone`` () =
    let src = "let f (x: int option) = x = None"
    assertCheckedSuggestion (findChecked src) src "x.IsNone"

[<Fact>]
let ``not-equals None becomes Option isSome`` () =
    let src = "let f (x: int option) = x <> None"
    assertCheckedSuggestion (findChecked src) src "x.IsSome"

[<Fact>]
let ``None on the left is recognized`` () =
    let src = "let f (x: int option) = None = x"
    assertCheckedSuggestion (findChecked src) src "x.IsNone"

[<Fact>]
let ``equals ValueNone becomes ValueOption isNone`` () =
    let src = "let f (x: int voption) = x = ValueNone"
    assertCheckedSuggestion (findChecked src) src "x.IsNone"

[<Fact>]
let ``shadowed None case is not rewritten`` () =
    Assert.Empty(
        findChecked "type T = Something | None\nlet f (x: T) = x = None"
        |> List.filter (fun s -> s.Kind = Simplification.SimplificationKind.OptionComparison)
    )

[<Fact>]
let ``None comparison without check results is not rewritten`` () =
    Assert.Empty(findParsed "module Test\nlet f (x: int option) = x = None")

[<Fact>]
let ``elif branch is never simplified`` () =
    // review regression: replacing the elif node with its condition would
    // glue the condition onto the preceding branch
    Assert.Empty(findParsed "module Test\nlet f a b (x: bool) = if a then x elif b then true else false")

[<Fact>]
let ``a shadowed collection module does not get isEmpty`` () =
    // a user module named Seq with its own length means something else —
    // with typed results at hand the symbol proves which one this is
    Assert.Empty(findChecked "module Seq =\n    let length (s: string) = 99\nlet f (s: string) = Seq.length s = 0")

[<Fact>]
let ``the genuine List.length still simplifies under the typed gate`` () =
    let src = "let f (xs: int list) = List.length xs = 0"
    assertCheckedSuggestion (findChecked src) src "List.isEmpty xs"

[<Fact>]
let ``a None comparison whose branch reads the payload is a match in disguise`` () =
    // `isSome` + `.Value` is the spelling to avoid; FR0034 binds the payload
    Assert.Empty(findChecked "let f (x: int option) = if x <> None then x.Value + 1 else 0")
    Assert.Empty(findChecked "let f (x: int option) = if x = None then 0 else Option.get x")

    Assert.Empty(
        findChecked
            "let f (x: int option) =\n    if x <> None then\n        let y = x.Value\n        y + 1\n    else\n        0"
    )

[<Fact>]
let ``a None comparison whose branches never read the payload still simplifies`` () =
    let src = "let f (x: int option) = if x <> None then 1 else 0"
    assertCheckedSuggestion (findChecked src) src "x.IsSome"

[<Fact>]
let ``a None comparison on an unannotated parameter keeps the module form`` () =
    // x's type is inferred from its later use; `x.IsSome` there is FS0072
    let src =
        "let f x = let b = x <> None in if b then x |> Option.map ((+) 1) else None"

    assertCheckedSuggestion (findChecked src) src "x |> Option.isSome"

[<Fact>]
let ``Option isSome on a settled receiver becomes the property`` () =
    let src = "let f (x: int option) = Option.isSome x"
    assertCheckedSuggestion (findChecked src) src "x.IsSome"

[<Fact>]
let ``piped Option isNone becomes the property`` () =
    let src = "let f (x: int voption) = x |> ValueOption.isNone"
    assertCheckedSuggestion (findChecked src) src "x.IsNone"

[<Fact>]
let ``a dotted receiver takes the property when its root is settled`` () =
    let src = "type R = { Age: int option }\nlet f (r: R) = Option.isSome r.Age"
    assertCheckedSuggestion (findChecked src) src "r.Age.IsSome"

[<Fact>]
let ``Option isSome on a lambda parameter stays`` () =
    Assert.Empty(findChecked "let f (xs: int option list) = xs |> List.filter (fun x -> Option.isSome x)")

[<Fact>]
let ``a let-bound local is settled by its right-hand side`` () =
    let src =
        "let f (n: int) =\n    let x = if n > 0 then Some n else None\n    Option.isNone x"

    assertCheckedSuggestion (findChecked src) src "x.IsNone"

[<Fact>]
let ``a user module named Option is not FSharp.Core's`` () =
    Assert.Empty(
        findChecked "module Option =\n    let isSome (x: int option) = true\nlet f (x: int option) = Option.isSome x"
    )

[<Fact>]
let ``Option isSome whose branch reads the payload is left to FR0034`` () =
    Assert.Empty(findChecked "let f (x: int option) = if Option.isSome x then x.Value else 0")
