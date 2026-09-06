module FSharp.Refactor.Tests.CompositionTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    // typed now: nothing syntactic separates a module function from a method,
    // and a method cannot be composed by name
    let tree, sourceText, check = parseAndCheck source
    Composition.find tree sourceText check

let private assertSingleSuggestion (source: string) (expectedReplacement: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``pipeline lambda becomes composition`` () =
    assertSingleSuggestion "module Test\nlet f g h xs = xs |> List.map (fun x -> x |> g |> h)" "g >> h"

[<Fact>]
let ``nested application lambda becomes composition`` () =
    assertSingleSuggestion "module Test\nlet f g h xs = xs |> List.map (fun x -> h (g x))" "g >> h"

[<Fact>]
let ``three-stage pipeline`` () =
    assertSingleSuggestion "module Test\nlet f g h k xs = xs |> List.map (fun x -> x |> g |> h |> k)" "g >> h >> k"

[<Fact>]
let ``partial application stages`` () =
    assertSingleSuggestion
        "module Test\nlet f g h xs = xs |> List.map (fun x -> x |> List.map g |> List.filter h)"
        "List.map g >> List.filter h"

[<Fact>]
let ``nested application with partial application`` () =
    assertSingleSuggestion "module Test\nlet f g h xs = xs |> List.map (fun x -> List.map g (h x))" "h >> List.map g"

[<Fact>]
let ``operator-section stage stays bare`` () =
    assertSingleSuggestion "module Test\nlet f g xs = xs |> List.map (fun x -> x |> g |> (+) 1)" "g >> (+) 1"

[<Fact>]
let ``stage referencing the parameter is not rewritten`` () =
    assertNoSuggestion "module Test\nlet f g xs = xs |> List.map (fun x -> x |> g |> List.append x)"

[<Fact>]
let ``single stage is not rewritten`` () =
    // eta-reduction territory, not composition
    assertNoSuggestion "module Test\nlet f g xs = xs |> List.map (fun x -> g x)"

[<Fact>]
let ``let-bound lambda is not rewritten`` () =
    // rewriting `let h = fun x -> ...` risks the value restriction
    assertNoSuggestion "module Test\nlet h = fun x -> x |> List.map id |> List.length"

[<Fact>]
let ``two parameters are not rewritten`` () =
    assertNoSuggestion "module Test\nlet f g h xs = xs |> List.mapi (fun i x -> x |> g |> h i)"

[<Fact>]
let ``annotated parameter is not rewritten`` () =
    // the annotation would be lost in the rewrite
    assertNoSuggestion "module Test\nlet f g h xs = xs |> List.map (fun (x: int) -> x |> g |> h)"

[<Fact>]
let ``pipeline not starting from the parameter is not rewritten`` () =
    assertNoSuggestion "module Test\nlet f g h y xs = xs |> List.map (fun x -> y |> g |> h)"

[<Fact>]
let ``infix body is not decomposed into an invalid stage`` () =
    // review regression: `(1 +) >> g` is not valid F#
    assertNoSuggestion "module Test\nlet f g xs = xs |> List.map (fun x -> g (1 + x))"

[<Fact>]
let ``parenthesized let-bound lambda is not rewritten`` () =
    // review regression: the composition form falls under the value restriction
    assertNoSuggestion "module Test\nlet h = (fun x -> x |> Seq.map id |> Seq.toList)"

[<Fact>]
let ``an operator stage is left as a lambda`` () =
    // prefix negation is `~-` in the tree but `-` in the source, so the
    // composition came out as `- >> d.AddDays`: not an expression at all,
    // and it took the rest of the file's parse with it. `(~-) >> d.AddDays`
    // would compile but reads worse than the lambda it replaces
    assertNoSuggestion
        "module Test\nopen System\nlet f (d: DateOnly) count =\n    Array.init count (fun i -> d.AddDays -i)"

[<Fact>]
let ``an operator the author already parenthesised still composes`` () =
    // `(+) 1` is an ordinary application as written, and `(+) 1 >> string`
    // is valid F# — only the BARE operator form is the problem
    assertSingleSuggestion "module Test\nlet f xs = List.map (fun x -> string ((+) 1 x)) xs" "(+) 1 >> string"

[<Fact>]
let ``a method stage is left as a lambda`` () =
    // a .NET method is not first class: the call compiles, the composition
    // does not mean the same thing. Fable's Fable2Babel lost a file to
    // `SwitchCase.switchCase`, a static member with optional parameters
    assertNoSuggestion
        "module Test\ntype Holder =\n    static member make(?a: int, ?b: int) = defaultArg a 0 + defaultArg b 0\nlet f (xs: int list) = List.map (fun x -> Holder.make (abs x)) xs"

[<Fact>]
let ``a parenthesised negation argument is left as a lambda`` () =
    // nu's GameTime: `GameTime.unary (fun updates -> UpdateTime (-updates))`
    // composed to `- >> UpdateTime`, which does not parse
    assertNoSuggestion
        "module Test\ntype T = UpdateTime of int64\nlet f (xs: int64 list) = List.map (fun updates -> UpdateTime (-updates)) xs"

[<Fact>]
let ``a lambda laid out over several lines is left as it is`` () =
    // fantomas Context.fs: a readable five-line lambda became a 170-column
    // composition
    assertNoSuggestion
        "module Test\nlet firstRangePerLine (xs: int list) = xs\nlet createAbsoluteAndOffsetOverridesBasedOnFirst (xs: int list) = xs\nlet f (groups: int list list) =\n    groups\n    |> List.collect (fun ranges ->\n        ranges\n        |> List.map (fun r -> r + 1)\n        |> firstRangePerLine\n        |> createAbsoluteAndOffsetOverridesBasedOnFirst)"

[<Fact>]
let ``a composition that would pass 100 columns is left as a lambda`` () =
    assertNoSuggestion
        "module Test\nlet firstRangePerLine (xs: int list) = xs\nlet createAbsoluteAndOffsetOverridesBasedOnFirst (xs: int list) = xs\nlet f (groups: int list list) =\n    groups |> List.collect (fun ranges -> ranges |> List.map (fun r -> r + 1) |> firstRangePerLine |> createAbsoluteAndOffsetOverridesBasedOnFirst)"

[<Fact>]
let ``a composition that stays within 100 columns still fires`` () =
    assertSingleSuggestion
        "module Test\nlet firstRangePerLine (xs: int list) = xs\nlet f (groups: int list list) =\n    groups |> List.collect (fun ranges -> ranges |> List.map (fun r -> r + 1) |> firstRangePerLine)"
        "List.map (fun r -> r + 1) >> firstRangePerLine"

[<Fact>]
let ``a lambda handed to an InlineIfLambda parameter is not composed`` () =
    // Mibo's filterA and section: the callee inlines the lambda; a
    // composition in its place is a closure it can no longer inline
    let tree, sourceText, check =
        parseAndCheck
            "module Test\nlet inline apply ([<InlineIfLambda>] f: int -> int) (x: int) = f x\nlet g (a: int -> int) (b: int -> int) = apply (fun v -> b (a v)) 1"

    Assert.Empty(Composition.find tree sourceText check)

[<Fact>]
let ``a lambda handed to an ordinary parameter is still composed`` () =
    let tree, sourceText, check =
        parseAndCheck
            "module Test\nlet apply (f: int -> int) (x: int) = f x\nlet g (a: int -> int) (b: int -> int) = apply (fun v -> b (a v)) 1"

    Assert.NotEmpty(Composition.find tree sourceText check)
