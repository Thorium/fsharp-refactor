module FSharp.Refactor.Tests.RedundantParensTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    RedundantParens.find tree sourceText

let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        assertParses "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``a line aligned past the argument keeps the parens`` () =
    // the `(flags = 1` block's second line is aligned under text after
    // the argument; one character shorter, it would stand offside
    assertNoSuggestion (
        fsharp
            """
            module Test
            let g (x: int) = x > 0
            let f (x: int) (flags: int) =
                g (x) && (flags = 1
                          || flags = 2)
            """
    )

[<Fact>]
let ``list literal argument loses its parens`` () =
    assertPatched "module Test\nlet m = List.max([ 4; 3 ])" "module Test\nlet m = List.max [ 4; 3 ]"

[<Fact>]
let ``identifier argument with a space keeps one space`` () =
    assertPatched
        "module Test\nlet f (s: string) = String.length (s)"
        "module Test\nlet f (s: string) = String.length s"

[<Fact>]
let ``adjacent call gains a separating space`` () =
    assertPatched "module Test\nlet f (s: string) = String.length(s)" "module Test\nlet f (s: string) = String.length s"

[<Fact>]
let ``string literal argument loses its parens`` () =
    assertPatched "module Test\nlet f g = g(\"hi\")" "module Test\nlet f g = g \"hi\""

[<Fact>]
let ``dotted path argument loses its parens`` () =
    assertPatched
        (fsharp
            """
            module Test
            type R = { Items: int list }
            let f (r: R) = List.length(r.Items)
            """)
        (fsharp
            """
            module Test
            type R = { Items: int list }
            let f (r: R) = List.length r.Items
            """)

[<Fact>]
let ``tuple argument is a method argument list and stays`` () =
    assertNoSuggestion "module Test\nlet c = System.String.Compare(\"a\", \"b\")"

[<Fact>]
let ``application argument keeps its parens`` () =
    // `f (g x)` without parens would become a three-argument application
    assertNoSuggestion "module Test\nlet f g (x: int) = List.singleton(g x)"

[<Fact>]
let ``negative constant keeps its parens`` () =
    assertNoSuggestion "module Test\nlet f = abs(-1)"

[<Fact>]
let ``projection continuation keeps its parens`` () =
    // review-class regression: `string s.Length` would bind differently
    assertNoSuggestion "module Test\nlet f (s: string) = string(s).Length"

[<Fact>]
let ``instance method call keeps its parens`` () =
    // style guide: method calls parenthesize their arguments
    assertNoSuggestion "module Test\nlet f (s: string) (t: string) = s.Contains(t)"
// ---- harder cases ----

[<Fact>]
let ``unary plus constant keeps its parens`` () =
    // `f +1` would re-parse as binary addition
    assertNoSuggestion "module Test\nlet f = abs(+1)"

[<Fact>]
let ``union case constructor loses its parens`` () =
    assertPatched "module Test\nlet s = Some(1)" "module Test\nlet s = Some 1"

[<Fact>]
let ``comprehension argument loses its parens`` () =
    assertPatched
        "module Test\nlet m = List.max([ for i in 1..3 -> i ])"
        "module Test\nlet m = List.max [ for i in 1..3 -> i ]"

[<Fact>]
let ``curried continuation still parses after removal`` () =
    assertPatched "module Test\nlet r = List.map(id) [ 1; 2 ]" "module Test\nlet r = List.map id [ 1; 2 ]"

[<Fact>]
let ``static method call keeps its parens`` () =
    // real-world corpus regression: File.ReadAllText(path)-style .NET calls
    // are method calls, and the style guide parenthesizes those
    assertNoSuggestion (
        fsharp
            """
            module Test
            let t (p: string) = System.IO.Path.GetFileName(p)
            """
    )

[<Fact>]
let ``constructor call keeps its parens`` () =
    // StringValues("x")-style constructors read as .NET interop, not F#
    // function application
    assertNoSuggestion (
        fsharp
            """
            module Test
            type W(x: int) =
                member _.V = x
            let w (i: int) = W(i)
            """
    )

[<Fact>]
let ``qualified constructor call keeps its parens`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let b (s: string) = System.Text.StringBuilder(s)
            """
    )

[<Fact>]
let ``doubly parenthesized operator reference keeps one paren pair`` () =
    // the operator reference's own parens are part of its range, so only the
    // redundant outer pair is removed
    assertPatched "module Test\nlet r = List.map((+)) [ 1 ]" "module Test\nlet r = List.map (+) [ 1 ]"

[<Fact>]
let ``operator method call keeps its parens`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (x: float32) = TorchSharp.Scalar.op_Implicit(x)
            """
    )

[<Fact>]
let ``an application that is a tuple element keeps its parens`` () =
    // ValueSome(x), y bare parses identically, but a comma beside a
    // spaced application makes the reader check who owns it
    Assert.Empty(
        findIn
            "module Test
let f (score: float) (ts: string) = ValueSome(score), ts"
    )

[<Fact>]
let ``the same application outside a tuple still sheds them`` () =
    Assert.NotEmpty(
        findIn
            "module Test
let f (score: float) = ValueSome(score)"
    )

[<Fact>]
let ``a body indented past the argument's start but short of its end is no alignment`` () =
    assertPatched
        (fsharp
            """
            module Test
            let g (x: int) = x > 0
            let f (x: int) =
                if g (x) then
                    1
                else
                    2
            """)
        (fsharp
            """
            module Test
            let g (x: int) = x > 0
            let f (x: int) =
                if g x then
                    1
                else
                    2
            """)

[<Fact>]
let ``the bare argument touching the next token gets one space, and no more`` () =
    // `not(true)with` is legal; the bare `true` would read `truewith`
    assertPatched
        (fsharp
            """
            module Test
            let f () =
                match not(true)with
                | true -> 1
                | false -> 2
            """)
        (fsharp
            """
            module Test
            let f () =
                match not true with
                | true -> 1
                | false -> 2
            """)
