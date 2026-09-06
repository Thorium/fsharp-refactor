module FSharp.Refactor.Tests.PatternParensTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    PatternParens.find tree sourceText

let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``a parenthesized clause pattern loses its parens`` () =
    assertPatched
        "module Test\nlet f x = match x with | (Some y) -> y | None -> 0"
        "module Test\nlet f x = match x with | Some y -> y | None -> 0"

[<Fact>]
let ``a tuple clause pattern keeps its parens`` () =
    // `| (a, b) ->` groups the tuple at a glance; `| a, b ->` makes the reader
    // work it out, which is the opposite of what dropping parens is for
    assertNoSuggestion "module Test\nlet f x = match x with | (a, b) -> a + b"

[<Fact>]
let ``a type-test clause pattern loses its parens`` () =
    assertPatched
        "module Test\nlet f (x: obj) = match x with | (:? string) -> 1 | _ -> 0"
        "module Test\nlet f (x: obj) = match x with | :? string -> 1 | _ -> 0"

[<Fact>]
let ``an atomic union-case argument loses its parens`` () =
    assertPatched
        "module Test\nlet f x = match x with | Some (y) -> y | None -> 0"
        "module Test\nlet f x = match x with | Some y -> y | None -> 0"

[<Fact>]
let ``a let parameter loses its parens`` () =
    assertPatched "module Test\nlet f (x) = x" "module Test\nlet f x = x"

[<Fact>]
let ``a nested union case keeps its parens`` () =
    // `Some (Some x)` must not become the nonsense `Some Some x`
    assertNoSuggestion "module Test\nlet f x = match x with | Some (Some y) -> y | _ -> 0"

[<Fact>]
let ``a tuple inside a union case keeps its parens`` () =
    // `Some (x, y)` is one case carrying a tuple; `Some x, y` is a pair
    assertNoSuggestion "module Test\ntype T = C of int * int\nlet f x = match x with | C (a, b) -> a + b"

[<Fact>]
let ``an annotated parameter keeps its parens`` () =
    assertNoSuggestion "module Test\nlet f (x: int) = x"

[<Fact>]
let ``a member parameter keeps its parens`` () =
    // `member _.M(x)` and `member _.M x` agree for one parameter and disagree
    // otherwise; a method's shape is not a formatting concern
    assertNoSuggestion "module Test\ntype T() =\n    member _.M(x) = x"

[<Fact>]
let ``a negative constant as a whole clause pattern is fine bare`` () =
    // `| -1 -> 0` parses as the constant, there being no left operand
    assertPatched
        "module Test\nlet f x = match x with | (-1) -> 0 | _ -> 1"
        "module Test\nlet f x = match x with | -1 -> 0 | _ -> 1"

[<Fact>]
let ``a negative constant inside a union case keeps its parens`` () =
    // `Some (-1)` bare would read as the subtraction `Some - 1`
    assertNoSuggestion "module Test\nlet f x = match x with | Some (-1) -> 0 | _ -> 1"

[<Fact>]
let ``the unit pattern is not parens around something`` () =
    // `()` parses as parens around the unit constant, but dropping them turns
    // the function `let f () = 1` into the value `let f = 1`
    assertNoSuggestion "module Test\nlet f () = 1"

[<Fact>]
let ``a unit member parameter is left alone too`` () =
    assertNoSuggestion "module Test\ntype T() =\n    member _.M() = 1"

[<Fact>]
let ``a typed clause pattern keeps its parens`` () =
    // from the corpus: `| (request: HttpRequestMessage) when ... ->`.
    // Bare, `| request: HttpRequestMessage when ... ->` does not parse.
    assertNoSuggestion
        "module Test\nlet f (x: obj) =\n    match x with\n    | (s: string) when s.Length > 0 -> 1\n    | _ -> 0"

[<Fact>]
let ``adjacent parameters gain the space the parens were providing`` () =
    // `let f (a)(b: int)` bare would be `a(b: int)` - an application, not two
    // parameters
    assertPatched "module Test\nlet f (a)(b: int) = b" "module Test\nlet f a (b: int) = b"

[<Fact>]
let ``a parameter glued to its function name gains a space`` () =
    assertPatched "module Test\nlet f(x) = x" "module Test\nlet f x = x"

[<Fact>]
let ``a wildcard argument of a union case keeps its parens without types`` () =
    // `Ctor(_)` may be a case that takes no data, where `Ctor _` is an error;
    // the typed FR0088 owns that shape
    Assert.Empty(findIn "module Test\ntype K =\n    | Ctor\nlet f k =\n    match k with\n    | Ctor(_) -> 0")

[<Fact>]
let ``a function head still loses the parens around its wildcard parameter`` () =
    // the union-case exemption keys on the capital: `f` is a function
    match findIn "module Test\nlet f (_) = 1" with
    | [ s ] -> Assert.Equal("_", s.ReplacementText)
    | other -> failwithf "Expected one paren cleanup, got %A" other

[<Fact>]
let ``an object expression member keeps the parens around its parameter`` () =
    // FSharp.CloudAgent and Mibo: `{ new I with member _.M(x) = ... }`
    Assert.Empty(
        findIn
            "module Test\ntype I =\n    abstract M: int -> int\nlet make () =\n    { new I with\n        member _.M(x) = x + 1 }"
    )
