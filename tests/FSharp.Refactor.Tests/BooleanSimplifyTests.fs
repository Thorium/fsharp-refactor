module FSharp.Refactor.Tests.BooleanSimplifyTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    BooleanSimplify.find tree sourceText

let private assertRewrite (source: string) (expected: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expected, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- FR0108 identity elements ----

[<Fact>]
let ``and true drops the literal`` () =
    assertRewrite "module Test\nlet f (x: int) = x > 1 && true" "x > 1"

[<Fact>]
let ``true and drops the literal`` () =
    assertRewrite "module Test\nlet f (x: int) = true && x > 1" "x > 1"

[<Fact>]
let ``or false drops the literal`` () =
    assertRewrite "module Test\nlet f (x: int) = x > 1 || false" "x > 1"

[<Fact>]
let ``false or drops the literal`` () =
    assertRewrite "module Test\nlet f (x: int) = false || x > 1" "x > 1"

[<Fact>]
let ``and false is left alone: the operand still evaluates`` () =
    Assert.Empty(findIn "module Test\nlet f (g: unit -> bool) = g () && false")

[<Fact>]
let ``true or is left alone: the operand is skipped`` () =
    Assert.Empty(findIn "module Test\nlet f (g: unit -> bool) = true || g ()")

[<Fact>]
let ``the identity fires inside a query where clause`` () =
    // a strictly simpler tree of already-accepted shapes: safe in queries
    match
        findIn
            "module Test\nopen System.Linq\nlet f (xs: int list) =\n    query {\n        for x in xs.AsQueryable() do\n            where (x > 2 && true)\n            select x\n    }"
    with
    | [ s ] -> Assert.Equal("x > 2", s.ReplacementText)
    | other -> failwithf "Expected one suggestion in the query, got %A" other

// ---- FR0109 idempotent duplicates ----

[<Fact>]
let ``a duplicated comparison collapses`` () =
    assertRewrite "module Test\nlet f (x: int) = x > 1 || x > 1" "x > 1"

[<Fact>]
let ``a duplicated property chain collapses`` () =
    assertRewrite "module Test\nlet f (s: string) = s.Length = 0 && s.Length = 0" "s.Length = 0"

[<Fact>]
let ``a negated duplicate collapses too`` () =
    assertRewrite "module Test\nlet f (b: bool) = not b || not b" "not b"

[<Fact>]
let ``the retry idiom is deliberately untouched`` () =
    // tryConnect() || tryConnect() retries on purpose; a call may lean on
    // its effects, so duplicates with calls inside never collapse
    Assert.Empty(findIn "module Test\nlet f (tryConnect: unit -> bool) = tryConnect () || tryConnect ()")

[<Fact>]
let ``a duplicated function application is untouched`` () =
    Assert.Empty(findIn "module Test\nlet f (p: int -> bool) (x: int) = p x && p x")

[<Fact>]
let ``different operands stay`` () =
    Assert.Empty(findIn "module Test\nlet f (x: int) (y: int) = x > 1 || y > 1")

// ---- FR0108: a call whose type the literal pins ----

[<Fact>]
let ``a call bound as a value keeps the literal that types it`` () =
    // FSharpPlus: `let _111 = parse "true" && true` — `parse` is SRTP and
    // the `&& true` is what makes its result a bool
    Assert.Empty(
        findIn "module Test\nlet inline parse (s: string) = Unchecked.defaultof<'a>\nlet v = parse \"true\" && true"
    )

[<Fact>]
let ``a call under an if still drops the literal`` () =
    assertRewrite "module Test\nlet f (g: int -> bool) = if g 1 && true then 1 else 2" "g 1"

[<Fact>]
let ``a comparison bound as a value still drops the literal`` () =
    assertRewrite "module Test\nlet f (x: int) =\n    let v = x > 1 && true\n    v" "x > 1"

[<Fact>]
let ``the kept operand touching a token beside it gets one space there, and no more`` () =
    // `if(true) && true then` is legal; the kept `true` would read `iftrue`
    assertRewrite "module Test\nlet f () = if(true) && true then 1 else 2" " true"

    assertRewrite
        "module Test\nlet f (x: int) =\n    match(true)&& x <= 0 with\n    | true -> 1\n    | false -> 2"
        " x <= 0"

    assertRewrite "module Test\nlet f (x: int) = (x <= 0 && true)" "x <= 0"
