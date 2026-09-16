module FSharp.Refactor.Tests.MethodCallParensTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    MethodCallParens.find tree sourceText

let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``instance method call loses its parens`` () =
    assertPatched
        "module Test\nlet f (s: string) = s.Contains(\"x\")"
        "module Test\nlet f (s: string) = s.Contains \"x\""

[<Fact>]
let ``char argument loses its parens`` () =
    assertPatched
        "module Test\nlet f (sb: System.Text.StringBuilder) = sb.Append('c')"
        "module Test\nlet f (sb: System.Text.StringBuilder) = sb.Append 'c'"

[<Fact>]
let ``method call on a projected receiver loses its parens`` () =
    assertPatched
        "module Test\nlet f (xs: string list) = xs.Head.Trim(' ')"
        "module Test\nlet f (xs: string list) = xs.Head.Trim ' '"

[<Fact>]
let ``a spaced call keeps one space`` () =
    assertPatched
        "module Test\nlet f (s: string) = s.Contains (\"x\")"
        "module Test\nlet f (s: string) = s.Contains \"x\""

// --- the same-line continuation guard ---

[<Fact>]
let ``an infix continuation on the same line keeps the parens`` () =
    // `s.Contains "x" <> false` reads as though the argument were `"x" <> false`
    assertNoSuggestion "module Test\nlet f (s: string) = s.Contains(\"x\") <> false"

[<Fact>]
let ``a pipe on the same line keeps the parens`` () =
    assertNoSuggestion "module Test\nlet f (s: string) = s.StartsWith(\"x\") |> ignore"

[<Fact>]
let ``a continuation on a later line is clear enough to fix`` () =
    assertPatched
        "module Test\nlet f (s: string) =\n    s.Contains(\"x\")\n    |> ignore"
        "module Test\nlet f (s: string) =\n    s.Contains \"x\"\n    |> ignore"

[<Fact>]
let ``a structural parent on the same line still gets fixed`` () =
    // `if`/`match`/list elements read fine bare — only applications are the
    // shapes where dropping parens changes how the line reads
    assertPatched
        "module Test\nlet f (s: string) = if s.Contains(\"x\") then 1 else 2"
        "module Test\nlet f (s: string) = if s.Contains \"x\" then 1 else 2"

[<Fact>]
let ``a line aligned past the argument keeps the parens`` () =
    // fparsec's CharParsers.fs: two characters shorter, the `(flags <- ...`
    // block's continuation line stood right of `flags` and the block
    // re-parsed as an application
    assertNoSuggestion
        "module Test\nlet f (s: string) (flags: int) =\n    let mutable flags = flags\n    s.Contains(\"inf\") && (flags <- flags ||| 1\n                          true)"

[<Fact>]
let ``a deeper line that is a body, not an alignment, still gets fixed`` () =
    assertPatched
        "module Test\nlet f (s: string) =\n    if s.Contains(\"x\") then\n        1\n    else\n        2"
        "module Test\nlet f (s: string) =\n    if s.Contains \"x\" then\n        1\n    else\n        2"

// --- constructors and static paths stay untouched ---

[<Fact>]
let ``a constructor keeps its parens`` () =
    // `new Uri "x"` does not compile: these parens are load-bearing
    assertNoSuggestion "module Test\nlet u = System.Uri(\"x\")"

[<Fact>]
let ``an explicit new keeps its parens`` () =
    assertNoSuggestion "module Test\nlet u = new System.Uri(\"x\")"

[<Fact>]
let ``an uppercase-headed static path is left alone`` () =
    // indistinguishable from a constructor without type information
    assertNoSuggestion "module Test\nlet t = System.IO.File.ReadAllText(\"x\")"

// --- inherited safety rules ---

[<Fact>]
let ``a multi-argument call keeps its parens`` () =
    assertNoSuggestion "module Test\nlet f (s: string) = s.Substring(1, 2)"

[<Fact>]
let ``a negative constant keeps its parens`` () =
    assertNoSuggestion "module Test\nlet f (s: string) = s.PadLeft(-1)"

[<Fact>]
let ``a projection keeps the parens`` () =
    assertNoSuggestion "module Test\nlet f (s: string) = s.Contains(\"x\").ToString()"

[<Fact>]
let ``an applied argument keeps its parens`` () =
    assertNoSuggestion "module Test\nlet f (s: string) (g: int -> int) = s.PadLeft(g 1)"

// --- no overlap with FR0013, which owns function calls ---

[<Fact>]
let ``function calls belong to FR0013, not here`` () =
    assertNoSuggestion "module Test\nlet m = List.max([ 4; 3 ])"
    assertNoSuggestion "module Test\nlet a = Some(\"x\")"

[<Fact>]
let ``FR0013 does not also claim method calls`` () =
    let tree, sourceText = parse "module Test\nlet f (s: string) = s.Contains(\"x\")"
    Assert.Empty(RedundantParens.find tree sourceText)

[<Fact>]
let ``a call feeding the dynamic operator keeps its parens`` () =
    // from the corpus: `hub.Clients.OthersInGroup(roomId)?visitorJoin(user)`.
    // Bare, `roomId` binds to the `?` and the file stops parsing.
    assertNoSuggestion "module Test\nlet f (hub: obj) (roomId: string) = hub?Clients?OthersInGroup(roomId)?visitorJoin"

[<Fact>]
let ``a method call that is a tuple element keeps its parens`` () =
    Assert.Empty(
        findIn
            "module Test
let f (s: string) (y: int) = s.Trim(' '), y"
    )

[<Fact>]
let ``the same method call outside a tuple still sheds them`` () =
    Assert.NotEmpty(
        findIn
            "module Test
let f (s: string) = s.Trim(' ')"
    )

[<Fact>]
let ``a parenthesised unit argument keeps its parens`` () =
    // `x.log (())` passes unit as a value to a generic parameter; bare,
    // `x.log ()` is a call with no arguments — a different thing
    assertNoSuggestion
        "module Test\ntype T() =\n    member x.log<'t> (v: 't, tag: string) = ()\n    member x.Exit() = x.log (())"

[<Fact>]
let ``a call in a shorthand lambda keeps its parens`` () =
    // welendus's `configureEndpoint _.WithName("x").WithGroupName(g)`: the
    // `_.` body must stay atomic, or the bare argument applies the lambda
    assertNoSuggestion
        "module Test\ntype E() =\n    member x.WithName(n: string) = x\n    member x.WithGroupName(g: string) = x\nlet configure (f: E -> E) (e: E) = f e\nlet r (e: E) = e |> configure _.WithName(\"a\").WithGroupName(\"g\")"
