module FSharp.Refactor.Tests.TypeSyntaxTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private parensIn (source: string) =
    let tree, sourceText = parse source
    TypeSyntax.findRedundantParens tree sourceText

let private abbreviationsIn (source: string) =
    let tree, sourceText = parse source
    TypeSyntax.findAbbreviations tree sourceText

let private assertPatched (finder: string -> TypeSyntax.Suggestion list) (source: string) (expectedPatched: string) =
    match finder source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

// --- FR0097 ---

[<Fact>]
let ``a parenthesized named type loses its parens`` () =
    assertPatched parensIn "module Test\nlet f (x: (int)) = x" "module Test\nlet f (x: int) = x"

[<Fact>]
let ``the bare type touching the next token gets one space, and no more`` () =
    // `(string)list` is legal; bare, it would read `stringlist`
    assertPatched parensIn "module Test\nlet xs: (string)list = []" "module Test\nlet xs: string list = []"

[<Fact>]
let ``a parenthesized type argument loses its parens`` () =
    assertPatched parensIn "module Test\nlet xs: (string) list = []" "module Test\nlet xs: string list = []"

[<Fact>]
let ``a function type keeps its parens`` () =
    // `(int -> int) list` and `int -> int list` are different types
    Assert.Empty(parensIn "module Test\nlet xs: (int -> int) list = []")

[<Fact>]
let ``a tuple type keeps its parens`` () =
    Assert.Empty(parensIn "module Test\nlet xs: (int * int) list = []")

// --- FR0098 ---

[<Fact>]
let ``System.Int32 is int`` () =
    assertPatched abbreviationsIn "module Test\nlet f (x: System.Int32) = x" "module Test\nlet f (x: int) = x"

[<Fact>]
let ``System.String is string`` () =
    assertPatched abbreviationsIn "module Test\nlet s: System.String = \"\"" "module Test\nlet s: string = \"\""

[<Fact>]
let ``System.Object is obj`` () =
    assertPatched abbreviationsIn "module Test\nlet o: System.Object = null" "module Test\nlet o: obj = null"

[<Fact>]
let ``a bare Int32 is left alone`` () =
    // what it resolves to depends on the opens and on what the file declares
    Assert.Empty(abbreviationsIn "module Test\nopen System\nlet f (x: Int32) = x")

[<Fact>]
let ``System.Void is left alone`` () =
    // unit is not its abbreviation; the two differ in signatures
    Assert.Empty(abbreviationsIn "module Test\nlet f (x: System.Void) = x")

[<Fact>]
let ``an unrelated System type is left alone`` () =
    Assert.Empty(abbreviationsIn "module Test\nlet g: System.Guid = System.Guid.Empty")
