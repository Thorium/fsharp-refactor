module FSharp.Refactor.Tests.TrailingSemicolonTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    TrailingSemicolon.find tree sourceText

let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``a line-ending semicolon is dropped`` () =
    assertPatched "module Test\nlet x = 1;" "module Test\nlet x = 1"

[<Fact>]
let ``blank space before the semicolon goes too`` () =
    assertPatched "module Test\nlet x = 1  ;" "module Test\nlet x = 1"

[<Fact>]
let ``a semicolon before a comment is dropped`` () =
    assertPatched "module Test\nlet x = 1; // note" "module Test\nlet x = 1 // note"

[<Fact>]
let ``a list element separator is kept`` () =
    assertNoSuggestion "module Test\nlet xs = [\n    1;\n    2 ]"

[<Fact>]
let ``an array element separator is kept`` () =
    assertNoSuggestion "module Test\nlet xs = [|\n    1;\n    2 |]"

[<Fact>]
let ``a record field separator is kept`` () =
    assertNoSuggestion "module Test\ntype R = { A: int; B: int }\nlet r = {\n    A = 1;\n    B = 2 }"

[<Fact>]
let ``an anonymous record field separator is kept`` () =
    assertNoSuggestion "module Test\nlet r = {|\n    A = 1;\n    B = 2 |}"

[<Fact>]
let ``an attribute separator is kept`` () =
    assertNoSuggestion "module Test\n[<System.Obsolete;\n  System.Serializable>]\ntype T() = class end"

[<Fact>]
let ``a semicolon inside a string is not a line ending`` () =
    assertNoSuggestion "module Test\nlet s = \"a ; b\""

[<Fact>]
let ``a semicolon inside a string still lets a real one be found`` () =
    assertPatched "module Test\nlet s = \"a ; b\";" "module Test\nlet s = \"a ; b\""

[<Fact>]
let ``a double semicolon is left alone`` () =
    // `;;` terminates an F# Interactive interaction, which is a different thing
    assertNoSuggestion "module Test\nlet x = 1;;"

[<Fact>]
let ``verbose syntax keeps every semicolon`` () =
    // verbose sources need not parse cleanly under the default settings, and
    // that is beside the point: the rule must decline before it looks
    let source = "#light \"off\"\nmodule Test\nlet x = 1;"
    let tree, _, sourceText = tryParseNamed "Test.fs" source
    Assert.Empty(TrailingSemicolon.find tree sourceText)

[<Fact>]
let ``a mid-line semicolon is left alone`` () =
    assertNoSuggestion "module Test\nlet f () = printfn \"a\"; printfn \"b\""

[<Fact>]
let ``a semicolon inside a computation expression is kept`` () =
    // proven: `seq { yield 1;` / `    yield 2;` / `  yield 3 }` parses and the
    // same lines without the semicolons do not, so inside a CE the `;` can be
    // holding the layout together
    assertNoSuggestion
        "module Test
let f () = async {
    printfn \"a\";
    return 1 }"

[<Fact>]
let ``a semicolon ending a line inside a multi-line string is untouched`` () =
    // The reason this rule lexes rather than scanning for ";\n": here the
    // text really does have a semicolon at the end of a line, and deleting it
    // would silently edit the string's contents.
    assertNoSuggestion "module Test\nlet sql = \"\"\"\nSELECT a;\nSELECT b\"\"\""

[<Fact>]
let ``a semicolon ending a comment is untouched`` () =
    assertNoSuggestion "module Test\n// a note about the ; character;\nlet x = 1"

[<Fact>]
let ``a file with no semicolons at all is skipped cheaply`` () =
    assertNoSuggestion "module Test\nlet f x = x + 1\nlet g y = y * 2"

[<Fact>]
let ``a list pattern separator is kept`` () =
    // from the corpus: AstIndex.replay never calls WalkPat, so list PATTERNS
    // were unprotected and their separators were stripped
    assertNoSuggestion "module Test\nlet f x =\n    match x with\n    | [ a;\n        b ] -> a + b\n    | _ -> 0"

[<Fact>]
let ``a record type definition field separator is kept`` () =
    assertNoSuggestion "module Test\ntype R = {\n    Host: int;\n    Customer: string\n}"

[<Fact>]
let ``a list pattern nested inside a union case keeps its separator`` () =
    // the SQLProvider shape: the list is the third argument of an active
    // pattern, not the clause pattern itself
    assertNoSuggestion
        "module Test\ntype T = C of int * int * int list\nlet f x =\n    match x with\n    | C(a, b, [ p;\n                q ]) -> a + b + p + q\n    | _ -> 0"

[<Fact>]
let ``a list pattern separator followed by trailing space is kept`` () =
    // the real SQLProvider line ends "source; " - trailing blank after the ;
    assertNoSuggestion
        "module Test\ntype T = C of int * int * int list\nlet f x =\n    match x with\n    | C(a, b, [ p; \n                q ]) -> a + b + p + q\n    | _ -> 0"


[<Fact>]
let ``a list pattern inside an object expression keeps its separator`` () =
    // The SQLProvider shape. The index lifts object-expression members, which
    // the SDK walker skips, but it used to lift only their EXPRESSIONS — so
    // the tokenizer saw this `;` while the pattern making it a separator was
    // missing, and the rule stripped it.
    assertNoSuggestion (
        "module Test\n"
        + "type IThing =\n"
        + "    abstract Pick: int list -> int\n"
        + "let make () =\n"
        + "    { new IThing with\n"
        + "        member _.Pick xs =\n"
        + "            match xs with\n"
        + "            | [ p;\n"
        + "                q ] -> p + q\n"
        + "            | _ -> 0 }"
    )

[<Fact>]
let ``semicolons holding a misindented list together are kept`` () =
    // verified against fsi: with the semicolons this is [1; 2; 3; 4]; without
    // them the misaligned lines read as function application (FS0003)
    assertNoSuggestion "module Test\nlet a, b, c, d = 1, 2, 3, 4\nlet items = [ a;\n    b; c;\n  d ]"

[<Fact>]
let ``a semicolon before a more indented line stays`` () =
    // without the `;` the deeper line continues the application: printf "a" printf "b"
    assertNoSuggestion "module Test\nlet f () =\n    printf \"a\";\n      printf \"b\""
