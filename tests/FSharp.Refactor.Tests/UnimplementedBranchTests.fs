module FSharp.Refactor.Tests.UnimplementedBranchTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    UnimplementedBranch.find tree sourceText

let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one unimplemented-branch suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

/// The shape this rule exists for: siblings compute, one branch admits it is
/// unfinished and hands back something a caller cannot tell from a result.
let private dispatch (lastBranch: string) =
    "module Test\n"
    + "type M = Gauss of int | Seidel of int | Jordan\n"
    + "let f (x: int) = Some x\n"
    + "let g (x: int) = Some x\n"
    + "let solve m =\n"
    + "    match m with\n"
    + "    | Gauss c -> f c\n"
    + "    | Seidel c -> g c\n"
    + lastBranch

[<Fact>]
let ``an unfinished branch returning None is reported`` () =
    assertPatched
        (dispatch "    | Jordan ->\n        // Not supported yet\n        None")
        (dispatch "    | Jordan ->\n        // Not supported yet\n        raise (System.NotImplementedException())")

[<Fact>]
let ``not implemented yet is recognised too`` () =
    assertPatched
        (dispatch "    | Jordan ->\n        // not implemented yet\n        None")
        (dispatch "    | Jordan ->\n        // not implemented yet\n        raise (System.NotImplementedException())")

[<Fact>]
let ``a block comment accuses just as well`` () =
    assertPatched
        (dispatch "    | Jordan ->\n        (* unimplemented *)\n        None")
        (dispatch "    | Jordan ->\n        (* unimplemented *)\n        raise (System.NotImplementedException())")

[<Fact>]
let ``an empty string stand-in is reported`` () =
    let source =
        "module Test\ntype M = A | B | C\nlet name (x: int) = string x\nlet f m =\n    match m with\n    | A -> name 1\n    | B -> name 2\n    | C ->\n        // not supported\n        \"\""

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

// --- what must NOT fire ---

[<Fact>]
let ``a bare None branch with no comment is idiomatic and left alone`` () =
    // `| Unknown -> None` is how option-returning dispatch is written
    assertNoSuggestion (dispatch "    | Jordan -> None")

[<Fact>]
let ``a TODO about something else does not accuse the branch`` () =
    // the comment is above the match, not inside the branch
    assertNoSuggestion (
        "module Test\ntype M = Gauss of int | Jordan\nlet f (x: int) = Some x\n"
        + "// TODO: cache these results\nlet solve m =\n    match m with\n    | Gauss c -> f c\n    | Jordan -> None"
    )

[<Fact>]
let ``a table of constants is data, not a stub`` () =
    // no sibling computes anything, so a constant branch is just a value
    assertNoSuggestion
        "module Test\ntype M = A | B | C\nlet f m =\n    match m with\n    | A -> 1\n    | B -> 2\n    | C ->\n        // not supported\n        0"

[<Fact>]
let ``a branch that does real work is untouched`` () =
    assertNoSuggestion (dispatch "    | Jordan ->\n        // not supported yet\n        f 3")

[<Fact>]
let ``null with a stub comment is accused`` () =
    let source =
        "module Test\ntype M = A | B\nlet f (x: int) : string = string x\nlet g m =\n    match m with\n    | A -> f 1\n    | B ->\n        // not implemented\n        null"

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion for null, got %A" other

[<Fact>]
let ``false with a stub comment is accused`` () =
    let source =
        "module Test\ntype M = A | B\nlet f (x: int) = x > 0\nlet g m =\n    match m with\n    | A -> f 1\n    | B ->\n        // Not supported yet\n        false"

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion for false, got %A" other

[<Fact>]
let ``false without a comment is an ordinary value`` () =
    Assert.Empty(
        findIn
            "module Test\ntype M = A | B\nlet f (x: int) = x > 0\nlet g m =\n    match m with\n    | A -> f 1\n    | B -> false"
    )

[<Fact>]
let ``ValueNone with a stub comment is accused`` () =
    let source =
        "module Test\ntype M = A | B\nlet f (x: int) = ValueSome x\nlet g m =\n    match m with\n    | A -> f 1\n    | B ->\n        // not implemented\n        ValueNone"

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion for ValueNone, got %A" other

[<Fact>]
let ``null without a comment is an ordinary value`` () =
    // from the corpus (SQLProvider): `| null -> null` passes a sentinel
    // through, and `| [] -> Unchecked.defaultof<'T>` IS SingleOrDefault's
    // contract — no value shape accuses itself
    assertNoSuggestion
        "module Test\ntype M = A | B\nlet f (x: int) : string = string x\nlet g m =\n    match m with\n    | A -> f 1\n    | B -> null"

[<Fact>]
let ``defaultof without a comment is an ordinary value`` () =
    assertNoSuggestion
        "module Test\nlet single (xs: int list) =\n    match xs with\n    | [ x ] -> x + 1\n    | _ -> Unchecked.defaultof<int>"

// --- commented-out code and option contracts (F# compiler ServiceInterfaceStubGenerator.fs) ---

[<Fact>]
let ``a commented-out debug print is not an unfinished-work note`` () =
    // the F# compiler's ServiceInterfaceStubGenerator.fs:
    //     | _ -> //debug "Unsupported case with %A and %A" t ts
    //         None
    // the "Unsupported" is a string the silenced print once carried
    assertNoSuggestion (
        dispatch "    | Jordan ->\n        //debug \"Unsupported case with %A and %A\" m m\n        None"
    )

[<Fact>]
let ``a commented-out call spelled with parentheses is code too`` () =
    assertNoSuggestion (dispatch "    | Jordan ->\n        // failwith(\"not implemented\")\n        None")

[<Fact>]
let ``None is the no-match result of a partial active pattern`` () =
    assertNoSuggestion
        "module Test\nlet f (x: int) = Some x\nlet (|Small|_|) (t: int) (ts: int list) =\n    match ts with\n    | [ x ] -> f (x + t)\n    | _ ->\n        // not supported yet\n        None"

[<Fact>]
let ``ValueNone inside a struct partial active pattern is its no-match result`` () =
    assertNoSuggestion
        "module Test\nlet f (x: int) = ValueSome x\n[<return: Struct>]\nlet (|Small|_|) (t: int) =\n    match t with\n    | 1 -> f t\n    | _ ->\n        // unsupported\n        ValueNone"

[<Fact>]
let ``None is the contract of a function declared to return an option`` () =
    assertNoSuggestion
        "module Test\ntype M = Gauss of int | Jordan\nlet f (x: int) = Some x\nlet solve m : int option =\n    match m with\n    | Gauss c -> f c\n    | Jordan ->\n        // not supported yet\n        None"

[<Fact>]
let ``a prose note above None in an inferred-option dispatch still fires`` () =
    // the rule's own example shape: nothing DECLARES the option, and the
    // comment is a sentence, not a silenced print
    assertPatched
        (dispatch "    | Jordan ->\n        // unsupported for now\n        None")
        (dispatch "    | Jordan ->\n        // unsupported for now\n        raise (System.NotImplementedException())")
