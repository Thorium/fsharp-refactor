/// FR0172 ListHeadPattern: a match arm that binds a whole list and reads
/// it only by position becomes a cons pattern.
module FSharp.Refactor.Tests.ListHeadPatternTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    ListHeadPattern.find tree sourceText

/// The one suggestion's rewritten clause.
let private rewritten (source: string) =
    match findIn source with
    | [ s ] -> s.ReplacementText
    | other -> failwithf "expected one suggestion, got %A" other

/// Apply the one suggestion and typecheck the result: no errors, and no
/// FS0025 — the cons pattern must leave the match as complete as it was.
let private appliedTypechecks (source: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        let _, _, check = parseAndCheck patched

        let offending =
            check.Diagnostics
            |> Array.filter (fun d ->
                d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
                || d.ErrorNumber = 25)

        Assert.True(Array.isEmpty offending, sprintf "%s\n%A" patched offending)
        patched
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0172: an arm reading only itms.[0] after a [] arm becomes a cons pattern`` () =
    let source =
        "module Test\nlet g (x: int) = x\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> g itms.[0]"

    Assert.Equal("itmsHead :: _ -> g itmsHead", rewritten source)
    let patched = appliedTypechecks source
    Assert.Contains("| itmsHead :: _ -> g itmsHead", patched)

[<Fact>]
let ``FR0172: every head spelling becomes the head name`` () =
    let source =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms[0] + itms.Head + List.head itms + (itms |> List.head) + List.item 0 itms"

    Assert.Equal("itmsHead :: _ -> itmsHead + itmsHead + itmsHead + (itmsHead) + itmsHead", rewritten source)

    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172: a second element needs a [_] arm as well`` () =
    let covered =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | [ _ ] -> 1\n    | itms -> itms.[0] + itms.[1]"

    Assert.Equal("itmsHead :: itmsSecond :: _ -> itmsHead + itmsSecond", rewritten covered)
    appliedTypechecks covered |> ignore

    // `[ _ ]` written as a cons, or in an or-pattern with the empty case
    let consCovered =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | _ :: [] -> 1\n    | itms -> itms.[0] + itms.[1]"

    Assert.Equal("itmsHead :: itmsSecond :: _ -> itmsHead + itmsSecond", rewritten consCovered)

    let orCovered =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] | [ _ ] -> 0\n    | itms -> itms.[1]"

    Assert.Equal("_ :: itmsSecond :: _ -> itmsSecond", rewritten orCovered)
    appliedTypechecks orCovered |> ignore

    // a one-element list reaches the arm and `itms.[1]` throws there; the
    // pattern would fall through instead
    let uncovered =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms.[0] + itms.[1]"

    Assert.Empty(findIn uncovered)

    // `[ 1 ]` matches only the list holding 1, not every one-element list
    let literalArm =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | [ 1 ] -> 1\n    | itms -> itms.[0] + itms.[1]"

    Assert.Empty(findIn literalArm)

[<Fact>]
let ``FR0172: the tail is named only when the arm reads it`` () =
    let tailRead =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms.[0] + List.length itms.Tail"

    Assert.Equal("itmsHead :: itmsTail -> itmsHead + List.length itmsTail", rewritten tailRead)
    appliedTypechecks tailRead |> ignore

    let onlyTail =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> []\n    | itms -> List.tail itms"

    Assert.Equal("_ :: itmsTail -> itmsTail", rewritten onlyTail)
    appliedTypechecks onlyTail |> ignore

[<Fact>]
let ``FR0172: any other use of the list keeps the arm`` () =
    for arm in
        [
            "itms.[0] + itms.Length"
            "itms.[0] + itms.[2]"
            "if itms.IsEmpty then 0 else itms.[0]"
            "List.sum itms + itms.[0]"
            "itms.[0] + (List.head itms).GetHashCode() + itms.Item 0"
            "itms.[itms.[0]]"
        ] do
        let source =
            $"module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> {arm}"

        Assert.Empty(findIn source)

[<Fact>]
let ``FR0172: without an earlier unguarded [] arm the rule stands down`` () =
    // no `[]` arm: the empty list reaches the arm and throws on the index
    let none =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | itms -> itms.[0]"

    Assert.Empty(findIn none)

    // `[]` after the arm never sees an empty list
    let after =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | itms when itms.Length > 3 -> itms.[0]\n    | [] -> 0\n    | _ -> 1"

    Assert.Empty(findIn after)

    // a guarded `[]` arm lets the empty list through when the guard fails
    let guarded =
        "module Test\nlet flag = true\nlet f (xs: int list) =\n    match xs with\n    | [] when flag -> 0\n    | itms -> itms.[0]"

    Assert.Empty(findIn guarded)

    // `[||]` is an array: O(1) indexing and no head/rest pattern
    let array =
        "module Test\nlet f (xs: int[]) =\n    match xs with\n    | [||] -> 0\n    | itms -> itms.[0]"

    Assert.Empty(findIn array)

[<Fact>]
let ``FR0172: a rebinding of the name inside the arm stands the rule down`` () =
    let lambda =
        "module Test\nlet f (xs: int list) (ys: int list list) =\n    match xs with\n    | [] -> []\n    | itms -> ys |> List.map (fun itms -> itms.[0])"

    Assert.Empty(findIn lambda)

    let shadowingLet =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms ->\n        let itms = [ 1; 2 ]\n        itms.[0]"

    Assert.Empty(findIn shadowingLet)

    let nestedArm =
        "module Test\nlet f (xs: int list) (ys: int list) =\n    match xs with\n    | [] -> 0\n    | itms ->\n        match ys with\n        | [] -> 0\n        | itms -> itms.[0]"

    // the inner arm qualifies on its own; the outer does not
    match findIn nestedArm with
    | [ s ] -> Assert.Equal("itmsHead :: _ -> itmsHead", s.ReplacementText)
    | other -> failwithf "expected the inner arm only, got %A" other

[<Fact>]
let ``FR0172: the guard is rewritten with the body, across lines`` () =
    let source =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms when itms.[0] > 0 ->\n        let doubled = itms.[0] * 2\n        doubled + 1\n    | _ -> -1"

    Assert.Equal(
        "itmsHead :: _ when itmsHead > 0 ->\n        let doubled = itmsHead * 2\n        doubled + 1",
        rewritten source
    )

    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172: function and match! arms qualify too`` () =
    let fn = "module Test\nlet f =\n    function\n    | [] -> 0\n    | itms -> itms.[0]"

    Assert.Equal("itmsHead :: _ -> itmsHead", rewritten fn)
    appliedTypechecks fn |> ignore

    let bang =
        "module Test\nlet f (xs: Async<int list>) =\n    async {\n        match! xs with\n        | [] -> return 0\n        | itms -> return itms.[0]\n    }"

    Assert.Equal("itmsHead :: _ -> return itmsHead", rewritten bang)
    appliedTypechecks bang |> ignore

[<Fact>]
let ``FR0172: a taken name gets a numeric suffix`` () =
    let source =
        "module Test\nlet itmsHead = 5\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms.[0] + itmsHead"

    Assert.Equal("itmsHead2 :: _ -> itmsHead2 + itmsHead", rewritten source)
    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172 harness: the typecheck sees an incomplete match as FS0025`` () =
    // what appliedTypechecks guards against must be visible to it
    let _, _, check =
        parseAndCheck "module Test\nlet f (xs: int list) =\n    match xs with\n    | h :: _ -> h"

    Assert.Contains(check.Diagnostics, fun d -> d.ErrorNumber = 25)

[<Fact>]
let ``FR0172: an earlier catch-all is no proof — it matches arrays and strings too`` () =
    // the arm is dead code either way (FS0025), but `| itmsHead :: _ ->`
    // over an ARRAY does not compile, and a sweep would have written it
    for scrutinee, ty, zero in [ "xs", "int[]", "0"; "s", "string", "' '"; "xs", "int list", "0" ] do
        let source =
            $"module Test\nlet f ({scrutinee}: {ty}) =\n    match {scrutinee} with\n    | _ -> {zero}\n    | itms -> itms.[0]"

        Assert.Empty(findIn source)

[<Fact>]
let ``FR0172: a lowercase .head is somebody's extension member, not List.head`` () =
    let source =
        "module Test\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms.head"

    Assert.Empty(findIn source)

[<Fact>]
let ``FR0172: a file with its own List module keeps the List.head spellings`` () =
    // parse-only: nothing resolves `List.head` here, and a shadow makes it
    // another function
    let shadowed =
        "module Test\nmodule List =\n    let head (xs: int list) = 42\n\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> List.head itms"

    Assert.Empty(findIn shadowed)

    // the member spellings are the list's own and stay offered
    let members =
        "module Test\nmodule List =\n    let head (xs: int list) = 42\n\nlet f (xs: int list) =\n    match xs with\n    | [] -> 0\n    | itms -> itms.Head"

    Assert.Equal("itmsHead :: _ -> itmsHead", rewritten members)
