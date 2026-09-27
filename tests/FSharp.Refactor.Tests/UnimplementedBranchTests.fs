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
        assertParses "Patched source" patched
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
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // Not supported yet
                        None
                """
        ))
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // Not supported yet
                        raise (System.NotImplementedException())
                """
        ))

[<Fact>]
let ``not implemented yet is recognised too`` () =
    assertPatched
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // not implemented yet
                        None
                """
        ))
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // not implemented yet
                        raise (System.NotImplementedException())
                """
        ))

[<Fact>]
let ``a block comment accuses just as well`` () =
    assertPatched
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        (* unimplemented *)
                        None
                """
        ))
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        (* unimplemented *)
                        raise (System.NotImplementedException())
                """
        ))

[<Fact>]
let ``an empty string stand-in is reported`` () =
    let source =
        fsharp
            """
            module Test
            type M = A | B | C
            let name (x: int) = string x
            let f m =
                match m with
                | A -> name 1
                | B -> name 2
                | C ->
                    // not supported yet
                    ""
            """

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
        fsharp
            """
            module Test
            type M = Gauss of int | Jordan
            let f (x: int) = Some x

            """
        + fsharp
            """
            // TODO: cache these results
            let solve m =
                match m with
                | Gauss c -> f c
                | Jordan -> None
            """
    )

[<Fact>]
let ``a table of constants is data, not a stub`` () =
    // no sibling computes anything, so a constant branch is just a value
    assertNoSuggestion (
        fsharp
            """
            module Test
            type M = A | B | C
            let f m =
                match m with
                | A -> 1
                | B -> 2
                | C ->
                    // not supported
                    0
            """
    )

[<Fact>]
let ``a branch that does real work is untouched`` () =
    assertNoSuggestion (
        dispatch (
            fsharp
                """
                    | Jordan ->
                        // not supported yet
                        f 3
                """
        )
    )

[<Fact>]
let ``null with a stub comment is accused`` () =
    let source =
        fsharp
            """
            module Test
            type M = A | B
            let f (x: int) : string = string x
            let g m =
                match m with
                | A -> f 1
                | B ->
                    // not implemented
                    null
            """

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion for null, got %A" other

[<Fact>]
let ``FR0100: a boolean under a stub comment is an answer, not a placeholder`` () =
    // `// not supported on this platform` above `false` IS the answer to
    // "is it supported?": a raise there turns a capability query into a crash
    for comment in [ "Not supported yet"; "not supported on this platform"; "not implemented" ] do
        for value in [ "false"; "true" ] do
            assertNoSuggestion
                $"module Test\ntype M = A | B\nlet f (x: int) = x > 0\nlet g m =\n    match m with\n    | A -> f 1\n    | B ->\n        // {comment}\n        {value}"

[<Fact>]
let ``FR0100: a documented platform gap is a real answer`` () =
    // "not supported" with nothing saying the gap is temporary describes
    // the platform; "not supported yet" / "for now" describes the code
    assertNoSuggestion (
        dispatch (
            fsharp
                """
                    | Jordan ->
                        // not supported on this platform
                        None
                """
        )
    )

    assertNoSuggestion (
        dispatch (
            fsharp
                """
                    | Jordan ->
                        // unsupported by the backend
                        None
                """
        )
    )

[<Fact>]
let ``false without a comment is an ordinary value`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                module Test
                type M = A | B
                let f (x: int) = x > 0
                let g m =
                    match m with
                    | A -> f 1
                    | B -> false
                """
        )
    )

[<Fact>]
let ``ValueNone with a stub comment is accused`` () =
    let source =
        fsharp
            """
            module Test
            type M = A | B
            let f (x: int) = ValueSome x
            let g m =
                match m with
                | A -> f 1
                | B ->
                    // not implemented
                    ValueNone
            """

    match findIn source with
    | [ s ] -> Assert.Equal("raise (System.NotImplementedException())", s.ReplacementText)
    | other -> failwithf "Expected one suggestion for ValueNone, got %A" other

[<Fact>]
let ``null without a comment is an ordinary value`` () =
    // from the corpus (SQLProvider): `| null -> null` passes a sentinel
    // through, and `| [] -> Unchecked.defaultof<'T>` IS SingleOrDefault's
    // contract — no value shape accuses itself
    assertNoSuggestion (
        fsharp
            """
            module Test
            type M = A | B
            let f (x: int) : string = string x
            let g m =
                match m with
                | A -> f 1
                | B -> null
            """
    )

[<Fact>]
let ``defaultof without a comment is an ordinary value`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let single (xs: int list) =
                match xs with
                | [ x ] -> x + 1
                | _ -> Unchecked.defaultof<int>
            """
    )

// --- commented-out code and option contracts (F# compiler ServiceInterfaceStubGenerator.fs) ---

[<Fact>]
let ``a commented-out debug print is not an unfinished-work note`` () =
    // the F# compiler's ServiceInterfaceStubGenerator.fs:
    //     | _ -> //debug "Unsupported case with %A and %A" t ts
    //         None
    // the "Unsupported" is a string the silenced print once carried
    assertNoSuggestion (
        dispatch (
            fsharp
                """
                    | Jordan ->
                        //debug "Unsupported case with %A and %A" m m
                        None
                """
        )
    )

[<Fact>]
let ``a commented-out call spelled with parentheses is code too`` () =
    assertNoSuggestion (
        dispatch (
            fsharp
                """
                    | Jordan ->
                        // failwith("not implemented")
                        None
                """
        )
    )

[<Fact>]
let ``None is the no-match result of a partial active pattern`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (x: int) = Some x
            let (|Small|_|) (t: int) (ts: int list) =
                match ts with
                | [ x ] -> f (x + t)
                | _ ->
                    // not supported yet
                    None
            """
    )

[<Fact>]
let ``ValueNone inside a struct partial active pattern is its no-match result`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (x: int) = ValueSome x
            [<return: Struct>]
            let (|Small|_|) (t: int) =
                match t with
                | 1 -> f t
                | _ ->
                    // unsupported
                    ValueNone
            """
    )

[<Fact>]
let ``None is the contract of a function declared to return an option`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            type M = Gauss of int | Jordan
            let f (x: int) = Some x
            let solve m : int option =
                match m with
                | Gauss c -> f c
                | Jordan ->
                    // not supported yet
                    None
            """
    )

[<Fact>]
let ``a prose note above None in an inferred-option dispatch still fires`` () =
    // the rule's own example shape: nothing DECLARES the option, and the
    // comment is a sentence, not a silenced print
    assertPatched
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // unsupported for now
                        None
                """
        ))
        (dispatch (
            fsharp
                """
                    | Jordan ->
                        // unsupported for now
                        raise (System.NotImplementedException())
                """
        ))
