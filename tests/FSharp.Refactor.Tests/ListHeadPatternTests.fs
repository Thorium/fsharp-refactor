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

/// Apply the one suggestion and typecheck the result: no errors, no FS0025
/// — the cons pattern must leave the match as complete as it was — and no
/// FS0058, a line the longer pattern pushed offside.
let private appliedTypechecks (source: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        let _, _, check = parseAndCheck patched

        let offending =
            check.Diagnostics
            |> Array.filter (fun d ->
                d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
                || d.ErrorNumber = 25
                || d.ErrorNumber = 58)

        Assert.True(Array.isEmpty offending, $"%s{patched}\n%A{offending}")
        patched
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0172: an arm reading only itms.[0] after a [] arm becomes a cons pattern`` () =
    let source =
        fsharp
            """
            module Test
            let g (x: int) = x
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> g itms.[0]
            """

    Assert.Equal("itmsHead :: _ -> g itmsHead", rewritten source)
    let patched = appliedTypechecks source
    Assert.Contains("| itmsHead :: _ -> g itmsHead", patched)

[<Fact>]
let ``FR0172: every head spelling becomes the head name`` () =
    let source =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms[0] + itms.Head + List.head itms + (itms |> List.head) + List.item 0 itms
            """

    Assert.Equal("itmsHead :: _ -> itmsHead + itmsHead + itmsHead + (itmsHead) + itmsHead", rewritten source)

    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172: a second element needs a [_] arm as well`` () =
    let covered =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | [ _ ] -> 1
                | itms -> itms.[0] + itms.[1]
            """

    Assert.Equal("itmsHead :: itmsSecond :: _ -> itmsHead + itmsSecond", rewritten covered)
    appliedTypechecks covered |> ignore

    // `[ _ ]` written as a cons, or in an or-pattern with the empty case
    let consCovered =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | _ :: [] -> 1
                | itms -> itms.[0] + itms.[1]
            """

    Assert.Equal("itmsHead :: itmsSecond :: _ -> itmsHead + itmsSecond", rewritten consCovered)

    let orCovered =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] | [ _ ] -> 0
                | itms -> itms.[1]
            """

    Assert.Equal("_ :: itmsSecond :: _ -> itmsSecond", rewritten orCovered)
    appliedTypechecks orCovered |> ignore

    // a one-element list reaches the arm and `itms.[1]` throws there; the
    // pattern would fall through instead
    let uncovered =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms.[0] + itms.[1]
            """

    Assert.Empty(findIn uncovered)

    // `[ 1 ]` matches only the list holding 1, not every one-element list
    let literalArm =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | [ 1 ] -> 1
                | itms -> itms.[0] + itms.[1]
            """

    Assert.Empty(findIn literalArm)

[<Fact>]
let ``FR0172: the tail is named only when the arm reads it`` () =
    let tailRead =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms.[0] + List.length itms.Tail
            """

    Assert.Equal("itmsHead :: itmsTail -> itmsHead + List.length itmsTail", rewritten tailRead)
    appliedTypechecks tailRead |> ignore

    let onlyTail =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> []
                | itms -> List.tail itms
            """

    Assert.Equal("_ :: itmsTail -> itmsTail", rewritten onlyTail)
    appliedTypechecks onlyTail |> ignore

[<Fact>]
let ``FR0172: a tail read beside the second element is the list after the head`` () =
    // `h :: s :: t` would bind the rest after the SECOND element, one
    // short of `itms.Tail`, and still typecheck
    let both =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | [ _ ] -> 1
                | itms -> itms.[0] + itms.[1] + List.length itms.Tail
            """

    Assert.Equal(
        "itmsHead :: (itmsSecond :: _ as itmsTail) -> itmsHead + itmsSecond + List.length itmsTail",
        rewritten both
    )

    appliedTypechecks both |> ignore

    let noHead =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] | [ _ ] -> []
                | itms -> itms.[1] :: itms.Tail
            """

    Assert.Equal("_ :: (itmsSecond :: _ as itmsTail) -> itmsSecond :: itmsTail", rewritten noHead)
    appliedTypechecks noHead |> ignore

    // the pattern's tail is the list's own Tail
    let xs = [ 1; 2; 3 ]

    match xs with
    | _ :: (_ :: _ as tail) -> Assert.Equal<int list>(xs.Tail, tail)
    | _ -> failwith "unreachable"

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
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | itms -> itms.[0]
            """

    Assert.Empty(findIn none)

    // `[]` after the arm never sees an empty list
    let after =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | itms when itms.Length > 3 -> itms.[0]
                | [] -> 0
                | _ -> 1
            """

    Assert.Empty(findIn after)

    // a guarded `[]` arm lets the empty list through when the guard fails
    let guarded =
        fsharp
            """
            module Test
            let flag = true
            let f (xs: int list) =
                match xs with
                | [] when flag -> 0
                | itms -> itms.[0]
            """

    Assert.Empty(findIn guarded)

    // `[||]` is an array: O(1) indexing and no head/rest pattern
    let array =
        fsharp
            """
            module Test
            let f (xs: int[]) =
                match xs with
                | [||] -> 0
                | itms -> itms.[0]
            """

    Assert.Empty(findIn array)

[<Fact>]
let ``FR0172: a rebinding of the name inside the arm stands the rule down`` () =
    let lambda =
        fsharp
            """
            module Test
            let f (xs: int list) (ys: int list list) =
                match xs with
                | [] -> []
                | itms -> ys |> List.map (fun itms -> itms.[0])
            """

    Assert.Empty(findIn lambda)

    let shadowingLet =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms ->
                    let itms = [ 1; 2 ]
                    itms.[0]
            """

    Assert.Empty(findIn shadowingLet)

    let nestedArm =
        fsharp
            """
            module Test
            let f (xs: int list) (ys: int list) =
                match xs with
                | [] -> 0
                | itms ->
                    match ys with
                    | [] -> 0
                    | itms -> itms.[0]
            """

    // the inner arm qualifies on its own; the outer does not
    match findIn nestedArm with
    | [ s ] -> Assert.Equal("itmsHead :: _ -> itmsHead", s.ReplacementText)
    | other -> failwithf "expected the inner arm only, got %A" other

[<Fact>]
let ``FR0172: the guard is rewritten with the body, across lines`` () =
    let source =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms when itms.[0] > 0 ->
                    let doubled = itms.[0] * 2
                    doubled + 1
                | _ -> -1
            """

    Assert.Equal(
        fsharp
            """
            itmsHead :: _ when itmsHead > 0 ->
                    let doubled = itmsHead * 2
                    doubled + 1
            """,
        rewritten source
    )

    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172: a body starting on the arrow line and continuing below is left alone`` () =
    // `itms` becomes `itmsHead :: _`, so the `->` moves right and the second
    // statement, aligned to the first, falls offside - and typechecks with a
    // warning, which no compile backstop stops
    let continued =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> ()
                | itms -> printfn "%d" itms.[0]
                          printfn "done"
            """

    Assert.Empty(findIn continued)

    // a guard spanning lines moves the same way
    let guarded =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms when itms.[0] > 0
                            && itms.[0] < 9 ->
                    1
                | _ -> -1
            """

    Assert.Empty(findIn guarded)

    // a later line indented past an edit that lengthens its line
    let aligned =
        fsharp
            """
            module Test
            let g (x: int) (f: int -> int) = f x
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms ->
                    g itms[0] (fun y ->
                                 y + 1)
            """

    Assert.Empty(findIn aligned)

    // a single-line clause followed on its line by text a line below is
    // anchored to: that text moves with the grown pattern
    let trailing =
        fsharp
            """
            module Test
            let f (xs: int list) =
                (match xs with [] -> 0 | itms -> itms[0]) + (match xs with
                                                             | [] -> 1
                                                             | _ -> 2)
            """

    Assert.Empty(findIn trailing)

    // a shortening edit with a later line aligned exactly to a token after
    // it: the line would read as an argument of the line above
    let exactAligned =
        fsharp
            """
            module Test
            let g (x: int) (fs: (int -> int) list) = fs |> List.sumBy (fun f -> f x)
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms ->
                    g (List.head itms) [ id
                                         id ]
            """

    Assert.Empty(findIn exactAligned)

    // an ordinary nested block below a lengthening edit is anchored to its
    // own lines, not to the edit: the fix stays
    let nested =
        fsharp
            """
            module Test
            let f (xs: string list) =
                match xs with
                | [] -> 0
                | itms ->
                    let cmd = itms[0]
                    for a in [ 1; 2 ] do
                        if a > 1 then
                            match cmd with
                            | "x" -> printfn "%d %s" a cmd
                            | _ -> if a > 0 then printfn "deep"
                    cmd.Length
            """

    Assert.Equal(1, (findIn nested).Length)
    appliedTypechecks nested |> ignore

    // the same shapes with the body on its own line, or a shortening edit,
    // keep the fix and typecheck without a warning
    let ownLine =
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> ()
                | itms ->
                    printfn "%d" itms.[0]
                    printfn "done"
            """

    Assert.Equal(
        fsharp
            """
            itmsHead :: _ ->
                    printfn "%d" itmsHead
                    printfn "done"
            """,
        rewritten ownLine
    )

    appliedTypechecks ownLine |> ignore

    let shortening =
        fsharp
            """
            module Test
            let g (x: int) (f: int -> int) = f x
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms ->
                    g itms.Head (fun y ->
                                   y + 1)
            """

    Assert.Equal(
        fsharp
            """
            itmsHead :: _ ->
                    g itmsHead (fun y ->
                                   y + 1)
            """,
        rewritten shortening
    )

    appliedTypechecks shortening |> ignore

[<Fact>]
let ``FR0172: function and match! arms qualify too`` () =
    let fn =
        fsharp
            """
            module Test
            let f =
                function
                | [] -> 0
                | itms -> itms.[0]
            """

    Assert.Equal("itmsHead :: _ -> itmsHead", rewritten fn)
    appliedTypechecks fn |> ignore

    let bang =
        fsharp
            """
            module Test
            let f (xs: Async<int list>) =
                async {
                    match! xs with
                    | [] -> return 0
                    | itms -> return itms.[0]
                }
            """

    Assert.Equal("itmsHead :: _ -> return itmsHead", rewritten bang)
    appliedTypechecks bang |> ignore

[<Fact>]
let ``FR0172: a taken name gets a numeric suffix`` () =
    let source =
        fsharp
            """
            module Test
            let itmsHead = 5
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms.[0] + itmsHead
            """

    Assert.Equal("itmsHead2 :: _ -> itmsHead2 + itmsHead", rewritten source)
    appliedTypechecks source |> ignore

[<Fact>]
let ``FR0172 harness: the typecheck sees an incomplete match as FS0025`` () =
    // what appliedTypechecks guards against must be visible to it
    let _, _, check =
        parseAndCheck (
            fsharp
                """
                module Test
                let f (xs: int list) =
                    match xs with
                    | h :: _ -> h
                """
        )

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
        fsharp
            """
            module Test
            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms.head
            """

    Assert.Empty(findIn source)

[<Fact>]
let ``FR0172: a file with its own List module keeps the List.head spellings`` () =
    // parse-only: nothing resolves `List.head` here, and a shadow makes it
    // another function
    let shadowed =
        fsharp
            """
            module Test
            module List =
                let head (xs: int list) = 42

            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> List.head itms
            """

    Assert.Empty(findIn shadowed)

    // the member spellings are the list's own and stay offered
    let members =
        fsharp
            """
            module Test
            module List =
                let head (xs: int list) = 42

            let f (xs: int list) =
                match xs with
                | [] -> 0
                | itms -> itms.Head
            """

    Assert.Equal("itmsHead :: _ -> itmsHead", rewritten members)
