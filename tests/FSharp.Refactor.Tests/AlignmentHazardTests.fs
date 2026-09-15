/// The apply tool's alignment backstop (`Text.alignmentHazard`, shared with
/// FR0094 and FR0013): a single-line edit is held only when the line below
/// stands differently against an offside anchor after the edit than before.
module FSharp.Refactor.Tests.AlignmentHazardTests

open Xunit
open FSharp.Refactor

let private hazardIn (lines: string list) (line: int) (endColumn: int) (delta: int) =
    let arr = List.toArray lines
    Text.alignmentHazard (fun l -> arr.[l - 1]) arr.Length line endColumn delta

[<Fact>]
let ``anchors are the tokens after still-open context openers`` () =
    // `=` anchors `(`; the paren closes on the line and takes `a` with it;
    // `[` stays open, so `c` anchors
    Assert.Equal<int list>([ 10; 21 ], Text.offsideAnchors "let f x = (a, b) + [ c")

[<Fact>]
let ``an opener that ends the line anchors nothing`` () =
    Assert.Equal<int list>([ 16 ], Text.offsideAnchors "    | Some x -> foo (")

[<Fact>]
let ``fparsec's paren block aligned under the shortened line is a hazard`` () =
    // dropping the parens of `("inf")` moves `flags` two columns left and
    // the line under it, aligned to `flags`, re-parses as an application
    let lines =
        [ "    s.SkipCaseFolded(\"inf\") && (flags <- flags ||| 1"
          "                                stream.SkipCaseFolded(\"inity\") |> ignore" ]

    Assert.True(hazardIn lines 1 27 -2)

[<Fact>]
let ``an argument continued to the right of every anchor is no hazard`` () =
    // ClearBank.Net's tests: the second line is a continuation of the call
    // after `=`, anchored to `ClearBank` (column 26), which the edit does not
    // move; standing right of the anchor before and after, it reads the same
    let lines =
        [ "            let! actual = ClearBank.UK.MultiCurrency.createNewAccount cfg cert (Guid.NewGuid()) sortCode \"x\""
          "                                                            ClearBank.UK.MultiCurrency.AccountKind.General [||] None" ]

    Assert.False(hazardIn lines 1 36 -10)

[<Fact>]
let ``a match arm body under the expanded wildcard is no hazard`` () =
    // management-portal's hubs: `| _ ->` to `| Authenticated _ ->`; the body
    // on the next line is anchored to nothing on the arm's line
    let lines = [ "            | _ ->"; "                let! userid = ensureLogin()" ]

    Assert.False(hazardIn lines 1 15 14)

[<Fact>]
let ``an anchor moving past the line below is a hazard`` () =
    // lengthening `foo` pushes `bar` (column 9) to column 12, right of the
    // continuation at column 10, which then closes the paren block
    let lines = [ "    foo (bar baz"; "          qux" ]
    Assert.True(hazardIn lines 1 7 3)

[<Fact>]
let ``an edit after every anchor moves nothing`` () =
    let lines = [ "    let x = f (Guid.NewGuid()) y"; "            z" ]
    // the `=` anchor is `f` at column 12; lengthening `y` leaves it in place
    Assert.False(hazardIn lines 1 32 5)

[<Fact>]
let ``a continuation right of a slightly moved anchor is no hazard`` () =
    let lines = [ "    let x = f (Guid.NewGuid()) y"; "              z" ]
    // `x` to `xx` moves `f` from 12 to 13; `z` at 14 stays right of it
    Assert.False(hazardIn lines 1 9 1)

[<Fact>]
let ``a sequential item exactly on a moving anchor is a hazard`` () =
    let lines = [ "    let x = f (Guid.NewGuid()) y"; "            z" ]
    // `z` continues the binding body at `f`'s column; `x` to `xxxxxx` moves
    // `f` right past it and the body ends before `z`
    Assert.True(hazardIn lines 1 9 5)

[<Fact>]
let ``no line below means no hazard`` () =
    Assert.False(hazardIn [ "    foo (bar" ] 1 7 3)

[<Fact>]
let ``a later continuation line on the anchor is a hazard too`` () =
    // the first line below is a deeper continuation; the second stands on
    // `bar` and is the paren block's next item
    let lines = [ "    foo (bar baz"; "              qux"; "         quux" ]
    Assert.True(hazardIn lines 1 7 -2)

[<Fact>]
let ``a line no deeper than the edited one ends the construct`` () =
    // `let y` closes everything line 1 opened; what follows it is not
    // anchored there, however its columns fall
    let lines = [ "    foo (bar baz"; "    let y = 1"; "         quux" ]
    Assert.False(hazardIn lines 1 7 -2)

[<Fact>]
let ``a comment line between carries no offside meaning`` () =
    let lines = [ "    foo (bar baz"; "         // note"; "         quux" ]
    Assert.True(hazardIn lines 1 7 -2)
