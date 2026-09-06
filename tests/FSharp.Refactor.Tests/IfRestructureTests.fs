module FSharp.Refactor.Tests.IfRestructureTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open FSharp.Analyzers.SDK

// ---- FR0111 else-if -> elif ----

let private elseIfsIn (source: string) =
    let tree, sourceText = parse source
    IfRestructure.findElseIf tree sourceText

[<Fact>]
let ``an else holding a whole if flattens to elif`` () =
    let source =
        "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        0\n    else\n        if y = 2 then\n            1\n        else 2"

    match elseIfsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

        // the nested if's block moves left with it: then-body and else
        // both sit at the outer if's depth
        Assert.Equal(
            "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        0\n    elif y = 2 then\n        1\n    else 2",
            patched
        )
    | other -> failwithf "Expected one elif suggestion, got %A" other

[<Fact>]
let ``an existing elif is left alone`` () =
    Assert.Empty(elseIfsIn "module Test\nlet f (x: int) =\n    if x = 1 then 0\n    elif x = 2 then 1\n    else 2")

[<Fact>]
let ``an else with more than the if keeps its shape`` () =
    Assert.Empty(
        elseIfsIn
            "module Test\nlet g () = ()\nlet f (x: int) (y: int) =\n    if x = 1 then\n        0\n    else\n        g ()\n        if y = 2 then 1 else 2"
    )

// ---- FR0112 equality chain -> match ----

let private chainsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    IfRestructure.findEqualityChains tree sourceText checkResults

[<Fact>]
let ``an equality chain over one ident becomes a match`` () =
    let source =
        "module Test\nlet f (x: int) =\n    if x = 1 then \"a\"\n    elif x = 2 then \"b\"\n    else \"c\""

    match chainsIn source with
    | [ s ] ->
        Assert.Contains("match x with", s.ReplacementText)
        Assert.Contains("| 1 -> \"a\"", s.ReplacementText)
        Assert.Contains("| 2 -> \"b\"", s.ReplacementText)
        Assert.Contains("| _ -> \"c\"", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one chain suggestion, got %A" other

[<Fact>]
let ``verbatim string literals chain into a match with their prefix intact`` () =
    let source =
        "module Test\nlet f (x: string) =\n    if x = @\"a\\b\" then 1\n    elif x = @\"c\\d\" then 2\n    else 3"

    match chainsIn source with
    | [ s ] ->
        Assert.Contains("| @\"a\\b\" -> 1", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one verbatim chain suggestion, got %A" other

[<Fact>]
let ``a chain over a CALL is left alone: re-evaluation is the semantics`` () =
    Assert.Empty(
        chainsIn
            "module Test\nlet f (g: unit -> int) =\n    if g () = 1 then \"a\"\n    elif g () = 2 then \"b\"\n    else \"c\""
    )

[<Fact>]
let ``mixed identifiers are left alone`` () =
    Assert.Empty(
        chainsIn
            "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then \"a\"\n    elif y = 2 then \"b\"\n    else \"c\""
    )

[<Fact>]
let ``duplicate literals are left alone`` () =
    Assert.Empty(
        chainsIn "module Test\nlet f (x: int) =\n    if x = 1 then \"a\"\n    elif x = 1 then \"b\"\n    else \"c\""
    )

[<Fact>]
let ``a two-arm string chain converts too`` () =
    let source =
        "module Test\nlet f (s: string) =\n    if s = \"json\" then 1\n    elif s = \"xml\" then 2\n    else 0"

    match chainsIn source with
    | [ s ] ->
        Assert.Contains("| \"json\" -> 1", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one string chain suggestion, got %A" other

// ---- FR0113 nested if merge ----

let private mergesIn (source: string) =
    let tree, sourceText = parse source
    IfRestructure.findNestedIfMerges tree sourceText

[<Fact>]
let ``nested ifs with the same else merge`` () =
    let source =
        "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        if y = 2 then 1 else 3\n    else 3"

    match mergesIn source with
    | [ s ] ->
        Assert.Contains("if x = 1 && y = 2 then", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one merge suggestion, got %A" other

[<Fact>]
let ``different elses are left alone`` () =
    Assert.Empty(
        mergesIn "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        if y = 2 then 1 else 3\n    else 4"
    )

[<Fact>]
let ``inner else missing while outer has one is the semantic trap`` () =
    // merging would run the outer else where the original ran NOTHING
    Assert.Empty(
        mergesIn
            "module Test\nlet g () = ()\nlet f (x: int) (y: int) =\n    if x = 1 then\n        (if y = 2 then g ())\n    else g ()"
    )

[<Fact>]
let ``both elses absent merges the unit shape`` () =
    let source =
        "module Test\nlet g () = ()\nlet f (x: int) (y: int) =\n    if x = 1 then\n        if y = 2 then g ()"

    match mergesIn source with
    | [ s ] ->
        Assert.Contains("if x = 1 && y = 2 then", s.ReplacementText)
        Assert.Contains("g ()", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one unit merge suggestion, got %A" other

[<Fact>]
let ``an or-condition gains parens before joining the and`` () =
    let source =
        "module Test\nlet f (x: int) (y: int) =\n    if x = 1 || x = 2 then\n        if y = 3 then 1 else 9\n    else 9"

    match mergesIn source with
    | [ s ] ->
        Assert.Contains("(x = 1 || x = 2) && y = 3", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one parenthesized merge, got %A" other

// ---- FR0110 missing DU cases ----

let private missingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MissingCases.find tree sourceText checkResults

/// Insertion fixes have a zero-width range: patch by splicing the text in.
let private applyInsert (source: string) (s: MissingCases.Suggestion) =
    let lines = source.Split '\n'

    let offset =
        (lines |> Seq.take (s.Range.StartLine - 1) |> Seq.sumBy (fun l -> l.Length + 1))
        + s.Range.StartColumn

    source.Substring(0, offset) + s.InsertText + source.Substring offset

[<Fact>]
let ``an incomplete DU match gains raising arms`` () =
    let source =
        "module Test\ntype Color = Red | Green | Blue\nlet f (c: Color) =\n    match c with\n    | Red -> \"r\"\n    | Green -> \"g\""

    match missingIn source with
    | [ s ] ->
        Assert.Equal<string list>([ "Blue" ], s.MissingCases)
        Assert.Contains("| Blue -> raise (System.NotImplementedException())", s.InsertText)
        let patched = applyInsert source s
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one missing-case suggestion, got %A" other

[<Fact>]
let ``a wildcard arm completes the match`` () =
    Assert.Empty(
        missingIn
            "module Test\ntype Color = Red | Green | Blue\nlet f (c: Color) =\n    match c with\n    | Red -> \"r\"\n    | _ -> \"x\""
    )

[<Fact>]
let ``field-carrying cases arrive with a wildcard`` () =
    let source =
        "module Test\ntype Shape = Dot | Circle of int\nlet f (s: Shape) =\n    match s with\n    | Dot -> 0"

    match missingIn source with
    | [ s ] -> Assert.Contains("| Circle _ -> raise", s.InsertText)
    | other -> failwithf "Expected one missing-case suggestion, got %A" other

[<Fact>]
let ``too many missing cases means a wildcard was the intent`` () =
    Assert.Empty(
        missingIn "module Test\ntype N = A | B | C | D | E | F\nlet f (n: N) =\n    match n with\n    | A -> 0"
    )

[<Fact>]
let ``guarded arms do not count as coverage`` () =
    let source =
        "module Test\ntype Color = Red | Green\nlet f (c: Color) =\n    match c with\n    | Red -> \"r\"\n    | Green when 1 > 0 -> \"g\""

    match missingIn source with
    | [ s ] -> Assert.Equal<string list>([ "Green" ], s.MissingCases)
    | other -> failwithf "Expected the guarded case still missing, got %A" other

// ---- FR0114 pyramid flip ----

let private flipsIn (source: string) =
    let tree, sourceText = parse source
    IfRestructure.findPyramidFlips 20 3 tree sourceText

let private bigThen =
    [ for i in 1..22 -> $"        let v{i} = {i}" ] @ [ "        v1 + v22" ]
    |> String.concat "\n"

[<Fact>]
let ``a large then behind a small else flips`` () =
    let source =
        $"module Test\nlet f (x: int) =\n    if x = 1 then\n{bigThen}\n    else\n        0"

    match flipsIn source with
    | [ s ] ->
        Assert.StartsWith("if not (x = 1) then", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one flip suggestion, got %A" other

[<Fact>]
let ``an already negated condition unwraps instead of double negating`` () =
    let source =
        $"module Test\nlet f (x: int) =\n    if not (x = 1) then\n{bigThen}\n    else\n        0"

    match flipsIn source with
    | [ s ] -> Assert.StartsWith("if x = 1 then", s.ReplacementText)
    | other -> failwithf "Expected one unwrapping flip, got %A" other

[<Fact>]
let ``a small then is left alone`` () =
    Assert.Empty(flipsIn "module Test\nlet f (x: int) =\n    if x = 1 then\n        2\n    else\n        0")

// ---- FR0115 guard order note ----

let private guardNotesIn (source: string) =
    let tree, sourceText = parse source
    IfRestructure.findGuardOrderNotes tree sourceText

[<Fact>]
let ``a compound guard on the first arm before a failing wildcard is noted`` () =
    match
        guardNotesIn
            "module Test\nlet f (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> \"base\"\n    | _ -> failwith \"err\""
    with
    | [ n ] -> Assert.Equal("x", n.Variable)
    | other -> failwithf "Expected one guard-order note, got %A" other

[<Fact>]
let ``FR0115: None, Error and raise wildcards are error arms`` () =
    let notes (arm: string) =
        guardNotesIn
            $"module Test\nlet f (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> Some x\n    | _ -> {arm}"

    Assert.Single(notes "None") |> ignore

    Assert.Single(notes "raise (System.ArgumentOutOfRangeException \"v\")")
    |> ignore

    Assert.Single(
        guardNotesIn
            "module Test\nlet f (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> Ok x\n    | _ -> Error \"out of range\""
    )
    |> ignore

[<Fact>]
let ``FR0115: a wildcard computing a value is an alternative, not an error arm`` () =
    // FCS CheckFormatStrings: `| _ -> None, fmtPos` (a tuple carrying None
    // is a result); fsdocs ProjectCracker: the wildcard probes further;
    // the generated lexer: the wildcard is the next state
    Assert.Empty(
        guardNotesIn
            "module Test\nlet f (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> Some x, 1\n    | _ -> None, 0"
    )

    Assert.Empty(
        guardNotesIn
            "module Test\nlet f (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> \"base\"\n    | _ -> \"err\""
    )

[<Fact>]
let ``a simple guard is not noted`` () =
    Assert.Empty(
        guardNotesIn
            "module Test\nlet f (v: int) (lo: int) =\n    match v with\n    | x when x >= lo -> \"base\"\n    | _ -> failwith \"err\""
    )

// ---- FR0116 rec group extraction ----

let private recGroupsIn (source: string) =
    let tree, sourceText = parse source
    RecGroup.find None tree sourceText

[<Fact>]
let ``a member referencing no sibling leaves the group`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1) + x\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1) - z"

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("f2", s.MemberName)
        Assert.StartsWith("let f2", s.InsertText)
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a member the group calls still leaves when it calls nobody`` () =
    // f2 is CALLED by f1 but calls no member itself: moving it above the
    // group keeps it in scope for the callers
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then f2 x else f1 (x - 1)\nand f2 (y: int) = y + 1"

    match recGroupsIn source with
    | [ s ] -> Assert.Equal("f2", s.MemberName)
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a genuinely mutual member stays`` () =
    Assert.Empty(
        recGroupsIn
            "module Test\nlet rec isEven (n: int) : bool = if n = 0 then true else isOdd (n - 1)\nand isOdd (n: int) : bool = if n = 0 then false else isEven (n - 1)"
    )

[<Fact>]
let ``the extraction applies to a compiling result`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1) + x\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1) - z"

    match recGroupsIn source with
    | [ s ] ->
        // apply remove-then-insert (remove is later in the file; do it first)
        let lines = source.Split '\n'

        let offsetOf (line: int) (col: int) =
            (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

        let removeStart = offsetOf s.RemoveRange.StartLine s.RemoveRange.StartColumn
        let removeEnd = offsetOf s.RemoveRange.EndLine s.RemoveRange.EndColumn
        let afterRemove = source.Substring(0, removeStart) + source.Substring removeEnd
        let insertAt = offsetOf s.InsertRange.StartLine s.InsertRange.StartColumn

        let patched =
            afterRemove.Substring(0, insertAt)
            + s.InsertText
            + afterRemove.Substring insertAt

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a self-recursive member leaves as its own let rec`` () =
    // adversarial: `fact` references itself but no sibling — extracting
    // it as a plain `let` would not compile; the rec must survive
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f2 (x - 1) + f1 x\nand fact (n: int) : int = if n = 0 then 1 else n * fact (n - 1)\nand f2 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("fact", s.MemberName)
        Assert.True s.IsSelfRecursive
        Assert.StartsWith("let rec fact", s.InsertText)
    | other -> failwithf "Expected one rec extraction, got %A" other

let private headRecrownsIn (source: string) =
    let tree, sourceText = parse source
    RecGroup.findHeadRecrowns None tree sourceText

[<Fact>]
let ``a head referencing no member is re-crowned in place`` () =
    // f2/f3 are genuinely mutual; helper heads the group but calls
    // nobody — two keyword rewrites split it off, nothing moves
    let source =
        "module Test\nlet rec helper (y: int) = y + 1\nand f2 (x: int) : int = if x = 0 then helper x else f3 (x - 1)\nand f3 (z: int) : int = if z = 0 then 0 else f2 (z - 1)"

    match headRecrownsIn source with
    | [ s ] ->
        Assert.Equal("helper", s.MemberName)

        let lines = source.Split '\n'

        let offsetOf (line: int) (col: int) =
            (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

        // apply back-to-front so earlier offsets stay valid
        let replace (r: FSharp.Compiler.Text.range) (text: string) (s: string) =
            s.Substring(0, offsetOf r.StartLine r.StartColumn)
            + text
            + s.Substring(offsetOf r.EndLine r.EndColumn)

        let patched = source |> replace s.AndRange "let rec" |> replace s.LetRecRange "let"
        Assert.Contains("let helper", patched)
        Assert.Contains("let rec f2", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one head re-crown, got %A" other

[<Fact>]
let ``a self-recursive head keeps its crown`` () =
    Assert.Empty(
        headRecrownsIn
            "module Test\nlet rec loop (n: int) : int = if n = 0 then 0 else loop (n - 1)\nand f2 (x: int) : int = if x = 0 then 1 else f3 (x - 1)\nand f3 (z: int) : int = if z = 0 then 0 else f2 (z - 1)"
    )

[<Fact>]
let ``a head referencing a member stays crowned`` () =
    Assert.Empty(
        headRecrownsIn
            "module Test\nlet rec isEven (n: int) : bool = if n = 0 then true else isOdd (n - 1)\nand isOdd (n: int) : bool = if n = 0 then false else isEven (n - 1)"
    )

[<Fact>]
let ``an and-extraction in the group defers the head re-crown`` () =
    // both f2 (and-position) and helper (head) are extractable; the two
    // fixes would overlap around the group's start, so the head waits
    // for the next pass
    let source =
        "module Test\nlet rec helper (y: int) = y + 1\nand f2 (w: int) = w * 2\nand f3 (z: int) : int = if z = 0 then 0 else f3 (z - 1)"

    Assert.NotEmpty(recGroupsIn source)
    Assert.Empty(headRecrownsIn source)

[<Fact>]
let ``a chain with no terminal else is left alone`` () =
    // adversarial: the trailing elif's text starts with the KEYWORD, and
    // splicing it into a wildcard arm produced invalid code before the gate
    Assert.Empty(
        chainsIn
            "module Test\nlet mutable sink = 0\nlet g (x: int) =\n    if x = 1 then sink <- 1\n    elif x = 2 then sink <- 2\n    elif x = 3 then sink <- 3"
    )

[<Fact>]
let ``a doc comment above the extracted member travels with it`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1)\n/// Adds one; used by callers outside the group.\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] ->
        Assert.StartsWith("/// Adds one", s.InsertText)
        Assert.Contains("let f2", s.InsertText)
        Assert.Equal(3, s.RemoveRange.StartLine)
    | other -> failwithf "Expected one extraction with its doc, got %A" other

[<Fact>]
let ``a name-mentioning plain comment travels too`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1)\n// f2 is the plain helper\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] -> Assert.StartsWith("// f2 is the plain helper", s.InsertText)
    | other -> failwithf "Expected one extraction with its comment, got %A" other

[<Fact>]
let ``an unrelated comment above the member stays put`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1)\n// general remark about the algorithm\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] ->
        Assert.StartsWith("let f2", s.InsertText)
        Assert.Equal(4, s.RemoveRange.StartLine)
    | other -> failwithf "Expected one extraction without the comment, got %A" other

[<Fact>]
let ``a primed sibling reference keeps the member in the group`` () =
    // \b finds no boundary after a trailing prime: `\bvisit'\b` never
    // matches `visit' e` — the LEO adversarial catch. identifierPattern
    // treats ' as an identifier character
    Assert.Empty(
        recGroupsIn
            "module Test\nlet rec visit' (x: int) : int = if x = 0 then 0 else helper (x - 1)\nand helper (y: int) : int = visit' (y - 1)"
    )

[<Fact>]
let ``commentSafeOnly drops a message whose fix swallows a comment`` () =
    // the WebsitePlayground isMono lesson, editor edition: light bulbs
    // have no build check or hold-back behind them, so a message with a
    // comment-eating fix must never reach the editor at all
    let source =
        "module Test\nlet f (b: bool) =\n    match b with\n    | true ->\n        // the note someone left here\n        1\n    | false -> 2"

    let tree, sourceText = parse source
    let raw = MatchToIf.find tree sourceText

    // the rule itself fires (collapsing the match would eat the comment)…
    Assert.NotEmpty raw

    let messages =
        raw
        |> List.map (fun s ->
            { Type = "test"
              Message = "m"
              Code = "FR0001"
              Severity = Severity.Hint
              Range = s.Range
              Fixes =
                [ { FromRange = s.Range
                    FromText = s.OriginalText
                    ToText = s.ReplacementText } ] })

    // …and the editor filter withholds it
    Assert.Empty(Analyzers.commentSafeOnly tree sourceText messages)

[<Fact>]
let ``commentSafeOnly keeps a fix that carries the comment along`` () =
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1)\n/// Adds one.\nand f2 (y: int) = y + 1\nand f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    let tree, sourceText = parse source

    match recGroupsIn source with
    | [ s ] ->
        let messages =
            [ { Type = "test"
                Message = "m"
                Code = "FR0116"
                Severity = Severity.Hint
                Range = s.RemoveRange
                Fixes =
                  [ { FromRange = s.InsertRange
                      FromText = ""
                      ToText = s.InsertText }
                    { FromRange = s.RemoveRange
                      FromText = ""
                      ToText = "" } ] } ]

        // the remove-half spans the /// comment, but the insert-half
        // re-emits it: message-level accounting keeps the fix
        Assert.Equal(1, (Analyzers.commentSafeOnly tree sourceText messages).Length)
    | other -> failwithf "Expected the doc-carrying extraction, got %A" other

// ---- FR0117 match arm merge ----

let private armMergesIn (source: string) =
    let tree, sourceText = parse source
    MissingCases.findMergeableArms tree sourceText

[<Fact>]
let ``adjacent same-result arms fold into an or-pattern`` () =
    let source =
        "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    | 2 -> true\n    | 3 -> true\n    | 4 -> true\n    | _ -> false"

    match armMergesIn source with
    | [ s ] ->
        Assert.Equal(4, s.Count)
        Assert.Equal("| 1\n    | 2\n    | 3\n    | 4 -> true", s.NewText)
    | other -> failwithf "Expected one merge, got %A" other

[<Fact>]
let ``the merged or-pattern applies to a compiling result`` () =
    let source =
        "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    | 2 -> true\n    | 3 -> true\n    | _ -> false"

    match armMergesIn source with
    | [ s ] ->
        let lines = source.Split '\n'

        let offsetOf (line: int) (col: int) =
            (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

        let s0 = offsetOf s.ReplaceRange.StartLine s.ReplaceRange.StartColumn
        let e0 = offsetOf s.ReplaceRange.EndLine s.ReplaceRange.EndColumn
        let patched = source.Substring(0, s0) + s.NewText + source.Substring e0
        Assert.Contains("| 1\n    | 2\n    | 3 -> true", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one merge, got %A" other

[<Fact>]
let ``non-adjacent same-result arms stay apart: order is semantics`` () =
    // 2 sits between the two `true` arms — merging around it would
    // reorder the match
    Assert.Empty(
        armMergesIn
            "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    | 2 -> false\n    | 3 -> true\n    | _ -> false"
    )

[<Fact>]
let ``a when-guarded arm never joins a merge`` () =
    Assert.Empty(
        armMergesIn
            "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    | n when n > 10 -> true\n    | _ -> false"
    )

[<Fact>]
let ``binder arms never merge: or-patterns demand identical bindings`` () =
    Assert.Empty(
        armMergesIn "module Test\nlet f (o: int option) =\n    match o with\n    | Some x -> x > 0\n    | None -> false"
    )

[<Fact>]
let ``union cases with literal payloads merge`` () =
    let source =
        "module Test\nlet f (o: int option) =\n    match o with\n    | Some 1 -> true\n    | Some 2 -> true\n    | Some _ -> false\n    | None -> false"

    match armMergesIn source with
    | [ s ] ->
        Assert.Equal(2, s.Count)
        Assert.Contains("| Some 1\n    | Some 2 -> true", s.NewText)
    | other -> failwithf "Expected one payload merge, got %A" other

[<Fact>]
let ``differing bodies do not merge even when adjacent`` () =
    Assert.Empty(
        armMergesIn
            "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    | 2 -> not false\n    | _ -> false"
    )

[<Fact>]
let ``a mutual active-pattern group stays whole: bars are not the use-name`` () =
    // the SQLProvider Patterns.fs catch: `(|Odd|_|)` is USED as `Odd`,
    // so checking the decorated definition name found no references and
    // offered to pull mutually recursive patterns apart
    let source =
        "module Test\n"
        + "let rec (|Even|_|) (n: int) =\n"
        + "    match n with\n"
        + "    | 0 -> Some()\n"
        + "    | _ -> match n - 1 with\n"
        + "           | Odd -> Some()\n"
        + "           | _ -> None\n"
        + "and (|Odd|_|) (n: int) =\n"
        + "    match n with\n"
        + "    | 0 -> None\n"
        + "    | _ -> match n - 1 with\n"
        + "           | Even -> Some()\n"
        + "           | _ -> None"

    Assert.Empty(recGroupsIn source)
    Assert.Empty(headRecrownsIn source)

[<Fact>]
let ``an active pattern referencing nobody still leaves its group`` () =
    let source =
        "module Test\n"
        + "let rec (|Even|_|) (n: int) =\n"
        + "    match n with\n"
        + "    | 0 -> Some()\n"
        + "    | _ -> match n - 1 with\n"
        + "           | Odd -> Some()\n"
        + "           | _ -> None\n"
        + "and (|Blue|_|) (s: string) = if s = \"b\" then Some() else None\n"
        + "and (|Odd|_|) (n: int) =\n"
        + "    match n with\n"
        + "    | 0 -> None\n"
        + "    | _ -> match n - 1 with\n"
        + "           | Even -> Some()\n"
        + "           | _ -> None"

    match recGroupsIn source with
    | [ s ] -> Assert.Equal("|Blue|_|", s.MemberName)
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a group with two extractable members offers one per pass`` () =
    // several suggestions would all insert at the group's start and only
    // be held back against each other; the multi-pass loop does the rest
    let source =
        "module Test\nlet rec f1 (x: int) : int = if x = 0 then 0 else f4 (x - 1) + x\nand f2 (y: int) = y + 1\nand f3 (w: int) = w * 2\nand f4 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] -> Assert.Equal("f2", s.MemberName)
    | other -> failwithf "Expected exactly one suggestion per pass, got %A" other

[<Fact>]
let ``an INDENTED group's commented member extracts without eating indentation`` () =
    // the FSharp.Azure.Quantum VQC.fs catch: inside a nested module the
    // comment-extended remove ran from column 0 to the next `and`'s
    // column, deleting its indentation and orphaning the keyword at the
    // margin; the insert side doubled the comment's indent
    let source =
        "module Test\n\nmodule Inner =\n    let rec f1 (x: int) : int = if x = 0 then 0 else f3 (x - 1)\n\n    /// Adds one; used outside the group.\n    and f2 (y: int) = y + 1\n\n    and f3 (z: int) : int = if z = 0 then 0 else f1 (z - 1)"

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("f2", s.MemberName)

        let lines = source.Split '\n'

        let offsetOf (line: int) (col: int) =
            (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

        let removeStart = offsetOf s.RemoveRange.StartLine s.RemoveRange.StartColumn
        let removeEnd = offsetOf s.RemoveRange.EndLine s.RemoveRange.EndColumn
        let afterRemove = source.Substring(0, removeStart) + source.Substring removeEnd
        let insertAt = offsetOf s.InsertRange.StartLine s.InsertRange.StartColumn

        let patched =
            afterRemove.Substring(0, insertAt)
            + s.InsertText
            + afterRemove.Substring insertAt

        // the surviving `and f3` keeps its indentation, and the moved
        // comment sits at the group's indent, not doubled
        Assert.Contains("\n    and f3", patched)
        Assert.Contains("\n    /// Adds one", patched)
        Assert.DoesNotContain("\n        /// Adds one", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``each arm keeps its own comment inside the or-pattern`` () =
    // an arm carrying a comment is an arm the author treats as a distinct
    // case, whatever its body says. Merging is fine; losing the comments
    // that tell the cases apart is not, so they travel with their patterns
    let source =
        "module Test\nlet f (a: int) =\n    match a with\n    | 1 ->\n        // one\n        true\n    | 2 ->\n        // two\n        true\n    | _ -> false"

    match armMergesIn source with
    | [ s ] ->
        Assert.Equal(2, s.Count)
        Assert.Equal("| 1\n    // one\n    | 2 ->\n        // two\n        true", s.NewText)
    | other -> failwithf "Expected one comment-carrying merge, got %A" other

[<Fact>]
let ``a comment between two arms is not reproduced, so the merge is held back`` () =
    // it belongs to neither arm's range and cannot be placed. The rule still
    // offers the merge; the comment guard is what refuses it, and refusing
    // beats deleting
    let source =
        "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> true\n    // between\n    | 2 -> true\n    | _ -> false"

    match armMergesIn source with
    | [ s ] -> Assert.DoesNotContain("// between", s.NewText)
    | other -> failwithf "Expected one merge, got %A" other

[<Fact>]
let ``a comment inside the body is not hoisted as well as spliced`` () =
    // the rule only fires when the bodies are textually identical, so a
    // comment inside one IS the comment the survivor already carries.
    // Hoisting it printed `(* why *)` three times — and it compiles, so no
    // build check would ever have caught it
    let source =
        "module Test\nlet f (a: int) =\n    match a with\n    | 1 -> 1 (* why *) + 1\n    | 2 -> 1 (* why *) + 1\n    | _ -> 0"

    match armMergesIn source with
    | [ s ] -> Assert.Equal("| 1\n    | 2 -> 1 (* why *) + 1", s.NewText)
    | other -> failwithf "Expected one merge, got %A" other

// ---- FR0116: a record-building member leaves with its types written out ----

/// Two records share the label `Pending`: inside the group `p`'s type comes
/// from the caller, alone `{ p with Pending = None }` has only the label.
[<Literal>]
let private sharedLabels =
    "module Test\ntype Model = { Pending: int option; Name: string }\ntype Picker = { Pending: int option; Index: int }\n"

let private recGroupsTyped (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RecGroup.find (Some checkResults) tree sourceText

[<Fact>]
let ``a record-updating member leaves the group with its parameter and return types`` () =
    let source =
        sharedLabels
        + "let rec run (m: Model) (p: Picker) : int =\n    if m.Name = \"\" then 0 else (clear 1 p).Index\nand clear register p =\n    let next = { p with Pending = None }\n    { next with Index = register }"

    match recGroupsTyped source with
    | [ s ] ->
        Assert.Equal("clear", s.MemberName)
        Assert.StartsWith("let clear (register: int) (p: Picker) : Picker =", s.InsertText)
        // remove first (later range), then insert at the group's start
        let patched = applyEdit source s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a record-updating member stays put without the typed tree`` () =
    let source =
        sharedLabels
        + "let rec run (m: Model) (p: Picker) : int =\n    if m.Name = \"\" then 0 else (clear 1 p).Index\nand clear register p =\n    { p with Index = register }"

    Assert.Empty(recGroupsIn source)

[<Fact>]
let ``a member that builds no record leaves without annotations`` () =
    let source =
        sharedLabels
        + "let rec run (m: Model) (p: Picker) : int =\n    if m.Name = \"\" then 0 else (bump 1 p)\nand bump register p =\n    p.Index + register"

    match recGroupsTyped source with
    // `p.Index` on a bare parameter: alone, the label would resolve to the
    // LAST record carrying it, so the header names the group's own type
    | [ s ] -> Assert.StartsWith("let bump (register: int) (p: Picker) : int =", s.InsertText)
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a backticked parameter keeps its backticks when annotated`` () =
    let source =
        sharedLabels
        + "let rec run (m: Model) (p: Picker) : int =\n    if m.Name = \"\" then 0 else (clear 1 p).Index\nand clear ``the register`` p =\n    { p with Index = ``the register`` }"

    match recGroupsTyped source with
    | [ s ] ->
        Assert.StartsWith("let clear (``the register``: int) (p: Picker) : Picker =", s.InsertText)
        let patched = applyEdit source s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a member testing the type of a bare parameter leaves with its header written out`` () =
    // TypeProviders SDK: `GetFieldInit bb x` matched `x` with `:? string`;
    // inside the group x's type came from the caller, alone it is a bare 'a
    let source =
        "module Test\ntype Buf() =\n    member _.Emit(b: byte[]) = ()\nlet rec first (buf: Buf) (x: obj) = second buf x\nand second buf x =\n    match x with\n    | :? string as s -> buf.Emit(System.Text.Encoding.Unicode.GetBytes s)\n    | _ -> ()"

    match recGroupsTyped source with
    | [ s ] ->
        Assert.Equal("second", s.MemberName)
        Assert.StartsWith("let second (buf: Buf) (x: obj) : unit =", s.InsertText)
        let patched = applyEdit source s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

    // without the typed tree there is nothing to write out: it stays
    Assert.Empty(recGroupsIn source)

[<Fact>]
let ``a member reading a shared record label off a bare parameter leaves with its header written out`` () =
    // the F# compiler's Optimizer.fs: several records carry `Info` and
    // `settings`; a member pulled out with bare parameters resolved the label
    // to the wrong record ("Lookup on object of indeterminate type")
    let source =
        sharedLabels
        + "let rec run (m: Model) (p: Picker) : int =\n    if m.Name = \"\" then 0 else (pending 1 m)\nand pending register m =\n    match m.Pending with\n    | Some v -> v + register\n    | None -> register"

    match recGroupsTyped source with
    | [ s ] ->
        Assert.StartsWith("let pending (register: int) (m: Model) : int =", s.InsertText)
        let patched = applyEdit source s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a member of a file with a signature leaves with its header written out`` () =
    // the F# compiler's `and accFreeInTupInfo _opts unt acc`: alone, the
    // parameters the body never constrains generalise, and the .fsi's
    // concrete types then fail FS0034
    let signature =
        "module Test\ntype Opts = { Deep: bool }\nval walk: Opts -> int -> int list -> int list\nval keep: Opts -> int -> int list -> int list"

    let implementation =
        "module Test\ntype Opts = { Deep: bool }\nlet rec walk (opts: Opts) (n: int) (acc: int list) : int list =\n    if n = 0 then acc else walk opts (n - 1) (keep opts n acc)\nand keep _opts n acc = n :: acc"

    let tree, sourceText, check, baseline, recheck =
        parseAndCheckSigned signature implementation

    Assert.Empty baseline

    // FCS reports the generalisation against the signature — the pass
    // check can rely on it
    let bare =
        "module Test\ntype Opts = { Deep: bool }\nlet keep _opts n acc = n :: acc\nlet rec walk (opts: Opts) (n: int) (acc: int list) : int list =\n    if n = 0 then acc else walk opts (n - 1) (keep opts n acc)"

    Assert.Contains(recheck bare, fun e -> e.StartsWith "FS0034")

    match RecGroup.find (Some check) tree sourceText with
    | [ s ] ->
        Assert.StartsWith("let keep (_opts: Opts) (n: int) (acc: int list) : int list =", s.InsertText)
        let patched = applyEdit implementation s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.Empty(recheck patched)
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``FR0111: the moved block's elif chain and else dedent with it`` () =
    // fsharplint's AstInfo.fs, suave's Bytes.fs: the block kept its old
    // depth and the trailing `else` landed deeper than its `elif`
    let source =
        "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        0\n    else\n        if y = 2 then\n            1\n        elif y = 3 then\n            2\n        else\n            3"

    match elseIfsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

        Assert.Equal(
            "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then\n        0\n    elif y = 2 then\n        1\n    elif y = 3 then\n        2\n    else\n        3",
            patched
        )
    | other -> failwithf "Expected one elif suggestion, got %A" other

[<Fact>]
let ``FR0111: an if on the else's own line is already flat and only the keyword changes`` () =
    let source =
        "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then 0\n    else if y = 2 then 1\n    else 2"

    match elseIfsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText

        Assert.Equal(
            "module Test\nlet f (x: int) (y: int) =\n    if x = 1 then 0\n    elif y = 2 then 1\n    else 2",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one elif suggestion, got %A" other

[<Fact>]
let ``a member leaves without the next member's doc comment`` () =
    // the F# compiler's Optimizer.fs: five members moved out took the ///
    // of the member after them along, leaving orphaned docs
    let source =
        "module Test\nlet rec run (n: int) : int = if n = 0 then 0 else helper n\n/// doc of helper\nand helper (n: int) : int = n - 1\n/// doc of last\nand last (n: int) : int = run n"

    match recGroupsTyped source with
    | [ s ] ->
        Assert.Equal("helper", s.MemberName)
        let patched = applyEdit source s.RemoveRange ""
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.Contains("/// doc of last\nand last", patched)
        Assert.Contains("/// doc of helper\nlet helper", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a member whose name appears only in a string is not recursive`` () =
    // the F# compiler kept `let rec` on fifteen extracted functions whose
    // only "self-call" was a failwith message naming them
    let source =
        "module Test\nlet rec run (n: int) : int = if n = 0 then 0 else helper n\nand helper (n: int) : int = if n < 0 then failwith \"helper: negative\" else n - 1"

    match recGroupsTyped source with
    | [ s ] -> Assert.StartsWith("let helper", s.InsertText)
    | other -> failwithf "Expected one extraction, got %A" other
