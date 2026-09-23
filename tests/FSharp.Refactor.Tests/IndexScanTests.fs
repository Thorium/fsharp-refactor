module FSharp.Refactor.Tests.IndexScanTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    IndexScan.find tree sourceText checkResults

let private assertRewrite (source: string) (expected: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expected, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``an ascending scan becomes a tail-recursive function`` () =
    assertRewrite
        "let firstText (lines: string[]) =\n    let mutable line = 0\n\n    while line < lines.Length && lines.[line].Trim() = \"\" do\n        line <- line + 1\n\n    line"
        "let firstText (lines: string[]) =\n    let rec advanceLine line =\n        if line < lines.Length && lines.[line].Trim() = \"\" then advanceLine (line + 1) else line\n\n    let line = advanceLine 0\n\n    line"

[<Fact>]
let ``a countdown retreats`` () =
    assertRewrite
        "let lastText (lines: string[]) (taskLine: int) =\n    let mutable line = taskLine - 1\n    while line >= 1 && lines.[line].Trim() = \"\" do\n        line <- line - 1\n    line"
        "let lastText (lines: string[]) (taskLine: int) =\n    let rec retreatLine line =\n        if line >= 1 && lines.[line].Trim() = \"\" then retreatLine (line - 1) else line\n\n    let line = retreatLine (taskLine - 1)\n    line"

[<Fact>]
let ``a long condition takes the multi-line if`` () =
    assertRewrite
        "let scan (lines: string[]) (limit: int) =\n    let mutable i = 0\n    while i < limit && i < lines.Length && (lines.[i].Trim() = \"\" || lines.[i].StartsWith \"//\" || lines.[i].StartsWith \"#\") do\n        i <- i + 1\n    i"
        "let scan (lines: string[]) (limit: int) =\n    let rec advanceI i =\n        if\n            i < limit && i < lines.Length && (lines.[i].Trim() = \"\" || lines.[i].StartsWith \"//\" || lines.[i].StartsWith \"#\")\n        then\n            advanceI (i + 1)\n        else\n            i\n\n    let i = advanceI 0\n    i"

[<Fact>]
let ``a later assignment keeps the mutable`` () =
    Assert.Empty(
        findIn
            "let f (lines: string[]) =\n    let mutable line = 0\n    while line < lines.Length && lines.[line] = \"\" do\n        line <- line + 1\n    line <- line + 2\n    line"
    )

[<Fact>]
let ``a body with more than the step is not a scan`` () =
    Assert.Empty(
        findIn
            "let f (lines: string[]) =\n    let mutable line = 0\n    let mutable seen = 0\n    while line < lines.Length && lines.[line] = \"\" do\n        seen <- seen + 1\n        line <- line + 1\n    line + seen"
    )

[<Fact>]
let ``a statement between the let and the while keeps the loop`` () =
    Assert.Empty(
        findIn
            "let f (lines: string[]) =\n    let mutable line = 0\n    printfn \"start\"\n    while line < lines.Length && lines.[line] = \"\" do\n        line <- line + 1\n    line"
    )

[<Fact>]
let ``a step that reads the index is not a step`` () =
    Assert.Empty(
        findIn
            "let f (lines: string[]) =\n    let mutable line = 0\n    while line < lines.Length && lines.[line] = \"\" do\n        line <- line + line\n    line"
    )

[<Fact>]
let ``a condition reading a Span parameter cannot move into the local function`` () =
    // the `let rec` would capture the ReadOnlySpan: FS0406
    Assert.Empty(
        findIn
            "module T\nopen System\nlet skipBlanks (s: ReadOnlySpan<char>) =\n    let mutable i = 0\n    while i < s.Length && s.[i] = ' ' do\n        i <- i + 1\n    i"
    )

[<Fact>]
let ``a struct member's primary-constructor value stays out of the local function`` () =
    // `limit` is a field of the struct's `this`, which the `let rec` cannot capture: FS0406
    Assert.Empty(
        findIn
            "module T\n[<Struct>]\ntype S(limit: int) =\n    member _.Scan(xs: int[]) =\n        let mutable i = 0\n        while i < limit && xs.[i] = 0 do\n            i <- i + 1\n        i"
    )
