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
        (fsharp
            """
            let firstText (lines: string[]) =
                let mutable line = 0

                while line < lines.Length && lines.[line].Trim() = "" do
                    line <- line + 1

                line
            """)
        (fsharp
            """
            let firstText (lines: string[]) =
                let rec advanceLine line =
                    if line < lines.Length && lines.[line].Trim() = "" then advanceLine (line + 1) else line

                let line = advanceLine 0

                line
            """)

[<Fact>]
let ``a countdown retreats`` () =
    assertRewrite
        (fsharp
            """
            let lastText (lines: string[]) (taskLine: int) =
                let mutable line = taskLine - 1
                while line >= 1 && lines.[line].Trim() = "" do
                    line <- line - 1
                line
            """)
        (fsharp
            """
            let lastText (lines: string[]) (taskLine: int) =
                let rec retreatLine line =
                    if line >= 1 && lines.[line].Trim() = "" then retreatLine (line - 1) else line

                let line = retreatLine (taskLine - 1)
                line
            """)

[<Fact>]
let ``a long condition takes the multi-line if`` () =
    assertRewrite
        (fsharp
            """
            let scan (lines: string[]) (limit: int) =
                let mutable i = 0
                while i < limit && i < lines.Length && (lines.[i].Trim() = "" || lines.[i].StartsWith "//" || lines.[i].StartsWith "#") do
                    i <- i + 1
                i
            """)
        (fsharp
            """
            let scan (lines: string[]) (limit: int) =
                let rec advanceI i =
                    if
                        i < limit && i < lines.Length && (lines.[i].Trim() = "" || lines.[i].StartsWith "//" || lines.[i].StartsWith "#")
                    then
                        advanceI (i + 1)
                    else
                        i

                let i = advanceI 0
                i
            """)

[<Fact>]
let ``a later assignment keeps the mutable`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (lines: string[]) =
                    let mutable line = 0
                    while line < lines.Length && lines.[line] = "" do
                        line <- line + 1
                    line <- line + 2
                    line
                """
        )
    )

[<Fact>]
let ``a body with more than the step is not a scan`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (lines: string[]) =
                    let mutable line = 0
                    let mutable seen = 0
                    while line < lines.Length && lines.[line] = "" do
                        seen <- seen + 1
                        line <- line + 1
                    line + seen
                """
        )
    )

[<Fact>]
let ``a statement between the let and the while keeps the loop`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (lines: string[]) =
                    let mutable line = 0
                    printfn "start"
                    while line < lines.Length && lines.[line] = "" do
                        line <- line + 1
                    line
                """
        )
    )

[<Fact>]
let ``a step that reads the index is not a step`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (lines: string[]) =
                    let mutable line = 0
                    while line < lines.Length && lines.[line] = "" do
                        line <- line + line
                    line
                """
        )
    )

[<Fact>]
let ``a condition reading a Span parameter cannot move into the local function`` () =
    // the `let rec` would capture the ReadOnlySpan: FS0406
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                open System
                let skipBlanks (s: ReadOnlySpan<char>) =
                    let mutable i = 0
                    while i < s.Length && s.[i] = ' ' do
                        i <- i + 1
                    i
                """
        )
    )

[<Fact>]
let ``a struct member's primary-constructor value stays out of the local function`` () =
    // `limit` is a field of the struct's `this`, which the `let rec` cannot capture: FS0406
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                [<Struct>]
                type S(limit: int) =
                    member _.Scan(xs: int[]) =
                        let mutable i = 0
                        while i < limit && xs.[i] = 0 do
                            i <- i + 1
                        i
                """
        )
    )
