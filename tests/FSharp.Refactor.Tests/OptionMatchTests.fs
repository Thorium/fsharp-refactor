module FSharp.Refactor.Tests.OptionMatchTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private optionMatchIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionMatch.find tree sourceText checkResults

let private assertOptionMatch (source: string) (expectedReplacement: string) =
    match optionMatchIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one option-match suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``IsSome with bare Value becomes a match`` () =
    assertOptionMatch "let f (x: int option) = if x.IsSome then x.Value else 0" "match x with | Some v -> v | None -> 0"

[<Fact>]
let ``a backticked option keeps its backticks and gets a plain binder`` () =
    // welendus's SignalRHubs.fs: the match spelled the ident's bare words
    // and `24h` was read as a numeric literal
    assertOptionMatch
        "let f (``in 24h period``: int option) = if ``in 24h period``.IsSome then ``in 24h period``.Value else 0"
        "match ``in 24h period`` with | Some v -> v | None -> 0"

[<Fact>]
let ``a backticked option whose v is taken falls back to a plain binder`` () =
    assertOptionMatch
        "let f (v: int) (``in 24h period``: int option) = if ``in 24h period``.IsSome then ``in 24h period``.Value + v else v"
        "match ``in 24h period`` with | Some value -> value + v | None -> v"

[<Fact>]
let ``IsNone form swaps the branches`` () =
    assertOptionMatch "let f (x: int option) = if x.IsNone then 0 else x.Value" "match x with | Some v -> v | None -> 0"

[<Fact>]
let ``negated IsSome is the IsNone form`` () =
    assertOptionMatch
        "let f (x: int option) = if not x.IsSome then 0 else x.Value"
        "match x with | Some v -> v | None -> 0"

[<Fact>]
let ``value option spells ValueSome`` () =
    assertOptionMatch
        "let f (x: int voption) = if x.IsSome then x.Value else 0"
        "match x with | ValueSome v -> v | ValueNone -> 0"

[<Fact>]
let ``Value inside a larger expression is substituted`` () =
    assertOptionMatch
        "let f (x: int option) = if x.IsSome then x.Value + 1 else 0"
        "match x with | Some v -> v + 1 | None -> 0"

[<Fact>]
let ``Value prefix of a longer path is substituted`` () =
    assertOptionMatch
        "let f (x: string option) = if x.IsSome then x.Value.Length else 0"
        "match x with | Some v -> v.Length | None -> 0"

[<Fact>]
let ``else-less unit conditional gains a unit clause`` () =
    assertOptionMatch
        """let f (x: int option) = if x.IsSome then printfn "%d" x.Value"""
        """match x with | Some v -> printfn "%d" v | None -> ()"""

[<Fact>]
let ``binder falls back when v is taken`` () =
    assertOptionMatch
        "let f (v: int) (x: int option) = if x.IsSome then x.Value + v else v"
        "match x with | Some xValue -> xValue + v | None -> v"

[<Fact>]
let ``Value in the None arm is left alone`` () =
    Assert.Empty(optionMatchIn "let f (x: int option) = if x.IsSome then 1 else x.Value")

[<Fact>]
let ``no Value use is left alone`` () =
    Assert.Empty(optionMatchIn "let f (x: int option) = if x.IsSome then 1 else 2")

[<Fact>]
let ``custom type with IsSome and Value members is left alone`` () =
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                type Box(v: int) =
                    member _.IsSome = true
                    member _.Value = v
                let f (x: Box) = if x.IsSome then x.Value else 0
                """
        )
    )

[<Fact>]
let ``a predicate reading a Span keeps the IsSome form`` () =
    // the fabricated lambda cannot capture a byref-like local
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                let f (x: int option) (bytes: byte[]) =
                    let span = System.Span<byte>(bytes)
                    x.IsSome && x.Value > span.Length
                """
        )
    )

[<Fact>]
let ``IsSome and a Value predicate becomes Option exists`` () =
    assertOptionMatch "let f (x: int option) = x.IsSome && x.Value > 3" "x |> Option.exists (fun v -> v > 3)"

[<Fact>]
let ``an and-chain of predicates joins inside the lambda`` () =
    assertOptionMatch
        "let f (x: int option) = x.IsSome && x.Value > 3 && x.Value < 10"
        "x |> Option.exists (fun v -> v > 3 && v < 10)"

[<Fact>]
let ``IsNone or a Value predicate becomes Option forall`` () =
    assertOptionMatch "let f (x: int option) = x.IsNone || x.Value > 3" "x |> Option.forall (fun v -> v > 3)"

[<Fact>]
let ``a combo without any Value use stays`` () =
    // `x.IsSome && flag` gains nothing from a lambda
    Assert.Empty(optionMatchIn "let f (x: int option) (flag: bool) = x.IsSome && flag")

[<Fact>]
let ``IsNone with && is not the exists shape`` () =
    Assert.Empty(optionMatchIn "let g (x: int option) = x.IsNone && (try x.Value > 3 with _ -> false)")

[<Fact>]
let ``a voption combo uses the ValueOption module`` () =
    assertOptionMatch "let f (x: int voption) = x.IsSome && x.Value > 3" "x |> ValueOption.exists (fun v -> v > 3)"

[<Fact>]
let ``a multiline if with single-line branches now rewrites`` () =
    assertOptionMatch
        (fsharp
            """
            let f (x: int option) =
                if x.IsSome then
                    x.Value + 1
                else
                    0
            """)
        "match x with | Some v -> v + 1 | None -> 0"

[<Fact>]
let ``the module-function spelling tests the same option`` () =
    assertOptionMatch
        "let f (x: int option) = if Option.isSome x then x.Value + 1 else 0"
        "match x with | Some v -> v + 1 | None -> 0"

[<Fact>]
let ``an elif else-arm cannot be spliced into a clause`` () =
    // its range starts at the `elif` keyword — after `| None ->` that is a
    // syntax error, not a branch
    Assert.Empty(optionMatchIn "let f (x: int option) (y: int) = if x.IsSome then x.Value + 1 elif y > 0 then 2 else 3")

[<Fact>]
let ``a predicate reading a mutable local stays a boolean chain`` () =
    // the predicates would move into an Option.exists lambda, where
    // capturing a mutable local was FS0407 before F# 10
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                let f (x: int option) =
                    let mutable total = 0
                    if x.IsSome && x.Value > total then total <- 1
                    total
                """
        )
    )

[<Fact>]
let ``IsNone chains inside a query expression stay untouched`` () =
    // inside query { } the property shape IS what the LINQ translator
    // recognizes; Option.forall with a lambda is a tree it has never seen
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                open System.Linq
                let f (xs: int list) (y: int option) =
                    query {
                        for x in xs.AsQueryable() do
                            where (y.IsNone || (y.Value > x))
                            select x
                    }
                """
        )
    )

[<Fact>]
let ``IsSome conditionals inside a quotation stay untouched`` () =
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                let f (y: int option) =
                    <@ if y.IsSome then y.Value + 1 else 0 @>
                """
        )
    )

[<Fact>]
let ``a None comparison is the same test as IsSome`` () =
    assertOptionMatch
        "let f (x: int option) = if x <> None then x.Value + 1 else 0"
        "match x with | Some v -> v + 1 | None -> 0"

[<Fact>]
let ``an equals-None comparison swaps the arms`` () =
    assertOptionMatch "let f (x: int option) = if None = x then 0 else x.Value" "match x with | Some v -> v | None -> 0"

[<Fact>]
let ``multi-line branches become a match laid out over lines`` () =
    assertOptionMatch
        (fsharp
            """
            let f (x: int option) =
                if x <> None then
                    let y = x.Value + 1
                    y * 2
                else
                    0
            """)
        (fsharp
            """
            match x with
                | Some v ->
                    let y = v + 1
                    y * 2
                | None ->
                    0
            """)

[<Fact>]
let ``an else-less multi-line unit branch gains a unit None arm`` () =
    assertOptionMatch
        (fsharp
            """
            let f (x: int option) =
                if x.IsSome then
                    printfn "%d" x.Value
                    printfn "done"
            """)
        (fsharp
            """
            match x with
                | Some v ->
                    printfn "%d" v
                    printfn "done"
                | None ->
                    ()
            """)

[<Fact>]
let ``one-line branches of a multi-line if fold to a one-line match`` () =
    assertOptionMatch
        (fsharp
            """
            let f (x: int option) =
                if x.IsSome then x.Value + 1
                else
                    0
            """)
        "match x with | Some v -> v + 1 | None -> 0"

[<Fact>]
let ``multi-line branches under an if that does not open its line stay`` () =
    // the match's clauses would sit under a `let`, not under the `if`
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                let f (x: int option) =
                    let r = if x.IsSome then
                                let y = x.Value
                                y + 1
                            else
                                0
                    r
                """
        )
    )

[<Fact>]
let ``a multi-line string inside a branch is never re-indented`` () =
    Assert.Empty(
        optionMatchIn
            "let f (x: string option) =\n    if x.IsSome then\n        let s = \"\"\"a\n  b\"\"\"\n        s + x.Value\n    else\n        \"\""
    )

[<Fact>]
let ``a struct member's primary-constructor value keeps the exists form out`` () =
    // `x` is a field of the struct's `this`, which no closure may capture: FS0406
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                module Test
                [<Struct>]
                type S(x: int) =
                    member _.M(o: int option) = o.IsSome && o.Value > x
                """
        )
    )

[<Fact>]
let ``a mutable receiver reassigned in the Some arm is left alone`` () =
    // the match binds the payload once; after `best <- ...` the original
    // reads the NEW value through best.Value and the binder the old one
    Assert.Empty(
        optionMatchIn (
            fsharp
                """
                let f () =
                    let mutable best = Some 1
                    if best.IsSome then
                        best <- Some (best.Value + 10)
                        printfn "%d" best.Value
                """
        )
    )
