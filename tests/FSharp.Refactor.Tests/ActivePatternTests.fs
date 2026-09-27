module FSharp.Refactor.Tests.ActivePatternTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ActivePattern.find true tree sourceText checkResults

/// Apply both edits of the suggestion (clause first — it sits later in the
/// document — then the insertion) and verify the result typechecks.
let private assertSingleSuggestion (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.ClauseRange s.ClauseText
        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``dotted guard function becomes an active pattern`` () =
    assertSingleSuggestion
        (fsharp
            """
            module Test
            let describe (s: string) =
                match s with
                | s when System.String.IsNullOrEmpty s -> "empty"
                | s -> s
            """)
        // a .NET member's extracted input is annotated with its resolved
        // parameter type — for the overloaded ones (Path.IsPathRooted) it
        // is the difference between compiling and FS0041
        (fsharp
            """
            module Test
            [<return: Struct>]
            let inline private (|IsNullOrEmpty|_|) (input: string) =
                if System.String.IsNullOrEmpty input then ValueSome input else ValueNone

            let describe (s: string) =
                match s with
                | IsNullOrEmpty _ -> "empty"
                | s -> s
            """)

[<Fact>]
let ``module-level guard function becomes an active pattern`` () =
    assertSingleSuggestion
        (fsharp
            """
            module Test
            let isEven (n: int) = n % 2 = 0
            let f x =
                match x with
                | n when isEven n -> n
                | n -> 0
            """)
        (fsharp
            """
            module Test
            let isEven (n: int) = n % 2 = 0
            [<return: Struct>]
            let inline private (|IsEven|_|) input =
                if isEven input then ValueSome input else ValueNone

            let f x =
                match x with
                | IsEven n -> n
                | n -> 0
            """)

[<Fact>]
let ``locally defined guard function is not extracted`` () =
    // the generated binding would sit outside isOdd's scope
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f x =
                let isOdd (n: int) = n % 2 = 1
                match x with
                | n when isOdd n -> n
                | _ -> 0
            """
    )

[<Fact>]
let ``guard using a lambda parameter function is not extracted`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (check: int -> bool) x =
                match x with
                | n when check n -> n
                | _ -> 0
            """
    )

[<Fact>]
let ``existing pattern of the same name suppresses the hint`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let isEven (n: int) = n % 2 = 0
            let (|IsEven|_|) (n: int) = if isEven n then Some n else None
            let f x =
                match x with
                | n when isEven n -> n
                | _ -> 0
            """
    )

[<Fact>]
let ``complex guard expression is not extracted`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f x =
                match x with
                | n when n % 2 = 0 -> n
                | _ -> 0
            """
    )

[<Fact>]
let ``guard applied to a different value is not extracted`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let isEven (n: int) = n % 2 = 0
            let f x y =
                match x with
                | n when isEven y -> n
                | _ -> 0
            """
    )

[<Fact>]
let ``guard inside a member is not extracted`` () =
    // review regression: the inserted binding would sit before the type, where
    // the member parameter is out of scope
    assertNoSuggestion (
        fsharp
            """
            module Test
            type T() =
                member _.Check f x =
                    match x with
                    | n when f n -> 1
                    | _ -> 0
            """
    )

[<Fact>]
let ``repeated guards yield a single suggestion`` () =
    // review regression: applying two identical insertions would produce a
    // duplicate definition
    let suggestions =
        findIn (
            fsharp
                """
                module Test
                let isEven (n: int) = n % 2 = 0
                let f x =
                    match x with
                    | n when isEven n -> n
                    | _ -> 0
                let g y =
                    match y with
                    | n when isEven n -> n
                    | _ -> 1
                """
        )

    Assert.Equal(1, List.length suggestions)

[<Fact>]
let ``an overloaded method guard annotates the extracted input`` () =
    // from Fuuga: Path.IsPathRooted takes string OR ReadOnlySpan<char>; the
    // extracted pattern's `input` has no inference context, so the resolved
    // parameter type is spelled out
    match
        findIn (
            fsharp
                """
                module Test
                open System.IO
                let f (p: string) =
                    match p with
                    | q when Path.IsPathRooted q -> q
                    | q -> q
                """
        )
    with
    | [ s ] ->
        Assert.Contains("(input: string)", s.InsertText)

        let patched =
            applyEdit
                (fsharp
                    """
                    module Test
                    open System.IO
                    let f (p: string) =
                        match p with
                        | q when Path.IsPathRooted q -> q
                        | q -> q
                    """)
                s.ClauseRange
                s.ClauseText

        let patched = applyEdit patched s.InsertRange s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one annotated suggestion, got %A" other

[<Fact>]
let ``a guard variable the body never reads becomes a wildcard`` () =
    // `| c when Char.IsDigit c -> Decimal` bound `c` only for the guard;
    // `| IsDigit c -> Decimal` would leave it unused, FS1182 — an error
    // under warnings-as-errors (FsAutoComplete's AdjustConstant)
    assertSingleSuggestion
        (fsharp
            """
            module Test
            let kind (ch: char) =
                match ch with
                | c when System.Char.IsDigit c -> "digit"
                | _ -> "other"
            """)
        (fsharp
            """
            module Test
            [<return: Struct>]
            let inline private (|IsDigit|_|) (input: char) =
                if System.Char.IsDigit input then ValueSome input else ValueNone

            let kind (ch: char) =
                match ch with
                | IsDigit _ -> "digit"
                | _ -> "other"
            """)

[<Fact>]
let ``a declaration left of its siblings' column gets no pattern`` () =
    // TypeProviders SDK's Codebuf: a `let` the compiler tolerates offside of
    // the module body; an attribute line spliced at its column attaches to
    // nothing
    let offside =
        fsharp
            """
            module Test
            module Inner =
                let a = 1
               let isX (i: int) = i > 0
                let f i =
                    match i with
                    | x when isX x -> x
                    | _ -> 0
            """

    let tree, sourceText, checkResults = parseAndCheck offside
    Assert.Empty(ActivePattern.find true tree sourceText checkResults)

    let aligned =
        fsharp
            """
            module Test
            module Inner =
                let isX (i: int) = i > 0
                let f i =
                    match i with
                    | x when isX x -> x
                    | _ -> 0
            """

    let tree, sourceText, checkResults = parseAndCheck aligned
    Assert.Single(ActivePattern.find true tree sourceText checkResults) |> ignore

[<Fact>]
let ``an offside declaration two modules deep under a namespace gets no pattern either`` () =
    // the TypeProviders SDK's exact nesting: namespace, module, nested
    // module whose first declaration sits one column right of the offender
    let source =
        fsharp
            """
            namespace Provider
            module Outer =
                let isX (i: int) = i > 0
                module Codebuf =
                     let first = 1
                    let f i =
                        match i with
                        | x when isX x -> x
                        | _ -> 0
            """

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(ActivePattern.find true tree sourceText checkResults)

[<Fact>]
let ``an old FSharp.Core gets the option-returning pattern`` () =
    // the TypeProviders SDK pins FSharp.Core 4.7, where `[<return: Struct>]`
    // does not exist: the attribute attached to nothing and the pattern
    // was refused
    let source =
        fsharp
            """
            module Test
            let isX (i: int) = i > 0
            let f i =
                match i with
                | x when isX x -> x
                | _ -> 0
            """

    let tree, sourceText, checkResults = parseAndCheck source

    match ActivePattern.find false tree sourceText checkResults with
    | [ s ] ->
        Assert.DoesNotContain("Struct", s.InsertText)
        Assert.Contains("then Some input else None", s.InsertText)
    | other -> failwithf "Expected one pattern, got %A" other

[<Fact>]
let ``a guard under #if yields a pattern under the same #if`` () =
    // a line generated from a conditional branch and lifted to module
    // level must keep its condition: freed of it, the definition would
    // need names that only exist under it
    let source =
        fsharp
            """
            module Test
            open System.IO
            let f (p: string) =
            #if !FOO
                match p with
                | q when Path.IsPathRooted q -> q
                | q -> q
            #else
                p
            #endif
            """

    match findIn source with
    | [ s ] ->
        Assert.StartsWith(
            fsharp
                """
                #if !FOO

                """,
            s.InsertText
        )

        Assert.Contains(
            fsharp
                """

                #endif

                """,
            s.InsertText
        )
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0006: a guard function bound by the declaration itself is never extracted`` () =
    // a parameter on its own line, a nested pattern binder, and a `let
    // rec ... and` sibling: all bound inside the declaration, none in scope
    // above it
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f
                (isOk: int -> bool)
                x =
                match x with
                | n when isOk n -> n
                | _ -> 0
            """
    )

    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (pair: (int -> bool) * int) =
                match pair with
                | (isOk, x) ->
                    match x with
                    | n when isOk n -> n
                    | _ -> 0
            """
    )

    assertNoSuggestion (
        fsharp
            """
            module Test
            let rec f x =
                match x with
                | n when isOk n -> n
                | _ -> 0
            and isOk (n: int) = n > 0
            """
    )

[<Fact>]
let ``FR0006: a guard variable ending in a prime is still read by the body`` () =
    match
        findIn (
            fsharp
                """
                module Test
                let isEven (n: int) = n % 2 = 0
                let f x =
                    match x with
                    | n' when isEven n' -> n' + 1
                    | _ -> 0
                """
        )
    with
    | [ s ] -> Assert.Equal("IsEven n'", s.ClauseText)
    | other -> failwithf "Expected one suggestion, got %A" other
