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
        "module Test\nlet describe (s: string) =\n    match s with\n    | s when System.String.IsNullOrEmpty s -> \"empty\"\n    | s -> s"
        // a .NET member's extracted input is annotated with its resolved
        // parameter type — for the overloaded ones (Path.IsPathRooted) it
        // is the difference between compiling and FS0041
        "module Test\n[<return: Struct>]\nlet inline private (|IsNullOrEmpty|_|) (input: string) =\n    if System.String.IsNullOrEmpty input then ValueSome input else ValueNone\n\nlet describe (s: string) =\n    match s with\n    | IsNullOrEmpty _ -> \"empty\"\n    | s -> s"

[<Fact>]
let ``module-level guard function becomes an active pattern`` () =
    assertSingleSuggestion
        "module Test\nlet isEven (n: int) = n % 2 = 0\nlet f x =\n    match x with\n    | n when isEven n -> n\n    | n -> 0"
        "module Test\nlet isEven (n: int) = n % 2 = 0\n[<return: Struct>]\nlet inline private (|IsEven|_|) input =\n    if isEven input then ValueSome input else ValueNone\n\nlet f x =\n    match x with\n    | IsEven n -> n\n    | n -> 0"

[<Fact>]
let ``locally defined guard function is not extracted`` () =
    // the generated binding would sit outside isOdd's scope
    assertNoSuggestion
        "module Test\nlet f x =\n    let isOdd (n: int) = n % 2 = 1\n    match x with\n    | n when isOdd n -> n\n    | _ -> 0"

[<Fact>]
let ``guard using a lambda parameter function is not extracted`` () =
    assertNoSuggestion
        "module Test\nlet f (check: int -> bool) x =\n    match x with\n    | n when check n -> n\n    | _ -> 0"

[<Fact>]
let ``existing pattern of the same name suppresses the hint`` () =
    assertNoSuggestion
        "module Test\nlet isEven (n: int) = n % 2 = 0\nlet (|IsEven|_|) (n: int) = if isEven n then Some n else None\nlet f x =\n    match x with\n    | n when isEven n -> n\n    | _ -> 0"

[<Fact>]
let ``complex guard expression is not extracted`` () =
    assertNoSuggestion "module Test\nlet f x =\n    match x with\n    | n when n % 2 = 0 -> n\n    | _ -> 0"

[<Fact>]
let ``guard applied to a different value is not extracted`` () =
    assertNoSuggestion
        "module Test\nlet isEven (n: int) = n % 2 = 0\nlet f x y =\n    match x with\n    | n when isEven y -> n\n    | _ -> 0"

[<Fact>]
let ``guard inside a member is not extracted`` () =
    // review regression: the inserted binding would sit before the type, where
    // the member parameter is out of scope
    assertNoSuggestion
        "module Test\ntype T() =\n    member _.Check f x =\n        match x with\n        | n when f n -> 1\n        | _ -> 0"

[<Fact>]
let ``repeated guards yield a single suggestion`` () =
    // review regression: applying two identical insertions would produce a
    // duplicate definition
    let suggestions =
        findIn
            "module Test\nlet isEven (n: int) = n % 2 = 0\nlet f x =\n    match x with\n    | n when isEven n -> n\n    | _ -> 0\nlet g y =\n    match y with\n    | n when isEven n -> n\n    | _ -> 1"

    Assert.Equal(1, List.length suggestions)

[<Fact>]
let ``an overloaded method guard annotates the extracted input`` () =
    // from Fuuga: Path.IsPathRooted takes string OR ReadOnlySpan<char>; the
    // extracted pattern's `input` has no inference context, so the resolved
    // parameter type is spelled out
    match
        findIn
            "module Test\nopen System.IO\nlet f (p: string) =\n    match p with\n    | q when Path.IsPathRooted q -> q\n    | q -> q"
    with
    | [ s ] ->
        Assert.Contains("(input: string)", s.InsertText)

        let patched =
            applyEdit
                "module Test\nopen System.IO\nlet f (p: string) =\n    match p with\n    | q when Path.IsPathRooted q -> q\n    | q -> q"
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
        "module Test\nlet kind (ch: char) =\n    match ch with\n    | c when System.Char.IsDigit c -> \"digit\"\n    | _ -> \"other\""
        "module Test\n[<return: Struct>]\nlet inline private (|IsDigit|_|) (input: char) =\n    if System.Char.IsDigit input then ValueSome input else ValueNone\n\nlet kind (ch: char) =\n    match ch with\n    | IsDigit _ -> \"digit\"\n    | _ -> \"other\""

[<Fact>]
let ``a declaration left of its siblings' column gets no pattern`` () =
    // TypeProviders SDK's Codebuf: a `let` the compiler tolerates offside of
    // the module body; an attribute line spliced at its column attaches to
    // nothing
    let offside =
        "module Test\nmodule Inner =\n     let isX (i: int) = i > 0\n    let f i =\n        match i with\n        | x when isX x -> x\n        | _ -> 0"

    let tree, sourceText, checkResults = parseAndCheck offside
    Assert.Empty(ActivePattern.find true tree sourceText checkResults)

    let aligned =
        "module Test\nmodule Inner =\n    let isX (i: int) = i > 0\n    let f i =\n        match i with\n        | x when isX x -> x\n        | _ -> 0"

    let tree, sourceText, checkResults = parseAndCheck aligned
    Assert.Single(ActivePattern.find true tree sourceText checkResults) |> ignore

[<Fact>]
let ``an offside declaration two modules deep under a namespace gets no pattern either`` () =
    // the TypeProviders SDK's exact nesting: namespace, module, nested
    // module whose first declaration sits one column right of the offender
    let source =
        "namespace Provider\nmodule Outer =\n    let isX (i: int) = i > 0\n    module Codebuf =\n         let first = 1\n        let f i =\n            match i with\n            | x when isX x -> x\n            | _ -> 0"

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(ActivePattern.find true tree sourceText checkResults)

[<Fact>]
let ``an old FSharp.Core gets the option-returning pattern`` () =
    // the TypeProviders SDK pins FSharp.Core 4.7, where `[<return: Struct>]`
    // does not exist: the attribute attached to nothing and the pattern
    // was refused
    let source =
        "module Test\nlet isX (i: int) = i > 0\nlet f i =\n    match i with\n    | x when isX x -> x\n    | _ -> 0"

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
        "module Test\nopen System.IO\nlet f (p: string) =\n#if !FOO\n    match p with\n    | q when Path.IsPathRooted q -> q\n    | q -> q\n#else\n    p\n#endif"

    match findIn source with
    | [ s ] ->
        Assert.StartsWith("#if !FOO\n", s.InsertText)
        Assert.Contains("\n#endif\n", s.InsertText)
    | other -> failwithf "Expected one suggestion, got %A" other
