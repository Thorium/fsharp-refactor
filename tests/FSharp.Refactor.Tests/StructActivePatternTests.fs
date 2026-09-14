module FSharp.Refactor.Tests.StructActivePatternTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StructActivePattern.find false tree sourceText checkResults

/// The same scan with API changes allowed, as `fsharp-refactor
/// --api-changes` runs it.
let private findWithApiChangesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StructActivePattern.find true tree sourceText checkResults

/// Apply all edits bottom-up and verify the result against expectation and
/// the typechecker (which also proves the call sites still work unchanged).
let private assertPatched
    (suggestions: StructActivePattern.Suggestion list)
    (source: string)
    (expectedPatched: string)
    =
    match suggestions with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
            |> List.fold (fun acc e -> applyEdit acc e.Range e.Replacement) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertSingleSuggestion (source: string) (expectedPatched: string) =
    assertPatched (findIn source) source expectedPatched

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``a body split by a directive is left alone`` () =
    // Thoth.Json.Core.Auto: only the active branch would turn ValueSome,
    // and the Fable-define build failed under the new attribute
    assertNoSuggestion
        "module Test\nlet private (|Even|_|) (n: int) =\n#if FABLE_COMPILER\n    if n % 2 = 0 then Some n else None\n#else\n    if n % 2 = 0 then Some n else None\n#endif"

[<Fact>]
let ``if-based partial active pattern becomes struct-returning`` () =
    assertSingleSuggestion
        "let private (|Even|_|) (n: int) = if n % 2 = 0 then Some n else None\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"
        "[<return: Struct>]\nlet private (|Even|_|) (n: int) = if n % 2 = 0 then ValueSome n else ValueNone\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``match-based partial active pattern becomes struct-returning`` () =
    assertSingleSuggestion
        "let private (|Positive|_|) (n: int) =\n    match n with\n    | n when n > 0 -> Some n\n    | _ -> None\nlet f x =\n    match x with\n    | Positive v -> v\n    | _ -> 0"
        "[<return: Struct>]\nlet private (|Positive|_|) (n: int) =\n    match n with\n    | n when n > 0 -> ValueSome n\n    | _ -> ValueNone\nlet f x =\n    match x with\n    | Positive v -> v\n    | _ -> 0"

[<Fact>]
let ``a public active pattern is left alone`` () =
    // the representation change is invisible to match sites but not to
    // explicit or first-class uses, which outside this assembly we cannot see
    assertNoSuggestion
        "let (|Even|_|) (n: int) = if n % 2 = 0 then Some n else None\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``a public active pattern is offered under api changes`` () =
    let source =
        "let (|Even|_|) (n: int) = if n % 2 = 0 then Some n else None\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

    assertPatched
        (findWithApiChangesIn source)
        source
        "[<return: Struct>]\nlet (|Even|_|) (n: int) = if n % 2 = 0 then ValueSome n else ValueNone\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``pattern with existing attribute is not touched`` () =
    assertNoSuggestion
        "[<return: Struct>]\nlet private (|Even|_|) (n: int) = if n % 2 = 0 then ValueSome n else ValueNone\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``pattern with return annotation is not touched`` () =
    // the `option` annotation would need to become `voption`
    assertNoSuggestion
        "let private (|Even|_|) (n: int) : int option = if n % 2 = 0 then Some n else None\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``pattern delegating to a helper is not touched`` () =
    // the helper returns an option; the result shape is not literal Some/None
    assertNoSuggestion
        "let private check (n: int) = if n % 2 = 0 then Some n else None\nlet private (|Even|_|) (n: int) = check n\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

[<Fact>]
let ``total active pattern is not touched`` () =
    assertNoSuggestion
        "let private (|Odd|Even|) (n: int) = if n % 2 = 1 then Odd else Even\nlet f x =\n    match x with\n    | Odd -> 1\n    | Even -> 0"

[<Fact>]
let ``ordinary function returning option is not touched`` () =
    assertNoSuggestion "let private tryPositive (n: int) = if n > 0 then Some n else None"
