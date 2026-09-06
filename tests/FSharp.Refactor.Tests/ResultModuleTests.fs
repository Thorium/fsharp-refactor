module FSharp.Refactor.Tests.ResultModuleTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ResultModule.find tree sourceText checkResults

let private assertSingleSuggestion (source: string) (expectedTarget: string) (expectedReplacement: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedTarget, s.Target)
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``Ok-wrapped body with rewrapped error becomes Result map`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok v -> Ok (v + 1) | Error e -> Error e"
        "Result.map"
        "r |> Result.map (fun v -> v + 1)"

[<Fact>]
let ``result-returning body becomes Result bind`` () =
    assertSingleSuggestion
        "let g v : Result<int, string> = Ok v\nlet f (r: Result<int, string>) = match r with | Ok v -> g v | Error e -> Error e"
        "Result.bind"
        "r |> Result.bind (fun v -> g v)"

[<Fact>]
let ``error transformation becomes Result mapError`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok v -> Ok v | Error e -> Error (e + \"!\")"
        "Result.mapError"
        "r |> Result.mapError (fun e -> e + \"!\")"

[<Fact>]
let ``rewrapped both sides is the identity`` () =
    assertSingleSuggestion "let f (r: Result<int, string>) = match r with | Ok v -> Ok v | Error e -> Error e" "" "r"

[<Fact>]
let ``true-false becomes Result isOk`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok _ -> true | Error _ -> false"
        "Result.isOk"
        "r |> Result.isOk"

[<Fact>]
let ``false-true becomes Result isError`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok _ -> false | Error _ -> true"
        "Result.isError"
        "r |> Result.isError"

[<Fact>]
let ``bound value with pure default becomes Result defaultValue`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok v -> v | Error _ -> 0"
        "Result.defaultValue"
        "r |> Result.defaultValue 0"

[<Fact>]
let ``default mentioning the error becomes Result defaultWith`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok v -> v | Error e -> e.Length"
        "Result.defaultWith"
        "r |> Result.defaultWith (fun e -> e.Length)"

[<Fact>]
let ``unit error-branch becomes Result iter`` () =
    assertSingleSuggestion
        "let f (g: int -> unit) (r: Result<int, string>) = match r with | Ok v -> g v | Error _ -> ()"
        "Result.iter"
        "r |> Result.iter (fun v -> g v)"

[<Fact>]
let ``transformed body with default becomes map and defaultValue`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Ok v -> v * 2 | Error _ -> 0"
        "Result.map + Result.defaultValue"
        "r |> Result.map (fun v -> v * 2) |> Result.defaultValue 0"

[<Fact>]
let ``reversed clause order is recognized`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) = match r with | Error e -> Error e | Ok v -> Ok (v * 2)"
        "Result.map"
        "r |> Result.map (fun v -> v * 2)"

[<Fact>]
let ``shadowed Ok and Error cases are not rewritten`` () =
    assertNoSuggestion
        "type MyResult = Ok of int | Error of string\nlet f (x: MyResult) = match x with | Ok v -> Ok (v + 1) | Error e -> Error e"

[<Fact>]
let ``when guard is not rewritten`` () =
    assertNoSuggestion "let f (r: Result<int, string>) = match r with | Ok v when v > 0 -> Ok v | _ -> Error \"neg\""

[<Fact>]
let ``error rewrapping a different value is not map`` () =
    // Error e2 rewraps a different name: only the catch-all combo applies, and
    // that changes the error type, so nothing should typecheck-break either way
    assertNoSuggestion
        "let f (r: Result<int, string>) (other: string) = match r with | Ok v -> Ok (v + 1) | Error _ -> Error other"

[<Fact>]
let ``a unit ok arm with a logging error arm keeps its match`` () =
    // fantomas Daemon: a readable three-line match became a 190-character
    // line carrying two closures, one of them `Result.map (fun _ -> ())`
    assertNoSuggestion
        "type FantomasLogLevel =\n    | Error\n    | Info\nlet log (level: FantomasLogLevel) (message: string) = ()\nlet f (result: Result<int, string>) =\n    match result with\n    | Ok _ -> ()\n    | Error error -> log FantomasLogLevel.Error $\"Failed: {error}\""

[<Fact>]
let ``a map lambda that would return unit is withheld`` () =
    // typed: Console.WriteLine returns unit, so `Result.map (fun v ->
    // Console.WriteLine v)` would map to Result<unit, _> only to throw it
    // away (printfn would not do as the probe: its symbol returns a
    // generic 'T that only the applied format makes unit)
    assertNoSuggestion
        "let f (r: Result<int, string>) =\n    match r with\n    | Ok v -> System.Console.WriteLine v\n    | Error e -> System.Console.Error.WriteLine e"

[<Fact>]
let ``a rewrite past 100 columns is withheld`` () =
    assertNoSuggestion
        "let computeTheAdjustedValueForTheGivenResult (v: int) = v * 2\nlet f (someRatherLongResultName: Result<int, string>) =\n    match someRatherLongResultName with\n    | Ok v -> computeTheAdjustedValueForTheGivenResult v + computeTheAdjustedValueForTheGivenResult v\n    | Error _ -> 0"

[<Fact>]
let ``a tuple arm keeps its match`` () =
    assertNoSuggestion
        "let f (r: Result<int, string>) =\n    match r with\n    | Ok v -> v, true\n    | Error _ -> 0, false"

[<Fact>]
let ``a pipeline arm keeps its match`` () =
    assertNoSuggestion
        "let f (r: Result<int list, string>) =\n    match r with\n    | Ok v -> v |> List.map abs |> List.sum\n    | Error _ -> 0"

[<Fact>]
let ``a lambda arm keeps its match`` () =
    assertNoSuggestion
        "let f (r: Result<int, string>) =\n    match r with\n    | Ok v -> fun x -> x + v\n    | Error _ -> fun x -> x"

[<Fact>]
let ``a multi-line match still rewrites when the line stays short`` () =
    assertSingleSuggestion
        "let f (r: Result<int, string>) =\n    match r with\n    | Ok v -> v * 2\n    | Error _ -> 0"
        "Result.map + Result.defaultValue"
        "r |> Result.map (fun v -> v * 2) |> Result.defaultValue 0"
