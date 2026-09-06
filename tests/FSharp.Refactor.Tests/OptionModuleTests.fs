module FSharp.Refactor.Tests.OptionModuleTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionModule.find tree sourceText checkResults

/// Expect exactly one suggestion; verify replacement text, target function,
/// and that the patched source still typechecks.
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
let ``Some-wrapped body with None becomes Option map`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some v -> Some (v + 1) | None -> None"
        "Option.map"
        "x |> Option.map (fun v -> v + 1)"

[<Fact>]
let ``option-returning body with None becomes Option bind`` () =
    assertSingleSuggestion
        "let g v = if v > 0 then Some v else None\nlet f (x: int option) = match x with | Some v -> g v | None -> None"
        "Option.bind"
        "x |> Option.bind (fun v -> g v)"

[<Fact>]
let ``bound variable with None becomes Option flatten`` () =
    assertSingleSuggestion
        "let f (x: int option option) = match x with | Some v -> v | None -> None"
        "Option.flatten"
        "x |> Option.flatten"

[<Fact>]
let ``rewrapped variable is the identity`` () =
    assertSingleSuggestion "let f (x: int option) = match x with | Some v -> Some v | None -> None" "" "x"

[<Fact>]
let ``bound variable with default becomes Option defaultValue`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some v -> v | None -> 0"
        "Option.defaultValue"
        "x |> Option.defaultValue 0"

[<Fact>]
let ``non-atomic default keeps its laziness with defaultWith`` () =
    // `defaultValue (d + 1)` would evaluate the default even in the Some case
    assertSingleSuggestion
        "let f (x: int option) (d: int) = match x with | Some v -> v | None -> d + 1"
        "Option.defaultWith"
        "x |> Option.defaultWith (fun () -> d + 1)"

[<Fact>]
let ``unit none-branch becomes Option iter`` () =
    assertSingleSuggestion
        "let f (g: int -> unit) (x: int option) = match x with | Some v -> g v | None -> ()"
        "Option.iter"
        "x |> Option.iter (fun v -> g v)"

[<Fact>]
let ``transformed body with default becomes map and defaultValue`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some v -> v * 2 | None -> 0"
        "Option.map + Option.defaultValue"
        "x |> Option.map (fun v -> v * 2) |> Option.defaultValue 0"

[<Fact>]
let ``transformed body with effectful default becomes map and defaultWith`` () =
    assertSingleSuggestion
        "let compute () = 42\nlet f (x: int option) = match x with | Some v -> v * 2 | None -> compute ()"
        "Option.map + Option.defaultWith"
        "x |> Option.map (fun v -> v * 2) |> Option.defaultWith (fun () -> compute ())"

[<Fact>]
let ``ValueSome match becomes ValueOption map`` () =
    assertSingleSuggestion
        "let f (x: int voption) = match x with | ValueSome v -> ValueSome (v + 1) | ValueNone -> ValueNone"
        "ValueOption.map"
        "x |> ValueOption.map (fun v -> v + 1)"

[<Fact>]
let ``ValueSome with default becomes ValueOption defaultValue`` () =
    assertSingleSuggestion
        "let f (x: int voption) = match x with | ValueSome v -> v | ValueNone -> 0"
        "ValueOption.defaultValue"
        "x |> ValueOption.defaultValue 0"

[<Fact>]
let ``true-false becomes Option isSome`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some _ -> true | None -> false"
        "Option.isSome"
        "x.IsSome"

[<Fact>]
let ``false-true becomes Option isNone`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some _ -> false | None -> true"
        "Option.isNone"
        "x.IsNone"

[<Fact>]
let ``reversed clause order is recognized`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | None -> None | Some v -> Some (v * 2)"
        "Option.map"
        "x |> Option.map (fun v -> v * 2)"

[<Fact>]
let ``wildcard Some pattern maps with underscore`` () =
    assertSingleSuggestion
        "let f (x: int option) = match x with | Some _ -> Some 1 | None -> None"
        "Option.map"
        "x |> Option.map (fun _ -> 1)"

[<Fact>]
let ``non-atomic scrutinee is parenthesized`` () =
    assertSingleSuggestion
        "let g (y: int) = if y > 0 then Some y else None\nlet f y = match g y with | Some v -> v | None -> 0"
        "Option.defaultValue"
        "(g y) |> Option.defaultValue 0"

[<Fact>]
let ``multi-line match is recognized`` () =
    assertSingleSuggestion
        "let f (x: int option) =\n    match x with\n    | Some v -> Some (v + 1)\n    | None -> None"
        "Option.map"
        "x |> Option.map (fun v -> v + 1)"

[<Fact>]
let ``shadowed Some and None cases are not rewritten`` () =
    // MyOpt shadows option's cases; rewriting to Option.map would not compile
    assertNoSuggestion
        "type MyOpt = Some of int | None\nlet f (x: MyOpt) = match x with | Some v -> Some (v + 1) | None -> None"

[<Fact>]
let ``when guard is not rewritten`` () =
    assertNoSuggestion "let f (x: int option) = match x with | Some v when v > 0 -> Some v | _ -> None"

[<Fact>]
let ``file with type errors produces no suggestions`` () =
    let tree, sourceText, checkResults =
        parseAndCheck
            "let f (x: int option) = match x with | Some v -> Some (v + 1) | None -> None\nlet broken: int = \"nope\""

    Assert.Empty(OptionModule.find tree sourceText checkResults)

[<Fact>]
let ``match with CE return bodies is not rewritten`` () =
    // `return ...` cannot move into a lambda; found by running the analyzer on itself
    assertNoSuggestion "let f (x: int option) = async { match x with | Some v -> return [ v ] | None -> return [] }"

[<Fact>]
let ``match as an infix operand is parenthesized`` () =
    // review regression: `1 + x |> Option.defaultValue 0` regroups as (1 + x) |> ...
    assertSingleSuggestion
        "let f (x: int option) = 1 + match x with | Some v -> v | None -> 0"
        "Option.defaultValue"
        "(x |> Option.defaultValue 0)"

[<Fact>]
let ``dotted default is treated as effectful and uses defaultWith`` () =
    // review regression: DateTime.Now is a property getter; defaultValue would
    // evaluate it even in the Some case
    assertSingleSuggestion
        "let f (x: System.DateTime option) = match x with | Some v -> v | None -> System.DateTime.Now"
        "Option.defaultWith"
        "x |> Option.defaultWith (fun () -> System.DateTime.Now)"

[<Fact>]
let ``a branch writing a mutable local cannot become an iter lambda`` () =
    // the arm may write `total` freely; the fabricated closure could not
    // on F# before 10 (FS0407)
    assertNoSuggestion
        "let f (x: int option) =\n    let mutable total = 0\n    match x with\n    | Some v -> total <- total + v\n    | None -> ()\n    total"

[<Fact>]
let ``a match in implicit-yield position of a comprehension is control flow`` () =
    // from Fuuga's ConfigWizard: inside [ ... ], `| None -> ()` means
    // "yield nothing" and the Some branch yields a string — rewriting to
    // Option.iter hands a string-returning lambda to a unit-wanting
    // combinator (FS0001 unit vs string)
    Assert.Empty(
        findIn
            "module Test\nlet f (g: string option) =\n    [ if true then \"A\"\n      match g with Some v -> v | None -> () ]"
    )

[<Fact>]
let ``a match bound inside a comprehension is a value again`` () =
    match
        findIn
            "module Test\nlet f (g: int option) =\n    [ let v = match g with Some v -> v | None -> 0\n      string v ]"
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one suggestion for the bound match, got %A" other

[<Fact>]
let ``an isSome test on an unannotated parameter keeps the module form`` () =
    // x's type is inferred from its later use; `x.IsSome` there is FS0072
    assertSingleSuggestion
        "let f x = let b = match x with | Some _ -> true | None -> false in if b then x |> Option.map ((+) 1) else None"
        "Option.isSome"
        "x |> Option.isSome"
