module FSharp.Refactor.Tests.SprintfInterpolationTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0042 SprintfInterpolation ----

let private sprintfIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SprintfInterpolation.find tree sourceText checkResults

let private assertSprintfFix (source: string) (expectedReplacement: string) =
    match sprintfIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one sprintf suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``single argument sprintf becomes typed interpolation`` () =
    assertSprintfFix "module Test\nlet f (x: string) = sprintf \"asdf %s\" x" "$\"asdf %s{x}\""

[<Fact>]
let ``multiple arguments splice in order`` () =
    assertSprintfFix
        (fsharp
            """
            module Test
            let f (name: string) (count: int) = sprintf "%s has %d items" name count
            """)
        "$\"%s{name} has %d{count} items\""

[<Fact>]
let ``width and precision specifiers survive`` () =
    assertSprintfFix
        (fsharp
            """
            module Test
            let f (price: float) = sprintf "cost: %0.2f eur" price
            """)
        "$\"cost: %0.2f{price} eur\""

[<Fact>]
let ``escaped percent is not a specifier`` () =
    assertSprintfFix "module Test\nlet f (n: int) = sprintf \"%d%% done\" n" "$\"%d{n}%% done\""

[<Fact>]
let ``braces in the format leave the call alone`` () =
    Assert.Empty(sprintfIn "module Test\nlet f (x: string) = sprintf \"{%s}\" x")

[<Fact>]
let ``partial application is left alone`` () =
    Assert.Empty(sprintfIn "module Test\nlet f : string -> string = sprintf \"%s!\"")

[<Fact>]
let ``function specifiers are left alone`` () =
    Assert.Empty(
        sprintfIn (
            fsharp
                """
                module Test
                let f (w: unit -> string) = sprintf "%t" (fun _ -> "x")
                """
        )
    )

[<Fact>]
let ``complex arguments are left alone`` () =
    Assert.Empty(
        sprintfIn (
            fsharp
                """
                module Test
                let f (xs: int list) = sprintf "%d" (List.sum xs)
                """
        )
    )

// ---- FR0043 TypedHoles ----

let private holesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TypedHoles.find tree sourceText checkResults

let private assertHoleFix (source: string) (expectedPatched: string) =
    match holesIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.Specifier
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one hole suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``untyped int hole in a typed string gains a specifier`` () =
    assertHoleFix
        "let f (name: string) (age: int) = $\"%s{name} is {age}\""
        "let f (name: string) (age: int) = $\"%s{name} is %d{age}\""

[<Fact>]
let ``untyped string hole gains percent-s`` () =
    assertHoleFix
        "let f (name: string) (city: string) = $\"%s{name} from {city}\""
        "let f (name: string) (city: string) = $\"%s{name} from %s{city}\""

[<Fact>]
let ``specifier-free interpolation stays on the fast path`` () =
    Assert.Empty(holesIn "let f (name: string) (age: int) = $\"{name} is {age}\"")

[<Fact>]
let ``bool holes stay untyped because percent-b lowercases`` () =
    Assert.Empty(holesIn "let f (ok: bool) (n: int) = $\"%d{n} ok: {ok}\"")

[<Fact>]
let ``float holes stay untyped because percent-f pads`` () =
    Assert.Empty(holesIn "let f (price: float) (n: int) = $\"%d{n} at {price}\"")

[<Fact>]
let ``the qualified Printf spelling converts too`` () =
    assertSprintfFix "module Test\nlet f (x: string) = Printf.sprintf \"asdf %s\" x" "$\"asdf %s{x}\""
