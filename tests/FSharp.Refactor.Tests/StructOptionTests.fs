module FSharp.Refactor.Tests.StructOptionTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private structOptionIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StructOption.find tree sourceText checkResults

/// Apply a suggestion's edits bottom-up and verify the patched text.
let private assertStructOption (source: string) (expectedPatched: string) =
    match structOptionIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one struct-option suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``definition and match site move to ValueOption together`` () =
    assertStructOption
        "let private tryHalf (n: int) = if n % 2 = 0 then Some(n / 2) else None\n\nlet describe (n: int) =\n    match tryHalf n with\n    | Some h -> string h\n    | None -> \"odd\""
        "let private tryHalf (n: int) = if n % 2 = 0 then ValueSome(n / 2) else ValueNone\n\nlet describe (n: int) =\n    match tryHalf n with\n    | ValueSome h -> string h\n    | ValueNone -> \"odd\""

[<Fact>]
let ``two match sites are both rewritten`` () =
    assertStructOption
        "let private pick (n: int) = if n > 0 then Some n else None\nlet a (n: int) =\n    match pick n with\n    | Some v -> v\n    | None -> 0\n\nlet b (n: int) =\n    match pick (n + 1) with\n    | Some v -> v\n    | _ -> 1"
        "let private pick (n: int) = if n > 0 then ValueSome n else ValueNone\nlet a (n: int) =\n    match pick n with\n    | ValueSome v -> v\n    | ValueNone -> 0\n\nlet b (n: int) =\n    match pick (n + 1) with\n    | ValueSome v -> v\n    | _ -> 1"

[<Fact>]
let ``use as a first-class value keeps the option`` () =
    Assert.Empty(
        structOptionIn
            "let private pick (n: int) = if n > 0 then Some n else None\nlet firsts (xs: int list) = xs |> List.tryPick pick"
    )

[<Fact>]
let ``a let-bound result keeps the option`` () =
    Assert.Empty(
        structOptionIn
            "let private pick (n: int) = if n > 0 then Some n else None\nlet f (n: int) =\n    let r = pick n\n    r |> Option.isSome"
    )

[<Fact>]
let ``public functions are left alone`` () =
    Assert.Empty(
        structOptionIn
            "let pick (n: int) = if n > 0 then Some n else None\nlet f (n: int) =\n    match pick n with\n    | Some v -> v\n    | None -> 0"
    )

[<Fact>]
let ``a non-constructor result position keeps the option`` () =
    // the body returns a computed option, not a literal constructor
    Assert.Empty(
        structOptionIn
            "let private pick (xs: int list) = List.tryHead xs\nlet f (xs: int list) =\n    match pick xs with\n    | Some v -> v\n    | None -> 0"
    )

[<Fact>]
let ``an explicit return annotation is left alone`` () =
    Assert.Empty(
        structOptionIn
            "let private pick (n: int) : int option = if n > 0 then Some n else None\nlet f (n: int) =\n    match pick n with\n    | Some v -> v\n    | None -> 0"
    )

[<Fact>]
let ``a recursive function's match on its own call moves too`` () =
    // the self-call's patterns sit inside the definition, where the use
    // scan used not to look: `| Some d` against a voption is FS0001
    assertStructOption
        "let rec private depth (n: int) =\n    if n <= 0 then Some 0\n    else\n        match depth (n - 1) with\n        | Some d -> Some (d + 1)\n        | None -> None\n\nlet show (n: int) =\n    match depth n with\n    | Some d -> string d\n    | None -> \"-\""
        "let rec private depth (n: int) =\n    if n <= 0 then ValueSome 0\n    else\n        match depth (n - 1) with\n        | ValueSome d -> ValueSome (d + 1)\n        | ValueNone -> ValueNone\n\nlet show (n: int) =\n    match depth n with\n    | ValueSome d -> string d\n    | ValueNone -> \"-\""

[<Fact>]
let ``an annotated result constructor keeps the option`` () =
    // `(ValueSome n : int option)` would not compile
    Assert.Empty(
        structOptionIn
            "let private pick (n: int) = if n > 0 then (Some n : int option) else None\nlet a (n: int) =\n    match pick n with\n    | Some v -> v\n    | None -> 0"
    )
