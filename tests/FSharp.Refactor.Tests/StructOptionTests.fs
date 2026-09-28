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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one struct-option suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``definition and match site move to ValueOption together`` () =
    assertStructOption
        (fsharp
            """
            let private tryHalf (n: int) = if n % 2 = 0 then Some(n / 2) else None

            let describe (n: int) =
                match tryHalf n with
                | Some h -> string h
                | None -> "odd"
            """)
        (fsharp
            """
            let private tryHalf (n: int) = if n % 2 = 0 then ValueSome(n / 2) else ValueNone

            let describe (n: int) =
                match tryHalf n with
                | ValueSome h -> string h
                | ValueNone -> "odd"
            """)

[<Fact>]
let ``two match sites are both rewritten`` () =
    assertStructOption
        (fsharp
            """
            let private pick (n: int) = if n > 0 then Some n else None
            let a (n: int) =
                match pick n with
                | Some v -> v
                | None -> 0

            let b (n: int) =
                match pick (n + 1) with
                | Some v -> v
                | _ -> 1
            """)
        (fsharp
            """
            let private pick (n: int) = if n > 0 then ValueSome n else ValueNone
            let a (n: int) =
                match pick n with
                | ValueSome v -> v
                | ValueNone -> 0

            let b (n: int) =
                match pick (n + 1) with
                | ValueSome v -> v
                | _ -> 1
            """)

[<Fact>]
let ``use as a first-class value keeps the option`` () =
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let private pick (n: int) = if n > 0 then Some n else None
                let firsts (xs: int list) = xs |> List.tryPick pick
                """
        )
    )

[<Fact>]
let ``a let-bound result keeps the option`` () =
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let private pick (n: int) = if n > 0 then Some n else None
                let f (n: int) =
                    let r = pick n
                    r |> Option.isSome
                """
        )
    )

[<Fact>]
let ``public functions are left alone`` () =
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let pick (n: int) = if n > 0 then Some n else None
                let f (n: int) =
                    match pick n with
                    | Some v -> v
                    | None -> 0
                """
        )
    )

[<Fact>]
let ``a non-constructor result position keeps the option`` () =
    // the body returns a computed option, not a literal constructor
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let private pick (xs: int list) = List.tryHead xs
                let f (xs: int list) =
                    match pick xs with
                    | Some v -> v
                    | None -> 0
                """
        )
    )

[<Fact>]
let ``an explicit return annotation is left alone`` () =
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let private pick (n: int) : int option = if n > 0 then Some n else None
                let f (n: int) =
                    match pick n with
                    | Some v -> v
                    | None -> 0
                """
        )
    )

[<Fact>]
let ``a recursive function's match on its own call moves too`` () =
    // the self-call's patterns sit inside the definition, which the use
    // scan must read too: `| Some d` against a voption is FS0001
    assertStructOption
        (fsharp
            """
            let rec private depth (n: int) =
                if n <= 0 then Some 0
                else
                    match depth (n - 1) with
                    | Some d -> Some (d + 1)
                    | None -> None

            let show (n: int) =
                match depth n with
                | Some d -> string d
                | None -> "-"
            """)
        (fsharp
            """
            let rec private depth (n: int) =
                if n <= 0 then ValueSome 0
                else
                    match depth (n - 1) with
                    | ValueSome d -> ValueSome (d + 1)
                    | ValueNone -> ValueNone

            let show (n: int) =
                match depth n with
                | ValueSome d -> string d
                | ValueNone -> "-"
            """)

[<Fact>]
let ``an annotated result constructor keeps the option`` () =
    // `(ValueSome n : int option)` would not compile
    Assert.Empty(
        structOptionIn (
            fsharp
                """
                let private pick (n: int) = if n > 0 then (Some n : int option) else None
                let a (n: int) =
                    match pick n with
                    | Some v -> v
                    | None -> 0
                """
        )
    )
