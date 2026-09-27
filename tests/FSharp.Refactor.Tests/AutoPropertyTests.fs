module FSharp.Refactor.Tests.AutoPropertyTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0026 AutoProperty ----

let private autoPropIn (source: string) =
    let tree, sourceText = parse source
    AutoProperty.find tree sourceText

/// Apply a suggestion's edits bottom-up and verify the patched text.
let private assertAutoProp (source: string) (expectedPatched: string) =
    match autoPropIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one auto-property suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``backing field with trivial accessors becomes member val`` () =
    assertAutoProp
        (fsharp
            """
            module Test
            type Person() =
                let mutable name = ""
                member this.Name
                    with get () = name
                    and set v = name <- v
            """)
        (fsharp
            """
            module Test
            type Person() =
                member val Name = "" with get, set
            """)

[<Fact>]
let ``other members survive around the collapse`` () =
    assertAutoProp
        (fsharp
            """
            module Test
            type Person() =
                let mutable age = 0
                member _.Greet() = "hi"
                member this.Age
                    with get () = age
                    and set v = age <- v
            """)
        (fsharp
            """
            module Test
            type Person() =
                member _.Greet() = "hi"
                member val Age = 0 with get, set
            """)

[<Fact>]
let ``backing field used by another member is left alone`` () =
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let mutable name = ""
                    member _.Shout() = name.ToUpper()
                    member this.Name
                        with get () = name
                        and set v = name <- v
                """
        )
    )

[<Fact>]
let ``setter with extra logic is left alone`` () =
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let mutable name = ""
                    member this.Name
                        with get () = name
                        and set v = name <- v.ToString()
                """
        )
    )

[<Fact>]
let ``getter computing a value is left alone`` () =
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let mutable name = ""
                    member this.Name
                        with get () = name.Trim()
                        and set v = name <- v
                """
        )
    )

[<Fact>]
let ``effectful initializer is left alone`` () =
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let mutable stamp = System.DateTime.Now.Ticks
                    member this.Stamp
                        with get () = stamp
                        and set v = stamp <- v
                """
        )
    )

[<Fact>]
let ``immutable backing field is left alone`` () =
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let name = ""
                    member this.Name with get () = name
                """
        )
    )

// ---- FR0007 type-level extension ----

let private mutablesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MutableRemoval.find tree sourceText checkResults

[<Fact>]
let ``type-level mutable never assigned is flagged`` () =
    let suggestions =
        mutablesIn (
            fsharp
                """
                type Holder() =
                    let mutable cache = ""
                    member _.Show() = cache
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("cache", s.Name)
    | other -> failwithf "Expected exactly one type-level mutable suggestion, got %A" other

[<Fact>]
let ``type-level mutable assigned in a member is left alone`` () =
    Assert.Empty(
        mutablesIn (
            fsharp
                """
                type Holder() =
                    let mutable cache = ""
                    member _.Store(v: string) = cache <- v
                    member _.Show() = cache
                """
        )
    )

[<Fact>]
let ``static type-level mutable never assigned is flagged`` () =
    let suggestions =
        mutablesIn (
            fsharp
                """
                type Holder() =
                    static let mutable shared = ""
                    member _.Show() = shared
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("shared", s.Name)
    | other -> failwithf "Expected exactly one static mutable suggestion, got %A" other

[<Fact>]
let ``an attributed accessor keeps its shape`` () =
    // the member-val rewrite replaces the member's whole range, which
    // includes the attribute list — [<Obsolete>] would silently vanish
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Person() =
                    let mutable name = ""
                    [<System.Obsolete "use X">]
                    member this.Name
                        with get () = name
                        and set v = name <- v
                """
        )
    )

[<Fact>]
let ``an override or default get-set pair is not an auto-property`` () =
    // `member val` declares a NEW slot: over an abstract one it hides the
    // override (FS0864) or fails to implement it
    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                [<AbstractClass>]
                type Base() =
                    abstract Name: string with get, set
                type Person() =
                    inherit Base()
                    let mutable name = ""
                    override this.Name
                        with get () = name
                        and set v = name <- v
                """
        )
    )

    Assert.Empty(
        autoPropIn (
            fsharp
                """
                module Test
                type Base() =
                    let mutable name = ""
                    abstract Name: string with get, set
                    default this.Name
                        with get () = name
                        and set v = name <- v
                """
        )
    )
