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
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one auto-property suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``backing field with trivial accessors becomes member val`` () =
    assertAutoProp
        "module Test\ntype Person() =\n    let mutable name = \"\"\n    member this.Name\n        with get () = name\n        and set v = name <- v"
        "module Test\ntype Person() =\n    member val Name = \"\" with get, set"

[<Fact>]
let ``other members survive around the collapse`` () =
    assertAutoProp
        "module Test\ntype Person() =\n    let mutable age = 0\n    member _.Greet() = \"hi\"\n    member this.Age\n        with get () = age\n        and set v = age <- v"
        "module Test\ntype Person() =\n    member _.Greet() = \"hi\"\n    member val Age = 0 with get, set"

[<Fact>]
let ``backing field used by another member is left alone`` () =
    Assert.Empty(
        autoPropIn
            "module Test\ntype Person() =\n    let mutable name = \"\"\n    member _.Shout() = name.ToUpper()\n    member this.Name\n        with get () = name\n        and set v = name <- v"
    )

[<Fact>]
let ``setter with extra logic is left alone`` () =
    Assert.Empty(
        autoPropIn
            "module Test\ntype Person() =\n    let mutable name = \"\"\n    member this.Name\n        with get () = name\n        and set v = name <- v.ToString()"
    )

[<Fact>]
let ``getter computing a value is left alone`` () =
    Assert.Empty(
        autoPropIn
            "module Test\ntype Person() =\n    let mutable name = \"\"\n    member this.Name\n        with get () = name.Trim()\n        and set v = name <- v"
    )

[<Fact>]
let ``effectful initializer is left alone`` () =
    Assert.Empty(
        autoPropIn
            "module Test\ntype Person() =\n    let mutable stamp = System.DateTime.Now.Ticks\n    member this.Stamp\n        with get () = stamp\n        and set v = stamp <- v"
    )

[<Fact>]
let ``immutable backing field is left alone`` () =
    Assert.Empty(
        autoPropIn "module Test\ntype Person() =\n    let name = \"\"\n    member this.Name with get () = name"
    )

// ---- FR0007 type-level extension ----

let private mutablesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MutableRemoval.find tree sourceText checkResults

[<Fact>]
let ``type-level mutable never assigned is flagged`` () =
    let suggestions =
        mutablesIn "type Holder() =\n    let mutable cache = \"\"\n    member _.Show() = cache"

    match suggestions with
    | [ s ] -> Assert.Equal("cache", s.Name)
    | other -> failwithf "Expected exactly one type-level mutable suggestion, got %A" other

[<Fact>]
let ``type-level mutable assigned in a member is left alone`` () =
    Assert.Empty(
        mutablesIn
            "type Holder() =\n    let mutable cache = \"\"\n    member _.Store(v: string) = cache <- v\n    member _.Show() = cache"
    )

[<Fact>]
let ``static type-level mutable never assigned is flagged`` () =
    let suggestions =
        mutablesIn "type Holder() =\n    static let mutable shared = \"\"\n    member _.Show() = shared"

    match suggestions with
    | [ s ] -> Assert.Equal("shared", s.Name)
    | other -> failwithf "Expected exactly one static mutable suggestion, got %A" other

[<Fact>]
let ``an attributed accessor keeps its shape`` () =
    // the member-val rewrite replaces the member's whole range, which
    // includes the attribute list — [<Obsolete>] would silently vanish
    Assert.Empty(
        autoPropIn
            "module Test\ntype Person() =\n    let mutable name = \"\"\n    [<System.Obsolete \"use X\">]\n    member this.Name\n        with get () = name\n        and set v = name <- v"
    )

[<Fact>]
let ``an override or default get-set pair is not an auto-property`` () =
    // `member val` declares a NEW slot: over an abstract one it hides the
    // override (FS0864) or fails to implement it
    Assert.Empty(
        autoPropIn
            "module Test\n[<AbstractClass>]\ntype Base() =\n    abstract Name: string with get, set\ntype Person() =\n    inherit Base()\n    let mutable name = \"\"\n    override this.Name\n        with get () = name\n        and set v = name <- v"
    )

    Assert.Empty(
        autoPropIn
            "module Test\ntype Base() =\n    let mutable name = \"\"\n    abstract Name: string with get, set\n    default this.Name\n        with get () = name\n        and set v = name <- v"
    )
