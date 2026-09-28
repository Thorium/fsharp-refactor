[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.DuFieldNamesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open System.IO

let private fieldNamesIn (source: string) =
    let tree, sourceText = parse source
    DuFieldNames.find false tree sourceText

/// The same scan with API changes allowed, as `fsharp-refactor
/// --api-changes` runs it.
let private fieldNamesWithApiChangesIn (source: string) =
    let tree, sourceText = parse source
    DuFieldNames.find true tree sourceText

/// Apply a suggestion's edits bottom-up and verify the patched text.
let private assertFieldNames (source: string) (expectedPatched: string) =
    match fieldNamesIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one field-name suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``match-site names flow onto the private case definition`` () =
    assertFieldNames
        (fsharp
            """
            module Test
            type private Order =
                | Line of int * decimal
                | Total of decimal
            let private f (o: Order) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)
        (fsharp
            """
            module Test
            type private Order =
                | Line of qty: int * price: decimal
                | Total of decimal
            let private f (o: Order) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)

[<Fact>]
let ``representation-private union is also accepted`` () =
    assertFieldNames
        (fsharp
            """
            module Test
            type Order =
                private
                | Line of int * decimal
                | Total of decimal
            let f (o: Order) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)
        (fsharp
            """
            module Test
            type Order =
                private
                | Line of qty: int * price: decimal
                | Total of decimal
            let f (o: Order) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)

[<Fact>]
let ``wildcard sites do not block the harvest`` () =
    assertFieldNames
        (fsharp
            """
            module Test
            type private Pair =
                | Pair of int * int
                | Empty
            let private f p =
                match p with
                | Pair(first, second) -> first + second
                | Empty -> 0
            let private g p =
                match p with
                | Pair _ -> true
                | Empty -> false
            """)
        (fsharp
            """
            module Test
            type private Pair =
                | Pair of first: int * second: int
                | Empty
            let private f p =
                match p with
                | Pair(first, second) -> first + second
                | Empty -> 0
            let private g p =
                match p with
                | Pair _ -> true
                | Empty -> false
            """)

[<Fact>]
let ``type inside an internal module is accepted`` () =
    assertFieldNames
        (fsharp
            """
            module Test
            module internal Impl =
                type OrderLine =
                    | Line of int * decimal
                    | Total of decimal
                let f (o: OrderLine) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                    | Total t -> t
            """)
        (fsharp
            """
            module Test
            module internal Impl =
                type OrderLine =
                    | Line of qty: int * price: decimal
                    | Total of decimal
                let f (o: OrderLine) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                    | Total t -> t
            """)

[<Fact>]
let ``internal top-level module is accepted`` () =
    assertFieldNames
        (fsharp
            """
            module internal Test
            type OrderLine =
                | Line of int * decimal
                | Total of decimal
            let f (o: OrderLine) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)
        (fsharp
            """
            module internal Test
            type OrderLine =
                | Line of qty: int * price: decimal
                | Total of decimal
            let f (o: OrderLine) =
                match o with
                | Line(qty, price) -> decimal qty * price
                | Total t -> t
            """)

[<Fact>]
let ``public type is left alone`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type Order =
                    | Line of int * decimal
                let f (o: Order) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                """
        )
    )

[<Fact>]
let ``public type is offered under api changes`` () =
    Assert.NotEmpty(
        fieldNamesWithApiChangesIn (
            fsharp
                """
                module Test
                type Order =
                    | Line of int * decimal
                let f (o: Order) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                """
        )
    )

[<Fact>]
let ``disagreeing sites cancel the suggestion`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type private Order =
                    | Line of int * decimal
                let f (o: Order) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                let g (o: Order) =
                    match o with
                    | Line(n, total) -> decimal n * total
                """
        )
    )

[<Fact>]
let ``partially named site cancels the suggestion`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type private Order =
                    | Line of int * decimal
                let f (o: Order) =
                    match o with
                    | Line(qty, _) -> qty
                """
        )
    )

[<Fact>]
let ``already named fields are left alone`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type private Order =
                    | Line of qty: int * price: decimal
                let f (o: Order) =
                    match o with
                    | Line(qty, price) -> decimal qty * price
                """
        )
    )

[<Fact>]
let ``ambiguous case name across two unions is skipped`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type private A =
                    | Item of int * int
                type private B =
                    | Item of string * string
                let f (a: A) =
                    match a with
                    | Item(left, right) -> left + right
                """
        )
    )

[<Fact>]
let ``case without any destructuring site is left alone`` () =
    Assert.Empty(
        fieldNamesIn (
            fsharp
                """
                module Test
                type private Order =
                    | Line of int * decimal
                    | Total of decimal
                """
        )
    )

[<Fact>]
let ``FR0022 stands down where a signature declares the case`` () =
    // the .fsi declares `Box of int * int`; naming the fields in the .fs
    // alone gives "The names differ" and the project stops compiling
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-du-" + System.Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let source =
            fsharp
                """
                module internal M

                type Shape =
                    | Box of int * int

                let area s =
                    match s with
                    | Box(width, height) -> width * height

                """

        let impl = Path.Combine(dir, "M.fs")
        File.WriteAllText(impl, source)

        File.WriteAllText(
            Path.Combine(dir, "M.fsi"),
            fsharp
                """
                module internal M

                type Shape =
                    | Box of int * int

                val area: Shape -> int

                """
        )

        let tree, sourceText = parseNamed impl source
        Assert.Empty(DuFieldNames.find false tree sourceText)

        // the same source with no signature beside it still qualifies
        let lone = Path.Combine(dir, "N.fs")
        File.WriteAllText(lone, source)
        let loneTree, loneText = parseNamed lone source
        Assert.NotEmpty(DuFieldNames.find false loneTree loneText)
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``a reserved word from the case name is not a field name`` () =
    // `| ModAndKey of mod: int * key: int` does not parse: `mod` is an
    // F# keyword, and so are `inline`, `const`, `sig`, `downto`, ...
    for caseName in
        [
            "ModAndKey"
            "InlineAndKey"
            "ConstAndKey"
            "SigAndKey"
            "DowntoAndKey"
            "ParamsAndKey"
        ] do
        Assert.Empty(fieldNamesIn $"module Test\ntype private K =\n    | {caseName} of int * int\n    | Other of int")
