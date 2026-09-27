module FSharp.Refactor.Tests.AttributeMergeTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private mergesIn (source: string) =
    let tree, sourceText = parse source
    AttributeMerge.find AttributeMerge.DefaultMaxAttributes AttributeMerge.DefaultWrapColumn tree sourceText

let private assertMerge (source: string) (expectedPatched: string) =
    match mergesIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one merge suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``stacked attribute lines merge into one bracket`` () =
    assertMerge
        (fsharp
            """
            module Test
            [<System.Obsolete>]
            [<CompiledName("Run")>]
            let f () = 1
            """)
        (fsharp
            """
            module Test
            [<System.Obsolete; CompiledName("Run")>]
            let f () = 1
            """)

[<Fact>]
let ``same-line attribute brackets merge too`` () =
    assertMerge
        (fsharp
            """
            module Test
            [<System.Obsolete>] [<CompiledName("Run")>]
            let f () = 1
            """)
        (fsharp
            """
            module Test
            [<System.Obsolete; CompiledName("Run")>]
            let f () = 1
            """)

[<Fact>]
let ``type attributes merge`` () =
    assertMerge
        (fsharp
            """
            module Test
            [<Sealed>]
            [<AllowNullLiteral>]
            type C() =
                member _.X = 1
            """)
        (fsharp
            """
            module Test
            [<Sealed; AllowNullLiteral>]
            type C() =
                member _.X = 1
            """)

[<Fact>]
let ``a single attribute list is fine`` () =
    Assert.Empty(
        mergesIn (
            fsharp
                """
                module Test
                [<System.Obsolete; CompiledName("Run")>]
                let f () = 1
                """
        )
    )

[<Fact>]
let ``a comment between brackets suppresses the merge`` () =
    Assert.Empty(
        mergesIn (
            fsharp
                """
                module Test
                [<System.Obsolete>]
                // keep separate
                [<CompiledName("Run")>]
                let f () = 1
                """
        )
    )

[<Fact>]
let ``more than four attributes stay in their own brackets`` () =
    // one merged line stops being a list you scan and starts being one you
    // parse; past the cap the separate brackets read better
    let source =
        fsharp
            """
            module Test
            [<A>]
            [<B>]
            [<C>]
            [<D>]
            [<E>]
            let f () = 1
            """

    Assert.Empty(mergesIn source)

[<Fact>]
let ``four attributes still merge`` () =
    let source =
        fsharp
            """
            module Test
            [<A>]
            [<B>]
            [<C>]
            [<D>]
            let f () = 1
            """

    match mergesIn source with
    | [ s ] -> Assert.Equal("[<A; B; C; D>]", s.ReplacementText)
    | other -> failwithf "Expected one merge at the cap, got %A" other

[<Fact>]
let ``a merge that would overrun the wrap column is left alone`` () =
    // the count is fine, the width is not
    let long = String.replicate 40 "X"
    let source = $"module Test\n[<{long}1>]\n[<{long}2>]\n[<{long}3>]\nlet f () = 1"

    Assert.Empty(mergesIn source)

[<Fact>]
let ``a raised cap merges what the default refuses`` () =
    // { "FR0060": { "maxAttributes": 6 } } — house style, not correctness
    let source =
        fsharp
            """
            module Test
            [<A>]
            [<B>]
            [<C>]
            [<D>]
            [<E>]
            let f () = 1
            """

    let tree, sourceText = parse source

    Assert.Empty(
        AttributeMerge.find AttributeMerge.DefaultMaxAttributes AttributeMerge.DefaultWrapColumn tree sourceText
    )

    match AttributeMerge.find 6 AttributeMerge.DefaultWrapColumn tree sourceText with
    | [ s ] -> Assert.Equal("[<A; B; C; D; E>]", s.ReplacementText)
    | other -> failwithf "Expected the merge once the cap allows it, got %A" other
