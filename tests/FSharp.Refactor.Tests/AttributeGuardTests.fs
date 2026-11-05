/// Rules that rewrite a declaration leave it alone for an attribute they don't know, and read past those that say
/// nothing of what the rewrite changes.
module FSharp.Refactor.Tests.AttributeGuardTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private applied (edits: (FSharp.Compiler.Text.range * string) list) (source: string) =
    edits
    |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun text (r, replacement) -> applyEdit text r replacement) source

let private smallRecord (attribute: string) =
    fsharp
        $"""
        module Test
        [<{attribute}>]
        type private P = {{ X: int; Y: int }}
        """

let private structFixOf (source: string) =
    let tree, sourceText = parse source
    let _, structs, _ = StructHints.find false tree sourceText
    (List.exactlyOne structs).Fix

[<Fact>]
let ``FR0070 offers the fix past an attribute that says nothing of storage`` () =
    let source = smallRecord "RequireQualifiedAccess"

    match structFixOf source with
    | Some(r, text) ->
        let patched = applyEdit source r text
        Assert.Contains("[<Struct>]", patched)
        assertTypechecks "Patched source" patched
    | None -> failwith "no fix"

[<Fact>]
let ``FR0070 stays advice on any other attribute`` () =
    Assert.True((structFixOf (smallRecord "CLIMutable")).IsNone)

let private commentDocIn (source: string) =
    let tree, sourceText = parse source
    CommentDoc.find tree sourceText

[<Fact>]
let ``FR0132 puts the doc above the attributes`` () =
    for source, expected in
        [
            fsharp
                """
                module Test
                [<System.Obsolete "old">]
                type Widget() = class end // Makes widgets
                """,
            fsharp
                """
                module Test
                /// Makes widgets
                [<System.Obsolete "old">]
                type Widget() = class end
                """
            fsharp
                """
                module Test
                [<System.Obsolete "old">]
                let widgets = 3 // How many there are
                """,
            fsharp
                """
                module Test
                /// How many there are
                [<System.Obsolete "old">]
                let widgets = 3
                """
        ] do
        let s = List.exactlyOne (commentDocIn source)
        let patched = applied [ for r, _, text in s.Edits -> r, text ] source
        Assert.Equal(expected, patched)
        assertTypechecks "Patched source" patched

[<Fact>]
let ``FR0130 reads past an attribute that says nothing of the value`` () =
    let source =
        fsharp
            """
            module Test
            [<System.Obsolete "old">]
            let private limit = 10
            let private twice = limit * 2
            """

    let tree, sourceText = parse source
    let s = List.exactlyOne (LiteralConst.findWith (fun _ -> false) true tree sourceText |> List.filter (fun s -> s.Name = "limit"))
    let r, text = s.Fix
    assertTypechecks "Patched source" (applyEdit source r text)

[<Fact>]
let ``FR0130 leaves any other attribute alone`` () =
    let source =
        fsharp
            """
            module Test
            [<System.CLSCompliant false>]
            let private limit = 10
            """

    let tree, sourceText = parse source
    Assert.Empty(LiteralConst.findWith (fun _ -> false) true tree sourceText)

let private tailCallOn (attribute: string) =
    fsharp
        $"""
        module Test
        [<{attribute}>]
        let rec count (n: int) (acc: int) = if n = 0 then acc else count (n - 1) (acc + 1)
        """

[<Fact>]
let ``FR0131 reads past an attribute that says nothing of the function`` () =
    let tree, sourceText, check = parseAndCheck (tailCallOn "System.Obsolete \"old\"")
    Assert.Single(RecTailCall.find tree sourceText check) |> ignore

[<Fact>]
let ``FR0131 leaves an existing TailCall alone`` () =
    let tree, sourceText, check = parseAndCheck (tailCallOn "TailCall")
    Assert.Empty(RecTailCall.find tree sourceText check)

let private patternOn (attribute: string) =
    fsharp
        $"""
        module Test
        [<{attribute}>]
        let private (|Even|_|) (n: int) = if n %% 2 = 0 then Some n else None
        let f x =
            match x with
            | Even v -> v
            | _ -> 0
        """

[<Fact>]
let ``FR0011 reads past an attribute that says nothing of the pattern`` () =
    let tree, sourceText, check = parseAndCheck (patternOn "System.Obsolete \"old\"")
    Assert.Single(StructActivePattern.find false tree sourceText check) |> ignore

[<Fact>]
let ``FR0011 leaves any other attribute alone`` () =
    let tree, sourceText, check = parseAndCheck (patternOn "System.CLSCompliant false")
    Assert.Empty(StructActivePattern.find false tree sourceText check)

let private staticsOn (attribute: string) =
    let source =
        fsharp
            $"""
            module Test
            type RunAttribute() =
                inherit System.Attribute()
            type C() =
                [<{attribute}>]
                member this.Twice(x: int) = x * 2
            """

    let tree, sourceText, check = parseAndCheck source
    let _, statics, _ = ObjectDesign.find true tree sourceText check
    statics |> List.map _.MemberName

[<Fact>]
let ``FR0033 reads past an attribute no framework dispatches on`` () =
    Assert.NotEmpty(staticsOn "System.Obsolete \"old\"")

[<Fact>]
let ``FR0033 leaves a member a framework may dispatch on`` () =
    Assert.Empty(staticsOn "Run")
