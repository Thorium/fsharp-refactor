module FSharp.Refactor.Tests.RecordFieldsTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0145 RecordFields ----

// FR0145 fixes FS0764 itself, so its inputs carry that error on purpose
let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheckAllowingErrors source
    RecordFields.find tree sourceText checkResults

[<Literal>]
let private config =
    "module Test\ntype Config = { Name: string; Retries: int; Tags: string list; Timeout: int option; Owners: Set<string> }\n"

[<Fact>]
let ``obvious empties are added inline and the result typechecks`` () =
    let source = config + """let c = { Name = "x"; Retries = 3 }"""

    match findIn source with
    | [ s ] ->
        Assert.Equal("; Tags = []; Timeout = None; Owners = Set.empty", s.InsertText)
        Assert.True s.AllObvious
        Assert.Equal<string list>([ "Tags"; "Timeout"; "Owners" ], s.Missing)
        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a multi-line record gets one field per line at the label column`` () =
    let source =
        config
        + fsharp
            """
            let c =
                { Name = "x"
                  Retries = 3 }
            """

    match findIn source with
    | [ s ] ->
        Assert.Equal(
            fsharp
                """

                      Tags = []
                      Timeout = None
                      Owners = Set.empty
                """,
            s.InsertText
        )

        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a field with no obvious default gets a placeholder, and a zero alternative`` () =
    let source =
        config
        + """let c = { Name = "x"; Tags = []; Timeout = None; Owners = Set.empty }"""

    match findIn source with
    | [ s ] ->
        Assert.False s.AllObvious
        Assert.Equal("""; Retries = raise (System.NotImplementedException "Retries")""", s.InsertText)
        Assert.Equal("; Retries = 0", s.ZeroInsertText)
        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Placeholder form" patched
        let zeroed = applyEdit source s.Range s.ZeroInsertText
        assertTypechecks "Zero form" zeroed
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a reference-typed field zeroes to Unchecked.defaultof`` () =
    let source =
        fsharp
            """
            module Test
            type Inner = { V: int }
            type Outer = { Label: string; Inner: Inner }
            let o = { Label = "x" }
            """

    match findIn source with
    | [ s ] -> Assert.Equal("; Inner = Unchecked.defaultof<_>", s.ZeroInsertText)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a copy-and-update and a complete record are left alone`` () =
    Assert.Empty(
        findIn (
            config
            + fsharp
                """
                let a = { Name = "x"; Retries = 3; Tags = []; Timeout = None; Owners = Set.empty }
                let b = { a with Retries = 4 }
                """
        )
    )

[<Fact>]
let ``a Guid field zeroes to Guid.Empty`` () =
    let source =
        fsharp
            """
            module Test
            type Row = { Label: string; Id: System.Guid }
            let r = { Label = "x" }
            """

    match findIn source with
    | [ s ] ->
        Assert.Equal("; Id = System.Guid.Empty", s.ZeroInsertText)
        let zeroed = applyEdit source s.Range s.ZeroInsertText
        assertTypechecks "Zero form" zeroed
    | other -> failwithf "Expected one suggestion, got %A" other
