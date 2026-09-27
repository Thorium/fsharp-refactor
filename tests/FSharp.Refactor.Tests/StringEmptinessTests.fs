module FSharp.Refactor.Tests.StringEmptinessTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    StringEmptiness.find tree sourceText

/// Expect one suggestion; verify the patched source typechecks. Without
/// `open System` the FSharp.Core String MODULE shadows the type, so the
/// replacement must carry the System. prefix.
let private assertPatched (source: string) (expectedReplacement: string) (guarded: bool) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        Assert.Equal(guarded, s.Guarded)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``isNull-or-empty becomes IsNullOrEmpty`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if isNull x || x = "" then 0 else 1
            """)
        "System.String.IsNullOrEmpty x"
        true

[<Fact>]
let ``the equals-null spelling is recognized too`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x = null || x = "" then 0 else 1
            """)
        "System.String.IsNullOrEmpty x"
        true

[<Fact>]
let ``reversed operand order still matches`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if "" = x || isNull x then 0 else 1
            """)
        "System.String.IsNullOrEmpty x"
        true

[<Fact>]
let ``the negated conjunction becomes not IsNullOrEmpty`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if not (isNull x) && x <> "" then 0 else 1
            """)
        "not (System.String.IsNullOrEmpty x)"
        true

[<Fact>]
let ``inequality with null spells the same conjunction`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x <> null && x <> "" then 0 else 1
            """)
        "not (System.String.IsNullOrEmpty x)"
        true

[<Fact>]
let ``a guarded Trim test becomes IsNullOrWhiteSpace`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if isNull x || x.Trim() = "" then 0 else 1
            """)
        "System.String.IsNullOrWhiteSpace x"
        true

[<Fact>]
let ``a bare Trim test is the editor-only whitespace rewrite`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x.Trim() = "" then 0 else 1
            """)
        "System.String.IsNullOrWhiteSpace x"
        false

[<Fact>]
let ``Trim Length zero is the same test`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x.Trim().Length = 0 then 0 else 1
            """)
        "System.String.IsNullOrWhiteSpace x"
        false

[<Fact>]
let ``IsNullOrEmpty over a trimmed copy stops trimming`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if String.IsNullOrEmpty (x.Trim()) then 0 else 1
            """)
        "System.String.IsNullOrWhiteSpace x"
        false

[<Fact>]
let ``a dotted subject carries its path`` () =
    assertPatched
        (fsharp
            """
            module Test
            type R = { Name: string }
            let f (r: R) = if isNull r.Name || r.Name = "" then 0 else 1
            """)
        "System.String.IsNullOrEmpty r.Name"
        true

[<Fact>]
let ``a Trim test LEADING the null check is editor-only — null throws before the guard`` () =
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x.Trim() = "" || isNull x then 0 else 1
            """)
        "System.String.IsNullOrWhiteSpace x"
        false

[<Fact>]
let ``a plain empty test leading the null check is still exact`` () =
    // `null = ""` is false, no dereference — order does not matter here
    assertPatched
        (fsharp
            """
            module Test
            let f (x: string) = if x = "" || isNull x then 0 else 1
            """)
        "System.String.IsNullOrEmpty x"
        true

[<Fact>]
let ``inside query the rule stands down entirely`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (q: Linq.QuerySource<string, System.Linq.IQueryable>) = query { for x in q do where (isNull x || x = "") }
            """
    )

[<Fact>]
let ``a backticked subject cannot be respelled and is left alone`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (``the value``: string) = if isNull ``the value`` || ``the value`` = "" then 0 else 1
            """
    )

[<Fact>]
let ``a file with open System gets the short spelling`` () =
    assertPatched
        (fsharp
            """
            module Test
            open System
            let f (x: string) = if isNull x || x = "" then 0 else 1
            """)
        "String.IsNullOrEmpty x"
        true

[<Fact>]
let ``different subjects on the two sides never match`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (x: string) (y: string) = if isNull x || y = "" then 0 else 1
            """
    )

[<Fact>]
let ``a plain empty comparison alone is idiomatic and stays`` () =
    assertNoSuggestion "module Test\nlet f (x: string) = if x = \"\" then 0 else 1"

[<Fact>]
let ``Trim with explicit characters tests a different set`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (x: string) = if x.Trim('_') = "" then 0 else 1
            """
    )

[<Fact>]
let ``a method-call subject is not a pure read`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let f (g: unit -> string) = if isNull (g ()) || g () = "" then 0 else 1
            """
    )
