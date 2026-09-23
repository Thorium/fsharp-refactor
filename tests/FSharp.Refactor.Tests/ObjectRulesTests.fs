module FSharp.Refactor.Tests.ObjectRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    ObjectRules.find tree sourceText

// ---- FR0019 Equals without GetHashCode ----

[<Fact>]
let ``Equals override without GetHashCode is flagged`` () =
    let equalsSuggestions, _, _ =
        findIn
            "module Test\ntype C(v: int) =\n    member _.V = v\n    override this.Equals(o) = match o with | :? C as c -> c.V = v | _ -> false"

    match equalsSuggestions with
    | [ s ] -> Assert.Equal("C", s.TypeName)
    | other -> failwithf "Expected exactly one Equals suggestion, got %A" other

[<Fact>]
let ``Equals with GetHashCode is fine`` () =
    let equalsSuggestions, _, _ =
        findIn
            "module Test\ntype C(v: int) =\n    member _.V = v\n    override this.Equals(o) = match o with | :? C as c -> c.V = v | _ -> false\n    override this.GetHashCode() = v"

    Assert.Empty equalsSuggestions

[<Fact>]
let ``non-override Equals member is not flagged`` () =
    let equalsSuggestions, _, _ =
        findIn "module Test\ntype C(v: int) =\n    member _.Equals(other: C) = other = Unchecked.defaultof<C>"

    Assert.Empty equalsSuggestions

// ---- FR0020 abstract call in constructor ----

[<Fact>]
let ``abstract member called during construction is flagged`` () =
    let _, ctorSuggestions, _ =
        findIn
            "module Test\n[<AbstractClass>]\ntype Base() as this =\n    let initial = this.Compute()\n    member _.Initial = initial\n    abstract Compute: unit -> int"

    match ctorSuggestions with
    | [ s ] -> Assert.Equal("Compute", s.MemberName)
    | other -> failwithf "Expected exactly one ctor-call suggestion, got %A" other

[<Fact>]
let ``abstract property read during construction is flagged`` () =
    let _, ctorSuggestions, _ =
        findIn
            "module Test\n[<AbstractClass>]\ntype Base() as this =\n    do printfn \"%d\" this.Size\n    abstract Size: int"

    match ctorSuggestions with
    | [ s ] -> Assert.Equal("Size", s.MemberName)
    | other -> failwithf "Expected exactly one ctor-property suggestion, got %A" other

[<Fact>]
let ``abstract member called from an ordinary member is fine`` () =
    let _, ctorSuggestions, _ =
        findIn
            "module Test\n[<AbstractClass>]\ntype Base() =\n    abstract Compute: unit -> int\n    member this.Run() = this.Compute()"

    Assert.Empty ctorSuggestions

[<Fact>]
let ``non-abstract self call during construction is fine`` () =
    let _, ctorSuggestions, _ =
        findIn
            "module Test\ntype C() as this =\n    let v = this.Fixed()\n    member _.Fixed() = 42\n    member _.V = v"

    Assert.Empty ctorSuggestions

// ---- FR0021 redundant ToString in interpolation ----

let private interpIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    InterpToString.find (Some check) tree sourceText

let private assertInterp (source: string) (expectedReplacement: string) =
    match interpIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one interpolation suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``simple ToString fill is dropped`` () =
    assertInterp "module Test\nlet f (x: int) = $\"{x.ToString()} items\"" "x"

[<Fact>]
let ``dotted receiver keeps its full path`` () =
    assertInterp "module Test\ntype R = { Count: int }\nlet f (r: R) = $\"total {r.Count.ToString()}\"" "r.Count"

[<Fact>]
let ``parenthesized receiver expression works`` () =
    assertInterp "module Test\nlet f (a: int) b = $\"{(a + b).ToString()}\"" "(a + b)"

[<Fact>]
let ``ToString with an argument is culture-sensitive and stays`` () =
    Assert.Empty(
        interpIn "module Test\nlet f (x: System.DateTime) (c: System.Globalization.CultureInfo) = $\"{x.ToString(c)}\""
    )

[<Fact>]
let ``ToString outside interpolation is not touched`` () =
    Assert.Empty(interpIn "module Test\nlet f (x: int) = x.ToString()")

[<Fact>]
let ``FR0021: a FormattableString or a format after the fill keeps the ToString`` () =
    // Invariant formats `{x}` with the invariant culture, `x.ToString()`
    // with the current one; `:N2` formats an int, but not a string
    let cases =
        [
            "module Test\nopen System\nlet f (x: float) = FormattableString.Invariant $\"{x.ToString()}\""
            "module Test\nopen System\nlet f (x: float) : FormattableString = $\"{x.ToString()}\""
            "module Test\nopen System\nlet f (x: float) =\n    let s: FormattableString = $\"{x.ToString()}\"\n    s"
            "module Test\nopen System\ntype R = { Msg: FormattableString }\nlet f (x: float) = { Msg = $\"{x.ToString()}\" }"
            "module Test\nlet f (x: int) = $\"{x.ToString():N2}\""
        ]

    for source in cases do
        Assert.Empty(interpIn source)

    // a string-typed hole in a lambda or a plain call still goes
    assertInterp "module Test\nlet f (xs: int list) = xs |> List.map (fun x -> $\"{x.ToString()}!\")" "x"
    assertInterp "module Test\nlet f (x: int) = printfn \"%s\" $\"{x.ToString()}!\"" "x"
