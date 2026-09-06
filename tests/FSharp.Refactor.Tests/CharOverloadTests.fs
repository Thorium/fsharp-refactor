module FSharp.Refactor.Tests.CharOverloadTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private charOverloadsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CharOverload.find tree sourceText checkResults

let private assertCharFix (source: string) (expectedReplacement: string) =
    match charOverloadsIn source with
    | [ s ] ->
        match s.ReplacementText with
        | Some replacement ->
            Assert.Equal(expectedReplacement, replacement)
            let patched = applyEdit source s.Range replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None ->
            failwith
                $"Expected a fix, got an advisory, calling assertCharFix with source: {source}, expectedReplacement: {expectedReplacement}"
    | other -> failwithf "Expected exactly one char-overload suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``Contains with a single-char string gets the char fix`` () =
    assertCharFix "let f (s: string) = s.Contains \"x\"" "'x'"

[<Fact>]
let ``StringBuilder Append gets the char fix`` () =
    assertCharFix "let f (sb: System.Text.StringBuilder) = sb.Append(\"x\")" "'x'"

[<Fact>]
let ``ordinal StartsWith collapses to the char overload`` () =
    assertCharFix "let f (s: string) = s.StartsWith(\"x\", System.StringComparison.Ordinal)" "('x')"

[<Fact>]
let ``quote character is escaped in the char literal`` () =
    assertCharFix "let f (s: string) = s.Contains \"'\"" "'\\''"

[<Fact>]
let ``bare EndsWith stays advisory because of culture semantics`` () =
    match charOverloadsIn "let f (s: string) = s.EndsWith \"x\"" with
    | [ s ] ->
        Assert.Equal(None, s.ReplacementText)
        Assert.Equal("EndsWith", s.MethodName)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``multi-character strings are left alone`` () =
    Assert.Empty(charOverloadsIn "let f (s: string) = s.Contains \"xy\"")

[<Fact>]
let ``list Contains is not the string method`` () =
    Assert.Empty(charOverloadsIn "let f (xs: System.Collections.Generic.List<string>) = xs.Contains \"x\"")

[<Fact>]
let ``a verbatim single-char string is the char overload too`` () =
    // @"\" is THE spelling of a backslash in path code — the FR0015 lesson.
    // Contains, because StartsWith(string) is culture-sensitive and only
    // ever gets the advisory tier
    assertCharFix "let f (s: string) = s.Contains @\"\\\"" "'\\\\'"

[<Fact>]
let ``Contains inside a query expression keeps the string overload`` () =
    // Contains(string) in a where clause is what SQL translators turn
    // into LIKE; the char overload is not a recognized pattern
    Assert.Empty(
        charOverloadsIn
            "open System.Linq\nlet f (xs: string list) =\n    query {\n        for x in xs.AsQueryable() do\n            where (x.Contains \"a\")\n            select x\n    }"
    )

[<Fact>]
let ``FR0038: a culture-sensitive call carries the ordinal char overload as an editor offer`` () =
    match charOverloadsIn "module Test\nlet f (s: string) = s.StartsWith \"@\"" with
    | [ s ] ->
        Assert.Equal(None, s.ReplacementText)

        match s.OrdinalOffer with
        | Some(_, original, replacement) ->
            Assert.Equal("\"@\"", original)
            Assert.Equal("'@'", replacement)
        | None -> failwith "Expected the ordinal offer"
    | other -> failwithf "Expected one char-overload note, got %A" other

[<Fact>]
let ``FR0038: Contains carries the portable IndexOf form for a narrow target`` () =
    // Contains(char) is netstandard2.1+, IndexOf(char) is everywhere and
    // both are ordinal — so the two forms agree
    match charOverloadsIn "let f (s: string) = s.Contains \"x\"" with
    | [ s ] ->
        match s.PortableOffer with
        | Some(r, _, replacement) ->
            Assert.Equal("s.IndexOf 'x' >= 0", replacement)
            let patched = applyEdit "let f (s: string) = s.Contains \"x\"" r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the portable offer"
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``FR0038: the culture-sensitive methods carry no portable form`` () =
    // StartsWith(string) is culture-sensitive and StartsWith(char) is not:
    // that change is the author's call, not a portability rewrite
    match charOverloadsIn "let f (s: string) = s.StartsWith \"x\"" with
    | [ s ] -> Assert.True(s.PortableOffer.IsNone)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``FR0038: a dotted receiver keeps its path in the portable form`` () =
    match charOverloadsIn "type T = { Name: string }\nlet f (t: T) = t.Name.Contains \"x\"" with
    | [ s ] ->
        match s.PortableOffer with
        | Some(_, _, replacement) -> Assert.Equal("t.Name.IndexOf 'x' >= 0", replacement)
        | None -> failwith "Expected the portable offer"
    | other -> failwithf "Expected exactly one suggestion, got %A" other
