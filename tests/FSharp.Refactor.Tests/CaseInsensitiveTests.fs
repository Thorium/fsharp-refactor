module FSharp.Refactor.Tests.CaseInsensitiveTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0039 CaseInsensitive ----

let private caseIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CaseInsensitive.find tree sourceText checkResults

[<Fact>]
let ``both-sides ToLower equality is noted`` () =
    match caseIn "let f (a: string) (b: string) = a.ToLower() = b.ToLower()" with
    | [ s ] ->
        Assert.Equal(CaseInsensitive.CaseKind.Equality, s.Kind)
        Assert.Equal("ToLower", s.LoweringName)
    | other -> failwithf "Expected exactly one equality note, got %A" other

[<Fact>]
let ``one-sided ToUpperInvariant against a literal is noted`` () =
    match caseIn "let f (a: string) = a.ToUpperInvariant() = \"ABC\"" with
    | [ s ] -> Assert.Equal("ToUpperInvariant", s.LoweringName)
    | other -> failwithf "Expected exactly one literal-comparison note, got %A" other

[<Fact>]
let ``StartsWith on a lowered copy is noted`` () =
    match caseIn "let f (s: string) = s.ToLower().StartsWith \"abc\"" with
    | [ s ] -> Assert.Equal(CaseInsensitive.CaseKind.MethodCall "StartsWith", s.Kind)
    | other -> failwithf "Expected exactly one method-call note, got %A" other

[<Fact>]
let ``inequality with ToLower is noted`` () =
    match caseIn "let f (a: string) (b: string) = a.ToLower() <> b" with
    | [ s ] -> Assert.Equal(CaseInsensitive.CaseKind.Equality, s.Kind)
    | other -> failwithf "Expected exactly one inequality note, got %A" other

[<Fact>]
let ``plain equality without lowering is fine`` () =
    Assert.Empty(caseIn "let f (a: string) (b: string) = a = b")

[<Fact>]
let ``ToLower used for its value is fine`` () =
    Assert.Empty(caseIn "let f (a: string) = a.ToLower()")

// ---- FR0040 RedundantGuard ----

let private guardsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RedundantGuard.find tree sourceText checkResults

let private assertGuardFix (source: string) (expectedReplacement: string) =
    match guardsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one guard suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``ContainsKey before Remove collapses`` () =
    assertGuardFix
        "open System.Collections.Generic\nlet f (d: Dictionary<int, string>) k = if d.ContainsKey k then d.Remove k |> ignore"
        "d.Remove k |> ignore"

[<Fact>]
let ``negated Contains before HashSet Add collapses`` () =
    assertGuardFix
        "open System.Collections.Generic\nlet f (s: HashSet<int>) x = if not (s.Contains x) then s.Add x |> ignore"
        "s.Add x |> ignore"

[<Fact>]
let ``Contains before HashSet Remove collapses`` () =
    assertGuardFix
        "open System.Collections.Generic\nlet f (s: HashSet<int>) x = if s.Contains x then s.Remove x |> ignore"
        "s.Remove x |> ignore"

[<Fact>]
let ``different keys are left alone`` () =
    Assert.Empty(
        guardsIn
            "open System.Collections.Generic\nlet f (d: Dictionary<int, string>) k j = if d.ContainsKey k then d.Remove j |> ignore"
    )

[<Fact>]
let ``an else branch is left alone`` () =
    Assert.Empty(
        guardsIn
            "open System.Collections.Generic\nlet f (d: Dictionary<int, string>) k = if d.ContainsKey k then d.Remove k |> ignore else printfn \"missing\""
    )

[<Fact>]
let ``a collection outside the whitelist is left alone`` () =
    Assert.Empty(
        guardsIn
            "open System.Collections.Generic\nlet f (xs: List<int>) x = if xs.Contains x then xs.Remove x |> ignore"
    )

[<Fact>]
let ``an ASCII literal comparison gets the OrdinalIgnoreCase fix`` () =
    let source =
        "module Test\nopen System\nlet f (role: string) = role.ToLowerInvariant() = \"user\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "String.Equals(role, \"user\", StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``inequality wraps the fix in not`` () =
    let source =
        "module Test\nopen System\nlet f (role: string) = role.ToUpperInvariant() <> \"USER\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "not (String.Equals(role, \"USER\", StringComparison.OrdinalIgnoreCase))", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a file without open System gets the qualified spelling`` () =
    let source =
        "module Test\nlet f (role: string) = role.ToLowerInvariant() = \"user\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(
            Some "System.String.Equals(role, \"user\", System.StringComparison.OrdinalIgnoreCase)",
            s.Replacement
        )

        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other


[<Fact>]
let ``a backticked receiver keeps its quoting in the rewrite`` () =
    // idText drops the backticks; the rebuilt call would not compile
    let source =
        "module Test\nopen System\nlet f (``the role``: string) = ``the role``.ToLowerInvariant() = \"user\""

    match caseIn source with
    | [ s ] ->
        match s.Replacement with
        | Some r ->
            Assert.Contains("``the role``", r)
            let patched = applyEdit source s.Range r
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> () // standing down is also acceptable
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a non-ASCII literal stays advice`` () =
    // outside ASCII the invariant mapping and ordinal folding genuinely
    // drift apart; the note asks for a deliberate choice
    match caseIn "module Test\nopen System\nlet f (s: string) = s.ToLowerInvariant() = \"straße\"" with
    | [ s ] -> Assert.Equal(None, s.Replacement)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``comparing two expressions stays advice`` () =
    match caseIn "module Test\nopen System\nlet f (a: string) (b: string) = a.ToLower() = b.ToLower()" with
    | suggestions -> Assert.True(suggestions |> List.forall (fun s -> s.Replacement |> Option.isNone))

[<Fact>]
let ``an invariant-lowered StartsWith against an ASCII literal gets the comparison-overload fix`` () =
    let source =
        "module Test\nopen System\nlet f (path: string) = path.ToLowerInvariant().StartsWith \"file:\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "path.StartsWith(\"file:\", StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a culture-lowered StartsWith gets the ordinal fix and the culture alternative`` () =
    // the plain `ToLower()` differs from OrdinalIgnoreCase on the Turkish
    // dotless i alone; the idiomatic ordinal spelling is the fix, with the
    // InvariantCulture spelling as the editor's alternative
    let source =
        "module Test\nopen System\nlet f (path: string) = path.ToLower().StartsWith \"file:\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(CaseInsensitive.CaseKind.MethodCall "StartsWith", s.Kind)
        Assert.Equal(Some "path.StartsWith(\"file:\", StringComparison.OrdinalIgnoreCase)", s.Replacement)

        Assert.Equal(
            Some "path.StartsWith(\"file:\", StringComparison.InvariantCultureIgnoreCase)",
            s.CultureReplacement
        )

        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a lowered call that names its StringComparison keeps that choice`` () =
    // the author chose the comparison; the fix drops the lowering and
    // spells the IgnoreCase counterpart of THAT choice, and offers no
    // alternative since the choice is made
    for comparison, expected in
        [
            "Ordinal", "OrdinalIgnoreCase"
            "CurrentCulture", "CurrentCultureIgnoreCase"
            "OrdinalIgnoreCase", "OrdinalIgnoreCase"
        ] do
        let source =
            $"module Test\nopen System\nlet f (path: string) = path.ToLower().StartsWith(\"file:\", StringComparison.{comparison})"

        match caseIn source with
        | [ s ] ->
            Assert.Equal(Some $"path.StartsWith(\"file:\", StringComparison.{expected})", s.Replacement)
            Assert.Equal(None, s.CultureReplacement)
            let patched = applyEdit source s.Range s.Replacement.Value
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected one suggestion for %s, got %A" comparison other

[<Fact>]
let ``a lowering and a named comparison of different families stay advice`` () =
    // an invariant lowering under a CurrentCulture comparison (or the
    // reverse) is two deliberate choices no single comparison keeps: under
    // tr-TR `"FILE:".ToLowerInvariant().StartsWith("file:", CurrentCulture)`
    // is true and `StartsWith("file:", CurrentCultureIgnoreCase)` is false
    for source in
        [
            "module Test\nopen System\nlet f (path: string) = path.ToLowerInvariant().StartsWith(\"file:\", StringComparison.CurrentCulture)"
            "module Test\nopen System\nlet f (path: string) = path.ToLower().StartsWith(\"file:\", StringComparison.InvariantCulture)"
        ] do
        match caseIn source with
        | [ s ] ->
            Assert.Equal(None, s.Replacement)
            Assert.Equal(None, s.CultureReplacement)
        | other -> failwithf "Expected one fix-less note for %s, got %A" source other

[<Fact>]
let ``the parenthesized argument spelling fixes the same way, qualified without open System`` () =
    let source =
        "module Test\nlet f (path: string) = path.ToUpperInvariant().EndsWith(\".CSV\")"

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "path.EndsWith(\".CSV\", System.StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a lowered Contains fixes where the StringComparison overload exists`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) = s.ToLowerInvariant().Contains \"error\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "s.Contains(\"error\", StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``an equality literal whose case fights the lowering stays advice`` () =
    // x.ToLower() = "ABC" is always false; OrdinalIgnoreCase would make
    // it start matching — same gate as the method-call shape
    match caseIn "module Test\nopen System\nlet f (x: string) = x.ToLower() = \"ABC\"" with
    | [ s ] -> Assert.Equal(None, s.Replacement)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a literal whose case fights the lowering stays advice`` () =
    // path.ToLower().StartsWith "FILE:" can never match; making it match
    // is a behavior change only a human should sign off on
    match caseIn "module Test\nopen System\nlet f (path: string) = path.ToLower().StartsWith \"FILE:\"" with
    | [ s ] -> Assert.Equal(None, s.Replacement)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a non-literal method argument stays advice`` () =
    match caseIn "module Test\nopen System\nlet f (path: string) (p: string) = path.ToLower().StartsWith p" with
    | [ s ] -> Assert.Equal(None, s.Replacement)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``an invariant-lowered IndexOf against an agreeing literal gets the fix`` () =
    let source =
        "module Test\nopen System\nlet f (email: string) = email.ToLowerInvariant().IndexOf \"@example.\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "email.IndexOf(\"@example.\", StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``the culture-aware alternative also typechecks`` () =
    let source =
        "module Test\nopen System\nlet f (role: string) = role.ToLowerInvariant() = \"user\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(
            Some "String.Equals(role, \"user\", StringComparison.InvariantCultureIgnoreCase)",
            s.CultureReplacement
        )

        let patched = applyEdit source s.Range s.CultureReplacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other
