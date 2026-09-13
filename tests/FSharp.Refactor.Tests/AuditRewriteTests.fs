/// Real-repo sweep findings of 0.8.11 (round 2 of the code audit): A3
/// (FR0147 shortening to a shadowed name), A4 (FR0073 collapsing a binder
/// still used in an arm), A8 (FR0043 inside `$$"""…"""`), and the cosmetic
/// FR0072 `Option.None` spelling and FR0042 leftover parentheses.
module FSharp.Refactor.Tests.AuditRewriteTests

open Xunit
open FSharp.Compiler.Syntax
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

let private lines (xs: string list) = String.concat "\n" xs

// ---- A3: FR0147 QualifiedNames ----

let private qualifiedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    QualifiedNames.find 3 2 tree sourceText checkResults

let private systemEdits (suggestions: QualifiedNames.Suggestion list) =
    suggestions
    |> List.filter (fun s -> s.Namespace = "System")
    |> List.collect (fun s -> s.Edits)

[<Fact>]
let ``FR0147: a use inside a same-named local let keeps its prefix while the others shorten`` () =
    // SageFs's HotReloadTests: `System.Version(1, 0, 0, 0)` under `open
    // System` shortened to `Version(...)`, which bound to something else
    // ("This value is not a function and cannot be applied")
    let source =
        lines
            [ "module Test"
              "open System"
              "let a () ="
              "    let Version = 3"
              "    let v = System.Version(1, 0, 0, 0)"
              "    Version + v.Major"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        Assert.Equal(2, s.Uses)
        let patched = applyAll source s.Edits
        Assert.Contains("let v = System.Version(1, 0, 0, 0)", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        Assert.Contains("let c () = Version(3, 0, 0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a parameter of the same name keeps the prefix inside its function`` () =
    let source =
        lines
            [ "module Test"
              "open System"
              "let a (Version: int) = System.Version(1, 0, 0, 0).Major + Version"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("let a (Version: int) = System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a class-level let of the name keeps the prefix throughout the type`` () =
    let source =
        lines
            [ "module Test"
              "open System"
              "type C() ="
              "    let Version = 3"
              "    member _.V() = System.Version(1, 0, 0, 0).Major + Version"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("member _.V() = System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a nullary union case brought by another open declines the shortening`` () =
    // Expecto's [<AutoOpen>] Tests module nests CLIArguments, whose bare
    // `Version` case is what `Version(1, 0, 0, 0)` would bind to
    let lib =
        lines
            [ "namespace Lib"
              "[<AutoOpen>]"
              "module Tests ="
              "    type CLIArguments ="
              "        | Sequenced"
              "        | Version" ]

    let user =
        lines
            [ "module Test"
              "open System"
              "open Lib"
              "let a () = System.Version(1, 0, 0, 0)"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    Assert.Empty(systemEdits (QualifiedNames.find 3 2 tree sourceText checkResults))

[<Fact>]
let ``FR0147: the same union under RequireQualifiedAccess cannot capture the name, so the shortening goes in`` () =
    let lib =
        lines
            [ "namespace Lib"
              "[<AutoOpen>]"
              "module Tests ="
              "    [<RequireQualifiedAccess>]"
              "    type CLIArguments ="
              "        | Sequenced"
              "        | Version" ]

    let user =
        lines
            [ "module Test"
              "open System"
              "open Lib"
              "let a () = System.Version(1, 0, 0, 0)"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    let edits = systemEdits (QualifiedNames.find 3 2 tree sourceText checkResults)
    Assert.Equal(3, edits.Length)
    Assert.Contains("let a () = Version(1, 0, 0, 0)", applyAll user edits)

[<Fact>]
let ``FR0147: a bare union case the file itself declares declines the shortening`` () =
    let source =
        lines
            [ "module Test"
              "open System"
              "type Cmd ="
              "    | Run"
              "    | Version"
              "let a () = System.Version(1, 0, 0, 0)"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    Assert.Empty(systemEdits (qualifiedIn source))

[<Fact>]
let ``FR0147: without any shadow the open-and-shorten still goes in`` () =
    let source =
        lines
            [ "module Test"
              "let a () = System.Version(1, 0, 0, 0)"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System", s.Namespace)
        let patched = applyAll source s.Edits
        Assert.Contains("open System\nlet a () = Version(1, 0, 0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one System finding, got %A" other

// ---- A4: FR0073 MatchBang ----

let private matchBangsIn (source: string) =
    let tree, sourceText = parse source
    MatchBangRule.find tree sourceText

[<Fact>]
let ``FR0073: a binder mentioned in an anonymous-record field of an arm stays`` () =
    // SageFs's Mcp.fs getStatus: two arms serialise `{| message = format
    // resolution |}`, and the walker never descends into those fields
    let source =
        lines
            [ "module Test"
              "type Res = Gone of string | Faulted of string"
              "let resolve () = task { return Gone \"x\" }"
              "let format (r: Res) = \"\""
              "let getStatus () ="
              "  task {"
              "    let! resolution = resolve ()"
              "    match resolution with"
              "    | Gone msg ->"
              "      let! n = task { return 1 }"
              "      return"
              "        System.Text.Json.JsonSerializer.Serialize("
              "          {| state = \"NoSession\""
              "             message = format resolution"
              "             available = n |})"
              "    | Faulted sid ->"
              "      return"
              "        System.Text.Json.JsonSerializer.Serialize("
              "          {| state = \"Faulted\""
              "             message = format resolution |})"
              "  }" ]

    Assert.Empty(matchBangsIn source)

[<Fact>]
let ``FR0073: the same shape without the field mention still collapses`` () =
    let source =
        lines
            [ "module Test"
              "type Res = Gone of string | Faulted of string"
              "let resolve () = task { return Gone \"x\" }"
              "let getStatus () ="
              "  task {"
              "    let! resolution = resolve ()"
              "    match resolution with"
              "    | Gone msg -> return {| state = \"NoSession\"; message = msg |}"
              "    | Faulted sid -> return {| state = \"Faulted\"; message = sid |}"
              "  }" ]

    match matchBangsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("    match! resolve () with", patched)
        Assert.DoesNotContain("let! resolution", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one match! note, got %A" other

[<Fact>]
let ``the index sees an anonymous record's copy source and field values`` () =
    let tree, _ =
        parse "module Test\nlet f (r: {| X: int |}) (v: int) = {| r with X = v |}"

    let idents =
        (AstIndex.ofTree tree).Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.Ident id -> Some id.idText
            | _ -> None)
        |> Array.sort

    Assert.Equal<string[]>([| "r"; "v" |], idents)

// ---- A8: FR0043 TypedHoles under $$ ----

let private holesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TypedHoles.find tree sourceText checkResults

[<Fact>]
let ``FR0043: holes of a double-dollar string gain a double-percent specifier before both braces`` () =
    // SqlHydra's SchemaTemplate.fs: `%%s{{version}}` already typed, the
    // other two holes got `%s{` spliced between their braces
    let source =
        lines
            [ "let f (name: string) (ns: string) (v: string) ="
              "    $$\"\"\""
              "// generated by `{{name}}` -- v%%s{{v}}."
              "namespace {{ns}}"
              "    \"\"\"" ]

    match holesIn source with
    | [ a; b ] ->
        Assert.Equal("%%s", a.Specifier)
        Assert.Equal("%%s", b.Specifier)
        let patched = applyAll source [ for s in [ a; b ] -> s.Range, "", s.Specifier ]
        Assert.Contains("generated by `%%s{{name}}` -- v%%s{{v}}.", patched)
        Assert.Contains("namespace %%s{{ns}}", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two hole suggestions, got %A" other

[<Fact>]
let ``FR0043: a single percent in a double-dollar string is text, not a typed hole`` () =
    // no typed hole → not on the printf path → nothing to add
    let source =
        lines
            [ "let f (name: string) (v: string) ="
              "    $$\"\"\"100%s of {{name}} and {{v}}\"\"\"" ]

    Assert.Empty(holesIn source)

[<Fact>]
let ``FR0043: a single-dollar string still gains its single-percent specifier`` () =
    let source = "let f (name: string) (v: string) = $\"a %s{v} b {name}\""

    match holesIn source with
    | [ s ] ->
        Assert.Equal("%s", s.Specifier)
        let patched = applyEdit source s.Range s.Specifier
        Assert.Equal("let f (name: string) (v: string) = $\"a %s{v} b %s{name}\"", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one hole suggestion, got %A" other

[<Fact>]
let ``FR0086: a hole-free double-dollar string loses both dollars`` () =
    let source = "module Test\nlet s = $$\"\"\"plain text\"\"\"\nlet t = $\"plain\""
    let tree, sourceText = parse source

    let replacements =
        RedundantSyntax.find None tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
        |> List.map (fun s -> s.ReplacementText)
        |> List.sort

    Assert.Equal<string list>([ "\"\"\"plain text\"\"\""; "\"plain\"" ], replacements)

// ---- FR0072 ExpandWildcard: RequireQualifiedAccess unions do not clash ----

let private wildcardsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ExpandWildcard.find tree sourceText checkResults

let private assertExpanded (source: string) (expectedReplacement: string) =
    match wildcardsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one wildcard note, got %A" other

[<Fact>]
let ``FR0072: a None on a RequireQualifiedAccess union in scope leaves Option's case bare`` () =
    // farmer's ScaleActionDirection.None had every Option match spelled
    // `Option.None`
    assertExpanded
        (lines
            [ "[<RequireQualifiedAccess>]"
              "type Direction ="
              "    | Decrease"
              "    | Increase"
              "    | None"
              "let f (o: int option) ="
              "    match o with"
              "    | Some v -> v"
              "    | _ -> 0" ])
        "None"

[<Fact>]
let ``FR0072: the same union without the attribute still qualifies the case`` () =
    assertExpanded
        (lines
            [ "type Direction ="
              "    | Decrease"
              "    | Increase"
              "    | None"
              "let f (o: int option) ="
              "    match o with"
              "    | Some v -> v"
              "    | _ -> 0" ])
        "Option.None"

[<Fact>]
let ``FR0072: a payload case named on a RequireQualifiedAccess union stays bare too`` () =
    // farmer's LinkedResource.Unmanaged _ beside NodeOSUpgradeChannel.Unmanaged
    assertExpanded
        (lines
            [ "type LinkedResource ="
              "    | Managed of int"
              "    | Unmanaged of int"
              "[<RequireQualifiedAccess>]"
              "type Channel ="
              "    | NodeImage"
              "    | Unmanaged"
              "let f (r: LinkedResource) ="
              "    match r with"
              "    | Managed x -> x"
              "    | _ -> 0" ])
        "Unmanaged _"

// ---- FR0042 SprintfInterpolation: parentheses that only wrapped the call ----

let private sprintfIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SprintfInterpolation.find tree sourceText checkResults

let private assertSprintfPatched (source: string) (expectedFragment: string) =
    match sprintfIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Contains(expectedFragment, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one sprintf suggestion, got %A" other

[<Fact>]
let ``FR0042: the parentheses around a curried function's sprintf argument go with it`` () =
    // farmer's Tests: `(sprintf "Should have thrown for %d" days)` became
    // `($"Should have thrown for %d{days}")`
    assertSprintfPatched
        (lines
            [ "module Test"
              "module Expect ="
              "    let throws (f: unit -> unit) (msg: string) = ()"
              "let check (days: int) ="
              "    Expect.throws (fun _ -> ()) (sprintf \"Should have thrown for %d\" days)" ])
        "Expect.throws (fun _ -> ()) $\"Should have thrown for %d{days}\""

[<Fact>]
let ``FR0042: a quoted format keeps its escapes and loses the parentheses`` () =
    // Giraffe's HttpStatusCodeHandlers.fs
    assertSprintfPatched
        (lines
            [ "module Test"
              "let setHttpHeader (k: string) (v: string) = ()"
              "let unauthorized (scheme: string) (realm: string) ="
              "    setHttpHeader \"WWW-Authenticate\" (sprintf \"%s realm=\\\"%s\\\"\" scheme realm)" ])
        "setHttpHeader \"WWW-Authenticate\" $\"%s{scheme} realm=\\\"%s{realm}\\\"\""

[<Fact>]
let ``FR0042: a binding's parenthesised value stands bare`` () =
    assertSprintfPatched
        "module Test\nlet f (days: int) =\n    let s = (sprintf \"d %d\" days)\n    s"
        "let s = $\"d %d{days}\""

[<Fact>]
let ``FR0042: a method's argument list keeps its parentheses`` () =
    assertSprintfPatched
        "module Test\ntype C() =\n    member _.M(s: string) = s.Length\nlet f (c: C) (days: int) = c.M (sprintf \"b %d\" days)"
        "c.M ($\"b %d{days}\")"

[<Fact>]
let ``FR0042: a call with no space keeps its parentheses`` () =
    assertSprintfPatched
        "module Test\ntype C() =\n    member _.M(s: string) = s.Length\nlet f (c: C) (days: int) = c.M(sprintf \"c %d\" days)"
        "c.M($\"c %d{days}\")"

[<Fact>]
let ``FR0042: a constructor's argument keeps its parentheses`` () =
    assertSprintfPatched
        "module Test\nlet f (days: int) = System.Exception (sprintf \"x %d\" days)"
        "System.Exception ($\"x %d{days}\")"

[<Fact>]
let ``FR0042: a receiver keeps its parentheses`` () =
    assertSprintfPatched "module Test\nlet f (days: int) = (sprintf \"e %d\" days).Length" "($\"e %d{days}\").Length"

[<Fact>]
let ``FR0042: a bare sprintf application is replaced as before`` () =
    assertSprintfPatched "module Test\nlet f (x: string) = sprintf \"asdf %s\" x" "let f (x: string) = $\"asdf %s{x}\""

[<Fact>]
let ``FR0043: a literal percent before a typed double-dollar hole is not a second specifier`` () =
    // `%%%s{{x}}` under `$$` is one literal `%` and then a `%%s` specifier;
    // reading the raw text as "untyped" spliced a second `%%s` in
    let source =
        lines
            [ "let f (x: string) (y: string) ="
              "    $$\"\"\"rate %%%s{{x}} of {{y}}\"\"\"" ]

    match holesIn source with
    | [ s ] ->
        Assert.Equal("%%s", s.Specifier)
        let patched = applyAll source [ s.Range, "", s.Specifier ]
        Assert.Contains("rate %%%s{{x}} of %%s{{y}}", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one hole suggestion, got %A" other

[<Fact>]
let ``FR0147: a primary-constructor parameter of the same name keeps the prefix inside its type`` () =
    // `type C(Version: int)` binds `Version` for the whole type without a
    // binding node; the member's `System.Version(...)` must keep its prefix
    let source =
        lines
            [ "module Test"
              "open System"
              "type C(Version: int) ="
              "    member _.V() = System.Version(1, 0, 0, 0).Major + Version"
              "let b () = System.Version(2, 0, 0, 0)"
              "let c () = System.Version(3, 0, 0, 0)" ]

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        Assert.Equal(2, s.Uses)
        let patched = applyAll source s.Edits
        Assert.Contains("System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one System finding, got %A" other
