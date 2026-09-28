/// A3 (FR0147 shortening to a shadowed name), A4 (FR0073 collapsing a binder
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
    // `System.Version(1, 0, 0, 0)` under `open System` shortened to
    // `Version(...)` binds to something else ("This value is not a
    // function and cannot be applied")
    let source =
        fsharp
            """
            module Test
            open System
            let a () =
                let Version = 3
                let v = System.Version(1, 0, 0, 0)
                Version + v.Major
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        Assert.Equal(2, s.Uses)
        let patched = applyAll source s.Edits
        Assert.Contains("let v = System.Version(1, 0, 0, 0)", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        Assert.Contains("let c () = Version(3, 0, 0, 0)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a parameter of the same name keeps the prefix inside its function`` () =
    let source =
        fsharp
            """
            module Test
            open System
            let a (Version: int) = System.Version(1, 0, 0, 0).Major + Version
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("let a (Version: int) = System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a class-level let of the name keeps the prefix throughout the type`` () =
    let source =
        fsharp
            """
            module Test
            open System
            type C() =
                let Version = 3
                member _.V() = System.Version(1, 0, 0, 0).Major + Version
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("member _.V() = System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0147: a nullary union case brought by another open declines the shortening`` () =
    // Expecto's [<AutoOpen>] Tests module nests CLIArguments, whose bare
    // `Version` case is what `Version(1, 0, 0, 0)` would bind to
    let lib =
        fsharp
            """
            namespace Lib
            [<AutoOpen>]
            module Tests =
                type CLIArguments =
                    | Sequenced
                    | Version
            """

    let user =
        fsharp
            """
            module Test
            open System
            open Lib
            let a () = System.Version(1, 0, 0, 0)
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    Assert.Empty(systemEdits (QualifiedNames.find 3 2 tree sourceText checkResults))

[<Fact>]
let ``FR0147: the same union under RequireQualifiedAccess cannot capture the name, so the shortening goes in`` () =
    let lib =
        fsharp
            """
            namespace Lib
            [<AutoOpen>]
            module Tests =
                [<RequireQualifiedAccess>]
                type CLIArguments =
                    | Sequenced
                    | Version
            """

    let user =
        fsharp
            """
            module Test
            open System
            open Lib
            let a () = System.Version(1, 0, 0, 0)
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    let edits = systemEdits (QualifiedNames.find 3 2 tree sourceText checkResults)
    Assert.Equal(3, edits.Length)
    Assert.Contains("let a () = Version(1, 0, 0, 0)", applyAll user edits)

[<Fact>]
let ``FR0147: a bare union case the file itself declares declines the shortening`` () =
    let source =
        fsharp
            """
            module Test
            open System
            type Cmd =
                | Run
                | Version
            let a () = System.Version(1, 0, 0, 0)
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    Assert.Empty(systemEdits (qualifiedIn source))

[<Fact>]
let ``FR0147: without any shadow the open-and-shorten still goes in`` () =
    let source =
        fsharp
            """
            module Test
            let a () = System.Version(1, 0, 0, 0)
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System", s.Namespace)
        let patched = applyAll source s.Edits

        Assert.Contains(
            fsharp
                """
                open System
                let a () = Version(1, 0, 0, 0)
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one System finding, got %A" other

// ---- A4: FR0073 MatchBang ----

let private matchBangsIn (source: string) =
    let tree, sourceText = parse source
    MatchBangRule.find tree sourceText

[<Fact>]
let ``FR0073: a binder mentioned in an anonymous-record field of an arm stays`` () =
    // two arms serialise `{| message = format resolution |}`, and the
    // walker must descend into those fields to see the binder
    let source =
        fsharp
            """
            module Test
            type Res = Gone of string | Faulted of string
            let resolve () = task { return Gone "x" }
            let format (r: Res) = ""
            let getStatus () =
              task {
                let! resolution = resolve ()
                match resolution with
                | Gone msg ->
                  let! n = task { return 1 }
                  return
                    System.Text.Json.JsonSerializer.Serialize(
                      {| state = "NoSession"
                         message = format resolution
                         available = n |})
                | Faulted sid ->
                  return
                    System.Text.Json.JsonSerializer.Serialize(
                      {| state = "Faulted"
                         message = format resolution |})
              }
            """

    Assert.Empty(matchBangsIn source)

[<Fact>]
let ``FR0073: the same shape without the field mention still collapses`` () =
    let source =
        fsharp
            """
            module Test
            type Res = Gone of string | Faulted of string
            let resolve () = task { return Gone "x" }
            let getStatus () =
              task {
                let! resolution = resolve ()
                match resolution with
                | Gone msg -> return {| state = "NoSession"; message = msg |}
                | Faulted sid -> return {| state = "Faulted"; message = sid |}
              }
            """

    match matchBangsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("    match! resolve () with", patched)
        Assert.DoesNotContain("let! resolution", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one match! note, got %A" other

[<Fact>]
let ``the index sees an anonymous record's copy source and field values`` () =
    let tree, _ =
        parse (
            fsharp
                """
                module Test
                let f (r: {| X: int |}) (v: int) = {| r with X = v |}
                """
        )

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
    // `%%s{{version}}` already typed; the other two holes must not get
    // `%s{` spliced between their braces
    let source =
        lines
            [
                "let f (name: string) (ns: string) (v: string) ="
                "    $$\"\"\""
                "// generated by `{{name}}` -- v%%s{{v}}."
                "namespace {{ns}}"
                "    \"\"\""
            ]

    match holesIn source with
    | [ a; b ] ->
        Assert.Equal("%%s", a.Specifier)
        Assert.Equal("%%s", b.Specifier)
        let patched = applyAll source [ for s in [ a; b ] -> s.Range, "", s.Specifier ]
        Assert.Contains("generated by `%%s{{name}}` -- v%%s{{v}}.", patched)
        Assert.Contains("namespace %%s{{ns}}", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected two hole suggestions, got %A" other

[<Fact>]
let ``FR0043: a single percent in a double-dollar string is text, not a typed hole`` () =
    // no typed hole → not on the printf path → nothing to add
    let source =
        lines
            [
                "let f (name: string) (v: string) ="
                "    $$\"\"\"100%s of {{name}} and {{v}}\"\"\""
            ]

    Assert.Empty(holesIn source)

[<Fact>]
let ``FR0043: a single-dollar string still gains its single-percent specifier`` () =
    let source = "let f (name: string) (v: string) = $\"a %s{v} b {name}\""

    match holesIn source with
    | [ s ] ->
        Assert.Equal("%s", s.Specifier)
        let patched = applyEdit source s.Range s.Specifier
        Assert.Equal("let f (name: string) (v: string) = $\"a %s{v} b %s{name}\"", patched)
        assertTypechecks "Patched source" patched
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one wildcard note, got %A" other

[<Fact>]
let ``FR0072: a None on a RequireQualifiedAccess union in scope leaves Option's case bare`` () =
    // a qualified-access union's None must not make every Option match
    // spell `Option.None`
    assertExpanded
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Direction =
                | Decrease
                | Increase
                | None
            let f (o: int option) =
                match o with
                | Some v -> v
                | _ -> 0
            """)
        "None"

[<Fact>]
let ``FR0072: the same union without the attribute still qualifies the case`` () =
    assertExpanded
        (fsharp
            """
            type Direction =
                | Decrease
                | Increase
                | None
            let f (o: int option) =
                match o with
                | Some v -> v
                | _ -> 0
            """)
        "Option.None"

[<Fact>]
let ``FR0072: a payload case named on a RequireQualifiedAccess union stays bare too`` () =
    // LinkedResource.Unmanaged _ beside a qualified-access Channel.Unmanaged
    assertExpanded
        (fsharp
            """
            type LinkedResource =
                | Managed of int
                | Unmanaged of int
            [<RequireQualifiedAccess>]
            type Channel =
                | NodeImage
                | Unmanaged
            let f (r: LinkedResource) =
                match r with
                | Managed x -> x
                | _ -> 0
            """)
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one sprintf suggestion, got %A" other

[<Fact>]
let ``FR0042: the parentheses around a curried function's sprintf argument go with it`` () =
    // `(sprintf "Should have thrown for %d" days)` must not become
    // `($"Should have thrown for %d{days}")`
    assertSprintfPatched
        (fsharp
            """
            module Test
            module Expect =
                let throws (f: unit -> unit) (msg: string) = ()
            let check (days: int) =
                Expect.throws (fun _ -> ()) (sprintf "Should have thrown for %d" days)
            """)
        "Expect.throws (fun _ -> ()) $\"Should have thrown for %d{days}\""

[<Fact>]
let ``FR0042: a prefix operator touching the parentheses gets a space`` () =
    // `~~(sprintf "..." x)`: bare, `~~$"..."` lexes `~~$` as
    // one (invalid) operator name
    assertSprintfPatched
        (fsharp
            """
            module Test
            let build (x: string) =
                let sb = System.Text.StringBuilder()
                let (~~) (t: string) = sb.Append t |> ignore
                ~~(sprintf "INSERT %s;" x)
                sb.ToString()
            """)
        "~~ $\"INSERT %s{x};\""

[<Fact>]
let ``FR0042: a quoted format keeps its escapes and loses the parentheses`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            let setHttpHeader (k: string) (v: string) = ()
            let unauthorized (scheme: string) (realm: string) =
                setHttpHeader "WWW-Authenticate" (sprintf "%s realm=\"%s\"" scheme realm)
            """)
        "setHttpHeader \"WWW-Authenticate\" $\"%s{scheme} realm=\\\"%s{realm}\\\"\""

[<Fact>]
let ``FR0042: a binding's parenthesised value stands bare`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            let f (days: int) =
                let s = (sprintf "d %d" days)
                s
            """)
        "let s = $\"d %d{days}\""

[<Fact>]
let ``FR0042: a method's argument list keeps its parentheses`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            type C() =
                member _.M(s: string) = s.Length
            let f (c: C) (days: int) = c.M (sprintf "b %d" days)
            """)
        """c.M ($"b %d{days}")"""

[<Fact>]
let ``FR0042: a call with no space keeps its parentheses`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            type C() =
                member _.M(s: string) = s.Length
            let f (c: C) (days: int) = c.M(sprintf "c %d" days)
            """)
        """c.M($"c %d{days}")"""

[<Fact>]
let ``FR0042: a constructor's argument keeps its parentheses`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            let f (days: int) = System.Exception (sprintf "x %d" days)
            """)
        """System.Exception ($"x %d{days}")"""

[<Fact>]
let ``FR0042: a receiver keeps its parentheses`` () =
    assertSprintfPatched
        (fsharp
            """
            module Test
            let f (days: int) = (sprintf "e %d" days).Length
            """)
        """($"e %d{days}").Length"""

[<Fact>]
let ``FR0042: a bare sprintf application is replaced as before`` () =
    assertSprintfPatched "module Test\nlet f (x: string) = sprintf \"asdf %s\" x" "let f (x: string) = $\"asdf %s{x}\""

[<Fact>]
let ``FR0043: a literal percent before a typed double-dollar hole is not a second specifier`` () =
    // `%%%s{{x}}` under `$$` is one literal `%` and then a `%%s` specifier;
    // reading the raw text as "untyped" would splice a second `%%s` in
    let source =
        lines
            [
                "let f (x: string) (y: string) ="
                "    $$\"\"\"rate %%%s{{x}} of {{y}}\"\"\""
            ]

    match holesIn source with
    | [ s ] ->
        Assert.Equal("%%s", s.Specifier)
        let patched = applyAll source [ s.Range, "", s.Specifier ]
        Assert.Contains("rate %%%s{{x}} of %%s{{y}}", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one hole suggestion, got %A" other

[<Fact>]
let ``FR0147: a primary-constructor parameter of the same name keeps the prefix inside its type`` () =
    // `type C(Version: int)` binds `Version` for the whole type without a
    // binding node; the member's `System.Version(...)` must keep its prefix
    let source =
        fsharp
            """
            module Test
            open System
            type C(Version: int) =
                member _.V() = System.Version(1, 0, 0, 0).Major + Version
            let b () = System.Version(2, 0, 0, 0)
            let c () = System.Version(3, 0, 0, 0)
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        Assert.Equal(2, s.Uses)
        let patched = applyAll source s.Edits
        Assert.Contains("System.Version(1, 0, 0, 0).Major + Version", patched)
        Assert.Contains("let b () = Version(2, 0, 0, 0)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one System finding, got %A" other

[<Fact>]
let ``FR0072: an arm indented deeper than its match keeps the cases on one line`` () =
    // `| _ -> return false }` four columns deeper than the match, past 100
    // columns with both cases; a case on a fresh line under that `|` reads
    // as no or-pattern at all
    let source =
        fsharp
            """
            type CollectState<'T> =
                | NotStarted of 'T
                | HaveInputEnumerator of System.Collections.Generic.IEnumerator<'T>
                | HaveTheVeryLongNamedIntermediateState of int
                | Finished
            let f (state: CollectState<int>) (x: int) =
                async {
                                          match state with
                                          | CollectState.NotStarted inp -> return inp > 0
                                          | CollectState.HaveInputEnumerator e1 ->
                                              if x > 1 then
                                                  return true
                                              else
                                                  return e1.MoveNext ()
                                              | _ -> return false }
            """

    match wildcardsIn source with
    | [ s ] ->
        Assert.DoesNotContain("\n", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one wildcard note, got %A" other

// ---- FR0147: a shortened head shadowed by a value or union case ----

[<Fact>]
let ``FR0147: a prefix whose remaining head is a union case in scope stays`` () =
    // under `open FParsec`, `FParsec.Error.NoErrorMessages` shortened to
    // `Error.NoErrorMessages` fails, since bare `Error` is
    // `ReplyStatus.Error` - an expression resolves its first name among
    // the values and cases before any module
    let lib =
        fsharp
            """
            namespace Lib
            [<AutoOpen>]
            module Reply =
                type ReplyStatus =
                    | Ok
                    | Error
            module Error =
                let NoErrorMessages = 0
            """

    let user =
        fsharp
            """
            module Test
            open Lib
            let a = Lib.Error.NoErrorMessages
            let b = Lib.Error.NoErrorMessages
            let c = Lib.Error.NoErrorMessages
            let status = Error
            """

    let tree, sourceText, checkResults = parseAndCheckSecond lib user

    for s in QualifiedNames.find 3 2 tree sourceText checkResults do
        Assert.Empty s.Edits

[<Fact>]
let ``FR0147: the same prefix shortens when nothing of the head's name is in scope`` () =
    let lib =
        fsharp
            """
            namespace Lib
            module Messages =
                let NoErrorMessages = 0
            """

    let user =
        fsharp
            """
            module Test
            open Lib
            let a = Lib.Messages.NoErrorMessages
            let b = Lib.Messages.NoErrorMessages
            let c = Lib.Messages.NoErrorMessages
            """

    let tree, sourceText, checkResults = parseAndCheckSecond lib user

    match QualifiedNames.find 3 2 tree sourceText checkResults with
    | [ s ] -> Assert.Contains("let a = Messages.NoErrorMessages", applyAll user s.Edits)
    | other -> failwithf "Expected one suggestion, got %A" other
