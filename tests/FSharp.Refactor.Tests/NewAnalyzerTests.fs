[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.NewAnalyzerTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open System.IO

// ---- FR0015 RegexUsage ----

let private regexIn (source: string) =
    let tree, sourceText = parse source
    RegexUsage.find tree sourceText

let private assertRegexFix (source: string) (expectedReplacement: string) =
    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.StringOperation, s.Kind)

        match s.Edits with
        | [ (range, _, replacement) ] ->
            Assert.Equal(expectedReplacement, replacement)
            let patched = applyEdit source range replacement
            Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
        | other -> failwithf "Expected exactly one edit, got %A" other
    | other -> failwithf "Expected exactly one regex suggestion, got %d: %A" (List.length other) other

/// Apply a hoist suggestion's edits bottom-up and verify the patched text.
let private assertRegexHoist (source: string) (expectedPatched: string) =
    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistFromLoop, s.Kind)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one hoist suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``anchored-start literal becomes StartsWith`` () =
    assertRegexFix
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"^abc\")"
        "s.StartsWith \"abc\""

[<Fact>]
let ``anchored-end literal becomes EndsWith`` () =
    assertRegexFix
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"abc$\")"
        "s.EndsWith \"abc\""

[<Fact>]
let ``unanchored literal becomes Contains`` () =
    assertRegexFix
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"abc\")"
        "s.Contains \"abc\""

[<Fact>]
let ``pattern with metacharacters is left alone`` () =
    Assert.Empty(
        regexIn "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"a.c\")"
    )

[<Fact>]
let ``escaped dollar is not an anchor`` () =
    Assert.Empty(
        regexIn "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"abc\\\\$\")"
    )

[<Fact>]
let ``fully anchored pattern is left alone`` () =
    Assert.Empty(
        regexIn "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"^abc$\")"
    )

[<Fact>]
let ``regex call in a loop is hoisted above the declaration`` () =
    assertRegexHoist
        "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for s in xs do\n        if Regex.IsMatch(s, \"a.c\") then printfn \"%s\" s"
        "module Test\nopen System.Text.RegularExpressions\nlet private acRegex = Regex \"a.c\"\nlet f (xs: string list) =\n    for s in xs do\n        if acRegex.IsMatch s then printfn \"%s\" s"

[<Fact>]
let ``hoist without the open stays advice-only`` () =
    let source =
        "module Test\nlet f (xs: string list) =\n    for s in xs do\n        if System.Text.RegularExpressions.Regex.IsMatch(s, \"a.c\") then printfn \"%s\" s"

    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistFromLoop, s.Kind)
        Assert.Empty s.Edits
    | other -> failwithf "Expected exactly one advice-only hoist, got %A" other

[<Fact>]
let ``regex Replace in a loop is hoisted with both remaining arguments`` () =
    assertRegexHoist
        "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for s in xs do\n        printfn \"%s\" (Regex.Replace(s, \"a.c\", \"-\"))"
        "module Test\nopen System.Text.RegularExpressions\nlet private acRegex = Regex \"a.c\"\nlet f (xs: string list) =\n    for s in xs do\n        printfn \"%s\" (acRegex.Replace(s, \"-\"))"

[<Fact>]
let ``literal match in a loop reports only the string operation`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for s in xs do\n        if Regex.IsMatch(s, \"abc\") then printfn \"%s\" s"

    match regexIn source with
    | [ s ] -> Assert.Equal(RegexUsage.RegexSuggestionKind.StringOperation, s.Kind)
    | other -> failwithf "Expected exactly one string-op suggestion, got %A" other

[<Fact>]
let ``instance regex call outside a loop is not flagged`` () =
    Assert.Empty(
        regexIn
            "module Test\nopen System.Text.RegularExpressions\nlet r = Regex \"a.c\"\nlet f (s: string) = r.IsMatch s"
    )

// ---- FR0016 StructDu ----

let private structDuIn (source: string) =
    let tree, sourceText = parse source
    StructDu.find false tree sourceText

/// The same scan with API changes allowed, as `fsharp-refactor
/// --api-changes` runs it.
let private structDuWithApiChangesIn (source: string) =
    let tree, sourceText = parse source
    StructDu.find true tree sourceText

let private assertPatchedStructDu (suggestions: StructDu.Suggestion list) (source: string) (expectedPatched: string) =
    match suggestions with
    | [ s ] ->
        let patched = applyEdit source s.InsertRange s.InsertText
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one struct-DU suggestion, got %d: %A" (List.length other) other

let private assertStructDu (source: string) (expectedPatched: string) =
    assertPatchedStructDu (structDuIn source) source expectedPatched

[<Fact>]
let ``small named-field union gains the attribute`` () =
    assertStructDu
        "module Test\ntype private Shape =\n    | Circle of radius: float\n    | Square of side: float"
        "module Test\n[<Struct>]\ntype private Shape =\n    | Circle of radius: float\n    | Square of side: float"

[<Fact>]
let ``single fielded case may be unnamed`` () =
    assertStructDu
        "module Test\ntype private Id =\n    | Id of int\n    | Missing"
        "module Test\n[<Struct>]\ntype private Id =\n    | Id of int\n    | Missing"

[<Fact>]
let ``a public union is left alone`` () =
    // struct-vs-class is a semantic change consumers outside the assembly
    // see without any compiler error
    Assert.Empty(structDuIn "module Test\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float")

[<Fact>]
let ``a union in an internal module is contained`` () =
    assertStructDu
        "module internal Test\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float"
        "module internal Test\n[<Struct>]\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float"

[<Fact>]
let ``a public union is offered under api changes`` () =
    let source =
        "module Test\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float"

    assertPatchedStructDu
        (structDuWithApiChangesIn source)
        source
        "module Test\n[<Struct>]\ntype Shape =\n    | Circle of radius: float\n    | Square of side: float"

[<Fact>]
let ``a private representation does not make a public union contained`` () =
    // the cases are hidden but the type itself is still public
    Assert.Empty(
        structDuIn "module Test\ntype Shape =\n    private\n    | Circle of radius: float\n    | Square of side: float"
    )

[<Fact>]
let ``string fields are not small value types`` () =
    Assert.Empty(structDuIn "module Test\ntype private T =\n    | A of string\n    | B of int")

[<Fact>]
let ``recursive union is excluded by the whitelist`` () =
    Assert.Empty(structDuIn "module Test\ntype private Tree =\n    | Leaf of int\n    | Node of Tree")

[<Fact>]
let ``two cases with unnamed fields are excluded`` () =
    // compiled ItemN names would collide in a struct union
    Assert.Empty(structDuIn "module Test\ntype private T =\n    | A of int\n    | B of float")

[<Fact>]
let ``existing attributes are left alone`` () =
    Assert.Empty(structDuIn "module Test\n[<Struct>]\ntype private T =\n    | A of a: int\n    | B of b: float")

[<Fact>]
let ``all-nullary union is not suggested`` () =
    Assert.Empty(structDuIn "module Test\ntype private T =\n    | A\n    | B")

// ---- FR0017 AsyncIgnore ----

let private discardedAsyncIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AsyncIgnore.find tree sourceText checkResults

[<Fact>]
let ``piped async into ignore is flagged`` () =
    let suggestions = discardedAsyncIn "let f (comp: Async<int>) = comp |> ignore"

    match suggestions with
    | [ s ] -> Assert.Equal("comp", s.Name)
    | other -> failwithf "Expected exactly one async-ignore suggestion, got %A" other

[<Fact>]
let ``direct ignore application is flagged`` () =
    let suggestions = discardedAsyncIn "let f (comp: Async<int>) = ignore comp"

    match suggestions with
    | [ s ] -> Assert.Equal("comp", s.Name)
    | other -> failwithf "Expected exactly one direct-ignore suggestion, got %A" other

[<Fact>]
let ``ignoring a non-async value is fine`` () =
    Assert.Empty(discardedAsyncIn "let f (n: int) = n |> ignore")

[<Fact>]
let ``Async.Ignore usage is not flagged`` () =
    Assert.Empty(discardedAsyncIn "let f (comp: Async<int>) = async { do! comp |> Async.Ignore }")

// --- verbatim patterns. `@"..."` is how F# writes regexes, and the rule
// --- used to look only at plain string literals, quietly missing most of them.

[<Fact>]
let ``a verbatim literal pattern simplifies like a plain one`` () =
    assertRegexFix
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, @\"^abc\")"
        "s.StartsWith \"abc\""

[<Fact>]
let ``a verbatim pattern hoists out of a loop keeping its own spelling`` () =
    // the binding must re-emit the source text: re-quoting the decoded value
    // would turn `@"\d+"` into the invalid `"\d+"`
    match
        regexIn
            "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for x in xs do\n        if Regex.IsMatch(x, @\"\d+\") then ()"
    with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistFromLoop, s.Kind)

        let inserted =
            s.Edits
            |> List.map (fun (_, _, replacement) -> replacement)
            |> String.concat "\n"

        Assert.Contains("@\"\d+\"", inserted)
    | other -> failwithf "Expected exactly one verbatim hoist suggestion, got %A" other

[<Fact>]
let ``a triple-quoted pattern is seen too`` () =
    assertRegexFix
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"\"\"^abc\"\"\")"
        "s.StartsWith \"abc\""

[<Fact>]
let ``an ignored async call result is flagged`` () =
    // the real fire-and-forget bug is a direct call ignored, not a named
    // binding: `saveAsync user |> ignore`
    let suggestions =
        discardedAsyncIn "let save (n: int) : Async<unit> = async { return () }\nlet f () = save 1 |> ignore"

    match suggestions with
    | [ s ] -> Assert.Equal("save", s.Name)
    | other -> failwithf "Expected exactly one ignored-call suggestion, got %A" other

[<Fact>]
let ``direct ignore of a call result is flagged`` () =
    let suggestions =
        discardedAsyncIn "let save (n: int) : Async<unit> = async { return () }\nlet f () = ignore (save 1)"

    match suggestions with
    | [ s ] -> Assert.Equal("save", s.Name)
    | other -> failwithf "Expected exactly one direct-ignore-call suggestion, got %A" other

[<Fact>]
let ``a partially applied async function is a different mistake`` () =
    // `save2 1` is a FUNCTION, not an Async — this rule stays quiet
    Assert.Empty(
        discardedAsyncIn "let save2 (a: int) (b: int) : Async<unit> = async { return () }\nlet f () = save2 1 |> ignore"
    )

[<Fact>]
let ``a piped construction of the async is flagged too`` () =
    let suggestions =
        discardedAsyncIn
            "let makeAsync (n: int) : Async<unit> = async { return () }\nlet f () = 1 |> makeAsync |> ignore"

    match suggestions with
    | [ s ] -> Assert.Equal("makeAsync", s.Name)
    | other -> failwithf "Expected exactly one piped suggestion, got %A" other

[<Fact>]
let ``a shape-changing fix beside a signature file fires only on private declarations`` () =
    // a .fsi declares every internal declaration too, and must agree on the
    // compiled shape: `[<Struct>]` on the implementation alone is a
    // representation mismatch. Only private escapes the signature. The gate
    // is Visibility.isInScope, shared by FR0011, FR0016 and FR0134
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-sig-" + System.Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let du name =
            $"module internal M\n\ntype {name} Shape =\n    | Box of side: int\n    | Ball of radius: int\n"

        File.WriteAllText(
            Path.Combine(dir, "M.fsi"),
            "module internal M\n\ntype Shape =\n    | Box of side: int\n    | Ball of radius: int\n"
        )

        let impl = Path.Combine(dir, "M.fs")

        // without the cross-file parser (an editor) the signature is
        // unreadable, and the internal fix is withheld; with it, the
        // signature is edited in step instead (SignatureCoEditTests)
        ProjectSources.configure None
        let internalTree, internalText = parseNamed impl (du "internal")
        Assert.Empty(StructDu.find true internalTree internalText)

        let privateTree, privateText = parseNamed impl (du "private")
        Assert.NotEmpty(StructDu.find false privateTree privateText)

        // no signature beside it: internal is in scope as before
        let lone = Path.Combine(dir, "N.fs")
        let loneTree, loneText = parseNamed lone (du "internal")
        Assert.NotEmpty(StructDu.find false loneTree loneText)
    finally
        Directory.Delete(dir, true)

// ---- FR0017: ValueTask discarded, interface members ----

[<Fact>]
let ``FR0017: an interface member returning Async discarded with ignore is flagged`` () =
    // FSharp.CloudAgent's `messageStream.AbandonMessage token |> ignore`
    let source =
        "module Test\ntype IStream =\n    abstract AbandonMessage: System.Guid -> Async<unit>\nlet f (stream: IStream) (token: System.Guid) =\n    stream.AbandonMessage token |> ignore"

    match discardedAsyncIn source with
    | [ s ] ->
        Assert.Equal("AbandonMessage", s.Name)
        Assert.False s.IsValueTask
    | other -> failwithf "Expected one discarded Async, got %A" other

[<Fact>]
let ``FR0017: a ValueTask discarded with ignore loses its outcome`` () =
    let source =
        "module Test\nopen System.Threading.Tasks\ntype ITransport =\n    abstract shutdown: unit -> ValueTask\nlet f (t: ITransport) =\n    t.shutdown() |> ignore"

    match discardedAsyncIn source with
    | [ s ] ->
        Assert.Equal("shutdown", s.Name)
        Assert.True s.IsValueTask
    | other -> failwithf "Expected one discarded ValueTask, got %A" other

    match discardedAsyncIn "module Test\nopen System.Threading.Tasks\nlet f (vt: ValueTask<int>) = ignore vt" with
    | [ s ] -> Assert.True s.IsValueTask
    | other -> failwithf "Expected one discarded ValueTask value, got %A" other

    // a Task is hot and observable through its own machinery: not this rule
    Assert.Empty(discardedAsyncIn "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) = t |> ignore")

    // a unit-returning shutdown is nothing to discard
    Assert.Empty(
        discardedAsyncIn
            "module Test\ntype ITransport =\n    abstract shutdown: unit -> unit\nlet f (t: ITransport) = t.shutdown() |> ignore"
    )

[<Fact>]
let ``a regex hoisted from under an #if lands under the same #if`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n#if !FOO\n    for x in xs do\n        if Regex.IsMatch(x, \"^a+$\") then printfn \"%s\" x\n#endif"

    match
        regexIn source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistFromLoop)
    with
    | [ s ] ->
        let inserted =
            s.Edits
            |> List.pick (fun (_, original, text) -> if original = "" then Some text else None)

        Assert.StartsWith("#if !FOO\nlet private ", inserted)
        Assert.Contains("\n#endif\n", inserted)
    | other -> failwithf "Expected one hoist suggestion, got %A" other

// ---- FR0149 UnhandledStart ----

let private unhandledStartsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AsyncIgnore.findUnhandledStart tree sourceText checkResults

[<Fact>]
let ``FR0149: a started computation with no handler is flagged`` () =
    // CloudAgent's listener: one throw from the loop body ends it silently
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    async {\n        while true do\n            let! _ = work ()\n            ()\n    }\n    |> Async.Start"
    with
    | [ s ] -> Assert.Equal("Async.Start", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a body wrapped in try-with is handled`` () =
    Assert.Empty(
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    async {\n        try\n            let! _ = work ()\n            ()\n        with ex -> printfn \"%s\" ex.Message\n    }\n    |> Async.Start"
    )

[<Fact>]
let ``FR0149: Async Catch counts only once both Choice arms consume it`` () =
    // producing the Choice is not handling it
    let source (tail: string) =
        "let work () = async { return 1 }\nlet run () =\n    async {\n        let! outcome = work () |> Async.Catch\n"
        + tail
        + "\n    }\n    |> Async.Start"

    Assert.Empty(
        unhandledStartsIn (
            source
                "        match outcome with\n        | Choice1Of2 _ -> ()\n        | Choice2Of2 ex -> printfn \"%s\" ex.Message"
        )
    )

    Assert.NotEmpty(unhandledStartsIn (source "        ignore outcome"))

[<Fact>]
let ``FR0149: a one-hop binding in the same file is read`` () =
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    let listener =\n        async {\n            let! _ = work ()\n            ()\n        }\n\n    Async.Start listener"
    with
    | [ s ] -> Assert.Equal("Async.Start", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a computation this file cannot see stays quiet`` () =
    Assert.Empty(unhandledStartsIn "let run (comp: Async<unit>) = Async.Start comp")

[<Fact>]
let ``FR0149: StartImmediate is the same shape and the token form is read`` () =
    match
        unhandledStartsIn
            "open System.Threading\nlet work () = async { return 1 }\nlet run (token: CancellationToken) =\n    Async.StartImmediate(\n        async {\n            let! _ = work ()\n            ()\n        },\n        token\n    )"
    with
    | [ s ] -> Assert.Equal("Async.StartImmediate", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a looping body says where the handler goes`` () =
    // CloudAgent's listener polls forever: a handler around the whole
    // computation still ends it on the first failure
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    async {\n        while true do\n            let! _ = work ()\n            ()\n    }\n    |> Async.Start"
    with
    | [ s ] -> Assert.True(s.LoopsInBody)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a straight-line body has no such choice`` () =
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    async {\n        let! _ = work ()\n        ()\n    }\n    |> Async.Start"
    with
    | [ s ] -> Assert.False(s.LoopsInBody)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try around the start is called out as not covering it`` () =
    // measured in fsi: `try async { failwith "y" } |> Async.Start with _ -> ()`
    // terminates the process — the handler is on this thread, the work is not
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with ex -> printfn \"%s\" ex.Message"
    with
    | [ s ] -> Assert.True(s.WrappedInTry)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a start with no try around it says nothing about one`` () =
    match
        unhandledStartsIn
            "let work () = async { return 1 }\nlet run () =\n    async {\n        let! _ = work ()\n        ()\n    }\n    |> Async.Start"
    with
    | [ s ] -> Assert.False(s.WrappedInTry)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try wrapping only the start moves its handler inside`` () =
    let source =
        "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement

            Assert.Contains(
                "    async {\n        try\n            let! _ = work ()\n            ()\n        with e ->\n            printfn \"%s\" e.Message\n    }\n    |> Async.Start",
                patched
            )

            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: several handler clauses travel verbatim`` () =
    // the Async.Catch spelling could not carry a typed clause or a guard;
    // moving the try keeps every clause as written
    let source =
        "open System\nlet work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with\n    | :? OperationCanceledException -> ()\n    | e when e.Message = \"x\" -> printfn \"x\"\n    | e -> printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement
            Assert.Contains(":? OperationCanceledException", patched)
            Assert.Contains("e when e.Message = \"x\"", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try holding more than the start offers no move`` () =
    // the handler may have been meant for the other statement, so the
    // rule will not decide that for the author
    let source =
        "let work () = async { return 1 }\nlet setup () = ()\nlet run () =\n    try\n        setup ()\n\n        async {\n            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] ->
        Assert.True(s.WrappedInTry)
        Assert.True(s.TryFix.IsNone, "a try holding other statements is not the author's handler for this start alone")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a start carrying a cancellation token keeps its argument`` () =
    // the tupled form would lose the token in the rewrite, so no fix
    let source =
        "open System.Threading\nlet work () = async { return 1 }\nlet run (token: CancellationToken) =\n    try\n        Async.Start(\n            async {\n                let! _ = work ()\n                ()\n            },\n            token\n        )\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] -> Assert.True(s.TryFix.IsNone)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other
