/// Semantic audit, round B: eight rules whose fix compiled but changed
/// what the program did. FR0118 handing the token to a cleanup call,
/// FR0075 `use` under a task still in flight in a collection, FR0012's
/// map fusion reordering effects and its name gate skipped without a
/// typed check, FR0015's culture-sensitive StartsWith and newline-tolerant
/// `$`, FR0039 rewriting the culture lowering, FR0142 dropping the value a
/// test returns, FR0002 moving a tail call into a lambda. Each gets its
/// repro (no suggestion, or the corrected text) and, where cheap, the
/// positive shape beside it.
module FSharp.Refactor.Tests.AuditSemanticBTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private lines (xs: string list) = String.concat "\n" xs

let private assertTypechecks (source: string) =
    Assert.True(typechecksCleanly source, $"Fixture does not typecheck:\n%s{source}")

// ---- 1: FR0118 CancellationOverload ----

let private cancellationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CancellationOverload.find tree sourceText checkResults

let private txScaffold =
    lines
        [
            "module Test"
            "open System.Threading"
            "open System.Threading.Tasks"
            "type Tx() ="
            "    member _.CommitAsync(ct: CancellationToken) : Task = Task.CompletedTask"
            "    member _.RollbackAsync() : Task = Task.CompletedTask"
            "    member _.RollbackAsync(ct: CancellationToken) : Task = Task.CompletedTask"
        ]

[<Fact>]
let ``FR0118: a cleanup call in a with handler or a finally never receives the token`` () =
    // `tx.RollbackAsync(ct)` after a cancelled `CommitAsync ct` throws
    // OperationCanceledException instead of rolling back
    let handler =
        lines
            [
                txScaffold
                "let commit (tx: Tx) (ct: CancellationToken) = task {"
                "    try"
                "        do! tx.CommitAsync(ct)"
                "    with _ ->"
                "        do! tx.RollbackAsync()"
                "}"
            ]

    assertTypechecks handler
    Assert.Empty(cancellationIn handler)

    let finallyBlock =
        lines
            [
                txScaffold
                "let commit (tx: Tx) (ct: CancellationToken) = task {"
                "    try"
                "        do! tx.CommitAsync(ct)"
                "    finally"
                "        tx.RollbackAsync() |> ignore"
                "}"
            ]

    assertTypechecks finallyBlock
    Assert.Empty(cancellationIn finallyBlock)

    // an explicit None in the handler is the author cutting the chain on
    // purpose — the propagation half of the rule stands down there too
    let explicitNone =
        lines
            [
                txScaffold
                "let commit (tx: Tx) (ct: CancellationToken) = task {"
                "    try"
                "        do! tx.CommitAsync(ct)"
                "    with _ ->"
                "        do! tx.RollbackAsync(CancellationToken.None)"
                "}"
            ]

    assertTypechecks explicitNone
    Assert.Empty(cancellationIn explicitNone)

[<Fact>]
let ``FR0118: the same call in the try body still gets the token`` () =
    let source =
        lines
            [
                txScaffold
                "let commit (tx: Tx) (ct: CancellationToken) = task {"
                "    try"
                "        do! tx.RollbackAsync()"
                "    with _ ->"
                "        ()"
                "}"
            ]

    match cancellationIn source with
    | [ s ] ->
        Assert.Equal(CancellationOverload.TokenGap.Omitted, s.Kind)
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("do! tx.RollbackAsync(ct)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one token suggestion, got %A" other

// ---- 2: FR0075 UseBinding ----

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

[<Fact>]
let ``FR0075: a task from the binder handed to a collection refuses the fix`` () =
    // the requests are still in flight in `tasks` when the scope returns
    // `Task.WhenAll tasks`; `use client` would dispose the client under them
    let source =
        lines
            [
                "module Test"
                "open System.IO"
                "open System.Threading.Tasks"
                "let readAll (path: string) (n: int) ="
                "    let reader = new StreamReader(path)"
                "    let tasks = ResizeArray<Task<string>>()"
                "    for _ in 1 .. n do"
                "        tasks.Add(reader.ReadLineAsync())"
                "    Task.WhenAll tasks"
            ]

    assertTypechecks source

    match useBindingsIn source |> List.filter (fun s -> s.Name = "reader") with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.InFlight "ReadLineAsync"), s.Destination)
        Assert.Contains("'ReadLineAsync'", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory for 'reader', got %A" other

[<Fact>]
let ``FR0075: a task from the binder finished in the scope still gets the fix`` () =
    let source =
        lines
            [
                "module Test"
                "open System.IO"
                "let readAll (path: string) (n: int) ="
                "    let reader = new StreamReader(path)"
                "    for _ in 1 .. n do"
                "        printfn \"%s\" (reader.ReadLineAsync().Result)"
            ]

    match useBindingsIn source |> List.filter (fun s -> s.Name = "reader") with
    | [ s ] ->
        Assert.True(Some("let", "use") = s.Fix, $"Expected a fix for 'reader', got %A{s}")
        let patched = applyEdit source s.Range "use"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one use-binding fix for 'reader', got %A" other

// ---- 3 and 4: FR0012 HintEngine ----

let private hintsIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    HintEngine.find [] tree sourceText (Some check)

[<Fact>]
let ``FR0012: map over map with effectful mappers is not fused`` () =
    // `List.map f (List.map g xs)` prints every "b" before the first "a";
    // `List.map (g >> f) xs` alternates them. FR0137 fuses the pure case
    for m, t in [ "List", "int list"; "Array", "int array"; "Seq", "int seq" ] do
        let source =
            $"module Test\nlet f (xs: {t}) = {m}.map (fun x -> printfn \"a\"; x + 1) ({m}.map (fun x -> printfn \"b\"; x * 2) xs)"

        assertTypechecks source
        Assert.Empty(hintsIn source)

    // and the pure spelling is not a built-in hint either
    Assert.Empty(hintsIn "module Test\nlet f g h (xs: int list) = List.map g (List.map h xs)")

let private lifecycle =
    lines
        [
            "module Test"
            "type LifecycleBuilder() ="
            "    member _.Yield(_: unit) = \"\""
            "    [<CustomOperation(\"id\")>]"
            "    member _.Id(_: string, name: string) = name"
            "let lifecycleRule = LifecycleBuilder()"
            "let rule = lifecycleRule { id \"rule\" }"
        ]

[<Fact>]
let ``FR0012: a built-in hint stands down on a file whose typed check has an error`` () =
    // one unrelated error used to skip the "left-side names are
    // FSharp.Core's" gate, and the builder's custom operation `id` matched
    // `id x ===> x` by shape: `lifecycleRule { id "rule" }` lost its keyword
    let source = lifecycle + "\nlet broken : int = \"oops\""
    let tree, sourceText, check = parseAndCheck source
    Assert.True(OptionModule.hasErrors check, "the fixture is meant to carry a type error")
    Assert.Empty(HintEngine.find [] tree sourceText (Some check))

[<Fact>]
let ``FR0012: a built-in hint stands down on the parse-only path inside a computation expression`` () =
    // the custom operation lives only in the builder's body; outside one
    // the untyped path fires as before (AuditGuardsBTests)
    let tree, sourceText = parse lifecycle
    Assert.Empty(HintEngine.find [] tree sourceText None)

    // the same shape on FSharp.Core's own `id`, typed clean, still fires
    match hintsIn "module Test\nlet f (x: int) = id x" with
    | [ s ] -> Assert.Equal("x", s.ReplacementText)
    | other -> failwithf "Expected one id hint, got %A" other

// ---- 5: FR0015 RegexUsage ----

let private regexIn (source: string) =
    let tree, sourceText = parse source
    RegexUsage.find tree sourceText

[<Fact>]
let ``FR0015: an anchored-start literal becomes the ordinal StartsWith`` () =
    // the regex compared ordinally; `StartsWith(string)` is current-culture
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"^abc\")"

    match regexIn source with
    | [ s ] ->
        match s.Edits with
        | [ (range, _, replacement) ] ->
            Assert.Equal("s.StartsWith(\"abc\", System.StringComparison.Ordinal)", replacement)
            let patched = applyEdit source range replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected exactly one edit, got %A" other
    | other -> failwithf "Expected exactly one regex suggestion, got %A" other

[<Fact>]
let ``FR0015: an anchored-end literal keeps the regex`` () =
    // `$` matches before a final newline; EndsWith does not (the regex is
    // kept — and hoisted out of the function body, which is a different
    // finding)
    Assert.Empty(
        regexIn "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.IsMatch(s, \"abc$\")"
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)
    )

// ---- 6: FR0039 CaseInsensitive ----

let private caseIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CaseInsensitive.find tree sourceText checkResults

[<Fact>]
let ``FR0039: the culture-sensitive lowering keeps the idiomatic ordinal fix`` () =
    // the plain `ToLower()` and OrdinalIgnoreCase differ on the Turkish
    // dotless i alone (`"FILE".ToLower()` is "fıle" under tr-TR); the
    // idiomatic ordinal spelling stays the fix - a CurrentCultureIgnoreCase
    // nobody writes is not a fix anyone wants - with the InvariantCulture
    // spelling as the editor's alternative
    for source, expected in
        [
            "module Test\nopen System\nlet f (x: string) = x.ToLower() = \"abc\"",
            "String.Equals(x, \"abc\", StringComparison.OrdinalIgnoreCase)"
            "module Test\nopen System\nlet f (x: string) = x.ToUpper() <> \"ABC\"",
            "not (String.Equals(x, \"ABC\", StringComparison.OrdinalIgnoreCase))"
            "module Test\nopen System\nlet f (path: string) = path.ToLower().StartsWith \"file:\"",
            "path.StartsWith(\"file:\", StringComparison.OrdinalIgnoreCase)"
            "module Test\nopen System\nlet f (path: string) = path.ToUpper().EndsWith(\".CSV\")",
            "path.EndsWith(\".CSV\", StringComparison.OrdinalIgnoreCase)"
        ] do
        match caseIn source with
        | [ s ] ->
            Assert.Equal(Some expected, s.Replacement)
            Assert.True(s.CultureReplacement.IsSome, "the culture alternative is offered beside the default")
            let patched = applyEdit source s.Range s.Replacement.Value
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected one suggestion for %s, got %A" source other

[<Fact>]
let ``FR0039: an explicit StringComparison on the lowered call is respected`` () =
    let source =
        "module Test\nopen System\nlet f (name: string) = name.ToLower().StartsWith(\"abc\", StringComparison.CurrentCulture)"

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "name.StartsWith(\"abc\", StringComparison.CurrentCultureIgnoreCase)", s.Replacement)
        Assert.Equal(None, s.CultureReplacement)
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0055 SwallowedException: the IO narrowing needs IO-only calls ----

let private swallowedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SwallowedException.find tree sourceText (Some checkResults)

[<Fact>]
let ``FR0055: the IO-only narrowing is not offered when a user function is on the line`` () =
    // Fuuga: `Some (Path.GetFileName d, Checkpoint.loadMetadata p)` under a
    // catch-all was narrowed to IOException by the `Path` on the line, and
    // loadMetadata's JsonException escaped the command meant to skip junk
    let source =
        lines
            [
                "module Test"
                "open System.IO"
                "module Checkpoint ="
                "    let loadMetadata (p: string) = System.Text.Json.JsonDocument.Parse(File.ReadAllText p)"
                "let f (d: string) (p: string) ="
                "    try Some (Path.GetFileName d, Checkpoint.loadMetadata p)"
                "    with _ -> None"
            ]

    match swallowedIn source with
    | [ s ] -> Assert.DoesNotContain(s.Offers, fun o -> o.Label.StartsWith "Alternative: catch the IO")
    | other -> failwithf "Expected one swallow note, got %A" other

[<Fact>]
let ``FR0055: the IO-only narrowing stays for a body of System.IO calls alone`` () =
    let source =
        lines
            [
                "module Test"
                "open System.IO"
                "let f (p: string) ="
                "    try Some (File.ReadAllText p)"
                "    with _ -> None"
            ]

    match swallowedIn source with
    | [ s ] -> Assert.Contains(s.Offers, fun o -> o.Label.StartsWith "Alternative: catch the IO")
    | other -> failwithf "Expected one swallow note, got %A" other

[<Fact>]
let ``FR0039: the invariant lowering keeps its fix`` () =
    let source =
        "module Test\nopen System\nlet f (x: string) = x.ToLowerInvariant() = \"abc\""

    match caseIn source with
    | [ s ] ->
        Assert.Equal(Some "String.Equals(x, \"abc\", StringComparison.OrdinalIgnoreCase)", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- 7: FR0142 TestReturnsTask ----

let private testsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    TestReturnsTask.find tree sourceText checkResults

/// NUnit-shaped attributes declared in the fixture (the module is named
/// `NUnit.Framework` so the rule trusts them to await a Task).
let private nunitScaffold =
    lines
        [
            "module NUnit.Framework"
            "open System"
            "open System.Threading.Tasks"
            "type TestCaseAttribute() ="
            "    inherit Attribute()"
            "    member val ExpectedResult: int = 0 with get, set"
            "type TestAttribute() ="
            "    inherit Attribute()"
            "let fetch () = Task.FromResult 2"
        ]

[<Fact>]
let ``FR0142: a test whose final expression is the value it returns is not wrapped`` () =
    // `task { ... x + 1 } :> Task` compiles (FS0020 only) and NUnit no
    // longer compares the result with ExpectedResult
    let source =
        lines
            [
                nunitScaffold
                "type Fixture() ="
                "    [<TestCase(ExpectedResult = 3)>]"
                "    member _.Sum() ="
                "        let x = fetch().Result"
                "        x + 1"
            ]

    assertTypechecks source
    Assert.Empty(testsIn source)

[<Fact>]
let ``FR0142: a unit test with the same blocking let still moves`` () =
    let source =
        lines
            [
                nunitScaffold
                "type Fixture() ="
                "    [<Test>]"
                "    member _.Check() ="
                "        let x = fetch().Result"
                "        ignore (x + 1)"
            ]

    match testsIn source with
    | [ s ] ->
        Assert.Contains("let! x = fetch()", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- 8: FR0002 OptionModule ----

let private optionsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionModule.find tree sourceText checkResults

[<Fact>]
let ``FR0002: an arm calling the enclosing let rec keeps its tail call`` () =
    // inside the `Option.map` lambda the call is no longer in tail
    // position, and the loop grows the stack per element
    let topLevel =
        lines
            [
                "module Test"
                "let rec loop (xs: int list) acc ="
                "    match List.tryHead xs with"
                "    | Some v -> loop (List.tail xs) (acc + v)"
                "    | None -> acc"
            ]

    assertTypechecks topLevel
    Assert.Empty(optionsIn topLevel)

    let local =
        lines
            [
                "module Test"
                "let sum (xs: int list) ="
                "    let rec loop (xs: int list) acc ="
                "        match List.tryHead xs with"
                "        | Some v -> loop (List.tail xs) (acc + v)"
                "        | None -> acc"
                "    loop xs 0"
            ]

    assertTypechecks local
    Assert.Empty(optionsIn local)

[<Fact>]
let ``FR0002: the same arms without a recursive call still fold`` () =
    let source =
        lines
            [
                "module Test"
                "let step (xs: int list) acc ="
                "    match List.tryHead xs with"
                "    | Some v -> acc + v"
                "    | None -> acc"
            ]

    match optionsIn source with
    | [ s ] ->
        Assert.StartsWith("Option.map", s.Target)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other
