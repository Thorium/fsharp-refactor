/// Audit fixes for FR0147 (QualifiedNames), FR0015 (RegexUsage) and FR0105
/// (CheckedArithmetic): every repro from the 0.8.2-to-HEAD audit, asserting
/// that the wrong fix is withheld (or corrected) and that the safe shape
/// each fix was designed for still gets it.
module FSharp.Refactor.Tests.AuditRegexQualifiedTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

// ---- FR0147 QualifiedNames: B8, the `#if` region insertion ----

// the tight thresholds, so the shapes stay small; the defaults are 6 and 4
let private qualifiedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    QualifiedNames.find 3 2 tree sourceText checkResults

let private opensOf (s: QualifiedNames.Suggestion) =
    s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open")

[<Fact>]
let ``FR0147: uses under a #if inside a function body get no open`` () =
    // the line after the `#if` is in expression position: an `open` there
    // is FS0010. Note only
    let source =
        "module Test\nlet f () =\n#if !WINDOWS\n    System.Runtime.InteropServices.Marshal.AllocHGlobal 1 |> ignore\n    System.Runtime.InteropServices.Marshal.AllocHGlobal 2 |> ignore\n    System.Runtime.InteropServices.Marshal.AllocHGlobal 3 |> ignore\n#endif\n    ()"

    match qualifiedIn source with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.True(s.Reason.IsSome, "expected a reason for the withheld open")
    | other -> failwithf "Expected one fix-less suggestion, got %A" other

[<Fact>]
let ``FR0147: a whole file under #if takes its open under the module line, not above it`` () =
    // the `#if` sits above `module Test`; the line after it is the header
    // itself, so the open goes under the header - still inside the region
    let source =
        "#if !FABLE_COMPILER\nmodule Test\nlet a = System.Text.RegularExpressions.Regex.Escape \"a\"\nlet b = System.Text.RegularExpressions.Regex.Escape \"b\"\nlet c = System.Text.RegularExpressions.Regex.Escape \"c\"\n#endif"

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, text) ] ->
            Assert.Equal("open System.Text.RegularExpressions\n", text)
            Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected one open under the module line, got %A" other

        let patched = applyAll source s.Edits

        Assert.Equal(
            "#if !FABLE_COMPILER\nmodule Test\nopen System.Text.RegularExpressions\nlet a = Regex.Escape \"a\"\nlet b = Regex.Escape \"b\"\nlet c = Regex.Escape \"c\"\n#endif",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a #if between two top-level declarations still takes the open under it`` () =
    let source =
        "module Test\nlet g = 1\n#if !FOO\nlet a = System.Text.Encoding.UTF8\nlet b = System.Text.Encoding.ASCII\nlet c = System.Text.Encoding.Unicode\n#endif"

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, text) ] ->
            Assert.Equal("open System.Text\n", text)
            Assert.Equal(4, r.StartLine)
        | other -> failwithf "Expected one open inside the #if, got %A" other

        let patched = applyAll source s.Edits
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0147 QualifiedNames: B9, files without a module header ----

[<Fact>]
let ``FR0147: a script's open lands after its leading hash directives`` () =
    // the `#r` is what makes the namespace exist: an open above it is
    // FS0039
    let source =
        "#r \"System.Text.RegularExpressions\"\n#I \".\"\nlet a = System.Text.RegularExpressions.Regex.Escape \"a\"\nlet b = System.Text.RegularExpressions.Regex.Escape \"b\"\nlet c = System.Text.RegularExpressions.Regex.Escape \"c\""

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, _) ] -> Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected one open after the directives, got %A" other

        let patched = applyAll source s.Edits

        Assert.Equal(
            "#r \"System.Text.RegularExpressions\"\n#I \".\"\nopen System.Text.RegularExpressions\nlet a = Regex.Escape \"a\"\nlet b = Regex.Escape \"b\"\nlet c = Regex.Escape \"c\"",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a first declaration's doc block keeps its let`` () =
    let source =
        "/// The first task.\n/// Two lines of it.\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            "open System.Threading.Tasks\n/// The first task.\n/// Two lines of it.\nlet a = Task.FromResult 1\nlet b = Task.Delay 10\nlet c (t: Task<int>) = t.Result",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a file without a header and without directives still opens before its first declaration`` () =
    let source =
        "let a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, _) ] -> Assert.Equal(1, r.StartLine)
        | other -> failwithf "Expected one open at the top, got %A" other
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0015 RegexUsage: A4, the Replace replacement literal ----

let private regexIn (source: string) =
    let tree, sourceText = parse source
    RegexUsage.find tree sourceText

let private stringOperations (source: string) =
    regexIn source
    |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)

[<Fact>]
let ``FR0015: a Replace replacement with an escaped backslash keeps the engine`` () =
    // the replacement text is a\nb, four characters; re-emitted inside a
    // regular literal it would be a newline
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.Replace(s, \"abc\", \"a\\\\nb\")"

    Assert.Empty(stringOperations source)

[<Fact>]
let ``FR0015: a verbatim backslash replacement keeps the engine`` () =
    // `@"\"` re-emitted as `"\"` is an unterminated string
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet toWindows (p: string) = Regex.Replace(p, \"/\", @\"\\\")"

    Assert.Empty(stringOperations source)

[<Fact>]
let ``FR0015: a plain Replace replacement still becomes String.Replace`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = Regex.Replace(s, \"abc\", \"x\")"

    match stringOperations source with
    | [ s ] ->
        match s.Edits with
        | [ (r, _, replacement) ] ->
            Assert.Equal("s.Replace(\"abc\", \"x\")", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected one edit, got %A" other
    | other -> failwithf "Expected one string-operation fix, got %A" other

// ---- FR0015 RegexUsage: B10, the hoisted instance call ----

let private hoistPatched (source: string) =
    match
        regexIn source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistFromLoop)
    with
    | [ s ] ->
        Assert.NotEmpty s.Edits
        applyAll source s.Edits
    | other -> failwithf "Expected one hoist with a fix, got %A" other

[<Fact>]
let ``FR0015: a hoisted Match keeps its Success continuation on the call`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet g (xs: string list) =\n    xs |> List.map (fun x -> Regex.Match(x, \"b+\").Success)"

    let patched = hoistPatched source
    Assert.Contains("bRegex.Match(x).Success", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0015: a hoisted Split keeps its index continuation on the call`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet g (xs: string list) =\n    xs |> List.map (fun s -> Regex.Split(s, \"p\").[0])"

    let patched = hoistPatched source
    Assert.Contains("pRegex.Split(s).[0]", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0015: a hoisted IsMatch is a parenthesised call`` () =
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for s in xs do\n        if Regex.IsMatch(s, \"a.c\") then printfn \"%s\" s"

    let patched = hoistPatched source

    Assert.Equal(
        "module Test\nopen System.Text.RegularExpressions\nlet private acRegex = Regex \"a.c\"\nlet f (xs: string list) =\n    for s in xs do\n        if acRegex.IsMatch(s) then printfn \"%s\" s",
        patched
    )

    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- FR0105 CheckedArithmetic: A6, the widening offer ----

let private checkedIn (source: string) =
    let tree, sourceText = parse source
    CheckedArithmetic.find tree sourceText

let private assertNoWiden (source: string) =
    match checkedIn source with
    | [ s ] ->
        Assert.Equal(None, s.WidenFix)

        // the Checked offer, a prefix application, is fine everywhere
        match s.CheckedFix with
        | Some(r, _, checked') ->
            let patched = applyEdit source r checked'
            Assert.True(typechecksCleanly patched, $"Checked source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the Checked offer"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0105: arithmetic already widened by the author gets no widening offer`` () =
    // `int64 (int64 seconds * 1_000_000L) |> Checked.int` flipped the
    // function's result type from int64 to int
    assertNoWiden "module Test\nlet k (seconds: int) = int64 (seconds * 1_000_000)"

[<Fact>]
let ``FR0105: arithmetic inside a method argument gets no widening offer`` () =
    // the paren held a tuple: `int64 (seconds * 1_000_000, 0)`
    assertNoWiden "module Test\nlet m (seconds: int) = System.Math.Max(seconds * 1_000_000, 0)"

[<Fact>]
let ``FR0105: arithmetic on one side of a comparison gets no widening offer`` () =
    // `|> Checked.int` binds looser than `<`: Checked.int of a bool
    assertNoWiden "module Test\nlet f (limit: int) (seconds: int) = if limit < seconds * 1_000_000 then 1 else 0"

[<Fact>]
let ``FR0105: a binding's whole right-hand side still widens, as a prefix call`` () =
    let source = "module Test\nlet micros (seconds: int) = seconds * 1_000_000"

    match checkedIn source with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit source r widened
            Assert.True(typechecksCleanly patched, $"Widened source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the widening offer"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0105: a local binding and an assignment widen too`` () =
    let local =
        "module Test\nlet f (seconds: int) =\n    let micros = seconds * 1_000_000\n    micros"

    match checkedIn local with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit local r widened
            Assert.True(typechecksCleanly patched, $"Widened source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the widening offer on a local binding"
    | other -> failwithf "Expected one finding, got %A" other

    let assignment =
        "module Test\nlet f (seconds: int) =\n    let mutable total = 0\n    total <- seconds * 1_000_000\n    total"

    match checkedIn assignment with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit assignment r widened
            Assert.True(typechecksCleanly patched, $"Widened source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the widening offer on an assignment"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0105: the widening climbs a parenthesised operand of a wider arithmetic`` () =
    let source = "module Test\nlet x = (1000000 * 1000000 + 5) / 100000"

    match checkedIn source with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int ((1000000L * 1000000L + 5L) / 100000L)", widened)
            let patched = applyEdit source r widened
            Assert.True(typechecksCleanly patched, $"Widened source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the widening offer"
    | other -> failwithf "Expected one finding, got %A" other
