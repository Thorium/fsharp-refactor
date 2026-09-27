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
        fsharp
            """
            module Test
            let f () =
            #if !WINDOWS
                System.Runtime.InteropServices.Marshal.AllocHGlobal 1 |> ignore
                System.Runtime.InteropServices.Marshal.AllocHGlobal 2 |> ignore
                System.Runtime.InteropServices.Marshal.AllocHGlobal 3 |> ignore
            #endif
                ()
            """

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
        fsharp
            """
            #if !FABLE_COMPILER
            module Test
            let a = System.Text.RegularExpressions.Regex.Escape "a"
            let b = System.Text.RegularExpressions.Regex.Escape "b"
            let c = System.Text.RegularExpressions.Regex.Escape "c"
            #endif
            """

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, text) ] ->
            Assert.Equal(
                fsharp
                    """
                    open System.Text.RegularExpressions

                    """,
                text
            )

            Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected one open under the module line, got %A" other

        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                #if !FABLE_COMPILER
                module Test
                open System.Text.RegularExpressions
                let a = Regex.Escape "a"
                let b = Regex.Escape "b"
                let c = Regex.Escape "c"
                #endif
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a #if between two top-level declarations still takes the open under it`` () =
    let source =
        fsharp
            """
            module Test
            let g = 1
            #if !FOO
            let a = System.Text.Encoding.UTF8
            let b = System.Text.Encoding.ASCII
            let c = System.Text.Encoding.Unicode
            #endif
            """

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, text) ] ->
            Assert.Equal(
                fsharp
                    """
                    open System.Text

                    """,
                text
            )

            Assert.Equal(4, r.StartLine)
        | other -> failwithf "Expected one open inside the #if, got %A" other

        let patched = applyAll source s.Edits
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0147 QualifiedNames: B9, files without a module header ----

[<Fact>]
let ``FR0147: a script's open lands after its leading hash directives`` () =
    // the `#r` is what makes the namespace exist: an open above it is
    // FS0039
    let source =
        fsharp
            """
            #r "System.Text.RegularExpressions"
            #I "."
            let a = System.Text.RegularExpressions.Regex.Escape "a"
            let b = System.Text.RegularExpressions.Regex.Escape "b"
            let c = System.Text.RegularExpressions.Regex.Escape "c"
            """

    match qualifiedIn source with
    | [ s ] ->
        match opensOf s with
        | [ (r, _, _) ] -> Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected one open after the directives, got %A" other

        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                #r "System.Text.RegularExpressions"
                #I "."
                open System.Text.RegularExpressions
                let a = Regex.Escape "a"
                let b = Regex.Escape "b"
                let c = Regex.Escape "c"
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a first declaration's doc block keeps its let`` () =
    let source =
        fsharp
            """
            /// The first task.
            /// Two lines of it.
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                open System.Threading.Tasks
                /// The first task.
                /// Two lines of it.
                let a = Task.FromResult 1
                let b = Task.Delay 10
                let c (t: Task<int>) = t.Result
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: a file without a header and without directives still opens before its first declaration`` () =
    let source =
        fsharp
            """
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

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
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.Replace(s, "abc", "a\\nb")
            """

    Assert.Empty(stringOperations source)

[<Fact>]
let ``FR0015: a verbatim backslash replacement keeps the engine`` () =
    // `@"\"` re-emitted as `"\"` is an unterminated string
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let toWindows (p: string) = Regex.Replace(p, "/", @"\")
            """

    Assert.Empty(stringOperations source)

[<Fact>]
let ``FR0015: a plain Replace replacement still becomes String.Replace`` () =
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.Replace(s, "abc", "x")
            """

    match stringOperations source with
    | [ s ] ->
        match s.Edits with
        | [ (r, _, replacement) ] ->
            Assert.Equal("""s.Replace("abc", "x")""", replacement)
            let patched = applyEdit source r replacement
            assertTypechecks "Patched source" patched
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
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let g (xs: string list) =
                xs |> List.map (fun x -> Regex.Match(x, "b+").Success)
            """

    let patched = hoistPatched source
    Assert.Contains("gRegex.Match(x).Success", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``FR0015: a hoisted Split keeps its index continuation on the call`` () =
    // a real pattern: a literal one is FR0015's String.Split rewrite instead
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let g (xs: string list) =
                xs |> List.map (fun s -> Regex.Split(s, "p+").[0])
            """

    let patched = hoistPatched source
    Assert.Contains("gRegex.Split(s).[0]", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``FR0015: a hoisted IsMatch is a parenthesised call`` () =
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                for s in xs do
                    if Regex.IsMatch(s, "a.c") then printfn "%s" s
            """

    let patched = hoistPatched source

    Assert.Equal(
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a.c"
            let f (xs: string list) =
                for s in xs do
                    if fRegex.IsMatch(s) then printfn "%s" s
            """,
        patched
    )

    assertTypechecks "Patched source" patched

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
            assertTypechecks "Checked source" patched
        | None -> failwith "Expected the Checked offer"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0105: arithmetic already widened by the author gets no widening offer`` () =
    // `int64 (int64 seconds * 1_000_000L) |> Checked.int` flipped the
    // function's result type from int64 to int
    assertNoWiden (
        fsharp
            """
            module Test
            let k (seconds: int) = int64 (seconds * 1_000_000)
            """
    )

[<Fact>]
let ``FR0105: arithmetic inside a method argument gets no widening offer`` () =
    // the paren held a tuple: `int64 (seconds * 1_000_000, 0)`
    assertNoWiden (
        fsharp
            """
            module Test
            let m (seconds: int) = System.Math.Max(seconds * 1_000_000, 0)
            """
    )

[<Fact>]
let ``FR0105: arithmetic on one side of a comparison gets no widening offer`` () =
    // `|> Checked.int` binds looser than `<`: Checked.int of a bool
    assertNoWiden (
        fsharp
            """
            module Test
            let f (limit: int) (seconds: int) = if limit < seconds * 1_000_000 then 1 else 0
            """
    )

[<Fact>]
let ``FR0105: a binding's whole right-hand side still widens, as a prefix call`` () =
    let source = "module Test\nlet micros (seconds: int) = seconds * 1_000_000"

    match checkedIn source with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit source r widened
            assertTypechecks "Widened source" patched
        | None -> failwith "Expected the widening offer"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0105: a local binding and an assignment widen too`` () =
    let local =
        fsharp
            """
            module Test
            let f (seconds: int) =
                let micros = seconds * 1_000_000
                micros
            """

    match checkedIn local with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit local r widened
            assertTypechecks "Widened source" patched
        | None -> failwith "Expected the widening offer on a local binding"
    | other -> failwithf "Expected one finding, got %A" other

    let assignment =
        fsharp
            """
            module Test
            let f (seconds: int) =
                let mutable total = 0
                total <- seconds * 1_000_000
                total
            """

    match checkedIn assignment with
    | [ s ] ->
        match s.WidenFix with
        | Some(r, _, widened) ->
            Assert.Equal("Checked.int (int64 seconds * 1_000_000L)", widened)
            let patched = applyEdit assignment r widened
            assertTypechecks "Widened source" patched
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
            assertTypechecks "Widened source" patched
        | None -> failwith "Expected the widening offer"
    | other -> failwithf "Expected one finding, got %A" other
