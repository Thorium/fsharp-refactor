[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.NewAnalyzerTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open System.IO
open System.Text.RegularExpressions

// ---- FR0015 RegexUsage ----

let private regexIn (source: string) =
    let tree, sourceText = parse source
    RegexUsage.find tree sourceText

/// The rule-1 view: a pattern the string rewrite declines. The regex stays
/// a regex there, and a hoist from the function body is a different finding.
let private noStringOperation (source: string) =
    Assert.Empty(
        regexIn source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)
    )

let private assertRegexFix (source: string) (expectedReplacement: string) =
    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.StringOperation, s.Kind)

        match s.Edits with
        | [ (range, _, replacement) ] ->
            Assert.Equal(expectedReplacement, replacement)
            let patched = applyEdit source range replacement
            assertParses "Patched source" patched
        | other -> failwithf "Expected exactly one edit, got %A" other
    | other -> failwithf "Expected exactly one regex suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``FR0015: a literal-pattern Regex.Replace becomes String.Replace`` () =
    assertRegexFix
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.Replace(s, "abcd", "x")
            """)
        """s.Replace("abcd", "x")"""

[<Fact>]
let ``FR0015: Regex.Replace keeps the engine wherever the swap would differ`` () =
    // each of these gives a different answer under String.Replace:
    //   "$&!"   Regex -> "xxabcd!yy"   String -> "xx$&!yy"
    //   "a$$b"  Regex -> "xxa$byy"     String -> "xxa$$byy"
    //   ""      Regex inserts between every char; String THROWS
    let unchanged (body: string) =
        let source =
            "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = " + body

        Assert.Empty(
            regexIn source
            |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)
        )

    unchanged """Regex.Replace(s, "[a-z]+", "x")""" // a real pattern
    unchanged """Regex.Replace(s, "abcd", "$&!")""" // substitution syntax
    unchanged """Regex.Replace(s, "abcd", "a$$b")""" // $$ is one $ to Regex
    unchanged """Regex.Replace(s, "", "-")""" // String.Replace would throw
    unchanged """Regex.Replace(s, "^abcd", "x")""" // an anchor Replace cannot carry
    unchanged """Regex.Replace(s, "abcd", "x", RegexOptions.IgnoreCase)""" // different operation

[<Fact>]
let ``FR0015: Match(...).Success and a Matches(...).Count test are the same Contains or StartsWith`` () =
    let header =
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = "

    assertRegexFix (header + """Regex.Match(s, "abcd").Success""") "s.Contains \"abcd\""

    assertRegexFix
        (header + """Regex.Match(s, "^abcd").Success""")
        """s.StartsWith("abcd", System.StringComparison.Ordinal)"""

    for test in [ "> 0"; "<> 0"; ">= 1" ] do
        assertRegexFix (header + $"Regex.Matches(s, \"abcd\").Count {test}") "s.Contains \"abcd\""

    for test in [ "= 0"; "< 1"; "<= 0" ] do
        assertRegexFix (header + $"Regex.Matches(s, \"abcd\").Count {test}") """not (s.Contains "abcd")"""

    // the literal on the left flips the comparison
    assertRegexFix (header + """0 < Regex.Matches(s, "abcd").Count""") "s.Contains \"abcd\""
    assertRegexFix (header + """0 = Regex.Matches(s, "abcd").Count""") """not (s.Contains "abcd")"""

    assertRegexFix
        (header + """1 > Regex.Matches(s, "^abcd").Count""")
        """not (s.StartsWith("abcd", System.StringComparison.Ordinal))"""

    // typechecks, and the semantics hold on the engine's own answers
    let source =
        header
        + """Regex.Match(s, "^abcd").Success, Regex.Matches(s, "abcd").Count > 0, 0 = Regex.Matches(s, "abcd").Count"""

    let patched =
        regexIn source
        |> List.collect (fun s -> s.Edits)
        |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
        |> List.fold (fun src (r, _, t) -> applyEdit src r t) source

    Assert.Equal(
        header
        + """s.StartsWith("abcd", System.StringComparison.Ordinal), s.Contains "abcd", not (s.Contains "abcd")""",
        patched
    )

    assertTypechecks "Patched source" patched

    for input in [ "abcd"; "xabcd"; "abc"; ""; "abcdabcd" ] do
        Assert.Equal(
            (Regex.Match(input, "^abcd").Success,
             Regex.Matches(input, "abcd").Count > 0,
             0 = Regex.Matches(input, "abcd").Count),
            (input.StartsWith("abcd", System.StringComparison.Ordinal),
             input.Contains "abcd",
             not (input.Contains "abcd"))
        )

[<Fact>]
let ``FR0015: a count that is a count, a real pattern and a Matches call on its own keep the engine`` () =
    let header =
        "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = "

    for body in
        [
            """Regex.Matches(s, "abcd").Count > 1"""
            """Regex.Matches(s, "abcd").Count"""
            """Regex.Matches(s, "a+").Count > 0"""
            """Regex.Match(s, "a.c").Success"""
            """Regex.Match(s, "abcd").Value"""
            """Regex.Matches(s, "abcd", RegexOptions.IgnoreCase).Count > 0"""
        ] do
        Assert.Empty(
            regexIn (header + body)
            |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)
        )

[<Fact>]
let ``FR0015: a literal-pattern Regex.Split is a String.Split with that separator`` () =
    assertRegexFix
        (fsharp
            """
            module Test
            open System
            open System.Text.RegularExpressions
            let f (s: string) = Regex.Split(s, "ab")
            """)
        """s.Split([| "ab" |], StringSplitOptions.None)"""

    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.Split(s, ", ")
            """

    match regexIn source with
    | [ s ] ->
        let _, _, replacement = s.Edits.Head
        Assert.Equal("""s.Split([| ", " |], System.StringSplitOptions.None)""", replacement)
        let patched = applyEdit source s.Range replacement
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

    for input in [ "a, b, c"; ", a, "; ""; "abc"; ", , " ] do
        Assert.Equal<string[]>(Regex.Split(input, ", "), input.Split([| ", " |], System.StringSplitOptions.None))

    // an anchored, a metacharacter and an options pattern keep the engine
    for body in
        [
            """Regex.Split(s, "^ab")"""
            """Regex.Split(s, "a|b")"""
            """Regex.Split(s, "ab", RegexOptions.IgnoreCase)"""
        ] do
        Assert.Empty(
            regexIn ("module Test\nopen System.Text.RegularExpressions\nlet f (s: string) = " + body)
            |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.StringOperation)
        )

[<Fact>]
let ``FR0015: a count test in a loop is the string operation alone, not a hoist as well`` () =
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (lines: string list) =
                for line in lines do
                    if Regex.Matches(line, "abcd").Count > 0 then printfn "%s" line
            """

    match regexIn source with
    | [ s ] -> Assert.Equal(RegexUsage.RegexSuggestionKind.StringOperation, s.Kind)
    | other -> failwithf "Expected the string operation alone, got %A" other

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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one hoist suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``anchored-start literal becomes an ordinal StartsWith`` () =
    // the regex compared ordinally; the bare `StartsWith "abc"` overload is
    // current-culture, so the Ordinal overload is the faithful spelling —
    // qualified, as the file does not `open System`
    assertRegexFix
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "^abc")
            """)
        """s.StartsWith("abc", System.StringComparison.Ordinal)"""

[<Fact>]
let ``anchored-start literal under open System spells the comparison short`` () =
    assertRegexFix
        (fsharp
            """
            module Test
            open System
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "^abc")
            """)
        """s.StartsWith("abc", StringComparison.Ordinal)"""

[<Fact>]
let ``anchored-end literal keeps the regex`` () =
    // `$` also matches before a final newline: `Regex.IsMatch("abc\n",
    // "abc$")` is true where `"abc\n".EndsWith "abc"` is false
    noStringOperation (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "abc$")
            """
    )

[<Fact>]
let ``unanchored literal becomes Contains`` () =
    assertRegexFix
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "abc")
            """)
        "s.Contains \"abc\""

[<Fact>]
let ``a member access after the test keeps the argument parenthesised`` () =
    // `s.Contains "abc".ToString()` would call ToString on the literal
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "abc").ToString()
            """

    assertRegexFix source """s.Contains("abc")"""

    match regexIn source with
    | [ { Edits = [ (range, _, replacement) ] } ] ->
        assertTypechecks "Patched source" (applyEdit source range replacement)
    | other -> failwithf "Expected one edit, got %A" other

[<Fact>]
let ``a case-insensitive construction without CultureInvariant is not hoisted`` () =
    // IgnoreCase folds case by the culture current at construction: built
    // per call it follows the thread's culture, hoisted it freezes the first
    let hoists (options: string) =
        regexIn (
            "module Test\nopen System.Text.RegularExpressions\nlet f (s: string) =\n    let r = Regex(\"a+\", "
            + options
            + ")\n    r.IsMatch s"
        )
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistConstruction)

    Assert.Empty(hoists "RegexOptions.IgnoreCase")
    Assert.Empty(hoists "RegexOptions.IgnoreCase ||| RegexOptions.Compiled")
    Assert.NotEmpty(hoists "RegexOptions.IgnoreCase ||| RegexOptions.CultureInvariant")
    Assert.NotEmpty(hoists "RegexOptions.Compiled")

[<Fact>]
let ``pattern with metacharacters is left alone`` () =
    noStringOperation (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "a.c")
            """
    )

[<Fact>]
let ``escaped dollar is not an anchor`` () =
    noStringOperation (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "abc\\$")
            """
    )

[<Fact>]
let ``fully anchored pattern is left alone`` () =
    noStringOperation (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, "^abc$")
            """
    )

[<Fact>]
let ``a regex call in a function body is hoisted once per call, a module value's is not`` () =
    // a function is called from loops the file cannot see (CR0109 hoists
    // from any member body); a module value's initialiser runs once
    match
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let f (s: string) = Regex.IsMatch(s, "a.c")
                """
        )
    with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistFromLoop, s.Kind)
        Assert.Equal(RegexUsage.Repeat.FunctionCall, s.Repeat)
        Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one per-call hoist, got %A" other

    Assert.Empty(
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let ok = Regex.IsMatch("abc", "a.c")
                """
        )
    )

    // a static call in a function body WITHOUT a landing fix (no open) is
    // not worth a note: the runtime cache serves it
    Assert.Empty(
        regexIn (
            fsharp
                """
                module Test
                let f (s: string) = System.Text.RegularExpressions.Regex.IsMatch(s, "a.c")
                """
        )
    )

    // a construction in a function body is parsed per call: hoisted
    match
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let f (s: string) =
                    let r = Regex("a+")
                    r.IsMatch s
                """
        )
    with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistConstruction, s.Kind)
        Assert.Equal(RegexUsage.Repeat.FunctionCall, s.Repeat)
    | other -> failwithf "Expected one construction hoist, got %A" other

[<Fact>]
let ``regex call in a loop is hoisted above the declaration`` () =
    assertRegexHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                for s in xs do
                    if Regex.IsMatch(s, "a.c") then printfn "%s" s
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a.c"
            let f (xs: string list) =
                for s in xs do
                    if fRegex.IsMatch(s) then printfn "%s" s
            """)

[<Fact>]
let ``hoist without the open stays advice-only`` () =
    let source =
        fsharp
            """
            module Test
            let f (xs: string list) =
                for s in xs do
                    if System.Text.RegularExpressions.Regex.IsMatch(s, "a.c") then printfn "%s" s
            """

    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistFromLoop, s.Kind)
        Assert.Empty s.Edits
    | other -> failwithf "Expected exactly one advice-only hoist, got %A" other

[<Fact>]
let ``regex Replace in a loop is hoisted with both remaining arguments`` () =
    assertRegexHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                for s in xs do
                    printfn "%s" (Regex.Replace(s, "a.c", "-"))
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a.c"
            let f (xs: string list) =
                for s in xs do
                    printfn "%s" (fRegex.Replace(s, "-"))
            """)

[<Fact>]
let ``literal match in a loop reports only the string operation`` () =
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                for s in xs do
                    if Regex.IsMatch(s, "abc") then printfn "%s" s
            """

    match regexIn source with
    | [ s ] -> Assert.Equal(RegexUsage.RegexSuggestionKind.StringOperation, s.Kind)
    | other -> failwithf "Expected exactly one string-op suggestion, got %A" other

[<Fact>]
let ``instance regex call outside a loop is not flagged`` () =
    Assert.Empty(
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let r = Regex "a.c"
                let f (s: string) = r.IsMatch s
                """
        )
    )

[<Fact>]
let ``regex call in a List.filter lambda is hoisted like a loop`` () =
    // a lambda handed to a collection function runs once per element
    assertRegexHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                xs |> List.filter (fun s -> Regex.IsMatch(s, "a.c"))
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a.c"
            let f (xs: string list) =
                xs |> List.filter (fun s -> fRegex.IsMatch(s))
            """)

[<Fact>]
let ``regex call in a lambda given to a non-collection function is not a loop`` () =
    // `lock` runs its callback once; only List/Seq/Array callbacks iterate
    // — the site still hoists, as any function body does, but per CALL
    match
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let f (o: obj) (s: string) =
                    lock o (fun () -> Regex.IsMatch(s, "a.c"))
                """
        )
    with
    | [ s ] -> Assert.Equal(RegexUsage.Repeat.FunctionCall, s.Repeat)
    | other -> failwithf "Expected one per-call hoist, got %A" other

/// Apply a construction hoist's edits bottom-up and verify the patched text.
let private assertRegexConstructionHoist (source: string) (expectedPatched: string) =
    match regexIn source with
    | [ s ] ->
        Assert.Equal(RegexUsage.RegexSuggestionKind.HoistConstruction, s.Kind)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, t) -> applyEdit acc r t) source

        Assert.Equal(expectedPatched, patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one construction hoist, got %d: %A" (List.length other) other

[<Fact>]
let ``regex constructed in a for loop is hoisted and the binding becomes an alias`` () =
    assertRegexConstructionHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                for x in xs do
                    let r = Regex "a+"
                    r.IsMatch x |> ignore
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a+"
            let f (xs: string list) =
                for x in xs do
                    let r = fRegex
                    r.IsMatch x |> ignore
            """)

[<Fact>]
let ``regex constructed in a List.map lambda is hoisted with the Split chain intact`` () =
    // as a hand hoist does it: only the construction moves, the `let
    // regex =` and the `.Split(v)` after it stay as they were
    assertRegexConstructionHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let expandMultiProperties (properties: (string * string) list) =
                properties |> List.map (fun (k, v) ->
                    let regex = Regex(";([a-z,A-Z,0-9,_,-]*)=")
                    let splits = regex.Split(v)
                    k, splits)
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private expandMultiPropertiesRegex = Regex(";([a-z,A-Z,0-9,_,-]*)=")
            let expandMultiProperties (properties: (string * string) list) =
                properties |> List.map (fun (k, v) ->
                    let regex = expandMultiPropertiesRegex
                    let splits = regex.Split(v)
                    k, splits)
            """)

[<Fact>]
let ``regex constructed with constant RegexOptions keeps them in the hoisted binding`` () =
    assertRegexConstructionHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
                xs |> List.map (fun x -> Regex("a+", RegexOptions.IgnoreCase ||| RegexOptions.CultureInvariant ||| RegexOptions.Multiline).IsMatch x)
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex("a+", RegexOptions.IgnoreCase ||| RegexOptions.CultureInvariant ||| RegexOptions.Multiline)
            let f (xs: string list) =
                xs |> List.map (fun x -> fRegex.IsMatch x)
            """)

[<Fact>]
let ``a qualified regex construction hoists without the open`` () =
    assertRegexConstructionHoist
        (fsharp
            """
            module Test
            let f (xs: string list) =
                for x in xs do
                    let r = new System.Text.RegularExpressions.Regex("a+")
                    r.IsMatch x |> ignore
            """)
        (fsharp
            """
            module Test
            let private fRegex = new System.Text.RegularExpressions.Regex("a+")
            let f (xs: string list) =
                for x in xs do
                    let r = fRegex
                    r.IsMatch x |> ignore
            """)

[<Fact>]
let ``a declined regex construction stays silent here and remains FR0037's note`` () =
    // a non-literal pattern, options naming a local, a bare `Regex` without
    // the open: each could differ per iteration or not be the Regex type
    // at all. This rule adds nothing, and LoopPerf's note still fires
    let declined (source: string) =
        let tree, sourceText = parse source
        Assert.Empty(RegexUsage.find tree sourceText)
        Assert.Empty(RegexUsage.hoistedConstructions true tree sourceText)
        let _, constructions = LoopPerf.find false None tree sourceText
        Assert.Equal(1, constructions.Length)

    declined (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (pattern: string) (xs: string list) =
                for x in xs do
                    let r = Regex pattern
                    r.IsMatch x |> ignore
            """
    )

    declined (
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (opts: RegexOptions) (xs: string list) =
                for x in xs do
                    let r = Regex("a+", opts)
                    r.IsMatch x |> ignore
            """
    )

    declined (
        fsharp
            """
            module Test
            let f (xs: string list) =
                for x in xs do
                    let r = Regex "a+"
                    r.IsMatch x |> ignore
            """
    )

    // and where this rule DOES fix, the range it hands FR0037 is the one
    // LoopPerf reports, so the note can stand down on exactly that node
    let tree, sourceText =
        parse (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let f (xs: string list) =
                    for x in xs do
                        let r = Regex "a+"
                        r.IsMatch x |> ignore
                """
        )

    let _, constructions = LoopPerf.find false None tree sourceText

    match RegexUsage.hoistedConstructions true tree sourceText, constructions with
    | [ hoisted ], [ noted ] -> Assert.Equal(noted.Range, hoisted)
    | other -> failwithf "Expected one hoist matching one note, got %A" other

[<Fact>]
let ``a hoisted regex binding lands above the declaration's doc comment`` () =
    // a declaration's range starts at its `///` block, so the binding goes
    // above it and the doc stays on the function; a plain `//` line above
    // the declaration is outside the range and is walked over the same way
    assertRegexHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions

            /// Counts the a-runs.
            /// Two lines of it.
            let f (xs: string list) =
                for x in xs do
                    if Regex.IsMatch(x, "a+") then ()
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions

            let private fRegex = Regex "a+"
            /// Counts the a-runs.
            /// Two lines of it.
            let f (xs: string list) =
                for x in xs do
                    if fRegex.IsMatch(x) then ()
            """)

    assertRegexHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let g = 1
            // counts the a-runs
            let f (xs: string list) =
                for x in xs do
                    if Regex.IsMatch(x, "a+") then ()
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let g = 1
            let private fRegex = Regex "a+"
            // counts the a-runs
            let f (xs: string list) =
                for x in xs do
                    if fRegex.IsMatch(x) then ()
            """)

    assertRegexConstructionHoist
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            /// Counts the a-runs.
            let f (xs: string list) =
                for x in xs do
                    let r = Regex "a+"
                    r.IsMatch x |> ignore
            """)
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let private fRegex = Regex "a+"
            /// Counts the a-runs.
            let f (xs: string list) =
                for x in xs do
                    let r = fRegex
                    r.IsMatch x |> ignore
            """)

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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one struct-DU suggestion, got %d: %A" (List.length other) other

let private assertStructDu (source: string) (expectedPatched: string) =
    assertPatchedStructDu (structDuIn source) source expectedPatched

[<Fact>]
let ``small named-field union gains the attribute`` () =
    assertStructDu
        (fsharp
            """
            module Test
            type private Shape =
                | Circle of radius: float
                | Square of side: float
            """)
        (fsharp
            """
            module Test
            [<Struct>]
            type private Shape =
                | Circle of radius: float
                | Square of side: float
            """)

[<Fact>]
let ``single fielded case may be unnamed`` () =
    assertStructDu
        (fsharp
            """
            module Test
            type private Id =
                | Id of int
                | Missing
            """)
        (fsharp
            """
            module Test
            [<Struct>]
            type private Id =
                | Id of int
                | Missing
            """)

[<Fact>]
let ``a public union is left alone`` () =
    // struct-vs-class is a semantic change consumers outside the assembly
    // see without any compiler error
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type Shape =
                    | Circle of radius: float
                    | Square of side: float
                """
        )
    )

[<Fact>]
let ``FR0016: a union over 32 bytes, or one the file boxes or locks, stays a class`` () =
    // a struct union lays every case's fields side by side: three decimal
    // cases are 48 bytes plus the tag, copied on every pass (CR0081's cap)
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type private Amount =
                    | Eur of eur: decimal
                    | Usd of usd: decimal
                    | Gbp of gbp: decimal
                """
        )
    )

    let typed (source: string) =
        let tree, sourceText, check = parseAndCheck source
        StructDu.findWith (Some check) true false tree sourceText

    Assert.Empty(
        typed (
            fsharp
                """
                module Test
                type private Shape =
                    | Circle of radius: float
                    | Square of side: float
                let private key (s: Shape) = (box s).GetHashCode()
                """
        )
    )

    Assert.Empty(
        typed (
            fsharp
                """
                module Test
                type private Shape =
                    | Circle of radius: float
                    | Square of side: float
                let private gate (s: Shape) (f: unit -> int) = lock s f
                """
        )
    )

    Assert.NotEmpty(
        typed (
            fsharp
                """
                module Test
                type private Shape =
                    | Circle of radius: float
                    | Square of side: float
                let private area (s: Shape) =
                    match s with
                    | Circle r -> r * r
                    | Square a -> a * a
                """
        )
    )

[<Fact>]
let ``a union in an internal module is contained`` () =
    assertStructDu
        (fsharp
            """
            module internal Test
            type Shape =
                | Circle of radius: float
                | Square of side: float
            """)
        (fsharp
            """
            module internal Test
            [<Struct>]
            type Shape =
                | Circle of radius: float
                | Square of side: float
            """)

[<Fact>]
let ``a public union is offered under api changes`` () =
    let source =
        fsharp
            """
            module Test
            type Shape =
                | Circle of radius: float
                | Square of side: float
            """

    assertPatchedStructDu
        (structDuWithApiChangesIn source)
        source
        (fsharp
            """
            module Test
            [<Struct>]
            type Shape =
                | Circle of radius: float
                | Square of side: float
            """)

[<Fact>]
let ``a private representation does not make a public union contained`` () =
    // the cases are hidden but the type itself is still public
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type Shape =
                    private
                    | Circle of radius: float
                    | Square of side: float
                """
        )
    )

[<Fact>]
let ``string fields are not small value types`` () =
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type private T =
                    | A of string
                    | B of int
                """
        )
    )

[<Fact>]
let ``recursive union is excluded by the whitelist`` () =
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type private Tree =
                    | Leaf of int
                    | Node of Tree
                """
        )
    )

[<Fact>]
let ``two cases with unnamed fields are excluded`` () =
    // compiled ItemN names would collide in a struct union
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type private T =
                    | A of int
                    | B of float
                """
        )
    )

[<Fact>]
let ``existing attributes are left alone`` () =
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                [<Struct>]
                type private T =
                    | A of a: int
                    | B of b: float
                """
        )
    )

[<Fact>]
let ``all-nullary union is not suggested`` () =
    Assert.Empty(
        structDuIn (
            fsharp
                """
                module Test
                type private T =
                    | A
                    | B
                """
        )
    )

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

// --- verbatim patterns. `@"..."` is how F# writes regexes, so the rule
// --- reads verbatim literals as well as plain ones.

[<Fact>]
let ``a verbatim literal pattern simplifies like a plain one`` () =
    assertRegexFix
        (fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (s: string) = Regex.IsMatch(s, @"^abc")
            """)
        """s.StartsWith("abc", System.StringComparison.Ordinal)"""

[<Fact>]
let ``a verbatim pattern hoists out of a loop keeping its own spelling`` () =
    // the binding must re-emit the source text: re-quoting the decoded value
    // would turn `@"\d+"` into the invalid `"\d+"`
    match
        regexIn (
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let f (xs: string list) =
                    for x in xs do
                        if Regex.IsMatch(x, @"\d+") then ()
                """
        )
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
        """s.StartsWith("abc", System.StringComparison.Ordinal)"""

[<Fact>]
let ``an ignored async call result is flagged`` () =
    // the real fire-and-forget bug is a direct call ignored, not a named
    // binding: `saveAsync user |> ignore`
    let suggestions =
        discardedAsyncIn (
            fsharp
                """
                let save (n: int) : Async<unit> = async { return () }
                let f () = save 1 |> ignore
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("save", s.Name)
    | other -> failwithf "Expected exactly one ignored-call suggestion, got %A" other

[<Fact>]
let ``direct ignore of a call result is flagged`` () =
    let suggestions =
        discardedAsyncIn (
            fsharp
                """
                let save (n: int) : Async<unit> = async { return () }
                let f () = ignore (save 1)
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("save", s.Name)
    | other -> failwithf "Expected exactly one direct-ignore-call suggestion, got %A" other

[<Fact>]
let ``a partially applied async function is a different mistake`` () =
    // `save2 1` is a FUNCTION, not an Async — this rule stays quiet
    Assert.Empty(
        discardedAsyncIn (
            fsharp
                """
                let save2 (a: int) (b: int) : Async<unit> = async { return () }
                let f () = save2 1 |> ignore
                """
        )
    )

[<Fact>]
let ``a piped construction of the async is flagged too`` () =
    let suggestions =
        discardedAsyncIn (
            fsharp
                """
                let makeAsync (n: int) : Async<unit> = async { return () }
                let f () = 1 |> makeAsync |> ignore
                """
        )

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
            fsharp
                """
                module internal M

                type Shape =
                    | Box of side: int
                    | Ball of radius: int

                """
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
    // `messageStream.AbandonMessage token |> ignore`
    let source =
        fsharp
            """
            module Test
            type IStream =
                abstract AbandonMessage: System.Guid -> Async<unit>
            let f (stream: IStream) (token: System.Guid) =
                stream.AbandonMessage token |> ignore
            """

    match discardedAsyncIn source with
    | [ s ] ->
        Assert.Equal("AbandonMessage", s.Name)
        Assert.False s.IsValueTask
    | other -> failwithf "Expected one discarded Async, got %A" other

[<Fact>]
let ``FR0017: a ValueTask discarded with ignore loses its outcome`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            type ITransport =
                abstract shutdown: unit -> ValueTask
            let f (t: ITransport) =
                t.shutdown() |> ignore
            """

    match discardedAsyncIn source with
    | [ s ] ->
        Assert.Equal("shutdown", s.Name)
        Assert.True s.IsValueTask
    | other -> failwithf "Expected one discarded ValueTask, got %A" other

    match
        discardedAsyncIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (vt: ValueTask<int>) = ignore vt
                """
        )
    with
    | [ s ] -> Assert.True s.IsValueTask
    | other -> failwithf "Expected one discarded ValueTask value, got %A" other

    // a Task is hot and observable through its own machinery: not this rule
    Assert.Empty(
        discardedAsyncIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (t: Task<int>) = t |> ignore
                """
        )
    )

    // a unit-returning shutdown is nothing to discard
    Assert.Empty(
        discardedAsyncIn (
            fsharp
                """
                module Test
                type ITransport =
                    abstract shutdown: unit -> unit
                let f (t: ITransport) = t.shutdown() |> ignore
                """
        )
    )

[<Fact>]
let ``a regex hoisted from under an #if lands under the same #if`` () =
    let source =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (xs: string list) =
            #if !FOO
                for x in xs do
                    if Regex.IsMatch(x, "^a+$") then printfn "%s" x
            #endif
            """

    match
        regexIn source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistFromLoop)
    with
    | [ s ] ->
        let inserted =
            s.Edits
            |> List.pick (fun (_, original, text) -> if original = "" then Some text else None)

        Assert.StartsWith("#if !FOO\nlet private ", inserted)

        Assert.Contains(
            fsharp
                """

                #endif

                """,
            inserted
        )
    | other -> failwithf "Expected one hoist suggestion, got %A" other

// ---- FR0149 UnhandledStart ----

let private unhandledStartsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AsyncIgnore.findUnhandledStart tree sourceText checkResults

[<Fact>]
let ``FR0149: a started computation with no handler is flagged`` () =
    // a listener loop: one throw from the loop body ends it silently
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    async {
                        while true do
                            let! _ = work ()
                            ()
                    }
                    |> Async.Start
                """
        )
    with
    | [ s ] -> Assert.Equal("Async.Start", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a body wrapped in try-with is handled`` () =
    Assert.Empty(
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    async {
                        try
                            let! _ = work ()
                            ()
                        with ex -> printfn "%s" ex.Message
                    }
                    |> Async.Start
                """
        )
    )

[<Fact>]
let ``FR0149: Async Catch counts only once both Choice arms consume it`` () =
    // producing the Choice is not handling it
    let source (tail: string) =
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                async {
                    let! outcome = work () |> Async.Catch

            """
        + tail
        + "\n    }\n    |> Async.Start"

    Assert.Empty(
        unhandledStartsIn (
            source (
                fsharp
                    """
                            match outcome with
                            | Choice1Of2 _ -> ()
                            | Choice2Of2 ex -> printfn "%s" ex.Message
                    """
            )
        )
    )

    Assert.NotEmpty(unhandledStartsIn (source "        ignore outcome"))

[<Fact>]
let ``FR0149: a one-hop binding in the same file is read`` () =
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    let listener =
                        async {
                            let! _ = work ()
                            ()
                        }

                    Async.Start listener
                """
        )
    with
    | [ s ] -> Assert.Equal("Async.Start", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a computation this file cannot see stays quiet`` () =
    Assert.Empty(unhandledStartsIn "let run (comp: Async<unit>) = Async.Start comp")

[<Fact>]
let ``FR0149: StartImmediate is the same shape and the token form is read`` () =
    match
        unhandledStartsIn (
            fsharp
                """
                open System.Threading
                let work () = async { return 1 }
                let run (token: CancellationToken) =
                    Async.StartImmediate(
                        async {
                            let! _ = work ()
                            ()
                        },
                        token
                    )
                """
        )
    with
    | [ s ] -> Assert.Equal("Async.StartImmediate", s.Starter)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a looping body says where the handler goes`` () =
    // a listener that polls forever: a handler around the whole
    // computation still ends it on the first failure
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    async {
                        while true do
                            let! _ = work ()
                            ()
                    }
                    |> Async.Start
                """
        )
    with
    | [ s ] -> Assert.True(s.LoopsInBody)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a straight-line body has no such choice`` () =
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                """
        )
    with
    | [ s ] -> Assert.False(s.LoopsInBody)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try around the start is called out as not covering it`` () =
    // `try async { failwith "y" } |> Async.Start with _ -> ()`
    // terminates the process — the handler is on this thread, the work is not
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    try
                        async {
                            let! _ = work ()
                            ()
                        }
                        |> Async.Start
                    with ex -> printfn "%s" ex.Message
                """
        )
    with
    | [ s ] -> Assert.True(s.WrappedInTry)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a start with no try around it says nothing about one`` () =
    match
        unhandledStartsIn (
            fsharp
                """
                let work () = async { return 1 }
                let run () =
                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                """
        )
    with
    | [ s ] -> Assert.False(s.WrappedInTry)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try wrapping only the start moves its handler inside`` () =
    let source =
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                try
                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
            """

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement

            Assert.Contains(
                fsharp
                    """
                        async {
                            try
                                let! _ = work ()
                                ()
                            with e ->
                                printfn "%s" e.Message
                        }
                        |> Async.Start
                    """,
                patched
            )

            assertTypechecks "Patched source" patched
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: several handler clauses travel verbatim`` () =
    // an Async.Catch spelling cannot carry a typed clause or a guard;
    // moving the try keeps every clause as written
    let source =
        fsharp
            """
            open System
            let work () = async { return 1 }
            let run () =
                try
                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                with
                | :? OperationCanceledException -> ()
                | e when e.Message = "x" -> printfn "x"
                | e -> printfn "%s" e.Message
            """

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement
            Assert.Contains(":? OperationCanceledException", patched)
            Assert.Contains("e when e.Message = \"x\"", patched)
            assertTypechecks "Patched source" patched
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a try holding more than the start offers no move`` () =
    // the handler may have been meant for the other statement, so the
    // rule will not decide that for the author
    let source =
        fsharp
            """
            let work () = async { return 1 }
            let setup () = ()
            let run () =
                try
                    setup ()

                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
            """

    match unhandledStartsIn source with
    | [ s ] ->
        Assert.True(s.WrappedInTry)
        Assert.True(s.TryFix.IsNone, "a try holding other statements is not the author's handler for this start alone")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a start carrying a cancellation token keeps its argument`` () =
    // the tupled form would lose the token in the rewrite, so no fix
    let source =
        fsharp
            """
            open System.Threading
            let work () = async { return 1 }
            let run (token: CancellationToken) =
                try
                    Async.Start(
                        async {
                            let! _ = work ()
                            ()
                        },
                        token
                    )
                with e ->
                    printfn "%s" e.Message
            """

    match unhandledStartsIn source with
    | [ s ] -> Assert.True(s.TryFix.IsNone)
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0015: an open below the declaration does not license a bare Regex above it`` () =
    // the hoisted binding lands above `f`; an `open System.Text.RegularExpressions`
    // further down the module is no help there, and the bare `Regex` would
    // not resolve - the qualified spelling needs no open at all
    let below =
        fsharp
            """
            module Test
            let f (lines: string list) =
                for line in lines do
                    if System.Text.RegularExpressions.Regex.IsMatch(line, "a+b") then ()
            open System.Text.RegularExpressions
            let g (s: string) = Regex.IsMatch(s, "x")
            """

    let tree, source = parse below

    let hoists =
        RegexUsage.find tree source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistFromLoop)

    match hoists with
    | [ s ] -> Assert.Empty s.Edits
    | other -> failwithf "Expected one fix-less hoist note, got %A" other

    let above =
        fsharp
            """
            module Test
            open System.Text.RegularExpressions
            let f (lines: string list) =
                for line in lines do
                    if Regex.IsMatch(line, "a+b") then ()
            """

    let tree, source = parse above

    match
        RegexUsage.find tree source
        |> List.filter (fun s -> s.Kind = RegexUsage.RegexSuggestionKind.HoistFromLoop)
    with
    | [ s ] -> Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one hoist with a fix, got %A" other
