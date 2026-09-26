/// Performance guardrail: every analyzer runs against a large synthetic
/// file, timed individually after a warmup round. A report with per-rule
/// timings lands in the temp directory; the assertion only catches
/// pathological blowups (quadratic scans and the like), not CI jitter.
/// In the "ProjectSources" collection: some tests set the process-wide
/// analysis scope (Scope.set), which must not run beside another test's.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.PerfTests

open System
open System.Diagnostics
open System.IO
open System.Reflection
open Xunit
open FSharp.Analyzers.SDK
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Refactor.Tests.Parsing

/// A block exercising many syntactic shapes at once; repeated with unique
/// suffixes to build a file of realistic size.
let private blockTemplate (i: int) =
    $"""
type RecordN{i} = {{ AlphaN{i}: int; BetaN{i}: string option }}

type UnionN{i} =
    | CaseAN{i} of int
    | CaseBN{i}
    | CaseCN{i}

let funcAN{i} (x: int option) =
    match x with
    | Some v -> v * {i} + 1
    | None -> 0

let funcBN{i} (items: string list) (needle: string) =
    let mutable count = 0

    for item in items do
        let bonus = {i} + 1

        if item.Contains needle then
            count <- count + item.Length + bonus

    count

let funcCN{i} (r: RecordN{i}) =
    match r.BetaN{i} with
    | Some s -> sprintf "%%s-%%d" s r.AlphaN{i}
    | None -> string r.AlphaN{i}

let funcDN{i} (u: UnionN{i}) =
    match u with
    | CaseAN{i} n -> n
    | _ -> {i}

let funcEN{i} (xs: int[]) =
    try
        xs |> Array.map (fun v -> v + {i}) |> Array.sum
    with _ ->
        0
"""

let private bigSource =
    "module PerfCorpus\n" + (Seq.init 60 blockTemplate |> String.concat "\n")

[<Fact>]
let ``every analyzer stays fast on a large file`` () =
    let sourceText = SourceText.ofString bigSource
    // a dedicated checker: analyzers may read the typed tree
    let checker = FSharpChecker.Create(keepAssemblyContents = true)

    task {
        let! options, _ =
            checker.GetProjectOptionsFromScript("Test.fsx", sourceText, assumeDotNetFramework = false)
            |> Async.StartImmediateAsTask

        let! projectResults =
            checker.ParseAndCheckProject options |> Async.StartImmediateAsTask

        let! parseResults, answer =
            checker.ParseAndCheckFileInProject("Test.fsx", bigSource.GetHashCode(), sourceText, options)
            |> Async.StartImmediateAsTask

        let checkResults =
            match answer with
            | FSharpCheckFileAnswer.Succeeded r -> r
            | FSharpCheckFileAnswer.Aborted -> failwith "typechecking aborted"

        let context: CliContext =
            {
                FileName = "Test.fsx"
                SourceText = sourceText
                ParseFileResults = parseResults
                CheckFileResults = checkResults
                TypedTree = checkResults.ImplementationFile
                CheckProjectResults = projectResults
                ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
                AnalyzerIgnoreRanges = Map.empty
            }

        let analyzers =
            [
                for t in typeof<FSharp.Refactor.RedundantParens.Suggestion>.Assembly.GetTypes() do
                    for m in t.GetMethods(BindingFlags.Static ||| BindingFlags.Public) do
                        if m.GetCustomAttributes(typeof<CliAnalyzerAttribute>, false).Length > 0 then
                            m
            ]

        let runOne (m: MethodInfo) =
            m.Invoke(null, [| box context |]) :?> Async<Message list>
            |> Async.RunSynchronously

        // warmup: JIT + the shared AstIndex memoization
        for m in analyzers do
            runOne m |> ignore

        let timings =
            [
                for m in analyzers do
                    let sw = Stopwatch.StartNew()
                    let messages = runOne m
                    sw.Stop()
                    m.Name, sw.Elapsed.TotalMilliseconds, messages.Length
            ]
            |> List.sortByDescending (fun (_, ms, _) -> ms)

        let report =
            [
                yield $"lines: {sourceText.GetLineCount()}, analyzers: {analyzers.Length}"
                for name, ms, hits in timings do
                    yield $"%-45s{name} %8.1f{ms} ms  %d{hits} hits"
            ]
            |> String.concat "\n"

        do! File.WriteAllTextAsync(Path.Combine(Path.GetTempPath(), "fsref-perf.txt"), report)

        let runTail () =
            let slow = timings |> List.filter (fun (_, ms, _) -> ms > 2000.0)

            Assert.True(
                slow.IsEmpty,
                "Pathologically slow analyzers:\n"
                + String.concat "\n" (slow |> List.map (fun (n, ms, _) -> $"%s{n}: %.0f{ms} ms"))
            )

        runTail ()
    }
    :> System.Threading.Tasks.Task

// ---- FR0106 SubstringSpan ----

let private substringSpansIn (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    FSharp.Refactor.SubstringSpan.find tree sourceText checkResults

[<Fact>]
let ``a Substring fed to Parse becomes AsSpan`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

    match substringSpansIn source with
    | [ sug ] ->
        let patched = applyEdit source sug.Range "AsSpan"
        Assert.Contains("Int32.Parse(s.AsSpan(6, 5))", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one AsSpan suggestion, got %A" other

[<Fact>]
let ``FR0106: a file that does not open System cannot see AsSpan and keeps its Substring`` () =
    // the tool's own SprintfInterpolation.fs opened only
    // System.Text.RegularExpressions: the swept `.AsSpan` did not resolve
    let source =
        "module Test\nopen System.Text.RegularExpressions\nlet f (fmt: string) (cursor: int) =\n    let builder = System.Text.StringBuilder()\n    builder.Append(fmt.Substring cursor) |> ignore\n    builder.ToString()"

    Assert.Empty(substringSpansIn source)
    // with the open, the same text is fixed and typechecks
    let opened = source.Replace("open System.Text.RegularExpressions", "open System")

    match substringSpansIn opened with
    | [ sug ] -> Assert.True(typechecksCleanly (applyEdit opened sug.Range "AsSpan"))
    | other -> failwithf "Expected exactly one AsSpan suggestion, got %A" other

[<Fact>]
let ``a Substring fed to TryParse becomes AsSpan`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) =\n    match Int32.TryParse(s.Substring 6) with\n    | true, v -> v\n    | _ -> 0"

    match substringSpansIn source with
    | [ sug ] ->
        let patched = applyEdit source sug.Range "AsSpan"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one TryParse suggestion, got %A" other

[<Fact>]
let ``a bound Substring escapes and is left alone`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\nlet f (s: string) =\n    let part = s.Substring(6, 5)\n    Int32.Parse part"
    )

[<Fact>]
let ``a parser without a span overload is left alone`` () =
    // the availability gate: no ReadOnlySpan<char> overload proven in the
    // compilation, no suggestion — this is how netstandard2.0/net4x
    // compilations stay untouched without any TFM sniffing
    Assert.Empty(
        substringSpansIn
            "module Test\ntype Money =\n    static member Parse(text: string) = text.Length\nlet f (s: string) = Money.Parse(s.Substring(6, 5))"
    )

[<Fact>]
let ``a Substring on a non-string receiver is left alone`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\ntype Doc(t: string) =\n    member _.Substring(a: int, b: int) = t.Substring(a, b)\nlet f (d: Doc) = Int32.Parse(d.Substring(6, 5))"
    )

[<Fact>]
let ``byref TryParse spelling is deliberately untouched`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\nlet f (s: string) =\n    let mutable r = 0\n    Int32.TryParse(s.Substring(6, 5), &r) |> ignore\n    r"
    )

[<Fact>]
let ``a Substring fed to StringBuilder.Append or TextWriter.Write becomes AsSpan`` () =
    let source =
        "module Test\nopen System\nopen System.IO\nopen System.Text\nlet f (s: string) (sb: StringBuilder) (w: TextWriter) (sw: StringWriter) =\n    sb.Append(s.Substring(6, 5)) |> ignore\n    w.Write(s.Substring 6)\n    sw.WriteLine(s.Substring(0, 3))\n    Console.Write(s.Substring 1)\n    sb.Append(s.Substring(6, 5)).Append(s.Substring 2) |> ignore"

    let found = substringSpansIn source
    // Console.Write has no span overload; the chained Append has two
    Assert.Equal<string list>(
        [ "Append"; "Write"; "WriteLine"; "Append"; "Append" ],
        found |> List.map (fun s -> s.ParserName)
    )

    Assert.Equal<string list>(
        [ "appends"; "writes"; "writes"; "appends"; "appends" ],
        found |> List.map (fun s -> s.Verb)
    )

    let patched =
        found
        |> List.sortByDescending (fun s -> s.Range.StartLine, s.Range.StartColumn)
        |> List.fold (fun src s -> applyEdit src s.Range "AsSpan") source

    Assert.Contains("sb.Append(s.AsSpan(6, 5)) |> ignore", patched)
    Assert.Contains("w.Write(s.AsSpan 6)", patched)
    Assert.Contains("sw.WriteLine(s.AsSpan(0, 3))", patched)
    Assert.Contains("Console.Write(s.Substring 1)", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a user type's Parse with a span overload of its own is not assumed identical either`` () =
    // MyType.Parse(string) and MyType.Parse(ReadOnlySpan<char>) are the
    // author's two methods; only the BCL's parsers are one implementation
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\ntype Money =\n    static member Parse(text: string) = text.Length\n    static member Parse(text: ReadOnlySpan<char>) = -text.Length\nlet f (s: string) = Money.Parse(s.Substring(6, 5))"
    )

    // while Guid, DateTime and BigInteger still qualify
    Assert.Equal(
        3,
        (substringSpansIn
            "module Test\nopen System\nlet f (s: string) = Guid.Parse(s.Substring 1), DateTime.Parse(s.Substring 2), Numerics.BigInteger.Parse(s.Substring 3)")
            .Length
    )

[<Fact>]
let ``a user type's Append with a span overload of its own is not assumed identical`` () =
    Assert.Empty(
        substringSpansIn
            "module Test\nopen System\ntype Sink() =\n    member _.Append(s: string) = s.Length\n    member _.Append(s: ReadOnlySpan<char>) = -s.Length\nlet f (s: string) (k: Sink) = k.Append(s.Substring(6, 5))"
    )

// ---- FR0166 PrefixCompare ----

let private prefixComparesIn (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    FSharp.Refactor.PrefixCompare.find true tree sourceText checkResults

let private patchedWith (source: string) (found: FSharp.Refactor.PrefixCompare.Suggestion list) =
    found
    |> List.sortByDescending (fun s -> s.Range.StartLine, s.Range.StartColumn)
    |> List.fold (fun src s -> applyEdit src s.Range s.ReplacementText) source

[<Fact>]
let ``FR0166: a slice compared with a literal is StartsWith or EndsWith, exactly`` () =
    let source =
        "module Test\nlet f (s: string) =\n    let a = s[..5] = \"ORDER-\"\n    let b = s.[0..2] <> \"ORD\"\n    let c = s[s.Length - 3 ..] = \"MED\"\n    let d = \"MED\" = s[s.Length - 3 ..]\n    a, b, c, d"

    let found = prefixComparesIn source
    Assert.Equal(4, found.Length)
    Assert.True(found |> List.forall (fun s -> s.Exact))

    Assert.Equal<string list>(
        [
            "s.StartsWith(\"ORDER-\", System.StringComparison.Ordinal)"
            "not (s.StartsWith(\"ORD\", System.StringComparison.Ordinal))"
            "s.EndsWith(\"MED\", System.StringComparison.Ordinal)"
            "s.EndsWith(\"MED\", System.StringComparison.Ordinal)"
        ],
        found |> List.map (fun s -> s.ReplacementText)
    )

    let patched = patchedWith source found
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0166: a module mutable reset by a call between the guard and the cut - directly, through a chain or a byref - is not exact; a reader loop is``
    ()
    =
    let source =
        "module Test\nmodule M =\n    let mutable s = \"ORDER-1\"\n    let clear () = s <- \"\"\n    let reset () = clear ()\n    let bump (r: byref<string>) = r <- \"\"\n    let resetRef () = bump &s\nlet direct () = if M.s.Length >= 6 then (M.clear (); M.s.Substring(0, 6) = \"ORDER-\") else false\nlet chained () = if M.s.Length >= 6 then (M.reset (); M.s.Substring(0, 6) = \"ORDER-\") else false\nlet byRef () = if M.s.Length >= 6 then (M.resetRef (); M.s.Substring(0, 6) = \"ORDER-\") else false\nlet reader (lines: string list) =\n    let mutable line = List.head lines\n    let mutable n = 0\n    while not (isNull line) do\n        if line.Length >= 6 && line.Substring(0, 6) = \"ORDER-\" then n <- n + 1\n        line <- null\n    n\nmodule Stats =\n    let mutable line = 0\nlet sameName (lines: string list) =\n    let mutable line = List.head lines\n    if line.Length >= 6 && (Stats.line <- Stats.line + 1; true) && line.Substring(0, 6) = \"ORDER-\" then 1 else 0\nmodule P =\n    let mutable s = \"ORDER-1\"\n    let setS (v: string) = s <- v\n    let resetPipe () = \"\" |> setS\nlet piped () = if P.s.Length >= 6 then (P.resetPipe (); P.s.Substring(0, 6) = \"ORDER-\") else false"

    // another scope's `line` written between is another value (exact); a
    // setter reached through a pipe is a reset (not exact)
    let found = prefixComparesIn source |> List.sortBy (fun s -> s.Range.StartLine)
    Assert.Equal<int list>([ 8; 9; 10; 15; 22; 27 ], found |> List.map (fun s -> s.Range.StartLine))
    Assert.Equal<bool list>([ false; false; false; true; true; false ], found |> List.map (fun s -> s.Exact))

[<Fact>]
let ``FR0166: a Substring compared with a literal is exact only under a length guard`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) (flag: bool) =\n    let a = s.Substring(0, 6) = \"ORDER-\"\n    let b = s.Length >= 6 && s.Substring(0, 6) = \"ORDER-\" && flag\n    let c = if s.Length > 5 then s.Substring(0, 6) <> \"ORDER-\" else false\n    let d = if s.Length < 3 then false else s.Substring(s.Length - 3) = \"MED\"\n    let e = s.Substring(0, 6) = \"ORDER-\" && s.Length >= 6\n    let g = 6 <= s.Length && s.Substring(0, 6) = \"ORDER-\"\n    a, b, c, d, e, g"

    let found = prefixComparesIn source
    Assert.Equal(6, found.Length)
    // a: bare; b, c, d, g: guarded before the cut; e: guarded AFTER it
    Assert.Equal<bool list>([ false; true; true; true; false; true ], found |> List.map (fun s -> s.Exact))
    Assert.Equal("s.StartsWith(\"ORDER-\", StringComparison.Ordinal)", found.Head.ReplacementText)
    Assert.Equal("not (s.StartsWith(\"ORDER-\", StringComparison.Ordinal))", found.[2].ReplacementText)
    Assert.Equal("s.EndsWith(\"MED\", StringComparison.Ordinal)", found.[3].ReplacementText)

    let patched = patchedWith source found
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0166: an else branch is guarded only when the failed condition proves Length at least the cut`` () =
    // the else branch of `if s.Length < k` knows Length >= k: exact only
    // for k >= 6; `<= k` gives Length >= k + 1
    let source =
        "module Test\nlet f (s: string) =\n    let a = if s.Length < 3 then false else s.Substring(0, 6) = \"ORDER-\"\n    let b = if s.Length <= 3 then false else s.Substring(0, 6) = \"ORDER-\"\n    let c = if 3 > s.Length then false else s.Substring(0, 6) = \"ORDER-\"\n    let d = if 3 >= s.Length then false else s.Substring(0, 6) = \"ORDER-\"\n    let e = if s.Length < 6 then false else s.Substring(0, 6) = \"ORDER-\"\n    let g = if s.Length <= 5 then false else s.Substring(0, 6) = \"ORDER-\"\n    let h = if 6 > s.Length then false else s.Substring(0, 6) = \"ORDER-\"\n    let i = if 5 >= s.Length then false else s.Substring(0, 6) = \"ORDER-\"\n    let j = if s.Length <= 4 then false else s.Substring(0, 6) = \"ORDER-\"\n    a, b, c, d, e, g, h, i, j"

    Assert.Equal<bool list>(
        [ false; false; false; false; true; true; true; true; false ],
        prefixComparesIn source |> List.map (fun s -> s.Exact)
    )

[<Fact>]
let ``FR0166: a literal of another length, a computed right-hand side, another receiver's Length and a non-string are left alone``
    ()
    =
    Assert.Empty(
        prefixComparesIn
            "module Test\ntype Doc(t: string) =\n    member _.Substring(a: int, b: int) = t.Substring(a, b)\n    member _.Length = t.Length\nlet f (s: string) (t: string) (d: Doc) (lit: string) =\n    let a = s.Substring(0, 3) = \"ab\"\n    let b = s[..2] = lit\n    let c = s.Substring(t.Length - 3) = \"abc\"\n    let d = d.Substring(0, 3) = \"abc\"\n    let e = s[1..3] = \"abc\"\n    let g = s.Substring(0, 3) = $\"ab{1}\"\n    a, b, c, d, e, g"
    )


[<Fact>]
let ``FR0166: a guard says nothing about a receiver rebound below it, and a slice is exact only under tolerant slicing``
    ()
    =
    let source =
        "module Test\nopen System\nlet f (s: string) (xs: string list) =\n    let a = if s.Length >= 6 then xs |> List.map (fun s -> s.Substring(0, 6) = \"ORDER-\") else []\n    let b = if s.Length >= 6 then (let t = s.Trim() in s.Substring(0, 6) = \"ORDER-\") else false\n    let c = if s.Length >= 6 then (let s = s.Trim() in s.Substring(0, 6) = \"ORDER-\") else false\n    let d = match xs with | s :: _ when s.Length >= 6 && s.Substring(0, 6) = \"ORDER-\" -> true | _ -> false\n    a, b, c, d"

    // a: a lambda rebinds `s`; b: a `let` of another name is fine; c: a
    // `let` rebinding `s`; d: a match arm's own guard, same binding
    Assert.Equal<bool list>([ false; true; false; true ], prefixComparesIn source |> List.map (fun s -> s.Exact))

    // under FSharp.Core 4 a slice throws like a Substring: exact only guarded
    let tree, sourceText, check =
        FSharp.Refactor.Tests.Parsing.parseAndCheck
            "module Test\nlet f (s: string) = s[..5] = \"ORDER-\", (s.Length > 5 && s[..5] = \"ORDER-\")"

    Assert.Equal<bool list>(
        [ false; true ],
        FSharp.Refactor.PrefixCompare.find false tree sourceText check
        |> List.map (fun s -> s.Exact)
    )

[<Fact>]
let ``FR0166: a guard proves nothing about a mutable receiver or a getter read twice`` () =
    // `s <- ""` between the guard and the cut, or a property answering a
    // new string per call: the Substring throws where StartsWith answers
    // false. An immutable record field is the same string both times
    let source =
        "module Test\ntype Doc = { Name: string }\ntype Box() =\n    let mutable current = \"ORDER-1\"\n    member _.Text = current\n    member _.Clear() = current <- \"\"\nlet f (s0: string) (b: Box) (d: Doc) =\n    let mutable s = s0\n    let a = if s.Length >= 6 then (s <- \"\"; s.Substring(0, 6) = \"ORDER-\") else false\n    let c = if b.Text.Length >= 6 then (b.Clear(); b.Text.Substring(0, 6) = \"ORDER-\") else false\n    let e = d.Name.Length >= 6 && d.Name.Substring(0, 6) = \"ORDER-\"\n    a, c, e"

    Assert.True(typechecksCleanly source)
    Assert.Equal<bool list>([ false; false; true ], prefixComparesIn source |> List.map (fun s -> s.Exact))

    // a `let mutable` not written between the guard and the cut is one
    // string there: the reader loop, `&&` over a local, a module mutable with
    // nothing running between; a module mutable a call between may reset
    let reader =
        "module Test\nopen System.IO\nlet mutable current = \"ORDER-1\"\nlet reset () = current <- \"\"\nlet read (r: TextReader) =\n    let mutable line = r.ReadLine()\n    let mutable n = 0\n    while not (isNull line) do\n        if line.Length >= 6 then\n            if line.Substring(0, 6) = \"ORDER-\" then n <- n + 1\n        line <- r.ReadLine()\n    n\nlet chain (s0: string) =\n    let mutable s = s0\n    s <- s.Trim()\n    s.Length >= 6 && s.Substring(0, 6) = \"ORDER-\"\nlet moduleValue () = current.Length >= 6 && current.Substring(0, 6) = \"ORDER-\"\nlet moduleValueReset () = current.Length >= 6 && (reset (); true) && current.Substring(0, 6) = \"ORDER-\""

    Assert.True(typechecksCleanly reader)
    Assert.Equal<bool list>([ true; true; true; false ], prefixComparesIn reader |> List.map (fun s -> s.Exact))

    // writes the window must see: the rest of an `if` condition after the
    // guard, a byref taken, a `while` between the guard and the cut whose
    // later round writes, and a class `let mutable` a method call resets
    let windows =
        "module Test\nlet clear (s: byref<string>) = s <- \"\"\nlet inCondition () =\n    let mutable s = \"ORDER-1\"\n    if s.Length >= 6 && (s <- \"\"; true) then s.Substring(0, 6) = \"ORDER-\" else false\nlet byrefTaken () =\n    let mutable s = \"ORDER-1\"\n    s.Length >= 6 && (clear &s; true) && s.Substring(0, 6) = \"ORDER-\"\nlet loop () =\n    let mutable s = \"ORDER-1\"\n    let mutable n = 0\n    if s.Length >= 6 then\n        let mutable i = 0\n        while i < 2 do\n            if s.Substring(0, 6) = \"ORDER-\" then n <- n + 1\n            s <- \"\"\n            i <- i + 1\n    n\ntype C() =\n    let mutable fld = \"ORDER-1\"\n    member this.Reset() = fld <- \"\"\n    member this.A = fld.Length >= 6 && (this.Reset(); true) && fld.Substring(0, 6) = \"ORDER-\"\n    member this.B = fld.Length >= 6 && fld.Substring(0, 6) = \"ORDER-\""

    Assert.True(typechecksCleanly windows)

    Assert.Equal<bool list>(
        [ false; false; false; false; true ],
        prefixComparesIn windows |> List.map (fun s -> s.Exact)
    )

    // a get-only `member val` and a BCL getter read one string; a settable
    // one and a byref's target may change between the guard and the cut
    let getters =
        "module Test\nopen System.IO\ntype Box() =\n    member val Title = \"ORDER-1\" with get\n    member val Mut = \"ORDER-1\" with get, set\n    member this.A = this.Title.Length >= 6 && this.Title.Substring(0, 6) = \"ORDER-\"\n    member this.B = this.Mut.Length >= 6 && this.Mut.Substring(0, 6) = \"ORDER-\"\nlet f (fi: FileInfo) = fi.Name.Length >= 6 && fi.Name.Substring(0, 6) = \"ORDER-\"\nlet h (s: byref<string>) = if s.Length >= 6 then (s <- \"\"; s.Substring(0, 6) = \"ORDER-\") else false"

    Assert.True(typechecksCleanly getters)

    Assert.Equal<bool list>([ true; false; true; false ], prefixComparesIn getters |> List.map (fun s -> s.Exact))

    // an immutable module value is one string, qualified or not
    let moduleValue =
        "module Test\nmodule Config =\n    let Name = System.Environment.MachineName\nlet f () = Config.Name.Length >= 6 && Config.Name.Substring(0, 6) = \"ORDER-\""

    Assert.Equal<bool list>([ true ], prefixComparesIn moduleValue |> List.map (fun s -> s.Exact))

[<Fact>]
let ``FR0166: a dotted receiver is proven through its member's type`` () =
    let source =
        "module Test\ntype Doc = { Name: string; Size: int64 }\nlet f (d: Doc) = d.Name[..2] = \"abc\", d.Name.Substring(d.Name.Length - 3) = \"abc\""

    let found = prefixComparesIn source

    Assert.Equal<string list>(
        [
            "d.Name.StartsWith(\"abc\", System.StringComparison.Ordinal)"
            "d.Name.EndsWith(\"abc\", System.StringComparison.Ordinal)"
        ],
        found |> List.map (fun s -> s.ReplacementText)
    )

    Assert.True(typechecksCleanly (patchedWith source found))

// ---- FR0167 CharArrayCopy ----

let private charArrayCopiesIn (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    FSharp.Refactor.CharArrayCopy.find tree sourceText checkResults

[<Fact>]
let ``FR0167: a ToCharArray copy read once by a loop or an Array function walks the string`` () =
    let source =
        "module Test\nopen System\nlet f (s: string) (name: string) =\n    let mutable n = 0\n    for c in s.ToCharArray() do\n        if c = '-' then n <- n + 1\n    let a = Array.exists Char.IsDigit (s.ToCharArray())\n    let b = s.Trim().ToCharArray() |> Array.forall (fun c -> c <> ' ')\n    name.ToCharArray() |> Array.iteri (fun i c -> n <- n + i + int c)\n    n, a, b"

    let found = charArrayCopiesIn source

    Assert.Equal<string list>(
        [ "for"; "String.exists"; "String.forall"; "String.iteri" ],
        found |> List.map (fun s -> s.Consumer)
    )
    // the `for` throws on a null string on both sides; the String module
    // reads null as empty where the copy threw, so those are not exact
    Assert.Equal<bool list>([ true; false; false; false ], found |> List.map (fun s -> s.Exact))

    Assert.Equal<string list>(
        [
            "s"
            "String.exists Char.IsDigit s"
            "s.Trim() |> String.forall (fun c -> c <> ' ')"
            "name |> String.iteri (fun i c -> n <- n + i + int c)"
        ],
        found |> List.map (fun s -> s.ReplacementText)
    )

    let patched =
        found
        |> List.sortByDescending (fun s -> s.Range.StartLine, s.Range.StartColumn)
        |> List.fold (fun src s -> applyEdit src s.Range s.ReplacementText) source

    Assert.Contains("for c in s do", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0167: a bound copy, a sliced copy, a Seq or map consumer and a non-string receiver are left alone`` () =
    Assert.Empty(
        charArrayCopiesIn
            "module Test\nopen System\ntype Doc(t: string) =\n    member _.ToCharArray() = t.ToCharArray()\nlet f (s: string) (d: Doc) =\n    let chars = s.ToCharArray()\n    for c in chars do ignore c\n    for c in s.ToCharArray(1, 2) do ignore c\n    let a = s.ToCharArray() |> Seq.filter Char.IsDigit |> Seq.length\n    let b = Array.map Char.ToUpper (s.ToCharArray())\n    for c in d.ToCharArray() do ignore c\n    a, b"
    )

[<Fact>]
let ``FR0167: on FSharp.Core 9 an order-code check walks nonNull s and still throws on a null code`` () =
    // an order-code validator: `null.ToCharArray()` threw, while
    // `String.exists Char.IsDigit null` answers false - a missing code would
    // quietly fail (or pass) validation. `nonNull s` throws the same
    // NullReferenceException the copy did, so with it the sweep may apply
    let source =
        "module Test\nopen System\nlet f (code: string) (name: string) =\n    let mutable n = 0\n    let a = Array.exists Char.IsDigit (code.ToCharArray())\n    let b = code.Trim().ToCharArray() |> Array.forall (fun c -> c <> ' ')\n    name.ToCharArray() |> Array.iteri (fun i c -> n <- n + i + int c)\n    Array.iter (fun c -> n <- n + int c) (code.ToCharArray())\n    n, a, b"

    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    let found = FSharp.Refactor.CharArrayCopy.findWith true tree sourceText checkResults

    Assert.Equal<bool list>([ true; true; true; true ], found |> List.map (fun s -> s.Exact))

    Assert.Equal<string list>(
        [
            "String.exists Char.IsDigit (FSharp.Core.Operators.nonNull code)"
            "FSharp.Core.Operators.nonNull (code.Trim()) |> String.forall (fun c -> c <> ' ')"
            "FSharp.Core.Operators.nonNull name |> String.iteri (fun i c -> n <- n + i + int c)"
            "String.iter (fun c -> n <- n + int c) (FSharp.Core.Operators.nonNull code)"
        ],
        found |> List.map (fun s -> s.ReplacementText)
    )

    let patched =
        found
        |> List.sortByDescending (fun s -> s.Range.StartLine, s.Range.StartColumn)
        |> List.fold (fun src s -> applyEdit src s.Range s.ReplacementText) source

    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

    // below FSharp.Core 9 there is no nonNull: the bare String twin, editor only
    let older =
        FSharp.Refactor.CharArrayCopy.findWith false tree sourceText checkResults

    Assert.All(older, (fun s -> Assert.False s.Exact))
    Assert.Equal("String.exists Char.IsDigit code", older.Head.ReplacementText)

[<Fact>]
let ``FR0167: a project's own nonNull does not take the rewrite's`` () =
    // the type-provider SDK's shape: an AutoOpen helper named nonNull, here
    // one that reads null as empty. Another file of the project sees it
    // under the bare name, which one file's scan cannot rule out; a module
    // of the project's own named Operators takes `Operators.nonNull` (F#
    // tries every Operators in scope). The full name is FSharp.Core's
    let source =
        "module Test\nopen System\n[<AutoOpen>]\nmodule Helpers =\n    let nonNull (s: string) = if isNull s then \"\" else s\nmodule Operators =\n    let nonNull (s: string) = if isNull s then \"\" else s\nlet f (code: string) = Array.exists Char.IsDigit (code.ToCharArray())"

    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    match FSharp.Refactor.CharArrayCopy.findWith true tree sourceText checkResults with
    | [ s ] ->
        Assert.True s.Exact
        Assert.Equal("String.exists Char.IsDigit (FSharp.Core.Operators.nonNull code)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

        // and the name binds to FSharp.Core's, not to either helper
        let _, patchedText, patchedCheck =
            FSharp.Refactor.Tests.Parsing.parseAndCheck patched

        let line = patched.Split('\n').Length
        let lineText = patchedText.GetLineString(line - 1)
        let column = lineText.IndexOf "nonNull" + "nonNull".Length

        match
            patchedCheck.GetSymbolUseAtLocation(line, column, lineText, [ "FSharp"; "Core"; "Operators"; "nonNull" ])
        with
        | Some u -> Assert.StartsWith("Microsoft.FSharp.Core.Operators", u.Symbol.FullName)
        | None -> failwith "nonNull did not resolve"
    | other -> failwithf "Expected one finding, got %A" other

    // the premise: the qualified name throws on null as the copy did
    let (missing: string) = null

    Assert.Throws<System.NullReferenceException>(fun () ->
        String.exists System.Char.IsDigit (FSharp.Core.Operators.nonNull missing)
        |> ignore)
    |> ignore


// ---- the modern-framework gate the string rules share ----

[<Fact>]
let ``FR0106, FR0166 and FR0167 stay quiet in a legacy .NET Framework compilation`` () =
    // the same shapes fire against modern .NET above; against mscorlib the
    // char and span overloads of String are absent, so nothing is proven
    // and nothing fires — this is how netstandard2.0/net4x stay untouched.
    // Only Windows ships the .NET Framework reference assemblies a legacy
    // script compilation resolves; elsewhere the fixture cannot typecheck
    if OperatingSystem.IsWindows() then
        let source =
            "module Test\nopen System\nopen System.Text\nlet f (s: string) (sb: StringBuilder) =\n    sb.Append(s.Substring(6, 5)) |> ignore\n    let a = s.[..5] = \"ORDER-\"\n    let b = s.Length >= 6 && s.Substring(0, 6) = \"ORDER-\"\n    let mutable n = 0\n    for c in s.ToCharArray() do n <- n + int c\n    let d = Array.exists Char.IsDigit (s.ToCharArray())\n    Int32.Parse(s.Substring(0, 2)), a, b, n, d"

        let tree, sourceText, check =
            FSharp.Refactor.Tests.Parsing.parseAndCheckLegacyFramework source

        Assert.False(FSharp.Refactor.OptionModule.hasErrors check, "the legacy fixture itself must typecheck")
        Assert.Empty(FSharp.Refactor.SubstringSpan.find tree sourceText check)
        Assert.Empty(FSharp.Refactor.PrefixCompare.find true tree sourceText check)
        Assert.Empty(FSharp.Refactor.CharArrayCopy.find tree sourceText check)

        // and the modern compilation of the very same text fires all three
        let tree, sourceText, check = FSharp.Refactor.Tests.Parsing.parseAndCheck source
        Assert.Equal(2, (FSharp.Refactor.SubstringSpan.find tree sourceText check).Length)
        Assert.Equal(2, (FSharp.Refactor.PrefixCompare.find true tree sourceText check).Length)
        Assert.Equal(2, (FSharp.Refactor.CharArrayCopy.find tree sourceText check).Length)

// ---- CapabilityFix dual-framework emission ----

let private withDualTfm (f: unit -> unit) =
    FSharp.Refactor.Scope.set
        { FSharp.Refactor.Scope.editor with
            DualTfmConstant = ValueSome "NETSTANDARD21"
        }

    try
        f ()
    finally
        FSharp.Refactor.Scope.reset ()

let private dualFixFor (source: string) =
    let tree, sourceText, checkResults =
        FSharp.Refactor.Tests.Parsing.parseAndCheck source

    match FSharp.Refactor.SubstringSpan.find tree sourceText checkResults with
    | [ s ] -> FSharp.Refactor.CapabilityFix.make sourceText s.Range "Substring" "AsSpan"
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a dual-framework run wraps the fix in an if-else pair`` () =
    withDualTfm (fun () ->
        let fix =
            dualFixFor
                "module Test\nopen System\n#if NETSTANDARD\nlet flag = 1\n#endif\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

        Assert.Contains("#if NETSTANDARD21", fix.ToText)
        Assert.Contains("Int32.Parse(s.AsSpan(6, 5))", fix.ToText)
        Assert.Contains("#else", fix.ToText)
        Assert.Contains("Int32.Parse(s.Substring(6, 5))", fix.ToText)
        Assert.Contains("#endif", fix.ToText))

[<Fact>]
let ``a file without conditionals keeps the plain fix even on a dual run`` () =
    withDualTfm (fun () ->
        let fix =
            dualFixFor "module Test\nopen System\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

        Assert.Equal("AsSpan", fix.ToText))

[<Fact>]
let ``a line already under a modern guard keeps the plain fix`` () =
    // the guard scan is textual, so drive CapabilityFix.make directly: a
    // test parse (empty defines) never enters the NET6_0_OR_GREATER branch
    withDualTfm (fun () ->
        let text =
            "module Test\nopen System\n#if NET6_0_OR_GREATER\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))\n#endif"

        let sourceText = SourceText.ofString text
        let line = sourceText.GetLineString 3
        let col = line.IndexOf "Substring"

        let r =
            FSharp.Compiler.Text.Range.mkRange
                "T.fs"
                (FSharp.Compiler.Text.Position.mkPos 4 col)
                (FSharp.Compiler.Text.Position.mkPos 4 (col + 9))

        let fix = FSharp.Refactor.CapabilityFix.make sourceText r "Substring" "AsSpan"
        Assert.Equal("AsSpan", fix.ToText))

[<Fact>]
let ``the negative branch of a modern guard still wraps`` () =
    // inside #else of the guard: this line IS what legacy compiles
    withDualTfm (fun () ->
        let fix =
            dualFixFor
                "module Test\nopen System\n#if NETSTANDARD21\nlet flag = 1\n#else\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))\n#endif"

        Assert.Contains("#if NETSTANDARD21", fix.ToText))

[<Fact>]
let ``without the dual signal the fix is always plain`` () =
    let fix =
        dualFixFor
            "module Test\nopen System\n#if NETSTANDARD\nlet flag = 1\n#endif\nlet f (s: string) = Int32.Parse(s.Substring(6, 5))"

    Assert.Equal("AsSpan", fix.ToText)

// ---- FR0170 DictKeysLoop ----

let private dictKeysLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    FSharp.Refactor.DictKeysLoop.find tree sourceText checkResults

[<Fact>]
let ``FR0170: a loop over Keys reading the indexer becomes a KeyValue loop`` () =
    let source =
        "module M\nopen System.Collections.Generic\nlet show (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        printfn \"%s=%d\" k d.[k]\n        printfn \"%d\" (d[k] + 1)\ntype Holder() =\n    member val Table = Dictionary<int, string>() with get\n    member this.Dump() =\n        for key in this.Table.Keys do\n            printfn \"%d %s\" key this.Table.[key]"

    match dictKeysLoopsIn source with
    | [ a; b ] ->
        Assert.Equal("k", a.KeyName)
        Assert.Equal("value", a.ValueName)
        Assert.Equal(3, a.Edits.Length)
        Assert.Equal("key", b.KeyName)

        let patched =
            a.Edits @ b.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            "    for KeyValue(k, value) in d do\n        printfn \"%s=%d\" k value\n        printfn \"%d\" (value + 1)",
            patched
        )

        Assert.Contains("for KeyValue(key, value) in this.Table do\n            printfn \"%d %s\" key value", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0170: a store through the indexer, a concurrent dictionary, no lookup, and a taken value name stay put`` () =
    let source =
        "module M\nopen System.Collections.Generic\nopen System.Collections.Concurrent\nlet bump (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        d.[k] <- d.[k] + 1\nlet concurrent (d: ConcurrentDictionary<string, int>) =\n    for k in d.Keys do\n        printfn \"%d\" d.[k]\nlet keysOnly (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        printfn \"%s\" k\nlet taken (d: Dictionary<string, int>) (value: int) (v: int) (v1: int) =\n    for k in d.Keys do\n        printfn \"%d\" (d.[k] + value + v + v1)"

    Assert.Empty(dictKeysLoopsIn source)

[<Fact>]
let ``FR0170: a visible writer through a setter, a hook, an auto-property, an alias or a constructing getter keeps the loop; a read-only helper converts``
    ()
    =
    let source =
        "module M\nopen System.Collections.Generic\ntype Holder(d: Dictionary<string, int>) =\n    member val D = Dictionary<string, int>() with get, set\n    member this.Bump with set (v: int) = d.[\"a\"] <- v\n    member this.Reset() = this.D.Clear()\n    member this.Dump() =\n        for k in this.D.Keys do\n            this.Reset()\n            printfn \"%d\" this.D.[k]\nlet setter (d: Dictionary<string, int>) (h: Holder) =\n    for k in d.Keys do\n        h.Bump <- 99\n        printfn \"%d\" d.[k]\nlet mutable hook = fun () -> ()\nlet hooked (d: Dictionary<string, int>) =\n    hook <- fun () -> d.Clear()\n    for k in d.Keys do\n        hook ()\n        printfn \"%d\" d.[k]\nlet tupleAlias (d: Dictionary<string, int>) =\n    let view, _ = d, 1\n    for k in d.Keys do\n        view.Remove k |> ignore\n        printfn \"%d\" d.[k]\ntype Env = { Table: Dictionary<string, int> }\nlet recordAlias (d: Dictionary<string, int>) =\n    let env = { Table = d }\n    for k in d.Keys do\n        env.Table.Remove k |> ignore\n        printfn \"%d\" d.[k]\nlet make () = Dictionary<string, int>()\ntype Store() =\n    member _.Table = make ()\nlet unstable (s: Store) =\n    for k in s.Table.Keys do\n        printfn \"%d\" s.Table.[k]\nlet table = Dictionary<string, int>()\nlet has (k: string) = table.ContainsKey k\nlet readOnly () =\n    for k in table.Keys do\n        if has k then printfn \"%s %d\" (table.Count.ToString()) table.[k]\ntype Holder2(d: Dictionary<string, int>) =\n    member _.Count with get () = d.Count and set (v: int) = d.[\"a\"] <- v\nlet getSet (d: Dictionary<string, int>) (h: Holder2) =\n    for k in d.Keys do\n        h.Count <- 99\n        printfn \"%d\" d.[k]\ntype Env2 = { Table2: Dictionary<string, int>; mutable Counter: int }\nlet holderCounter (d: Dictionary<string, int>) =\n    let env = { Table2 = d; Counter = 0 }\n    for k in d.Keys do\n        env.Counter <- env.Counter + 1\n        printfn \"%d\" d.[k]\nlet sumValues () = table.Values |> Seq.sum\nlet readsValues () =\n    for k in table.Keys do\n        printfn \"%d %d\" (sumValues ()) table.[k]\nlet trace (x: Dictionary<string, int>) = (let sb = System.Text.StringBuilder() in sb.Append(x.Count) |> ignore); x\ntype Store2() =\n    member _.Traced = trace table\nlet stable (s: Store2) =\n    for k in s.Traced.Keys do\n        printfn \"%d\" s.Traced.[k]\nlet tuplePair (d: Dictionary<string, int>) (other: Dictionary<string, int>) =\n    let a, b = d, other\n    for k in d.Keys do\n        b.Remove k |> ignore\n        printfn \"%d %d\" a.Count d.[k]"

    // the read-only helper, the holder's counter, the Values-summing helper,
    // the getter through a non-constructing helper and the tuple's other
    // dictionary convert; the get/set property and everything above it hold
    Assert.Equal<int list>([ 41; 52; 57; 63; 67 ], dictKeysLoopsIn source |> List.map (fun s -> s.Range.StartLine))

// ---- FR0171 ByteStringLiteral ----

let private byteStringsIn (source: string) =
    let tree, sourceText = parse source
    FSharp.Refactor.ByteStringLiteral.find tree sourceText

[<Fact>]
let ``FR0171: an ASCII literal handed to GetBytes is a byte string literal`` () =
    let source =
        "module M\nopen System.Text\nlet a = Encoding.UTF8.GetBytes \"GET / HTTP/1.1\"\nlet b = Encoding.ASCII.GetBytes(\"OK\")\nlet c = System.Text.Encoding.UTF8.GetBytes @\"C:\\x\"\nlet d = Text.Encoding.Latin1.GetBytes \"a\\nb\""

    match byteStringsIn source with
    | [ a; b; c; d ] ->
        Assert.Equal("\"GET / HTTP/1.1\"B", a.ReplacementText)
        Assert.Equal("\"OK\"B", b.ReplacementText)
        Assert.Equal("@\"C:\\x\"B", c.ReplacementText)
        Assert.Equal("\"a\\nb\"B", d.ReplacementText)

        let patched =
            [ a; b; c; d ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold (fun acc s -> applyEdit acc s.Range s.ReplacementText) source

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected four findings, got %A" other

[<Fact>]
let ``FR0171: a non-ASCII literal, an interpolated string, a variable and another encoding stay put`` () =
    let source =
        "module M\nopen System.Text\nlet a = Encoding.UTF8.GetBytes \"häh\"\nlet b (n: int) = Encoding.UTF8.GetBytes $\"n={n}\"\nlet c (s: string) = Encoding.UTF8.GetBytes s\nlet d = Encoding.Unicode.GetBytes \"OK\"\nlet e = Encoding.UTF8.GetBytes \"\"\"OK\"\"\""

    Assert.Empty(byteStringsIn source)

[<Fact>]
let ``FR0170: a body that rebinds the key keeps the loop`` () =
    // `d.[k]` under a `let k = ...` reads another key: replacing it with the
    // pair's value would read the wrong one
    let source =
        "module M\nopen System.Collections.Generic\nlet shifted (d: Dictionary<int, int>) =\n    for k in d.Keys do\n        let k = k + 1\n        if d.ContainsKey k then printfn \"%d\" d.[k]\nlet lambda (d: Dictionary<int, int>) (f: (int -> int) -> unit) =\n    for k in d.Keys do\n        f (fun k -> d.[k])"

    Assert.Empty(dictKeysLoopsIn source)

[<Fact>]
let ``FR0170: a read deferred under a lambda, lazy, computation expression or object expression keeps the loop`` () =
    // the deferred read sees the dictionary as it is when it runs; the
    // pair's value is a snapshot taken during the loop
    let source =
        "module M\nopen System\nopen System.Collections.Generic\nlet readers (d: Dictionary<int, int>) (acts: ResizeArray<unit -> int>) =\n    for k in d.Keys do\n        acts.Add(fun () -> d.[k])\nlet lazies (d: Dictionary<int, int>) (acc: ResizeArray<Lazy<int>>) =\n    for k in d.Keys do\n        acc.Add(lazy d.[k])\nlet asyncs (d: Dictionary<int, int>) (acc: ResizeArray<Async<int>>) =\n    for k in d.Keys do\n        acc.Add(async { return d.[k] })\nlet objs (d: Dictionary<int, int>) (acc: ResizeArray<obj>) =\n    for k in d.Keys do\n        acc.Add({ new Object() with member _.ToString() = string d.[k] })\nlet matchers (d: Dictionary<int, int>) (acc: ResizeArray<int -> int>) =\n    for k in d.Keys do\n        acc.Add(function 0 -> d.[k] | n -> n)"

    // the rule stands down on a compile error: the source must be clean
    Assert.True(typechecksCleanly source)
    Assert.Empty(dictKeysLoopsIn source)

[<Fact>]
let ``FR0170: what visibly writes the dictionary before a read keeps the loop`` () =
    // `v` is the value when the iteration started, `d.[k]` the value when it
    // runs, and since .NET Core 3.0 an overwrite or a Remove leaves the
    // enumeration running: a helper handed the dictionary, a local function
    // writing it, an alias, a Remove, a rebound receiver, a getter of this
    // file that builds a dictionary. A callback of unknown body (`f ()`) is
    // taken as harmless: the fix by default
    let source =
        "module M\nopen System.Collections.Generic\nlet bumpIn (d: Dictionary<string, int>) (k: string) = d.[k] <- d.[k] + 1\nlet helper (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        bumpIn d k\n        printfn \"%d\" d.[k]\nlet closure (d: Dictionary<string, int>) =\n    let bump (k: string) = d.[k] <- 0\n    for k in d.Keys do\n        bump k\n        printfn \"%d\" d.[k]\nlet alias (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        let m = d\n        m.[k] <- 0\n        printfn \"%d\" d.[k]\nlet removed (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        d.Remove k |> ignore\n        printfn \"%b\" (d.ContainsKey k && d.[k] > 0)\nlet rebound (d: Dictionary<string, int>) (other: Dictionary<string, int>) =\n    for k in d.Keys do\n        let d = other\n        printfn \"%d\" d.[k]\nlet nested (d: Dictionary<string, int>) (f: unit -> unit) =\n    for k in d.Keys do\n        for _ in 1..2 do\n            printfn \"%d\" d.[k]\n            f ()\ntype Computed() =\n    member _.Table = Dictionary<int, string>()\n    member this.Dump() =\n        for key in this.Table.Keys do\n            printfn \"%s\" this.Table.[key]"

    Assert.True(typechecksCleanly source)

    match dictKeysLoopsIn source with
    | [ s ] -> Assert.Equal(27, s.Range.StartLine)
    | other -> failwithf "Expected the loop with the unknown callback alone, got %A" other

    // the premise: an overwrite mid-enumeration no longer throws, and the
    // pair's value is the one from before it
    let d = System.Collections.Generic.Dictionary<string, int>(dict [ "a", 1 ])

    for KeyValue(k, value) in d do
        d.[k] <- value + 1
        Assert.Equal(1, value)
        Assert.Equal(2, d.[k])

[<Fact>]
let ``FR0170: reassignment, aliases, a visibly writing getter, outer loops, local functions and forced definitions keep the loop``
    ()
    =
    // each visibly writes the dictionary before a read in the same
    // iteration: a reassigned mutable receiver; an alias bound before the
    // loop; a getter of this file that clears, handed to printfn; a Remove
    // in a loop around the inner loop that reads; a read inside a local
    // function called after the Remove; an Async of this file that clears,
    // run; a Seq.length forcing a sequence of this file whose generator
    // removes. An event's handler is not the event's definition: the
    // Trigger is taken as harmless
    let source =
        "module M\nopen System.Collections.Generic\nlet d = Dictionary<string, int>()\nlet mutableReceiver (a: Dictionary<string, int>) (b: Dictionary<string, int>) =\n    let mutable m = a\n    for k in m.Keys do\n        m <- b\n        printfn \"%d\" m.[k]\nlet aliasOutside () =\n    let view: IDictionary<string, int> = d\n    for k in d.Keys do\n        view.[k] <- 0\n        printfn \"%d\" d.[k]\ntype Evictor() =\n    member _.Evicted =\n        d.Clear()\n        0\nlet getterArgument (e: Evictor) =\n    for k in d.Keys do\n        printfn \"%d %d\" e.Evicted d.[k]\nlet outerLoop () =\n    let mutable n = 0\n    for k in d.Keys do\n        while n < 2 do\n            for _ in 1..2 do\n                printfn \"%d\" d.[k]\n            d.Remove k |> ignore\n            n <- n + 1\nlet localFunction () =\n    for k in d.Keys do\n        let get () = d.[k]\n        d.Remove k |> ignore\n        printfn \"%d\" (get ())\nlet ev = Event<string>()\nev.Publish.Add(fun key -> d.Remove key |> ignore)\nlet trigger () =\n    for k in d.Keys do\n        ev.Trigger k\n        printfn \"%d\" d.[k]\nlet flush = async { d.Clear() }\nlet runAsync () =\n    for k in d.Keys do\n        Async.RunSynchronously flush\n        printfn \"%d\" d.[k]\nlet s = seq { d.Remove \"a\" |> ignore; yield 1 }\nlet forced () =\n    for k in d.Keys do\n        let n = Seq.length s\n        printfn \"%d %d\" n d.[k]"

    Assert.True(typechecksCleanly source)

    match dictKeysLoopsIn source with
    | [ s ] -> Assert.Equal(37, s.Range.StartLine)
    | other -> failwithf "Expected the event's loop alone, got %A" other

[<Fact>]
let ``FR0170: interface calls and a user collection convert; a suspension in seq or task keeps the loop`` () =
    // an interface call (an observer, a disposable, a comparer handed to
    // Array.Sort) and a collection of the user's own run code the analysis
    // cannot see: taken as harmless, the fix by default, the accepted
    // residual. In `seq { }` the consumer runs at each yield, in `task { }`
    // other code runs at each let! and do!: those keep the loop
    let source =
        "module M\nopen System\nopen System.Collections.Generic\nopen System.Threading.Tasks\nlet d = Dictionary<string, int>()\nlet observer (o: IObserver<string>) =\n    for k in d.Keys do\n        o.OnNext k\n        printfn \"%d\" d.[k]\nlet disposer (x: IDisposable) =\n    for k in d.Keys do\n        x.Dispose()\n        printfn \"%d\" d.[k]\nlet sorter (arr: string[]) (cmp: IComparer<string>) =\n    for k in d.Keys do\n        Array.Sort(arr, cmp)\n        printfn \"%d\" d.[k]\ntype Bag() =\n    interface IEnumerable<int> with\n        member _.GetEnumerator() : IEnumerator<int> = (d.Clear(); Seq.empty<int>.GetEnumerator())\n        member _.GetEnumerator() : Collections.IEnumerator = (d.Clear(); (Seq.empty<int> :> Collections.IEnumerable).GetEnumerator())\nlet bag (b: Bag) =\n    for k in d.Keys do\n        for _ in b do ()\n        printfn \"%d\" d.[k]\nlet yields () =\n    seq {\n        for k in d.Keys do\n            yield k\n            yield string d.[k]\n    }\nlet awaits (t: Task<int>) =\n    task {\n        for k in d.Keys do\n            let! x = t\n            printfn \"%d %d\" x d.[k]\n    }"

    Assert.True(typechecksCleanly source)

    Assert.Equal<int list>(
        [ 7; 11; 15; 23 ],
        dictKeysLoopsIn source |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

[<Fact>]
let ``FR0170: a callback before the read converts unless a definition of this file visibly writes the dictionary`` () =
    // a local dictionary with a logger, an interface call or a callback
    // before the read: the fix; in a `task { }` the `do!` keeps the loop
    let unreached =
        "module M\nopen System\nopen System.Collections.Generic\nlet log (s: string) = printfn \"%s\" s\nlet count (words: string[]) (o: IObserver<string>) =\n    let d = Dictionary<string, int>()\n    for w in words do\n        d.[w] <- (if d.ContainsKey w then d.[w] else 0) + 1\n    for k in d.Keys do\n        log k\n        o.OnNext k\n        printfn \"%d\" d.[k]\nlet awaited (words: string[]) (t: Threading.Tasks.Task) =\n    task {\n        let d = Dictionary<string, int>()\n        for w in words do d.[w] <- 1\n        for k in d.Keys do\n            do! t\n            printfn \"%d\" d.[k]\n    }"

    Assert.True(typechecksCleanly unreached)

    // the plain function converts; inside `task { }` the function may write
    // the dictionary while the loop waits, so no local is unreached there
    match dictKeysLoopsIn unreached with
    | [ s ] -> Assert.Equal(9, s.Range.StartLine)
    | other -> failwithf "Expected the plain loop alone, got %A" other

    // handed to a helper, captured by a closure, bound to another name, with
    // a callback of unknown body before the read: the callback may reach it
    // through those, but nothing visible says so - the fix by default, the
    // accepted residual
    let escaped =
        "module M\nopen System.Collections.Generic\nlet bump (m: Dictionary<string, int>) = m.[\"a\"] <- 0\nlet handedOn (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>()\n    for w in words do d.[w] <- 1\n    let g () = bump d\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]\nlet captured (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>()\n    let reset = fun () -> d.Clear()\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]\nlet aliased (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>()\n    let view = d\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]"

    Assert.True(typechecksCleanly escaped)
    Assert.Equal(3, (dictKeysLoopsIn escaped).Length)

    // what is visible keeps the loop: a writer taken as a value and called,
    // a sequence of this file that writes, forced; an implicit yield. An
    // extension of the project's own on the receiver before the loop, and a
    // framework extension on a parameter that may alias it, are not visible
    // writes: the fix
    let hidden =
        "module M\nopen System.Collections.Generic\n[<System.Runtime.CompilerServices.Extension>]\ntype Ext =\n    [<System.Runtime.CompilerServices.Extension>]\n    static member Track(m: Dictionary<string, int>) = ()\nlet methodValue (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>()\n    let reset = d.Clear\n    for k in d.Keys do\n        f k\n        reset ()\n        printfn \"%d\" d.[k]\nlet extension (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>()\n    d.Track()\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]\nlet computation (words: string[]) =\n    let d = Dictionary<string, int>()\n    let later = seq { d.[\"a\"] <- 100; yield 1 }\n    for k in d.Keys do\n        let n = Seq.length later\n        printfn \"%d %d\" n d.[k]\nlet aliasRemove (d: Dictionary<string, int>) (other: IDictionary<string, int>) =\n    for k in d.Keys do\n        let mutable old = 0\n        other.Remove(k, &old) |> ignore\n        printfn \"%d\" d.[k]\nlet implicitYield (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            k\n            string d.[k]\n    }"

    Assert.True(typechecksCleanly hidden)

    Assert.Equal<int list>([ 17; 27 ], dictKeysLoopsIn hidden |> List.map (fun s -> s.Range.StartLine) |> List.sort)

    // a comparer or key type of the user's own changes nothing visible: the
    // fix for all three
    let lookups =
        "module M\nopen System\nopen System.Collections.Generic\ntype Key(n: int) =\n    member _.N = n\n    override _.GetHashCode() = n\n    override _.Equals(o) = (match o with :? Key as k -> k.N = n | _ -> false)\ntype Cmp() =\n    interface IEqualityComparer<string> with\n        member _.Equals(a, b) = a = b\n        member _.GetHashCode(s) = s.GetHashCode()\nlet userComparer (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>(Cmp())\n    for w in words do d.[w] <- 1\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]\nlet userKey (keys: Key[]) (f: Key -> unit) =\n    let d = Dictionary<Key, int>()\n    for w in keys do d.[w] <- 1\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]\nlet frameworkComparer (words: string[]) (f: string -> unit) =\n    let d = Dictionary<string, int>(StringComparer.OrdinalIgnoreCase)\n    for w in words do d.[w] <- 1\n    for k in d.Keys do\n        f k\n        printfn \"%d\" d.[k]"

    Assert.True(typechecksCleanly lookups)
    Assert.Equal(3, (dictKeysLoopsIn lookups).Length)

[<Fact>]
let ``FR0170: a helper of this file before the read converts unless its body touches a dictionary`` () =
    // `label k` and `counting k` (a module mutable int) touch no dictionary;
    // `touching k` removes from one, and `chained k` calls it
    let source =
        "module M\nopen System.Collections.Generic\nlet shared = Dictionary<string, int>()\nlet label (k: string) = k.ToUpper() + \":\"\nlet mutable count = 0\nlet counting (k: string) =\n    count <- count + 1\n    k\nlet touching (k: string) =\n    shared.Remove k |> ignore\n    k\nlet chained (k: string) = touching k\nlet pure (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        let l = label k\n        printfn \"%s %d\" l d.[k]\nlet storing (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        let l = counting k\n        printfn \"%s %d\" l d.[k]\nlet dictionary () =\n    for k in shared.Keys do\n        let l = touching k\n        printfn \"%s %d\" l shared.[k]\nlet viaOther () =\n    for k in shared.Keys do\n        let l = chained k\n        printfn \"%s %d\" l shared.[k]"

    Assert.True(typechecksCleanly source)

    Assert.Equal<int list>([ 14; 18 ], dictKeysLoopsIn source |> List.map (fun s -> s.Range.StartLine) |> List.sort)

    // in a `seq { }` a unit statement yields nothing: a printf, a store, a
    // Console call before the read leave the consumer out of the loop
    let unitStatements =
        "module M\nopen System\nopen System.Collections.Generic\nlet logged (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            printfn \"%s\" k\n            Console.WriteLine k\n            yield d.[k]\n    }\nlet mutable seen = 0\nlet stored (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            seen <- seen + 1\n            yield d.[k]\n    }"

    Assert.True(typechecksCleanly unitStatements)
    Assert.Equal(2, (dictKeysLoopsIn unitStatements).Length)

    // a helper forcing a sequence whose generator writes, an active pattern
    // of the user's own tried before the read, and an else-less `if` or a
    // loop with a value - an implicit yield - in a `seq { }`
    let reached =
        "module M\nopen System.Collections.Generic\nlet table = Dictionary<string, int>()\nlet sneaky = seq { table.Clear(); yield 1 }\nlet helper () = Seq.length sneaky\nlet forced () =\n    for k in table.Keys do\n        helper () |> ignore\n        printfn \"%d\" table.[k]\nlet (|Touch|_|) (k: string) =\n    table.[\"a\"] <- 99\n    Some()\nlet active () =\n    for k in table.Keys do\n        match k with\n        | Touch -> printfn \"%d\" table.[k]\n        | _ -> ()\nlet implicitIf (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            if k = \"a\" then 10\n            printfn \"%d\" d.[k]\n    }\nlet implicitFor (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            for j in 1..1 do\n                j\n            printfn \"%d\" d.[k]\n    }"

    Assert.True(typechecksCleanly reached)
    Assert.Empty(dictKeysLoopsIn reached)

[<Fact>]
let ``FR0170: LINQ, field stores, another dictionary's writes and a yield of the read keep converting`` () =
    // LINQ consumes a receiver checked where it stands; a record field store
    // runs no code; a dictionary of other type arguments cannot be this one;
    // a lookup through IReadOnlyDictionary reads; `yield k, d.[k]` reads
    // before it yields, and a list comprehension runs nothing between
    let source =
        "module M\nopen System.Linq\nopen System.Collections.Generic\ntype Acc = { mutable Count: int }\nlet linq (d: Dictionary<string, int>) (xs: int[]) =\n    for k in d.Keys do\n        let n = xs.Count(fun x -> x > 0)\n        let big = xs.Where(fun x -> x > 10).ToArray()\n        printfn \"%d %d %d\" n big.Length d.[k]\nlet fieldStore (d: Dictionary<string, int>) (acc: Acc) =\n    for k in d.Keys do\n        acc.Count <- acc.Count + 1\n        printfn \"%d\" d.[k]\nlet otherDictionary (d: Dictionary<string, int>) =\n    let seen = Dictionary<string, bool>()\n    for k in d.Keys do\n        seen.[k] <- true\n        seen.Add(k + \"!\", false)\n        printfn \"%d\" d.[k]\nlet readOnlyLookup (d: Dictionary<string, int>) (other: IReadOnlyDictionary<string, int>) =\n    for k in d.Keys do\n        let found, v = other.TryGetValue k\n        printfn \"%b %d %d\" found v d.[k]\nlet yieldsPair (d: Dictionary<string, int>) =\n    seq {\n        for k in d.Keys do\n            yield k, d.[k]\n    }\nlet comprehension (d: Dictionary<string, int>) =\n    [ for k in d.Keys do\n        yield k\n        yield string d.[k] ]"

    Assert.True(typechecksCleanly source)
    Assert.Equal(6, (dictKeysLoopsIn source).Length)

[<Fact>]
let ``FR0170: a call that runs after the reads, or takes the read as its argument, keeps the rewrite`` () =
    // a call's arguments run before it: `store k d.[k]` reads first. A
    // user call after the last read cannot change what the reads saw, and
    // FSharp.Core, the BCL and local mutables cannot reach the dictionary
    let source =
        "module M\nopen System.Collections.Generic\nlet store (acc: ResizeArray<string>) (k: string) (v: int) = acc.Add(k + string v)\nlet argument (d: Dictionary<string, int>) (acc: ResizeArray<string>) =\n    for k in d.Keys do\n        store acc k d.[k]\nlet after (d: Dictionary<string, int>) (f: string -> unit) =\n    for k in d.Keys do\n        printfn \"%d\" d.[k]\n        f k\nlet core (d: Dictionary<string, int>) (sums: int[]) =\n    let mutable total = 0\n    for k in d.Keys do\n        total <- total + String.length k\n        sums.[0] <- sums.[0] + 1\n        printfn \"%d %d\" total d.[k]"

    Assert.True(typechecksCleanly source)
    Assert.Equal(3, (dictKeysLoopsIn source).Length)

    // the everyday shapes beside the guards: copying into another
    // dictionary (its write runs after the read it is handed), a
    // StringBuilder, an interpolation, a pipe into a user function, the
    // console before the read, a record field and a BCL getter on the way
    let everyday =
        "module M\nopen System\nopen System.Text\nopen System.Collections.Generic\ntype Row = { Name: string }\nlet show (x: int) = printfn \"%d\" x\nlet copy (d: Dictionary<string, int>) (acc: Dictionary<string, int>) =\n    for k in d.Keys do\n        acc.Add(k, d.[k])\nlet store (d: Dictionary<string, int>) (acc: Dictionary<string, int>) =\n    for k in d.Keys do\n        acc.[k] <- d.[k] + 1\nlet build (d: Dictionary<string, int>) (sb: StringBuilder) =\n    for k in d.Keys do\n        sb.Append(k).Append('=').Append(d.[k]) |> ignore\nlet interpolate (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        Console.WriteLine k\n        printfn $\"{k}={d.[k]}\"\nlet piped (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        d.[k] |> show\nlet fields (d: Dictionary<string, Row>) (now: DateTime) =\n    for k in d.Keys do\n        let year = now.Year\n        printfn \"%d %s\" year d.[k].Name"

    Assert.True(typechecksCleanly everyday)
    Assert.Equal(6, (dictKeysLoopsIn everyday).Length)

[<Fact>]
let ``FR0171: a user type named Encoding is not the framework's under a typecheck`` () =
    let source =
        "module M\ntype Codec() =\n    member _.GetBytes(s: string) = Array.zeroCreate<byte> s.Length\ntype Encoding() =\n    static member val UTF8 = Codec() with get\nlet a = Encoding.UTF8.GetBytes \"OK\"\nlet b = System.Text.Encoding.UTF8.GetBytes \"OK\""

    let tree, sourceText, check = parseAndCheck source

    match FSharp.Refactor.ByteStringLiteral.findWith (Some check) tree sourceText with
    | [ s ] -> Assert.Equal(7, s.Range.StartLine)
    | other -> failwithf "Expected the framework call alone, got %A" other

    // parse-only, the spelling is the proof: both
    Assert.Equal(2, (FSharp.Refactor.ByteStringLiteral.find tree sourceText).Length)

// ---- AstIndex.exprsWithin ----

[<Fact>]
let ``exprsWithin answers exactly what a walk of the whole index answers`` () =
    // the rules ask it per candidate in place of `index.Exprs |> filter
    // (rangeContainsRange r)`: the same nodes in the same order, or a rule
    // would see a different file. Two of this package's own sources: every
    // shape it walks, object expressions (the lifted nodes) included
    for file in [ "SwallowedException.fs"; "AstIndex.fs" ] do
        let path =
            Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "src", "FSharp.Refactor.Analyzers", file)

        let tree, _ = parseNamed file (File.ReadAllText path)
        let index = FSharp.Refactor.AstIndex.ofTree tree

        let spans =
            [
                // every seventh node's own range, and windows of lines that
                // cut through nodes
                for i, (_, e) in Array.indexed index.Exprs do
                    if i % 7 = 0 then
                        e.Range

                for line in 1..13..1200 do
                    Range.mkRange file (Position.mkPos line 4) (Position.mkPos (line + 9) 30)
            ]

        Assert.True(spans.Length > 100, $"{file}: too few spans to prove anything")

        for r in spans do
            let expected =
                index.Exprs
                |> Array.filter (fun (_, e) -> Range.rangeContainsRange r e.Range)
                |> Array.map snd

            let actual = FSharp.Refactor.AstIndex.exprsWithin index r |> Array.map snd

            Assert.True(
                expected.Length = actual.Length
                && Array.forall2
                    (fun (a: obj) (b: obj) -> obj.ReferenceEquals(a, b))
                    (Array.map box expected)
                    (Array.map box actual),
                $"{file} {r}: {expected.Length} nodes by the walk, {actual.Length} by the query"
            )

            // the patterns the same way
            let expectedPats =
                index.Pats
                |> Array.filter (fun (_, p) -> Range.rangeContainsRange r p.Range)
                |> Array.map snd

            let actualPats = FSharp.Refactor.AstIndex.patsWithin index r |> Array.map snd

            Assert.True(
                expectedPats.Length = actualPats.Length
                && Array.forall2
                    (fun (a: obj) (b: obj) -> obj.ReferenceEquals(a, b))
                    (Array.map box expectedPats)
                    (Array.map box actualPats),
                $"{file} {r}: {expectedPats.Length} patterns by the walk, {actualPats.Length} by the query"
            )
