/// Regression tests from the 2026-08-26 critical review: replacement
/// logic errors and false-positive identifications, one test per
/// confirmed finding.
module FSharp.Refactor.Tests.CriticalReviewTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

[<Fact>]
let ``FR0026: a field assigned in another member is not an auto-property`` () : unit =
    // the assignment is a LongIdentSet, not an Ident expression — the fix
    // used to delete the field and leave Reset() referencing nothing
    let tree, sourceText =
        parse
            "module Test\ntype Person() =\n    let mutable name = \"\"\n    member _.Reset() = name <- \"\"\n    member this.Name\n        with get () = name\n        and set v = name <- v"

    Assert.Empty(AutoProperty.find tree sourceText)

[<Fact>]
let ``FR0034: a shadowing lambda parameter suppresses the rewrite`` () : unit =
    // the inner x is a different option; substituting its .Value with the
    // outer binder would change which value the code reads
    let tree, sourceText, check =
        parseAndCheck
            "let f (x: int option) = if x.IsSome then [ Some 1 ] |> List.map (fun x -> x.Value) |> List.sum else 0"

    Assert.Empty(OptionMatch.find tree sourceText check)

[<Fact>]
let ``FR0031: a shadowed plus operator is never rewritten`` () : unit =
    let tree, sourceText, check =
        parseAndCheck "let (+) (a: string) (b: string) = a\nlet f (x: string) = \"pre \" + x + \"!\""

    Assert.Empty(StringConcat.find tree sourceText check)

[<Fact>]
let ``FR0035: a per-iteration collection is not loop-invariant`` () : unit =
    let tree, sourceText =
        parse
            "module Test\nlet f (xs: int list) =\n    for x in xs do\n        let ys = [ x; x + 1 ]\n        if List.contains x ys then printfn \"%d\" x"

    let contains, _ = LoopPerf.find false tree sourceText
    Assert.Empty contains

[<Fact>]
let ``FR0021: ToString under a typed hole pins the type and stays`` () : unit =
    // %s requires a string; dropping .ToString() would not typecheck
    let tree, sourceText = parse "module Test\nlet f (x: int) = $\"%s{x.ToString()}\""
    Assert.Empty(InterpToString.find tree sourceText)

[<Fact>]
let ``FR0021: ToString in an untyped hole is still simplified`` () : unit =
    let tree, sourceText =
        parse "module Test\nlet f (x: int) = $\"{x.ToString()} items\""

    match InterpToString.find tree sourceText with
    | [ s ] -> Assert.Equal("x", s.ReplacementText)
    | other -> failwithf "Expected exactly one ToString suggestion, got %A" other

[<Fact>]
let ``FR0025: a shadowed isNull is never rewritten`` () : unit =
    let tree, sourceText, check =
        parseAndCheck "let isNull (s: string) = s.Length = 0\nlet f (s: string) = if isNull s then None else Some s"

    Assert.Empty(OptionOfObj.find tree sourceText check)

[<Fact>]
let ``FR0012: a method call substituted as an argument keeps its parentheses`` () : unit =
    // corpus find (FSharp.Data/build/build.fs): the hint produced
    // `not (isNull Environment.GetEnvironmentVariable("CI"))`, which is
    // error FS0597 — a high-precedence application still needs parens in
    // argument position
    let tree, sourceText =
        parse "module Test\nopen System\nlet isCI = Environment.GetEnvironmentVariable(\"CI\") <> null"

    match HintEngine.find [] tree sourceText None with
    | [ s ] ->
        // and F# brackets the whole application: (f x), never (f(x))
        Assert.Equal("not (isNull (Environment.GetEnvironmentVariable \"CI\"))", s.ReplacementText)

        let patched =
            applyEdit
                "module Test\nopen System\nlet isCI = Environment.GetEnvironmentVariable(\"CI\") <> null"
                s.Range
                s.ReplacementText

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one null-comparison hint, got %A" other

[<Fact>]
let ``FR0008: a method call in a call tuple keeps its parentheses`` () : unit =
    // same shape through TupleParams: `add f(1) 2` would be FS0597
    let source =
        "module Test\nlet g (n: int) = n\nlet private add (a: int, b: int) = a + b\nlet total = add (g(1), 2)"

    let tree, sourceText, check = parseAndCheck source

    match TupleParams.find tree sourceText check with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
            |> List.fold (fun acc e -> applyEdit acc e.Range e.Replacement) source

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one tupled-parameter suggestion, got %A" other

[<Fact>]
let ``FR0012: a multi-argument call keeps its argument list`` () : unit =
    // Path.Combine(a, b) — those parens ARE the argument list, so they
    // cannot be moved the way a single argument's can
    let source =
        "module Test\nopen System\nlet f (a: string) (b: string) = IO.Path.Combine(a, b) <> null"

    let tree, sourceText = parse source

    match HintEngine.find [] tree sourceText None with
    | [ s ] ->
        Assert.Equal("not (isNull (IO.Path.Combine(a, b)))", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one multi-argument null hint, got %A" other

[<Fact>]
let ``FR0081: escape-sequence building is not a path join`` () : unit =
    // corpus find (FsAutoComplete InteractiveDirectives.fs): backslash
    // literals used to fire with no path evidence at all
    let tree, sourceText =
        parse
            "module Test\nlet f (c: char) =\n    let mutable result = \"\"\n    result <- result + \"\\\\\" + string c\n    result"

    Assert.Empty(PathSeparator.find tree sourceText)

[<Fact>]
let ``FR0081: a trailing separator is not a join`` () : unit =
    // Path.Combine cannot append a trailing marker, so this is not advice
    let tree, sourceText =
        parse "module Test\nopen System.IO\nlet f (dir: string) = Path.GetFileName(dir) + \"/\""

    Assert.Empty(PathSeparator.find tree sourceText)

[<Fact>]
let ``FR0081: a real path join still fires`` () : unit =
    let tree, sourceText =
        parse "module Test\nlet f (rootDir: string) (fileName: string) = rootDir + \"/\" + fileName"

    Assert.Single(PathSeparator.find tree sourceText) |> ignore

[<Fact>]
let ``FR0081: a web route is not a filesystem path`` () : unit =
    // corpus find: "/img/userimages/" + fileId is a URL, and Path.Combine
    // would turn it into backslashes. `fileId` matching "file" is too weak
    // to call a leading-slash literal a filesystem path
    let tree, sourceText =
        parse "module Test\nlet f (fileId: string) = \"/img/userimages/\" + fileId"

    Assert.Empty(PathSeparator.find tree sourceText)

[<Fact>]
let ``FR0081: a rooted literal is still strong enough`` () : unit =
    let tree, sourceText =
        parse "module Test\nlet f (name: string) = \"./data/\" + name + \".json\""

    Assert.Single(PathSeparator.find tree sourceText) |> ignore

[<Fact>]
let ``FR0016: Struct goes below the doc comment, not above it`` () : unit =
    // corpus find: a declaration's range starts at its XML doc, so
    // inserting at the range start put the attribute above the /// lines
    let source =
        "module Test\n/// A shape.\ntype private Shape =\n    | Circle of radius: float\n    | Square of side: float"

    let tree, sourceText = parse source

    match StructDu.find false tree sourceText with
    | [ s ] ->
        let patched = applyEdit source s.InsertRange s.InsertText

        Assert.Equal(
            "module Test\n/// A shape.\n[<Struct>]\ntype private Shape =\n    | Circle of radius: float\n    | Square of side: float",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one struct-DU suggestion, got %A" other

[<Fact>]
let ``FR0011: return Struct goes below the doc comment too`` () : unit =
    let source =
        "/// Matches even numbers.\nlet private (|Even|_|) (n: int) = if n % 2 = 0 then Some n else None\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

    let tree, sourceText, check = parseAndCheck source

    match StructActivePattern.find false tree sourceText check with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
            |> List.fold (fun acc e -> applyEdit acc e.Range e.Replacement) source

        Assert.StartsWith("/// Matches even numbers.\n[<return: Struct>]\nlet private (|Even|_|)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one struct active pattern, got %A" other

[<Fact>]
let ``a struct DU needs same-named fields to agree on type`` () : unit =
    // FS3585: `A of value: float | B of value: int` refuses [<Struct>]
    let tree, sourceText =
        parse
            "module Test\nmodule private Impl =\n    type Mixed =\n        | A of value: float\n        | B of value: int"

    Assert.Empty(StructDu.find false tree sourceText)

[<Fact>]
let ``same-named fields of one type still take the attribute`` () : unit =
    let tree, sourceText =
        parse
            "module Test\nmodule private Impl =\n    type Same =\n        | A of value: int\n        | B of value: int"

    match StructDu.find false tree sourceText with
    | [ s ] -> Assert.Equal("Same", s.TypeName)
    | other -> failwithf "Expected exactly one struct suggestion, got %A" other

[<Fact>]
let ``FR0008: an active pattern's tuple input is not curried`` () : unit =
    // `(|Both|One|) (xs, names)` takes ONE input, matched as `Both pairs` on
    // a tuple; curried it would expect an expression argument
    // (FsAutoComplete's ConvertPositionalDUToNamed)
    let source =
        "module Test\nlet private (|Both|One|) (xs: int list, names: string list) =\n    if xs.Length = names.Length then Both(List.zip xs names) else One xs\nlet f (xs: int list) (names: string list) =\n    match (xs, names) with\n    | Both pairs -> pairs.Length\n    | One rest -> rest.Length"

    let tree, sourceText, check = parseAndCheck source
    Assert.Empty(TupleParams.find tree sourceText check)

[<Fact>]
let ``FR0011: an active pattern the file also calls as a function keeps its option`` () : unit =
    // the F# compiler's Spreads.fs: a local (|NestedUpdate|_|) calls the
    // module-level one and matches its result against Some — a struct
    // return would reach that call
    let source =
        "let private (|Even|_|) (n: int) = if n % 2 = 0 then Some n else None\nlet evens (xs: int list) = List.choose (|Even|_|) xs\nlet f x =\n    match x with\n    | Even v -> v\n    | _ -> 0"

    let tree, sourceText, check = parseAndCheck source
    Assert.Empty(StructActivePattern.find false tree sourceText check)
