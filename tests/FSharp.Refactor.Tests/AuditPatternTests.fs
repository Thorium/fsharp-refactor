/// Audit fixes for the pattern/option/rec-group rules (report 09):
///   B2  FR0002/FR0010 `.IsSome`/`.IsNone` only on a receiver whose type is
///       settled before the lookup (positive evidence; else the module form)
///   B3  FR0116 sibling references inside interpolation holes and after a
///       `'"'` char literal are seen
///   B12 FR0006/FR0116 `#if`-wrapped insertions carry the declaration's
///       indentation, the directives at column 0
module FSharp.Refactor.Tests.AuditPatternTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- B2: the property form needs a settled receiver ----

let private optionMatchesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionModule.find tree sourceText checkResults

let private simplificationsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Simplification.find tree sourceText (Some checkResults)

let private assertOptionMatch (source: string) (expectedTarget: string) (expectedReplacement: string) =
    match optionMatchesIn source with
    | [ s ] ->
        Assert.Equal(expectedTarget, s.Target)
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertSimplification (source: string) (expectedReplacement: string) =
    match simplificationsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``B2: a for variable keeps the module form`` () =
    // `o` is typed by `xs`, whose type is inferred from this very use:
    // `o.IsSome` is FS0072 "lookup on object of indeterminate type"
    Assert.Empty(
        simplificationsIn
            "let anyPresent xs =\n    let mutable found = false\n    for o in xs do\n        if Option.isSome o then found <- true\n    found"
    )

    assertSimplification
        "let anyPresent xs =\n    let mutable found = false\n    for o in xs do\n        if o <> None then found <- true\n    found"
        "o |> Option.isSome"

[<Fact>]
let ``B2: a let bound to a generic projection keeps the module form`` () =
    // 0.8.2 gave `a |> Option.isSome`; `fst` returns a bare type parameter
    assertSimplification "let pick y = let a = fst y in a <> None" "a |> Option.isSome"

[<Fact>]
let ``B2: a primary-constructor parameter keeps the module form`` () =
    assertOptionMatch
        "type Holder(x) =\n    member _.Present = match x with | Some _ -> true | None -> false"
        "Option.isSome"
        "x |> Option.isSome"

[<Fact>]
let ``B2: a match-bound name keeps the module form`` () =
    assertOptionMatch
        "let firstSet ys =\n    match ys with\n    | o :: _ -> (match o with | Some _ -> true | None -> false)\n    | [] -> false"
        "Option.isSome"
        "o |> Option.isSome"

[<Fact>]
let ``B2: a tuple-destructured let keeps the module form`` () =
    assertSimplification "let f (y: int option * int) =\n    let (a, _) = y\n    a <> None" "a |> Option.isSome"

[<Fact>]
let ``B2: an annotated parameter still takes the property`` () =
    assertSimplification "let f (x: int option) = Option.isSome x" "x.IsSome"
    assertSimplification "let f (x: int option) = x <> None" "x.IsSome"

    assertOptionMatch "let f (x: int option) = match x with | Some _ -> true | None -> false" "Option.isSome" "x.IsSome"

[<Fact>]
let ``B2: a let settled by its right-hand side still takes the property`` () =
    assertSimplification "let f (n: int) =\n    let x = if n > 0 then Some n else None\n    Option.isNone x" "x.IsNone"

    // the declared return type of List.tryFind is an option whatever the
    // element type turns out to be
    assertSimplification "let f ys =\n    let a = List.tryFind (fun v -> v > 0) ys\n    a <> None" "a.IsSome"

[<Fact>]
let ``B2: a record field on a settled root still takes the property`` () =
    assertSimplification "type R = { Age: int option }\nlet f (r: R) = Option.isSome r.Age" "r.Age.IsSome"

[<Fact>]
let ``B2: a module-level value read from a later declaration takes the property`` () =
    assertSimplification "let cfg = Some 1\nlet f () = Option.isSome cfg" "cfg.IsSome"

// ---- B3: RecGroup sees references inside holes and past char literals ----

let private recGroupsIn (source: string) =
    let tree, sourceText = parse source
    RecGroup.find None tree sourceText

let private applyExtraction (source: string) (s: RecGroup.Suggestion) =
    // remove first (later range), then insert at the group's start
    let patched = applyEdit source s.RemoveRange ""
    applyEdit patched s.InsertRange s.InsertText

[<Fact>]
let ``B3: a sibling called inside an interpolation hole keeps the member in the group`` () =
    // extracted above `size`, `describe` would not compile (FS0039)
    Assert.Empty(
        recGroupsIn
            "module Test\nlet rec size n = if n = 0 then 0 else 1 + size (n - 1)\nand describe n = $\"size is {size n}\""
    )

[<Fact>]
let ``B3: a char literal quote does not hide the self-call after it`` () =
    // `'"'` opened a phantom string that ran to the failwith message,
    // blanking the recursive call in between: the member left as `let`
    let source =
        "module Test\n"
        + "let rec lexToken (cs: char list) : string * char list =\n"
        + "    match cs with\n"
        + "    | '\"' :: rest -> lexString \"\" rest\n"
        + "    | _ -> \"\", cs\n"
        + "and lexString (acc: string) (cs: char list) : string * char list =\n"
        + "    match cs with\n"
        + "    | '\"' :: rest -> acc, rest\n"
        + "    | c :: rest -> lexString (acc + string c) rest\n"
        + "    | [] -> failwith \"unterminated string\""

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("lexString", s.MemberName)
        Assert.True s.IsSelfRecursive
        Assert.StartsWith("let rec lexString", s.InsertText)
        let patched = applyExtraction source s
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one rec extraction, got %A" other

[<Fact>]
let ``B3: a name in an interpolated string's text is still no reference`` () =
    let source =
        "module Test\nlet rec run (n: int) : int = if n = 0 then 0 else helper n\nand helper (n: int) : int = if n < 0 then failwith $\"helper: negative {n}\" else n - 1"

    match recGroupsIn source with
    | [ s ] ->
        Assert.False s.IsSelfRecursive
        Assert.StartsWith("let helper", s.InsertText)
        let patched = applyExtraction source s
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

// ---- B12: `#if`-wrapped insertions inside an indented module ----

[<Fact>]
let ``B12: an active pattern under #if carries the module's indentation`` () =
    let source =
        "namespace N\nmodule M =\n    let isBig (i: int) = i > 10\n    let f i =\n        match i with\n#if !FABLE_COMPILER\n        | x when isBig x -> x\n#endif\n        | _ -> 0"

    let tree, sourceText, checkResults = parseAndCheck source

    match ActivePattern.find true tree sourceText checkResults with
    | [ s ] ->
        let patched = applyEdit source s.ClauseRange s.ClauseText
        let patched = applyEdit patched s.InsertRange s.InsertText

        Assert.Equal(
            "namespace N\nmodule M =\n    let isBig (i: int) = i > 10\n#if !FABLE_COMPILER\n    [<return: Struct>]\n    let inline private (|IsBig|_|) input =\n        if isBig input then ValueSome input else ValueNone\n#endif\n\n    let f i =\n        match i with\n#if !FABLE_COMPILER\n        | IsBig x -> x\n#endif\n        | _ -> 0",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``B12: a rec group member under #if carries the module's indentation`` () =
    let source =
        "namespace N\nmodule M =\n    let rec f (x: int) : int = if x = 0 then 0 else g x\n#if !FOO\n    and g (y: int) : int = y + 1\n#endif"

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("g", s.MemberName)
        Assert.Equal(0, s.InsertRange.StartColumn)
        Assert.Equal("#if !FOO\n    let g (y: int) : int = y + 1\n#endif\n\n", s.InsertText)
        let patched = applyExtraction source s

        Assert.Equal(
            "namespace N\nmodule M =\n#if !FOO\n    let g (y: int) : int = y + 1\n#endif\n\n    let rec f (x: int) : int = if x = 0 then 0 else g x\n#if !FOO\n    \n#endif",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``B12: an unconditioned extraction still rides on the group's indentation`` () =
    let source =
        "namespace N\nmodule M =\n    let rec f (x: int) : int = if x = 0 then 0 else g x\n    and g (y: int) : int = y + 1"

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal(4, s.InsertRange.StartColumn)
        Assert.Equal("let g (y: int) : int = y + 1\n\n    ", s.InsertText)
        let patched = applyExtraction source s
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one extraction, got %A" other
