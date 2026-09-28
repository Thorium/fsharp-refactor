/// Guards for the pattern/option/rec-group rules:
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertSimplification (source: string) (expectedReplacement: string) =
    match simplificationsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``B2: a for variable keeps the module form`` () =
    // `o` is typed by `xs`, whose type is inferred from this very use:
    // `o.IsSome` is FS0072 "lookup on object of indeterminate type"
    Assert.Empty(
        simplificationsIn (
            fsharp
                """
                let anyPresent xs =
                    let mutable found = false
                    for o in xs do
                        if Option.isSome o then found <- true
                    found
                """
        )
    )

    assertSimplification
        (fsharp
            """
            let anyPresent xs =
                let mutable found = false
                for o in xs do
                    if o <> None then found <- true
                found
            """)
        "o |> Option.isSome"

[<Fact>]
let ``B2: a let bound to a generic projection keeps the module form`` () =
    // `fst` returns a bare type parameter: no settled receiver for `.IsSome`
    assertSimplification "let pick y = let a = fst y in a <> None" "a |> Option.isSome"

[<Fact>]
let ``B2: a primary-constructor parameter keeps the module form`` () =
    assertOptionMatch
        (fsharp
            """
            type Holder(x) =
                member _.Present = match x with | Some _ -> true | None -> false
            """)
        "Option.isSome"
        "x |> Option.isSome"

[<Fact>]
let ``B2: a match-bound name keeps the module form`` () =
    assertOptionMatch
        (fsharp
            """
            let firstSet ys =
                match ys with
                | o :: _ -> (match o with | Some _ -> true | None -> false)
                | [] -> false
            """)
        "Option.isSome"
        "o |> Option.isSome"

[<Fact>]
let ``B2: a tuple-destructured let keeps the module form`` () =
    assertSimplification
        (fsharp
            """
            let f (y: int option * int) =
                let (a, _) = y
                a <> None
            """)
        "a |> Option.isSome"

[<Fact>]
let ``B2: an annotated parameter still takes the property`` () =
    assertSimplification "let f (x: int option) = Option.isSome x" "x.IsSome"
    assertSimplification "let f (x: int option) = x <> None" "x.IsSome"

    assertOptionMatch "let f (x: int option) = match x with | Some _ -> true | None -> false" "Option.isSome" "x.IsSome"

[<Fact>]
let ``B2: a let settled by its right-hand side still takes the property`` () =
    assertSimplification
        (fsharp
            """
            let f (n: int) =
                let x = if n > 0 then Some n else None
                Option.isNone x
            """)
        "x.IsNone"

    // the declared return type of List.tryFind is an option whatever the
    // element type turns out to be
    assertSimplification
        (fsharp
            """
            let f ys =
                let a = List.tryFind (fun v -> v > 0) ys
                a <> None
            """)
        "a.IsSome"

[<Fact>]
let ``B2: a record field on a settled root still takes the property`` () =
    assertSimplification
        (fsharp
            """
            type R = { Age: int option }
            let f (r: R) = Option.isSome r.Age
            """)
        "r.Age.IsSome"

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
        recGroupsIn (
            fsharp
                """
                module Test
                let rec size n = if n = 0 then 0 else 1 + size (n - 1)
                and describe n = $"size is {size n}"
                """
        )
    )

[<Fact>]
let ``B3: a char literal quote does not hide the self-call after it`` () =
    // read as a string opener, `'"'` would run a phantom string to the
    // failwith message, blanking the recursive call in between: the member
    // would leave the group as `let`
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one rec extraction, got %A" other

[<Fact>]
let ``B3: a name in an interpolated string's text is still no reference`` () =
    let source =
        fsharp
            """
            module Test
            let rec run (n: int) : int = if n = 0 then 0 else helper n
            and helper (n: int) : int = if n < 0 then failwith $"helper: negative {n}" else n - 1
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.False s.IsSelfRecursive
        Assert.StartsWith("let helper", s.InsertText)
        let patched = applyExtraction source s
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

// ---- B12: `#if`-wrapped insertions inside an indented module ----

[<Fact>]
let ``B12: an active pattern under #if carries the module's indentation`` () =
    let source =
        fsharp
            """
            namespace N
            module M =
                let isBig (i: int) = i > 10
                let f i =
                    match i with
            #if !FABLE_COMPILER
                    | x when isBig x -> x
            #endif
                    | _ -> 0
            """

    let tree, sourceText, checkResults = parseAndCheck source

    match ActivePattern.find true tree sourceText checkResults with
    | [ s ] ->
        let patched = applyEdit source s.ClauseRange s.ClauseText
        let patched = applyEdit patched s.InsertRange s.InsertText

        Assert.Equal(
            fsharp
                """
                namespace N
                module M =
                    let isBig (i: int) = i > 10
                #if !FABLE_COMPILER
                    [<return: Struct>]
                    let inline private (|IsBig|_|) input =
                        if isBig input then ValueSome input else ValueNone
                #endif

                    let f i =
                        match i with
                #if !FABLE_COMPILER
                        | IsBig x -> x
                #endif
                        | _ -> 0
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``B12: a rec group member under #if carries the module's indentation`` () =
    let source =
        fsharp
            """
            namespace N
            module M =
                let rec f (x: int) : int = if x = 0 then 0 else g x
            #if !FOO
                and g (y: int) : int = y + 1
            #endif
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal("g", s.MemberName)
        Assert.Equal(0, s.InsertRange.StartColumn)

        Assert.Equal(
            fsharp
                """
                #if !FOO
                    let g (y: int) : int = y + 1
                #endif


                """,
            s.InsertText
        )

        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                namespace N
                module M =
                #if !FOO
                    let g (y: int) : int = y + 1
                #endif

                    let rec f (x: int) : int = if x = 0 then 0 else g x
                #if !FOO

                #endif
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``B12: an unconditioned extraction still rides on the group's indentation`` () =
    let source =
        fsharp
            """
            namespace N
            module M =
                let rec f (x: int) : int = if x = 0 then 0 else g x
                and g (y: int) : int = y + 1
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal(4, s.InsertRange.StartColumn)
        Assert.Equal("let g (y: int) : int = y + 1\n\n    ", s.InsertText)
        let patched = applyExtraction source s
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

// ---- FR0116: every leaver in one pass, comments along, no whitespace tail ----

[<Fact>]
let ``every member that can leave goes in one pass, in dependency order`` () =
    // `h` calls `g`, which leaves in the first wave; `h` follows it above
    // the group, so the order compiles. Adjacent blocks merge into one
    // removal
    let source =
        fsharp
            """
            module Test
            let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x
            and g (y: int) : int = y + 1
            and h (z: int) : int = g z * 2
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal<(string * bool) list>([ "g", false; "h", false ], s.Members)
        Assert.Equal(1, s.Removes.Length)

        Assert.Equal(
            fsharp
                """
                let g (y: int) : int = y + 1

                let h (z: int) : int = g z * 2


                """,
            s.InsertText
        )

        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                module Test
                let g (y: int) : int = y + 1

                let h (z: int) : int = g z * 2

                let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``the last member leaves no whitespace-only line behind`` () =
    // a removed block that begins after the line's indentation leaves that
    // indentation behind as a line of spaces
    let source =
        fsharp
            """
            namespace N
            module M =
                let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x

                and g (y: int) : int = y + 1
            """

    match recGroupsIn source with
    | [ s ] ->
        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                namespace N
                module M =
                    let g (y: int) : int = y + 1

                    let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a plain comment directly above the member travels with it`` () =
    // left behind, `// REVIEW ...` would head whatever binding came next
    let source =
        fsharp
            """
            module Test
            let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x
            // REVIEW: write into an accumulating buffer
            and g (y: int) : int = y + 1
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.StartsWith(
            fsharp
                """
                // REVIEW: write into an accumulating buffer
                let g
                """,
            s.InsertText
        )

        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                module Test
                // REVIEW: write into an accumulating buffer
                let g (y: int) : int = y + 1

                let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a commented member and the plain last member leave as one removal`` () =
    // the comment-extended block ends at column 0 of the last member's
    // line; as two removals the second's tail trim would reach back into
    // the first and the edits overlap
    let source =
        fsharp
            """
            namespace N
            module M =
                let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x
                // g's note
                and g (y: int) : int = y + 1
                and h (z: int) : int = z * 2
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal(1, s.Removes.Length)
        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                namespace N
                module M =
                    // g's note
                    let g (y: int) : int = y + 1

                    let h (z: int) : int = z * 2

                    let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a member referencing a sibling under #if waits for it`` () =
    // g leaves alone on its own pass (it is last, so its block spans no directive); h references it and must wait, or it would sit above the group with g still below
    let source =
        fsharp
            """
            module Test
            let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x
            and h (z: int) : int = g z * 2
            #if !FOO
            and g (y: int) : int = y + 1
            #endif
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal<(string * bool) list>([ "g", false ], s.Members)

        Assert.StartsWith(
            fsharp
                """
                #if !FOO
                let g
                """,
            s.InsertText
        )
    | other -> failwithf "Expected one extraction, got %A" other

[<Fact>]
let ``a merged removal headed by a comment ends at column 0 before a staying member`` () =
    // a comment-extended head merged with the plain blocks after it must
    // not end at the next `and`'s column, or that `and` is left at the
    // margin
    let source =
        fsharp
            """
            namespace N
            module M =
                let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x + k x
                // g's note
                and g (y: int) : int = y + 1
                and h (z: int) : int = g z * 2
                and k (w: int) : int = f w + 1
            """

    match recGroupsIn source with
    | [ s ] ->
        Assert.Equal<(string * bool) list>([ "g", false; "h", false ], s.Members)
        let patched = applyExtraction source s

        Assert.Equal(
            fsharp
                """
                namespace N
                module M =
                    // g's note
                    let g (y: int) : int = y + 1

                    let h (z: int) : int = g z * 2

                    let rec f (x: int) : int = if x = 0 then 0 else f (x - 1) + g x + h x + k x
                    and k (w: int) : int = f w + 1
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one extraction, got %A" other
