/// FR0111 ElseIfFlatten, FR0112 EqualityChainToMatch, FR0113 NestedIfMerge,
/// FR0114 PyramidFlip, FR0115 GuardOrder (IfRestructure); FR0147
/// QualifiedNames; FR0133 NameQuoting; FR0130 LiteralConst; FR0062
/// VisibleMutableState, FR0067 CultureParse, FR0068 DuplicateEnumValue
/// (MiscRules); FR0132 CommentDoc; FR0135 LiterateComment; FR0080
/// TabIndentation: the branch shapes and the declaration-level notes.
///
/// FR0062 and FR0067 are notes here, as the CLI reports them: the editor's
/// `private `/`internal ` and InvariantCulture/CurrentCulture alternatives
/// share one zero-width insertion range, which the harness's overlap test
/// would apply together. FR0080 has no shape: a leading tab in code is a
/// compile error (FS1161), so the rule fires only on a file the compiler
/// rejects, and a generated program must typecheck. Its one typechecking
/// trigger — a tabbed line inside a block comment holding a string literal
/// that spells `*)` — was a lexer discrepancy this suite found, fixed since
/// (the rule now reads a string inside a comment as the compiler does).
/// The rule still runs over every program, so the damaged-program property
/// exercises it; a tabbed comment shape keeps it quiet on a clean one.
module FSharp.Refactor.PropertyTests.Families.Branching

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

/// A failing wildcard arm and the base arm it pairs with, typed alike.
let private genGuardArms =
    Gen.elements
        [
            "x", "failwith \"out of range\""
            "Some x", "None"
            "Ok x", "Error \"out of range\""
            "x", "invalidArg \"v\" \"out of range\""
        ]

/// A culture-sensitive Parse, juxtaposed or parenthesised.
let private genParse =
    Gen.elements
        [
            "Double.Parse s"
            "DateTime.Parse(s)"
            "System.Decimal.Parse s"
            "Single.Parse(s)"
        ]

let private shapes =
    [
        // FR0111: an else holding a whole if, on its own line
        withFree "ElseIf" [ "FR0111" ] genSmall (fun n i ->
            $"let f{i} (x: int) (y: int) =\n    if x = {n} then\n        0\n    else\n        if y = 2 then\n            1\n        else 2")
        // FR0111: the if on the else's own line
        withFree "ElseIfSameLine" [ "FR0111" ] genSmall (fun n i ->
            $"let f{i} (x: int) (y: int) =\n    if x = {n} then\n        0\n    else if y = 2 then\n        1\n    else 2")
        // FR0112: one identifier against distinct int literals
        withFree "IntChain" [ "FR0112" ] (Gen.zip genSmall genWord) (fun (n, w) i ->
            $"let f{i} (x: int) =\n    if x = {n} then \"{w}\"\n    elif x = {n + 1} then \"b\"\n    else \"c\"")
        // FR0112: string literals, three arms
        withFree "StringChain" [ "FR0112" ] genWord (fun w i ->
            $"let f{i} (s: string) =\n    if s = \"{w}\" then 1\n    elif s = \"Xml\" then 2\n    elif s = \"Csv\" then 3\n    else 0")
        // FR0113: same else on both levels, multi-line
        withFree "NestedSameElse" [ "FR0113" ] genSmall (fun n i ->
            $"let f{i} (x: int) (y: int) =\n    if x = 1 then\n        if y = 2 then {n} else 3\n    else 3")
        // FR0113: the single-line form with an or-condition outside
        withFree "NestedSameElseOr" [ "FR0113" ] genSmall (fun n i ->
            $"let f{i} (x: int) (y: int) = if x = 1 || x = {n} then (if y = 2 then 1 else 9) else 9")
        // FR0113: no else anywhere, unit result
        withFree "NestedUnit" [ "FR0113" ] genSmall (fun n i ->
            $"let f{i} (x: int) (y: int) (g: int -> unit) =\n    if x = 1 then\n        if y = 2 then g {n}")
        // FR0114: a then-branch of twenty-plus lines behind a one-line else
        withFree "PyramidFlip" [ "FR0114" ] (Gen.zip (Gen.choose (20, 24)) genSmall) (fun (lines, n) i ->
            let body =
                [ for k in 1..lines -> $"        let v{k} = {k}" ]
                @ [ $"        v1 + v{lines}" ]
                |> String.concat "\n"

            $"let f{i} (x: int) =\n    if x = {n} then\n{body}\n    else\n        0")
        // FR0114: an already negated condition unwraps
        withFree "PyramidFlipNot" [ "FR0114" ] (Gen.choose (20, 24)) (fun lines i ->
            let body =
                [ for k in 1..lines -> $"        let v{k} = {k}" ]
                @ [ $"        v1 + v{lines}" ]
                |> String.concat "\n"

            $"let f{i} (x: int) =\n    if not (x = 1) then\n{body}\n    else\n        0")
        // FR0115: the base case first behind a compound guard, then a failing wildcard
        withFree "GuardOrder" [ "FR0115" ] genGuardArms (fun (base', err) i ->
            $"let f{i} (v: int) (lo: int) (hi: int) =\n    match v with\n    | x when x >= lo && x <= hi -> {base'}\n    | _ -> {err}")
        // FR0147: a three-segment namespace spelled four times earns an open
        // (upper-case suffixes: `an` + `d` spelled the keyword `and`)
        withFree "DeepNamespace" [ "FR0147" ] genWord (fun w i ->
            $"let f{i} () =\n    let {w}A = System.Collections.Concurrent.ConcurrentQueue<int>()\n    let {w}B = System.Collections.Concurrent.ConcurrentQueue<int>()\n    let {w}C = System.Collections.Concurrent.ConcurrentQueue<int>()\n    let {w}D = System.Collections.Concurrent.ConcurrentQueue<int>()\n    {w}A.Count + {w}B.Count + {w}C.Count + {w}D.Count")
        // FR0147: a namespace the module already opens only gets its use shortened
        withFree "OpenedNamespace" [ "FR0147" ] genSmall (fun n i ->
            $"let v{i} = System.Threading.Tasks.Task.FromResult {n}")
        // FR0133: a test-attributed private five-word name; TestCaseSource is
        // the one test attribute the shared test-file marker does not read,
        // so FR0132's shapes keep firing in the same program
        withFree "TestName" [ "FR0133" ] genWord (fun w i ->
            $"module M{i} =\n    type TestCaseSourceAttribute() =\n        inherit System.Attribute()\n\n    [<TestCaseSource>]\n    let private checkThatRatesRoundCorrectly{i} () = ignore \"{w}\"")
        // FR0130: a private module-level constant, an int or a string
        withFree
            "PrivateConst"
            [ "FR0130" ]
            (Gen.oneof [ Gen.map string genSmall; Gen.map (fun w -> $"\"{w}\"") genWord ])
            (fun literal i -> $"let private Konst{i} = {literal}")
        // FR0062: a public mutable the module writes twice
        withFree "PublicMutable" [ "FR0062" ] genSmall (fun n i ->
            $"module State{i} =\n    let mutable counter{i} = {n}\n    let bump{i} () = counter{i} <- counter{i} + 1")
        // FR0067: a culture-sensitive Parse without a culture
        withFree "CulturelessParse" [ "FR0067" ] genParse (fun call i -> $"let f{i} (s: string) = {call}")
        // FR0068: two enum cases with one value
        withFree "DuplicateEnum" [ "FR0068" ] genSmall (fun n i ->
            $"type E{i} =\n    | Alpha = {n}\n    | Beta = {n + 1}\n    | Gamma = {n}")
        // FR0132: a public binding's trailing comment
        withFree "TrailingCommentLet" [ "FR0132" ] genWord (fun w i ->
            $"let f{i} (r: int) = r * 2 // doubles the rate for the {w}")
        // FR0132: a public type's trailing comment
        withFree "TrailingCommentType" [ "FR0132" ] genWord (fun w i ->
            $"type R{i} = {{ X{i}: int }} // the record of the module {w}")
        // FR0132: a union case's trailing comment
        withFree "TrailingCommentCase" [ "FR0132" ] genWord (fun w i ->
            $"type U{i} =\n    | A{i} of int // the case of the union {w}\n    | B{i}")
        // FR0135: a block comment carrying a markdown heading or fence
        withFree "LiterateBlock" [ "FR0135" ] (Gen.zip genWord (Gen.elements [ true; false ])) (fun (w, fence) i ->
            let body =
                if fence then
                    $"```fsharp\nlet {w} = 1\n```"
                else
                    $"### Setup {w}"

            $"(*\n{body}\n*)\nlet v{i} = 3")
        // FR0080 must stay quiet: the compiler reads the string literal inside
        // the comment as a string and stays in the comment, so the tabbed line
        // is prose; the rule once read it as code (found by this suite)
        withFree "TabInCommentedString" [ "!FR0080" ] genSmall (fun n i ->
            $"(* \"*)\" '\"'\n\tlet tabbed = {n}\n*)\nlet v{i} = {n}")
    ]

let family: Family =
    {
        Name = "Branching"
        Shapes = shapes
        Edits =
            fun c ->
                let ifs = IfRestructure.findElseIf c.Tree c.Source
                let chains = IfRestructure.findEqualityChains c.Tree c.Source c.Check
                let merges = IfRestructure.findNestedIfMerges c.Tree c.Source
                let flips = IfRestructure.findPyramidFlips 20 3 c.Tree c.Source

                // a namespace whose open would clash is a note (see Notes)
                let qualified =
                    QualifiedNames.find 6 4 c.Tree c.Source c.Check
                    |> List.filter (fun s -> not s.Edits.IsEmpty)

                let quoted = NameQuoting.find false c.Tree c.Source c.Check None

                let literals =
                    LiteralConst.findWith (fun _ -> false) (Visibility.apiChangesAllowed ()) c.Tree c.Source

                let docs = CommentDoc.find c.Tree c.Source
                let literate = LiterateComment.find c.Tree c.Source
                let tabs = TabIndentation.find "Test.fsx" c.Source

                [
                    for s in flips -> "FR0114", [ edit "FR0114" s.Range s.ReplacementText ]
                    for s in ifs -> "FR0111", [ edit "FR0111" s.Range s.ReplacementText ]
                    for s in chains -> "FR0112", [ edit "FR0112" s.Range s.ReplacementText ]
                    for s in merges -> "FR0113", [ edit "FR0113" s.Range s.ReplacementText ]
                    for s in qualified -> "FR0147", [ for r, _, t in s.Edits -> edit "FR0147" r t ]
                    for s in quoted -> "FR0133", [ for r, _, t in s.Edits -> edit "FR0133" r t ]
                    for s in literals ->
                        "FR0130",
                        edit "FR0130" (fst s.Fix) (snd s.Fix)
                        :: [ for r, _, t in s.SignatureEdits -> edit "FR0130" r t ]
                    for s in docs -> "FR0132", [ for r, _, t in s.Edits -> edit "FR0132" r t ]
                    for s in literate -> "FR0135", [ edit "FR0135" (fst s.Fix) (snd s.Fix) ]
                    for s in tabs -> "FR0080", [ for r, _, t in s.Edits -> edit "FR0080" r t ]
                ]
        Notes =
            fun c ->
                let mutables, parses, enums = MiscRules.find c.Tree c.Source

                let clashing =
                    QualifiedNames.find 6 4 c.Tree c.Source c.Check
                    |> List.filter (fun s -> s.Edits.IsEmpty)

                [
                    for s in IfRestructure.findGuardOrderNotes c.Tree c.Source -> "FR0115", s.Range
                    for s in clashing -> "FR0147", s.Range
                    for s in mutables -> "FR0062", s.Range
                    for s in parses -> "FR0067", s.Range
                    for s in enums -> "FR0068", s.Range
                ]
    }
