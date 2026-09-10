[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.QualityRulesTests
// the FR0125 fixtures below carry REAL invisible characters on purpose
// fsharpanalyzer: ignore-file FR0125

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open System.IO

// ---- FR0061 ArgNames ----

let private argNamesIn (source: string) =
    let tree, sourceText = parse source
    ArgNames.find tree sourceText

[<Fact>]
let ``a misspelled invalidArg name is noted`` () =
    match
        argNamesIn
            "module Test\nlet scale (value: int) (factor: int) =\n    if factor = 0 then invalidArg \"facotr\" \"zero\"\n    value * factor"
    with
    | [ s ] ->
        Assert.Equal("facotr", s.UsedName)
        Assert.Equal<string list>([ "value"; "factor" ], s.ParameterNames)
    | other -> failwithf "Expected exactly one arg-name note, got %A" other

[<Fact>]
let ``a correct ArgumentNullException name is fine`` () =
    Assert.Empty(
        argNamesIn
            "module Test\nlet f (input: string) =\n    if isNull input then raise (System.ArgumentNullException \"input\")\n    input.Length"
    )

[<Fact>]
let ``ArgumentException second argument is the parameter name`` () =
    match
        argNamesIn
            "module Test\nlet f (input: string) =\n    if input = \"\" then raise (System.ArgumentException(\"empty\", \"inptu\"))\n    input.Length"
    with
    | [ s ] -> Assert.Equal("inptu", s.UsedName)
    | other -> failwithf "Expected exactly one ctor arg-name note, got %A" other

[<Fact>]
let ``a CLI flag name is not a parameter reference`` () =
    // "--mode" can never BE an F# parameter name; the author is naming an
    // external concept, not referencing the signature
    Assert.Empty(
        argNamesIn
            "module Test\nlet run (args: string list) =\n    if args.IsEmpty then invalidArg \"--mode\" \"missing\"\n    args.Length"
    )

[<Fact>]
let ``a custom operation validates its DSL operand name`` () =
    Assert.Empty(
        argNamesIn
            "module Test\ntype Cfg() =\n    member _.Yield(_: unit) = 0\n    [<CustomOperation \"vpc\">]\n    member _.Vpc(state: int) =\n        if state < 0 then invalidArg \"vpc\" \"bad\"\n        state"
    )

// ---- FR0063 / FR0064 ExceptionRules ----

let private exceptionsIn (source: string) =
    let tree, sourceText = parse source
    ExceptionRules.find tree sourceText

[<Fact>]
let ``raise inside finally is noted`` () =
    let finallies, _ =
        exceptionsIn
            "module Test\nlet f (act: unit -> int) (cleanup: unit -> unit) =\n    try\n        act ()\n    finally\n        cleanup ()\n        failwith \"cleanup failed\""

    Assert.Single finallies |> ignore

[<Fact>]
let ``a finally that only cleans up is fine`` () =
    let finallies, _ =
        exceptionsIn
            "module Test\nlet f (act: unit -> int) (cleanup: unit -> unit) =\n    try\n        act ()\n    finally\n        cleanup ()"

    Assert.Empty finallies

[<Fact>]
let ``raising a reserved runtime exception is noted`` () =
    let _, reserved =
        exceptionsIn "module Test\nlet f () = raise (System.IndexOutOfRangeException \"custom\")"

    match reserved with
    | [ s ] -> Assert.Equal("IndexOutOfRangeException", s.TypeName)
    | other -> failwithf "Expected exactly one reserved-exception note, got %A" other

[<Fact>]
let ``ordinary exceptions raise freely`` () =
    let _, reserved =
        exceptionsIn "module Test\nlet f () = raise (System.InvalidOperationException \"bad state\")"

    Assert.Empty reserved

[<Fact>]
let ``FR0064: a match raising three or more distinct exceptions is a dispatch table`` () =
    // FCS `SimulateException`: fault injection raises OutOfMemory,
    // AccessViolation, IndexOutOfRange... one per arm, by request
    let _, reserved =
        exceptionsIn
            "module Test\nopen System\nlet simulate (config: string option) =\n    match config with\n    | Some \"oom\" -> raise (OutOfMemoryException())\n    | Some \"av\" -> raise (AccessViolationException())\n    | Some \"ior\" -> raise (IndexOutOfRangeException())\n    | Some \"fail\" -> failwith \"simulated\"\n    | _ -> ()"

    Assert.Empty reserved

[<Fact>]
let ``FR0064: two arms raising the same reserved type are no table`` () =
    // illib's Array.replace stays true: one IndexOutOfRange where an
    // ArgumentOutOfRange was meant
    let _, reserved =
        exceptionsIn
            "module Test\nopen System\nlet f (index: int) (arr: int[]) =\n    match index with\n    | i when i < 0 -> raise (IndexOutOfRangeException \"index\")\n    | i when i >= arr.Length -> raise (IndexOutOfRangeException \"index\")\n    | i -> arr.[i]"

    Assert.Equal(2, reserved.Length)

// ---- FR0065 / FR0066 SecurityRules ----

let private securityIn (source: string) =
    let tree, sourceText = parse source
    SecurityRules.find tree sourceText (fun _ -> false)

[<Fact>]
let ``MD5 Create is noted as weak`` () =
    let crypto, _, _ =
        securityIn "module Test\nlet hash () = System.Security.Cryptography.MD5.Create()"

    match crypto with
    | [ s ] -> Assert.Equal(SecurityRules.WeakKind.Hash "MD5", s.Kind)
    | other -> failwithf "Expected exactly one weak-hash note, got %A" other

[<Fact>]
let ``SHA256 is fine`` () =
    let crypto, _, _ =
        securityIn "module Test\nlet hash () = System.Security.Cryptography.SHA256.Create()"

    Assert.Empty crypto

[<Fact>]
let ``interpolated CommandText is noted`` () =
    let _, sql, _ =
        securityIn
            "module Test\nlet q (cmd: obj) (setText: string -> unit) (name: string) =\n    setText $\"select * from users where name = '{name}'\""

    // setText is a function, not CommandText — nothing fires
    Assert.Empty sql

[<Fact>]
let ``CommandText assignment from interpolation is noted`` () =
    let _, sql, _ =
        securityIn
            "module Test\ntype Cmd() =\n    member val CommandText = \"\" with get, set\nlet q (cmd: Cmd) (name: string) = cmd.CommandText <- $\"select * from t where n = '{name}'\""

    match sql with
    | [ s ] -> Assert.Equal("CommandText", s.Sink)
    | other -> failwithf "Expected exactly one sql note, got %A" other

[<Fact>]
let ``a literal CommandText is fine`` () =
    let _, sql, _ =
        securityIn
            "module Test\ntype Cmd() =\n    member val CommandText = \"\" with get, set\nlet q (cmd: Cmd) = cmd.CommandText <- \"select * from t where n = @n\""

    Assert.Empty sql

// ---- FR0062 / FR0067 / FR0068 MiscRules ----

let private miscIn (source: string) =
    let tree, sourceText = parse source
    MiscRules.find tree sourceText

[<Fact>]
let ``public module-level mutable is noted`` () =
    let mutables, _, _ =
        miscIn "module Test\nlet mutable counter = 0\nlet bump () = counter <- counter + 1"

    match mutables with
    | [ s ] -> Assert.Equal("counter", s.Name)
    | other -> failwithf "Expected exactly one mutable-state note, got %A" other

[<Fact>]
let ``an UPPERCASE public mutable is noted too`` () =
    // a lone uppercase binder parses as a no-argument LongIdent, not Named
    let mutables, _, _ =
        miscIn "module Test\nlet mutable Instance = 0\nlet bump () = Instance <- Instance + 1"

    match mutables with
    | [ s ] -> Assert.Equal("Instance", s.Name)
    | other -> failwithf "Expected exactly one mutable-state note, got %A" other

[<Fact>]
let ``private module-level mutable is a contained decision`` () =
    let mutables, _, _ =
        miscIn "module Test\nlet mutable private counter = 0\nlet bump () = counter <- counter + 1"

    Assert.Empty mutables

[<Fact>]
let ``a mutable inside a private module is confined`` () =
    let mutables, _, _ =
        miscIn "module Test\nmodule private State =\n    let mutable counter = 0"

    Assert.Empty mutables

[<Fact>]
let ``cultureless DateTime Parse is noted`` () =
    let _, parses, _ = miscIn "module Test\nlet f (s: string) = System.DateTime.Parse s"

    match parses with
    | [ s ] -> Assert.Equal("DateTime.Parse", s.CallName)
    | other -> failwithf "Expected exactly one culture note, got %A" other

[<Fact>]
let ``Parse with a culture argument is fine`` () =
    let _, parses, _ =
        miscIn
            "module Test\nlet f (s: string) = System.DateTime.Parse(s, System.Globalization.CultureInfo.InvariantCulture)"

    Assert.Empty parses

[<Fact>]
let ``int Parse is low-risk and not flagged`` () =
    let _, parses, _ = miscIn "module Test\nlet f (s: string) = System.Int32.Parse s"
    Assert.Empty parses

[<Fact>]
let ``duplicate enum values are noted`` () =
    let _, _, enums =
        miscIn "module Test\ntype Color =\n    | Red = 1\n    | Green = 2\n    | Crimson = 1"

    match enums with
    | [ s ] ->
        Assert.Equal("Crimson", s.CaseName)
        Assert.Equal("Red", s.OriginalName)
    | other -> failwithf "Expected exactly one duplicate-enum note, got %A" other

[<Fact>]
let ``distinct enum values are fine`` () =
    let _, _, enums = miscIn "module Test\ntype Color =\n    | Red = 1\n    | Green = 2"
    Assert.Empty enums

[<Fact>]
let ``FR0068: a Flags enum names bits, and a bit under two names is a table`` () =
    // FCS ilnativeres.fs mirrors winnt.h's section characteristics
    let _, _, enums =
        miscIn
            "module Test\n[<System.Flags>]\ntype Section =\n    | TypeReg = 0u\n    | MemProtected = 16384u\n    | NoDeferSpecExc = 16384u\n    | GPRel = 32768u\n    | MemFardata = 32768u"

    Assert.Empty enums

[<Fact>]
let ``FR0068: a zero Default alias declared beside its twin is a synonym`` () =
    // FCS ServiceLexing: `Default = 0 | Text = 0` on a public enum
    let _, _, enums =
        miscIn "module Test\ntype Kind =\n    | Default = 0\n    | Text = 0\n    | Keyword = 1"

    Assert.Empty enums

    // the same pair apart, or a non-zero adjacent pair, is still the slip
    let _, _, apart =
        miscIn "module Test\ntype Kind =\n    | Default = 0\n    | Keyword = 1\n    | Text = 0"

    let _, _, adjacentNonZero =
        miscIn "module Test\ntype Kind =\n    | Keyword = 1\n    | Comment = 2\n    | Blue = 2"

    Assert.Single apart |> ignore
    Assert.Single adjacentNonZero |> ignore

[<Fact>]
let ``a builder Run member validates DSL keywords not parameters`` () =
    Assert.Empty(
        argNamesIn
            "module Test\ntype SgBuilder() =\n    member _.Yield(_: unit) = 0\n    member _.Zero() = 0\n    member _.Run(config: int) =\n        if config < 0 then invalidArg \"vpc\" \"required\"\n        config"
    )

// ---- FR0069 / FR0070 StructHints ----

let private structHintsIn (source: string) =
    let tree, sourceText = parse source
    StructHints.find false tree sourceText

/// The same scan with API changes allowed, as `fsharp-refactor
/// --api-changes` runs it.
let private structHintsWithApiChangesIn (source: string) =
    let tree, sourceText = parse source
    StructHints.find true tree sourceText

[<Fact>]
let ``a public record is offered under api changes`` () =
    let voptions, _, _ =
        structHintsWithApiChangesIn "module Test\ntype Row = { Id: System.Guid option; Name: string }"

    Assert.NotEmpty voptions

[<Fact>]
let ``a struct option field in a private record suggests voption`` () =
    let voptions, _, _ =
        structHintsIn "module Test\ntype private Row = { Id: System.Guid option; Name: string }"

    match voptions with
    | [ s ] ->
        Assert.Equal("Id", s.FieldName)
        Assert.Equal("System.Guid", s.ElementText)
    | other -> failwithf "Expected exactly one voption note, got %A" other

[<Fact>]
let ``a public record keeps its option fields`` () =
    // serialization shapes and call sites are unbounded for public types
    let voptions, _, _ = structHintsIn "module Test\ntype Row = { Id: int option }"
    Assert.Empty voptions

[<Fact>]
let ``a reference payload keeps its option`` () =
    let voptions, _, _ =
        structHintsIn "module Test\ntype private Row = { Name: string option }"

    Assert.Empty voptions

[<Fact>]
let ``a record in a private module is contained`` () =
    let voptions, _, _ =
        structHintsIn "module Test\nmodule private Inner =\n    type Row = { Stamp: System.DateTime option }"

    Assert.Single voptions |> ignore

[<Fact>]
let ``a small all-struct private record suggests Struct`` () =
    let _, structs, _ =
        structHintsIn "module Test\ntype private Point = { X: float; Y: float }"

    match structs with
    | [ s ] ->
        Assert.Equal("Point", s.TypeName)
        Assert.Equal(2, s.FieldCount)
    | other -> failwithf "Expected exactly one struct note, got %A" other

[<Fact>]
let ``five fields are past the struct sweet spot`` () =
    let _, structs, _ =
        structHintsIn "module Test\ntype private Wide = { A: int; B: int; C: int; D: int; E: int }"

    Assert.Empty structs

[<Fact>]
let ``a string field keeps the record on the heap`` () =
    let _, structs, _ =
        structHintsIn "module Test\ntype private Named = { X: int; Name: string }"

    Assert.Empty structs

[<Fact>]
let ``an existing Struct attribute is already done`` () =
    let _, structs, _ =
        structHintsIn "module Test\n[<Struct>]\ntype private Point = { X: float; Y: float }"

    Assert.Empty structs

[<Fact>]
let ``a mutable field would change copy semantics`` () =
    let _, structs, _ =
        structHintsIn "module Test\ntype private Counter = { mutable N: int }"

    Assert.Empty structs

[<Fact>]
let ``a voption field already counts as flat for the struct hint`` () =
    let _, structs, _ =
        structHintsIn "module Test\ntype private Row = { Id: int voption; N: int }"

    Assert.Single structs |> ignore

// ---- FR0071 LoopInvariant ----

let private invariantsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    LoopInvariant.find tree sourceText checkResults

let private assertHoisted (source: string) (expectedPatched: string) =
    match invariantsIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one invariant note, got %A" other

[<Fact>]
let ``an invariant binding hoists out of a for loop`` () =
    assertHoisted
        "let sink (n: int) = ()\nlet run (a: int) =\n    for x = 0 to 100 do\n        let c = a + 3\n        sink (x + c)"
        "let sink (n: int) = ()\nlet run (a: int) =\n    let c = a + 3\n    for x = 0 to 100 do\n        sink (x + c)"

[<Fact>]
let ``an invariant binding hoists out of a foreach loop`` () =
    assertHoisted
        "let sink (n: int) = ()\nlet run (a: int) (xs: int list) =\n    for x in xs do\n        let c = a + 3\n        sink (x + c)"
        "let sink (n: int) = ()\nlet run (a: int) (xs: int list) =\n    let c = a + 3\n    for x in xs do\n        sink (x + c)"

[<Fact>]
let ``an invariant binding hoists out of a map lambda`` () =
    assertHoisted
        "let run (a: int) (xs: int list) =\n    xs\n    |> List.map (fun x ->\n        let c = a + 3\n        x + c)"
        "let run (a: int) (xs: int list) =\n    let c = a + 3\n    xs\n    |> List.map (fun x ->\n        x + c)"

[<Fact>]
let ``a loop-variable-dependent binding stays`` () =
    Assert.Empty(
        invariantsIn
            "let sink (n: int) = ()\nlet run (a: int) =\n    for x = 0 to 100 do\n        let c = a + x\n        sink (x + c)"
    )

[<Fact>]
let ``a function-call binding is not provably pure and stays`` () =
    Assert.Empty(
        invariantsIn
            "let compute (n: int) = n * 2\nlet sink (n: int) = ()\nlet run (a: int) =\n    for x = 0 to 100 do\n        let c = compute a\n        sink (x + c)"
    )

[<Fact>]
let ``a binding reading a variable the loop mutates stays`` () =
    Assert.Empty(
        invariantsIn
            "let sink (n: int) = ()\nlet run (a: int) =\n    let mutable m = a\n    for x = 0 to 100 do\n        let c = m + 3\n        m <- m + 1\n        sink (x + c)"
    )

[<Fact>]
let ``a name used after the loop stays put`` () =
    // hoisting would widen the binding's scope over the later use
    Assert.Empty(
        invariantsIn
            "let sink (n: int) = ()\nlet run (a: int) =\n    let c = 99\n    for x = 0 to 100 do\n        let c = a + 3\n        sink (x + c)\n    sink c"
    )

[<Fact>]
let ``while loops hoist too`` () =
    assertHoisted
        "let sink (n: int) = ()\nlet run (a: int) (keep: unit -> bool) =\n    while keep () do\n        let c = a + 3\n        sink c"
        "let sink (n: int) = ()\nlet run (a: int) (keep: unit -> bool) =\n    let c = a + 3\n    while keep () do\n        sink c"

// ---- FR0072 ExpandWildcard ----

let private wildcardsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ExpandWildcard.find tree sourceText checkResults

let private assertExpanded (source: string) (expectedReplacement: string) =
    match wildcardsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one wildcard note, got %A" other

[<Fact>]
let ``a wildcard hiding one case expands to it`` () =
    assertExpanded
        "type T =\n    | A\n    | B\n    | C\n    | D\n\nlet f (t: T) =\n    match t with\n    | A -> 1\n    | B -> 2\n    | C -> 3\n    | _ -> 4"
        "D"

[<Fact>]
let ``a wildcard hiding two cases expands to an or-pattern`` () =
    assertExpanded
        "type T =\n    | A\n    | B\n    | C\n    | D\n\nlet f (t: T) =\n    match t with\n    | A -> 1\n    | B -> 2\n    | _ -> 0"
        "C | D"

[<Fact>]
let ``a hidden case with fields gets a payload wildcard`` () =
    assertExpanded
        "type T =\n    | A\n    | B of int\n\nlet f (t: T) =\n    match t with\n    | A -> 1\n    | _ -> 0"
        "B _"

[<Fact>]
let ``three hidden cases would bloat the match and stay`` () =
    Assert.Empty(
        wildcardsIn
            "type T =\n    | A\n    | B\n    | C\n    | D\n\nlet f (t: T) =\n    match t with\n    | A -> 1\n    | _ -> 0"
    )

[<Fact>]
let ``a guarded clause breaks coverage reasoning`` () =
    Assert.Empty(
        wildcardsIn
            "type T =\n    | A of int\n    | B\n\nlet f (t: T) =\n    match t with\n    | A n when n > 0 -> 1\n    | _ -> 0"
    )

[<Fact>]
let ``a literal payload covers its case only partially`` () =
    Assert.Empty(
        wildcardsIn
            "type T =\n    | A of int\n    | B\n\nlet f (t: T) =\n    match t with\n    | A 3 -> 1\n    | _ -> 0"
    )

[<Fact>]
let ``enums are open sets and stay wild`` () =
    Assert.Empty(
        wildcardsIn
            "type Color =\n    | Red = 1\n    | Green = 2\n\nlet f (c: Color) =\n    match c with\n    | Color.Red -> 1\n    | _ -> 0"
    )

[<Fact>]
let ``an option match expands to None`` () =
    assertExpanded "let f (x: int option) =\n    match x with\n    | Some v -> v\n    | _ -> 0" "None"

[<Fact>]
let ``a RequireQualifiedAccess union keeps its qualifier in the fix`` () =
    assertExpanded
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | Fast\n    | Careful\n    | Dry\n\nlet f (m: Mode) =\n    match m with\n    | Mode.Fast -> 1\n    | Mode.Careful -> 2\n    | _ -> 0"
        "Mode.Dry"

// ---- FR0093 StructTupleField ----

let private structTuplesIn (source: string) =
    let _, _, tuples = structHintsIn source
    tuples

[<Fact>]
let ``a struct tuple field in a private record is noted`` () =
    match structTuplesIn "module Test\ntype private Row = { Span: int * int }" with
    | [ s ] ->
        Assert.Equal("Span", s.FieldName)
        Assert.Equal("int * int", s.TupleText)
        Assert.Equal("Row", s.TypeName)
    | other -> failwithf "Expected exactly one struct-tuple note, got %A" other

[<Fact>]
let ``four elements are still worth flattening`` () =
    Assert.Single(structTuplesIn "module Test\ntype private Box = { Bounds: float * float * float * float }")
    |> ignore

[<Fact>]
let ``five elements copy more than they save`` () =
    Assert.Empty(structTuplesIn "module Test\ntype private Wide = { P: int * int * int * int * int }")

[<Fact>]
let ``a reference element keeps the tuple on the heap`` () =
    Assert.Empty(structTuplesIn "module Test\ntype private Row = { Pair: int * string }")

[<Fact>]
let ``an already struct tuple is left alone`` () =
    Assert.Empty(structTuplesIn "module Test\ntype private Row = { Span: struct (int * int) }")

[<Fact>]
let ``a public record keeps its reference tuples`` () =
    Assert.Empty(structTuplesIn "module Test\ntype Row = { Span: int * int }")

[<Fact>]
let ``a public record tuple is offered under api changes`` () =
    let _, _, tuples =
        structHintsWithApiChangesIn "module Test\ntype Row = { Span: int * int }"

    Assert.Single tuples |> ignore

[<Fact>]
let ``a plain struct field is not a tuple`` () =
    Assert.Empty(structTuplesIn "module Test\ntype private Row = { Count: int }")

[<Fact>]
let ``the small struct record gains an attribute fix that typechecks`` () =
    let source =
        "module Test\n\nmodule Inner =\n    /// A point.\n    type private Point = { X: int; Y: int }\n\n    let private origin = { X = 0; Y = 0 }"

    let _, structs, _ = structHintsIn source

    match structs with
    | [ s ] ->
        match s.Fix with
        | Some(r, text) ->
            Assert.Equal("    [<Struct>]\n", text)

            let lines = source.Split '\n'

            let offset =
                (lines |> Seq.take (r.StartLine - 1) |> Seq.sumBy (fun l -> l.Length + 1))
                + r.StartColumn

            let patched = source.Substring(0, offset) + text + source.Substring offset
            // the attribute lands between the doc comment and the type
            Assert.Contains("/// A point.\n    [<Struct>]\n    type private Point", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected an attribute fix"
    | other -> failwithf "Expected one struct suggestion, got %A" other

[<Fact>]
let ``an attributed record stays advice`` () =
    // CLIMutable + Struct conflict outright; any existing attribute
    // keeps this a note
    let source =
        "module Test\n[<CLIMutable>]\ntype private Point = { X: int; Y: int }\nlet origin = { X = 0; Y = 0 }"

    let _, structs, _ = structHintsIn source

    for s in structs do
        Assert.Equal(None, s.Fix)


// ---- FR0069 voption migration ----

let private voptionFixIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    let voptions, _, _ = StructHints.find false tree sourceText

    voptions
    |> List.map (fun s ->
        s,
        if s.IsFilePrivate then
            VOptionMigration.migrate tree sourceText checkResults s.FieldIdRange s.FieldName s.OptionNameRange
        else
            None)

let private applyMigration (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``a file-private option field migrates with every use`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option; Name: string }\n"
        + "let private mk (d: System.DateTime) = { Seen = Some d; Name = \"a\" }\n"
        + "let private clear (r: Row) = { r with Seen = None }\n"
        + "let private describe (r: Row) =\n"
        + "    match r.Seen with\n"
        + "    | Some d -> string d\n"
        + "    | None -> \"never\"\n"
        + "let private year (r: Row) = r.Seen |> Option.map (fun d -> d.Year)\n"
        + "let private known (r: Row) = r.Seen.IsSome\n"
        + "let private orNow (r: Row) (now: System.DateTime) = defaultArg r.Seen now"

    match voptionFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("Seen: System.DateTime voption", patched)
        Assert.Contains("{ Seen = ValueSome d; Name = \"a\" }", patched)
        Assert.Contains("{ r with Seen = ValueNone }", patched)
        Assert.Contains("| ValueSome d -> string d", patched)
        Assert.Contains("| ValueNone -> \"never\"", patched)
        Assert.Contains("r.Seen |> ValueOption.map", patched)
        Assert.Contains("r.Seen.IsSome", patched)
        Assert.Contains("defaultValueArg r.Seen now", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one migratable field, got %A" other

[<Fact>]
let ``a use that binds the option value keeps the note`` () =
    // `let s = r.Seen` starts dataflow the scan does not follow
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option }\n"
        + "let private mk (d: System.DateTime) = { Seen = Some d }\n"
        + "let private stash (r: Row) =\n"
        + "    let s = r.Seen\n"
        + "    s"

    match voptionFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the migration to bail, got %A" other

// ---- FR0093 struct-tuple migration ----

let private structTupleFixIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    let _, _, structTuples = StructHints.find false tree sourceText

    structTuples
    |> List.map (fun s ->
        s,
        if s.IsFilePrivate then
            StructTupleMigration.migrate tree sourceText checkResults s.FieldIdRange s.FieldName s.Range
        else
            None)

[<Fact>]
let ``a file-private tuple field migrates with every use`` () =
    let source =
        "module Test\n"
        + "type private P = { A: int * int; Tag: string }\n"
        + "let private mk (x: int) = { A = (x, x + 1); Tag = \"t\" }\n"
        + "let private flip (p: P) = { p with A = p.Tag.Length, 0 }\n"
        + "let private show (p: P) =\n"
        + "    match p.A with\n"
        + "    | (0, _) | (_, 0) -> \"edge\"\n"
        + "    | (x, y) -> string (x + y)\n"
        + "let private parts (p: P) =\n"
        + "    let (a, b) = p.A\n"
        + "    a - b\n"
        + "let private isOrigin (p: P) = p.A = (0, 0)"

    match structTupleFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("A: struct (int * int)", patched)
        Assert.Contains("{ A = struct (x, x + 1); Tag = \"t\" }", patched)
        Assert.Contains("{ p with A = struct (p.Tag.Length, 0) }", patched)
        Assert.Contains("| struct (0, _) | struct (_, 0) -> \"edge\"", patched)
        Assert.Contains("| struct (x, y) -> string (x + y)", patched)
        Assert.Contains("let struct (a, b) = p.A", patched)
        Assert.Contains("p.A = struct (0, 0)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one migratable tuple field, got %A" other

[<Fact>]
let ``a tuple field passed along whole keeps the note`` () =
    // `fst p.A` needs the reference tuple — dataflow the scan cannot follow
    let source =
        "module Test\n"
        + "type private P = { A: int * int }\n"
        + "let private mk () = { A = (1, 2) }\n"
        + "let private first (p: P) = fst p.A"

    match structTupleFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the tuple migration to bail, got %A" other

[<Fact>]
let ``an internal tuple field keeps the note`` () =
    let source =
        "module Test\n"
        + "type internal P = { A: int * int }\n"
        + "let internal mk () = { A = (1, 2) }"

    match structTupleFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected no migration for internal, got %A" other

[<Fact>]
let ``an option value flowing in from a variable keeps the note`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option }\n"
        + "let private mk (d: System.DateTime option) = { Seen = d }"

    match voptionFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the migration to bail, got %A" other

[<Fact>]
let ``a non-private contained type keeps the note`` () =
    let source =
        "module Test\n"
        + "type internal Row = { Seen: System.DateTime option }\n"
        + "let internal mk (d: System.DateTime) = { Seen = Some d }"

    match voptionFixIn source with
    | [ (s, migration) ] ->
        Assert.False s.IsFilePrivate
        Assert.Equal(None, migration)
    | other -> failwithf "Expected one non-private suggestion, got %A" other

[<Fact>]
let ``a binder match arm keeps the note`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option }\n"
        + "let private mk (d: System.DateTime) = { Seen = Some d }\n"
        + "let private peek (r: Row) =\n"
        + "    match r.Seen with\n"
        + "    | x -> x"

    match voptionFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the migration to bail, got %A" other

[<Fact>]
let ``equality with None migrates the literal too`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option }\n"
        + "let private mk (d: System.DateTime) = { Seen = Some d }\n"
        + "let private empty (r: Row) = r.Seen = None"

    match voptionFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("r.Seen = ValueNone", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected a migratable field, got %A" other

[<Fact>]
let ``a record pattern destructuring Some migrates`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime option; Name: string }\n"
        + "let private mk (d: System.DateTime) = { Seen = Some d; Name = \"x\" }\n"
        + "let private label (r: Row) =\n"
        + "    match r with\n"
        + "    | { Seen = Some d } -> string d\n"
        + "    | { Seen = None } -> \"never\""

    match voptionFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("{ Seen = ValueSome d }", patched)
        Assert.Contains("{ Seen = ValueNone }", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected a migratable field, got %A" other

// ---- FR0120 CatchLogException ----

// a stand-in for Microsoft.Extensions.Logging so the typed gate has a
// real entity to resolve without the package reference
let private loggerScaffold =
    "namespace Microsoft.Extensions.Logging\n"
    + "type ILogger = interface end\n"
    + "[<System.Runtime.CompilerServices.Extension>]\n"
    + "type LoggerExtensions =\n"
    + "    [<System.Runtime.CompilerServices.Extension>]\n"
    + "    static member LogError(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) = ignore (logger, message, args)\n"
    + "    [<System.Runtime.CompilerServices.Extension>]\n"
    + "    static member LogError(logger: ILogger, ex: exn, message: string, [<System.ParamArray>] args: obj[]) = ignore (logger, ex, message, args)\n"
    + "namespace Test\n"
    + "open Microsoft.Extensions.Logging\n"

let private catchLogsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck (loggerScaffold + source)
    CatchLogException.find tree sourceText checkResults

[<Fact>]
let ``a handler log without the exception gains it first`` () =
    let source =
        "module M =\n    let run (logger: ILogger) (work: unit -> int) =\n        try\n            work ()\n        with ex ->\n            logger.LogError(\"work failed\")\n            0"

    match catchLogsIn source with
    | [ s ] ->
        Assert.Equal("ex", s.ExceptionName)

        let full = loggerScaffold + source
        let patched = applyEdit full s.Range $"{s.ExceptionName}, "
        Assert.Contains("logger.LogError(ex, \"work failed\")", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one catch-log suggestion, got %A" other

[<Fact>]
let ``logging the message only is a legitimate PII choice`` () =
    let source =
        "module M =\n    let run (logger: ILogger) (work: unit -> int) =\n        try\n            work ()\n        with ex ->\n            logger.LogError(\"work failed: {Error}\", ex.Message)\n            0"

    Assert.Empty(catchLogsIn source)

[<Fact>]
let ``a log already passing the exception is left alone`` () =
    let source =
        "module M =\n    let run (logger: ILogger) (work: unit -> int) =\n        try\n            work ()\n        with ex ->\n            logger.LogError(ex, \"work failed\")\n            0"

    Assert.Empty(catchLogsIn source)

[<Fact>]
let ``a log outside any handler is left alone`` () =
    let source =
        "module M =\n    let run (logger: ILogger) =\n        logger.LogError(\"routine complaint\")\n        0"

    Assert.Empty(catchLogsIn source)

[<Fact>]
let ``a user type with a LogError member is not a logger`` () =
    let source =
        "module M =\n    type Fake() =\n        member _.LogError(msg: string) = ignore msg\n    let run (f: Fake) (work: unit -> int) =\n        try\n            work ()\n        with ex ->\n            f.LogError(\"work failed\")\n            0"

    Assert.Empty(catchLogsIn source)

// ---- FR0121 DateTimeRules ----

let private wallClocksIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DateTimeRules.find tree sourceText checkResults

[<Fact>]
let ``a non-Utc timestamp setter takes local time`` () =
    // fsdocs: `File.SetLastWriteTime(path, DateTime.Now)` is right as
    // written — the non-Utc setters take LOCAL time, and UtcNow there would
    // stamp the file hours off
    Assert.Empty(
        wallClocksIn "module M\nlet touch (p: string) = System.IO.File.SetLastWriteTime(p, System.DateTime.Now)"
    )

    Assert.Empty(wallClocksIn "module M\nlet touch (fi: System.IO.FileInfo) = fi.LastWriteTime <- System.DateTime.Now")

    // the Utc setter wants UtcNow
    match
        wallClocksIn "module M\nlet touch (p: string) = System.IO.File.SetLastWriteTimeUtc(p, System.DateTime.Now)"
    with
    | [ s ] ->
        match s.Kind with
        | DateTimeRules.WallClockKind.LocalNow -> ()
        | other -> failwithf "Expected the local-clock note, got %A" other
    | other -> failwithf "Expected one wall-clock note, got %A" other

[<Fact>]
let ``Now read as an instant through a member call is still a local clock read`` () =
    // the compiler's `DateTime.Now.Ticks.ToString()` as a version number
    // goes backwards at the DST fall-back; UtcNow serves as well, so the
    // rewrite is offered
    match wallClocksIn "module M\nlet version () = System.DateTime.Now.Ticks.ToString()" with
    | [ s ] ->
        (match s.Kind with
         | DateTimeRules.WallClockKind.LocalNow -> ()
         | other -> failwithf "Expected the local-clock note, got %A" other)

        Assert.True s.FixRange.IsSome
    | other -> failwithf "Expected one wall-clock note, got %A" other

    // fsdocs' `DateTime.Now.ToString("yyMMddhh")` renders the local
    // calendar: the note, but not the rewrite
    match wallClocksIn "module M\nlet stamp () = System.DateTime.Now.ToString(\"yyMMddhh\")" with
    | [ s ] ->
        (match s.Kind with
         | DateTimeRules.WallClockKind.LocalNow -> ()
         | other -> failwithf "Expected the local-clock note, got %A" other)

        Assert.True s.FixRange.IsNone
    | other -> failwithf "Expected one wall-clock note, got %A" other

[<Fact>]
let ``UtcNow Date is a timezone-random calendar cut`` () =
    match wallClocksIn "module M\nlet today () = System.DateTime.UtcNow.Date" with
    | [ s ] ->
        match s.Kind with
        | DateTimeRules.WallClockKind.UtcDateCut _ -> ()
        | other -> failwithf "Expected the date-cut note, got %A" other
    | other -> failwithf "Expected one wall-clock note, got %A" other

[<Fact>]
let ``Today is the server's calendar date`` () =
    match wallClocksIn "module M\nlet today () = System.DateTime.Today" with
    | [ s ] ->
        match s.Kind with
        | DateTimeRules.WallClockKind.UtcDateCut _ -> ()
        | other -> failwithf "Expected the date-cut note, got %A" other
    | other -> failwithf "Expected one wall-clock note, got %A" other

[<Fact>]
let ``a bare Now carries the opt-in UtcNow rewrite`` () =
    let source = "module M\nlet stamp () = System.DateTime.Now"

    match wallClocksIn source with
    | [ s ] ->
        Assert.Equal(DateTimeRules.WallClockKind.LocalNow, s.Kind)

        match s.FixRange with
        | Some r ->
            let patched = applyEdit source r "UtcNow"
            Assert.Contains("System.DateTime.UtcNow", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the Now fix range"
    | other -> failwithf "Expected one wall-clock suggestion, got %A" other

[<Fact>]
let ``Now under a calendar read gets no rewrite: it would create the date-cut bug`` () =
    // DateTime.Now.Date is a LOCAL calendar read; swapping Now for UtcNow
    // underneath it manufactures exactly the UtcNow.Date defect
    Assert.Empty(wallClocksIn "module M\nlet today () = System.DateTime.Now.Date")

[<Fact>]
let ``a user type named DateTime is not the BCL clock`` () =
    Assert.Empty(wallClocksIn "module M\ntype DateTime = { Now: int }\nlet fake (d: DateTime) = d.Now")

// ---- FR0122 RegexValidity ----

let private invalidPatternsIn (source: string) =
    let tree, _ = parse source
    RegexUsage.findInvalidPatterns tree

[<Fact>]
let ``an unclosed group is a guaranteed runtime exception`` () =
    match
        invalidPatternsIn "module M\nlet f (s: string) = System.Text.RegularExpressions.Regex.IsMatch(s, \"(unclosed\")"
    with
    | [ (_, pattern, _) ] -> Assert.Equal("(unclosed", pattern)
    | other -> failwithf "Expected one invalid pattern, got %A" other

[<Fact>]
let ``a valid pattern stays quiet`` () =
    Assert.Empty(
        invalidPatternsIn "module M\nlet f (s: string) = System.Text.RegularExpressions.Regex.IsMatch(s, @\"\d+\")"
    )

[<Fact>]
let ``an invalid ctor pattern is caught too`` () =
    match invalidPatternsIn "module M\nlet r = System.Text.RegularExpressions.Regex(\"[a-\")" with
    | [ (_, pattern, _) ] -> Assert.Equal("[a-", pattern)
    | other -> failwithf "Expected one invalid ctor pattern, got %A" other

[<Fact>]
let ``a dynamic pattern is out of reach and stays quiet`` () =
    Assert.Empty(
        invalidPatternsIn "module M\nlet f (s: string) (p: string) = System.Text.RegularExpressions.Regex.IsMatch(s, p)"
    )

// ---- FR0123 MonitorLock ----

let private monitorLocksIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MonitorLock.find tree sourceText checkResults

[<Fact>]
let ``the canonical Enter-try-finally-Exit becomes lock`` () =
    let source =
        "module M =\n    let gate = obj ()\n    let mutable count = 0\n    let bump () =\n        System.Threading.Monitor.Enter gate\n        try\n            // guarded increment\n            count <- count + 1\n            count\n        finally\n            System.Threading.Monitor.Exit gate"

    match monitorLocksIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.StartsWith("lock gate (fun () ->", replacement)
            let patched = applyEdit source r replacement
            Assert.Contains("lock gate (fun () ->", patched)
            Assert.Contains("// guarded increment", patched)
            Assert.DoesNotContain("Monitor.Exit", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the lock rewrite"
    | other -> failwithf "Expected one monitor suggestion, got %A" other

[<Fact>]
let ``mismatched lock objects keep their hands off`` () =
    let source =
        "module M =\n    let a = obj ()\n    let b = obj ()\n    let bump () =\n        System.Threading.Monitor.Enter a\n        try\n            1\n        finally\n            System.Threading.Monitor.Exit b"

    match monitorLocksIn source with
    | [ s ] -> Assert.Equal(None, s.Fix)
    | other -> failwithf "Expected one fix-less suggestion, got %A" other

[<Fact>]
let ``a bare Enter without try is the leak note`` () =
    let source =
        "module M =\n    let gate = obj ()\n    let mutable count = 0\n    let bump () =\n        System.Threading.Monitor.Enter gate\n        count <- count + 1\n        System.Threading.Monitor.Exit gate\n        count"

    match monitorLocksIn source with
    | [ s ] -> Assert.Equal(None, s.Fix)
    | other -> failwithf "Expected one bare-Enter note, got %A" other

[<Fact>]
let ``FR0123: a statement after the finally still leaves the Enter guarded`` () =
    // FCS illib's InlineDelayInit.Value: `Monitor.Enter(this)`, a blank
    // line, try/finally, then `value` — the trailing read nests the
    // try/finally one Sequential deeper, and the leak note fired
    let source =
        "module M =\n    let gate = obj ()\n    let mutable value = 0\n    let force () =\n        System.Threading.Monitor.Enter(gate)\n\n        try\n            value <- value + 1\n        finally\n            System.Threading.Monitor.Exit(gate)\n\n        value"

    match monitorLocksIn source with
    | [ s ] ->
        Assert.True(s.Guarded, "the try/finally guards the Enter")

        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.StartsWith("lock gate (fun () ->", replacement)
            let patched = applyEdit source r replacement
            Assert.Contains("value <- value + 1", patched)
            Assert.EndsWith("value", patched.TrimEnd())
            Assert.DoesNotContain("Monitor.Exit", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the lock rewrite"
    | other -> failwithf "Expected one guarded suggestion, got %A" other

[<Fact>]
let ``the two-argument Enter overload carries protocol and stays`` () =
    let source =
        "module M =\n    let gate = obj ()\n    let bump () =\n        let mutable taken = false\n        System.Threading.Monitor.Enter(gate, &taken)\n        try\n            1\n        finally\n            if taken then System.Threading.Monitor.Exit gate"

    Assert.Empty(monitorLocksIn source)

[<Fact>]
let ``a user Monitor type is not the BCL one`` () =
    let source =
        "module M =\n    type Monitor = static member Enter(_: obj) = ()\n    let bump () =\n        Monitor.Enter(obj ())\n        1"

    Assert.Empty(monitorLocksIn source)

// ---- FR0124 LogTemplates ----

let private logTemplatesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck (loggerScaffold + source)
    LogTemplates.find tree sourceText checkResults

[<Fact>]
let ``a template with more placeholders than arguments is a lie`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (user: string) =\n        logger.LogError(\"user {User} did {Action}\", user)"

    match logTemplatesIn source with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.CountMismatch(2, 1), s.Problem)
    | other -> failwithf "Expected one template mismatch, got %A" other

[<Fact>]
let ``a matching template stays quiet`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (user: string) (act: string) =\n        logger.LogError(\"user {User} did {Action}\", user, act)"

    Assert.Empty(logTemplatesIn source)

[<Fact>]
let ``a leading exception argument is skipped before counting`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (work: unit -> int) (id: int) =\n        try\n            work ()\n        with ex ->\n            logger.LogError(ex, \"work {Id} failed\", id)\n            0"

    Assert.Empty(logTemplatesIn source)

[<Fact>]
let ``duplicate placeholder names overwrite each other`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (a: int) (b: int) =\n        logger.LogError(\"{Id} then {Id}\", a, b)"

    match logTemplatesIn source with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.DuplicateName "Id", s.Problem)
    | other -> failwithf "Expected one duplicate note, got %A" other

[<Fact>]
let ``an interpolated template destroys structured logging`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (user: string) =\n        logger.LogError($\"failed for {user}\")"

    match logTemplatesIn source with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.Interpolated, s.Problem)
    | other -> failwithf "Expected one interpolation note, got %A" other

[<Fact>]
let ``escaped braces are literal text not placeholders`` () =
    let source =
        "module M =\n    let go (logger: ILogger) =\n        logger.LogError(\"literal {{braces}} here\")"

    Assert.Empty(logTemplatesIn source)

// ---- FR0065 weak TLS protocols ----

[<Fact>]
let ``a weak TLS protocol constant is noted`` () =
    let crypto, _, _ =
        securityIn
            "module Test\nlet setup () = System.Net.ServicePointManager.SecurityProtocol <- System.Net.SecurityProtocolType.Tls11"

    match crypto with
    | [ s ] -> Assert.Equal(SecurityRules.WeakKind.Protocol "Tls11", s.Kind)
    | other -> failwithf "Expected one weak-protocol note, got %A" other

[<Fact>]
let ``Tls12 is fine`` () =
    let crypto, _, _ =
        securityIn
            "module Test\nlet setup () = System.Net.ServicePointManager.SecurityProtocol <- System.Net.SecurityProtocolType.Tls12"

    Assert.Empty crypto

// ---- adversarial pins for the new-rule guard rails ----

[<Fact>]
let ``FR0123 a body awaiting inside a task is not wrapped in a lambda`` () =
    // do! cannot live in a plain lambda — the rewrite would not compile
    let source =
        "module M =\n    let gate = obj ()\n    let go () = task {\n        System.Threading.Monitor.Enter gate\n        try\n            do! System.Threading.Tasks.Task.Delay 1\n            return 1\n        finally\n            System.Threading.Monitor.Exit gate\n    }"

    for s in monitorLocksIn source do
        Assert.Equal(None, s.Fix)

[<Fact>]
let ``FR0123 a body touching an enclosing local mutable is not wrapped`` () =
    // a closure cannot capture a local mutable (FS0407)
    let source =
        "module M =\n    let gate = obj ()\n    let go () =\n        let mutable count = 0\n        System.Threading.Monitor.Enter gate\n        try\n            count <- count + 1\n            count\n        finally\n            System.Threading.Monitor.Exit gate"

    for s in monitorLocksIn source do
        Assert.Equal(None, s.Fix)

[<Fact>]
let ``FR0120 an EventId-first log gets no exception inserted before it`` () =
    // LoggerExtensions wants (EventId, Exception, template) — inserting
    // the exception FIRST matches no overload
    let source =
        "module M =\n    let go (logger: ILogger) (eventId: int) (work: unit -> int) =\n        try\n            work ()\n        with ex ->\n            logger.LogError(eventId, \"work failed\")\n            0"

    Assert.Empty(catchLogsIn source)

[<Fact>]
let ``FR0121 DateTimeOffset Now carries its offset and stays quiet`` () =
    Assert.Empty(wallClocksIn "module M\nlet stamp () = System.DateTimeOffset.Now")

[<Fact>]
let ``FR0121 the date cut is caught mid-chain too`` () =
    match wallClocksIn "module M\nlet tomorrow () = System.DateTime.UtcNow.Date.AddDays 1.0" with
    | [ s ] ->
        match s.Kind with
        | DateTimeRules.WallClockKind.UtcDateCut _ -> ()
        | other -> failwithf "Expected the date-cut note, got %A" other
    | other -> failwithf "Expected one mid-chain note, got %A" other

[<Fact>]
let ``FR0121 Today survives a following call too`` () =
    match wallClocksIn "module M\nlet tomorrow () = System.DateTime.Today.AddDays 1.0" with
    | [ s ] ->
        match s.Kind with
        | DateTimeRules.WallClockKind.UtcDateCut _ -> ()
        | other -> failwithf "Expected the date-cut note, got %A" other
    | other -> failwithf "Expected one Today note, got %A" other

[<Fact>]
let ``FR0124 a params array passed whole is not an arity claim`` () =
    let source =
        "module M =\n    let go (logger: ILogger) (args: obj[]) =\n        logger.LogError(\"a {X} and {Y}\", args)"

    Assert.Empty(logTemplatesIn source)

[<Fact>]
let ``FR0124 a hole-free interpolation compiles to a constant and stays quiet`` () =
    let source =
        "module M =\n    let go (logger: ILogger) =\n        logger.LogError($\"plain text\")"

    Assert.Empty(logTemplatesIn source)

// ---- FR0125 UnicodeHygiene ----

let private unicodeIn (source: string) =
    let tree, sourceText = parse source
    UnicodeHygiene.find tree sourceText

[<Fact>]
let ``a bidi override in source is Trojan Source`` () =
    // U+202E RIGHT-TO-LEFT OVERRIDE inside a comment
    let source = "module M\n// check ‮access granted\nlet ok = 1"

    match unicodeIn source with
    | [ s ] ->
        Assert.Equal("U+202E", s.CodePoint)
        Assert.Equal(None, s.Fix) // in a comment: nothing safe to rewrite
    | other -> failwithf "Expected one bidi finding, got %A" other

[<Fact>]
let ``a zero-width space inside a regular literal gains the escape fix`` () =
    let source = "module M\nlet name = \"user​name\""

    match unicodeIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.Equal("\\u200B", replacement)
            let patched = applyEdit source r replacement
            Assert.Contains("\\u200B", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the escape fix inside a regular literal"
    | other -> failwithf "Expected one invisible finding, got %A" other

[<Fact>]
let ``a Unicode tag block character is the smuggling channel`` () =
    // U+E0041 TAG LATIN CAPITAL LETTER A (astral, surrogate pair)
    let source = "module M\nlet prompt = \"hello \U000E0041world\""

    match unicodeIn source with
    | [ s ] -> Assert.Equal("U+0E0041", s.CodePoint)
    | other -> failwithf "Expected one tag-block finding, got %A" other

[<Fact>]
let ``emoji ZWJ sequences are legitimate and stay quiet`` () =
    // family emoji uses U+200D ZERO WIDTH JOINER by design
    let source = "module M\nlet family = \"👨‍👩\""

    Assert.Empty(unicodeIn source)

[<Fact>]
let ``plain unicode text is not flagged`` () =
    Assert.Empty(unicodeIn "module M\nlet greeting = \"tervetuloa — päivää\"")

// ---- FR0126 process sinks ----

[<Fact>]
let ``an interpolated Process Start command is the injection sink`` () =
    let _, _, sinks =
        securityIn "module Test\nlet run (userInput: string) = System.Diagnostics.Process.Start($\"tool {userInput}\")"

    match sinks with
    | [ s ] -> Assert.Equal("Process.Start", s.Sink)
    | other -> failwithf "Expected one process sink, got %A" other

[<Fact>]
let ``a fixed command with dynamic arguments still flags the ctor`` () =
    let _, _, sinks =
        securityIn "module Test\nlet run (v: string) = new System.Diagnostics.ProcessStartInfo(\"git\", \"clone \" + v)"

    match sinks with
    | [ s ] -> Assert.Equal("ProcessStartInfo", s.Sink)
    | other -> failwithf "Expected one ctor sink, got %A" other

[<Fact>]
let ``an Arguments property fed a sprintf is flagged`` () =
    let _, _, sinks =
        securityIn
            "module Test\nlet configure (psi: System.Diagnostics.ProcessStartInfo) (v: string) =\n    psi.Arguments <- sprintf \"run %s\" v"

    match sinks with
    | [ s ] -> Assert.Equal("Arguments", s.Sink)
    | other -> failwithf "Expected one Arguments sink, got %A" other

[<Fact>]
let ``a constant command line is fine`` () =
    let _, _, sinks =
        securityIn "module Test\nlet run () = System.Diagnostics.Process.Start(\"notepad.exe\")"

    Assert.Empty sinks

// ---- FR0127 SecretLiterals ----

let private secretsIn (source: string) =
    let tree, _ = parse source
    SecretLiterals.find tree

[<Fact>]
let ``an Anthropic-format key literal is a leaked credential`` () =
    // the fixture key is assembled at TEST-source level so this file's
    // own literal cannot match the format
    let key = "sk-ant-" + "api03-abcdefghijklmnop"
    let source = $"module M\nlet k = \"%s{key}\""

    match secretsIn source with
    | [ s ] -> Assert.Equal("Anthropic", s.Provider)
    | other -> failwithf "Expected one key finding, got %A" other

[<Fact>]
let ``an AWS access key id matches its documented shape`` () =
    let key = "AKIA" + "IOSFODNN7EXAMPLE"
    let source = $"module M\nlet k = \"%s{key}\""

    match secretsIn source with
    | [ s ] -> Assert.Equal("AWS", s.Provider)
    | other -> failwithf "Expected one key finding, got %A" other

[<Fact>]
let ``a PEM private key header is key material`` () =
    let header = "-----BEGIN RSA PRIVATE" + " KEY-----"
    let source = $"module M\nlet pem = \"%s{header}\""

    match secretsIn source with
    | [ s ] -> Assert.Equal("PEM private key", s.Provider)
    | other -> failwithf "Expected one PEM finding, got %A" other

[<Fact>]
let ``ordinary prefixed identifiers are not keys`` () =
    Assert.Empty(secretsIn "module M\nlet sku = \"sk-1234\"\nlet gh = \"ghx_short\"")

// ---- FR0128 ObsoleteCrypto ----

let private obsoleteCryptoIn (source: string) =
    let tree, sourceText = parse source
    ObsoleteCrypto.find tree sourceText

[<Fact>]
let ``an obsolete Managed constructor becomes the static factory`` () =
    let source =
        "module M\nlet hash () = new System.Security.Cryptography.SHA256Managed()"

    match obsoleteCryptoIn source with
    | [ s ] ->
        Assert.Equal("System.Security.Cryptography.SHA256.Create()", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one obsolete-ctor suggestion, got %A" other

[<Fact>]
let ``RNGCryptoServiceProvider maps to RandomNumberGenerator`` () =
    let source =
        "module M\nopen System.Security.Cryptography\nlet rng () = new RNGCryptoServiceProvider()"

    match obsoleteCryptoIn source with
    | [ s ] ->
        Assert.Equal("RandomNumberGenerator.Create()", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one RNG suggestion, got %A" other

[<Fact>]
let ``a constructor with arguments carries state and stays`` () =
    Assert.Empty(
        obsoleteCryptoIn
            "module M\ntype AesManaged(key: byte[]) = member _.K = key\nlet a (key: byte[]) = new AesManaged(key)"
    )

[<Fact>]
let ``an obsolete name mentioned in a type position vetoes the rewrite`` () =
    // SHA256.Create() returns the BASE type — an explicit SHA256Managed
    // annotation (or `:?` test / typeof<>) would break or change meaning
    Assert.Empty(
        obsoleteCryptoIn "module M\nopen System.Security.Cryptography\nlet h: SHA256Managed = new SHA256Managed()"
    )

[<Fact>]
let ``the veto is per name, not per file`` () =
    let source =
        "module M\nopen System.Security.Cryptography\nlet h: SHA256Managed = new SHA256Managed()\nlet g () = new SHA512Managed()"

    match obsoleteCryptoIn source with
    | [ s ] -> Assert.Equal("SHA512Managed", s.ObsoleteName)
    | other -> failwithf "Expected only the SHA512 suggestion, got %A" other

// ---- FR0129 MatchGuards ----

let private guardEqualsIn (source: string) =
    let tree, sourceText = parse source
    MatchGuards.find tree sourceText

[<Fact>]
let ``a guard that only tests the binder becomes the literal pattern`` () =
    let source =
        "module M\nlet f (a: string) =\n    match a with\n    | x when x = \"A\" -> 1\n    | x when x = \"B\" -> 2\n    | _ -> 3"

    match guardEqualsIn source with
    | [ s1; s2 ] ->
        Assert.Equal("\"A\"", s1.LiteralText)

        let patched =
            applyEdit (applyEdit source s2.Range s2.LiteralText) s1.Range s1.LiteralText

        Assert.Contains("| \"A\" -> 1", patched)
        Assert.Contains("| \"B\" -> 2", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two guard suggestions, got %A" other

[<Fact>]
let ``function-style matching gets the same rewrite`` () =
    let source =
        "module M\nlet f = function\n    | x when x = 42 -> \"yes\"\n    | _ -> \"no\""

    match guardEqualsIn source with
    | [ s ] ->
        Assert.Equal("42", s.LiteralText)
        let patched = applyEdit source s.Range s.LiteralText
        Assert.Contains("| 42 -> \"yes\"", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one function-guard suggestion, got %A" other

[<Fact>]
let ``a body still using the binder keeps the guard`` () =
    Assert.Empty(
        guardEqualsIn
            "module M\nlet f (a: string) =\n    match a with\n    | x when x = \"A\" -> x + \"!\"\n    | _ -> \"no\""
    )

[<Fact>]
let ``a compound guard is more than the literal`` () =
    Assert.Empty(
        guardEqualsIn
            "module M\nlet f (a: string) (b: bool) =\n    match a with\n    | x when x = \"A\" && b -> 1\n    | _ -> 3"
    )

[<Fact>]
let ``a decimal literal is not spellable in the pattern language`` () =
    Assert.Empty(
        guardEqualsIn "module M\nlet f (a: decimal) =\n    match a with\n    | x when x = 1.5m -> 1\n    | _ -> 3"
    )

[<Fact>]
let ``a guard against a VARIABLE cannot become a pattern`` () =
    Assert.Empty(
        guardEqualsIn
            "module M\nlet f (a: string) (expected: string) =\n    match a with\n    | x when x = expected -> 1\n    | _ -> 3"
    )

// ---- FR0130 LiteralConst ----

let private literalsIn (source: string) =
    let tree, sourceText = parse source
    LiteralConst.find false tree sourceText

[<Fact>]
let ``a private constant string gains the Literal attribute`` () =
    let source =
        "module M\nlet private Greeting = \"hello world\"\nlet show () = Greeting"

    match literalsIn source with
    | [ s ] ->
        Assert.Equal("Greeting", s.Name)
        let r, text = s.Fix
        let patched = applyEdit source r text
        Assert.Contains("[<Literal>]\nlet private Greeting", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one literal suggestion, got %A" other

[<Fact>]
let ``a public constant is an api change and stays without the flag`` () =
    Assert.Empty(literalsIn "module M\nlet Greeting = \"hello world\"")

[<Fact>]
let ``a computed value is not a literal`` () =
    Assert.Empty(literalsIn "module M\nlet private greeting = \"hello \" + \"world\"")

[<Fact>]
let ``a name also used as a match binder must not become a constant pattern`` () =
    // once `greeting` is a literal, `| greeting ->` MATCHES it instead of
    // binding — compiles fine, behavior silently changes
    Assert.Empty(
        literalsIn
            "module M\nlet private greeting = \"hello\"\nlet f (s: string) =\n    match s with\n    | greeting -> greeting"
    )

[<Fact>]
let ``a name also bound by a local let must not become a partial match`` () =
    Assert.Empty(
        literalsIn "module M\nlet private greeting = \"hello\"\nlet f (s: string) =\n    let greeting = s\n    greeting"
    )

// ---- FR0110 / FR0117 over function-style matching ----

[<Fact>]
let ``missing DU cases are added to function-style matches too`` () =
    let source =
        "module Test\ntype Color = Red | Green | Blue\nlet f : Color -> string = function\n    | Red -> \"r\"\n    | Green -> \"g\""

    let tree, sourceText, checkResults = parseAndCheck source

    match MissingCases.find tree sourceText checkResults with
    | [ s ] -> Assert.Equal<string list>([ "Blue" ], s.MissingCases)
    | other -> failwithf "Expected one missing-case suggestion, got %A" other

[<Fact>]
let ``adjacent same-result arms merge in function-style matches too`` () =
    let source =
        "module Test\nlet f : int -> bool = function\n    | 1 -> true\n    | 2 -> true\n    | _ -> false"

    let tree, sourceText = parse source

    match MissingCases.findMergeableArms tree sourceText with
    | [ s ] -> Assert.Equal(2, s.Count)
    | other -> failwithf "Expected one function-arm merge, got %A" other

// ---- FR0131 RecTailCall ----

let private tailCallsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RecTailCall.find tree sourceText checkResults

/// The attribute's whole point is FS3569 — the patched source must carry
/// NEITHER errors nor that warning.
let private assertTailCallClean (patched: string) =
    let _, _, checkResults = parseAndCheck patched

    let offending =
        checkResults.Diagnostics
        |> Array.filter (fun d ->
            d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error
            || d.ErrorNumber = 3569)

    Assert.True(Array.isEmpty offending, $"Patched source raises %A{offending}:\n%s{patched}")

[<Fact>]
let ``an accumulator loop over match gains TailCall`` () =
    let source =
        "module M\nlet rec sum (acc: int) (xs: int list) =\n    match xs with\n    | [] -> acc\n    | h :: t -> sum (acc + h) t"

    match tailCallsIn source with
    | [ s ] ->
        Assert.Equal("sum", s.Name)
        let r, text = s.Fix
        let patched = applyEdit source r text
        Assert.Contains("[<TailCall>]\nlet rec sum", patched)
        assertTailCallClean patched
    | other -> failwithf "Expected one TailCall suggestion, got %A" other

[<Fact>]
let ``function-style accumulator loops count their implicit parameter`` () =
    let source =
        "module M\nlet rec go (acc: int) = function\n    | [] -> acc\n    | (h: int) :: t -> go (acc + h) t"

    match tailCallsIn source with
    | [ s ] ->
        let r, text = s.Fix
        let patched = applyEdit source r text
        assertTailCallClean patched
    | other -> failwithf "Expected one function-style suggestion, got %A" other

[<Fact>]
let ``a piped self-call is a tail call`` () =
    let source =
        "module M\nlet rec drain (n: int) (xs: int list) =\n    match xs with\n    | [] -> n\n    | _ :: t -> t |> drain (n + 1)"

    match tailCallsIn source with
    | [ s ] ->
        let r, text = s.Fix
        assertTailCallClean (applyEdit source r text)
    | other -> failwithf "Expected one piped suggestion, got %A" other

[<Fact>]
let ``a cons around the self-call is not a tail call`` () =
    Assert.Empty(
        tailCallsIn
            "module M\nlet rec twice (xs: int list) =\n    match xs with\n    | [] -> []\n    | h :: t -> h :: h :: twice t"
    )

[<Fact>]
let ``the function passed as a VALUE cannot be verified`` () =
    Assert.Empty(
        tailCallsIn
            "module M\nlet rec flatten (acc: int list) (xss: int list list) =\n    match xss with\n    | [] -> acc\n    | _ -> List.fold flatten acc xss"
    )

[<Fact>]
let ``a self-call inside try-with is never tail`` () =
    Assert.Empty(
        tailCallsIn
            "module M\nlet rec retry (n: int) (f: unit -> int) =\n    try f ()\n    with _ -> if n > 0 then retry (n - 1) f else 0"
    )

[<Fact>]
let ``mutual and-groups stay untouched`` () =
    Assert.Empty(
        tailCallsIn
            "module M\nlet rec even (n: int) = if n = 0 then true else odd (n - 1)\nand odd (n: int) = if n = 0 then false else even (n - 1)"
    )

[<Fact>]
let ``an unverifiable call shape is left alone`` () =
    // `(k (n - 1)) x` — the parenthesised head hides the spine, so the
    // conservative catch-all vetoes rather than guesses
    Assert.Empty(tailCallsIn "module M\nlet rec k (n: int) (x: int) : int =\n    if n <= 0 then x else (k (n - 1)) x")

// ---- cross-file migrations (internal visibility, --api-changes class) ----

[<Fact>]
let ``an internal option field migrates across files`` () =
    let sourceA =
        "module A\ntype internal Row = { Seen: System.DateTime option }\nlet internal mk (d: System.DateTime) = { Seen = Some d }"

    let sourceB =
        "module B\nlet internal clear (r: A.Row) = { r with Seen = None }\nlet internal describe (r: A.Row) =\n    match r.Seen with\n    | Some d -> string d\n    | None -> \"never\""

    let treeA, sourceTextA, checkA, projectResults, pathA, _, recheck =
        parseAndCheckPair sourceA sourceB

    let voptions, _, _ = StructHints.find true treeA sourceTextA

    match voptions with
    | [ s ] ->
        match
            VOptionMigration.migrateProject
                treeA
                sourceTextA
                checkA
                projectResults
                s.FieldIdRange
                s.FieldName
                s.OptionNameRange
        with
        | Some edits ->
            // edits span both files
            let byFile =
                edits
                |> List.groupBy (fun (r, _, _) -> Path.GetFileName r.FileName)
                |> Map.ofList

            Assert.True(byFile.ContainsKey "A.fs")
            Assert.True(byFile.ContainsKey "B.fs")

            let apply (source: string) (fileEdits: (FSharp.Compiler.Text.range * string * string) list) =
                fileEdits
                |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
                |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

            let patchedA = apply sourceA byFile.["A.fs"]
            let patchedB = apply sourceB byFile.["B.fs"]
            Assert.Contains("System.DateTime voption", patchedA)
            Assert.Contains("Seen = ValueSome d", patchedA)
            Assert.Contains("Seen = ValueNone", patchedB)
            Assert.Contains("| ValueSome d -> string d", patchedB)

            let errors = recheck patchedA patchedB
            Assert.True(Array.isEmpty errors, $"patched pair does not typecheck: %A{errors}")
        | None -> failwith "expected a cross-file migration"
    | other -> failwithf "Expected one voption suggestion, got %A" other

[<Fact>]
let ``a sibling use outside the shapes vetoes the cross-file migration`` () =
    let sourceA =
        "module A\ntype internal Row = { Seen: System.DateTime option }\nlet internal mk (d: System.DateTime) = { Seen = Some d }"

    // `let s = r.Seen` in the OTHER file starts dataflow the scan cannot follow
    let sourceB = "module B\nlet internal stash (r: A.Row) =\n    let s = r.Seen\n    s"

    let treeA, sourceTextA, checkA, projectResults, _, _, _ =
        parseAndCheckPair sourceA sourceB

    let voptions, _, _ = StructHints.find true treeA sourceTextA

    match voptions with
    | [ s ] ->
        Assert.Equal(
            None,
            VOptionMigration.migrateProject
                treeA
                sourceTextA
                checkA
                projectResults
                s.FieldIdRange
                s.FieldName
                s.OptionNameRange
        )
    | other -> failwithf "Expected one voption suggestion, got %A" other

// ---- FR0132 CommentDoc ----

let private commentDocIn (source: string) =
    let tree, sourceText = parse source
    CommentDoc.find tree sourceText

[<Fact>]
let ``a trailing comment on a public binding becomes its XML doc`` () =
    let source = "module M\nlet interestRate r n = r * n // monthly, non-compounding"

    match commentDocIn source with
    | [ s ] ->
        let patched = applyMigration source s.Edits
        Assert.Contains("/// monthly, non-compounding\nlet interestRate r n = r * n", patched)
        Assert.False(patched.Contains "n // monthly")
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one doc promotion, got %A" other

[<Fact>]
let ``a union case's trailing comment docs the case`` () =
    let source =
        "module M\ntype Money =\n    | Rate of float // interest and rate\n    | Amount of int"

    match commentDocIn source with
    | [ s ] ->
        let patched = applyMigration source s.Edits
        Assert.Contains("    /// interest and rate\n    | Rate of float", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one case promotion, got %A" other

[<Fact>]
let ``a private binding keeps its trailing note`` () =
    Assert.Empty(commentDocIn "module M\nlet private helper r n = r * n // internal scratch")

[<Fact>]
let ``an existing XML doc wins`` () =
    Assert.Empty(commentDocIn "module M\n/// documented already\nlet interestRate r n = r * n // stale note")

[<Fact>]
let ``a suppression comment is an instruction, not documentation`` () =
    Assert.Empty(commentDocIn "module M\nlet rate r = r * 2 // fsharpanalyzer: ignore-line FR0001")

// ---- FR0133 NameQuoting ----

let private nameQuotingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    NameQuoting.find true tree sourceText checkResults None

[<Fact>]
let ``a five-word private name becomes a double-backtick name everywhere`` () =
    let source =
        "module M\nlet private thisIsMyVeryComplexMethod (x: int) = x + 1\nlet use1 () = thisIsMyVeryComplexMethod 1\nlet use2 () = thisIsMyVeryComplexMethod 2"

    match nameQuotingIn source with
    | [ s ] ->
        Assert.Equal("this is my very complex method", s.Quoted)
        let patched = applyMigration source s.Edits
        Assert.Contains("let private ``this is my very complex method`` (x: int)", patched)
        Assert.Contains("let use1 () = ``this is my very complex method`` 1", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one quoting suggestion, got %A" other

[<Fact>]
let ``a snake-case local renames inside its function`` () =
    let source =
        "module M\nlet f () =\n    let this_is_my_very_complex_case = 4\n    this_is_my_very_complex_case + 1"

    match nameQuotingIn source with
    | [ s ] ->
        let patched = applyMigration source s.Edits
        Assert.Contains("let ``this is my very complex case`` = 4", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one local quoting suggestion, got %A" other

[<Fact>]
let ``an acronym is a word already`` () =
    Assert.Empty(nameQuotingIn "module M\nlet private calcAPRUnitRateForLoan (x: int) = x")

[<Fact>]
let ``four words are readable as they are`` () =
    Assert.Empty(nameQuotingIn "module M\nlet private thisIsComplexMethod (x: int) = x")

[<Fact>]
let ``a public non-test name is a contract`` () =
    Assert.Empty(nameQuotingIn "module M\nlet thisIsMyVeryComplexMethod (x: int) = x")

[<Fact>]
let ``a test-attributed public name renames when the project proves it local`` () =
    let sourceA =
        "module ATests\n[<System.Obsolete>]\nlet fake () = ()\ntype FactAttribute() =\n    inherit System.Attribute()\n[<Fact>]\nlet checkThatRatesRoundCorrectly () = ()"

    let sourceB = "module B\nlet unrelated = 1"

    let treeA, sourceTextA, checkA, projectResults, _, _, _ =
        parseAndCheckPair sourceA sourceB

    match NameQuoting.find false treeA sourceTextA checkA (Some projectResults) with
    | [ s ] -> Assert.Equal("check that rates round correctly", s.Quoted)
    | other -> failwithf "Expected one test-name quoting, got %A" other

[<Fact>]
let ``without the locals opt-in only test names rewrite`` () =
    // default configuration: private five-word names stay put
    let tree, sourceText, checkResults =
        parseAndCheck
            "module M\nlet private thisIsMyVeryComplexHelper (x: int) = x\nlet go () = thisIsMyVeryComplexHelper 2"

    Assert.Empty(NameQuoting.find false tree sourceText checkResults None)

// ---- FR0022 new name sources ----

let private duNamesIn (source: string) =
    let tree, sourceText = parse source
    DuFieldNames.find false tree sourceText

[<Fact>]
let ``an XAndY case name names its own fields`` () =
    let source =
        "module M\ntype private Pricing =\n    | InterestAndRate of float * float\n    | Empty"

    match duNamesIn source with
    | [ s ] ->
        Assert.Equal<string list>([ "interest"; "rate" ], s.Names)
        let patched = applyMigration source s.Edits
        Assert.Contains("| InterestAndRate of interest: float * rate: float", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one name-sourced suggestion, got %A" other

[<Fact>]
let ``a clear trailing comment names the fields`` () =
    let source =
        "module M\ntype private Pricing =\n    | Pair of float * float // interest and rate\n    | Empty"

    match duNamesIn source with
    | [ s ] ->
        Assert.Equal<string list>([ "interest"; "rate" ], s.Names)
        let patched = applyMigration source s.Edits
        Assert.Contains("| Pair of interest: float * rate: float // interest and rate", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one comment-sourced suggestion, got %A" other

[<Fact>]
let ``a star-separated comment works too`` () =
    let source =
        "module M\ntype private Pricing =\n    | Pair of float * float // interest * rate\n    | Empty"

    match duNamesIn source with
    | [ s ] -> Assert.Equal<string list>([ "interest"; "rate" ], s.Names)
    | other -> failwithf "Expected one star-comment suggestion, got %A" other

[<Fact>]
let ``a type-note comment is not a name list`` () =
    // `// string * int` spells TYPES — using them as field names would
    // shadow the type names and read as nonsense
    Assert.Empty(duNamesIn "module M\ntype private T =\n    | Pair of string * int // string * int\n    | Empty")

[<Fact>]
let ``Command does not split at its lowercase and`` () =
    Assert.Empty(duNamesIn "module M\ntype private T =\n    | Command of string * int\n    | Empty")

[<Fact>]
let ``match sites still outrank the weaker sources`` () =
    let source =
        "module M\ntype private Pricing =\n    | InterestAndRate of float * float // wrong and comment\n    | Empty\nlet f (p: Pricing) =\n    match p with\n    | InterestAndRate(basis, spread) -> basis + spread\n    | Empty -> 0.0"

    match duNamesIn source with
    | [ s ] -> Assert.Equal<string list>([ "basis"; "spread" ], s.Names)
    | other -> failwithf "Expected the site names to win, got %A" other

// ---- FR0134 DateTimeOffset migration ----

let private dtoFixIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source

    DateTimeOffsetMigration.find false tree sourceText
    |> List.map (fun s ->
        s,
        if s.IsFilePrivate then
            DateTimeOffsetMigration.migrate tree sourceText checkResults s
        else
            None)

[<Fact>]
let ``a UtcNow-fed private DateTime field migrates to DateTimeOffset`` () =
    let source =
        "module Test\nopen System\n"
        + "type private Row = { Seen: DateTime; Name: string }\n"
        + "let private mk () = { Seen = DateTime.UtcNow; Name = \"a\" }\n"
        + "let private year (r: Row) = r.Seen.Year\n"
        + "let private later (r: Row) = r.Seen.AddDays 1.0\n"
        + "let private newer (a: Row) (b: Row) = a.Seen > b.Seen\n"
        + "let private gap (a: Row) (b: Row) = a.Seen - b.Seen"

    match dtoFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("Seen: DateTimeOffset", patched)
        Assert.Contains("{ Seen = DateTimeOffset.UtcNow; Name = \"a\" }", patched)
        Assert.Contains("r.Seen.Year", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one DateTimeOffset migration, got %A" other

[<Fact>]
let ``a ToString read escapes the envelope`` () =
    let source =
        "module Test\nopen System\n"
        + "type private Row = { Seen: DateTime }\n"
        + "let private mk () = { Seen = DateTime.UtcNow }\n"
        + "let private show (r: Row) = r.Seen.ToString \"o\""

    match dtoFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the migration to bail on ToString, got %A" other

[<Fact>]
let ``mixed Now and UtcNow writes bail`` () =
    let source =
        "module Test\nopen System\n"
        + "type private Row = { Seen: DateTime }\n"
        + "let private a () = { Seen = DateTime.UtcNow }\n"
        + "let private b () = { Seen = DateTime.Now }"

    match dtoFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the mixed-clock bail, got %A" other

[<Fact>]
let ``a computed write escapes the envelope`` () =
    let source =
        "module Test\nopen System\n"
        + "type private Row = { Seen: DateTime }\n"
        + "let private mk (d: DateTime) = { Seen = d }"

    match dtoFixIn source with
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected the computed-write bail, got %A" other

[<Fact>]
let ``an attributed binding keeps its comment where it is`` () =
    // the /// would land between the attribute and the let — FS3520 territory
    Assert.Empty(commentDocIn "module M\n[<System.Obsolete>]\nlet rate r = r * 2 // monthly figure")

[<Fact>]
let ``a user-defined DateTime type never migrates`` () =
    let source =
        "module Test\n"
        + "type DateTime = { Ticks: int64 }\n"
        + "module private Clock =\n"
        + "    let UtcNow = { Ticks = 0L }\n"
        + "type private Row = { Seen: DateTime }\n"
        + "let private mk () = { Seen = Clock.UtcNow }"

    match dtoFixIn source with
    | [] -> ()
    | [ (_, None) ] -> ()
    | other -> failwithf "Expected no migration for the user type, got %A" other

// ---- audit gates: cross-file confinement and classifier soundness ----

[<Fact>]
let ``a public field is never confined, even under api-changes`` () =
    let tree, sourceText = parse "module M\ntype Row = { Seen: System.DateTime option }"
    let voptions, _, _ = StructHints.find true tree sourceText

    match voptions with
    | [ s ] ->
        Assert.False s.IsFilePrivate
        Assert.False s.IsConfined
    | other -> failwithf "Expected one public voption hint, got %A" other

[<Fact>]
let ``an internal field is confined but not file-private`` () =
    let tree, sourceText =
        parse "module M\ntype internal Row = { Seen: System.DateTime option }"

    let voptions, _, _ = StructHints.find true tree sourceText

    match voptions with
    | [ s ] ->
        Assert.False s.IsFilePrivate
        Assert.True s.IsConfined
    | other -> failwithf "Expected one internal voption hint, got %A" other

[<Fact>]
let ``BeginAndEnd would name fields with keywords and stays`` () =
    Assert.Empty(duNamesIn "module M\ntype private T =\n    | BeginAndEnd of int * int\n    | Nothing")

[<Fact>]
let ``an XML-hostile comment stays where escaping cannot follow`` () =
    Assert.Empty(commentDocIn "module M\nlet cmp a b = a < b // true when a < b")

[<Fact>]
let ``a fake DateTime clock never migrates to the real one`` () =
    let source =
        "module Test\n"
        + "module DateTime =\n"
        + "    let mutable UtcNow = System.DateTime(2020, 1, 1)\n"
        + "type private Row = { Seen: System.DateTime }\n"
        + "let private mk () = { Seen = DateTime.UtcNow }"

    match dtoFixIn source with
    | [ (_, None) ] -> ()
    | [] -> ()
    | other -> failwithf "Expected the fake-clock bail, got %A" other

[<Fact>]
let ``a same-named field on another type is not a sound comparison operand`` () =
    let source =
        "module Test\nopen System\n"
        + "type private Row = { Seen: DateTime }\n"
        + "type Other = { Seen: DateTime }\n"
        + "let private mk () = { Row.Seen = DateTime.UtcNow }\n"
        + "let private newer (r: Row) (o: Other) = r.Seen > o.Seen"

    match dtoFixIn source with
    | [ (_, None) ] -> ()
    | [] -> ()
    | other -> failwithf "Expected the cross-type comparison bail, got %A" other

[<Fact>]
let ``a name referenced by string never renames`` () =
    // [<TestCaseSource("...")>]-style references resolve at runtime
    let tree, sourceText, checkResults =
        parseAndCheck
            "module M\nlet private thisIsMyVeryLongCaseSource = [ 1 ]\nlet describe () = \"thisIsMyVeryLongCaseSource drives the tests\"\nlet go () = thisIsMyVeryLongCaseSource"

    Assert.Empty(NameQuoting.find true tree sourceText checkResults None)

// ---- FR0135 LiterateComment ----

let private literateIn (source: string) =
    let tree, sourceText = parseNamed "Doc.fsx" source
    LiterateComment.find tree sourceText

[<Fact>]
let ``a fenced block comment in a script becomes a literate cell`` () =
    let source = "(*\n### Setup\n```fsharp\nlet x = 1\n```\n*)\nlet go = 2"

    match literateIn source with
    | [ s ] ->
        let r, text = s.Fix
        let patched = applyEdit source r text
        Assert.StartsWith("(**\n### Setup", patched)
        Assert.True(parsesCleanlyNamed "Doc.fsx" patched)
    | other -> failwithf "Expected one literate suggestion, got %A" other

[<Fact>]
let ``a heading alone is evidence too`` () =
    let source = "(*\n### Usage notes\nplain prose here\n*)\nlet go = 2"

    match literateIn source with
    | [ s ] -> Assert.Equal("a ### heading", s.Evidence)
    | other -> failwithf "Expected one heading suggestion, got %A" other

[<Fact>]
let ``an existing literate cell is already one`` () =
    Assert.Empty(literateIn "(**\n### Setup\n*)\nlet go = 2")

[<Fact>]
let ``a command cell is tooling syntax, not markdown`` () =
    Assert.Empty(literateIn "(*** hide ***)\nlet go = 2")

[<Fact>]
let ``prose without markdown stays a comment`` () =
    Assert.Empty(literateIn "(*\njust words\nacross lines\n*)\nlet go = 2")

[<Fact>]
let ``a compiled file is not a literate script`` () =
    let tree, sourceText = parse "module M\n(*\n### Setup\n```\nx\n```\n*)\nlet go = 2"
    Assert.Empty(LiterateComment.find tree sourceText)

[<Fact>]
let ``a name referenced from an ATTRIBUTE argument never renames`` () =
    // the real TestCaseSource shape: the string lives in the attribute's
    // argument, which is not an indexed expression
    let tree, sourceText, checkResults =
        parseAndCheck
            "module M\nlet private thisIsMyVeryLongCaseSource = [ 1 ]\n[<System.Obsolete(\"see thisIsMyVeryLongCaseSource\")>]\nlet go () = thisIsMyVeryLongCaseSource"

    Assert.Empty(NameQuoting.find true tree sourceText checkResults None)

[<Fact>]
let ``a fully qualified UtcNow write migrates too`` () =
    let source =
        "module Test\n"
        + "type private Row = { Seen: System.DateTime }\n"
        + "let private mk () = { Seen = System.DateTime.UtcNow }"

    match dtoFixIn source with
    | [ (_, Some edits) ] ->
        let patched = applyMigration source edits
        Assert.Contains("{ Seen = System.DateTimeOffset.UtcNow }", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected the qualified migration, got %A" other

// ---- FR0062 setup-singleton gate / FR0067 culture fixes ----

[<Fact>]
let ``a set-once config mutable is the poor man's DI, not churn`` () =
    // assigned once, not from itself: the startup-config / test-seam
    // pattern — no note
    let mutables, _, _ =
        miscIn "module Test\nlet mutable Config = \"default\"\nlet setup (c: string) = Config <- c\nlet get () = Config"

    Assert.Empty mutables

[<Fact>]
let ``a repeatedly assigned public mutable keeps the note`` () =
    let mutables, _, _ =
        miscIn
            "module Test\nlet mutable Current = \"a\"\nlet setA () = Current <- \"a\"\nlet setB () = Current <- \"b\""

    match mutables with
    | [ s ] -> Assert.Equal("Current", s.Name)
    | other -> failwithf "Expected one churn note, got %A" other

[<Fact>]
let ``the culture fix grows the parenthesised argument list`` () =
    let _, parses, _ =
        miscIn "module Test\nlet f (s: string) = System.DateTime.Parse(s)"

    match parses with
    | [ p ] ->
        match p.CultureFix with
        | Some mk ->
            let r, _, replacement = mk "InvariantCulture"
            let source = "module Test\nlet f (s: string) = System.DateTime.Parse(s)"
            let patched = applyEdit source r replacement
            Assert.Contains("System.DateTime.Parse(s, System.Globalization.CultureInfo.InvariantCulture)", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "expected a culture fix"
    | other -> failwithf "Expected one culture suggestion, got %A" other

[<Fact>]
let ``the culture fix wraps a juxtaposed argument`` () =
    let _, parses, _ = miscIn "module Test\nlet f (s: string) = System.DateTime.Parse s"

    match parses with
    | [ p ] ->
        match p.CultureFix with
        | Some mk ->
            let r, _, replacement = mk "InvariantCulture"
            let source = "module Test\nlet f (s: string) = System.DateTime.Parse s"
            let patched = applyEdit source r replacement
            Assert.Contains("System.DateTime.Parse (s, System.Globalization.CultureInfo.InvariantCulture)", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "expected a culture fix"
    | other -> failwithf "Expected one culture suggestion, got %A" other

[<Fact>]
let ``the WebSocket handshake's SHA-1 is the protocol, not a choice`` () =
    // RFC 6455: Sec-WebSocket-Accept is SHA-1 of the key and this GUID, and
    // nothing else will do (Suave's WebSocket.fs spells the GUID)
    let tree, sourceText =
        parse
            "module Test\nopen System.Security.Cryptography\nlet magicGUID = \"258EAFA5-E914-47DA-95CA-C5AB0DC85B11\"\nlet sha1 (x: string) =\n    let algo = SHA1.Create()\n    algo.ComputeHash(System.Text.Encoding.ASCII.GetBytes x)"

    let crypto, _, _ = SecurityRules.find tree sourceText (fun _ -> false)
    Assert.Empty crypto

    // without the GUID the same SHA1 is a choice
    let tree2, sourceText2 =
        parse
            "module Test\nopen System.Security.Cryptography\nlet sha1 (x: string) =\n    let algo = SHA1.Create()\n    algo.ComputeHash(System.Text.Encoding.ASCII.GetBytes x)"

    let crypto2, _, _ = SecurityRules.find tree2 sourceText2 (fun _ -> false)
    Assert.NotEmpty crypto2

[<Fact>]
let ``SHA-1 in a match arm whose sibling constructs SHA-256 is a format option`` () =
    // the compiler's --checksumalgorithm (ilwritepdb, ilwrite): the strong
    // algorithm is on offer in the next arm, SHA-1 is what the caller asked
    let tree, sourceText =
        parse
            "module Test\nopen System.Security.Cryptography\ntype Checksum =\n    | Sha1\n    | Sha256\nlet algorithm (c: Checksum) : HashAlgorithm =\n    match c with\n    | Sha1 -> SHA1.Create() :> HashAlgorithm\n    | Sha256 -> SHA256.Create() :> HashAlgorithm"

    let crypto, _, _ = SecurityRules.find tree sourceText (fun _ -> false)
    Assert.Empty crypto

    // a match whose arms all pick weak hashes has no strong sibling
    let tree2, sourceText2 =
        parse
            "module Test\nopen System.Security.Cryptography\nlet algorithm (md5: bool) : HashAlgorithm =\n    match md5 with\n    | true -> MD5.Create() :> HashAlgorithm\n    | false -> SHA1.Create() :> HashAlgorithm"

    let crypto2, _, _ = SecurityRules.find tree2 sourceText2 (fun _ -> false)
    Assert.Equal(2, crypto2.Length)

[<Fact>]
let ``the weak protocol constant swaps to Tls12`` () =
    let tree, sourceText =
        parse
            "module Test\nopen System.Net\nlet setup () =\n    ServicePointManager.SecurityProtocol <- SecurityProtocolType.Tls11"

    let crypto, _, _ = SecurityRules.find tree sourceText (fun _ -> false)

    match crypto with
    | [ s ] ->
        match s.AlgoRange with
        | Some r ->
            let source =
                "module Test\nopen System.Net\nlet setup () =\n    ServicePointManager.SecurityProtocol <- SecurityProtocolType.Tls11"

            let patched = applyEdit source r "Tls12"
            Assert.Contains("SecurityProtocolType.Tls12", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "expected the protocol ident range"
    | other -> failwithf "Expected one protocol suggestion, got %A" other

[<Fact>]
let ``an existing Globalization open keeps the culture spelling short`` () =
    let source =
        "module Test\nopen System.Globalization\nlet f (s: string) = System.DateTime.Parse(s)"

    let _, parses, _ = miscIn source

    match parses with
    | [ p ] ->
        match p.CultureFix with
        | Some mk ->
            let r, _, replacement = mk "InvariantCulture"
            let patched = applyEdit source r replacement
            Assert.Contains("System.DateTime.Parse(s, CultureInfo.InvariantCulture)", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "expected a culture fix"
    | other -> failwithf "Expected one culture suggestion, got %A" other

// ---- FR0136 EmptyGuid ----

let private emptyGuidIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    EmptyGuid.find tree sourceText checkResults

[<Fact>]
let ``a zero-argument Guid constructor states Empty`` () =
    let source = "module M\nopen System\nlet id = Guid()"

    match emptyGuidIn source with
    | [ s ] ->
        Assert.Equal("Guid.Empty", s.EmptyText)
        Assert.Equal("Guid.NewGuid()", s.NewGuidText)
        let patched = applyEdit source s.Range s.EmptyText
        Assert.Contains("let id = Guid.Empty", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one Guid suggestion, got %A" other

[<Fact>]
let ``new System Guid keeps its qualification`` () =
    let source = "module M\nlet id = new System.Guid()"

    match emptyGuidIn source with
    | [ s ] ->
        Assert.Equal("System.Guid.Empty", s.EmptyText)
        let patched = applyEdit source s.Range s.NewGuidText
        Assert.Contains("let id = System.Guid.NewGuid()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified Guid suggestion, got %A" other

[<Fact>]
let ``a Guid built FROM something is deliberate`` () =
    Assert.Empty(emptyGuidIn "module M\nlet id (s: string) = System.Guid(s)")

[<Fact>]
let ``a user type named Guid is not System Guid`` () =
    Assert.Empty(emptyGuidIn "module M\ntype Guid() = class end\nlet g = Guid()")

[<Fact>]
let ``inside a query the whole culture suggestion stands down`` () =
    // the quotation belongs to the database's type system — no cultures
    // there, and the two-argument Parse can stop a provider translating
    let source =
        "module M\nlet f (xs: System.Linq.IQueryable<string>) =\n    query {\n        for x in xs do\n        where (System.DateTime.Parse(x) > System.DateTime.MinValue)\n        select x\n    }"

    let _, parses, _ = miscIn source
    Assert.Empty parses

[<Fact>]
let ``compact tuple spelling keeps its compact field names`` () =
    let source = "module M\ntype private Mut =\n    | RxAndRy of int*int\n    | Nothing"

    match duNamesIn source with
    | [ s ] ->
        let patched = applyMigration source s.Edits
        Assert.Contains("| RxAndRy of rx:int*ry:int", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one compact suggestion, got %A" other

// ---- FR0035 startup-set quick-fix ----

let private containsIn (source: string) =
    let tree, sourceText = parse source
    let contains, _ = LoopPerf.find false tree sourceText
    contains

[<Fact>]
let ``a startup list whose only uses are probes converts in place to a Set`` () =
    let source =
        "module M\nlet private allowed = [ \"a\"; \"b\"; \"c\" ]\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then\n            printfn \"%s\" x"

    match containsIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fix
        let patched = applyMigration source s.Fix
        Assert.Contains("let private allowed = [ \"a\"; \"b\"; \"c\" ] |> Set.ofList", patched)
        Assert.Contains("if allowed.Contains x then", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``a list with other uses keeps its type and gains the HashSet companion`` () =
    // the stray List.length use pins the binding's type, so the fix
    // reaches for the shadow set instead of converting in place
    let source =
        "module M\nlet allowed = [ \"a\"; \"b\"; \"c\" ]\nlet count = List.length allowed\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then\n            printfn \"%s\" x"

    match containsIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fix
        let patched = applyMigration source s.Fix
        Assert.Contains("let private allowedProbeSet = System.Collections.Generic.HashSet(allowed)", patched)
        Assert.Contains("if allowedProbeSet.Contains x then", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``a companion for probes under an #if lands under the same #if`` () =
    // the collection is unconditional, the probe is not: the companion
    // serves the probe, so it takes the probe's condition
    let source =
        "module M\nlet allowed = [ \"a\"; \"b\"; \"c\" ]\nlet count = List.length allowed\n#if !FOO\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then\n            printfn \"%s\" x\n#endif"

    match containsIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fix
        let patched = applyMigration source s.Fix

        Assert.Contains(
            "#if !FOO\nlet private allowedProbeSet = System.Collections.Generic.HashSet(allowed)\n#endif\n",
            patched
        )

        Assert.Contains("if allowedProbeSet.Contains x then", patched)
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``probes under different conditions get no companion`` () =
    let source =
        "module M\nlet allowed = [ \"a\"; \"b\"; \"c\" ]\nlet count = List.length allowed\n#if !FOO\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then\n            printfn \"%s\" x\n#endif\nlet g (ys: string list) =\n    for y in ys do\n        if List.contains y allowed then\n            printfn \"%s\" y"

    match containsIn source with
    | suggestions -> Assert.All(suggestions, (fun s -> Assert.Empty s.Fix))

[<Fact>]
let ``an array literal converts with ofArray`` () =
    let source =
        "module M\nlet private allowed = [| 1; 2; 3 |]\nlet f (xs: int list) =\n    for x in xs do\n        if Array.contains x allowed then\n            printfn \"%d\" x"

    match containsIn source with
    | [ s ] ->
        let patched = applyMigration source s.Fix
        Assert.Contains("[| 1; 2; 3 |] |> Set.ofArray", patched)
        Assert.Contains("if allowed.Contains x then", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``a shadowed collection name keeps the note only`` () =
    // a parameter of the same name makes resolution ambiguous to a
    // parse-only scan
    let source =
        "module M\nlet allowed = [ \"a\" ]\nlet f (allowed: string list) (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then\n            printfn \"%s\" x"

    match containsIn source with
    | [ s ] -> Assert.Empty s.Fix
    | other -> failwithf "Expected the note without a fix, got %A" other

[<Fact>]
let ``a dotted-path collection keeps the note only`` () =
    let source =
        "module M\ntype C = { Allowed: string list }\nlet f (c: C) (xs: string list) =\n    for x in xs do\n        if List.contains x c.Allowed then\n            printfn \"%s\" x"

    match containsIn source with
    | [ s ] -> Assert.Empty s.Fix
    | other -> failwithf "Expected the dotted note, got %A" other

[<Fact>]
let ``two probes of one startup list convert together with one companion`` () =
    let source =
        "module M\nlet private allowed = [ \"a\"; \"b\" ]\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x allowed then printfn \"a\"\nlet g (ys: string list) =\n    for y in ys do\n        if List.contains y allowed then printfn \"b\""

    match containsIn source with
    | [ s1; s2 ] ->
        Assert.Equal(3, (s1.Fix @ s2.Fix).Length) // one conversion + two rewrites, carried once
        let patched = applyMigration source (s1.Fix @ s2.Fix)
        Assert.Equal(1, System.Text.RegularExpressions.Regex.Matches(patched, "Set.ofList").Count)
        Assert.Contains("if allowed.Contains x then", patched)
        Assert.Contains("if allowed.Contains y then", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two contains suggestions, got %A" other

// ---- FR0005 return!-identity collapse / FR0029 single-return arms ----

let private ceStripIn (source: string) =
    let tree, sourceText = parse source
    CeStrip.find tree sourceText

[<Fact>]
let ``a return-bang around a single-return task is a no-op machine`` () =
    let source =
        "module M\nlet f (t: System.Threading.Tasks.Task<int>) =\n    task {\n        return! task {\n            return! t\n        }\n    }"

    match
        ceStripIn source
        |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ReturnBangIdentity)
    with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Contains("return! t", patched)
        Assert.False(patched.Contains "return! task {")
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one identity strip, got %A" other

[<Fact>]
let ``nested no-op machines unwind layer by layer`` () =
    // the management-portal damage shape: each pass strips one layer
    let source =
        "module M\nlet f (t: System.Threading.Tasks.Task<int>) =\n    task {\n        return! task {\n            return! task {\n                return! t\n            }\n        }\n    }"

    let strips =
        ceStripIn source
        |> List.filter (fun s -> s.Kind = CeStrip.StripKind.ReturnBangIdentity)

    Assert.True(strips.Length >= 1)

[<Fact>]
let ``a single return-bang arm is never wrapped`` () =
    // wrapping `| A -> return! X` moves nothing out of the machine and
    // once re-wrapped itself every pass
    let source =
        "module Test\nlet g () = System.Threading.Tasks.Task.FromResult 1\nlet f (cond: bool) =\n    task {\n        match cond with\n        | true ->\n            return! g ()\n        | false ->\n            let! a = g ()\n            let! b = g ()\n            let! c = g ()\n            let! d = g ()\n            let! e = g ()\n            let! h = g ()\n            let! i = g ()\n            let! j = g ()\n            return a + b + c + d + e + h + i + j\n    }"

    let taskAdviceIn (src: string) =
        let tree, sourceText = parse src
        TaskStateMachine.find tree sourceText 4 false Set.empty

    let splits =
        taskAdviceIn source
        |> List.tryPick (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.SplitBranches -> Some s.Edits
            | _ -> None)

    match splits with
    | Some edits ->
        // the true arm (single return!) must not appear in any edit
        for r, _ in edits do
            Assert.False(r.StartLine <= 7 && r.EndLine >= 7 && r.StartLine > 5)
    | None -> ()

[<Fact>]
let ``FR0013 leaves parens alone inside a shorthand lambda`` () =
    // `_.` demands an ATOMIC body: `_.reshape([| n |])` compiles and
    // `_.reshape [| n |]` does not. Found on toro, where six of these were
    // applied, broke the build and were rolled back
    let source =
        "module Test\ntype Box() =\n    member _.reshape(a: int64[]) = a\nlet f (bs: Box list) = bs |> List.map _.reshape([| 1L |])"

    let tree, sourceText = parse source
    Assert.Empty(RedundantParens.find tree sourceText)

[<Fact>]
let ``FR0130 withholds where a signature declares the value and cannot be read`` () =
    // `[<Literal>]` is part of what a signature must agree on, so annotating
    // only the implementation gives "The literal constant values and/or
    // attributes differ" (found on Fable's fcs-fable, 176 signature files).
    // With the cross-file parser installed the signature is edited in step
    // (SignatureCoEditTests); without one, as in an editor, the fix for a
    // non-private value is withheld rather than offered half-done
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-fsi-" + System.Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let impl = Path.Combine(dir, "M.fs")
        File.WriteAllText(Path.Combine(dir, "M.fsi"), "module M\n\nval internal version: string\n")
        let source = "module M\n\nlet internal version = \"1.0\"\n"
        File.WriteAllText(impl, source)

        ProjectSources.configure None
        let tree, sourceText = parseNamed impl source
        Assert.Empty(LiteralConst.find false tree sourceText)

        // ...and the same source without a signature beside it still qualifies
        let lone = Path.Combine(dir, "N.fs")
        File.WriteAllText(lone, source)
        let loneTree, loneText = parseNamed lone source
        Assert.NotEmpty(LiteralConst.find false loneTree loneText)
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``FR0070 keeps a record a class when its fields are read inside a quotation`` () =
    // a struct local captured in a quotation lambda cannot have a field
    // read — that takes its address, which quotations forbid
    // (Linq.Expression.Optimizer's query tests)
    let source =
        "module Test\ntype private Itm = { x: int }\nlet q (items: Itm list) = <@ items |> List.filter (fun i -> i.x = 3) @>"

    let _, structs, _ = structHintsIn source

    match structs with
    | [ s ] ->
        Assert.Equal("Itm", s.TypeName)
        Assert.True(s.Fix.IsNone, "a quoted field read must leave the struct fix out")
    | other -> failwithf "Expected one struct hint, got %A" other

[<Fact>]
let ``FR0070 still offers the struct fix when the quotation reads other fields`` () =
    let source =
        "module Test\ntype private Itm = { x: int }\ntype private Other = { y: int }\nlet q (items: Other list) = <@ items |> List.filter (fun i -> i.y = 3) @>"

    let _, structs, _ = structHintsIn source
    Assert.Contains(structs, fun s -> s.TypeName = "Itm" && s.Fix.IsSome)

[<Fact>]
let ``FR0121: a same-day comparison against a Date is not a calendar cut`` () =
    // FSharp.Data's TimeOnly probe: TryParse fills in today's date, and the
    // check `dt.Date <> DateTime.Today` asks whether a real date was given
    Assert.Empty(
        wallClocksIn
            "module Test\nopen System\nlet hasRealDate (dt: DateTime) = dt.Date <> DateTime.Today\nlet isToday (dt: DateTime) = DateTime.Today = dt.Date"
    )

[<Fact>]
let ``FR0121: Today used as a value is still a calendar cut`` () =
    match wallClocksIn "module Test\nopen System\nlet stamp () = DateTime.Today.AddDays 1.0" with
    | [ _ ] -> ()
    | other -> failwithf "Expected one wall-clock note, got %A" other

[<Fact>]
let ``FR0123: a guarded Enter whose body binds in a computation is not called a leak`` () =
    // SQLProvider's providers: Enter, try ... finally Exit around a task
    // body — the shape cannot leak, only the lock rewrite is withheld
    match
        monitorLocksIn
            "module Test\nopen System.Threading\nlet gate = obj ()\nlet run (work: System.Threading.Tasks.Task<int>) =\n    task {\n        Monitor.Enter gate\n        try\n            let! v = work\n            return v + 1\n        finally\n            Monitor.Exit gate\n    }"
    with
    | [ s ] ->
        Assert.True(s.Guarded)
        Assert.Equal(None, s.Fix)
    | other -> failwithf "Expected one guarded lock note, got %A" other

// ---- widenings from the C:\git sweep ----

[<Fact>]
let ``FR0068: enum aliases spelled with unsigned suffixes are duplicates too`` () =
    // a PLAIN enum (the [<Flags>] table this shape came from is now
    // exempt): `16384u` keys the same as `16384`, so the second name for
    // the value is still the duplicate
    let _, _, enums =
        miscIn
            "module Test\ntype Section =\n    | MemProtected = 16384u\n    | NoDeferSpecExc = 16384u\n    | GPRel = 32768u"

    match enums with
    | [ e ] -> Assert.Equal("NoDeferSpecExc", e.CaseName)
    | other -> failwithf "Expected one duplicate, got %A" other

[<Fact>]
let ``FR0122: the bare Regex constructor under the open is checked`` () =
    match invalidPatternsIn "module Test\nopen System.Text.RegularExpressions\nlet r = Regex(\"(unclosed\")" with
    | [ (_, pattern, _) ] -> Assert.Equal("(unclosed", pattern)
    | other -> failwithf "Expected one invalid pattern, got %A" other

[<Fact>]
let ``FR0122: a pattern valid only under IgnorePatternWhitespace is compiled with it`` () =
    Assert.Empty(
        invalidPatternsIn
            "module Test\nopen System.Text.RegularExpressions\nlet r = Regex(\"a b # a comment (\", RegexOptions.IgnorePatternWhitespace)"
    )

[<Fact>]
let ``FR0127: a connection string carrying a real password is a leak, a placeholder is not`` () =
    match
        secretsIn
            "module Test\nlet cs = \"Data Source=db.example.net;Initial Catalog=x;User Id=app;Password=W3lf0rd!Prod\"\nlet sample = \"Server=.;Database=x;User Id=sa;Password=password\""
    with
    | [ s ] -> Assert.Equal("connection-string password", s.Provider)
    | other -> failwithf "Expected exactly one connection-string leak, got %A" other

[<Fact>]
let ``FR0127: a type provider's connection-string argument and a three-segment JWT are scanned`` () =
    let found =
        secretsIn
            "module Test\ntype Db = SqlDataProvider<ConnectionString = \"Server=db;Database=x;Uid=app;Pwd=Sup3rS3cret9\">\nlet token = \"eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.SflKxwRJSMeKKF2QT4fwpMeJf36POk6yJV_adQssw5c\"\nlet header = \"eyJ0eXAiOiJKV1QiLCJhbGciOiJIUzI1NiJ9\""
        |> List.map (fun s -> s.Provider)
        |> List.sort

    Assert.Equal<string list>([ "JWT"; "connection-string password" ], found)

[<Fact>]
let ``FR0153: a credential in a Literal on a remote server still fires, as a design-time one`` () =
    // the instance suffix is spelled with a doubled backslash so the ANALYSED
    // source carries the single one a connection string really has
    match
        secretsIn
            "module Test\n[<Literal>]\nlet connstr = \"Data Source=157.24.1.223\\SQL2017;User Id=sa;Password=Password12!; Initial Catalog=sqlprovider;TrustServerCertificate=true;\""
    with
    | [ s ] ->
        Assert.Equal("connection-string password", s.Provider)
        Assert.True(s.DesignTimeLiteral, "a [<Literal>] binding is a design-time credential")
    | other -> failwithf "Expected exactly one leak on a remote server, got %A" other

[<Fact>]
let ``FR0153: a public IP is not the loopback, however dotted`` () =
    for host in
        [ "157.24.1.223"
          "157.24.6.126"
          "127.0.0.100"
          "10.0.0.5"
          "localhost.evil.com"
          "notlocalhost" ] do
        let source =
            $"module Test\nlet cs = \"Data Source=%s{host};Initial Catalog=x;User Id=sa;Password=W3lf0rd9Prod\""

        match secretsIn source with
        | [ s ] -> Assert.Equal("connection-string password", s.Provider)
        | other -> failwithf "Expected %s to report a leak, got %A" host other

[<Fact>]
let ``FR0153: a loopback server is a developer's own machine, whatever the password looks like`` () =
    for host in
        [ "localhost"
          "127.0.0.1"
          "127.0.0.1,1433"
          "localhost\\SQLEXPRESS"
          "(local)"
          "(localdb)\\MSSQLLocalDB"
          "."
          ".\\SQLEXPRESS"
          "::1" ] do
        let source =
            $"module Test\nlet cs = \"Data Source=%s{host};Initial Catalog=x;User Id=sa;Password=Hunter2Real9x\""

        Assert.Empty(secretsIn source)

[<Fact>]
let ``FR0153: the same credential outside a Literal is not design-time`` () =
    match
        secretsIn
            "module Test\nlet cs = \"Data Source=db.corp.example.com;Initial Catalog=x;User Id=sa;Password=W3lf0rd9Prod\""
    with
    | [ s ] -> Assert.False(s.DesignTimeLiteral, "a plain let is not a design-time literal")
    | other -> failwithf "Expected exactly one leak, got %A" other

[<Fact>]
let ``FR0124: a template spelled as a chain of literals is read whole`` () =
    match
        logTemplatesIn
            "module M =
    let f (logger: ILogger) (a: string) (b: string) = logger.LogError(\"only {Pinned} of {Blocks} blocks \" + \"pinned; pin all {Blocks} blocks\", a, b, b)"
    with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.DuplicateName "Blocks", s.Problem)
    | other -> failwithf "Expected one duplicate-name finding, got %A" other

[<Fact>]
let ``FR0124: an array literal as the params argument counts its elements`` () =
    Assert.Empty(
        logTemplatesIn
            "module M =
    let f (logger: ILogger) (a: int) (b: int) (c: int) = logger.LogError(\"a={A}; b={B}; c={C}\", [| box a; box b; box c |])"
    )

[<Fact>]
let ``FR0124: Serilog's static Log carries the same template rules`` () =
    match
        logTemplatesIn
            "namespace Serilog\ntype Log =\n    static member Information(template: string, [<System.ParamArray>] args: obj[]) = ignore (template, args)\nnamespace Test\nopen Serilog\nmodule M =\n    let f (user: string) = Log.Information($\"Refreshed token for {user}\")"
    with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.Interpolated, s.Problem)
    | other -> failwithf "Expected one interpolated-template finding, got %A" other

// ---- FR0066 / FR0146: unparametrized SQL ----

[<Fact>]
let ``FR0066: a dynamic string bound one hop before the command is the same leak`` () =
    let _, sqls, _ =
        securityIn
            "module Test\nlet f (con: MySql.Data.MySqlClient.MySqlConnection) (keys: string list) =\n    let querySql = \"SELECT Skey FROM setting WHERE Skey IN (\" + String.concat \",\" keys + \")\"\n    use command = new MySqlCommand(querySql, con)\n    command"

    match sqls with
    | [ s ] ->
        Assert.Equal("MySqlCommand", s.Sink)
        Assert.False s.Unparametrized
    | other -> failwithf "Expected one string-built SQL finding, got %A" other

[<Fact>]
let ``FR0066: CreateCommand and a helper named for SQL are sinks`` () =
    let _, sqls, _ =
        securityIn
            "module Test\nlet g (provider: ISqlProvider) (con: obj) (name: string) =\n    use com = provider.CreateCommand(con, $\"SELECT typeof([{name}]) FROM t\")\n    executeSql (\"UPDATE t SET x = '\" + name + \"'\") []"

    Assert.Equal<string list>([ "CreateCommand"; "executeSql" ], sqls |> List.map (fun s -> s.Sink))

[<Fact>]
let ``FR0146: a literal statement with no parameter marker is suspicious, a parametrized one is not`` () =
    let _, sqls, _ =
        securityIn
            "module Test\nlet h (cmd: System.Data.IDbCommand) =\n    cmd.CommandText <- \"SELECT * FROM users\"\n    cmd.CommandText <- \"SELECT * FROM users WHERE id = @id\"\n    cmd.CommandText <- \"CREATE TABLE t (id int)\""

    match sqls with
    | [ s ] ->
        Assert.True s.Unparametrized
        Assert.Equal("CommandText", s.Sink)
    | other -> failwithf "Expected one unparametrized finding, got %A" other

[<Literal>]
let private logaryScaffold =
    "namespace Logary\nmodule Message =\n    let eventInfo (template: string) = template\n    let eventWarn (template: string) = template\n    let setField (name: string) (value: obj) (message: string) = ignore (name, value); message\nnamespace Test\nopen Logary\n"

let private logaryTemplatesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck (logaryScaffold + source)
    LogTemplates.find tree sourceText checkResults

[<Fact>]
let ``FR0124: a Logary placeholder no setField fills is reported`` () =
    match
        logaryTemplatesIn
            "module M =\n    let f (writeLog: string -> unit) (query: string) =\n        Message.eventInfo \"Executing {sql} for {user}\" |> Message.setField \"sql\" (box query) |> writeLog"
    with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.MissingFields [ "user" ], s.Problem)
    | other -> failwithf "Expected one missing-field finding, got %A" other

[<Fact>]
let ``FR0124: a Logary pipeline that fills every placeholder is fine, point-free too`` () =
    Assert.Empty(
        logaryTemplatesIn
            "module M =\n    let f (writeLog: string -> unit) (query: string) (err: string) =\n        Message.eventInfo \"Executing {sql}\" |> Message.setField \"sql\" (box query) |> writeLog\n        \"SetupTest err: {err}\" |> Message.eventInfo |> Message.setField \"err\" (box err) |> writeLog"
    )

[<Fact>]
let ``FR0124: an interpolated Logary template is flagged`` () =
    match
        logaryTemplatesIn
            "module M =\n    let f (writeLog: string -> unit) (id: int) =\n        Message.eventWarn $\"Null ref for {id}\" |> writeLog"
    with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.Interpolated, s.Problem)
    | other -> failwithf "Expected one interpolated finding, got %A" other

// ---- FR0120 across logging libraries ----

[<Fact>]
let ``FR0120: a Serilog Log.Error in a handler that forgets the exception gets it first`` () =
    let source =
        "namespace Serilog\ntype Log =\n    static member Error(template: string, [<System.ParamArray>] args: obj[]) = ignore (template, args)\n    static member Error(ex: exn, template: string, [<System.ParamArray>] args: obj[]) = ignore (ex, template, args)\nnamespace Test\nopen Serilog\nmodule M =\n    let go (id: int) =\n        try ()\n        with ex -> Log.Error(\"sync failed {Id}\", id)"

    match catchLogsIn source with
    | [ s ] ->
        Assert.Equal("Serilog", s.Family)
        Assert.Equal("ex", s.ExceptionName)
        Assert.Equal("Error", s.LogMethod)
    | other -> failwithf "Expected one Serilog finding, got %A" other

[<Fact>]
let ``FR0120: a Logary event pipeline in a handler without addExn gets the stage`` () =
    let source =
        "namespace Logary\nmodule Message =\n    let eventError (template: string) = template\n    let setField (name: string) (value: obj) (message: string) = ignore (name, value); message\n    let addExn (ex: exn) (message: string) = ignore ex; message\nnamespace Test\nopen Logary\nmodule M =\n    let go (writeLog: string -> unit) (id: int) =\n        try ()\n        with ex -> Message.eventError \"sync failed {Id}\" |> Message.setField \"Id\" (box id) |> writeLog"

    match catchLogsIn source with
    | [ s ] ->
        Assert.Equal("Logary", s.Family)
        // the insertion point sits right after the event stage
        let patched = applyEdit (loggerScaffold + source) s.Range " |> Message.addExn ex"
        Assert.Contains("Message.eventError \"sync failed {Id}\" |> Message.addExn ex |> Message.setField", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one Logary finding, got %A" other

[<Fact>]
let ``FR0120: a Logary pipeline that already adds the exception is fine`` () =
    Assert.Empty(
        catchLogsIn
            "namespace Logary\nmodule Message =\n    let eventError (template: string) = template\n    let addExn (ex: exn) (message: string) = ignore ex; message\nnamespace Test\nopen Logary\nmodule M =\n    let go (writeLog: string -> unit) =\n        try ()\n        with ex -> Message.eventError \"sync failed\" |> Message.addExn ex |> writeLog"
    )

[<Fact>]
let ``FR0146: a literal statement handed to a SQL helper with an empty parameter list is the same no-parameter command``
    ()
    =
    let _, sqls, _ =
        securityIn
            "module Test\nlet maxEventId (readSqlInteger: string -> obj list -> int) = readSqlInteger \"select max(id) from events\" []\nlet byId (readSqlInteger: string -> obj list -> int) (id: int) = readSqlInteger \"select count(*) from events where id = @id\" [ box id ]"

    match sqls with
    | [ s ] ->
        Assert.True s.Unparametrized
        Assert.Equal("readSqlInteger", s.Sink)
    | other -> failwithf "Expected one unparametrized helper finding, got %A" other

[<Fact>]
let ``FR0127: a connection string mentioning test anywhere is a fixture, not a leak`` () =
    Assert.Empty(
        secretsIn
            "module Test\nlet cs = \"Data Source=db.example.net;Initial Catalog=welendus_test_database;User Id=app;Password=W3lf0rd!Prod\"\nlet cs2 = \"Server=.;Database=x;User Id=sa;Password=TestW3lf0rd!\""
    )

[<Fact>]
let ``FR0124: Logary fields set by other stages are not missing, and setFieldValue names its field`` () =
    let scaffold =
        "namespace Logary\nmodule Message =\n    let eventInfo (template: string) = template\n    let setField (name: string) (value: obj) (message: string) = ignore (name, value); message\n    let setFieldValue (name: string) (value: obj) (message: string) = ignore (name, value); message\n    let setFieldsFromObject (o: obj) (message: string) = ignore o; message\nnamespace Test\nopen Logary\n"

    let source =
        scaffold
        + "module M =\n    let f (writeLog: string -> unit) (query: string) =\n        Message.eventInfo \"Executing {sql} for {user}\" |> Message.setField \"sql\" (box query) |> Message.setFieldsFromObject (box query) |> writeLog\n    let g (writeLog: string -> unit) (query: string) =\n        Message.eventInfo \"Executing {sql}\" |> Message.setFieldValue \"sql\" (box query) |> writeLog"

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(LogTemplates.find tree sourceText checkResults)

[<Fact>]
let ``FR0121: a translator arm that maps a member named Now to the clock is not a clock read`` () =
    // SQLProvider's expression-tree evaluator reproduces DateTime.Now on
    // purpose: `when me.Member.Name = "Now" -> DateTime.Now` is a table
    let source =
        "module M\nlet eval (name: string) : obj option =\n    match name with\n    | n when n = \"Now\" -> Some(box System.DateTime.Now)\n    | \"Today\" -> Some(box System.DateTime.Today)\n    | _ -> None\nlet stamp () = System.DateTime.Now"

    match wallClocksIn source with
    | [ s ] -> Assert.Equal(7, s.Range.StartLine)
    | other -> failwithf "Expected only the plain clock read, got %A" other

[<Fact>]
let ``FR0072: a hidden case another union in scope also names is written qualified`` () =
    // suave's Http2.fs matched a Result; `Error` there is ScanResult.Error
    // from an earlier file of the project, and a bare `Error _` typed wrong
    let lib = "namespace Lib\ntype ScanResult =\n    | NeedMore\n    | Error of string"

    let user =
        "module Example\nopen Lib\nlet f (r: Result<int, string>) =\n    match r with\n    | Ok v -> v\n    | _ -> 0"

    let tree, sourceText, checkResults = parseAndCheckSecond lib user

    match ExpandWildcard.find tree sourceText checkResults with
    | [ s ] -> Assert.Equal("Result.Error _", s.ReplacementText)
    | other -> failwithf "Expected one wildcard note, got %A" other

[<Fact>]
let ``FR0072: a hidden case nobody else names stays bare`` () =
    assertExpanded "let f (r: Result<int, string>) =\n    match r with\n    | Ok v -> v\n    | _ -> 0" "Error _"

// ---- FR0035 visibility gate on the in-place Set conversion (fsharplint) ----

[<Fact>]
let ``FR0035: a PUBLIC startup list keeps its type and gets the HashSet companion`` () =
    // fsharplint's public `testMethodAttributes` list, in a NuGet library,
    // was converted to a Set<string> — an API change without --api-changes
    let source =
        "module M\nlet testMethodAttributes = [ \"Test\"; \"TestMethod\" ]\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x testMethodAttributes then\n            printfn \"%s\" x"

    match containsIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fix
        let patched = applyMigration source s.Fix
        Assert.DoesNotContain("Set.ofList", patched)
        Assert.Contains("let testMethodAttributes = [ \"Test\"; \"TestMethod\" ]", patched)

        Assert.Contains(
            "let private testMethodAttributesProbeSet = System.Collections.Generic.HashSet(testMethodAttributes)",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``FR0035: a public list converts in place under --api-changes`` () =
    let source =
        "module M\nlet testMethodAttributes = [ \"Test\"; \"TestMethod\" ]\nlet f (xs: string list) =\n    for x in xs do\n        if List.contains x testMethodAttributes then\n            printfn \"%s\" x"

    let tree, sourceText = parse source

    match fst (LoopPerf.find true tree sourceText) with
    | [ s ] ->
        let patched = applyMigration source s.Fix
        Assert.Contains("|> Set.ofList", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

[<Fact>]
let ``FR0035: a list in a private module converts in place`` () =
    let source =
        "module M\nmodule private Inner =\n    let allowed = [ \"a\"; \"b\" ]\n    let f (xs: string list) =\n        for x in xs do\n            if List.contains x allowed then\n                printfn \"%s\" x"

    match containsIn source with
    | [ s ] ->
        let patched = applyMigration source s.Fix
        Assert.Contains("|> Set.ofList", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one contains suggestion, got %A" other

// ---- FR0132 comment and file guards (suave, test fixtures) ----

[<Fact>]
let ``FR0132: a test file's fixtures keep their trailing notes`` () =
    // `let emojiParty = "\U0001F389" // 🎉 PARTY POPPER` labels a fixture
    Assert.Empty(
        commentDocIn
            "module M\nopen Xunit\nlet emojiParty = \"\U0001F389\" // party popper fixture\n[<Fact>]\nlet ``uses it`` () = Assert.NotNull emojiParty"
    )

[<Fact>]
let ``FR0132: a test attribute marks the file without a framework open`` () =
    Assert.Empty(
        commentDocIn "module M\nlet emojiParty = \"x\" // party popper fixture for tests\n[<Test>]\nlet check () = ()"
    )

[<Fact>]
let ``FR0132: a punctuation marker is an annotation, not a summary`` () =
    // suave: `// ^ Index is out of range`, `// -- node no.`
    Assert.Empty(commentDocIn "module M\nlet index (xs: int[]) i = xs.[i] // ^ Index is out of range")
    Assert.Empty(commentDocIn "module M\nlet nodeNo (n: int) = n + 1 // -- node no. of the parent")

[<Fact>]
let ``FR0132: a single word or a short note stays in the margin`` () =
    Assert.Empty(commentDocIn "module M\nlet legacy (x: int) = x // unused")
    Assert.Empty(commentDocIn "module M\nlet legacy (x: int) = x // old api")

// ---- FR0071 only work is hoisted (Mibo's Primitive3D) ----

[<Fact>]
let ``FR0071: a bare identifier copy does no work and stays in the loop`` () =
    // `let ny = sinPhi` was hoisted out of the inner loop, separated from
    // the `nx`/`nz` it belongs with
    Assert.Empty(
        invariantsIn
            "let sink (a: float) (b: float) = ()\nlet run (sinPhi: float) (cosPhi: float) =\n    for x = 0 to 100 do\n        let ny = sinPhi\n        let nx = cosPhi * float x\n        sink nx ny"
    )

[<Fact>]
let ``FR0071: a constant copy stays in the loop`` () =
    Assert.Empty(
        invariantsIn
            "let sink (n: int) = ()\nlet run () =\n    for x = 0 to 100 do\n        let c = 3\n        sink (x + c)"
    )


// ---- FR0131 RecTailCall: byref parameters (F# compiler TaggedCollections.fs) ----

[<Fact>]
let ``FR0131 a byref parameter passed along by address is never attributed`` () =
    // the F# compiler's TaggedCollections.fs `tryGetValue ... (v: byref<'Value>)`
    // recurses with `&v`: the compiler's own tail-call checker refuses byref
    // arguments, so [<TailCall>] there manufactures the FS3569 it guards against
    let source =
        "module M\nlet rec tryGetValue (key: int) (xs: (int * int) list) (v: byref<int>) : bool =\n    match xs with\n    | [] -> false\n    | (k, x) :: t ->\n        if k = key then\n            v <- x\n            true\n        else\n            tryGetValue key t &v"

    Assert.True(typechecksCleanly source, "the fixture itself must typecheck")
    Assert.Empty(tailCallsIn source)

[<Fact>]
let ``FR0131 an inref parameter vetoes the binding too`` () =
    let source =
        "module M\nlet rec count (n: int) (r: inref<int>) : int =\n    if n <= 0 then r else count (n - 1) &r"

    Assert.True(typechecksCleanly source, "the fixture itself must typecheck")
    Assert.Empty(tailCallsIn source)

[<Fact>]
let ``FR0131 the byref-free accumulator loop still gains TailCall`` () =
    let source =
        "module M\nlet rec count (n: int) (acc: int) : int =\n    if n <= 0 then acc else count (n - 1) (acc + n)"

    match tailCallsIn source with
    | [ s ] ->
        Assert.Equal("count", s.Name)
        let r, text = s.Fix
        assertTailCallClean (applyEdit source r text)
    | other -> failwithf "Expected one TailCall suggestion, got %A" other


[<Fact>]
let ``FR0123: the lock lambda closes at the end of its last line`` () =
    // the compiler's illib.fs: a `)` on a line of its own is not the layout
    // fantomas --check accepts; it belongs after the body's last line
    let source =
        "module M =\n    let gate = obj ()\n    let mutable count = 0\n    let bump () =\n        System.Threading.Monitor.Enter gate\n        try\n            count <- count + 1\n            count\n        finally\n            System.Threading.Monitor.Exit gate"

    match monitorLocksIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.Equal("lock gate (fun () ->\n            count <- count + 1\n            count)", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the lock rewrite"
    | other -> failwithf "Expected one monitor suggestion, got %A" other

[<Fact>]
let ``FR0123: a comment ending the body keeps the paren on its own line`` () =
    // the body travels verbatim, a trailing comment line included; appended
    // to `// the tally`, the `)` would be part of the comment
    let source =
        "module M =\n    let gate = obj ()\n    let mutable count = 0\n    let bump () =\n        System.Threading.Monitor.Enter gate\n        try\n            count <- count + 1\n            count\n            // the tally\n        finally\n            System.Threading.Monitor.Exit gate"

    match monitorLocksIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.EndsWith("count\n            // the tally\n        )", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the lock rewrite"
    | other -> failwithf "Expected one monitor suggestion, got %A" other

[<Fact>]
let ``FR0072: two short hidden cases share the wildcard's line`` () =
    assertExpanded
        "type T =\n    | A\n    | B\n    | C\n    | D\n\nlet f (t: T) =\n    match t with\n    | A -> 1\n    | B -> 2\n    | _ -> 4"
        "C | D"

[<Fact>]
let ``FR0072: hidden cases past 100 columns take a line each under the bar`` () =
    // one joined line ran well past 100 columns on a qualified union; each
    // case now sits under the clause's `|`, the last one carrying the `->`
    assertExpanded
        "[<RequireQualifiedAccess>]\ntype WorkspaceProjectStateNotification =\n    | Loading of string\n    | Loaded of string\n    | Failed of string\n    | Cancelled of string\n\nlet describe (state: WorkspaceProjectStateNotification) =\n    match state with\n    | WorkspaceProjectStateNotification.Failed reason -> reason\n    | WorkspaceProjectStateNotification.Cancelled reason -> reason\n    | _ -> \"the project is still on its way through the loader\""
        "WorkspaceProjectStateNotification.Loading _\n    | WorkspaceProjectStateNotification.Loaded _"

[<Fact>]
let ``FR0071: a binding hoisted out of a loop under #if keeps the #if`` () =
    // the binding is conditional, the loop it lifts above is not: the
    // lifted binding takes the condition with it, and the directive opens
    // its own line
    let source =
        "let sink (n: int) = ()\nlet run (a: int) =\n    for x = 0 to 100 do\n#if !FOO\n        let c = a + 3\n        sink (x + c)\n#endif"

    match invariantsIn source with
    | [ s ] ->
        let inserted =
            s.Edits
            |> List.pick (fun (_, original, text) -> if original = "" then Some text else None)

        Assert.StartsWith("#if !FOO\n", inserted)
        Assert.Contains("let c = a + 3", inserted)
        Assert.EndsWith("#endif\n", inserted)
    | other -> failwithf "Expected exactly one invariant note, got %A" other

// ---- FR0151 ExceptionDetail / FR0152 CachedFailure ----

let private exceptionDetailIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ExceptionDetail.find tree sourceText checkResults

let private cachedFailureIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CachedFailure.find tree sourceText checkResults

[<Fact>]
let ``FR0151: a ReflectionTypeLoadException handler reading only Message gets the loader exceptions`` () =
    let source =
        "module M\nopen System.Reflection\nlet run (a: Assembly) =\n    try\n        a.GetTypes() |> Array.length\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%s\" e.Message\n        0"

    match exceptionDetailIn source with
    | [ s ] ->
        Assert.Equal("ReflectionTypeLoadException", s.ExceptionType)
        Assert.Equal("Types", s.Carrier)

        match s.Fix with
        | Some(r, _, replacement) ->
            Assert.Contains("LoaderExceptions", replacement)
            // the null filter is the point: on .NET Framework these can be null
            Assert.Contains("isNull", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected a fix for ReflectionTypeLoadException"
    | other -> failwithf "Expected one exception-detail suggestion, got %A" other

[<Fact>]
let ``FR0151: a handler already reading LoaderExceptions is left alone`` () =
    let source =
        "module M\nopen System.Reflection\nlet run (a: Assembly) =\n    try\n        a.GetTypes() |> Array.length\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%d\" e.LoaderExceptions.Length\n        0"

    Assert.Empty(exceptionDetailIn source)

[<Fact>]
let ``FR0151: WebException is reported without a fix`` () =
    // the body needs two `use` bindings and Response can be null, so the
    // note stands alone
    let source =
        "module M\nopen System.Net\nlet run (r: WebRequest) =\n    try\n        r.GetResponse() |> ignore\n        0\n    with :? WebException as wex ->\n        printfn \"%s\" wex.Message\n        1"

    match exceptionDetailIn source with
    | [ s ] ->
        Assert.Equal("WebException", s.ExceptionType)
        Assert.Equal("Response", s.Carrier)
        Assert.True(s.Fix.IsNone, "WebException must not carry a fix")
    | other -> failwithf "Expected one WebException suggestion, got %A" other

[<Fact>]
let ``FR0151: an ordinary exception handler is not this rule's business`` () =
    // FR0120 owns the plain handler, and ex.Message there is a PII choice
    let source =
        "module M\nlet run (work: unit -> int) =\n    try\n        work ()\n    with e ->\n        printfn \"%s\" e.Message\n        0"

    Assert.Empty(exceptionDetailIn source)

[<Fact>]
let ``FR0152: GetOrAdd caching a Task is reported`` () =
    let source =
        "module M\nopen System.Threading.Tasks\nopen System.Collections.Concurrent\nlet cache = ConcurrentDictionary<string, Task<int>>()\nlet get (k: string) = cache.GetOrAdd(k, (fun _ -> Task.FromResult 1))"

    match cachedFailureIn source with
    | [ s ] -> Assert.Equal("Task", s.ValueKind)
    | other -> failwithf "Expected one cached-failure suggestion, got %A" other

[<Fact>]
let ``FR0152: a plain value cache is fine`` () =
    // a factory that THROWS caches nothing, so an untyped cache never fires
    let source =
        "module M\nopen System.Collections.Concurrent\nlet cache = ConcurrentDictionary<string, int>()\nlet get (k: string) = cache.GetOrAdd(k, (fun _ -> 1))"

    Assert.Empty(cachedFailureIn source)

[<Fact>]
let ``FR0151: a handler already reading Types is left alone`` () =
    // reading Types IS the informed handler - it carries on with what loaded
    let source =
        "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n        e.Types |> Array.filter (isNull >> not)"

    Assert.Empty(exceptionDetailIn source)

[<Fact>]
let ``FR0151: a rethrowing GetTypes handler is offered the types that loaded`` () =
    let source =
        "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%s\" e.Message\n        reraise ()"

    match exceptionDetailIn source with
    | [ s ] ->
        match s.AlternativeFix with
        | Some(r, original, replacement) ->
            Assert.Contains("reraise", original)
            Assert.Contains("e.Types", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the carry-on alternative fix"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a handler guarding on Response is already informed`` () =
    // the idiomatic shape across the corpus: ClearBank.Common.fs, CarmelNet,
    // welendus and management-portal all write the guard this way
    let source =
        "module M\nopen System.Net\nlet run (r: WebRequest) =\n    try\n        r.GetResponse() |> ignore\n        0\n    with :? WebException as wex when not (isNull wex.Response) ->\n        printfn \"%s\" wex.Message\n        1"

    Assert.Empty(exceptionDetailIn source)

[<Fact>]
let ``FR0151: a mid-line rethrow gets the fix without a trailing comment`` () =
    // the comment would swallow the `else` branch and the closing paren
    let source =
        "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) (fallback: bool) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%s\" e.Message\n        (if fallback then Array.empty else reraise ())"

    match exceptionDetailIn source with
    | [ s ] ->
        match s.AlternativeFix with
        | Some(r, _, replacement) ->
            Assert.DoesNotContain("//", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the carry-on alternative fix"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: an end-of-line rethrow keeps the TODO comment`` () =
    let source =
        "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%s\" e.Message\n        reraise ()"

    match exceptionDetailIn source with
    | [ s ] ->
        match s.AlternativeFix with
        | Some(r, _, replacement) ->
            Assert.Contains("// TODO", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the carry-on alternative fix"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a longer chain off Message must not be swallowed by the fix`` () =
    // `e.Message.Length` is ONE LongIdent [e; Message; Length] whose range
    // covers the whole chain - replacing all of it with the join drops
    // `.Length` and the result no longer typechecks
    let source =
        "module M\nopen System.Reflection\nlet run (a: Assembly) =\n    try\n        a.GetTypes() |> Array.length\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%d\" e.Message.Length\n        0"

    match exceptionDetailIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> () // declining to fix a chain is the correct answer too
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: the carry-on fix never targets a nested handler's rethrow`` () =
    // the inner reraise belongs to the INNER exception. Rewriting it to the
    // outer e.Types still TYPECHECKS - e is in scope and both are Type[] -
    // so only the range tells us it is wrong
    let source =
        "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) (b: Assembly) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n        printfn \"%s\" e.Message\n        try\n            b.GetTypes()\n        with :? ReflectionTypeLoadException as inner ->\n            reraise ()"

    let nestedStart = source.IndexOf "        try\n"

    for s in exceptionDetailIn source do
        match s.AlternativeFix with
        | Some(r, original, _) ->
            Assert.Equal("reraise ()", original.Trim())
            // the only acceptable rethrow is the outer one, and in this source
            // there is no outer rethrow at all
            Assert.True(false, $"fix targeted a nested rethrow at line %d{r.StartLine}")
        | None -> ()

    ignore nestedStart

[<Fact>]
let ``FR0065: a protocol the framework marks obsolete is flagged beyond the curated list`` () =
    // the framework marks its own inconsistently - SslProtocols.Tls11 carries
    // [<Obsolete>], SecurityProtocolType.Tls11 does not, a decade on - so the
    // curated list catches today and the attribute catches whatever a later
    // .NET retires. Neither signal alone is enough
    let tree, sourceText =
        parse
            "module Test\nlet f (p: System.Security.Authentication.SslProtocols) = p = System.Security.Authentication.SslProtocols.Tls13"

    // nothing curated here, and nothing marked: silence
    let quiet, _, _ = SecurityRules.find tree sourceText (fun _ -> false)
    Assert.Empty quiet

    // the same call site once the framework HAS marked it
    let flagged, _, _ = SecurityRules.find tree sourceText (fun _ -> true)

    match flagged with
    | [ s ] -> Assert.Equal(SecurityRules.WeakKind.Protocol "Tls13", s.Kind)
    | other -> failwithf "Expected one protocol note, got %A" other
