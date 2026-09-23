/// Audit guards A: the 0.8.23 audit closed real defects, and several of
/// its fixes did so by standing a rule down on a far wider class than the
/// defect. Each rule now carries the PRECISE guard the typed tree can
/// prove and keeps every legitimate rewrite it used to deliver: FR0107
/// follows a same-file predicate into its body (and no mutable, partial or
/// extension callee), FR0071 asks what the statement calls of a local
/// mutable too (a closure captures one) over the whole anchor, and tells
/// a total division from a hazardous one, FR0157 deletes a dead `| null
/// ->` arm and keeps one beside a literal, FR0003 reads every identifier
/// of a path, FR0004 knows the whole mutation vocabulary, FR0002 sees a
/// member's self-call, qualified too, and FR0101 keeps a Fable string
/// loop indexed.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AuditGuardsATests

open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private lines (xs: string list) = String.concat "\n" xs

let private applyAll (source: string) (edits: (range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

/// A negative test on a typed rule proves nothing when the input has a
/// type error: every typed rule returns [] on errors. So the input is
/// checked first.
let private assertTypechecks (source: string) =
    Assert.True(typechecksCleanly source, $"Test input does not typecheck:\n%s{source}")

let private assertPatchedTypechecks (patched: string) =
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- 1: FR0107 flag loop: a same-file predicate ----

let private flagLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.findFlagLoops tree sourceText checkResults

let private assertFlagRewrite (source: string) (expected: string) =
    match flagLoopsIn source with
    | [ s ] ->
        Assert.Equal(expected, s.ReplacementText)
        assertPatchedTypechecks (applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one flag-loop suggestion, got %A" other

[<Fact>]
let ``FR0107: a same-file function whose body only computes still becomes exists`` () =
    assertFlagRewrite
        (lines
            [
                "module T"
                "let isValid (x: string) = x.Length > 3"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if isValid file then found <- true"
                "    found"
            ])
        "let found = files |> List.exists (fun file -> isValid file)"

[<Fact>]
let ``FR0107: a same-file predicate is followed through the functions it calls`` () =
    // isLong calls isValid: two declarations deep, both compute only
    assertFlagRewrite
        (lines
            [
                "module T"
                "let isValid (x: string) = x.Length > 3"
                "let isLong (x: string) = isValid x && x.EndsWith \".fs\""
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if isLong file then found <- true"
                "    found"
            ])
        "let found = files |> List.exists (fun file -> isLong file)"

[<Fact>]
let ``FR0107: a local function of the enclosing body counts as declared in the file`` () =
    assertFlagRewrite
        (lines
            [
                "module T"
                "let check (files: string list) ="
                "    let isValid (x: string) = x.Length > 3"
                "    let mutable found = false"
                "    for file in files do"
                "        if isValid file then found <- true"
                "    found"
            ])
        "let found = files |> List.exists (fun file -> isValid file)"

[<Fact>]
let ``FR0107: a method on another type in the predicate keeps the loop`` () =
    let source =
        lines
            [
                "module T"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if System.IO.File.Exists file then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: an effectful FSharp.Core call in the predicate keeps the loop`` () =
    // `lock` runs its lambda under a monitor; exists would take it fewer times
    let source =
        lines
            [
                "module T"
                "let gate = obj ()"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if lock gate (fun () -> file.Length > 3) then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: a record field holding a function is a call and keeps the loop`` () =
    let source =
        lines
            [
                "module T"
                "type Rules = { Validate: string -> bool }"
                "let check (rules: Rules) (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if rules.Validate file then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: a same-file chain deeper than three declarations keeps the loop`` () =
    let source =
        lines
            [
                "module T"
                "let d (x: string) = x.Length > 3"
                "let c (x: string) = d x"
                "let b (x: string) = c x"
                "let a (x: string) = b x"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if a file then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: a mutable holding a function is an unknown callee and keeps the loop`` () =
    // `validator` may be reassigned before the loop runs; its initial
    // lambda says nothing about what a call runs
    let source =
        lines
            [
                "module T"
                "let mutable validator = fun (x: string) -> x.Length > 3"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if validator file then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: an annotated same-file predicate is still followed into its body`` () =
    assertFlagRewrite
        (lines
            [
                "module T"
                "let isValid: string -> bool = fun x -> x.Length > 3"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if isValid file then found <- true"
                "    found"
            ])
        "let found = files |> List.exists (fun file -> isValid file)"

[<Fact>]
let ``FR0107: a partial FSharp.Core function in the predicate keeps the loop`` () =
    // `List.head` throws on an empty list: the loop threw on its first
    // element, `exists` may stop before it ever gets there
    let source =
        lines
            [
                "module T"
                "let check (files: string list) (firsts: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if List.head firsts = file then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

    // Operators.max over two values is total, and still passes
    assertFlagRewrite
        (lines
            [
                "module T"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if max file.Length 3 > 3 then found <- true"
                "    found"
            ])
        "let found = files |> List.exists (fun file -> max file.Length 3 > 3)"

[<Fact>]
let ``FR0107: an extension member on a BCL type in the predicate keeps the loop`` () =
    // System.String is the apparent owner; the body is the user's
    let source =
        lines
            [
                "module T"
                "type System.String with"
                "    member s.Shout() ="
                "        printfn \"%s\" s"
                "        s.Length > 3"
                "let check (files: string list) ="
                "    let mutable found = false"
                "    for file in files do"
                "        if file.Shout() then found <- true"
                "    found"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

// ---- 2: FR0071 LoopInvariant: what the statement calls, division ----

let private invariantsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    LoopInvariant.find tree sourceText checkResults

let private assertHoisted (source: string) (expectedFragment: string) =
    match invariantsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains(expectedFragment, patched)
        assertPatchedTypechecks patched
    | other -> failwithf "Expected exactly one invariant note, got %A" other

[<Fact>]
let ``FR0071: a local mutable read beside a printfn still hoists`` () =
    // the loop calls FSharp.Core alone, which cannot write `total`, and the
    // loop's own text does not assign it
    assertHoisted
        (lines
            [
                "module T"
                "let run (xs: int list) ="
                "    let mutable total = 0"
                "    total <- 5"
                "    for x in xs do"
                "        let c = total + 3"
                "        printfn \"%d\" (x + c)"
                "    total"
            ])
        "    let c = total + 3\n    for x in xs do"

[<Fact>]
let ``FR0071: a local mutable assigned in the loop stays in it`` () =
    let source =
        lines
            [
                "module T"
                "let run (xs: int list) ="
                "    let mutable total = 0"
                "    for x in xs do"
                "        let c = total + 3"
                "        total <- total + x + c"
                "    total"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a local mutable a same-scope closure writes stays in the loop`` () =
    // since F# 4.0 `bump` captures `total` as a ref cell: hoisted, `c`
    // would stay 3 while the loop's `total` climbs
    let source =
        lines
            [
                "module T"
                "let run (xs: int list) ="
                "    let mutable total = 0"
                "    let bump () = total <- total + 1"
                "    for x in xs do"
                "        let c = total + 3"
                "        bump ()"
                "        printfn \"%d %d\" x c"
                "    total"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a pipeline head that writes the mutable keeps the binding in the lambda`` () =
    // the hoisted binding lands above the whole pipeline, so `produce ()`
    // runs between it and the lambda; the lambda's body alone was scanned
    let source =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let produce () ="
                "    offset <- offset + 1"
                "    [ 1; 2 ]"
                "let run () ="
                "    produce ()"
                "    |> List.map (fun x ->"
                "        let c = offset + 3"
                "        x + c)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

    // a head that is a plain value leaves nothing to run, and the lambda
    // still hoists
    assertHoisted
        (lines
            [
                "module T"
                "let mutable offset = 0"
                "let run (xs: int list) ="
                "    xs"
                "    |> List.map (fun x ->"
                "        let c = offset + 3"
                "        x + c)"
            ])
        "    let c = offset + 3\n    xs\n    |> List.map (fun x ->"

[<Fact>]
let ``FR0071: a function-typed field, a user getter and an active pattern are callees the rule cannot follow`` () =
    let viaField =
        lines
            [
                "module T"
                "type Ops = { Bump: unit -> unit }"
                "let mutable offset = 0"
                "let run (ops: Ops) (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        ops.Bump ()"
                "        ignore (x + c)"
            ]

    assertTypechecks viaField
    Assert.Empty(invariantsIn viaField)

    let viaGetter =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "type Counter() ="
                "    member _.Next ="
                "        offset <- offset + 1"
                "        offset"
                "let run (counter: Counter) (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        ignore (counter.Next + x + c)"
            ]

    assertTypechecks viaGetter
    Assert.Empty(invariantsIn viaGetter)

    let viaActivePattern =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let (|Bumped|) (n: int) ="
                "    offset <- offset + 1"
                "    n"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        match x with"
                "        | Bumped n -> ignore (n + c)"
            ]

    assertTypechecks viaActivePattern
    Assert.Empty(invariantsIn viaActivePattern)

    // a BCL getter cannot reach a mutable of this file
    assertHoisted
        (lines
            [
                "module T"
                "let mutable offset = 0"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        ignore (xs.Length + x + c)"
            ])
        "    let c = offset + 3\n    for x in xs do"

[<Fact>]
let ``FR0071: a module mutable read beside a call into another assembly stays in the loop`` () =
    // Console.WriteLine is neither this file's nor FSharp.Core's: for all
    // the typed tree can tell it writes `offset`
    let source =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        System.Console.WriteLine(x + c)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a module mutable written two calls deep stays in the loop`` () =
    let source =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let bump () = offset <- offset + 1"
                "let step () = bump ()"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        step ()"
                "        ignore (x + c)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a division and a remainder by a non-zero literal hoist`` () =
    assertHoisted
        (lines
            [
                "module T"
                "let sink (n: int) = ()"
                "let run (a: int) (xs: int list) ="
                "    for x in xs do"
                "        let c = a / 2 + a % 4"
                "        sink (x + c)"
            ])
        "    let c = a / 2 + a % 4\n    for x in xs do"

[<Fact>]
let ``FR0071: a division by a variable stays in the loop`` () =
    // the divisor may be zero on a loop that never ran
    let source =
        lines
            [
                "module T"
                "let sink (n: int) = ()"
                "let run (a: int) (b: int) (xs: int list) ="
                "    for x in xs do"
                "        let c = a / b"
                "        sink (x + c)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

// ---- 3: FR0157 StringUnion: the null arm ----

let private worldOf (check: FSharpCheckFileResults) (source: ISourceText) (tree: FSharp.Compiler.Syntax.ParsedInput) =
    let rec names (entities: FSharpEntity seq) =
        seq {
            for e in entities do
                yield e.DisplayName
                yield! names e.NestedEntities
        }

    {
        StringUnion.UsesOf = check.GetUsesOfSymbolInFile
        StringUnion.File = (fun _ -> Some(tree, source))
        StringUnion.SymbolAt =
            (fun _ id ->
                let r = id.idRange

                check.GetSymbolUseAtLocation(
                    r.EndLine,
                    r.EndColumn,
                    source.GetLineString(r.EndLine - 1),
                    [ id.idText ]
                ))
        StringUnion.FileOrder = (fun _ -> 0)
        StringUnion.ScopeOpen = true
        StringUnion.TypeNames = names check.PartialAssemblySignature.Entities |> Set.ofSeq
        StringUnion.InternalsVisible = false
        StringUnion.SourceFiles = [ "Test.fsx" ]
    }

let private unionsIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    StringUnion.find (worldOf check sourceText tree) tree sourceText

[<Fact>]
let ``FR0157: an unguarded null arm is dead and goes with the wildcard`` () =
    // every source is a literal, so null never arrives
    let source =
        lines
            [
                "module T"
                "let describe (region: string) ="
                "    match region with"
                "    | null -> \"none\""
                "    | \"eu\" -> \"Europe\""
                "    | \"uk\" -> \"Britain\""
                "    | _ -> failwith \"?\""
                "let a = describe \"eu\""
                "let b = describe \"uk\""
            ]

    match unionsIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
            |> List.fold (fun acc e -> applyEdit acc e.Range e.Replacement) source

        Assert.DoesNotContain("null", patched)
        Assert.Contains("| Region.Eu -> \"Europe\"", patched)
        assertPatchedTypechecks patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``FR0157: a guarded null arm stays open and the rule stands down`` () =
    let source =
        lines
            [
                "module T"
                "let debug = true"
                "let describe (region: string) ="
                "    match region with"
                "    | null when debug -> \"none\""
                "    | \"eu\" -> \"Europe\""
                "    | \"uk\" -> \"Britain\""
                "    | _ -> failwith \"?\""
                "let a = describe \"eu\""
                "let b = describe \"uk\""
            ]

    assertTypechecks source
    Assert.Empty(unionsIn source)

[<Fact>]
let ``FR0157: a null beside a literal in one or-pattern stands the rule down`` () =
    // read as a dead catch-all AND a literal arm, the clause was deleted
    // while its literal half was edited too
    let source =
        lines
            [
                "module T"
                "let describe (region: string) ="
                "    match region with"
                "    | null | \"na\" -> \"none\""
                "    | \"eu\" -> \"Europe\""
                "    | \"uk\" -> \"Britain\""
                "    | _ -> failwith \"?\""
                "let a = describe \"eu\""
                "let b = describe \"uk\""
            ]

    assertTypechecks source
    Assert.Empty(unionsIn source)

    let literalFirst =
        lines
            [
                "module T"
                "let describe (region: string) ="
                "    match region with"
                "    | \"na\" | null -> \"none\""
                "    | \"eu\" -> \"Europe\""
                "    | \"uk\" -> \"Britain\""
                "    | _ -> failwith \"?\""
                "let a = describe \"eu\""
                "let b = describe \"uk\""
            ]

    assertTypechecks literalFirst
    Assert.Empty(unionsIn literalFirst)

// ---- 4: FR0003 Composition: every identifier of a path ----

let private compositionsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Composition.find tree sourceText checkResults

[<Fact>]
let ``FR0003: a field read through a mutable record keeps the lambda`` () =
    // `cfg.N` reads differently once `cfg` is reassigned
    let source =
        lines
            [
                "module T"
                "type Config = { N: int }"
                "let mutable cfg = { N = 3 }"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN cfg.N |> string)"
            ]

    assertTypechecks source
    Assert.Empty(compositionsIn source)

[<Fact>]
let ``FR0003: a mutable field read keeps the lambda`` () =
    let source =
        lines
            [
                "module T"
                "type Config = { mutable N: int }"
                "let cfg = { N = 3 }"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN cfg.N |> string)"
            ]

    assertTypechecks source
    Assert.Empty(compositionsIn source)

[<Fact>]
let ``FR0003: an immutable record's field still composes`` () =
    let source =
        lines
            [
                "module T"
                "type Config = { N: int }"
                "let cfg = { N = 3 }"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN cfg.N |> string)"
            ]

    match compositionsIn source with
    | [ s ] ->
        Assert.Equal("addN cfg.N >> string", s.ReplacementText)
        assertPatchedTypechecks (applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``FR0003: a module-qualified stage still composes`` () =
    // `String` on the path is an entity, not a value
    let source =
        lines
            [
                "module T"
                "let f (xs: string list) = xs |> List.map (fun s -> s |> String.length |> string)"
            ]

    match compositionsIn source with
    | [ s ] ->
        Assert.Equal("String.length >> string", s.ReplacementText)
        assertPatchedTypechecks (applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- 5: FR0004 ConversionMove: the mutation vocabulary ----

let private conversionsIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    ConversionMove.findWith (Some check) tree sourceText

[<Fact>]
let ``FR0004: a lambda calling AddRange, Sort or UnionWith keeps the eager copy`` () =
    Assert.Empty(
        conversionsIn
            "module T\nlet f (xs: seq<int>) (sink: ResizeArray<int>) =\n    xs |> Seq.toList |> List.iter (fun x -> sink.AddRange [ x ])"
    )

    Assert.Empty(
        conversionsIn
            "module T\nlet f (xs: seq<int>) (sink: ResizeArray<int>) =\n    xs |> Seq.toList |> List.iter (fun _ -> sink.Sort())"
    )

    Assert.Empty(
        conversionsIn
            "module T\nlet f (xs: seq<int>) (sink: System.Collections.Generic.HashSet<int>) =\n    xs |> Seq.toList |> List.iter (fun x -> sink.UnionWith [ x ])"
    )

[<Fact>]
let ``FR0004: a lambda that only queries a collection still drops the conversion`` () =
    match
        conversionsIn
            "module T\nlet f (xs: ResizeArray<int>) (sink: ResizeArray<int>) =\n    xs |> Seq.toList |> List.iter (fun x -> sink.Contains x |> ignore)"
    with
    | [ s ] -> Assert.Equal("Seq.iter (fun x -> sink.Contains x |> ignore)", s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- 6: FR0002 OptionModule: a member's self-call ----

let private optionsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionModule.find tree sourceText checkResults

[<Fact>]
let ``FR0002: a member arm calling itself through its self identifier keeps the match`` () =
    // `this.Walk` in arm position is the tail call `let rec loop` makes
    let viaThis =
        lines
            [
                "module T"
                "type Walker() ="
                "    member this.Walk (xs: int list) (acc: int) : int ="
                "        match List.tryHead xs with"
                "        | Some v -> this.Walk (List.tail xs) (acc + v)"
                "        | None -> acc"
            ]

    assertTypechecks viaThis
    Assert.Empty(optionsIn viaThis)

    let viaOwnName =
        lines
            [
                "module T"
                "type Walker() ="
                "    member w.Walk (xs: int list) (acc: int) : int ="
                "        match List.tryHead xs with"
                "        | Some v -> w.Walk (List.tail xs) (acc + v)"
                "        | None -> acc"
            ]

    assertTypechecks viaOwnName
    Assert.Empty(optionsIn viaOwnName)

[<Fact>]
let ``FR0002: a static member calling itself through the type's name keeps the match`` () =
    // `Walker.Walk` in arm position is the same tail call as `this.Walk`
    let viaTypeName =
        lines
            [
                "module T"
                "type Walker() ="
                "    static member Walk (xs: int list) (acc: int) : int ="
                "        match List.tryHead xs with"
                "        | Some v -> Walker.Walk (List.tail xs) (acc + v)"
                "        | None -> acc"
            ]

    assertTypechecks viaTypeName
    Assert.Empty(optionsIn viaTypeName)

    // a module's `let rec` called through the module's name (a recursive
    // module, where the qualified spelling resolves)
    let viaModuleName =
        lines
            [
                "module T"
                "module rec M ="
                "    let rec loop (xs: int list) (acc: int) : int ="
                "        match List.tryHead xs with"
                "        | Some v -> M.loop (List.tail xs) (acc + v)"
                "        | None -> acc"
            ]

    assertTypechecks viaModuleName
    Assert.Empty(optionsIn viaModuleName)

[<Fact>]
let ``FR0002: a member whose arm calls another member still folds`` () =
    let source =
        lines
            [
                "module T"
                "type Walker() ="
                "    member _.Weight (v: int) = v * 2"
                "    member this.Step (xs: int list) (acc: int) : int ="
                "        match List.tryHead xs with"
                "        | Some v -> acc + this.Weight v"
                "        | None -> acc"
            ]

    match optionsIn source with
    | [ s ] ->
        Assert.StartsWith("Option.map", s.Target)
        assertPatchedTypechecks (applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- 7: FR0101 IndexedLoop: a string source under Fable ----

[<Fact>]
let ``FR0101: a string source in a Fable project keeps its index`` () =
    // Fable's Rust target has no string enumerator
    let source =
        lines
            [
                "module T"
                "let count (value: string) ="
                "    let mutable n = 0"
                "    for i in 0 .. value.Length - 1 do"
                "        if value.[i] = 'a' then n <- n + 1"
                "    n"
            ]

    let tree, sourceText, check = parseAndCheck source
    Assert.Empty(IndexedLoop.findWith tree sourceText (IndexedLoop.SourceGate.NoStrings(Some check)))
    // without a typed tree nothing proves the source is not a string
    Assert.Empty(IndexedLoop.findWith tree sourceText (IndexedLoop.SourceGate.NoStrings None))

    // on .NET the string enumerates its characters
    match IndexedLoop.findWith tree sourceText IndexedLoop.SourceGate.Any with
    | [ s ] -> Assert.Contains("for item in value", applyAll source s.Edits)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``FR0101: an array source in a Fable project still iterates directly`` () =
    let source =
        lines
            [
                "module T"
                "let count (values: int[]) ="
                "    let mutable n = 0"
                "    for i in 0 .. values.Length - 1 do"
                "        if values.[i] > 3 then n <- n + 1"
                "    n"
            ]

    let tree, sourceText, check = parseAndCheck source

    match IndexedLoop.findWith tree sourceText (IndexedLoop.SourceGate.NoStrings(Some check)) with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("for item in values do", patched)
        assertPatchedTypechecks patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other
