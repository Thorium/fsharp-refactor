/// Semantic audit A: rewrites that COMPILED and silently changed behaviour.
/// FR0071 hoisting a call spelled as an operator or a mutable a callee
/// writes, FR0050 turning a wrapping integer loop into a checked `sum`,
/// FR0107 running a user predicate fewer times under `exists`, FR0004
/// dropping the eager copy in front of a lambda that mutates the source,
/// FR0003 evaluating a stage's argument once instead of per element, and
/// FR0044 rethrowing a wrapper where the payload was raised. Each rule now
/// stands down on the shape; the intended shapes still rewrite.
module FSharp.Refactor.Tests.AuditSemanticATests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private lines (xs: string list) = String.concat "\n" xs

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

/// A negative test on a typed rule proves nothing when the input has a
/// type error: every typed rule returns [] on errors. So the input is
/// checked first.
let private assertTypechecks (source: string) =
    Assert.True(typechecksCleanly source, $"Test input does not typecheck:\n%s{source}")

// ---- FR0071 LoopInvariant ----

let private invariantsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    LoopInvariant.find tree sourceText checkResults

[<Fact>]
let ``FR0071: a pipe into a function is a call and stays in the loop`` () =
    // `reader |> readLine` hoisted above `while reader.Peek() >= 0` read
    // one line, and the loop spun on it
    let source =
        lines
            [
                "module T"
                "open System.IO"
                "let readLine (r: TextReader) = r.ReadLine()"
                "let handle (l: string) = printfn \"%s\" l"
                "let run (reader: TextReader) ="
                "    while reader.Peek() >= 0 do"
                "        let line = reader |> readLine"
                "        handle line"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a backward pipe and a composition stay in the loop too`` () =
    let source =
        lines
            [
                "module T"
                "let next (n: int) = n + 1"
                "let sink (n: int) = ()"
                "let run (a: int) (xs: int list) ="
                "    for x in xs do"
                "        let c = next <| a"
                "        let d = next >> next"
                "        sink (x + c + d a)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a mutable a called function writes is not invariant`` () =
    // `offset <- offset + 1` sits in `advance`, not in the loop's text
    let source =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let advance () = offset <- offset + 1"
                "let sink (n: int) = ()"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        advance ()"
                "        sink (x + c)"
            ]

    assertTypechecks source
    Assert.Empty(invariantsIn source)

[<Fact>]
let ``FR0071: a mutable read beside a same-file call that does not write it still hoists`` () =
    // `sink` is declared in this file and its body assigns nothing, so
    // nothing the loop calls can change `offset` between iterations (a
    // callee declared elsewhere would stand the rule down: AuditGuardsATests)
    let source =
        lines
            [
                "module T"
                "let mutable offset = 0"
                "let sink (n: int) = ()"
                "let run (xs: int list) ="
                "    for x in xs do"
                "        let c = offset + 3"
                "        sink (x + c)"
            ]

    match invariantsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("    let c = offset + 3\n    for x in xs do", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one invariant note, got %A" other

[<Fact>]
let ``FR0071: an arithmetic invariant over an immutable still hoists`` () =
    let source =
        lines
            [
                "module T"
                "let sink (n: int) = ()"
                "let run (a: int) (xs: int list) ="
                "    for x in xs do"
                "        let c = a * 2 + 3"
                "        sink (x + c)"
            ]

    match invariantsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("    let c = a * 2 + 3\n    for x in xs do", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one invariant note, got %A" other

// ---- FR0050 Accumulation: checked sum ----

let private accumulationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.find tree sourceText checkResults

[<Fact>]
let ``FR0050: an integer accumulator never becomes sum or sumBy`` () =
    // the loop wraps on overflow, List.sumBy adds checked and throws
    let source =
        lines
            [
                "module T"
                "let f (items: string list) ="
                "    let mutable h = 0"
                "    for x in items do"
                "        h <- h + x.GetHashCode()"
                "    h"
            ]

    let folds, _ = accumulationIn source

    for s in folds do
        Assert.DoesNotContain("sum", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0050: a float accumulator still becomes sumBy`` () =
    let source =
        lines
            [
                "module T"
                "let f (items: float list) ="
                "    let mutable total = 0.0"
                "    for x in items do"
                "        total <- total + x * 2.0"
                "    total"
            ]

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal("items |> List.sumBy (fun x -> x * 2.0)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

// ---- FR0107 flag loops: user predicates ----

let private flagLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.findFlagLoops tree sourceText checkResults

[<Fact>]
let ``FR0107: a user function in the predicate keeps the loop`` () =
    // exists stops at the first hit; `validate` printed for every file
    let source =
        lines
            [
                "module T"
                "let validate (f: string) ="
                "    printfn \"%s\" f"
                "    f.Length > 3"
                "let check (files: string list) ="
                "    let mutable bad = false"
                "    for file in files do"
                "        if validate file then bad <- true"
                "    bad"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: a user function handed to a core function keeps the loop`` () =
    let source =
        lines
            [
                "module T"
                "let validate (f: string) ="
                "    printfn \"%s\" f"
                "    f.Length > 3"
                "let check (files: string list list) ="
                "    let mutable bad = false"
                "    for group in files do"
                "        if List.exists validate group then bad <- true"
                "    bad"
            ]

    assertTypechecks source
    Assert.Empty(flagLoopsIn source)

[<Fact>]
let ``FR0107: a property read and a core operator still become exists`` () =
    let source =
        lines
            [
                "module T"
                "let check (files: string list) ="
                "    let mutable bad = false"
                "    for file in files do"
                "        if file.Length > 3 then bad <- true"
                "    bad"
            ]

    match flagLoopsIn source with
    | [ s ] ->
        Assert.Equal("let bad = files |> List.exists (fun file -> file.Length > 3)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one flag-loop suggestion, got %A" other

[<Fact>]
let ``FR0107: a String method in the predicate still becomes exists`` () =
    let source =
        lines
            [
                "module T"
                "let check (files: string list) ="
                "    let mutable bad = false"
                "    for file in files do"
                "        if file.EndsWith \".tmp\" then bad <- true"
                "    bad"
            ]

    match flagLoopsIn source with
    | [ s ] -> Assert.Equal("let bad = files |> List.exists (fun file -> file.EndsWith \".tmp\")", s.ReplacementText)
    | other -> failwithf "Expected exactly one flag-loop suggestion, got %A" other

// ---- FR0004 ConversionMove: a lambda that mutates the source ----

let private conversionsIn (source: string) =
    let tree, sourceText = parse source
    ConversionMove.find tree sourceText

[<Fact>]
let ``FR0004: a lambda removing from the source keeps the eager copy`` () =
    // `Seq.iter` over the ResizeArray it removes from throws
    // InvalidOperationException on the second element
    assertTypechecks
        "module T\nlet f (rs: ResizeArray<int>) =\n    rs |> Seq.toList |> List.iter (fun x -> rs.Remove x |> ignore)"

    Assert.Empty(
        conversionsIn
            "module T\nlet f (rs: ResizeArray<int>) =\n    rs |> Seq.toList |> List.iter (fun x -> rs.Remove x |> ignore)"
    )

[<Fact>]
let ``FR0004: a lambda adding to any collection keeps the eager copy`` () =
    // `sink` may alias the source; nothing here can tell
    Assert.Empty(
        conversionsIn
            "module T\nlet f (xs: seq<int>) (sink: ResizeArray<int>) =\n    xs |> Seq.toList |> List.iter (fun x -> sink.Add x)"
    )

[<Fact>]
let ``FR0004: a lambda that only reads still drops the conversion`` () =
    match conversionsIn "module T\nlet f (xs: seq<int>) = xs |> Seq.toList |> List.iter (printfn \"%d\")" with
    | [ s ] -> Assert.Equal("Seq.iter (printfn \"%d\")", s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- FR0003 Composition: stage arguments evaluated once ----

let private compositionsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Composition.find tree sourceText checkResults

[<Fact>]
let ``FR0003: a stage applying a function in its argument keeps the lambda`` () =
    // `compute ()` ran per element; `addN (compute ()) >> string` runs it once
    let source =
        lines
            [
                "module T"
                "let compute () = 3"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN (compute ()) |> string)"
            ]

    assertTypechecks source
    Assert.Empty(compositionsIn source)

[<Fact>]
let ``FR0003: a property read in a stage argument keeps the lambda`` () =
    let source =
        lines
            [
                "module T"
                "let addT (t: System.DateTime) (x: int) = x + t.Second"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addT System.DateTime.Now |> string)"
            ]

    assertTypechecks source
    Assert.Empty(compositionsIn source)

[<Fact>]
let ``FR0003: a mutable in a stage argument keeps the lambda`` () =
    let source =
        lines
            [
                "module T"
                "let mutable n = 3"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN n |> string)"
            ]

    assertTypechecks source
    Assert.Empty(compositionsIn source)

[<Fact>]
let ``FR0003: a literal stage argument still composes`` () =
    let source =
        lines
            [
                "module T"
                "let addN (n: int) (x: int) = x + n"
                "let f (xs: int list) = xs |> List.map (fun x -> x |> addN 3 |> string)"
            ]

    match compositionsIn source with
    | [ s ] ->
        Assert.Equal("addN 3 >> string", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

// ---- FR0044 Reraise: a payload is not the caught exception ----

let private reraiseIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Reraise.find tree sourceText checkResults

let private assertReraise (source: string) =
    match reraiseIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range "reraise ()"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one reraise suggestion, got %A" other

[<Fact>]
let ``FR0044: raising a field of the caught exception is not a rethrow`` () =
    // `reraise ()` rethrows ParseFailed; `raise inner` threw its payload
    let source =
        lines
            [
                "module T"
                "exception ParseFailed of string * exn"
                "let f (act: unit -> int) ="
                "    try act ()"
                "    with ParseFailed(_, inner) -> raise inner"
            ]

    assertTypechecks source
    Assert.Empty(reraiseIn source)

[<Fact>]
let ``FR0044: a bare binder still becomes reraise`` () =
    assertReraise "module T\nlet f (act: unit -> int) =\n    try act ()\n    with ex -> raise ex"

[<Fact>]
let ``FR0044: a type-test binder still becomes reraise`` () =
    assertReraise
        "module T\nlet f (act: unit -> int) =\n    try act ()\n    with\n    | :? System.IO.IOException as e -> raise e"

[<Fact>]
let ``FR0044: the whole exception bound beside a case pattern still becomes reraise`` () =
    assertReraise (
        lines
            [
                "module T"
                "exception ParseFailed of string * exn"
                "let f (act: unit -> int) ="
                "    try act ()"
                "    with ParseFailed(_, _) as whole -> raise whole"
            ]
    )
