/// Compile-breaking fixes found by the 0.8.21 audit, one test per defect:
/// FR0049 returning INSIDE a parenthesised tail, FR0013 baring an argument
/// whose application is itself the function of an indexer or a further
/// application, FR0095 taking a record-, cons- or field-bound `id` for
/// FSharp.Core's, FR0147 opening a namespace over a union case the file
/// matches on, and FR0155 sealing a class a flexible type `#Node` widens.
/// In the "ProjectSources" collection: the two-file harnesses install the
/// process-wide cross-file parser.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AuditCompileBreakTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

let private lines (xs: string list) = String.concat "\n" xs

// ---- FR0049 Taskify ----

let private taskifyIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Taskify.find tree sourceText checkResults None

[<Fact>]
let ``FR0049: a parenthesised tail is returned whole, not from inside the parentheses`` () =
    // `(r, 1)` became `(return r, 1)` — FS0792 — because the walk went
    // through the parentheses to the tuple; `return` belongs before them
    let source =
        lines
            [
                "module Test"
                "open System.Threading.Tasks"
                "let private fetch (x: int) ="
                "    let t = Task.Run(fun () -> x)"
                "    let r = t.GetAwaiter().GetResult()"
                "    (r, 1)"
                "let consume () = task {"
                "    let s = fetch 1"
                "    return fst s"
                "}"
            ]

    match taskifyIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("return (r, 1)", patched)
        Assert.DoesNotContain("(return", patched)
        Assert.Contains("let! r = t", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one taskify suggestion, got %A" other

[<Fact>]
let ``FR0049: a parenthesised blocking drain in tail position is still return-banged`` () =
    let source =
        lines
            [
                "module Test"
                "open System.Threading.Tasks"
                "let private fetch (x: int) ="
                "    let t = Task.Run(fun () -> x)"
                "    (t.GetAwaiter().GetResult())"
                "let consume () = task {"
                "    let s = fetch 1"
                "    return s"
                "}"
            ]

    match taskifyIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("return! t", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one taskify suggestion, got %A" other

// ---- FR0013 RedundantParens ----

let private parensIn (source: string) =
    let tree, sourceText = parse source
    RedundantParens.find tree sourceText

[<Fact>]
let ``FR0013: an application indexed with the F# 6 syntax keeps its parentheses`` () =
    // `List.sort(xs)[0]` bare is `List.sort xs[0]`: the indexer binds to
    // `xs` first — FS0193
    Assert.Empty(parensIn "module Test\nlet xs = [ 3; 1 ]\nlet first = List.sort(xs)[0]")

[<Fact>]
let ``FR0013: an application applied to a further argument keeps its parentheses`` () =
    // `add(s)(2)` bare is `add s(2)`: `s(2)` is the application
    Assert.Empty(parensIn "module Test\nlet add (a: int) (b: int) = a + b\nlet s = 1\nlet r = add(s)(2)")

[<Fact>]
let ``FR0013: a plain parenthesised atom still loses its parentheses`` () =
    match parensIn "module Test\nlet m = List.max([ 4; 3 ])" with
    | [ s ] -> Assert.Equal(" [ 4; 3 ]", s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0095 LambdaBuiltin ----

let private lambdaIn (source: string) =
    let tree, sourceText = parse source
    LambdaBuiltin.find tree sourceText

[<Fact>]
let ``FR0095: an id bound by a record pattern shadows the builtin`` () =
    // `{ Id = id }` binds `id` for the arm; `List.map id` there would call
    // the field, not FSharp.Core's identity
    Assert.Empty(
        lambdaIn (
            lines
                [
                    "module Test"
                    "type R = { Id: int -> int }"
                    "let f (r: R) (xs: int list) ="
                    "    match r with"
                    "    | { Id = id } -> xs |> List.map (fun x -> x)"
                ]
        )
    )

[<Fact>]
let ``FR0095: an id bound by a cons pattern shadows the builtin`` () =
    Assert.Empty(
        lambdaIn (
            lines
                [
                    "module Test"
                    "let g (pairs: ((int -> int) * int) list) (xs: int list) ="
                    "    match pairs with"
                    "    | (id, _) :: _ -> xs |> List.map (fun x -> x)"
                    "    | [] -> xs"
                ]
        )
    )

[<Fact>]
let ``FR0095: an id bound by a named union field shadows the builtin`` () =
    Assert.Empty(
        lambdaIn (
            lines
                [
                    "module Test"
                    "type U = Case of Id: (int -> int) * Tag: int"
                    "let h (u: U) (xs: int list) ="
                    "    match u with"
                    "    | Case(Id = id) -> xs |> List.map (fun x -> x)"
                ]
        )
    )

[<Fact>]
let ``FR0095: with nothing shadowing it the lambda still becomes id`` () =
    match lambdaIn "module Test\nlet m (xs: int list) = xs |> List.map (fun x -> x)" with
    | [ s ] -> Assert.Equal("id", s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- FR0147 QualifiedNames ----

/// FR0147's suggestions for B, compiled after A.
let private qualifiedIn (sourceA: string) (sourceB: string) =
    let tree, sourceText, checkResults = parseAndCheckSecond sourceA sourceB
    QualifiedNames.find 3 2 tree sourceText checkResults

[<Fact>]
let ``FR0147: an open that would rebind a union case the file matches on is withheld`` () =
    // `| Active ->` is Other.Status.Active today; `open Lib` below `open
    // Other` would make it Lib.Flag.Active and the match stop compiling.
    // Only expression heads were checked for the clash, never a pattern's
    let lib =
        lines
            [
                "namespace Lib"
                "type Flag ="
                "    | Active"
                "    | Inactive"
                "module Util ="
                "    let f (x: int) = x"
                "namespace Other"
                "type Status ="
                "    | Active"
                "    | Deleted"
                ""
            ]

    let source =
        lines
            [
                "module Test"
                "open Other"
                "let a = Lib.Util.f 1"
                "let b = Lib.Util.f 2"
                "let c = Lib.Util.f 3"
                "let describe (s: Status) ="
                "    match s with"
                "    | Active -> 1"
                "    | Deleted -> 0"
                ""
            ]

    match qualifiedIn lib source |> List.filter (fun s -> s.Namespace = "Lib") with
    | [] -> ()
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("Active", defaultArg s.Reason "")
    | other -> failwithf "Expected the open withheld, got %A" other

[<Fact>]
let ``FR0147: a union case the file matches on from the namespace itself is no clash`` () =
    // the file's `Active` already IS Lib's: the open changes nothing
    let lib =
        lines
            [
                "namespace Lib"
                "type Flag ="
                "    | Active"
                "    | Inactive"
                "module Util ="
                "    let f (x: int) = x"
                ""
            ]

    let source =
        lines
            [
                "module Test"
                "let a = Lib.Util.f 1"
                "let b = Lib.Util.f 2"
                "let c = Lib.Util.f 3"
                "let describe (s: Lib.Flag) ="
                "    match s with"
                "    | Lib.Active -> 1"
                "    | Lib.Inactive -> 0"
                ""
            ]

    match qualifiedIn lib source |> List.filter (fun s -> s.Namespace = "Lib") with
    | [ s ] ->
        Assert.NotEmpty s.Edits
        let patched = applyAll source s.Edits
        Assert.Contains("open Lib", patched)
    | other -> failwithf "Expected one suggestion with edits, got %A" other

// ---- FR0155 SealedClass ----

[<Fact>]
let ``FR0155: a class used as a flexible type is not sealed`` () =
    // `#A.Node` asks for Node or any subtype; on a sealed class FS0064
    // says the annotation is less generic than written — an error under
    // TreatWarningsAsErrors. The same array trigger without the flexible
    // use would seal it
    let node = "module A\n\ntype internal Node(v: int) =\n    member _.Value = v\n"

    let flexible =
        "module B\n\nlet internal slots: A.Node[] = Array.zeroCreate 4\n\nlet internal describe (x: #A.Node) = x.Value\n"

    let tree, source, check, project, _, _, _ = parseAndCheckPair node flexible
    Assert.Empty(SealedClass.find false tree source check (Some project))

    let plain = "module B\n\nlet internal slots: A.Node[] = Array.zeroCreate 4\n"
    let tree2, source2, check2, project2, _, _, _ = parseAndCheckPair node plain

    match SealedClass.find false tree2 source2 check2 (Some project2) with
    | [ s ] -> Assert.Equal("Node", s.TypeName)
    | other -> failwithf "Expected the seal without the flexible use, got %A" other
