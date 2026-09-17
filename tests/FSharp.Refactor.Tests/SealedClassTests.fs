/// FR0155: `[<Sealed>]` on an internal class nothing inherits, where the
/// project stores it in arrays or type-tests it.
/// In the "ProjectSources" collection: parseAndCheckPair installs the
/// cross-file parser, process-wide state the signature tests read too.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.SealedClassTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open System.IO

/// FR0155 for A, compiled with B after it; `scope` opens the public case.
let private sealedIn (scope: bool) (sourceA: string) (sourceB: string) =
    let tree, source, check, project, _, _, recheck = parseAndCheckPair sourceA sourceB
    SealedClass.find scope tree source check (Some project), recheck

[<Literal>]
let private node =
    "module A\n\ntype internal Node(v: int) =\n    member _.Value = v\n"

[<Literal>]
let private nodeArray =
    "module B\n\nlet internal slots: A.Node[] = Array.zeroCreate 4\n\nlet internal fill () =\n    for i in 0..3 do\n        slots.[i] <- A.Node i\n"

// ---- the two triggers ----

[<Fact>]
let ``an internal class stored in an array of its type gains [<Sealed>] above the type line`` () =
    let found, recheck = sealedIn false node nodeArray

    match found with
    | [ s ] ->
        Assert.Equal("Node", s.TypeName)
        Assert.Equal("a Node[]", s.Reason)

        match s.Fix with
        | Some(r, text) ->
            Assert.Equal("[<Sealed>]\n", text)
            Assert.Equal(3, r.StartLine)
            let patched = applyEdit node r text
            Assert.Contains("[<Sealed>]\ntype internal Node(v: int) =", patched)
            Assert.Empty(recheck patched nodeArray)
        | None -> failwith "expected the attribute fix"
    | other -> failwith $"expected one suggestion, got %A{other}"

[<Fact>]
let ``a type test in another file is the other trigger`` () =
    let tested =
        "module B\n\nlet value (o: obj) =\n    match o with\n    | :? A.Node as n -> n.Value\n    | _ -> 0\n"

    let found, _ = sealedIn false node tested

    match found with
    | [ s ] -> Assert.Equal("a :? Node test", s.Reason)
    | other -> failwith $"expected one suggestion, got %A{other}"

[<Fact>]
let ``a downcast counts as a type test and both triggers are named together`` () =
    let both =
        "module B\n\nlet slots: A.Node array = Array.zeroCreate 1\n\nlet cast (o: obj) = (o :?> A.Node).Value\n"

    let found, _ = sealedIn false node both

    match found with
    | [ s ] -> Assert.Equal("a Node[] and a :? Node test", s.Reason)
    | other -> failwith $"expected one suggestion, got %A{other}"

[<Fact>]
let ``a class only ever constructed and called is left alone: nothing pays for the seal`` () =
    let plain = "module B\n\nlet total = (A.Node 1).Value + (A.Node 2).Value\n"
    let found, _ = sealedIn false node plain
    Assert.Empty found

// ---- vetoes ----

[<Fact>]
let ``a class another file inherits is not sealed`` () =
    let sub = nodeArray + "\ntype Sub() =\n    inherit A.Node(9)\n"
    let found, _ = sealedIn false node sub
    Assert.Empty found

[<Fact>]
let ``a class an object expression builds on is not sealed`` () =
    let objExpr =
        nodeArray
        + "\nlet special = { new A.Node(1) with\n                    member _.ToString() = \"one\" }\n"

    let found, _ = sealedIn false node objExpr
    Assert.Empty found

[<Fact>]
let ``an object expression with the brace on the line above is still seen`` () =
    let objExpr =
        nodeArray
        + "\nlet special =\n    {\n        new A.Node(1) with\n            member _.ToString() = \"one\"\n    }\n"

    let found, _ = sealedIn false node objExpr
    Assert.Empty found

[<Fact>]
let ``a class with an abstract or default member cannot be sealed`` () =
    let withSlot =
        "module A\n\ntype internal Node(v: int) =\n    member _.Value = v\n    abstract Weight: unit -> int\n    default _.Weight() = v\n"

    let found, _ = sealedIn false withSlot nodeArray
    Assert.Empty found

[<Fact>]
let ``an already sealed class and an abstract class are not reported`` () =
    let sealedAlready =
        "module A\n\n[<Sealed>]\ntype internal Node(v: int) =\n    member _.Value = v\n"

    let abstractOne =
        "module A\n\n[<AbstractClass>]\ntype internal Node(v: int) =\n    member _.Value = v\n    abstract Weight: unit -> int\n"

    Assert.Empty(fst (sealedIn false sealedAlready nodeArray))
    Assert.Empty(fst (sealedIn false abstractOne nodeArray))

[<Fact>]
let ``a type-variable constraint naming the class vetoes the seal`` () =
    let constrained =
        nodeArray + "\nlet first<'T when 'T :> A.Node> (xs: 'T list) = List.head xs\n"

    let found, _ = sealedIn false node constrained
    Assert.Empty found

[<Fact>]
let ``a record is never a candidate`` () =
    let record = "module A\n\ntype internal Node = { Value: int }\n"
    let arr = "module B\n\nlet slots: A.Node[] = Array.zeroCreate 4\n"
    Assert.Empty(fst (sealedIn false record arr))

// ---- scope ----

[<Fact>]
let ``a public class seals only when the shape scope is open`` () =
    let publicNode = "module A\n\ntype Node(v: int) =\n    member _.Value = v\n"
    Assert.Empty(fst (sealedIn false publicNode nodeArray))
    Assert.Single(fst (sealedIn true publicNode nodeArray)) |> ignore

[<Fact>]
let ``without project results the rule says nothing`` () =
    let tree, source, check, _, _, _, _ = parseAndCheckPair node nodeArray
    Assert.Empty(SealedClass.find false tree source check None)

// ---- placement ----

[<Fact>]
let ``existing attributes above the type line take the seal above them`` () =
    let attributed =
        "module A\n\n/// A node.\n[<AllowNullLiteral>]\ntype internal Node(v: int) =\n    member _.Value = v\n"

    let found, recheck = sealedIn false attributed nodeArray

    match found with
    | [ s ] ->
        match s.Fix with
        | Some(r, text) ->
            Assert.Equal(4, r.StartLine)
            let patched = applyEdit attributed r text
            Assert.Contains("/// A node.\n[<Sealed>]\n[<AllowNullLiteral>]\ntype internal Node", patched)
            Assert.Empty(recheck patched nodeArray)
        | None -> failwith "expected the attribute fix"
    | other -> failwith $"expected one suggestion, got %A{other}"

[<Fact>]
let ``attributes on the type line itself keep the advice without an edit`` () =
    let inline' =
        "module A\n\ntype [<AllowNullLiteral>] internal Node(v: int) =\n    member _.Value = v\n"

    let found, _ = sealedIn false inline' nodeArray

    match found with
    | [ s ] -> Assert.True(s.Fix.IsNone)
    | other -> failwith $"expected one suggestion, got %A{other}"


// ---- outside the compilation ----

[<Fact>]
let ``a subclass in another project of the repository vetoes the seal`` () =
    // the project's typed results see only the project; a test project
    // stubbing the class, or a script #loading it, is read as text under
    // the repository root
    let tree, source, check, project, pathA, _, _ = parseAndCheckPair node nodeArray
    let dir = Path.GetDirectoryName pathA

    Directory.CreateDirectory(Path.Combine(dir, ".git")) |> ignore

    Directory.CreateDirectory(Path.Combine(dir, "tests")) |> ignore

    File.WriteAllText(Path.Combine(dir, "tests", "Stub.fs"), "module Stub\n\ntype Fake() =\n    inherit A.Node(0)\n")

    Assert.Empty(SealedClass.find false tree source check (Some project))

[<Fact>]
let ``an object expression in a script of the repository vetoes the seal`` () =
    let tree, source, check, project, pathA, _, _ = parseAndCheckPair node nodeArray
    let dir = Path.GetDirectoryName pathA

    Directory.CreateDirectory(Path.Combine(dir, ".git")) |> ignore

    File.WriteAllText(
        Path.Combine(dir, "probe.fsx"),
        "#load \"A.fs\"\n\nlet fake =\n    { new A.Node(0) with\n        member _.ToString() = \"\" }\n"
    )

    Assert.Empty(SealedClass.find false tree source check (Some project))
