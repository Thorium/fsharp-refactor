/// The companion signature edited IN STEP with a shape-changing rewrite:
/// FR0130's [<Literal>] (attribute plus the value the .fsi must then spell
/// out), FR0016's [<Struct>], FR0133's rename — all through SignatureFile,
/// the mechanism FR0022 introduced for union-case field names.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.SignatureCoEditTests

open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// An implementation with its signature beside it, and the cross-file
/// parser the CLI installs, so the rule can read the .fsi. The parser is
/// taken down again afterwards: the tests that assert a stand-down beside
/// an UNREADABLE signature rely on there being none.
let private withSignature (impl: string) (signature: string) (test: string -> string -> unit) =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-coedit-" + System.Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore
    let implPath = Path.Combine(dir, "M.fs")
    let sigPath = Path.Combine(dir, "M.fsi")
    File.WriteAllText(implPath, impl)
    File.WriteAllText(sigPath, signature)
    ProjectSources.configure (Some(fun path -> Some(parseNamed path (File.ReadAllText path))))

    try
        test implPath sigPath
    finally
        ProjectSources.configure None
        Directory.Delete(dir, true)

/// Apply a rule's signature edits to the signature text, bottom-up so
/// earlier positions stay valid.
let private patchSignature (signature: string) (edits: SignatureFile.Edit list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun text (r, _, replacement) -> applyEdit text r replacement) signature

[<Fact>]
let ``FR0130 carries the literal into the signature`` () =
    // a signature declares a literal WITH its value — `val answer: int = 42`
    // — so the .fsi gets both the attribute and the value
    withSignature "module M\n\nlet answer = 42\n" "module M\n\nval answer: int\n" (fun implPath _ ->
        let tree, sourceText = parseNamed implPath (File.ReadAllText implPath)

        match LiteralConst.find true tree sourceText with
        | [ s ] ->
            Assert.Equal(2, s.SignatureEdits.Length)

            Assert.Equal(
                fsharp
                    """
                    module M

                    [<Literal>]
                    val answer: int = 42

                    """,
                patchSignature "module M\n\nval answer: int\n" s.SignatureEdits
            )
        | other -> failwithf "Expected one literal fix carrying its signature, got %A" other)

[<Fact>]
let ``FR0130 leaves a value the signature does not declare alone`` () =
    // hidden behind the signature: the implementation's own business
    withSignature "module M\n\nlet answer = 42\n" "module M\n\nval other: int\n" (fun implPath _ ->
        let tree, sourceText = parseNamed implPath (File.ReadAllText implPath)

        match LiteralConst.find true tree sourceText with
        | [ s ] -> Assert.Empty s.SignatureEdits
        | other -> failwithf "Expected one literal fix with no signature half, got %A" other)

[<Fact>]
let ``FR0130 withholds where the signature already attributes the value`` () =
    withSignature
        "module M\n\nlet answer = 42\n"
        (fsharp
            """
            module M

            [<Literal>]
            val answer: int = 42

            """)
        (fun implPath _ ->
            let tree, sourceText = parseNamed implPath (File.ReadAllText implPath)
            Assert.Empty(LiteralConst.find true tree sourceText))

[<Fact>]
let ``FR0130 withholds where the signature cannot be read`` () =
    // editors install no cross-file parser: a half-done fix is worse than
    // none
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-coedit-" + System.Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let implPath = Path.Combine(dir, "M.fs")
        File.WriteAllText(implPath, "module M\n\nlet answer = 42\n")
        File.WriteAllText(Path.Combine(dir, "M.fsi"), "module M\n\nval answer: int\n")
        ProjectSources.configure None
        let tree, sourceText = parseNamed implPath "module M\n\nlet answer = 42\n"
        Assert.Empty(LiteralConst.find true tree sourceText)
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``FR0016 carries the Struct attribute into the signature`` () =
    let impl =
        fsharp
            """
            module M

            type Shape =
                | Circle of radius: float
                | Square of side: float

            """

    let signature =
        fsharp
            """
            module M

            type Shape =
                | Circle of radius: float
                | Square of side: float

            """

    withSignature impl signature (fun implPath _ ->
        let tree, sourceText = parseNamed implPath impl

        match StructDu.find true tree sourceText with
        | [ s ] ->
            Assert.Equal(
                fsharp
                    """
                    module M

                    [<Struct>]
                    type Shape =
                        | Circle of radius: float
                        | Square of side: float

                    """,
                patchSignature signature s.SignatureEdits
            )
        | other -> failwithf "Expected one struct fix carrying its signature, got %A" other)

[<Fact>]
let ``FR0133 renames the signature's val alongside every use`` () =
    // a test-attributed public function is the one FR0133 candidate a
    // signature can declare; the attribute type is declared in the source
    // so the fixture needs no test framework
    let impl =
        fsharp
            """
            module A

            type FactAttribute() =
                inherit System.Attribute()

            [<Fact>]
            let thisIsMyVeryComplexTestCase () = ()

            """

    let treeA, sourceTextA, checkA, projectResults, pathA, _, _ =
        parseAndCheckPair impl "module B\n"

    File.WriteAllText(
        Path.ChangeExtension(pathA, ".fsi"),
        fsharp
            """
            module A

            type FactAttribute =
                inherit System.Attribute
                new: unit -> FactAttribute

            [<Fact>]
            val thisIsMyVeryComplexTestCase: unit -> unit

            """
    )

    match NameQuoting.find false treeA sourceTextA checkA (Some projectResults) with
    | [ s ] ->
        let signatureEdits =
            s.Edits |> List.filter (fun (r, _, _) -> r.FileName.EndsWith ".fsi")

        match signatureEdits with
        | [ _, original, replacement ] ->
            Assert.Equal("thisIsMyVeryComplexTestCase", original)
            Assert.Equal("``this is my very complex test case``", replacement)
        | other -> failwithf "Expected exactly one signature rename, got %A" other
    | other -> failwithf "Expected one rename carrying its signature, got %A" other
