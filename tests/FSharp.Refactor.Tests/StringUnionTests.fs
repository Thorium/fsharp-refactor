[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.StringUnionTests

open System
open System.IO
open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

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

let private findIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    StringUnion.find (worldOf check sourceText tree) tree sourceText

let private applyEdits (source: string) (edits: StringUnion.Edit list) =
    let lines = source.Split '\n'

    let offsetOf (line: int) (col: int) =
        (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

    edits
    |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
    |> List.fold
        (fun (acc: string) e ->
            let s = offsetOf e.Range.StartLine e.Range.StartColumn
            let en = offsetOf e.Range.EndLine e.Range.EndColumn
            acc.Substring(0, s) + e.Replacement + acc.Substring en)
        source

let private assertRewrite (source: string) (expected: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdits source s.Edits
        Assert.Equal(expected, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        s
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``a parameter every call site passes a literal for becomes a union, wildcard dropped`` () =
    let s =
        assertRewrite
            "let describe (region: string) =\n    match region with\n    | \"eu\"\n    | \"united kingdom\" -> 1\n    | \"united states\" -> 2\n    | _ -> failwith \"unsupported\"\n\nlet a = describe \"eu\"\nlet b = describe \"united states\"\nlet c = describe \"united kingdom\""
            "[<RequireQualifiedAccess>]\ntype Region =\n    | Eu\n    | UnitedKingdom\n    | UnitedStates\n\n    override this.ToString() =\n        match this with\n        | Region.Eu -> \"eu\"\n        | Region.UnitedKingdom -> \"united kingdom\"\n        | Region.UnitedStates -> \"united states\"\n\nlet describe (region: Region) =\n    match region with\n    | Region.Eu\n    | Region.UnitedKingdom -> 1\n    | Region.UnitedStates -> 2\n\nlet a = describe Region.Eu\nlet b = describe Region.UnitedStates\nlet c = describe Region.UnitedKingdom"

    Assert.Equal("Region", s.Name)
    Assert.Empty s.ShadowedConstants

[<Fact>]
let ``constants name the cases and the shadowing bug becomes the comparison it read as`` () =
    let s =
        assertRewrite
            "[<Literal>]\nlet uk = \"united kingdom\"\nlet us = \"united states\"\nlet eu = \"european union\"\n\nlet code (x: string) =\n    match x with\n    | uk -> 1\n    | us -> 2\n    | eu -> 3\n    | _ -> failwith \"not supported\"\n\nlet r = code uk + code us + code eu"
            "[<Literal>]\nlet uk = \"united kingdom\"\nlet us = \"united states\"\nlet eu = \"european union\"\n\n[<RequireQualifiedAccess>]\ntype X =\n    | Uk\n    | Us\n    | Eu\n\n    override this.ToString() =\n        match this with\n        | X.Uk -> uk\n        | X.Us -> us\n        | X.Eu -> eu\n\nlet code (x: X) =\n    match x with\n    | X.Uk -> 1\n    | X.Us -> 2\n    | X.Eu -> 3\n\nlet r = code X.Uk + code X.Us + code X.Eu"

    Assert.Equal<string list>([ "us"; "eu" ], s.ShadowedConstants)

[<Fact>]
let ``a producer whose every exit is a literal proves the set from the other end`` () =
    assertRewrite
        "let policyOf (json: string) =\n    match json.Trim() with\n    | \"n\" -> \"none\"\n    | \"nc\" -> \"no-correctness\"\n    | _ -> \"all\"\n\nlet honoured (json: string) =\n    let policy = if json = \"\" then \"all\" else policyOf json\n\n    match policy with\n    | \"none\" -> false\n    | \"no-correctness\" -> true\n    | _ -> true"
        "[<RequireQualifiedAccess>]\ntype Policy =\n    | None\n    | NoCorrectness\n    | All\n\n    override this.ToString() =\n        match this with\n        | Policy.None -> \"none\"\n        | Policy.NoCorrectness -> \"no-correctness\"\n        | Policy.All -> \"all\"\n\nlet policyOf (json: string) =\n    match json.Trim() with\n    | \"n\" -> Policy.None\n    | \"nc\" -> Policy.NoCorrectness\n    | _ -> Policy.All\n\nlet honoured (json: string) =\n    let policy = if json = \"\" then Policy.All else policyOf json\n\n    match policy with\n    | Policy.None -> false\n    | Policy.NoCorrectness -> true\n    | _ -> true"
    |> ignore

[<Fact>]
let ``a literal no arm names keeps the wildcard and gains a case`` () =
    assertRewrite
        "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = f \"on\" + f \"off\" + f \"auto\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n    | Auto\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n        | Mode.Auto -> \"auto\"\n\nlet f (mode: Mode) =\n    match mode with\n    | Mode.On -> 1\n    | Mode.Off -> 0\n    | _ -> -1\n\nlet x = f Mode.On + f Mode.Off + f Mode.Auto"
    |> ignore

[<Fact>]
let ``an interpolated print and a comparison ride along`` () =
    assertRewrite
        "let f (mode: string) =\n    printfn $\"mode {mode}\"\n    let quiet = mode = \"off\"\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = f \"on\" + f \"off\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n\nlet f (mode: Mode) =\n    printfn $\"mode {mode}\"\n    let quiet = mode = Mode.Off\n    match mode with\n    | Mode.On -> 1\n    | Mode.Off -> 0\n\nlet x = f Mode.On + f Mode.Off"
    |> ignore

[<Fact>]
let ``a record field fed by literals becomes a union field`` () =
    assertRewrite
        "type Item = { Kind: string; Size: int }\n\nlet items = [ { Kind = \"file\"; Size = 1 }; { Kind = \"dir\"; Size = 0 } ]\n\nlet weight (i: Item) =\n    match i.Kind with\n    | \"file\" -> i.Size\n    | \"dir\" -> 0\n    | _ -> failwith \"?\""
        "[<RequireQualifiedAccess>]\ntype Kind =\n    | File\n    | Dir\n\n    override this.ToString() =\n        match this with\n        | Kind.File -> \"file\"\n        | Kind.Dir -> \"dir\"\n\ntype Item = { Kind: Kind; Size: int }\n\nlet items = [ { Kind = Kind.File; Size = 1 }; { Kind = Kind.Dir; Size = 0 } ]\n\nlet weight (i: Item) =\n    match i.Kind with\n    | Kind.File -> i.Size\n    | Kind.Dir -> 0"
    |> ignore

[<Fact>]
let ``an option-wrapped flow keeps its None arm and its wildcard`` () =
    assertRewrite
        "let family (n: int) =\n    if n = 1 then Some \"MEL\"\n    elif n = 2 then Some \"Serilog\"\n    else None\n\nlet f (n: int) =\n    match family n with\n    | Some \"MEL\" -> 1\n    | Some \"Serilog\" -> 2\n    | _ -> 0"
        "[<RequireQualifiedAccess>]\ntype Family =\n    | MEL\n    | Serilog\n\n    override this.ToString() =\n        match this with\n        | Family.MEL -> \"MEL\"\n        | Family.Serilog -> \"Serilog\"\n\nlet family (n: int) =\n    if n = 1 then Some Family.MEL\n    elif n = 2 then Some Family.Serilog\n    else None\n\nlet f (n: int) =\n    match family n with\n    | Some Family.MEL -> 1\n    | Some Family.Serilog -> 2\n    | _ -> 0"
    |> ignore

[<Fact>]
let ``a call site passing a computed string keeps the set open`` () =
    Assert.Empty(
        findIn
            "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x (s: string) = f \"on\" + f (s.Trim())"
    )

[<Fact>]
let ``a %s hole becomes %O and a concatenation gains string`` () =
    assertRewrite
        "let f (mode: string) =\n    printfn \"mode %s, %d\" mode 1\n    let line = \"mode: \" + mode\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = f \"on\" + f \"off\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n\nlet f (mode: Mode) =\n    printfn \"mode %O, %d\" mode 1\n    let line = \"mode: \" + string mode\n    match mode with\n    | Mode.On -> 1\n    | Mode.Off -> 0\n\nlet x = f Mode.On + f Mode.Off"
    |> ignore

[<Fact>]
let ``a method call on the string keeps the set open`` () =
    Assert.Empty(
        findIn
            "let f (mode: string) =\n    let n = mode.Length\n    match mode with\n    | \"on\" -> n\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = f \"on\" + f \"off\""
    )

[<Fact>]
let ``a function used as a value keeps the set open`` () =
    Assert.Empty(
        findIn
            "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = [ \"on\"; \"off\" ] |> List.map f"
    )

[<Fact>]
let ``one literal arm is no set`` () =
    Assert.Empty(
        findIn "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | _ -> 0\n\nlet x = f \"on\""
    )

[<Fact>]
let ``a live named catch-all that prints stays, one that formats keeps the set open`` () =
    assertRewrite
        "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | other -> failwith $\"unknown {other}\"\n\nlet x = f \"on\" + f \"off\" + f \"auto\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n    | Auto\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n        | Mode.Auto -> \"auto\"\n\nlet f (mode: Mode) =\n    match mode with\n    | Mode.On -> 1\n    | Mode.Off -> 0\n    | other -> failwith $\"unknown {other}\"\n\nlet x = f Mode.On + f Mode.Off + f Mode.Auto"
    |> ignore

    Assert.Empty(
        findIn
            "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | other -> failwithf \"unknown %s\" other\n\nlet x = f \"on\" + f \"off\" + f \"auto\""
    )

[<Fact>]
let ``a name the project already uses for a type takes the Kind suffix`` () =
    let s =
        assertRewrite
            "type Mode = { Value: int }\n\nlet f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ -> -1\n\nlet x = f \"on\" + f \"off\""
            "type Mode = { Value: int }\n\n[<RequireQualifiedAccess>]\ntype ModeKind =\n    | On\n    | Off\n\n    override this.ToString() =\n        match this with\n        | ModeKind.On -> \"on\"\n        | ModeKind.Off -> \"off\"\n\nlet f (mode: ModeKind) =\n    match mode with\n    | ModeKind.On -> 1\n    | ModeKind.Off -> 0\n\nlet x = f ModeKind.On + f ModeKind.Off"

    Assert.Equal("ModeKind", s.Name)

[<Fact>]
let ``call sites in a later file are rewritten with the definition`` () =
    let sourceA =
        "module A\n\nlet describe (region: string) =\n    match region with\n    | \"eu\" -> 1\n    | \"uk\" -> 2\n    | _ -> 0\n"

    let sourceB = "module B\n\nlet x = A.describe \"eu\" + A.describe \"uk\"\n"

    let treeA, sourceTextA, checkA, projectResults, pathA, pathB, recheck =
        parseAndCheckPair sourceA sourceB

    let allUses = projectResults.GetAllUsesOfAllSymbols()

    let world =
        { worldOf checkA sourceTextA treeA with
            UsesOf = projectResults.GetUsesOfSymbol
            File =
                (fun path ->
                    if
                        String.Equals(
                            Path.GetFullPath path,
                            Path.GetFullPath pathA,
                            StringComparison.OrdinalIgnoreCase
                        )
                    then
                        Some(treeA, sourceTextA)
                    else
                        ProjectSources.tryParse path)
            SymbolAt =
                (fun file id ->
                    allUses
                    |> Array.tryFind (fun u ->
                        String.Equals(
                            Path.GetFullPath u.Range.FileName,
                            Path.GetFullPath file,
                            StringComparison.OrdinalIgnoreCase
                        )
                        && u.Range.StartLine = id.idRange.StartLine
                        && u.Range.StartColumn = id.idRange.StartColumn
                        && u.Range.EndColumn = id.idRange.EndColumn))
            FileOrder =
                (fun path ->
                    if Path.GetFullPath path = Path.GetFullPath pathA then
                        0
                    else
                        1)
        }

    match StringUnion.find world treeA sourceTextA with
    | [ s ] ->
        let inA =
            s.Edits
            |> List.filter (fun e -> Path.GetFullPath e.Range.FileName = Path.GetFullPath pathA)

        let inB =
            s.Edits
            |> List.filter (fun e -> Path.GetFullPath e.Range.FileName = Path.GetFullPath pathB)

        Assert.Equal(2, inB.Length)
        let patchedA = applyEdits sourceA inA
        let patchedB = applyEdits sourceB inB
        Assert.Equal("module B\n\nlet x = A.describe A.Region.Eu + A.describe A.Region.Uk\n", patchedB)
        let errors = recheck patchedA patchedB
        Assert.True(Array.isEmpty errors, $"errors: %A{errors}\n{patchedA}\n{patchedB}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``literals that only flow into a value nothing discriminates are not a set`` () =
    // a path, a message: two `Some "..."` sources and a `Some ex` that
    // passes the value on whole name no case anyone would want
    Assert.Empty(
        findIn
            "type W = { Example: string option }\nlet ws = [ { Example = Some \"examples/a.fsx\" }; { Example = Some \"examples/b.fsx\" } ]\nlet describe (w: W) =\n    match w.Example with\n    | Some ex -> $\"see {ex}\"\n    | None -> \"\""
    )

[<Fact>]
let ``a dead catch-all's comments outlive the arm`` () =
    assertRewrite
        "let f (mode: string) =\n    match mode with\n    | \"on\" -> 1\n    | \"off\" -> 0\n    | _ ->\n        // TODO: implement later\n        raise (System.NotSupportedException \"yeah\") // right?\n\nlet x = f \"on\" + f \"off\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n\nlet f (mode: Mode) =\n    match mode with\n    | Mode.On -> 1\n    | Mode.Off -> 0\n    // TODO: implement later\n    // right?\n\nlet x = f Mode.On + f Mode.Off"
    |> ignore

[<Fact>]
let ``a Result whose every Error is a literal becomes a Result of the union`` () =
    assertRewrite
        "let load (path: string) : Result<int, string> =\n    if path = \"\" then Error \"not found\"\n    elif path = \"x\" then Error \"locked\"\n    else Ok path.Length\n\nlet describe (path: string) =\n    match load path with\n    | Ok n -> string n\n    | Error \"not found\" -> \"missing\"\n    | Error \"locked\" -> \"busy\"\n    | Error e -> $\"other: {e}\""
        "[<RequireQualifiedAccess>]\ntype Load =\n    | NotFound\n    | Locked\n\n    override this.ToString() =\n        match this with\n        | Load.NotFound -> \"not found\"\n        | Load.Locked -> \"locked\"\n\nlet load (path: string) : Result<int, Load> =\n    if path = \"\" then Error Load.NotFound\n    elif path = \"x\" then Error Load.Locked\n    else Ok path.Length\n\nlet describe (path: string) =\n    match load path with\n    | Ok n -> string n\n    | Error Load.NotFound -> \"missing\"\n    | Error Load.Locked -> \"busy\""
    |> ignore

[<Fact>]
let ``a sentence-shaped literal keeps its words behind backticks`` () =
    assertRewrite
        "let f (reason: string) =\n    match reason with\n    | \"bank account could not be selected here\" -> 1\n    | \"ok\" -> 0\n    | _ -> -1\n\nlet x = f \"ok\" + f \"bank account could not be selected here\""
        "[<RequireQualifiedAccess>]\ntype Reason =\n    | ``Bank account could not be selected here``\n    | Ok\n\n    override this.ToString() =\n        match this with\n        | Reason.``Bank account could not be selected here`` -> \"bank account could not be selected here\"\n        | Reason.Ok -> \"ok\"\n\nlet f (reason: Reason) =\n    match reason with\n    | Reason.``Bank account could not be selected here`` -> 1\n    | Reason.Ok -> 0\n\nlet x = f Reason.Ok + f Reason.``Bank account could not be selected here``"
    |> ignore

[<Fact>]
let ``an Ok value that is a string is not the error: only the error side becomes the union`` () =
    // the `Error _` catch-all is dead once both errors have arms and the Ok
    // case its own; it goes
    assertRewrite
        "let load (path: string) : Result<string, string> =\n    if path = \"\" then Error \"not found\" else Ok path\n\nlet describe (path: string) =\n    match load path with\n    | Ok s -> s.Length\n    | Error \"not found\" -> -1\n    | Error \"locked\" -> -2\n    | Error _ -> 0"
        "[<RequireQualifiedAccess>]\ntype Load =\n    | NotFound\n    | Locked\n\n    override this.ToString() =\n        match this with\n        | Load.NotFound -> \"not found\"\n        | Load.Locked -> \"locked\"\n\nlet load (path: string) : Result<string, Load> =\n    if path = \"\" then Error Load.NotFound else Ok path\n\nlet describe (path: string) =\n    match load path with\n    | Ok s -> s.Length\n    | Error Load.NotFound -> -1\n    | Error Load.Locked -> -2"
    |> ignore

[<Fact>]
let ``a dynamic error message keeps the set open`` () =
    Assert.Empty(
        findIn
            "let load (path: string) : Result<int, string> =\n    if path = \"\" then Error \"not found\"\n    elif path = \"x\" then Error $\"locked by {path}\"\n    else Ok 1\n\nlet describe (path: string) =\n    match load path with\n    | Ok n -> n\n    | Error \"not found\" -> -1\n    | Error \"locked\" -> -2\n    | Error _ -> 0"
    )

[<Fact>]
let ``a record a serializer fills keeps its string field`` () =
    // CLIMutable, or the type as a type argument of a Deserialize: a
    // construction with a literal is not the field's only source
    Assert.Empty(
        findIn
            "[<CLIMutable>]\ntype Item = { Kind: string; Size: int }\n\nlet items = [ { Kind = \"file\"; Size = 1 }; { Kind = \"dir\"; Size = 0 } ]\n\nlet weight (i: Item) =\n    match i.Kind with\n    | \"file\" -> i.Size\n    | \"dir\" -> 0\n    | _ -> failwith \"?\""
    )

    Assert.Empty(
        findIn
            "type Item = { Kind: string; Size: int }\n\nlet items = [ { Kind = \"file\"; Size = 1 }; { Kind = \"dir\"; Size = 0 } ]\nlet load (json: string) = System.Text.Json.JsonSerializer.Deserialize<Item>(json)\n\nlet weight (i: Item) =\n    match i.Kind with\n    | \"file\" -> i.Size\n    | \"dir\" -> 0\n    | _ -> failwith \"?\""
    )

[<Fact>]
let ``arms alone prove nothing: a function nothing calls keeps its string`` () =
    Assert.Empty(
        findIn
            "let log (level: string) (message: string) =\n    match level with\n    | \"Debug\" -> 1\n    | \"Info\" -> 2\n    | _ -> 3"
    )

let private findClosed (source: string) =
    let tree, sourceText, check = parseAndCheck source

    StringUnion.find
        { worldOf check sourceText tree with
            ScopeOpen = false
        }
        tree
        sourceText

let private assertClosedRewrite (source: string) (expected: string) =
    match findClosed source with
    | [ s ] ->
        let patched = applyEdits source s.Edits
        Assert.Equal(expected, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        s
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``an exported parameter keeps its string signature behind OfString and a private twin`` () =
    // callers outside the compilation keep `describe "eu"`; unknown input
    // raises exactly as the catch-all did, now from OfString
    assertClosedRewrite
        "module Lib\n\nlet describe (region: string) =\n    match region with\n    | \"eu\" -> 1\n    | \"uk\" -> 2\n    | other -> failwith (\"unsupported: \" + other)\n\nlet total = describe \"eu\" + describe \"uk\""
        "module Lib\n\n[<RequireQualifiedAccess>]\ntype Region =\n    | Eu\n    | Uk\n\n    override this.ToString() =\n        match this with\n        | Region.Eu -> \"eu\"\n        | Region.Uk -> \"uk\"\n\n    static member OfString(other: string) =\n        match other with\n        | \"eu\" -> Region.Eu\n        | \"uk\" -> Region.Uk\n        | other -> failwith (\"unsupported: \" + other)\n\nlet private describeCore (region: Region) =\n    match region with\n    | Region.Eu -> 1\n    | Region.Uk -> 2\n\n// TODO: consider changing the API to Region and removing this mapping\nlet describe (region: string) =\n    describeCore (Region.OfString region)\n\nlet total = describeCore Region.Eu + describeCore Region.Uk"
    |> ignore

[<Fact>]
let ``an exported Result return keeps its string signature behind Result.mapError`` () =
    assertClosedRewrite
        "module Lib\n\nlet load (path: string) : Result<int, string> =\n    if path = \"\" then Error \"not found\"\n    elif path = \"x\" then Error \"locked\"\n    else Ok path.Length\n\nlet private describe (path: string) =\n    match load path with\n    | Ok n -> n\n    | Error \"not found\" -> -1\n    | Error \"locked\" -> -2\n    | Error _ -> 0"
        "module Lib\n\n[<RequireQualifiedAccess>]\ntype Load =\n    | NotFound\n    | Locked\n\n    override this.ToString() =\n        match this with\n        | Load.NotFound -> \"not found\"\n        | Load.Locked -> \"locked\"\n\nlet private loadCore (path: string) : Result<int, Load> =\n    if path = \"\" then Error Load.NotFound\n    elif path = \"x\" then Error Load.Locked\n    else Ok path.Length\n\n// TODO: consider changing the API to Load and removing this mapping\nlet load (path: string) : Result<int, string> =\n    loadCore path |> Result.mapError string\n\nlet private describe (path: string) =\n    match loadCore path with\n    | Ok n -> n\n    | Error Load.NotFound -> -1\n    | Error Load.Locked -> -2"
    |> ignore

[<Fact>]
let ``an exported parameter whose catch-all returns a default has no OfString to give`` () =
    Assert.Empty(
        findClosed
            "module Lib\n\nlet describe (region: string) =\n    match region with\n    | \"eu\" -> 1\n    | \"uk\" -> 2\n    | _ -> 0\n\nlet total = describe \"eu\" + describe \"uk\""
    )

[<Fact>]
let ``a typed %s hole in an interpolated string becomes %O`` () =
    assertRewrite
        "let f (mode: string) =\n    let line = $\"mode: %s{mode}!\"\n    match mode with\n    | \"on\" -> line\n    | \"off\" -> \"\"\n    | _ -> \"?\"\n\nlet x = f \"on\" + f \"off\""
        "[<RequireQualifiedAccess>]\ntype Mode =\n    | On\n    | Off\n\n    override this.ToString() =\n        match this with\n        | Mode.On -> \"on\"\n        | Mode.Off -> \"off\"\n\nlet f (mode: Mode) =\n    let line = $\"mode: %O{mode}!\"\n    match mode with\n    | Mode.On -> line\n    | Mode.Off -> \"\"\n\nlet x = f Mode.On + f Mode.Off"
    |> ignore
