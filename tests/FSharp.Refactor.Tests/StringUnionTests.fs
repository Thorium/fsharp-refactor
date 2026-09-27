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
            (fsharp
                """
                let describe (region: string) =
                    match region with
                    | "eu"
                    | "united kingdom" -> 1
                    | "united states" -> 2
                    | _ -> failwith "unsupported"

                let a = describe "eu"
                let b = describe "united states"
                let c = describe "united kingdom"
                """)
            (fsharp
                """
                [<RequireQualifiedAccess>]
                type Region =
                    | Eu
                    | UnitedKingdom
                    | UnitedStates

                    override this.ToString() =
                        match this with
                        | Region.Eu -> "eu"
                        | Region.UnitedKingdom -> "united kingdom"
                        | Region.UnitedStates -> "united states"

                let describe (region: Region) =
                    match region with
                    | Region.Eu
                    | Region.UnitedKingdom -> 1
                    | Region.UnitedStates -> 2

                let a = describe Region.Eu
                let b = describe Region.UnitedStates
                let c = describe Region.UnitedKingdom
                """)

    Assert.Equal("Region", s.Name)
    Assert.Empty s.ShadowedConstants

[<Fact>]
let ``constants name the cases and the shadowing bug becomes the comparison it read as`` () =
    let s =
        assertRewrite
            (fsharp
                """
                [<Literal>]
                let uk = "united kingdom"
                let us = "united states"
                let eu = "european union"

                let code (x: string) =
                    match x with
                    | uk -> 1
                    | us -> 2
                    | eu -> 3
                    | _ -> failwith "not supported"

                let r = code uk + code us + code eu
                """)
            (fsharp
                """
                [<Literal>]
                let uk = "united kingdom"
                let us = "united states"
                let eu = "european union"

                [<RequireQualifiedAccess>]
                type X =
                    | Uk
                    | Us
                    | Eu

                    override this.ToString() =
                        match this with
                        | X.Uk -> uk
                        | X.Us -> us
                        | X.Eu -> eu

                let code (x: X) =
                    match x with
                    | X.Uk -> 1
                    | X.Us -> 2
                    | X.Eu -> 3

                let r = code X.Uk + code X.Us + code X.Eu
                """)

    Assert.Equal<string list>([ "us"; "eu" ], s.ShadowedConstants)

[<Fact>]
let ``a producer whose every exit is a literal proves the set from the other end`` () =
    assertRewrite
        (fsharp
            """
            let policyOf (json: string) =
                match json.Trim() with
                | "n" -> "none"
                | "nc" -> "no-correctness"
                | _ -> "all"

            let honoured (json: string) =
                let policy = if json = "" then "all" else policyOf json

                match policy with
                | "none" -> false
                | "no-correctness" -> true
                | _ -> true
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Policy =
                | None
                | NoCorrectness
                | All

                override this.ToString() =
                    match this with
                    | Policy.None -> "none"
                    | Policy.NoCorrectness -> "no-correctness"
                    | Policy.All -> "all"

            let policyOf (json: string) =
                match json.Trim() with
                | "n" -> Policy.None
                | "nc" -> Policy.NoCorrectness
                | _ -> Policy.All

            let honoured (json: string) =
                let policy = if json = "" then Policy.All else policyOf json

                match policy with
                | Policy.None -> false
                | Policy.NoCorrectness -> true
                | _ -> true
            """)
    |> ignore

[<Fact>]
let ``a literal no arm names keeps the wildcard and gains a case`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                match mode with
                | "on" -> 1
                | "off" -> 0
                | _ -> -1

            let x = f "on" + f "off" + f "auto"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off
                | Auto

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"
                    | Mode.Auto -> "auto"

            let f (mode: Mode) =
                match mode with
                | Mode.On -> 1
                | Mode.Off -> 0
                | _ -> -1

            let x = f Mode.On + f Mode.Off + f Mode.Auto
            """)
    |> ignore

[<Fact>]
let ``an interpolated print and a comparison ride along`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                printfn $"mode {mode}"
                let quiet = mode = "off"
                match mode with
                | "on" -> 1
                | "off" -> 0
                | _ -> -1

            let x = f "on" + f "off"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"

            let f (mode: Mode) =
                printfn $"mode {mode}"
                let quiet = mode = Mode.Off
                match mode with
                | Mode.On -> 1
                | Mode.Off -> 0

            let x = f Mode.On + f Mode.Off
            """)
    |> ignore

[<Fact>]
let ``a record field fed by literals becomes a union field`` () =
    assertRewrite
        (fsharp
            """
            type Item = { Kind: string; Size: int }

            let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]

            let weight (i: Item) =
                match i.Kind with
                | "file" -> i.Size
                | "dir" -> 0
                | _ -> failwith "?"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Kind =
                | File
                | Dir

                override this.ToString() =
                    match this with
                    | Kind.File -> "file"
                    | Kind.Dir -> "dir"

            type Item = { Kind: Kind; Size: int }

            let items = [ { Kind = Kind.File; Size = 1 }; { Kind = Kind.Dir; Size = 0 } ]

            let weight (i: Item) =
                match i.Kind with
                | Kind.File -> i.Size
                | Kind.Dir -> 0
            """)
    |> ignore

[<Fact>]
let ``an option-wrapped flow keeps its None arm and its wildcard`` () =
    assertRewrite
        (fsharp
            """
            let family (n: int) =
                if n = 1 then Some "MEL"
                elif n = 2 then Some "Serilog"
                else None

            let f (n: int) =
                match family n with
                | Some "MEL" -> 1
                | Some "Serilog" -> 2
                | _ -> 0
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Family =
                | MEL
                | Serilog

                override this.ToString() =
                    match this with
                    | Family.MEL -> "MEL"
                    | Family.Serilog -> "Serilog"

            let family (n: int) =
                if n = 1 then Some Family.MEL
                elif n = 2 then Some Family.Serilog
                else None

            let f (n: int) =
                match family n with
                | Some Family.MEL -> 1
                | Some Family.Serilog -> 2
                | _ -> 0
            """)
    |> ignore

[<Fact>]
let ``a call site passing a computed string keeps the set open`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | _ -> -1

                let x (s: string) = f "on" + f (s.Trim())
                """
        )
    )

[<Fact>]
let ``a %s hole becomes %O and a concatenation gains string`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                printfn "mode %s, %d" mode 1
                let line = "mode: " + mode
                match mode with
                | "on" -> 1
                | "off" -> 0
                | _ -> -1

            let x = f "on" + f "off"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"

            let f (mode: Mode) =
                printfn "mode %O, %d" mode 1
                let line = "mode: " + string mode
                match mode with
                | Mode.On -> 1
                | Mode.Off -> 0

            let x = f Mode.On + f Mode.Off
            """)
    |> ignore

[<Fact>]
let ``a method call on the string keeps the set open`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (mode: string) =
                    let n = mode.Length
                    match mode with
                    | "on" -> n
                    | "off" -> 0
                    | _ -> -1

                let x = f "on" + f "off"
                """
        )
    )

[<Fact>]
let ``a function used as a value keeps the set open`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | _ -> -1

                let x = [ "on"; "off" ] |> List.map f
                """
        )
    )

[<Fact>]
let ``one literal arm is no set`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let f (mode: string) =
                    match mode with
                    | "on" -> 1
                    | _ -> 0

                let x = f "on"
                """
        )
    )

[<Fact>]
let ``a live named catch-all that prints stays, one that formats keeps the set open`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                match mode with
                | "on" -> 1
                | "off" -> 0
                | other -> failwith $"unknown {other}"

            let x = f "on" + f "off" + f "auto"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off
                | Auto

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"
                    | Mode.Auto -> "auto"

            let f (mode: Mode) =
                match mode with
                | Mode.On -> 1
                | Mode.Off -> 0
                | other -> failwith $"unknown {other}"

            let x = f Mode.On + f Mode.Off + f Mode.Auto
            """)
    |> ignore

    Assert.Empty(
        findIn (
            fsharp
                """
                let f (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | other -> failwithf "unknown %s" other

                let x = f "on" + f "off" + f "auto"
                """
        )
    )

[<Fact>]
let ``a name the project already uses for a type takes the Kind suffix`` () =
    let s =
        assertRewrite
            (fsharp
                """
                type Mode = { Value: int }

                let f (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | _ -> -1

                let x = f "on" + f "off"
                """)
            (fsharp
                """
                type Mode = { Value: int }

                [<RequireQualifiedAccess>]
                type ModeKind =
                    | On
                    | Off

                    override this.ToString() =
                        match this with
                        | ModeKind.On -> "on"
                        | ModeKind.Off -> "off"

                let f (mode: ModeKind) =
                    match mode with
                    | ModeKind.On -> 1
                    | ModeKind.Off -> 0

                let x = f ModeKind.On + f ModeKind.Off
                """)

    Assert.Equal("ModeKind", s.Name)

[<Fact>]
let ``call sites in a later file are rewritten with the definition`` () =
    let sourceA =
        fsharp
            """
            module A

            let describe (region: string) =
                match region with
                | "eu" -> 1
                | "uk" -> 2
                | _ -> 0

            """

    let sourceB =
        fsharp
            """
            module B

            let x = A.describe "eu" + A.describe "uk"

            """

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

        Assert.Equal(
            fsharp
                """
                module B

                let x = A.describe A.Region.Eu + A.describe A.Region.Uk

                """,
            patchedB
        )

        let errors = recheck patchedA patchedB
        Assert.True(Array.isEmpty errors, $"errors: %A{errors}\n%s{patchedA}\n%s{patchedB}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``literals that only flow into a value nothing discriminates are not a set`` () =
    // a path, a message: two `Some "..."` sources and a `Some ex` that
    // passes the value on whole name no case anyone would want
    Assert.Empty(
        findIn (
            fsharp
                """
                type W = { Example: string option }
                let ws = [ { Example = Some "examples/a.fsx" }; { Example = Some "examples/b.fsx" } ]
                let describe (w: W) =
                    match w.Example with
                    | Some ex -> $"see {ex}"
                    | None -> ""
                """
        )
    )

[<Fact>]
let ``a dead catch-all's comments outlive the arm`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                match mode with
                | "on" -> 1
                | "off" -> 0
                | _ ->
                    // TODO: implement later
                    raise (System.NotSupportedException "yeah") // right?

            let x = f "on" + f "off"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"

            let f (mode: Mode) =
                match mode with
                | Mode.On -> 1
                | Mode.Off -> 0
                // TODO: implement later
                // right?

            let x = f Mode.On + f Mode.Off
            """)
    |> ignore

[<Fact>]
let ``a Result whose every Error is a literal becomes a Result of the union`` () =
    assertRewrite
        (fsharp
            """
            let load (path: string) : Result<int, string> =
                if path = "" then Error "not found"
                elif path = "x" then Error "locked"
                else Ok path.Length

            let describe (path: string) =
                match load path with
                | Ok n -> string n
                | Error "not found" -> "missing"
                | Error "locked" -> "busy"
                | Error e -> $"other: {e}"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Load =
                | NotFound
                | Locked

                override this.ToString() =
                    match this with
                    | Load.NotFound -> "not found"
                    | Load.Locked -> "locked"

            let load (path: string) : Result<int, Load> =
                if path = "" then Error Load.NotFound
                elif path = "x" then Error Load.Locked
                else Ok path.Length

            let describe (path: string) =
                match load path with
                | Ok n -> string n
                | Error Load.NotFound -> "missing"
                | Error Load.Locked -> "busy"
            """)
    |> ignore

[<Fact>]
let ``a sentence-shaped literal keeps its words behind backticks`` () =
    assertRewrite
        (fsharp
            """
            let f (reason: string) =
                match reason with
                | "bank account could not be selected here" -> 1
                | "ok" -> 0
                | _ -> -1

            let x = f "ok" + f "bank account could not be selected here"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Reason =
                | ``Bank account could not be selected here``
                | Ok

                override this.ToString() =
                    match this with
                    | Reason.``Bank account could not be selected here`` -> "bank account could not be selected here"
                    | Reason.Ok -> "ok"

            let f (reason: Reason) =
                match reason with
                | Reason.``Bank account could not be selected here`` -> 1
                | Reason.Ok -> 0

            let x = f Reason.Ok + f Reason.``Bank account could not be selected here``
            """)
    |> ignore

[<Fact>]
let ``an Ok value that is a string is not the error: only the error side becomes the union`` () =
    // the `Error _` catch-all is dead once both errors have arms and the Ok
    // case its own; it goes
    assertRewrite
        (fsharp
            """
            let load (path: string) : Result<string, string> =
                if path = "" then Error "not found" else Ok path

            let describe (path: string) =
                match load path with
                | Ok s -> s.Length
                | Error "not found" -> -1
                | Error "locked" -> -2
                | Error _ -> 0
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Load =
                | NotFound
                | Locked

                override this.ToString() =
                    match this with
                    | Load.NotFound -> "not found"
                    | Load.Locked -> "locked"

            let load (path: string) : Result<string, Load> =
                if path = "" then Error Load.NotFound else Ok path

            let describe (path: string) =
                match load path with
                | Ok s -> s.Length
                | Error Load.NotFound -> -1
                | Error Load.Locked -> -2
            """)
    |> ignore

[<Fact>]
let ``a dynamic error message keeps the set open`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let load (path: string) : Result<int, string> =
                    if path = "" then Error "not found"
                    elif path = "x" then Error $"locked by {path}"
                    else Ok 1

                let describe (path: string) =
                    match load path with
                    | Ok n -> n
                    | Error "not found" -> -1
                    | Error "locked" -> -2
                    | Error _ -> 0
                """
        )
    )

[<Fact>]
let ``a record a serializer fills keeps its string field`` () =
    // CLIMutable, or the type as a type argument of a Deserialize: a
    // construction with a literal is not the field's only source
    Assert.Empty(
        findIn (
            fsharp
                """
                [<CLIMutable>]
                type Item = { Kind: string; Size: int }

                let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }

                let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]
                let load (json: string) = System.Text.Json.JsonSerializer.Deserialize<Item>(json)

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"
                """
        )
    )

[<Fact>]
let ``arms alone prove nothing: a function nothing calls keeps its string`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                let log (level: string) (message: string) =
                    match level with
                    | "Debug" -> 1
                    | "Info" -> 2
                    | _ -> 3
                """
        )
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
        (fsharp
            """
            module Lib

            let describe (region: string) =
                match region with
                | "eu" -> 1
                | "uk" -> 2
                | other -> failwith ("unsupported: " + other)

            let total = describe "eu" + describe "uk"
            """)
        (fsharp
            """
            module Lib

            [<RequireQualifiedAccess>]
            type Region =
                | Eu
                | Uk

                override this.ToString() =
                    match this with
                    | Region.Eu -> "eu"
                    | Region.Uk -> "uk"

                static member OfString(other: string) =
                    match other with
                    | "eu" -> Region.Eu
                    | "uk" -> Region.Uk
                    | other -> failwith ("unsupported: " + other)

            let private describeCore (region: Region) =
                match region with
                | Region.Eu -> 1
                | Region.Uk -> 2

            // TODO: consider changing the API to Region and removing this mapping
            let describe (region: string) =
                describeCore (Region.OfString region)

            let total = describeCore Region.Eu + describeCore Region.Uk
            """)
    |> ignore

[<Fact>]
let ``an exported Result return keeps its string signature behind Result.mapError`` () =
    assertClosedRewrite
        (fsharp
            """
            module Lib

            let load (path: string) : Result<int, string> =
                if path = "" then Error "not found"
                elif path = "x" then Error "locked"
                else Ok path.Length

            let private describe (path: string) =
                match load path with
                | Ok n -> n
                | Error "not found" -> -1
                | Error "locked" -> -2
                | Error _ -> 0
            """)
        (fsharp
            """
            module Lib

            [<RequireQualifiedAccess>]
            type Load =
                | NotFound
                | Locked

                override this.ToString() =
                    match this with
                    | Load.NotFound -> "not found"
                    | Load.Locked -> "locked"

            let private loadCore (path: string) : Result<int, Load> =
                if path = "" then Error Load.NotFound
                elif path = "x" then Error Load.Locked
                else Ok path.Length

            // TODO: consider changing the API to Load and removing this mapping
            let load (path: string) : Result<int, string> =
                loadCore path |> Result.mapError string

            let private describe (path: string) =
                match loadCore path with
                | Ok n -> n
                | Error Load.NotFound -> -1
                | Error Load.Locked -> -2
            """)
    |> ignore

[<Fact>]
let ``an exported parameter whose catch-all returns a default has no OfString to give`` () =
    Assert.Empty(
        findClosed (
            fsharp
                """
                module Lib

                let describe (region: string) =
                    match region with
                    | "eu" -> 1
                    | "uk" -> 2
                    | _ -> 0

                let total = describe "eu" + describe "uk"
                """
        )
    )

[<Fact>]
let ``a typed %s hole in an interpolated string becomes %O`` () =
    assertRewrite
        (fsharp
            """
            let f (mode: string) =
                let line = $"mode: %s{mode}!"
                match mode with
                | "on" -> line
                | "off" -> ""
                | _ -> "?"

            let x = f "on" + f "off"
            """)
        (fsharp
            """
            [<RequireQualifiedAccess>]
            type Mode =
                | On
                | Off

                override this.ToString() =
                    match this with
                    | Mode.On -> "on"
                    | Mode.Off -> "off"

            let f (mode: Mode) =
                let line = $"mode: %O{mode}!"
                match mode with
                | Mode.On -> line
                | Mode.Off -> ""

            let x = f Mode.On + f Mode.Off
            """)
    |> ignore

[<Fact>]
let ``two fields of the same name in one file get distinct union names`` () =
    // both records have a `Kind` field over their own literal sets: the
    // second union carries its record's name rather than duplicating `Kind`
    // (Fuuga's generate-honesty-data.fsx, a duplicate definition rolled back)
    let names =
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }
                type Job = { Kind: string; Id: int }

                let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]
                let jobs = [ { Kind = "build"; Id = 1 }; { Kind = "test"; Id = 2 } ]

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"

                let cost (j: Job) =
                    match j.Kind with
                    | "build" -> 10
                    | "test" -> 1
                    | _ -> failwith "?"
                """
        )
        |> List.map (fun s -> s.Name)
        |> List.sort

    Assert.Equal<string list>([ "JobKind"; "Kind" ], names)

[<Fact>]
let ``a record handed to a serializer with its type inferred stands down`` () =
    // no type argument names the record, the value does: every field is
    // read by reflection, and a union field would serialize differently
    Assert.Empty(
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }

                let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"

                let json = System.Text.Json.JsonSerializer.Serialize items
                """
        )
    )

[<Fact>]
let ``a record piped into a serializer stands down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }

                let item = { Kind = "file"; Size = 1 }

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"

                let json = item |> System.Text.Json.JsonSerializer.Serialize
                """
        )
    )

[<Fact>]
let ``a record handed to an ordinary function keeps the union`` () =
    let found =
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }

                let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"

                let total = items |> List.sumBy weight
                """
        )

    Assert.Equal(1, found.Length)

[<Fact>]
let ``a union typing only private slots is private`` () =
    // a public type the rule added would widen a library's API by itself
    match
        findIn (
            fsharp
                """
                module M

                let private describe (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | _ -> failwith "?"

                let run () = describe "on" + describe "off"
                """
        )
    with
    | [ s ] ->
        let union =
            s.Edits
            |> List.map (fun e -> e.Replacement)
            |> List.find (fun t -> t.Contains "type ")

        Assert.Contains("type private Mode =", union)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a union typing an internal slot is internal`` () =
    match
        findIn (
            fsharp
                """
                module M

                let internal describe (mode: string) =
                    match mode with
                    | "on" -> 1
                    | "off" -> 0
                    | _ -> failwith "?"

                let private run () = describe "on" + describe "off"
                """
        )
    with
    | [ s ] ->
        let union =
            s.Edits
            |> List.map (fun e -> e.Replacement)
            |> List.find (fun t -> t.Contains "type ")

        Assert.Contains("type internal Mode =", union)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a record reached through a field and a curried serializer call stands down`` () =
    // `Serialize options wrapper.Items`: the record is two arguments in and
    // behind a field, and every field of it is still read by reflection
    Assert.Empty(
        findIn (
            fsharp
                """
                type Item = { Kind: string; Size: int }
                type Wrapper = { Items: Item list }

                let wrapper = { Items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ] }

                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"

                let serialize (options: System.Text.Json.JsonSerializerOptions) (value: Item list) = System.Text.Json.JsonSerializer.Serialize(value, options)
                let json = serialize (System.Text.Json.JsonSerializerOptions()) wrapper.Items
                """
        )
    )

[<Fact>]
let ``a guarded catch-all is not dead: the rule stands down`` () =
    // `| v when v.Length = 4` takes "POST" before its own arm does; deleting
    // it as a dead catch-all would turn `route "POST"` from "four" into "write"
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let route (verb: string) =
                    match verb with
                    | v when v.Length = 4 -> "four"
                    | "GET" -> "read"
                    | "POST" -> "write"
                    | _ -> failwith "unsupported"
                let a = route "GET"
                let b = route "POST"
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let debug = true
                let route (verb: string) =
                    match verb with
                    | _ when debug -> "trace"
                    | "GET" -> "read"
                    | "POST" -> "write"
                    | _ -> failwith "unsupported"
                let a = route "GET"
                let b = route "POST"
                """
        )
    )

[<Fact>]
let ``an unguarded null arm is dead like the wildcard and goes with it`` () =
    // every source is a literal, so null never arrives: the arm is deleted
    // as a catch-all (a union has no null arm to keep, FS0043)
    assertRewrite
        (fsharp
            """
            module T
            let describe (region: string) =
                match region with
                | null -> "none"
                | "eu" -> "Europe"
                | "uk" -> "Britain"
                | _ -> failwith "?"
            let a = describe "eu"
            let b = describe "uk"
            """)
        (fsharp
            """
            module T
            [<RequireQualifiedAccess>]
            type Region =
                | Eu
                | Uk

                override this.ToString() =
                    match this with
                    | Region.Eu -> "eu"
                    | Region.Uk -> "uk"

            let describe (region: Region) =
                match region with
                | Region.Eu -> "Europe"
                | Region.Uk -> "Britain"
            let a = describe Region.Eu
            let b = describe Region.Uk
            """)
    |> ignore

[<Fact>]
let ``a guarded null arm stays open and the rule stands down`` () =
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let debug = true
                let describe (region: string) =
                    match region with
                    | null when debug -> "none"
                    | "eu" -> "Europe"
                    | "uk" -> "Britain"
                    | _ -> failwith "?"
                let a = describe "eu"
                let b = describe "uk"
                """
        )
    )

[<Fact>]
let ``a constant is resolved by its declaration, not by its name`` () =
    // `Overrides.kind` is "dir"; the file's own `kind` is "file". Read by
    // name, both were "file" and `weight Overrides.kind` became the File case
    // name. Both constants name their case `Kind`, so the cases fall back to
    // the texts; the nested module's constant is not in reach by its bare
    // name where the union sits, so its ToString arm keeps the literal
    assertRewrite
        (fsharp
            """
            module T
            let kind = "file"
            module Overrides =
                let kind = "dir"
            let weight (kind: string) =
                match kind with
                | "file" -> 1
                | "dir" -> 0
                | _ -> failwith "?"
            let a = weight Overrides.kind
            let b = weight kind
            """)
        (fsharp
            """
            module T
            let kind = "file"
            module Overrides =
                let kind = "dir"
            [<RequireQualifiedAccess>]
            type Kind =
                | ``File``
                | ``Dir``

                override this.ToString() =
                    match this with
                    | Kind.``File`` -> kind
                    | Kind.``Dir`` -> "dir"

            let weight (kind: Kind) =
                match kind with
                | Kind.``File`` -> 1
                | Kind.``Dir`` -> 0
            let a = weight Kind.``Dir``
            let b = weight Kind.``File``
            """)
    |> ignore

[<Fact>]
let ``a field read through a DotGet off a call is an unknown use and stands down`` () =
    // `(mk b).Kind` resolves to a range no expression node matches: an
    // unmatched read is unsafe, never "no sink"
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                type Item = { Kind: string; Size: int }
                let mk (b: bool) = if b then { Kind = "file"; Size = 1 } else { Kind = "dir"; Size = 0 }
                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"
                let up = (mk true).Kind.ToUpper()
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                type Item = { Kind: string; Size: int }
                let mk (b: bool) = if b then { Kind = "file"; Size = 1 } else { Kind = "dir"; Size = 0 }
                let weight (i: Item) =
                    match i.Kind with
                    | "file" -> i.Size
                    | "dir" -> 0
                    | _ -> failwith "?"
                let shown = sprintf "%A" (mk true).Kind
                """
        )
    )

[<Fact>]
let ``literals that make no valid case name stand down`` () =
    // ``1.0`` and ``1/2`` are not union case names (FS0883)
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let f (v: string) =
                    match v with
                    | "1.0" -> 1
                    | "2.0" -> 2
                    | _ -> failwith "?"
                let a = f "1.0"
                let b = f "2.0"
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let f (v: string) =
                    match v with
                    | "1/2" -> 1
                    | "1/4" -> 2
                    | _ -> failwith "?"
                let a = f "1/2"
                let b = f "1/4"
                """
        )
    )

[<Fact>]
let ``case names clashing with generated members stand down`` () =
    // `IsEu` from "is-eu" clashes with case Eu's generated tester, and a
    // `ToString` case with the override (FS0023)
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let f (v: string) =
                    match v with
                    | "eu" -> 1
                    | "is-eu" -> 2
                    | _ -> failwith "?"
                let a = f "eu"
                let b = f "is-eu"
                """
        )
    )

    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let f (v: string) =
                    match v with
                    | "to-string" -> 1
                    | "other" -> 2
                    | _ -> failwith "?"
                let a = f "to-string"
                let b = f "other"
                """
        )
    )

[<Fact>]
let ``a null nested in an option pattern goes like a top-level one`` () =
    // `| Some null -> 3` cannot match a union (FS0043): every literal has
    // its arm, so it is dead and goes like `Some _` would; the wildcard
    // stays for None
    let source =
        fsharp
            """
            module T
            let family (n: int) =
                if n = 1 then Some "MEL"
                elif n = 2 then Some "Serilog"
                else None
            let f (n: int) =
                match family n with
                | Some null -> 3
                | Some "MEL" -> 1
                | Some "Serilog" -> 2
                | _ -> 0
            """

    match findIn source with
    | [ s ] ->
        let patched = applyEdits source s.Edits
        Assert.DoesNotContain("null", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d" other.Length

    // a literal no arm names leaves `Some null` live: no spelling on the union
    Assert.Empty(
        findIn (
            fsharp
                """
                module T
                let family (n: int) =
                    if n = 1 then Some "MEL"
                    elif n = 2 then Some "Serilog"
                    elif n = 3 then Some "NLog"
                    else None
                let f (n: int) =
                    match family n with
                    | Some null -> 3
                    | Some "MEL" -> 1
                    | Some "Serilog" -> 2
                    | _ -> 0
                """
        )
    )

[<Fact>]
let ``a record printed whole or compared keeps its string field`` () =
    // retyping the field changes `%A`/`string r` output and the record's
    // structural order (cases compare by declaration, not by text)
    let prefix =
        fsharp
            """
            module T
            type Item = { Kind: string; Size: int }
            let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]
            let weight (i: Item) =
                match i.Kind with
                | "file" -> i.Size
                | "dir" -> 0
                | _ -> failwith "?"

            """

    for tail in
        [
            """let shown = sprintf "%A" (List.head items)"""
            "let shown = string (List.head items)"
            "let shown = $\"{List.head items}\""
            "let sorted = List.sort items"
            "let c = compare items.[0] items.[1]"
            "let m = items |> List.map (fun i -> i, 1) |> Map.ofList"
            "let s = Set.ofList items"
            "let b = items.[0] < items.[1]"
        ] do
        Assert.True(List.isEmpty (findIn (prefix + tail)), tail)

[<Fact>]
let ``a record field's rewrite is offered by the editor alone`` () =
    // the record's printed text and order change with the field, and a
    // generic helper doing either is out of the scan's sight: a sweep
    // reports the set without a fix
    let source =
        fsharp
            """
            type Item = { Kind: string; Size: int }

            let items = [ { Kind = "file"; Size = 1 }; { Kind = "dir"; Size = 0 } ]

            let weight (i: Item) =
                match i.Kind with
                | "file" -> i.Size
                | "dir" -> 0
                | _ -> failwith "?"
            """

    let tree, sourceText, check = parseAndCheck source
    let world = worldOf check sourceText tree
    Assert.True((StringUnion.find world tree sourceText |> List.exactlyOne).FieldSlot)

    match FSharp.Refactor.Analyzers.stringUnionMessagesIn false world tree sourceText with
    | [ m ] ->
        Assert.Empty m.Fixes
        Assert.Contains("the editor offers the rewrite", m.Message)
    | other -> failwithf "Expected one message, got %d" other.Length

    match FSharp.Refactor.Analyzers.stringUnionMessagesIn true world tree sourceText with
    | [ m ] -> Assert.NotEmpty m.Fixes
    | other -> failwithf "Expected one message, got %d" other.Length

    // a parameter slot alone is no field slot: the sweep applies it
    let source =
        fsharp
            """
            let f (mode: string) =
                match mode with
                | "on" -> 1
                | "off" -> 0
                | _ -> -1

            let x = f "on" + f "off"
            """

    let tree, sourceText, check = parseAndCheck source
    let world = worldOf check sourceText tree

    match FSharp.Refactor.Analyzers.stringUnionMessagesIn false world tree sourceText with
    | [ m ] -> Assert.NotEmpty m.Fixes
    | other -> failwithf "Expected one message, got %d" other.Length
