/// Wrong fixes the 2026-11-18 dotnet-fsharp sweep (fsharp-refactor 0.8.57,
/// FSharp.slnx) rolled back or put back. Each test asserts the correct
/// behaviour, so it fails until the rule or the tool is fixed. The sweep is
/// not re-run: these snippets are the regression check.
module FSharp.Refactor.Tests.DotnetSweep1118Tests

open System
open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0139 SeqOnArray: the collection of a piped Seq.fold is the pipe's left side ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0139 reads the piped collection, not the array state of Seq.fold`` () =
    // src/Compiler/Facilities/Hashing.fs:68 `items |> Seq.fold (fun s a -> addItem a s) s`
    let source =
        fsharp
            """
            module Test
            let addSeq<'item> (items: 'item seq) (addItem: 'item -> byte array -> byte array) (s: byte array) =
                items |> Seq.fold (fun s a -> addItem a s) s
            """

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(SeqOnArray.find tree sourceText checkResults)

// ---- FR0042 SprintfInterpolation: a call of several typed holes converts, and the tool keeps it ----

// FCS 43.13.404's per-file check rejects a typed interpolated string of two
// or more holes when one of them is not %s/%d/%i/%c/%M (FS0001); its project
// check, its background check and fsc accept it. The sweep rolled every such
// FR0042 fix back in a file with a signature, and the file's other fixes
// with it. The defect is the verification's, so it is fixed there
// (AuditDriverTests: `a pass that writes a typed interpolated string of
// several holes into a signed file is no error`) and the rule converts these.
let private interpolated (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source

    SprintfInterpolation.find tree sourceText checkResults
    |> List.map (fun s -> s.ReplacementText)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0042 still converts a call whose holes the typechecker accepts`` () =
    let source =
        fsharp
            """
            module Test
            let describe (name: string) (count: int) (single: float) =
                let a = sprintf "%s: %d" name count
                let b = sprintf "%.2f" single
                a + b
            """

    let tree, sourceText, checkResults = parseAndCheck source
    let suggestions = SprintfInterpolation.find tree sourceText checkResults
    Assert.Equal(2, suggestions.Length)

    for s in suggestions do
        assertTypechecks "Patched source" (applyEdit source s.Range s.ReplacementText)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0042 converts a call of two %u holes`` () =
    // src/Compiler/AbstractIL/il.fs:382 `sprintf "ILVersionInfo: %u %u %u %u" x.Major ...`
    let source =
        fsharp
            """
            module Test
            type V =
                { Major: uint16; Minor: uint16 }
                override x.ToString() =
                    sprintf "ILVersionInfo: %u %u" x.Major x.Minor
            """

    Assert.Equal<string list>([ "$\"ILVersionInfo: %u{x.Major} %u{x.Minor}\"" ], interpolated source)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0042 converts a call of two %A holes`` () =
    // src/Compiler/Utilities/rational.fs:61 `sprintf "(%A/%A)" m.numerator m.denominator`
    let source =
        fsharp
            """
            module Test
            let toS (n: bigint) (d: bigint) =
                if d = 1I then n.ToString() else sprintf "(%A/%A)" n d
            """

    Assert.Equal<string list>([ "$\"(%A{n}/%A{d})\"" ], interpolated source)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0042 converts a call of %+A beside %s`` () =
    // src/Compiler/TypedTree/TypedTree.fs:5619 `sprintf "%+A(%s)" op vref.LogicalName`
    let source =
        fsharp
            """
            module Test
            type Op = | Get | Set
            let describe (op: Op) (name: string) = sprintf "%+A(%s)" op name
            """

    Assert.Equal<string list>([ "$\"%+A{op}(%s{name})\"" ], interpolated source)

// ---- FR0140 ObjectInitializer: `let x = C() in x.P <- v; body` keeps its `in` ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0140 folding a one-line let-in keeps the in`` () =
    // tests/service/data/TestTP/TestTP.fs:276 `<@@ let x = Helper.C() in x.Property <- 1; x.Property @@>`
    let source =
        fsharp
            """
            module Test
            type C() =
                member val Property = 0 with get, set
            let r () = let x = C() in x.Property <- 1; x.Property
            let q = <@@ let x = C() in x.Property <- 1; x.Property @@>
            """

    let tree, sourceText, checkResults = parseAndCheck source

    for s in ObjectInitializer.find tree sourceText checkResults do
        assertTypechecks "Patched source" (applyEdit source s.Range s.ReplacementText)

// ---- FR0007 MutableRemoval: an address taken with & is a mutation, primed names too ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0007 keeps mutable on a primed name whose address is taken`` () =
    // tests/FSharp.Compiler.ComponentTests/CompilerService/Caches.fs:238 `cache.TryGetValue(t1, &v1')`
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let f (d: Dictionary<int, int>) =
                let mutable v1' = 0
                let mutable v2 = 0
                d.TryGetValue(1, &v1') |> ignore
                d.TryGetValue(2, &v2) |> ignore
                v1' + v2
            """

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(MutableRemoval.find tree sourceText checkResults |> List.map (fun s -> s.Name))

// the same `\bname\b` read of a primed name, in the other rules that ask
// "does this text mention the name": `\be'\b` never matches `e'`

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0009 keeps a primed error variable its default reads`` () =
    let source =
        fsharp
            """
            module Test
            let orItself (r: Result<string, string>) =
                match r with
                | Ok v -> v
                | Error e' -> e'
            """

    let tree, sourceText, checkResults = parseAndCheck source

    for s in ResultModule.find tree sourceText checkResults do
        assertTypechecks "Patched source" (applyEdit source s.Range s.ReplacementText)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0030 keeps a loop whose receiver reads the primed loop variable`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let fill (columns: List<int>[]) (tiles: int list) =
                for tile' in tiles do
                    columns.[tile' % 2].Add tile'
            """

    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(AddRange.find tree sourceText checkResults)

// ---- tool: an api migration waits while a call site sits in a framework #if branch ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``a call site inside an #if NETCOREAPP branch holds the api migration back`` () =
    // tests/FSharp.Compiler.Service.Tests/ProjectAnalysisTests.fs:4697: the net472 pass reshaped
    // `mkProjectCommandLineArgs` (FR0090) and missed this call; the all-framework build put back 63 files
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", "sweep1118-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore
    let file = Path.Combine(dir, "ProjectAnalysisTests.fs")

    File.WriteAllText(
        file,
        fsharp
            """
            module ProjectAnalysisTests
            let test (dllPath: string) (fileNames: string[]) =
            #if NETCOREAPP
                let args = mkProjectCommandLineArgs(dllPath, fileNames)
                args
            #else
                [||]
            #endif
            """
    )

    Assert.True(Text.namedInDirectiveRegion [ file ] "mkProjectCommandLineArgs")

// ---- FR0142 TestReturnsTask: `task` must be FSharp.Core's builder where the test sits ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0142 leaves a test in a file that shadows task with a non-builder`` () =
    // tests/FSharp.Core.UnitTests/.../TasksDynamic.fs:163 `let task = Do_no_use_task_in_this_file_use_taskDynamic_instead.Nope`
    // FR0142 rewrote 26 tests to `task { … }`: "builder defines no 'Bind' method", rolled back in every framework
    let scaffold (shadow: string) =
        "module Xunit\nopen System\nopen System.Threading.Tasks\ntype FactAttribute() =\n    inherit Attribute()\n"
        + "type Nope = Nope\n"
        + shadow
        + "let fetch () = Task.FromResult 2\n"

    let test =
        fsharp
            """
            [<Fact>]
            let ``fetches`` () =
                let res = (fetch ()).Result
                if res <> 2 then failwith "wrong"
            """

    let findIn (source: string) =
        let tree, sourceText, checkResults = parseAndCheck source
        TestReturnsTask.find tree sourceText checkResults

    // control: with FSharp.Core's `task` in scope the test is converted
    Assert.Single(findIn (scaffold "" + test)) |> ignore
    Assert.Empty(findIn (scaffold "let task = Nope\n" + test))

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0142 leaves a test where a module of another file binds task`` () =
    // the same shadow, declared in a file above and opened here: this file's own declarations do not show it
    let shadows =
        "namespace Shadows\n[<AutoOpen>]\nmodule Builders =\n    type Nope = Nope\n    let task = Nope\n"

    let tests (opens: string) =
        "module Xunit\nopen System\nopen System.Threading.Tasks\n"
        + opens
        + "type FactAttribute() =\n    inherit Attribute()\n"
        + "let fetch () = Task.FromResult 2\n"
        + "[<Fact>]\nlet ``fetches`` () =\n    let res = (fetch ()).Result\n    if res <> 2 then failwith \"wrong\"\n"

    let findIn (source: string) =
        let tree, sourceText, checkResults = parseAndCheckSecond shadows source
        TestReturnsTask.find tree sourceText checkResults

    Assert.Single(findIn (tests "")) |> ignore
    Assert.Empty(findIn (tests "open Shadows\n"))
