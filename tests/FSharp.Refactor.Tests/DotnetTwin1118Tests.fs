/// The F# twins of the wrong fixes the 2026-11-18 csharp-refactor sweep of
/// dotnet/aspnetcore found (CSharp.Refactor DotnetSweep1118Tests.fs). A twin
/// rule that shares the defect asserts the behaviour it should have; one that
/// already guards the shape pins the guard.
module FSharp.Refactor.Tests.DotnetTwin1118Tests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private lineOf (source: string) (needle: string) =
    (source.Replace("\r\n", "\n").Split('\n')
     |> Array.findIndex (fun l -> l.Contains needle))
    + 1

// ---- FR0100 (CR0012) ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0100 leaves an arm commented unsupported that returns the function's no-result`` () =
    // twin of CR0012 leaves a default arm that returns the method's own no-result for unknown input
    let source =
        fsharp
            """
            module Test
            let httpMethods (name: string) =
                match name with
                | "MapGet" -> Some [ "GET" ]
                | "MapPost" -> Some [ "POST" ]
                | "Map" -> Some []
                | _ ->
                    // Unknown/unsupported method.
                    None
            """

    let tree, sourceText = parse source
    Assert.Empty(UnimplementedBranch.find tree sourceText)
    // the control: a temporary marker makes the same arm unfinished
    let marked =
        source.Replace("// Unknown/unsupported method.", "// not supported yet")

    let tree, sourceText = parse marked
    Assert.Single(UnimplementedBranch.find tree sourceText) |> ignore

// ---- FR0164 (CR0171) ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0164 leaves an edit whose statements end in raise and still reports one that loops on`` () =
    // twin of CR0171 leaves a mutation whose block ends in break: the edit, a second edit, then the exit
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            exception Replaced of string
            let set (tags: List<KeyValuePair<string, obj>>) (name: string) (value: obj) =
                for tag in tags do
                    if tag.Key = name then
                        tags.Remove tag |> ignore
                        tags.Add(KeyValuePair(name, value))
                        raise (Replaced name)
            let drop (others: List<KeyValuePair<string, obj>>) (name: string) =
                for other in others do
                    if other.Key = name then
                        others.Add(KeyValuePair(name, null))
            """

    let tree, sourceText, check = parseAndCheck source

    Assert.Equal<string list>(
        [ "others" ],
        EnumerationMutation.find tree sourceText check
        |> List.map (fun s -> s.Collection)
    )

// ---- FR0119 (CR0042) ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0119 leaves a sync call made beside its async twin on the same receiver`` () =
    // twin of CR0042 leaves a sync call a test makes beside its async twin on the same receiver
    let source =
        fsharp
            """
            module Test
            open System.IO
            open System.Text
            open System.Threading.Tasks
            type ViewWriter() =
                inherit TextWriter()
                member val Count = 0 with get, set
                override _.Encoding = Encoding.UTF8
                override x.Write(value: char) = x.Count <- x.Count + 1
            let writesBothWays () : Task<bool> = task {
                let writer = new ViewWriter()
                writer.WriteLine()
                do! writer.WriteLineAsync()
                return writer.Count > 0
            }
            let other () : Task<bool> = task {
                let other = new ViewWriter()
                other.WriteLine()
                do! Task.Yield()
                return other.Count > 0
            }
            """

    let tree, sourceText, check = parseAndCheck source

    Assert.Equal<int list>(
        [ lineOf source "other.WriteLine()" ],
        AwaitableOverload.find tree sourceText check
        |> List.map (fun s -> s.Range.StartLine)
    )

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0119 leaves a StreamWriter over a MemoryStream`` () =
    // twin of CR0042 leaves a StreamWriter over a MemoryStream (FR0049's onMemoryStream gate)
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            open System.Threading.Tasks
            let writeMessages (messages: string list) (append: ArraySegment<byte> -> Task) : Task = task {
                use stream = new MemoryStream()
                use writer = new StreamWriter(stream)
                for message in messages do
                    writer.Write(message)
                writer.Flush()
                let ok, buffer = stream.TryGetBuffer()
                if ok then do! append buffer
            }
            """

    let tree, sourceText, check = parseAndCheck source
    Assert.Empty(AwaitableOverload.find tree sourceText check)

// ---- FR0075 (CR0060) ----

let private useFixes (source: string) =
    let tree, sourceText, check = parseAndCheck source

    UseBinding.find tree sourceText check
    |> List.filter (fun s -> s.Fix.IsSome)
    |> List.map (fun s -> s.Name)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0075 never disposes a writer whose stream the function returns`` () =
    // twin of CR0060 never disposes a writer whose stream the method returns
    let source =
        fsharp
            """
            module Test
            open System.IO
            let downloadFromStream () : Stream =
                let stream = new MemoryStream()
                let writer = new StreamWriter(stream)
                writer.Write("This is sample text from a stream")
                writer.Flush()
                stream.Seek(0L, SeekOrigin.Begin) |> ignore
                stream :> Stream
            """

    Assert.Empty(useFixes source)
    // the control: the stream kept local, both stay undisposed and the writer gets its `use`
    let kept =
        source.Replace("stream :> Stream", "stream.Length").Replace(": Stream =", "=")

    Assert.Contains("writer", useFixes kept)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0075 never disposes a pooled builder whose segment is stored`` () =
    // twin of CR0060 never disposes a pooled builder whose segment is stored
    let source =
        fsharp
            """
            module Test
            open System
            open System.Buffers
            open System.Collections.Generic
            type ArrayBuilder<'T>() =
                let items = ArrayPool<'T>.Shared.Rent 16
                let mutable count = 0
                member _.Append(source: 'T[], start: int, length: int) =
                    Array.Copy(source, start, items, count, length)
                    count <- count + length
                member _.ToSegment(from: int, upTo: int) = ArraySegment<'T>(items, from, upTo - from)
                interface IDisposable with
                    member _.Dispose() = ArrayPool<'T>.Shared.Return items
            type CapturedBatch() =
                member val Diffs = List<ArraySegment<int>>()
                member x.AddDiff(edits: int[]) =
                    let cloneBuilder = new ArrayBuilder<int>()
                    cloneBuilder.Append(edits, 0, edits.Length)
                    x.Diffs.Add(cloneBuilder.ToSegment(0, edits.Length))
            """

    Assert.Empty(useFixes source)
    // the control: nothing taken out of it, the builder does get its `use`
    let dropped =
        source.Replace("x.Diffs.Add(cloneBuilder.ToSegment(0, edits.Length))", "cloneBuilder.Append(edits, 0, 0)")

    Assert.Contains("cloneBuilder", useFixes dropped)

// ---- FR0070 (CR0081) ----

let private structFixes (source: string) =
    let tree, sourceText, check = parseAndCheck source
    let _, structs, _ = StructHints.findWith (Some check) false tree sourceText
    structs |> List.filter (fun s -> s.Fix.IsSome) |> List.map (fun s -> s.TypeName)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0070 leaves a record passed where obj is taken`` () =
    // twin of CR0081 leaves a record passed where object is taken
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            type ValidationStack() =
                let seen = HashSet<obj>(ReferenceEqualityComparer.Instance)
                member _.Push(model: obj) = seen.Add model
                member _.Pop(model: obj) = seen.Remove model |> ignore
                member _.Count = seen.Count
            type internal Model = { Position: int }
            let internal run (stack: ValidationStack) =
                let models = [ { Position = 1 }; { Position = 2 } ]
                for model in models do stack.Push model |> ignore
                for model in models do stack.Pop model
                stack.Count
            """

    Assert.Empty(structFixes source)
    // the control: never handed to obj, the record does take [<Struct>]
    let unboxed =
        source
            .Replace("stack.Push model |> ignore", "ignore model.Position")
            .Replace("stack.Pop model", "ignore model.Position")

    Assert.Equal<string list>([ "Model" ], structFixes unboxed)

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0070 leaves a record whose Type is handed to reflection`` () =
    // twin of CR0081 leaves a record whose Type is handed to reflection
    let source =
        fsharp
            """
            module Test
            open System
            type internal RecordClassParameterizedConstructor = { Foo: int }
            let hasConstructor (t: Type) = t.GetConstructors().Length > 0 && not t.IsValueType
            let internal probe () = hasConstructor typeof<RecordClassParameterizedConstructor>
            """

    Assert.Empty(structFixes source)

// ---- FR0101 (CR0015) ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0101 leaves an indexed loop over an interface-typed list and still converts an array`` () =
    // twin of CR0015 leaves an indexed loop over an interface-typed list and still converts an array
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let count (endpoints: IReadOnlyList<string>) =
                let mutable n = 0
                for i in 0 .. endpoints.Count - 1 do
                    if endpoints.[i].Length > 0 then n <- n + 1
                n
            let sum (xs: int[]) =
                let mutable n = 0
                for i in 0 .. xs.Length - 1 do
                    n <- n + xs.[i]
                n
            """

    let tree, sourceText, check = parseAndCheck source

    Assert.Equal<string list>(
        [ "xs" ],
        IndexedLoop.findChecked tree sourceText IndexedLoop.SourceGate.Any check
        |> List.map (fun s -> s.CollectionText)
    )

// ---- FR0071 (CR0177) ----

[<Fact; Trait("Category", "Sweep1118")>]
let ``FR0071 leaves a zeroed local whose address the loop hands out`` () =
    // twin of CR0177 leaves a zeroed local whose address the loop hands out
    let source =
        fsharp
            """
            module Test
            #nowarn "9"
            open Microsoft.FSharp.NativeInterop
            type Native =
                static member Receive(bytes: nativeptr<uint32>, fill: bool) =
                    if fill then NativePtr.write bytes 42u
                    if fill then 234u else 997u
                static member Fill(b: byref<uint32>) = b <- b + 42u
            let load () =
                let mutable retry = true
                let mutable last = 0u
                while retry do
                    retry <- false
                    let mutable bytesReceived = 0u
                    let status = Native.Receive(&&bytesReceived, (last = 0u))
                    if status = 234u then retry <- true
                    last <- bytesReceived
                last
            let loadByref () =
                let mutable retry = true
                let mutable last = 0u
                while retry do
                    retry <- false
                    let mutable bytesReceived = 0u
                    Native.Fill &bytesReceived
                    last <- last + bytesReceived
                    retry <- last < 100u
                last
            """

    let tree, sourceText, check = parseAndCheck source

    Assert.Empty(
        LoopInvariant.find tree sourceText check
        |> List.filter (fun s -> not s.Edits.IsEmpty)
    )
