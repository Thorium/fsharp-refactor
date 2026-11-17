/// The F# twins of the defects a 2026-11-16 sweep of ten public C#
/// repositories found in CSharp.Refactor (fixed there as 0.1.28).
module FSharp.Refactor.Tests.CorpusTwinTests

open System
open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private applyAll (source: string) (fixes: (FSharp.Compiler.Text.range * string * string) list) =
    fixes
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

// ---- FR0119 ----

let private awaitableIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AwaitableOverload.find tree sourceText checkResults

[<Fact>]
let ``FR0119 leaves in-memory writers, the console and a member named for its sync work`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            let memory (w: StringWriter) (s: string) = task {
                w.Write(s)
                Console.Out.WriteLine(s)
                return ()
            }
            let writeTokenSyncReadingAsync (reader: TextReader) = task {
                let line = reader.ReadLine()
                return line
            }
            let head (reader: TextReader) = task {
                let line = reader.ReadLine()
                return line
            }
            """

    match awaitableIn source with
    | [ s ] -> Assert.Equal(14, s.Range.StartLine)
    | other -> failwithf "Expected the one ReadLine in head, got %A" other

[<Fact>]
let ``FR0119 binds with ConfigureAwait where the task body's own binds all do, bare otherwise`` () =
    let source =
        fsharp
            """
            module Test
            open System.IO
            open System.Threading.Tasks
            let configured (reader: TextReader) = task {
                do! Task.Delay(1).ConfigureAwait(false)
                let line = reader.ReadLine()
                return line
            }
            let bare (reader: TextReader) = task {
                do! Task.Delay(1)
                let line = reader.ReadLine()
                return line
            }
            """

    let fixedSource =
        awaitableIn source |> List.collect (fun s -> s.Fixes) |> applyAll source

    Assert.Contains("let! line = reader.ReadLineAsync().ConfigureAwait(false)", fixedSource)
    Assert.Contains("do! Task.Delay(1)\n    let! line = reader.ReadLineAsync()\n", fixedSource.Replace("\r\n", "\n"))
    assertTypechecks "FR0119 ConfigureAwait" fixedSource

// ---- FR0049 ----

let private blockingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SyncOverAsync.find tree sourceText checkResults

[<Fact>]
let ``FR0049 binds a Task with ConfigureAwait where the body's own binds all do`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let total (t: Task<int>) = task {
                do! Task.Delay(1).ConfigureAwait(false)
                let r = t.Result
                return r + 1
            }
            """

    let fixedSource =
        blockingIn source |> List.collect (fun s -> s.Fixes) |> applyAll source

    Assert.Contains("let! r = t.ConfigureAwait(false)", fixedSource)
    assertTypechecks "FR0049 ConfigureAwait" fixedSource

// ---- FR0075 ----

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

[<Fact>]
let ``FR0075 leaves an object built with a null argument`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            type Connection(socket: Stream) =
                member _.Peek() = 1
                interface IDisposable with
                    member _.Dispose() = socket.Dispose()
            let probe () =
                let con = new Connection(null)
                con.Peek()
            let probe2 () =
                let con = new Connection(Unchecked.defaultof<Stream>)
                con.Peek()
            let real (path: string) =
                let con = new Connection(File.OpenRead path)
                con.Peek()
            """

    let names =
        useBindingsIn source
        |> List.filter (fun s -> s.Fix.IsSome)
        |> List.map (fun s -> s.Range.StartLine)

    Assert.Equal<int list>([ 15 ], names)

// ---- FR0160 ----

let private lostInnerIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    LostInnerException.find tree sourceText checkResults

[<Fact>]
let ``FR0160 stays a note where the try adds HTTP headers`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.Net.Http
            type ApiException(message: string, inner: exn) =
                inherit Exception(message, inner)
                new(message: string) = ApiException(message, null)
            let add (client: HttpClient) (key: string) =
                try
                    client.DefaultRequestHeaders.Add("X-Api-Key", key)
                with ex ->
                    raise (ApiException("bad header"))
            let parse (text: string) =
                try
                    int text
                with ex ->
                    raise (ApiException("bad number"))
            """

    let found = lostInnerIn source
    Assert.Equal(2, found.Length)
    Assert.Contains(found, fun s -> s.HeaderValues && s.Edits.IsEmpty)
    Assert.Contains(found, fun s -> not s.HeaderValues && not s.Edits.IsEmpty)

// ---- FR0007 ----

let private mutablesIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    MutableRemoval.find tree sourceText check

[<Fact>]
let ``FR0007 keeps mutable on a local an inactive #if branch writes`` () =
    let source =
        fsharp
            """
            module Test
            let ignored (probe: unit -> bool) =
                let mutable hasIgnore = false
            #if HAVE_IGNORE
                hasIgnore <- probe ()
            #endif
                hasIgnore
            let plain () =
                let mutable width = 2
                width + 1
            """

    match mutablesIn source with
    | [ s ] -> Assert.Equal("width", s.Name)
    | other -> failwithf "Expected only 'width', got %A" other

// ---- FR0124 ----

let private serilogScaffold =
    "namespace Serilog\n"
    + "type ILogger =\n"
    + "    abstract Information: messageTemplate: string * [<System.ParamArray>] propertyValues: obj[] -> unit\n"
    + "namespace Test\n"
    + "open Serilog\n"

let private melScaffold =
    "namespace Microsoft.Extensions.Logging\n"
    + "type ILogger = interface end\n"
    + "[<System.Runtime.CompilerServices.Extension>]\n"
    + "type LoggerExtensions =\n"
    + "    [<System.Runtime.CompilerServices.Extension>]\n"
    + "    static member LogError(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) = ignore (logger, message, args)\n"
    + "namespace Test\n"
    + "open Microsoft.Extensions.Logging\n"

let private templatesIn (scaffold: string) (source: string) =
    let tree, sourceText, checkResults = parseAndCheck (scaffold + source)
    LogTemplates.find tree sourceText checkResults

[<Fact>]
let ``FR0124 lets Serilog read a repeated positional placeholder once`` () =
    let source =
        fsharp
            """
            module M =
                let go (log: ILogger) (n: int) =
                    log.Information("{0} and again {0}", n)
            """

    Assert.Empty(templatesIn serilogScaffold source)

[<Fact>]
let ``FR0124 counts every hole for Microsoft.Extensions.Logging before naming a duplicate`` () =
    let source =
        fsharp
            """
            module M =
                let go (logger: ILogger) (n: int) =
                    logger.LogError("{0} and {0}", n)
            """

    match templatesIn melScaffold source with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.CountMismatch(2, 1), s.Problem)
    | other -> failwithf "Expected one count mismatch, got %A" other

// ---- the tool ----

[<Fact>]
let ``frameworks rank by API surface: net20 below net462 below net47, netstandard below its first .NET Framework`` () =
    let order =
        [
            "net10.0"
            "net47"
            "netstandard2.0"
            "net462"
            "net20"
            "netcoreapp3.1"
            "net461"
            "net46"
            "net35"
            "netstandard2.1"
        ]
        |> List.sortBy FSharp.Refactor.Tool.Program.tfmRank

    Assert.Equal<string list>(
        [
            "net20"
            "net35"
            "net46"
            "netstandard2.0"
            "net461"
            "net462"
            "net47"
            "netstandard2.1"
            "netcoreapp3.1"
            "net10.0"
        ],
        order
    )

    Assert.True(FSharp.Refactor.Tool.Program.tfmRank "netstandard1.0" < FSharp.Refactor.Tool.Program.tfmRank "net45")

[<Fact>]
let ``a solution without Any CPU builds for x64, or its first platform, never Mixed Platforms`` () =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let write name (text: string) =
            let path = Path.Combine(dir, name)
            File.WriteAllText(path, text)
            path

        let platformOf = FSharp.Refactor.Tool.Program.solutionPlatform

        Assert.Equal(
            Some "x64",
            platformOf (
                write
                    "Files.slnx"
                    """<Solution><Configurations><Platform Name="arm64" /><Platform Name="x64" /></Configurations></Solution>"""
            )
        )

        Assert.Equal(
            None,
            platformOf (
                write
                    "Lib.sln"
                    "Global\n\tGlobalSection(SolutionConfigurationPlatforms) = preSolution\n\t\tDebug|Any CPU = Debug|Any CPU\n\tEndGlobalSection\nEndGlobal\n"
            )
        )

        Assert.Equal(
            Some "x86",
            platformOf (
                write
                    "Old.sln"
                    "Global\n\tGlobalSection(SolutionConfigurationPlatforms) = preSolution\n\t\tDebug|Mixed Platforms = Debug|Mixed Platforms\n\t\tDebug|x86 = Debug|x86\n\tEndGlobalSection\nEndGlobal\n"
            )
        )
    finally
        Directory.Delete(dir, true)

// ---- found by the regression review of 0.8.55 ----

[<Fact>]
let ``FR0049 adds no second ConfigureAwait, and configures the Delay it writes`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let total (t: Task<int>) = task {
                do! Task.Delay(1).ConfigureAwait(false)
                let r = t.ConfigureAwait(false).GetAwaiter().GetResult()
                let s = t.GetAwaiter().GetResult()
                Thread.Sleep 5
                return r + s
            }
            """

    let fixedSource =
        (blockingIn source |> List.collect (fun s -> s.Fixes) |> applyAll source).Replace("\r\n", "\n")

    Assert.Contains("let! r = t.ConfigureAwait(false)\n", fixedSource)
    Assert.Contains("let! s = t.ConfigureAwait(false)\n", fixedSource)
    Assert.Contains("do! (System.Threading.Tasks.Task.Delay 5).ConfigureAwait(false)\n", fixedSource)
    assertTypechecks "FR0049 awaiters" fixedSource

[<Fact>]
let ``FR0119 reads the receiver's own type, and Sync as a noun is no sync work`` () =
    let source =
        fsharp
            """
            module Test
            open System.IO
            let memory (w: StringWriter) (s: string) = task {
                w.WriteLine(s)
                return ()
            }
            let runSyncJobAsync (reader: TextReader) = task {
                let line = reader.ReadLine()
                return line
            }
            """

    match awaitableIn source with
    | [ s ] -> Assert.Equal(8, s.Range.StartLine)
    | other -> failwithf "Expected the one ReadLine in runSyncJobAsync, got %A" other

[<Fact>]
let ``FR0075 takes a package's assembly for someone else's type`` () =
    Assert.True(UseBinding.packagePath @"C:\Users\me\.nuget\packages\npgsql\8.0.0\lib\net8.0\Npgsql.dll")
    Assert.True(UseBinding.packagePath "/src/app/packages/Npgsql/lib/net8.0/Npgsql.dll")
    Assert.True(UseBinding.packagePath "/usr/share/dotnet/packs/Microsoft.AspNetCore.App.Ref/8.0.0/ref/net8.0/A.dll")
    Assert.False(UseBinding.packagePath @"C:\git\App\src\Core\bin\Debug\net8.0\Core.dll")

[<Fact>]
let ``FR0075 leaves a null-built object however the null and the type are spelled`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            type Connection(socket: Stream) =
                member _.Peek() = 1
                interface IDisposable with
                    member _.Dispose() = socket.Dispose()
            type Box<'T>(socket: Stream) =
                member _.Peek() = 1
                interface IDisposable with
                    member _.Dispose() = socket.Dispose()
            let named () =
                let con = new Connection(socket = null)
                con.Peek()
            let generic () =
                let box = new Box<int>(Unchecked.defaultof<_>)
                box.Peek()
            let real (path: string) =
                let con = new Connection(File.OpenRead path)
                con.Peek()
            """

    let lines =
        useBindingsIn source
        |> List.filter (fun s -> s.Fix.IsSome)
        |> List.map (fun s -> s.Range.StartLine)

    Assert.Equal<int list>([ 19 ], lines)

[<Fact>]
let ``FR0160 keeps the fix where the try only reads headers, a note where it builds a header value`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.Net.Http
            open System.Net.Http.Headers
            type ApiException(message: string, inner: exn) =
                inherit Exception(message, inner)
                new(message: string) = ApiException(message, null)
            let etag (response: HttpResponseMessage) =
                try
                    response.Headers.GetValues("ETag") |> Seq.head
                with ex ->
                    raise (ApiException("no etag"))
            let authorize (client: HttpClient) (key: string) =
                try
                    client.DefaultRequestHeaders.Authorization <- AuthenticationHeaderValue(key)
                with ex ->
                    raise (ApiException("bad key"))
            """

    let found = lostInnerIn source
    Assert.Equal(2, found.Length)
    Assert.Contains(found, fun s -> s.Range.StartLine < 13 && not s.HeaderValues && not s.Edits.IsEmpty)
    Assert.Contains(found, fun s -> s.Range.StartLine > 13 && s.HeaderValues && s.Edits.IsEmpty)

[<Fact>]
let ``FR0007 keeps mutable where the inactive write closes the function`` () =
    let source =
        fsharp
            """
            module Test
            let run (work: int -> unit) =
                let mutable count = 0
                work count
            #if DEBUG_COUNT
                count <- count + 1
            #endif
            let plain () =
                let mutable width = 2
                width + 1
            """

    match mutablesIn source with
    | [ s ] -> Assert.Equal("width", s.Name)
    | other -> failwithf "Expected only 'width', got %A" other

[<Fact>]
let ``FR0124 reads a Serilog template by position only when every hole is a number`` () =
    let fits =
        fsharp
            """
            module M =
                let go (log: ILogger) (a: int) (b: int) (c: int) =
                    log.Information("{0} {Name} {1}", a, b, c)
            """

    Assert.Empty(templatesIn serilogScaffold fits)

    let repeated =
        fsharp
            """
            module M =
                let go (log: ILogger) (a: int) (b: int) (c: int) =
                    log.Information("{0} {Name} {0}", a, b, c)
            """

    match templatesIn serilogScaffold repeated with
    | [ s ] -> Assert.Equal(LogTemplates.TemplateProblem.DuplicateName "0", s.Problem)
    | other -> failwithf "Expected the duplicate '0', got %A" other

[<Fact>]
let ``an unknown framework ranks before unreadable projects and scripts, a dotted .NET Framework as its version`` () =
    let rank = FSharp.Refactor.Tool.Program.tfmRank
    Assert.True(rank "uap10.0.19041" < 98.0)
    Assert.True(rank "monoandroid13.0" < 98.0)
    Assert.True(rank "net10.0" < rank "uap10.0.19041")
    Assert.Equal(rank "net48", rank "net4.8")
    Assert.Equal(rank "net472", rank "net4.7.2")
    Assert.True(rank "net4.8" < rank "netcoreapp3.1")

[<Fact>]
let ``a solution that maps an old-format project to Any CPU keeps the projects' own platforms`` () =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-tests", Guid.NewGuid().ToString "N")

    Directory.CreateDirectory dir |> ignore

    try
        let write name (text: string) =
            let path = Path.Combine(dir, name)
            File.WriteAllText(path, text)
            path

        write
            "Legacy.fsproj"
            """<Project ToolsVersion="15.0"><PropertyGroup Condition="'$(Configuration)|$(Platform)' == 'Debug|AnyCPU'" /></Project>"""
        |> ignore

        write "Modern.fsproj" """<Project Sdk="Microsoft.NET.Sdk" />""" |> ignore

        let solution (project: string) =
            "Project(\"{F2A71F9B-5D33-465A-A702-920D77279786}\") = \"P\", \""
            + project
            + "\", \"{11111111-1111-1111-1111-111111111111}\"\nEndProject\nGlobal\n"
            + "\tGlobalSection(SolutionConfigurationPlatforms) = preSolution\n\t\tDebug|x64 = Debug|x64\n\tEndGlobalSection\n"
            + "\tGlobalSection(ProjectConfigurationPlatforms) = postSolution\n"
            + "\t\t{11111111-1111-1111-1111-111111111111}.Debug|x64.ActiveCfg = Debug|Any CPU\n\tEndGlobalSection\nEndGlobal\n"

        let platformOf = FSharp.Refactor.Tool.Program.solutionPlatform
        Assert.Equal(None, platformOf (write "Old.sln" (solution "Legacy.fsproj")))
        Assert.Equal(Some "x64", platformOf (write "New.sln" (solution "Modern.fsproj")))
    finally
        Directory.Delete(dir, true)

[<Fact>]
let ``FR0118 leaves the explicit None of a cleanup call, and replaces another`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            type Core() =
                member _.StopCoreAsync(token: CancellationToken) = Task.Delay(1, token)
                member _.LoadAsync(token: CancellationToken) = Task.Delay(1, token)
            let start (core: Core) (ct: CancellationToken) = task {
                do! core.LoadAsync(CancellationToken.None)
                do! core.StopCoreAsync(CancellationToken.None)
            }
            """

    let tree, sourceText, checkResults = parseAndCheck source

    match
        CancellationOverload.find tree sourceText checkResults
        |> List.filter (fun s -> s.Kind = CancellationOverload.TokenGap.NonePassed)
    with
    | [ s ] -> Assert.Equal(8, s.Range.StartLine)
    | other -> failwithf "Expected the one None in LoadAsync, got %A" other

[<Fact>]
let ``FR0118 leaves a stream over memory and an async iterator handed its token by WithCancellation`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            open System.IO
            open System.IO.Compression
            open System.Threading
            open System.Threading.Tasks
            type Pages() =
                member _.PageAsync() : IAsyncEnumerable<int> = Unchecked.defaultof<_>
                member _.PageAsync(ct: CancellationToken) : IAsyncEnumerable<int> = Unchecked.defaultof<_>
            let buffer = new MemoryStream()
            let zip = new GZipStream(buffer, CompressionMode.Compress, true)
            let pages (p: Pages) (ct: CancellationToken) = p.PageAsync().WithCancellation(ct)
            let pagesBare (p: Pages) (ct: CancellationToken) = p.PageAsync()
            let streams (source: Stream) (b: byte[]) (ct: CancellationToken) = task {
                let! n = source.ReadAsync(b, 0, b.Length)
                do! zip.WriteAsync(b, 0, n)
                do! buffer.FlushAsync()
                do! zip.CopyToAsync(source)
                let file = new GZipStream(File.OpenWrite "x", CompressionMode.Compress) :> Stream
                do! file.WriteAsync(b, 0, n)
            }
            """

    let tree, sourceText, checkResults = parseAndCheck source

    Assert.Equal<(string * int) list>(
        [ "PageAsync", 13; "ReadAsync", 15; "CopyToAsync", 18; "WriteAsync", 20 ],
        CancellationOverload.find tree sourceText checkResults
        |> List.filter (fun s -> s.Kind = CancellationOverload.TokenGap.Omitted)
        |> List.map (fun s -> s.MethodName, s.Range.StartLine)
    )

[<Fact>]
let ``FR0118 memory-stream guard keeps to Stream's own calls`` () =
    let source =
        fsharp
            """
            module Test
            open System.IO
            open System.IO.Compression
            open System.Threading
            open System.Threading.Tasks
            type Upload() =
                inherit MemoryStream()
                member _.SendAsync() : Task = Task.CompletedTask
                member _.SendAsync(ct: CancellationToken) : Task = Task.CompletedTask
            type Sink() =
                member _.Push(s: Stream) : Task = Task.CompletedTask
                member _.Push(s: Stream, ct: CancellationToken) : Task = Task.CompletedTask
            let buffer = new MemoryStream()
            let upload = new Upload()
            let run (sink: Sink) (b: byte[]) (ct: CancellationToken) = task {
                do! upload.SendAsync()
                do! upload.WriteAsync(b, 0, 1)
                do! sink.Push(buffer)
                let wrapped = new BufferedStream(buffer)
                do! wrapped.FlushAsync()
            }
            """

    let tree, sourceText, checkResults = parseAndCheck source

    Assert.Equal<(string * int) list>(
        [ "SendAsync", 16; "Push", 18 ],
        CancellationOverload.find tree sourceText checkResults
        |> List.filter (fun s -> s.Kind = CancellationOverload.TokenGap.Omitted)
        |> List.map (fun s -> s.MethodName, s.Range.StartLine)
    )
