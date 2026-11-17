/// The F# twins of the defects a 2026-11-17 sweep of seven public C#
/// repositories (PowerToys, shadowsocks-windows, Files, ShareX,
/// RevokeMsgPatcher, Polly, azure-sdk-for-net) found in CSharp.Refactor.
module FSharp.Refactor.Tests.CorpusTwin1117Tests

open System
open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tool
open FSharp.Refactor.Tests.Parsing

let private lineOf (source: string) (needle: string) =
    (source.Replace("\r\n", "\n").Split('\n')
     |> Array.findIndex (fun l -> l.Contains needle))
    + 1

// ---- FR0119 ----

let private awaitableIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AwaitableOverload.find tree sourceText checkResults

[<Fact>]
let ``FR0119 never binds the member the call sits in`` () =
    // ShareX CaptureLastRegion: `Execute` inside `ExecuteAsync` became the method itself
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            type Capture() =
                member x.Execute(s: int) = s
                member x.ExecuteAsync(s: int) : Task<int> = task {
                    do! Task.Delay(1)
                    let r = x.Execute(s)
                    return r
                }
                member x.Other(s: int) : Task<int> = task {
                    do! Task.Delay(1)
                    let r2 = x.Execute(s)
                    return r2
                }
            """

    Assert.Equal<int list>([ lineOf source "let r2 =" ], awaitableIn source |> List.map (fun s -> s.Range.StartLine))

[<Fact>]
let ``FR0119 leaves a fire-and-forget wrapper and still binds a blocking one`` () =
    // RevokeMsgPatcher GAHelper: `RequestPageView` drops `RequestPageViewAsync`'s task
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            type Ga() =
                member x.PingAsync(page: string) : Task = Task.Delay(1)
                member x.Ping(page: string) : unit = x.PingAsync(page) |> ignore
                member x.FlushAsync(page: string) : Task = Task.Delay(1)
                member x.Flush(page: string) : unit = x.FlushAsync(page).Wait()
            let load (ga: Ga) = task {
                ga.Ping("/main")
                ga.Flush("/main")
                return ()
            }
            """

    Assert.Equal<int list>([ lineOf source "ga.Flush(" ], awaitableIn source |> List.map (fun s -> s.Range.StartLine))

[<Fact>]
let ``FR0119 leaves the sync branch of a dual sync-async body and a call commented as sync`` () =
    // Azure.Core's `bool async` policies; MultipartReaderStream's `// Sync, it's already buffered`
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            type Policy() =
                member x.ProcessNext(m: int) : unit = ()
                member x.ProcessNextAsync(m: int) : Task = Task.CompletedTask
                member x.Process(m: int, isAsync: bool) : Task = task {
                    if isAsync then
                        do! x.ProcessNextAsync(m)
                    else
                        x.ProcessNext(m)
                        ()
                    return ()
                }
                member x.Commented(m: int) : Task = task {
                    // Sync, it's already buffered
                    x.ProcessNext(m)
                    return ()
                }
                member x.Kept(k: int) : Task = task {
                    // keep in sync with the writer
                    x.ProcessNext(k)
                    return ()
                }
                member x.Plain(p: int) : Task = task {
                    x.ProcessNext(p)
                    return ()
                }
            """

    Assert.Equal<int list>(
        [ lineOf source "x.ProcessNext(k)"; lineOf source "x.ProcessNext(p)" ],
        awaitableIn source |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

[<Fact>]
let ``FR0119 binds every statement of a CE body, after a do-bang and after another statement`` () =
    // the index records only a chain's outermost Sequential: only the first
    // statement of a body was ever rewritten
    let source =
        fsharp
            """
            module Test
            open System.IO
            open System.Threading.Tasks
            let flushAll (a: Stream) (b: Stream) (c: Stream) = task {
                do! Task.Delay(1)
                a.Flush()
                b.Flush()
                c.Flush()
                return 1
            }
            """

    let found = awaitableIn source

    Assert.Equal<int list>(
        [
            lineOf source "a.Flush()"
            lineOf source "b.Flush()"
            lineOf source "c.Flush()"
        ],
        found |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

    let patched =
        found
        |> List.collect (fun s -> s.Fixes)
        |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
        |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

    Assert.Contains("do! b.FlushAsync()", patched)
    assertTypechecks "FR0119 later statements" patched

[<Fact>]
let ``FR0119 binds a wrapper's call to another object's twin of the same name`` () =
    // `ReadAsync` around `inner.Read` is the shape the rule exists for; only a
    // member of the twin's own type, or one derived from it, would bind itself
    let source =
        fsharp
            """
            module Test
            open System.IO
            open System.Threading.Tasks
            type Wrapper(inner: Stream) =
                member _.ReadAsync(buffer: byte[]) : Task<int> = task {
                    let n = inner.Read(buffer, 0, buffer.Length)
                    return n
                }
            type Capture() =
                member x.Execute(s: int) = s
                member x.ExecuteAsync(s: int) : Task<int> = task {
                    do! Task.Delay(1)
                    let r = x.Execute(s)
                    return r
                }
            """

    Assert.Equal<int list>([ lineOf source "let n =" ], awaitableIn source |> List.map (fun s -> s.Range.StartLine))

[<Fact>]
let ``FR0119 binds a sync member that discards a value, not work`` () =
    // `let _ = d.Remove id` drops a bool: no fire-and-forget wrapper
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            open System.Threading.Tasks
            type Cache() =
                let d = Dictionary<int, string>()
                member _.Save(id: int) : unit =
                    let _ = d.Remove id
                    d.[id] <- "x"
                member _.SaveAsync(id: int) : Task = Task.CompletedTask
            let store (c: Cache) = task {
                c.Save 1
                return 2
            }
            """

    Assert.Equal<int list>([ lineOf source "c.Save 1" ], awaitableIn source |> List.map (fun s -> s.Range.StartLine))

[<Fact>]
let ``FR0119 binds a call whose comment opens with sync but asks for the change`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            type Policy() =
                member x.ProcessNext(m: int) : unit = ()
                member x.ProcessNextAsync(m: int) : Task = Task.CompletedTask
                member x.Asked(a: int) : Task = task {
                    // sync over async here, fix later
                    x.ProcessNext(a)
                    return ()
                }
                member x.Todo(t: int) : Task = task {
                    // Synchronous for now: TODO make it async
                    x.ProcessNext(t)
                    return ()
                }
                member x.Meant(m: int) : Task = task {
                    // Sync on purpose: the caller holds the gate
                    x.ProcessNext(m)
                    return ()
                }
            """

    Assert.Equal<int list>(
        [ lineOf source "x.ProcessNext(a)"; lineOf source "x.ProcessNext(t)" ],
        awaitableIn source |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

// ---- FR0049 ----

let private blockingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SyncOverAsync.find tree sourceText checkResults

[<Fact>]
let ``FR0049 leaves a dual-path read, a commented one and one a WhenAny raise proved complete`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let dual (t: Task<int>) (isAsync: bool) = task {
                if isAsync then
                    let! r0 = t
                    return r0
                else
                    let r1 = t.Result
                    return r1
            }
            let raced (t: Task<int>) (other: Task<int>) = task {
                let! w = Task.WhenAny(t, other)
                if w <> t then failwith "timeout"
                let r2 = t.Result
                return r2
            }
            let commented (t: Task<int>) = task {
                do! Task.Delay(1)
                // synchronous on purpose: the task is finished here
                let r3 = t.Result
                return r3
            }
            let blocking (t: Task<int>) = task {
                do! Task.Delay(1)
                let r4 = t.Result
                return r4
            }
            let unrelated (u: Task<int>) (wait: bool) = task {
                if wait then
                    do! Task.Delay(100)
                    return 0
                else
                    let r5 = u.Result
                    return r5
            }
            """

    Assert.Equal<int list>(
        [ lineOf source "let r4 ="; lineOf source "let r5 =" ],
        blockingIn source |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

// ---- FR0118 ----

let private unobservedLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CancellationOverload.findUnobservedLoops tree sourceText checkResults

[<Fact>]
let ``FR0118 notes a loop over awaited data, and leaves an enumerator built from the token and an explicit None`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            open System.Threading
            open System.Threading.Tasks
            let fetched (ct: CancellationToken) (getAll: CancellationToken -> Task<int list>) (handle: int -> Task) = task {
                let! items = getAll ct
                for x in items do
                    do! handle x
                return 0
            }
            let uncancelled (ct: CancellationToken) (xs: int list) (delete: int -> CancellationToken -> Task) = task {
                for x in xs do
                    do! delete x CancellationToken.None
                return 0
            }
            let enumerated (ct: CancellationToken) (source: IAsyncEnumerable<int>) = task {
                let e = source.GetAsyncEnumerator ct
                let stepper = e
                let mutable go = true
                while go do
                    let! more = stepper.MoveNextAsync()
                    go <- more
                return 0
            }
            """

    Assert.Equal<int list>(
        [ lineOf source "for x in items do" ],
        unobservedLoopsIn source |> List.map (fun s -> s.Range.StartLine)
    )

[<Fact>]
let ``FR0118 keeps the None of a compensation before a raise`` () =
    // ShareX's S3 rename: the rollback delete passes None on purpose
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let rename (a: string) (b: string) (ct: CancellationToken) (delete: string -> CancellationToken -> Task<bool>) = task {
                let! ok = delete a ct
                if not ok then
                    let! _ = delete b CancellationToken.None
                    failwith "rollback"
                let! last = delete b CancellationToken.None
                return last
            }
            """

    let tree, sourceText, checkResults = parseAndCheck source

    let nonePassed =
        CancellationOverload.find tree sourceText checkResults
        |> List.filter (fun s -> s.Kind = CancellationOverload.TokenGap.NonePassed)

    Assert.Equal<int list>([ lineOf source "let! last =" ], nonePassed |> List.map (fun s -> s.Range.StartLine))

[<Fact>]
let ``FR0118 reads every element of a statement chain: a later bare statement is left running, a third-statement result is returned``
    ()
    =
    // the index records only a chain's outermost Sequential: the final element
    // of three statements never read as the chain's value (the returned task's
    // None was missed), and only the first statement read as a statement
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let fire (ct: CancellationToken) (start: CancellationToken -> Task) =
                printfn "a"
                start CancellationToken.None
                printfn "b"
            let returned (ct: CancellationToken) (start: CancellationToken -> Task) : Task =
                printfn "a"
                printfn "b"
                start CancellationToken.None
            let waited (ct: CancellationToken) (start: CancellationToken -> Task) = task {
                printfn "a"
                do! start CancellationToken.None
                printfn "b"
            }
            """

    let tree, sourceText, checkResults = parseAndCheckAllowingErrors source

    let nonePassed =
        CancellationOverload.find tree sourceText checkResults
        |> List.filter (fun s -> s.Kind = CancellationOverload.TokenGap.NonePassed)

    let returnedLine =
        (source.Replace("\r\n", "\n").Split('\n')
         |> Array.mapi (fun i l -> i + 1, l)
         |> Array.filter (fun (_, l) -> l.Trim() = "start CancellationToken.None")
         |> Array.map fst
         |> Array.last)

    Assert.Equal<int list>(
        [ returnedLine; lineOf source "do! start CancellationToken.None" ],
        nonePassed |> List.map (fun s -> s.Range.StartLine) |> List.sort
    )

[<Fact>]
let ``FR0118 notes a loop over data derived from a value computed with the token`` () =
    // `ys` is data; a token read off a linked source carries it
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let derived (ct: CancellationToken) (compute: CancellationToken -> int list) (handle: int -> Task) = task {
                let xs = compute ct
                let ys = xs |> List.filter (fun x -> x > 0)
                for y in ys do
                    do! handle y
                return 0
            }
            let linked (ct: CancellationToken) (xs: int list) (handle: int -> CancellationToken -> Task) = task {
                use source = CancellationTokenSource.CreateLinkedTokenSource ct
                let token = source.Token
                for x in xs do
                    do! handle x token
                return 0
            }
            """

    Assert.Equal<int list>(
        [ lineOf source "for y in ys do" ],
        unobservedLoopsIn source |> List.map (fun s -> s.Range.StartLine)
    )

// ---- FR0163 ----

[<Fact>]
let ``FR0163 notes a threading timer dropped as a later statement`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading
            let start (tick: obj -> unit) =
                printfn "starting"
                new Timer(TimerCallback tick, null, 0, 1000)
                printfn "started"
            """

    let tree, sourceText, checkResults = parseAndCheckAllowingErrors source

    Assert.Equal<int list>(
        [ lineOf source "new Timer(" ],
        DroppedTimer.find tree sourceText checkResults
        |> List.map (fun s -> s.Range.StartLine)
    )

// ---- FR0092 ----

let private failwithContextIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    FailwithContext.find tree sourceText checkResults

[<Fact>]
let ``FR0092 drops the message's closing mark before the arguments, a full-width one too`` () =
    let source =
        fsharp
            """
            module Test
            let rejected (x: int) =
                failwith "Rejected."
            let missing (path: string) =
                failwith "未找到资源项。"
            """

    let patched =
        failwithContextIn source
        |> List.sortByDescending (fun s -> s.Range.StartLine)
        |> List.fold (fun acc s -> applyEdit acc s.Range s.ReplacementText) source

    Assert.Contains("failwith $\"Rejected, calling rejected with x: {x}\"", patched)
    Assert.Contains("failwith $\"未找到资源项, calling missing with path: {path}\"", patched)
    assertTypechecks "FR0092 trimmed" patched

// ---- FR0162 ----

[<Fact>]
let ``FR0162 leaves a mutable whose address is taken`` () =
    let resized =
        "module Cache\n\nopen System\n\nlet mutable private buf: int[] = null\n\nlet ensure (n: int) =\n    if isNull buf then buf <- Array.zeroCreate n\n    Array.Resize(&buf, n)\n    buf\n"

    let plain =
        "module Cache\n\nlet mutable private buf: int[] = null\n\nlet ensure (n: int) =\n    if isNull buf then buf <- Array.zeroCreate n\n    buf\n"

    let tree, source = parse resized
    Assert.Empty(LazyInit.find tree source)
    let tree, source = parse plain
    Assert.Single(LazyInit.find tree source) |> ignore

// ---- tool ----

[<Fact>]
let ``a console note is keyed by the lines around it, not by its own line alone`` () =
    let lines =
        [|
            "let first (t: Task<int>) ="
            "    printfn \"first\""
            "    t.Result"
            ""
            "let second (t: Task<int>) ="
            "    printfn \"second\""
            "    t.Result"
        |]

    // the same line in two functions is two notes
    Assert.NotEqual<string>(Program.noteContext lines 3, Program.noteContext lines 7)

    // a line added above shifts the note, not its key
    let shifted = Array.append [| "open System" |] lines
    Assert.Equal<string>(Program.noteContext lines 7, Program.noteContext shifted 8)

[<Fact>]
let ``a project whose nearest Platforms lacks AnyCPU builds for x64`` () =
    let dir =
        Path.Combine(Path.GetTempPath(), "fsref-platform-" + Guid.NewGuid().ToString("N"))

    let write (rel: string) (text: string) =
        let path = Path.Combine(dir, rel)
        Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
        File.WriteAllText(path, text)
        path

    try
        Directory.CreateDirectory(Path.Combine(dir, ".git")) |> ignore

        write
            "Directory.Build.props"
            "<Project><PropertyGroup><Platforms>ARM64;x64</Platforms></PropertyGroup></Project>"
        |> ignore

        let inherited =
            write "src/A/A.fsproj" """<Project Sdk="Microsoft.NET.Sdk"></Project>"""

        let own =
            write
                "src/B/B.fsproj"
                """<Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><Platforms>AnyCPU;x64</Platforms></PropertyGroup></Project>"""

        Assert.Equal(Some "x64", Program.projectPlatform inherited)
        Assert.Equal(None, Program.projectPlatform own)
        Assert.Equal(Some "x64", Program.projectPlatform (Path.GetDirectoryName inherited))
        Assert.Equal(None, Program.projectPlatform (Path.Combine(dir, "Directory.Build.props")))
    finally
        try
            Directory.Delete(dir, true)
        with _ ->
            ()

[<Xunit.Collection("ProjectSources")>]
type ReportNotes() =

    [<Fact>]
    member _.``a note in a file a later pass re-analyses is reported once, at its current line``() =
        // RevokeMsgPatcher (C# twin): pass 1 added a line, pass 2 found the notes one
        // line lower, and the SARIF carried both
        let dir =
            Path.Combine(Path.GetTempPath(), "fsref-notes-" + Guid.NewGuid().ToString("N"))

        Directory.CreateDirectory dir |> ignore

        let framework = $"net{Environment.Version.Major}.0"

        File.WriteAllText(
            Path.Combine(dir, "Sample.fsproj"),
            $"<Project Sdk=\"Microsoft.NET.Sdk\"><PropertyGroup><TargetFramework>{framework}</TargetFramework></PropertyGroup><ItemGroup><Compile Include=\"Sample.fs\" /></ItemGroup></Project>"
        )

        let file = Path.Combine(dir, "Sample.fs")

        File.WriteAllText(
            file,
            "module Sample\n\nopen System.Threading\nopen System.Threading.Tasks\n\nlet pump (ct: CancellationToken) (xs: int list) (handle: int -> Task) =\n    task {\n        for x in xs do\n            do! handle x\n\n        return 0\n    }\n\nlet probe (s: string) =\n    try\n        int s\n    with _ ->\n        0\n"
        )

        let report = Path.Combine(dir, "x.sarif")

        try
            let code =
                use captured = new StringWriter()
                let oldOut = Console.Out
                Console.SetOut captured

                try
                    Program.main
                        [|
                            Path.Combine(dir, "Sample.fsproj")
                            "--codes"
                            "FR0118,FR0055"
                            "--notes"
                            "--report"
                            report
                            "--no-color"
                        |]
                finally
                    Console.SetOut oldOut

            Assert.Equal(0, code)
            let edited = File.ReadAllText file
            Assert.Contains("ct.ThrowIfCancellationRequested()", edited)

            use doc = System.Text.Json.JsonDocument.Parse(File.ReadAllText report)

            let lines =
                [
                    for run in doc.RootElement.GetProperty("runs").EnumerateArray() do
                        for result in run.GetProperty("results").EnumerateArray() do
                            if result.GetProperty("ruleId").GetString() = "FR0055" then
                                result
                                    .GetProperty("locations")
                                    .[0].GetProperty("physicalLocation")
                                    .GetProperty("region")
                                    .GetProperty("startLine")
                                    .GetInt32()
                ]

            Assert.Equal<int list>([ lineOf edited "with _ ->" ], lines)
        finally
            try
                Directory.Delete(dir, true)
            with _ ->
                ()
