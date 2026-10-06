/// FR0075 (UseBinding) escape shapes (A1, B4):
/// a value derived through the binder and bound to a local, a method group
/// handed on, a self-active object, a wrapper over a foreign resource, and
/// a `let` inside a computation expression whose builder has no `Using`.
/// Each shape refuses the `let` -> `use` fix; the safe shape beside it
/// still gets one, and the patched source typechecks.
module FSharp.Refactor.Tests.AuditUseBindingTests

open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open Xunit

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

let private expectNoFix (name: string) (source: string) =
    match useBindingsIn source |> List.filter (fun s -> s.Name = name) with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        s
    | other -> failwithf "Expected exactly one advisory for '%s', got %A" name other

let private expectFix (name: string) (source: string) =
    match useBindingsIn source |> List.filter (fun s -> s.Name = name) with
    | [ s ] ->
        Assert.True(Some("let", "use") = s.Fix, $"Expected a fix for '%s{name}', got %A{s}")
        let patched = applyEdit source s.Range "use"
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one use-binding fix for '%s', got %A" name other

// a disposable with a derived-value surface: a command from a connection,
// a reader from a command, a method to hand on, an event to subscribe
[<Literal>]
let private types =
    "module Test
open System
type Reader() =
    member _.Read() = 1
    interface IDisposable with
        member _.Dispose() = ()
type Cmd() =
    member val Text = \"\" with get, set
    member _.ExecuteReader() = new Reader()
    member _.ExecuteNonQuery() = 1
    interface IDisposable with
        member _.Dispose() = ()
type Conn() =
    member _.CreateCommand() = new Cmd()
    member _.TryRead() : int option = Some 1
    member _.Convert(s: string) = s.ToUpper()
    member _.Refresh() = ()
    member _.Start() = ()
    interface IDisposable with
        member _.Dispose() = ()
"

// ---- A1: a value derived through the binder, bound to a local ----

[<Fact>]
let ``a task derived from the reader and returned through a local refuses the fix`` () =
    let s =
        expectNoFix
            "reader"
            (fsharp
                """
                module Test
                open System.IO
                let fetch (path: string) =
                    let reader = new StreamReader(path)
                    let pending = reader.ReadToEndAsync()
                    pending
                """)

    Assert.Equal(Some UseBinding.Destination.ReadInResult, s.Destination)

[<Fact>]
let ``a reader from a command from the connection, returned, refuses the fix`` () =
    expectNoFix
        "conn"
        (types
         + fsharp
             """
             let openReader (sql: string) =
                 let conn = new Conn()
                 let cmd = conn.CreateCommand()
                 cmd.Text <- sql
                 cmd.ExecuteReader()
             """)
    |> ignore

    // through a chain of locals
    expectNoFix
        "conn"
        (types
         + fsharp
             """
             let openReader (sql: string) =
                 let conn = new Conn()
                 let cmd = conn.CreateCommand()
                 let r = cmd.ExecuteReader()
                 r
             """)
    |> ignore

[<Fact>]
let ``a derived local handed to a function or captured refuses the fix`` () =
    let s =
        expectNoFix
            "conn"
            (types
             + fsharp
                 """
                 let run (sink: Cmd -> unit) =
                     let conn = new Conn()
                     let cmd = conn.CreateCommand()
                     sink cmd
                     1
                 """)

    Assert.Equal(Some(UseBinding.Destination.Function("sink", false)), s.Destination)

    let s =
        expectNoFix
            "conn"
            (types
             + fsharp
                 """
                 let run (defer: (unit -> int) -> unit) =
                     let conn = new Conn()
                     let cmd = conn.CreateCommand()
                     defer (fun () -> cmd.ExecuteNonQuery())
                     1
                 """)

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

[<Fact>]
let ``a derived local consumed in the scope still gets use`` () =
    expectFix
        "conn"
        (types
         + fsharp
             """
             let count (sql: string) =
                 let conn = new Conn()
                 let cmd = conn.CreateCommand()
                 cmd.Text <- sql
                 let n = cmd.ExecuteNonQuery()
                 n + 1
             """)

    // a plain-valued container is evaluated and done
    expectFix
        "conn"
        (types
         + fsharp
             """
             let probe () =
                 let conn = new Conn()
                 let r = conn.TryRead()
                 r
             """)

// ---- A1: a method group handed on ----

[<Fact>]
let ``a method group inside a lazy combinator as the result refuses the fix`` () =
    let s =
        expectNoFix
            "c"
            (types
             + fsharp
                 """
                 let upper (xs: string list) =
                     let c = new Conn()
                     Seq.map c.Convert xs
                 """)

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

    expectNoFix
        "c"
        (types
         + fsharp
             """
             let upper (xs: string list) =
                 let c = new Conn()
                 xs |> List.map c.Convert
             """)
    |> ignore

[<Fact>]
let ``a method group registered on a publisher refuses the fix`` () =
    let s =
        expectNoFix
            "c"
            (types
             + fsharp
                 """
                 let hook (changed: IEvent<unit>) =
                     let c = new Conn()
                     changed.Add c.Refresh
                     ()
                 """)

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

[<Fact>]
let ``an invoked plain-valued member as the result still gets use`` () =
    expectFix
        "c"
        (types
         + fsharp
             """
             let upper (s: string) =
                 let c = new Conn()
                 c.Convert s
             """)

    expectFix
        "c"
        (types
         + fsharp
             """
             let upper (s: string) =
                 let c = new Conn()
                 c.Convert(s).Length
             """)

// ---- A1: self-active objects ----

[<Fact>]
let ``a file system watcher refuses the fix`` () =
    let s =
        expectNoFix
            "w"
            (fsharp
                """
                module Test
                let watch (path: string) (onChange: string -> unit) =
                    let w = new System.IO.FileSystemWatcher(path)
                    w.Changed.Add(fun e -> onChange e.FullPath)
                    w.EnableRaisingEvents <- true
                """)

    Assert.Equal(Some UseBinding.Destination.SelfActive, s.Destination)
    Assert.Contains("work of its own", UseBinding.describeEscape s)

[<Fact>]
let ``a threading timer built with a callback refuses the fix`` () =
    expectNoFix
        "t"
        (fsharp
            """
            module Test
            let schedule (tick: unit -> unit) =
                let t = new System.Threading.Timer((fun _ -> tick ()), null, 0, 1000)
                ()
            """)
    |> ignore

[<Fact>]
let ``a timer started in the scope refuses the fix`` () =
    expectNoFix
        "timer"
        (fsharp
            """
            module Test
            let startHeartbeat (log: string -> unit) =
                let timer = new System.Timers.Timer(1000.0)
                timer.Elapsed.Add(fun _ -> log "tick")
                timer.Start()
            """)
    |> ignore

[<Fact>]
let ``a process, a listener and a socket refuse the fix`` () =
    expectNoFix
        "p"
        (fsharp
            """
            module Test
            let launch (exe: string) =
                let p = new System.Diagnostics.Process()
                p.StartInfo.FileName <- exe
                p.Start()
            """)
    |> ignore

    expectNoFix
        "l"
        (fsharp
            """
            module Test
            let listen (port: int) =
                let l = new System.Net.Sockets.TcpListener(System.Net.IPAddress.Any, port)
                l.Start()
                ()
            """)
    |> ignore

    expectNoFix
        "s"
        (fsharp
            """
            module Test
            open System.Net.Sockets
            let bind (port: int) =
                let s = new Socket(SocketType.Stream, ProtocolType.Tcp)
                s.Bind(System.Net.IPEndPoint(System.Net.IPAddress.Any, port))
                s.Listen 10
            """)
    |> ignore

[<Fact>]
let ``a disposable whose event the scope subscribes to refuses the fix`` () =
    let source =
        "module Test
open System
type Cache() =
    let changed = Event<unit>()
    [<CLIEvent>]
    member _.Changed = changed.Publish
    member _.Count = 1
    interface IDisposable with
        member _.Dispose() = ()
let hook (log: string -> unit) =
    let c = new Cache()
    c.Changed.Add(fun () -> log \"changed\")
    c.Count
let pipe (log: string -> unit) =
    let c = new Cache()
    c.Changed |> Event.add (fun () -> log \"changed\")
    c.Count"

    match useBindingsIn source with
    | [ a; b ] ->
        Assert.Equal(None, a.Fix)
        Assert.Equal(None, b.Fix)
    | other -> failwithf "Expected two advisories, got %A" other

[<Fact>]
let ``a token source with a registration refuses the fix; one merely read still gets use`` () =
    expectNoFix
        "cts"
        (fsharp
            """
            module Test
            let arm (onCancel: unit -> unit) =
                let cts = new System.Threading.CancellationTokenSource()
                cts.Token.Register(fun () -> onCancel ()) |> ignore
                cts.CancelAfter 100
            """)
    |> ignore

    expectFix
        "cts"
        (fsharp
            """
            module Test
            let probe () =
                let cts = new System.Threading.CancellationTokenSource()
                cts.CancelAfter 100
                cts.IsCancellationRequested
            """)

[<Fact>]
let ``a unit Start call on any disposable refuses the fix`` () =
    let s =
        expectNoFix
            "c"
            (types
             + fsharp
                 """
                 let run () =
                     let c = new Conn()
                     c.Start()
                     1
                 """)

    Assert.Equal(Some UseBinding.Destination.SelfActive, s.Destination)

// ---- A1: wrappers over a foreign resource ----

[<Fact>]
let ``a reader over a constructor parameter is not the scope's to dispose`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type LineSource(stream: Stream) =
                    member _.Next() =
                        let r = new StreamReader(stream)
                        r.ReadLine()
                """
        )
    )

[<Fact>]
let ``a client over an injected handler is not the scope's to dispose`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                type Api(handler: HttpMessageHandler) =
                    member _.Get(url: string) =
                        let client = new HttpClient(handler)
                        let s = client.GetStringAsync(url).Result
                        s.Length
                """
        )
    )

[<Fact>]
let ``a wrapper over a class field, a module value, a property or a record field is not the scope's`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Source(path: string) =
                    let stream = File.OpenRead path
                    member _.Next() =
                        let r = new StreamReader(stream)
                        r.ReadLine()
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private shared = File.OpenRead "x"
                let next () =
                    let r = new StreamReader(shared)
                    r.ReadLine()
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Holder() =
                    member val Input: Stream = null with get, set
                    member this.Next() =
                        let r = new StreamReader(this.Input)
                        r.ReadLine()
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Cfg = { Input: Stream }
                let next (cfg: Cfg) =
                    let r = new StreamReader(cfg.Input)
                    r.ReadLine()
                """
        )
    )

[<Fact>]
let ``a wrapper inside a lambda over a stream the function opened is not the lambda's`` () =
    // the stream is shared by every call of the lambda; the first `use`
    // would close it under the rest
    let suggestions =
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let lines (path: string) (keys: string list) =
                    let s = File.OpenRead path
                    keys |> List.map (fun k ->
                        let r = new StreamReader(s)
                        r.ReadLine() + k)
                """
        )

    Assert.DoesNotContain(suggestions, fun s -> s.Name = "r")

[<Fact>]
let ``compression and crypto streams over a caller's stream are not the scope's`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                open System.IO.Compression
                let inflate (input: Stream) =
                    let z = new GZipStream(input, CompressionMode.Decompress)
                    z.ReadByte()
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                open System.Security.Cryptography
                let encrypt (output: Stream) (aes: Aes) =
                    let cs = new CryptoStream(output, aes.CreateEncryptor(), CryptoStreamMode.Write)
                    cs.WriteByte 1uy
                """
        )
    )

[<Fact>]
let ``a wrapper over a stream this scope opened, a path or a locally built handler still gets use`` () =
    expectFix
        "r"
        (fsharp
            """
            module Test
            open System.IO
            let read (path: string) =
                let s = File.OpenRead path
                let r = new StreamReader(s)
                r.ReadToEnd()
            """)

    expectFix
        "w"
        (fsharp
            """
            module Test
            open System.IO
            let write (path: string) =
                let w = new StreamWriter(path, false, System.Text.Encoding.UTF8)
                w.Write "x"
            """)

    // a wrapper over a LOCAL resource is the scope's: the stream is adopted
    // by the reader, and the reader is disposed here
    expectFix
        "r"
        (fsharp
            """
            module Test
            open System.IO
            let get (path: string) =
                let stream = new FileStream(path, FileMode.Open)
                let r = new StreamReader(stream)
                let s = r.ReadLine()
                s.Length
            """)

// ---- B4: a computation expression whose builder has no Using ----

[<Fact>]
let ``a let inside a builder without Using refuses the fix`` () =
    let s =
        expectNoFix
            "s"
            (fsharp
                """
                module Test
                type MaybeBuilder() =
                    member _.Bind(m, f) = Option.bind f m
                    member _.Return x = Some x
                let maybe = MaybeBuilder()
                let firstByte (path: string) (probe: int64 -> int option) =
                    maybe {
                        let s = new System.IO.FileStream(path, System.IO.FileMode.Open)
                        let! n = probe s.Length
                        return n
                    }
                """)

    Assert.Equal(Some UseBinding.Destination.NoBuilderUsing, s.Destination)
    Assert.Contains("no 'Using'", UseBinding.describeEscape s)

[<Fact>]
let ``a let inside a builder with Using, or a core builder, still gets use`` () =
    expectFix
        "s"
        (fsharp
            """
            module Test
            type MaybeBuilder() =
                member _.Bind(m, f) = Option.bind f m
                member _.Return x = Some x
                member _.Using(r: 'r, f: 'r -> 'a option) : 'a option when 'r :> System.IDisposable =
                    try f r finally r.Dispose()
            let maybe = MaybeBuilder()
            let firstByte (path: string) (probe: int64 -> int option) =
                maybe {
                    let s = new System.IO.FileStream(path, System.IO.FileMode.Open)
                    let! n = probe s.Length
                    return n
                }
            """)

    expectFix
        "s"
        (fsharp
            """
            module Test
            let firstByte (path: string) (probe: int64 -> Async<int>) =
                async {
                    let s = new System.IO.FileStream(path, System.IO.FileMode.Open)
                    let! n = probe s.Length
                    return n
                }
            """)

    expectFix
        "s"
        (fsharp
            """
            module Test
            let bytes (path: string) =
                seq {
                    let s = new System.IO.FileStream(path, System.IO.FileMode.Open)
                    yield s.ReadByte()
                }
            """)

[<Fact>]
let ``a let inside a local function inside such a builder is ordinary code`` () =
    expectFix
        "s"
        (fsharp
            """
            module Test
            type MaybeBuilder() =
                member _.Bind(m, f) = Option.bind f m
                member _.Return x = Some x
            let maybe = MaybeBuilder()
            let firstByte (path: string) =
                maybe {
                    let size (p: string) =
                        let s = new System.IO.FileStream(p, System.IO.FileMode.Open)
                        s.Length
                    return size path
                }
            """)

// ---- a lazy body runs after the scope ----

[<Fact>]
let ``a disposable read inside a returned lazy refuses the fix`` () =
    expectNoFix
        "s"
        (fsharp
            """
            module Test
            let deferred (path: string) =
                let s = new System.IO.FileStream(path, System.IO.FileMode.Open)
                lazy (s.ReadByte())
            """)
    |> ignore

[<Fact>]
let ``FR0075 a window shown non-modally or run as the main window is not the scope's to dispose`` () =
    // a shown window closes, and disposes itself, when the user is done with it;
    // only the modal `ShowDialog` returns with the window closed
    let source =
        fsharp
            """
            namespace System.Windows.Forms
            type Form() =
                member _.Show() = ()
                member _.Show(owner: obj) = ()
                member _.ShowDialog() = 0
                interface System.IDisposable with
                    member _.Dispose() = ()
            type Application =
                static member Run(main: Form) = ()
            namespace App
            open System.Windows.Forms
            type MyForm() =
                inherit Form()
            module M =
                let shown () =
                    let f = new MyForm()
                    f.Show()
                let modal () =
                    let f = new MyForm()
                    f.ShowDialog() |> ignore
                let main () =
                    let f = new MyForm()
                    Application.Run(f)
            """

    let tree, sourceText, checkResults = parseAndCheck source

    let fired =
        UseBinding.find tree sourceText checkResults
        |> List.map (fun s -> s.Range.StartLine)

    Assert.Equal<int list>([ 19 ], fired)
