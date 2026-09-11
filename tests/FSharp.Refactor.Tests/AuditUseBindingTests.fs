/// FR0075 (UseBinding) escape shapes from the 0.8.2-to-HEAD audit (A1, B4):
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
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one use-binding fix for '%s', got %A" name other

// a disposable with a derived-value surface: a command from a connection,
// a reader from a command, a method to hand on, an event to subscribe
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
let ``a task derived from the client and returned through a local refuses the fix`` () =
    let s =
        expectNoFix
            "client"
            "module Test\nopen System.Net.Http\nlet fetch (url: string) =\n    let client = new HttpClient()\n    let pending = client.GetStringAsync url\n    pending"

    Assert.Equal(Some UseBinding.Destination.ReadInResult, s.Destination)

[<Fact>]
let ``a reader from a command from the connection, returned, refuses the fix`` () =
    expectNoFix
        "conn"
        (types
         + "let openReader (sql: string) =\n    let conn = new Conn()\n    let cmd = conn.CreateCommand()\n    cmd.Text <- sql\n    cmd.ExecuteReader()")
    |> ignore

    // through a chain of locals
    expectNoFix
        "conn"
        (types
         + "let openReader (sql: string) =\n    let conn = new Conn()\n    let cmd = conn.CreateCommand()\n    let r = cmd.ExecuteReader()\n    r")
    |> ignore

[<Fact>]
let ``a derived local handed to a function or captured refuses the fix`` () =
    let s =
        expectNoFix
            "conn"
            (types
             + "let run (sink: Cmd -> unit) =\n    let conn = new Conn()\n    let cmd = conn.CreateCommand()\n    sink cmd\n    1")

    Assert.Equal(Some(UseBinding.Destination.Function("sink", false)), s.Destination)

    let s =
        expectNoFix
            "conn"
            (types
             + "let run (defer: (unit -> int) -> unit) =\n    let conn = new Conn()\n    let cmd = conn.CreateCommand()\n    defer (fun () -> cmd.ExecuteNonQuery())\n    1")

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

[<Fact>]
let ``a derived local consumed in the scope still gets use`` () =
    expectFix
        "conn"
        (types
         + "let count (sql: string) =\n    let conn = new Conn()\n    let cmd = conn.CreateCommand()\n    cmd.Text <- sql\n    let n = cmd.ExecuteNonQuery()\n    n + 1")

    // a plain-valued container is evaluated and done
    expectFix
        "conn"
        (types
         + "let probe () =\n    let conn = new Conn()\n    let r = conn.TryRead()\n    r")

// ---- A1: a method group handed on ----

[<Fact>]
let ``a method group inside a lazy combinator as the result refuses the fix`` () =
    let s =
        expectNoFix
            "c"
            (types
             + "let upper (xs: string list) =\n    let c = new Conn()\n    Seq.map c.Convert xs")

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

    expectNoFix
        "c"
        (types
         + "let upper (xs: string list) =\n    let c = new Conn()\n    xs |> List.map c.Convert")
    |> ignore

[<Fact>]
let ``a method group registered on a publisher refuses the fix`` () =
    let s =
        expectNoFix
            "c"
            (types
             + "let hook (changed: IEvent<unit>) =\n    let c = new Conn()\n    changed.Add c.Refresh\n    ()")

    Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)

[<Fact>]
let ``an invoked plain-valued member as the result still gets use`` () =
    expectFix "c" (types + "let upper (s: string) =\n    let c = new Conn()\n    c.Convert s")

    expectFix
        "c"
        (types
         + "let upper (s: string) =\n    let c = new Conn()\n    c.Convert(s).Length")

// ---- A1: self-active objects ----

[<Fact>]
let ``a file system watcher refuses the fix`` () =
    let s =
        expectNoFix
            "w"
            "module Test\nlet watch (path: string) (onChange: string -> unit) =\n    let w = new System.IO.FileSystemWatcher(path)\n    w.Changed.Add(fun e -> onChange e.FullPath)\n    w.EnableRaisingEvents <- true"

    Assert.Equal(Some UseBinding.Destination.SelfActive, s.Destination)
    Assert.Contains("work of its own", UseBinding.describeEscape s)

[<Fact>]
let ``a threading timer built with a callback refuses the fix`` () =
    expectNoFix
        "t"
        "module Test\nlet schedule (tick: unit -> unit) =\n    let t = new System.Threading.Timer((fun _ -> tick ()), null, 0, 1000)\n    ()"
    |> ignore

[<Fact>]
let ``a timer started in the scope refuses the fix`` () =
    expectNoFix
        "timer"
        "module Test\nlet startHeartbeat (log: string -> unit) =\n    let timer = new System.Timers.Timer(1000.0)\n    timer.Elapsed.Add(fun _ -> log \"tick\")\n    timer.Start()"
    |> ignore

[<Fact>]
let ``a process, a listener and a socket refuse the fix`` () =
    expectNoFix
        "p"
        "module Test\nlet launch (exe: string) =\n    let p = new System.Diagnostics.Process()\n    p.StartInfo.FileName <- exe\n    p.Start()"
    |> ignore

    expectNoFix
        "l"
        "module Test\nlet listen (port: int) =\n    let l = new System.Net.Sockets.TcpListener(System.Net.IPAddress.Any, port)\n    l.Start()\n    ()"
    |> ignore

    expectNoFix
        "s"
        "module Test\nopen System.Net.Sockets\nlet bind (port: int) =\n    let s = new Socket(SocketType.Stream, ProtocolType.Tcp)\n    s.Bind(System.Net.IPEndPoint(System.Net.IPAddress.Any, port))\n    s.Listen 10"
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
        "module Test\nlet arm (onCancel: unit -> unit) =\n    let cts = new System.Threading.CancellationTokenSource()\n    cts.Token.Register(fun () -> onCancel ()) |> ignore\n    cts.CancelAfter 100"
    |> ignore

    expectFix
        "cts"
        "module Test\nlet probe () =\n    let cts = new System.Threading.CancellationTokenSource()\n    cts.CancelAfter 100\n    cts.IsCancellationRequested"

[<Fact>]
let ``a unit Start call on any disposable refuses the fix`` () =
    let s =
        expectNoFix "c" (types + "let run () =\n    let c = new Conn()\n    c.Start()\n    1")

    Assert.Equal(Some UseBinding.Destination.SelfActive, s.Destination)

// ---- A1: wrappers over a foreign resource ----

[<Fact>]
let ``a reader over a constructor parameter is not the scope's to dispose`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype LineSource(stream: Stream) =\n    member _.Next() =\n        let r = new StreamReader(stream)\n        r.ReadLine()"
    )

[<Fact>]
let ``a client over an injected handler is not the scope's to dispose`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.Net.Http\ntype Api(handler: HttpMessageHandler) =\n    member _.Get(url: string) =\n        let client = new HttpClient(handler)\n        let s = client.GetStringAsync(url).Result\n        s.Length"
    )

[<Fact>]
let ``a wrapper over a class field, a module value, a property or a record field is not the scope's`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Source(path: string) =\n    let stream = File.OpenRead path\n    member _.Next() =\n        let r = new StreamReader(stream)\n        r.ReadLine()"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private shared = File.OpenRead \"x\"\nlet next () =\n    let r = new StreamReader(shared)\n    r.ReadLine()"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Holder() =\n    member val Input: Stream = null with get, set\n    member this.Next() =\n        let r = new StreamReader(this.Input)\n        r.ReadLine()"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Cfg = { Input: Stream }\nlet next (cfg: Cfg) =\n    let r = new StreamReader(cfg.Input)\n    r.ReadLine()"
    )

[<Fact>]
let ``a wrapper inside a lambda over a stream the function opened is not the lambda's`` () =
    // the stream is shared by every call of the lambda; the first `use`
    // would close it under the rest
    let suggestions =
        useBindingsIn
            "module Test\nopen System.IO\nlet lines (path: string) (keys: string list) =\n    let s = File.OpenRead path\n    keys |> List.map (fun k ->\n        let r = new StreamReader(s)\n        r.ReadLine() + k)"

    Assert.DoesNotContain(suggestions, fun s -> s.Name = "r")

[<Fact>]
let ``compression and crypto streams over a caller's stream are not the scope's`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nopen System.IO.Compression\nlet inflate (input: Stream) =\n    let z = new GZipStream(input, CompressionMode.Decompress)\n    z.ReadByte()"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nopen System.Security.Cryptography\nlet encrypt (output: Stream) (aes: Aes) =\n    let cs = new CryptoStream(output, aes.CreateEncryptor(), CryptoStreamMode.Write)\n    cs.WriteByte 1uy"
    )

[<Fact>]
let ``a wrapper over a stream this scope opened, a path or a locally built handler still gets use`` () =
    expectFix
        "r"
        "module Test\nopen System.IO\nlet read (path: string) =\n    let s = File.OpenRead path\n    let r = new StreamReader(s)\n    r.ReadToEnd()"

    expectFix
        "w"
        "module Test\nopen System.IO\nlet write (path: string) =\n    let w = new StreamWriter(path, false, System.Text.Encoding.UTF8)\n    w.Write \"x\""

    expectFix
        "client"
        "module Test\nopen System.Net.Http\nlet get (url: string) =\n    let handler = new HttpClientHandler()\n    let client = new HttpClient(handler)\n    let s = client.GetStringAsync(url).Result\n    s.Length"

// ---- B4: a computation expression whose builder has no Using ----

[<Fact>]
let ``a let inside a builder without Using refuses the fix`` () =
    let s =
        expectNoFix
            "s"
            "module Test\ntype MaybeBuilder() =\n    member _.Bind(m, f) = Option.bind f m\n    member _.Return x = Some x\nlet maybe = MaybeBuilder()\nlet firstByte (path: string) (probe: int64 -> int option) =\n    maybe {\n        let s = new System.IO.FileStream(path, System.IO.FileMode.Open)\n        let! n = probe s.Length\n        return n\n    }"

    Assert.Equal(Some UseBinding.Destination.NoBuilderUsing, s.Destination)
    Assert.Contains("no 'Using'", UseBinding.describeEscape s)

[<Fact>]
let ``a let inside a builder with Using, or a core builder, still gets use`` () =
    expectFix
        "s"
        "module Test\ntype MaybeBuilder() =\n    member _.Bind(m, f) = Option.bind f m\n    member _.Return x = Some x\n    member _.Using(r: 'r, f: 'r -> 'a option) : 'a option when 'r :> System.IDisposable =\n        try f r finally r.Dispose()\nlet maybe = MaybeBuilder()\nlet firstByte (path: string) (probe: int64 -> int option) =\n    maybe {\n        let s = new System.IO.FileStream(path, System.IO.FileMode.Open)\n        let! n = probe s.Length\n        return n\n    }"

    expectFix
        "s"
        "module Test\nlet firstByte (path: string) (probe: int64 -> Async<int>) =\n    async {\n        let s = new System.IO.FileStream(path, System.IO.FileMode.Open)\n        let! n = probe s.Length\n        return n\n    }"

    expectFix
        "s"
        "module Test\nlet bytes (path: string) =\n    seq {\n        let s = new System.IO.FileStream(path, System.IO.FileMode.Open)\n        yield s.ReadByte()\n    }"

[<Fact>]
let ``a let inside a local function inside such a builder is ordinary code`` () =
    expectFix
        "s"
        "module Test\ntype MaybeBuilder() =\n    member _.Bind(m, f) = Option.bind f m\n    member _.Return x = Some x\nlet maybe = MaybeBuilder()\nlet firstByte (path: string) =\n    maybe {\n        let size (p: string) =\n            let s = new System.IO.FileStream(p, System.IO.FileMode.Open)\n            s.Length\n        return size path\n    }"

// ---- a lazy body runs after the scope ----

[<Fact>]
let ``a disposable read inside a returned lazy refuses the fix`` () =
    expectNoFix
        "s"
        "module Test\nlet deferred (path: string) =\n    let s = new System.IO.FileStream(path, System.IO.FileMode.Open)\n    lazy (s.ReadByte())"
    |> ignore
