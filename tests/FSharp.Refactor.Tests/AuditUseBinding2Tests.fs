/// FR0075 (UseBinding) escape shapes from the 0.8.11 real-repo sweep (A6,
/// A7): a wrapper over a LOCAL stream that itself escapes the scope
/// (Giraffe's tests store the MemoryStream under a StreamWriter in
/// `ctx.Request.Body` and return a `task { }` that reads it), and a
/// Task/Async-returning member of the disposable whose result is dropped
/// while the work runs (FsCheck's `testCase.RunAsync(...) |> Async.AwaitTask
/// |> ignore`). Each shape refuses the `let` -> `use` fix; the safe shape
/// beside it still gets one, and the patched source typechecks.
module FSharp.Refactor.Tests.AuditUseBinding2Tests

open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open Xunit

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

/// No fix for `name`: either nothing is said (the wrapper counts as
/// foreign) or an advisory without a fix.
let private expectNoFixFor (name: string) (source: string) =
    match useBindingsIn source |> List.filter (fun s -> s.Name = name) with
    | [] -> ()
    | [ s ] -> Assert.True(s.Fix.IsNone, $"Expected no fix for '%s{name}', got %A{s}")
    | other -> failwithf "Expected at most one suggestion for '%s', got %A" name other

/// Exactly one advisory for `name`, without a fix.
let private expectAdvisory (name: string) (source: string) =
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

// ---- A6: a wrapper over a local stream that escapes ----

// a request whose body is read by a task after the handler has returned
[<Literal>]
let private request =
    "module Test
open System
open System.IO
open System.Threading.Tasks
type Request() =
    member val Body: Stream = null with get, set
let handle (req: Request) : Task<string> =
    task {
        do! Task.Yield()
        use r = new StreamReader(req.Body)
        return! r.ReadToEndAsync()
    }
let send (s: Stream) = s.Length
"

[<Fact>]
let ``a writer over a local stream stored in a request body read by the returned task refuses the fix`` () =
    // the Giraffe shape (HttpHandlerTests.fs / ModelBindingTests.fs): the
    // writer's Dispose closes the stream, which the task reads after the
    // function has returned
    expectNoFixFor
        "writer"
        (request
         + "let post (req: Request) =
    let stream = new MemoryStream()
    let writer = new StreamWriter(stream, Text.Encoding.UTF8)
    writer.Write \"payload\"
    writer.Flush()
    stream.Position <- 0L
    req.Body <- stream
    task {
        let! body = handle req
        return body.Length
    }")

[<Fact>]
let ``a writer over a local stream aliased into a local the returned task reads refuses the fix`` () =
    // the fsi repro's shape: `let body : Stream = stream` stands in for the
    // request body
    expectNoFixFor
        "writer"
        (request
         + "let post () =
    let stream = new MemoryStream()
    let writer = new StreamWriter(stream, Text.Encoding.UTF8)
    writer.Write \"payload\"
    writer.Flush()
    stream.Position <- 0L
    let body : Stream = stream
    task {
        do! Task.Yield()
        use r = new StreamReader(body)
        return! r.ReadToEndAsync()
    }")

[<Fact>]
let ``a writer over a local stream that is returned, handed on or captured refuses the fix`` () =
    // returned: the caller reads a closed stream
    expectNoFixFor
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    ms.Position <- 0L
    ms")

    // returned through an upcast
    expectNoFixFor
        "w"
        (request
         + "let build (x: string) : Stream =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    ms :> Stream")

    // handed to a function whose ownership is unknown
    expectNoFixFor
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    send ms")

    // captured by a lambda the scope returns
    expectNoFixFor
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    fun () -> ms.ToArray()")

    // read directly by the returned task
    expectNoFixFor
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    task {
        do! Task.Yield()
        return ms.ToArray()
    }")

[<Fact>]
let ``a writer over a local stream stored in a request body inside the task body refuses the fix too`` () =
    // Giraffe's JsonTests/XmlTests shape: correct in practice (the reads
    // happen inside the block), but the stream still escapes into the
    // request — withheld rather than guessed
    expectNoFixFor
        "writer"
        (request
         + "let post (req: Request) =
    task {
        let stream = new MemoryStream()
        let writer = new StreamWriter(stream, Text.Encoding.UTF8)
        writer.Write \"payload\"
        writer.Flush()
        stream.Position <- 0L
        req.Body <- stream
        let! body = handle req
        return body.Length
    }")

[<Fact>]
let ``a writer over a local stream consumed in the scope still gets use`` () =
    // the buffer is copied out before the scope ends: the wrapper's
    // Dispose closes a stream nobody needs any more
    expectFix
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    ms.ToArray()")

    // a property set and a plain-valued read of the stream keep it here
    expectFix
        "w"
        (request
         + "let build (x: string) =
    let ms = new MemoryStream()
    let w = new StreamWriter(ms)
    w.Write x
    w.Flush()
    ms.Position <- 0L
    let n = ms.Length
    ms.ToArray().Length + int n")

[<Fact>]
let ``a writer over a local stream already use-bound still gets use whatever the stream does`` () =
    // `use stream` closes the stream at scope exit anyway; the wrapper's
    // `use` only adds a flush before that
    expectFix
        "writer"
        (request
         + "let post (req: Request) =
    use stream = new MemoryStream()
    let writer = new StreamWriter(stream, Text.Encoding.UTF8)
    writer.Write \"payload\"
    writer.Flush()
    stream.Position <- 0L
    req.Body <- stream
    int stream.Length")

// ---- A7: a Task/Async-returning member whose result is dropped ----

[<Literal>]
let private runner =
    "module Test
open System
open System.Threading.Tasks
type Runner() =
    member _.RunAsync(n: int) : Task<int> = Task.FromResult n
    member _.Run(n: int) : Task = Task.CompletedTask
    member _.Work(n: int) : Async<int> = async { return n }
    member _.Count = 1
    interface IDisposable with
        member _.Dispose() = ()
"

[<Fact>]
let ``a task from the binder dropped through Async.AwaitTask and ignore refuses the fix`` () =
    // FsCheck's Runner.fs: `testCase.RunAsync(...) |> Async.AwaitTask |> ignore`
    let s =
        expectAdvisory
            "tc"
            (runner
             + "let check () =
    let tc = new Runner()
    tc.RunAsync(1) |> Async.AwaitTask |> ignore
    tc.Count")

    Assert.Equal(Some(UseBinding.Destination.InFlight "RunAsync"), s.Destination)
    Assert.Contains("'RunAsync'", UseBinding.describeEscape s)
    Assert.Contains("still be running", UseBinding.describeEscape s)

[<Fact>]
let ``a task dropped bare, piped to ignore or applied to ignore refuses the fix`` () =
    expectAdvisory
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    tc.RunAsync(1) |> ignore
    tc.Count")
    |> ignore

    expectAdvisory
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    ignore (tc.RunAsync 1)
    tc.Count")
    |> ignore

    // a bare statement of Task type (FS0020 warns, the work still runs)
    expectAdvisory
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    tc.Run 1
    tc.Count")
    |> ignore

    // a generic method: the type application sits between the mention
    // and the call
    expectAdvisory
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    tc.RunAsync(1) |> Async.AwaitTask |> Async.Ignore |> ignore
    tc.Count")
    |> ignore

[<Fact>]
let ``an async from the binder started and forgotten refuses the fix; one never started is fine`` () =
    let s =
        expectAdvisory
            "tc"
            (runner
             + "let check () =
    let tc = new Runner()
    tc.Work 1 |> Async.Ignore |> Async.Start
    tc.Count")

    Assert.Equal(Some(UseBinding.Destination.InFlight "Work"), s.Destination)

    expectAdvisory
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    Async.StartAsTask(tc.Work 1) |> ignore
    tc.Count")
    |> ignore

    // an Async that is never started does no work: nothing is in flight
    expectFix
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    tc.Work 1 |> ignore
    tc.Count")

[<Fact>]
let ``an awaited, waited or synchronously run result still gets use`` () =
    expectFix
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    tc.RunAsync(1).Wait()
    tc.Count")

    expectFix
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    let n = tc.RunAsync(1).Result
    n + tc.Count")

    expectFix
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    let n = tc.RunAsync(1) |> Async.AwaitTask |> Async.RunSynchronously
    n + tc.Count")

    expectFix
        "tc"
        (runner
         + "let check () =
    let tc = new Runner()
    let n = tc.Work 1 |> Async.RunSynchronously
    n + tc.Count")

    expectFix
        "tc"
        (runner
         + "let check () =
    task {
        let tc = new Runner()
        let! n = tc.RunAsync 1
        do! tc.Run 1
        return n + tc.Count
    }")
