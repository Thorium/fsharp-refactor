[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.AsyncPerfRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0049 SyncOverAsync ----

let private blockingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SyncOverAsync.find tree sourceText checkResults

[<Fact>]
let ``Result inside a task is flagged`` () =
    match blockingIn "let f (t: System.Threading.Tasks.Task<int>) = task { return t.Result + 1 }" with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.TaskResult, s.Kind)
        Assert.Equal(Some "task", s.Builder)
    | other -> failwithf "Expected exactly one Result site, got %A" other

[<Fact>]
let ``Wait inside an async is flagged`` () =
    match blockingIn "let f (t: System.Threading.Tasks.Task) = async { t.Wait() }" with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected exactly one Wait site, got %A" other

[<Fact>]
let ``a wait in a thread-choreographed function gets no boundary note`` () =
    // the body hands work to a thread and waits on a signal; "wrap it in
    // task { }" is the advice FR0142 refuses for the same body
    Assert.Empty(
        blockingIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let f () =
                    let signal = new ManualResetEventSlim(false)
                    let worker = Task.Run(fun () -> signal.Set())
                    signal.Wait()
                    worker.Wait()
                """
        )
    )

    // the same wait without the choreography keeps its note
    match
        blockingIn (
            fsharp
                """
                open System.Threading.Tasks
                let g () =
                    let worker = Task.Run(fun () -> 1)
                    worker.Wait()
                """
        )
    with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected exactly one boundary Wait site, got %A" other

[<Fact>]
let ``GetResult outside any CE is still an antipattern`` () =
    match blockingIn "let f (t: System.Threading.Tasks.Task<int>) = t.GetAwaiter().GetResult()" with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.AwaiterGetResult, s.Kind)
        Assert.Equal(None, s.Builder)
    | other -> failwithf "Expected exactly one boundary GetResult site, got %A" other

[<Fact>]
let ``RunSynchronously inside a task is flagged`` () =
    match blockingIn "let f (comp: Async<int>) = task { return (comp |> Async.RunSynchronously) }" with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.RunSynchronously, s.Kind)
    | other -> failwithf "Expected exactly one RunSynchronously site, got %A" other

[<Fact>]
let ``Thread Sleep in an async gets the Async Sleep fix`` () =
    match
        blockingIn (
            fsharp
                """
                let f () = async {
                    System.Threading.Thread.Sleep 100
                    return 1
                }
                """
        )
    with
    | [ s ] ->
        match s.Fixes with
        | [ (r, _, replacement) ] ->
            Assert.Equal("do! Async.Sleep 100", replacement)

            let source =
                fsharp
                    """
                    let f () = async {
                        System.Threading.Thread.Sleep 100
                        return 1
                    }
                    """

            let patched = applyEdit source r replacement
            assertTypechecks "Patched source" patched
        | _ -> failwith "Expected a fix for Thread.Sleep"
    | other -> failwithf "Expected exactly one Sleep site, got %A" other

[<Fact>]
let ``Thread Sleep in sync code is legitimate`` () =
    Assert.Empty(blockingIn "let f () = System.Threading.Thread.Sleep 100")

[<Fact>]
let ``a user type with a Result property is not a task`` () =
    Assert.Empty(
        blockingIn (
            fsharp
                """
                type R() =
                    member _.Result = 1
                let f (r: R) = task { return r.Result }
                """
        )
    )

[<Fact>]
let ``binding with let-bang is fine`` () =
    Assert.Empty(
        blockingIn (
            fsharp
                """
                let f (t: System.Threading.Tasks.Task<int>) = task {
                    let! x = t
                    return x
                }
                """
        )
    )

// ---- FR0050 / FR0051 Accumulation ----

let private accumulationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.find tree sourceText checkResults

let private assertFold (source: string) (expectedReplacement: string) =
    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``sum accumulation becomes Seq sum`` () =
    // a FLOAT accumulator: List.sum adds checked, so only the floating
    // types compute what the loop computed (AuditSemanticATests has the
    // integer shape, which keeps the fold)
    assertFold
        (fsharp
            """
            let f (xs: float list) =
                let mutable total = 0.0
                for x in xs do
                    total <- total + x
                total * 2.0
            """)
        "let total = xs |> List.sum"

[<Fact>]
let ``projected sum becomes sumBy`` () =
    assertFold
        (fsharp
            """
            let f (xs: float list) =
                let mutable total = 0.0
                for x in xs do
                    total <- total + x * x
                total
            """)
        "xs |> List.sumBy (fun x -> x * x)"

[<Fact>]
let ``general combine becomes a fold`` () =
    assertFold
        (fsharp
            """
            let f (xs: int list) =
                let mutable best = 1
                for x in xs do
                    best <- max best (x % 7)
                best
            """)
        "xs |> List.fold (fun best x -> max best (x % 7)) 1"

[<Fact>]
let ``reassignment after the loop keeps the mutable`` () =
    let folds, _ =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable total = 0
                    for x in xs do
                        total <- total + x
                    total <- total + 1
                    total
                """
        )

    Assert.Empty folds

[<Fact>]
let ``counting a non-generic IEnumerable stays a loop`` () =
    // from the corpus (SQLProvider SeqValues): `for` accepts the non-generic
    // IEnumerable, Seq.sumBy needs seq<'T> — the rewrite would be FS0001
    let folds, _ =
        accumulationIn (
            fsharp
                """
                let f (values: System.Collections.IEnumerable) =
                    let mutable count = 0
                    for v in values do
                        count <- count + 1
                    count
                """
        )

    Assert.Empty folds

[<Fact>]
let ``quadratic list append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable acc: int list = []
                    for x in xs do
                        if x > 0 then acc <- acc @ [ x ]
                    acc
                """
        )

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one quadratic note, got %A" other

[<Fact>]
let ``quadratic Array append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable acc: int[] = [||]
                    for x in xs do
                        if x > 0 then acc <- Array.append acc [| x |]
                    acc
                """
        )

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one Array-append note, got %A" other

// ---- FR0107 FlagLoop ----

let private flagLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.findFlagLoops tree sourceText checkResults

let private assertFlagRewrite (source: string) (expectedReplacement: string) =
    match flagLoopsIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one flag-loop suggestion, got %A" other

[<Fact>]
let ``a false flag set in a loop becomes exists`` () =
    assertFlagRewrite
        (fsharp
            """
            let f (xs: int list) =
                let mutable found = false
                for x in xs do
                    if x > 3 then found <- true
                found
            """)
        "let found = xs |> List.exists (fun x -> x > 3)"

[<Fact>]
let ``an array source resolves to Array exists`` () =
    assertFlagRewrite
        (fsharp
            """
            let f (xs: int[]) =
                let mutable found = false
                for x in xs do
                    if x > 3 then found <- true
                found
            """)
        "let found = xs |> Array.exists (fun x -> x > 3)"

[<Fact>]
let ``a true flag falsified in a loop becomes forall`` () =
    assertFlagRewrite
        (fsharp
            """
            let f (xs: int list) =
                let mutable ok = true
                for x in xs do
                    if x < 0 then ok <- false
                ok
            """)
        "let ok = xs |> List.forall (fun x -> not (x < 0))"

[<Fact>]
let ``a negated predicate in the forall dual loses its not`` () =
    // a core-operator predicate: a user function (`valid x`) would run
    // fewer times under forall's short-circuit and keeps the loop
    assertFlagRewrite
        (fsharp
            """
            let f (xs: int list) =
                let mutable ok = true
                for x in xs do
                    if not (x >= 0) then ok <- false
                ok
            """)
        "let ok = xs |> List.forall (fun x -> (x >= 0))"

[<Fact>]
let ``a second statement in the loop body keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable found = false
                    let mutable count = 0
                    for x in xs do
                        count <- count + 1
                        if x > 3 then found <- true
                    found
                """
        )
    )

[<Fact>]
let ``a side-effecting predicate keeps the mutable`` () =
    // exists short-circuits — a predicate with visible effects would run
    // fewer times after the rewrite
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable found = false
                    let mutable seen = 0
                    for x in xs do
                        if (seen <- seen + 1; x > 3) then found <- true
                    found, seen
                """
        )
    )

[<Fact>]
let ``an else branch keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let g () = ()
                let f (xs: int list) =
                    let mutable found = false
                    for x in xs do
                        if x > 3 then found <- true else g ()
                    found
                """
        )
    )

[<Fact>]
let ``flag reassignment after the loop keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable found = false
                    for x in xs do
                        if x > 3 then found <- true
                    found <- found && xs.Length > 1
                    found
                """
        )
    )

[<Fact>]
let ``a predicate reading the flag keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable found = false
                    for x in xs do
                        if not found && x > 3 then found <- true
                    found
                """
        )
    )

[<Fact>]
let ``a non-generic IEnumerable source keeps the mutable`` () =
    // `for` accepts it; List/Array/Seq.exists do not
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (values: System.Collections.IEnumerable) =
                    let mutable found = false
                    for v in values do
                        if hash v > 3 then found <- true
                    found
                """
        )
    )

// ---- FR0052 CountIsEmpty ----

let private countsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CountIsEmpty.find tree sourceText checkResults

[<Fact>]
let ``ConcurrentQueue Count equals zero becomes IsEmpty`` () =
    match countsIn "let f (q: System.Collections.Concurrent.ConcurrentQueue<int>) = q.Count = 0" with
    | [ s ] -> Assert.Equal("q.IsEmpty", s.ReplacementText)
    | other -> failwithf "Expected exactly one IsEmpty suggestion, got %A" other

[<Fact>]
let ``Count greater than zero negates IsEmpty`` () =
    match countsIn "let f (q: System.Collections.Concurrent.ConcurrentQueue<int>) = q.Count > 0" with
    | [ s ] -> Assert.Equal("not q.IsEmpty", s.ReplacementText)
    | other -> failwithf "Expected exactly one negated suggestion, got %A" other

[<Fact>]
let ``a List Count is a cheap field and fine`` () =
    Assert.Empty(countsIn "let f (xs: ResizeArray<int>) = xs.Count = 0")

// ---- FR0053 HexString ----

let private hexIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    HexString.find tree sourceText checkResults

[<Fact>]
let ``dash-stripped BitConverter chain becomes ToHexString`` () =
    match
        hexIn (
            fsharp
                """
                module Test
                let f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace("-", "")
                """
        )
    with
    | [ s ] -> Assert.Equal("System.Convert.ToHexString bytes", s.ReplacementText)
    | other -> failwithf "Expected exactly one hex suggestion, got %A" other


[<Fact>]
let ``a trailing member access keeps the call parenthesised`` () =
    // prismatic: the space form left `ToHexString hash.Substring(0, 16)`,
    // handing the substring OF THE BYTES to ToHexString
    let source =
        fsharp
            """
            module Test
            let f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace("-", "").Substring(0, 16)
            """

    match hexIn source with
    | [ s ] ->
        Assert.Equal("(System.Convert.ToHexString bytes)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one hex suggestion, got %A" other

[<Fact>]

let ``other Replace arguments are left alone`` () =
    Assert.Empty(
        hexIn (
            fsharp
                """
                module Test
                let f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace("-", ":")
                """
        )
    )

// ---- FR0055 SwallowedException ----

let private swallowedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SwallowedException.find tree sourceText (Some checkResults)

[<Fact>]
let ``empty wildcard catch is noted`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let f (act: unit -> unit) =
                    try act ()
                    with _ -> ()
                """
        )
    with
    | [ s ] -> Assert.Equal("_", s.PatternText)
    | other -> failwithf "Expected exactly one swallow note, got %A" other

[<Fact>]
let ``empty typed Exception catch is noted`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let f (act: unit -> unit) =
                    try act ()
                    with :? System.Exception -> ()
                """
        )
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one typed swallow note, got %A" other

[<Fact>]
let ``handler that does something is fine`` () =
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (act: unit -> unit) =
                    try act ()
                    with ex -> printfn "%s" ex.Message
                """
        )
    )

[<Fact>]
let ``deliberately ignoring a specific exception is fine`` () =
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (act: unit -> unit) =
                    try act ()
                    with :? System.OperationCanceledException -> ()
                """
        )
    )

[<Fact>]
let ``a catch-all after a rethrown cancellation is not blind`` () =
    // the compiler's NameResolution: `:? OperationCanceledException ->
    // reraise ()` first, then `_ -> None`
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (act: unit -> int) =
                    try
                        Some(act ())
                    with
                    | :? System.OperationCanceledException -> reraise ()
                    | _ -> None
                """
        )
    )

[<Fact>]
let ``a catch-all followed by an unconditional failure converts the swallow into a failure`` () =
    // DiagnosticsLogger's exiter: `try Environment.Exit n with _ -> ()`
    // and then a failwith — the exception is replaced, not lost
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let exit (n: int) : int =
                    try
                        System.Environment.Exit n
                    with _ ->
                        ()

                    failwith "exit did not exit"
                """
        )
    )

[<Fact>]
let ``a one-call teardown body is the best-effort release idiom`` () =
    // Suave's `try acceptSocket.Shutdown ... with _ -> ()`, `try
    // s.Dispose(); s <- null with _ -> ()`, `try File.Delete p with _ -> ()`
    let teardownOf (source: string) =
        match swallowedIn source with
        | [ s ] -> s.Teardown
        | other -> failwithf "Expected exactly one swallow note, got %A" other

    Assert.True(
        teardownOf (
            fsharp
                """
                module Test
                let close (s: System.IO.Stream) =
                    try s.Dispose() with _ -> ()
                """
        )
    )

    Assert.True(
        teardownOf (
            fsharp
                """
                module Test
                type T() =
                    let mutable s: System.IO.Stream = null
                    member _.Close() =
                        try
                            s.Dispose()
                            s <- null
                        with _ -> ()
                """
        )
    )

    Assert.True(
        teardownOf (
            fsharp
                """
                module Test
                let cleanup (p: string) =
                    try System.IO.File.Delete p with ex -> ()
                """
        )
    )

    // a call to anything else is a swallow around real work
    Assert.False(
        teardownOf (
            fsharp
                """
                module Test
                let f (act: unit -> unit) =
                    try act () with _ -> ()
                """
        )
    )

    Assert.False(
        teardownOf (
            fsharp
                """
                module Test
                let f (s: System.IO.Stream) (bytes: byte[]) =
                    try s.Write(bytes, 0, bytes.Length) with _ -> ()
                """
        )
    )

[<Fact>]
let ``a fallback that is a variable, a sentinel or a tuple carrying a default disguises the failure`` () =
    // fsi: `with _ -> path`, `with _ -> (istate, Completed None)`; fsdocs:
    // `with _ -> DateTime.MaxValue`, `with _ -> Int32.MaxValue`
    let fallbackOf (source: string) =
        match swallowedIn source with
        | [ s ] -> s.FallbackText
        | other -> failwithf "Expected exactly one swallow note, got %A" other

    Assert.Equal(
        Some "path",
        fallbackOf (
            fsharp
                """
                module Test
                let create (path: string) =
                    try
                        System.IO.Directory.CreateDirectory path |> ignore
                        path
                    with _ ->
                        path
                """
        )
    )

    Assert.Equal(
        Some "(state, Completed None)",
        fallbackOf (
            fsharp
                """
                module Test
                type Step =
                    | Completed of int option
                let run (state: int) (f: int -> int * Step) =
                    try f state
                    with _ -> (state, Completed None)
                """
        )
    )

    Assert.Equal(
        Some "System.Int32.MaxValue",
        fallbackOf (
            fsharp
                """
                module Test
                let index (s: string) =
                    try int32 s
                    with _ -> System.Int32.MaxValue
                """
        )
    )

    Assert.Equal(
        Some "System.DateTime.MaxValue",
        fallbackOf (
            fsharp
                """
                module Test
                let stamp (p: string) =
                    try
                        let fi = System.IO.FileInfo p
                        System.IO.File.GetLastWriteTime fi.FullName
                    with _ ->
                        System.DateTime.MaxValue
                """
        )
    )

    // a tuple of plain names carries no default: it is a computed answer
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let run (state: int) (other: int) (f: int -> int * int) =
                    try f state
                    with _ -> (state, other)
                """
        )
    )

[<Fact>]
let ``a guard that never looks at the exception still swallows every one`` () =
    // fsdocs: `with _ when watch -> ()`
    match
        swallowedIn (
            fsharp
                """
                module Test
                let copy (watch: bool) (src: string) (dst: string) =
                    try System.IO.File.Copy(src, dst, true)
                    with _ when watch -> ()
                """
        )
    with
    | [ s ] -> Assert.Equal("_ when watch", s.PatternText)
    | other -> failwithf "Expected exactly one guarded swallow note, got %A" other

    // a guard on the exception itself is a decision
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let copy (src: string) (dst: string) =
                    try System.IO.File.Copy(src, dst, true)
                    with ex when ex.Message.Contains "locked" -> ()
                """
        )
    )

[<Fact>]
let ``a try around a probe that answers for a missing path should go`` () =
    // fsdocs: `try File.Exists p with _ -> false`, `try File.GetLastWriteTime
    // p with _ -> DateTime.MaxValue`
    let probeOf (source: string) =
        match swallowedIn source with
        | [ s ] -> s.Probe
        | other -> failwithf "Expected exactly one swallow note, got %A" other

    Assert.Equal(
        Some "File.Exists",
        probeOf (
            fsharp
                """
                module Test
                let has (p: string) =
                    try System.IO.File.Exists p
                    with _ -> false
                """
        )
    )

    Assert.Equal(
        Some "Directory.Exists",
        probeOf (
            fsharp
                """
                module Test
                let has (p: string) =
                    (try
                        System.IO.Directory.Exists(p)
                     with _ ->
                        false)
                """
        )
    )

    Assert.Equal(
        Some "File.GetLastWriteTime",
        probeOf (
            fsharp
                """
                module Test
                let stamp (p: string) =
                    try System.IO.File.GetLastWriteTime p
                    with _ -> System.DateTime.MaxValue
                """
        )
    )

    // a body doing more than the probe is not a probe
    Assert.Equal(
        None,
        probeOf (
            fsharp
                """
                module Test
                let stamp (p: string) =
                    try
                        let fi = System.IO.FileInfo p
                        System.IO.File.GetLastWriteTime fi.FullName
                    with _ ->
                        System.DateTime.MaxValue
                """
        )
    )

// ---- FR0054 RaiseInSpecialMember ----

let private objectRulesIn (source: string) =
    let tree, sourceText = parse source
    ObjectRules.find tree sourceText

[<Fact>]
let ``failwith inside GetHashCode is noted`` () =
    let _, _, raises =
        objectRulesIn (
            fsharp
                """
                module Test
                type T() =
                    override _.Equals(o) = false
                    override _.GetHashCode() = failwith "no hash"
                """
        )

    match raises with
    | [ s ] -> Assert.Equal("GetHashCode", s.MemberName)
    | other -> failwithf "Expected exactly one raise-in-special note, got %A" other

[<Fact>]
let ``ToString returning a value is fine`` () =
    let _, _, raises =
        objectRulesIn (
            fsharp
                """
                module Test
                type T() =
                    override _.ToString() = "t"
                """
        )

    Assert.Empty raises

[<Fact>]
let ``FR0054: a Dispose that catches its own flush failure throws nothing to its caller`` () =
    // the raise sits under a try/with inside the member: the member handles
    // it, so nothing escapes into the using block that disposes it
    let _, _, raises =
        objectRulesIn (
            fsharp
                """
                module Test
                type Session(conn: System.IO.Stream) =
                    interface System.IDisposable with
                        member _.Dispose() =
                            try
                                if not conn.CanWrite then failwith "stream already closed"
                                conn.Flush()
                            with ex ->
                                eprintfn "flush on dispose failed: %s" ex.Message
                """
        )

    Assert.Empty raises

// ---- FR0058 RecursiveSeq ----

let private recursiveSeqIn (source: string) =
    let tree, sourceText = parse source
    RecursiveSeq.find tree sourceText

[<Fact>]
let ``a rec function yielding itself through seq is noted`` () =
    match
        recursiveSeqIn (
            fsharp
                """
                module Test
                let rec countDown n = seq {
                    yield n
                    if n > 0 then yield! countDown (n - 1)
                    yield -1
                }
                """
        )
    with
    | [ s ] ->
        Assert.Equal("countDown", s.FunctionName)
        Assert.Equal("seq", s.Builder)
    | other -> failwithf "Expected exactly one recursive-seq note, got %A" other

[<Fact>]
let ``self-reference via Seq collect inside the seq is also caught`` () =
    match
        recursiveSeqIn (
            fsharp
                """
                module Test
                let rec walk (xs: int list list) = seq {
                    yield xs.Length
                    yield! Seq.collect walk []
                }
                """
        )
    with
    | [ s ] -> Assert.Equal("walk", s.FunctionName)
    | other -> failwithf "Expected exactly one collect-form note, got %A" other

[<Fact>]
let ``a non-recursive seq is fine`` () =
    Assert.Empty(
        recursiveSeqIn (
            fsharp
                """
                module Test
                let numbers n = seq {
                    for i in 1..n do
                        yield i * i
                }
                """
        )
    )

[<Fact>]
let ``recursion outside any seq is fine`` () =
    Assert.Empty(
        recursiveSeqIn (
            fsharp
                """
                module Test
                let rec fact n = if n <= 1 then 1 else n * fact (n - 1)
                let s = seq { yield 1 }
                """
        )
    )

// ---- FR0057 XmlDocParams ----

let private xmlDocsIn (source: string) =
    let tree, sourceText = parse source
    XmlDocParams.find tree sourceText

[<Fact>]
let ``a missing param tag is noted`` () =
    match
        xmlDocsIn (
            fsharp
                """
                module Test
                /// <summary>Scales.</summary>
                /// <param name="value">The value.</param>
                let scale (value: int) (factor: int) = value * factor
                """
        )
    with
    | [ s ] ->
        Assert.Equal("scale", s.BindingName)
        Assert.Equal<string list>([ "factor" ], s.MissingParams)
    | other -> failwithf "Expected exactly one doc-drift note, got %A" other

[<Fact>]
let ``fully documented parameters are fine`` () =
    Assert.Empty(
        xmlDocsIn (
            fsharp
                """
                module Test
                /// <summary>Scales.</summary>
                /// <param name="value">The value.</param>
                /// <param name="factor">The factor.</param>
                let scale (value: int) (factor: int) = value * factor
                """
        )
    )

[<Fact>]
let ``undocumented functions are a style choice`` () =
    Assert.Empty(
        xmlDocsIn (
            fsharp
                """
                module Test
                /// Scales a value.
                let scale (value: int) (factor: int) = value * factor
                """
        )
    )

[<Fact>]
let ``a custom operation documents the DSL keyword not the signature`` () =
    Assert.Empty(
        xmlDocsIn (
            fsharp
                """
                module Test
                type Cfg() =
                    member _.Yield(_: unit) = 0
                    /// <summary>Sets the width.</summary>
                    /// <param name="w">The width.</param>
                    [<CustomOperation "width">]
                    member _.Width(state: int, w: int) = state + w
                """
        )
    )

[<Fact>]
let ``sync-over-async inside an object expression member is found`` () =
    // corpus regression: Dispose bodies in `{ new IDisposable with ... }`
    // hid GetResult calls from the walker
    match
        blockingIn (
            fsharp
                """
                module Test
                open System
                open System.Threading.Tasks
                let scope (t: Task) =
                    { new IDisposable with
                        member _.Dispose() = t.GetAwaiter().GetResult() }
                """
        )
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one blocking note, got %A" other

[<Fact>]
let ``catch-all substituting an empty string is noted`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let f (read: unit -> string) =
                    try read ()
                    with _ -> ""
                """
        )
    with
    | [ s ] -> Assert.Equal(Some "\"\"", s.FallbackText)
    | other -> failwithf "Expected exactly one fallback note, got %A" other

[<Fact>]
let ``catch-all substituting zero is noted`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let f (count: unit -> int) =
                    try count ()
                    with _ -> 0
                """
        )
    with
    | [ s ] -> Assert.Equal(Some "0", s.FallbackText)
    | other -> failwithf "Expected exactly one zero-fallback note, got %A" other

[<Fact>]
let ``catch-all substituting defaultof is noted`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let f (get: unit -> string) =
                    try get ()
                    with _ -> Unchecked.defaultof<string>
                """
        )
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one defaultof-fallback note, got %A" other

[<Fact>]
let ``the bool probe idiom stays quiet`` () =
    // `try ping (); true with _ -> false` — the failure IS the answer
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let canPing (ping: unit -> unit) =
                    try
                        ping ()
                        true
                    with _ -> false
                """
        )
    )

[<Fact>]
let ``the inverted did-it-throw probe stays quiet too`` () =
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let throws (act: unit -> unit) =
                    try
                        act ()
                        false
                    with _ -> true
                """
        )
    )

[<Fact>]
let ``a false fallback on a non-probe body is a disguise`` () =
    // the body computes a real bool; the catch-all rewrites failure as
    // `false`, indistinguishable from an honest negative
    match
        swallowedIn (
            fsharp
                """
                module Test
                let isValid (parse: string -> bool) (s: string) =
                    try parse s
                    with _ -> false
                """
        )
    with
    | [ s ] -> Assert.Equal(Some "false", s.FallbackText)
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``a ValueNone fallback is a disguise`` () =
    match
        swallowedIn (
            fsharp
                """
                module Test
                let tryRead (read: unit -> int) =
                    try ValueSome(read ())
                    with _ -> ValueNone
                """
        )
    with
    | [ s ] -> Assert.Equal(Some "ValueNone", s.FallbackText)
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``a specific exception with a default is a decision`` () =
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (read: unit -> string) =
                    try read ()
                    with :? System.IO.FileNotFoundException -> ""
                """
        )
    )

[<Fact>]
let ``a string accumulator becomes String.concat, not a quadratic fold`` () =
    let folds, _ =
        accumulationIn (
            fsharp
                """
                module Test
                let joinAll (xs: string list) =
                    let mutable acc = ""
                    for x in xs do
                        acc <- acc + x
                    acc
                """
        )

    match folds with
    | [ s ] -> Assert.Equal("xs |> String.concat \"\"", s.ReplacementText)
    | other -> failwithf "Expected exactly one string-concat fold, got %A" other

[<Fact>]
let ``a projected string accumulator maps then concats`` () =
    let folds, _ =
        accumulationIn (
            fsharp
                """
                module Test
                let render (xs: int list) =
                    let mutable acc = ""
                    for x in xs do
                        acc <- acc + string x
                    acc
                """
        )

    match folds with
    | [ s ] -> Assert.Equal("xs |> List.map (fun x -> string x) |> String.concat \"\"", s.ReplacementText)
    | other -> failwithf "Expected exactly one mapped string concat, got %A" other

[<Fact>]
let ``a non-empty seed prefixes the concatenation`` () =
    let folds, _ =
        accumulationIn (
            fsharp
                """
                module Test
                let render (xs: string list) =
                    let mutable acc = "head:"
                    for x in xs do
                        acc <- acc + x
                    acc
                """
        )

    match folds with
    | [ s ] -> Assert.Equal("\"head:\" + (xs |> String.concat \"\")", s.ReplacementText)
    | other -> failwithf "Expected exactly one seeded string concat, got %A" other

[<Fact>]
let ``ValueTask Result blocks like Task Result`` () =
    // post-core BCL async I/O returns ValueTask everywhere
    let suggestions =
        blockingIn (
            fsharp
                """
                let f (vt: System.Threading.Tasks.ValueTask<int>) =
                    task {
                        return vt.Result
                    }
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskResult, s.Kind)
    | other -> failwithf "Expected exactly one ValueTask.Result note, got %A" other

[<Fact>]
let ``Task WaitAll is a blocking wait too`` () =
    let suggestions =
        blockingIn (
            fsharp
                """
                let f (t1: System.Threading.Tasks.Task) =
                    task {
                        System.Threading.Tasks.Task.WaitAll [| t1 |]
                        return 1
                    }
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected exactly one WaitAll note, got %A" other

[<Fact>]
let ``a Thread.Sleep inside a nested seq gets no do-fix`` () =
    // `do!` in the seq body would call a Bind the seq builder lacks
    let suggestions =
        blockingIn (
            fsharp
                """
                let f () =
                    async {
                        let xs = seq {
                            System.Threading.Thread.Sleep 100
                            yield 1
                        }
                        return Seq.length xs
                    }
                """
        )

    Assert.NotEmpty suggestions
    Assert.True(suggestions |> List.forall (fun s -> s.Fixes.IsEmpty))

[<Fact>]
let ``a field-held concurrent queue count is an emptiness check too`` () =
    let suggestions =
        countsIn (
            fsharp
                """
                type H() =
                    member val Queue = System.Collections.Concurrent.ConcurrentQueue<int>() with get
                    member this.Check() = this.Queue.Count = 0
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("this.Queue.IsEmpty", s.ReplacementText)
    | other -> failwithf "Expected exactly one count note, got %A" other

[<Fact>]
let ``a recursive member yielding itself through seq is noted`` () =
    // members are implicitly recursive — no `rec` keyword to find — and
    // OO-style tree APIs are where recursive seqs live
    let suggestions =
        recursiveSeqIn (
            fsharp
                """
                module Test
                type Node(children: Node list) =
                    member this.Descendants() : seq<int> = seq {
                        yield 1
                        for c in children do
                            yield! c.Descendants()
                    }
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("Descendants", s.FunctionName)
    | other -> failwithf "Expected exactly one recursive-member note, got %A" other

[<Fact>]
let ``quadratic List.append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable acc: int list = []
                    for x in xs do
                        if x > 0 then acc <- List.append acc [ x ]
                    acc
                """
        )

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one List.append note, got %A" other

[<Fact>]
let ``quadratic append through a ref cell is noted`` () =
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let acc = ref ([]: int list)
                    for x in xs do
                        acc.Value <- acc.Value @ [ x ]
                    acc.Value
                """
        )

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one ref-cell note, got %A" other

[<Fact>]
let ``a plain seq source still sums with the Seq module`` () =
    // the module-resolved output names List/Array when it can; a true
    // seq has nothing better than Seq.sum
    assertFold
        (fsharp
            """
            let f (xs: float seq) =
                let mutable total = 0.0
                for x in xs do
                    total <- total + x
                total
            """)
        "xs |> Seq.sum"

[<Fact>]
let ``quadratic string building in a while loop is noted`` () =
    // measured: 57.8µs and 1MB per 1000 pieces against 1.6µs/4.6KB for a
    // StringBuilder — the worst string builder there is
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (next: unit -> string option) =
                    let mutable acc = ""
                    let mutable go = true
                    while go do
                        match next () with
                        | Some s -> acc <- acc + s
                        | None -> go <- false
                    acc
                """
        )

    match quadratics with
    | [ s ] ->
        Assert.Equal("acc", s.Name)
        Assert.Equal(Accumulation.QuadraticKind.Str, s.Kind)
    | other -> failwithf "Expected exactly one string-quadratic note, got %A" other

[<Fact>]
let ``numeric accumulation with plus is ordinary code`` () =
    let _, quadratics =
        accumulationIn (
            fsharp
                """
                let f (next: unit -> int option) =
                    let mutable total = 0
                    let mutable go = true
                    while go do
                        match next () with
                        | Some n -> total <- total + n
                        | None -> go <- false
                    total
                """
        )

    Assert.Empty quadratics

[<Fact>]
let ``the FR0050 string shape gets the fix, not the note`` () =
    // the fold fix rewrites this whole shape into one String.concat; a
    // note on the same site would nag about code the fix removes
    let folds, quadratics =
        accumulationIn (
            fsharp
                """
                let render (xs: int list) =
                    let mutable acc = ""
                    for x in xs do
                        acc <- acc + string x
                    acc
                """
        )

    Assert.Single folds |> ignore
    Assert.Empty quadratics

[<Fact>]
let ``a seq source materializes before String concat`` () =
    // the lazy-seq path through String.concat measured 42.7µs/194KB per
    // 1000 pieces against 2.6µs/2KB once materialized
    assertFold
        (fsharp
            """
            let render (xs: int seq) =
                let mutable acc = ""
                for x in xs do
                    acc <- acc + string x
                acc
            """)
        "xs |> Seq.map (fun x -> string x) |> Seq.toArray |> String.concat \"\""

[<Fact>]
let ``a pure let prefix folds into the exists lambda`` () =
    // the opensSystem shape from our own code review: a let-bound
    // projection before the flag test is still an exists question
    assertFlagRewrite
        (fsharp
            """
            let f (lines: string list) =
                let mutable found = false
                for l in lines do
                    let t = l.Trim()
                    if t = "open System" then found <- true
                found
            """)
        """let found = lines |> List.exists (fun l -> let t = l.Trim() in t = "open System")"""

[<Fact>]
let ``a mutable let in the body keeps the flag loop`` () =
    Assert.Empty(
        flagLoopsIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable found = false
                    for x in xs do
                        let mutable y = x + 1
                        if y > 3 then found <- true
                    found
                """
        )
    )

[<Fact>]
let ``a GetResult binding inside task becomes a let bang bind`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                let x = t.GetAwaiter().GetResult()
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (kwRange, _, "let!"); (rhsRange, _, receiver) ] ->
            Assert.Equal("t", receiver)
            let patched = applyEdit (applyEdit source rhsRange receiver) kwRange "let!"
            Assert.Contains("let! x = t", patched)
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the let!-bind pair, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``a GetResult boundary call swaps to a provable sync sibling`` () =
    // File.ReadAllTextAsync has the synchronous File.ReadAllText sibling
    // with the same argument count — verified via the typed tree
    let source =
        "let f (path: string) = System.IO.File.ReadAllTextAsync(path).GetAwaiter().GetResult()"

    match blockingIn source with
    | [ s ] ->
        // toward-sync is an ALTERNATIVE (editor action / config opt-in),
        // never the auto-applied fix: async-in-sync is usually a waypoint
        // toward full async, and the tool must not walk it backward
        Assert.Empty s.Fixes

        match s.AlternativeFixes with
        | [ (nameRange, "ReadAllTextAsync", "ReadAllText"); (dropRange, _, "") ] ->
            let patched = applyEdit (applyEdit source dropRange "") nameRange "ReadAllText"
            Assert.Contains("System.IO.File.ReadAllText(path)", patched)
            Assert.DoesNotContain("GetAwaiter", patched)
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the sibling swap pair, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``a GetResult call with no sync sibling stays advice`` () =
    // HttpClient has no synchronous GetString — the note must carry no fix
    let source =
        "let f (c: System.Net.Http.HttpClient) (u: string) = c.GetStringAsync(u).GetAwaiter().GetResult()"

    match blockingIn source with
    | [ s ] ->
        Assert.Empty s.Fixes
        Assert.Empty s.AlternativeFixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``draining a plain task value outside a CE stays advice`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = t.GetAwaiter().GetResult()"

    match blockingIn source with
    | [ s ] ->
        Assert.Empty s.Fixes
        Assert.Empty s.AlternativeFixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``a ValueTask GetResult binding inside async is not rewritten`` () =
    // async { } binds a Task via Async.AwaitTask — but AwaitTask has no
    // ValueTask overload, so a ValueTaskAwaiter drain stays advice
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.ValueTask<int>) = async {
                let x = t.GetAwaiter().GetResult()
                return x + 1
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a GetResult binding in a finally block keeps its hands off`` () =
    // let!/do! are illegal inside finally — the pre-existing Sleep fix
    // shared this hole
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                try
                    return 1
                finally
                    let x = t.GetAwaiter().GetResult()
                    ignore x
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``Thread Sleep in a finally block keeps its blocking form`` () =
    let source =
        fsharp
            """
            let f () = task {
                try
                    return 1
                finally
                    System.Threading.Thread.Sleep 100
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a type-annotated GetResult binding stays advice`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                let x: int = t.GetAwaiter().GetResult()
                return x + 1
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

// ---- the bind matrix: {Task, Async} receivers x {task, async} builders ----

let private applyAll (source: string) (fixes: (FSharp.Compiler.Text.range * string * string) list) =
    fixes
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``RunSynchronously binding inside async becomes a native bind`` () =
    let source =
        fsharp
            """
            let f (comp: Async<int>) = async {
                let x = comp |> Async.RunSynchronously
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = comp", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one RunSynchronously site, got %A" other

[<Fact>]
let ``RunSynchronously binding inside task binds the async directly`` () =
    // the task builder's medium-priority overload binds Async<'T> with a
    // plain let! — no StartAsTask adapter needed
    let source =
        fsharp
            """
            let f (comp: Async<int>) = task {
                let x = Async.RunSynchronously comp
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = comp", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one RunSynchronously site, got %A" other

[<Fact>]
let ``RunSynchronously with a timeout tuple stays advice`` () =
    let source =
        fsharp
            """
            let f (comp: Async<int>) = async {
                let x = Async.RunSynchronously(comp, timeout = 100)
                return x + 1
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a GetResult binding inside async binds via AwaitTask`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = async {
                let x = t.GetAwaiter().GetResult()
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = Async.AwaitTask t", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``a Result binding inside task becomes a plain bind`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = task {
                let x = t.Result
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = t", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one Result site, got %A" other

[<Fact>]
let ``a Result binding on a call inside async parenthesizes the AwaitTask arg`` () =
    let source =
        fsharp
            """
            let g () = System.Threading.Tasks.Task.FromResult 2
            let f () = async {
                let x = (g ()).Result
                return x + 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("Async.AwaitTask (", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one Result site, got %A" other

[<Fact>]
let ``a ValueTask Result binding inside async stays advice`` () =
    // Async.AwaitTask has no ValueTask overload — no fix to offer there
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.ValueTask<int>) = async {
                let x = t.Result
                return x + 1
            }
            """

    for s in blockingIn source do
        Assert.Empty s.Fixes

// ---- FR0118 CancellationOverload ----

let private cancellationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CancellationOverload.find tree sourceText checkResults

[<Fact>]
let ``an omitted token is appended from the in-scope parameter`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let pause (ct: CancellationToken) = task {
                do! Task.Delay(100)
                return 1
            }
            """

    match cancellationIn source with
    | [ s ] ->
        Assert.Equal(CancellationOverload.TokenGap.Omitted, s.Kind)
        Assert.Equal(", ct", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("Task.Delay(100, ct)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one token suggestion, got %A" other

let private unobservedLoopsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CancellationOverload.findUnobservedLoops tree sourceText checkResults

[<Fact>]
let ``FR0118: a loop under a token that never reads it is noted once, at the outermost loop`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let pump (ct: CancellationToken) (next: unit -> int option) (handle: int -> Task) = task {
                let mutable go = true
                while go do
                    match next () with
                    | Some v ->
                        do! handle v
                        while v > 0 do
                            do! handle (v - 1)
                    | None -> go <- false
                return 0
            }
            let items (ct: CancellationToken) (xs: int list) (handle: int -> Task) = task {
                for x in xs do
                    do! handle x
                return 0
            }
            """

    match unobservedLoopsIn source with
    | [ a; b ] ->
        Assert.Equal("ct", a.TokenName)
        Assert.Equal(5, a.Range.StartLine)
        Assert.Equal(15, b.Range.StartLine)

        // the fix (CR0170's): the check as the body's first statement, the
        // first statement moving down a line at its own indentation
        match a.Fix, b.Fix with
        | Some(ra, _, ta), Some(rb, _, tb) ->
            Assert.Equal("ct.ThrowIfCancellationRequested()\n        ", ta)
            let patched = applyEdit (applyEdit source rb tb) ra ta

            Assert.Contains(
                fsharp
                    """
                        while go do
                            ct.ThrowIfCancellationRequested()
                            match next () with
                    """,
                patched
            )

            Assert.Contains(
                fsharp
                    """
                        for x in xs do
                            ct.ThrowIfCancellationRequested()
                            do! handle x
                    """,
                patched
            )

            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected both loops to carry the fix, got %A" other
    | other -> failwithf "Expected two loop notes, got %A" other

[<Fact>]
let ``FR0118: a one-line loop body gets the note without the fix`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let items (ct: CancellationToken) (xs: int list) (handle: int -> Task) = task {
                for x in xs do do! handle x
                return 0
            }
            """

    match unobservedLoopsIn source with
    | [ s ] -> Assert.True(s.Fix.IsNone, "a body on the header's line has no first statement to lead")
    | other -> failwithf "Expected one loop note, got %A" other

[<Fact>]
let ``FR0118: a loop that observes the token, sits in async, or has the token fix inside stays quiet`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let checks (ct: CancellationToken) (handle: int -> Task) = task {
                let mutable i = 0
                while i < 10 do
                    ct.ThrowIfCancellationRequested()
                    do! handle i
                    i <- i + 1
                return 0
            }
            let passes (ct: CancellationToken) (handle: int * CancellationToken -> Task) = task {
                let mutable i = 0
                while i < 10 do
                    do! handle (i, ct)
                    i <- i + 1
                return 0
            }
            let inAsync (ct: CancellationToken) (handle: int -> Async<unit>) = async {
                let mutable i = 0
                while i < 10 do
                    do! handle i
                    i <- i + 1
                return 0
            }
            let fixable (ct: CancellationToken) = task {
                let mutable i = 0
                while i < 10 do
                    do! Task.Delay(100)
                    i <- i + 1
                return 0
            }
            let plainFor (ct: CancellationToken) (xs: int list) =
                let mutable total = 0
                for x in xs do
                    total <- total + x
                total
            """

    Assert.Empty(unobservedLoopsIn source)

[<Fact>]
let ``FR0118: a synchronous drain and a loop stepping a local built with the token stay quiet`` () =
    // Fuuga's Server.fs: `while reader.TryRead(&tok)` empties what a channel
    // already holds, and an async enumerator created with the token observes
    // it at every MoveNextAsync
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            open System.Collections.Generic
            let drain (ct: CancellationToken) (reader: Channels.ChannelReader<int>) (sink: int -> unit) =
                let mutable tok = 0
                while reader.TryRead(&tok) do
                    sink tok
            let stream (ct: CancellationToken) (source: IAsyncEnumerable<int>) (sink: int -> unit) = task {
                let enumerator = source.GetAsyncEnumerator ct
                let mutable go = true
                while go do
                    let! hasNext = enumerator.MoveNextAsync().AsTask()
                    if hasNext then sink enumerator.Current else go <- false
                return 0
            }
            let stepped (ct: CancellationToken) = task {
                let step () = Task.Delay(10, ct)
                let mutable i = 0
                while i < 10 do
                    do! step ()
                    i <- i + 1
                return i
            }
            """

    Assert.Empty(unobservedLoopsIn source)

[<Fact>]
let ``CancellationToken None is replaced by the in-scope token`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let pause (ct: CancellationToken) = task {
                do! Task.Delay(100, CancellationToken.None)
                return 1
            }
            """

    match cancellationIn source with
    | [ s ] ->
        Assert.Equal(CancellationOverload.TokenGap.NonePassed, s.Kind)
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("Task.Delay(100, ct)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one propagation suggestion, got %A" other

[<Fact>]
let ``no token in scope means no suggestion`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading.Tasks
                let pause () = task {
                    do! Task.Delay(100)
                    return 1
                }
                """
        )
    )

[<Fact>]
let ``two tokens in scope make the choice a human call`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let pause (a: CancellationToken) (b: CancellationToken) = task {
                    do! Task.Delay(100)
                    return 1
                }
                """
        )
    )

[<Fact>]
let ``a call already passing the token is left alone`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let pause (ct: CancellationToken) = task {
                    do! Task.Delay(100, ct)
                    return 1
                }
                """
        )
    )

[<Fact>]
let ``a trailing lambda argument is wrapped before the token is appended`` () =
    // Paket's PackageResolver.fs: `ContinueWith(fun (_: Task) -> (), ct)`
    // made the lambda return `unit * CancellationToken`
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let f (ct: CancellationToken) (t: Task) = task {
                do! t.ContinueWith(fun (_: Task) -> ())
                return 1
            }
            """

    match cancellationIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("t.ContinueWith((fun (_: Task) -> ()), ct)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one token suggestion, got %A" other

[<Fact>]
let ``a token passed as the PAYLOAD is not appended again`` () =
    // CreateLinkedTokenSource(ct) takes the token as its argument — a
    // params/two-token sibling overload would happily compile `(ct, ct)`
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                let link (ct: CancellationToken) =
                    CancellationTokenSource.CreateLinkedTokenSource(ct)
                """
        )
    )

[<Fact>]
let ``a NAMED argument defeats arity counting and vetoes the append`` () =
    // `cancellationToken = ct` may well BE the token; appending `, ct`
    // after a named argument is a syntax error besides
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                type C() =
                    member _.Get(a: int) = Task.FromResult a
                    member _.Get(a: int, ct: CancellationToken) = Task.FromResult a
                let f (c: C) (ct: CancellationToken) = task {
                    let! x = c.Get(a = 1)
                    return x
                }
                """
        )
    )

[<Fact>]
let ``a method with no token overload is left alone`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                let check (ct: CancellationToken) (s: string) = s.Contains("x")
                """
        )
    )

[<Fact>]
let ``a stored None binding is not rewritten`` () =
    // not an argument: replacing a binding's RHS rewrites intent the
    // scan cannot see
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                let keep (ct: CancellationToken) =
                    let none = CancellationToken.None
                    none
                """
        )
    )

// ---- FR0119 AwaitableOverload ----

let private awaitableIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AwaitableOverload.find tree sourceText checkResults

let private applyAwaitable (source: string) (s: AwaitableOverload.Suggestion) =
    s.Fixes
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``a blocking read inside task becomes its async twin`` () =
    let source =
        fsharp
            """
            open System.IO
            let head (reader: TextReader) = task {
                let line = reader.ReadLine()
                return line
            }
            """

    match awaitableIn source with
    | [ s ] ->
        Assert.Equal("ReadLine", s.MethodName)
        let patched = applyAwaitable source s
        Assert.Contains("let! line = reader.ReadLineAsync()", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one awaitable suggestion, got %A" other


[<Fact>]
let ``a call nested in another binding's RHS is not a let-bang site`` () =
    // the prismatic shape: the call sits inside the CE's RANGE but not on
    // its statement spine, so `let!` there cannot compile — 21 rollbacks in
    // one sweep repo were all this
    let source =
        fsharp
            """
            open System.IO
            let f (reader: TextReader) = task {
                let pair =
                    let line = reader.ReadLine()
                    line, line.Length
                return snd pair
            }
            """

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a statement nested in another binding's RHS is not a do-bang site`` () =
    let source =
        fsharp
            """
            open System.IO
            let f (writer: TextWriter) (s: string) = task {
                let n =
                    writer.Write(s)
                    1
                return n
            }
            """

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a blocking statement inside task becomes do-bang`` () =
    let source =
        fsharp
            """
            open System.IO
            let push (writer: TextWriter) (s: string) = task {
                writer.Write(s)
                return 1
            }
            """

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! writer.WriteAsync(s)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one statement suggestion, got %A" other

[<Fact>]
let ``inside async the twin bridges via AwaitTask`` () =
    let source =
        fsharp
            """
            open System.IO
            let head (reader: TextReader) = async {
                let line = reader.ReadLine()
                return line
            }
            """

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("let! line = reader.ReadLineAsync() |> Async.AwaitTask", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one bridged suggestion, got %A" other

[<Fact>]
let ``outside any CE the blocking call is fine`` () =
    Assert.Empty(
        awaitableIn (
            fsharp
                """
                open System.IO
                let head (reader: TextReader) = reader.ReadLine()
                """
        )
    )

[<Fact>]
let ``inside a lambda within the task nothing fires`` () =
    Assert.Empty(
        awaitableIn (
            fsharp
                """
                open System.IO
                let all (readers: TextReader list) = task {
                    let lines = readers |> List.map (fun r -> r.ReadLine())
                    return lines
                }
                """
        )
    )

[<Fact>]
let ``a method with no async twin is left alone`` () =
    Assert.Empty(
        awaitableIn (
            fsharp
                """
                let f (s: string) = task {
                    let u = s.ToUpperInvariant()
                    return u
                }
                """
        )
    )

[<Fact>]
let ``FR0119 a local function inside the task is a plain function`` () =
    // its body is a closure the AST does not spell as a Lambda — a do!
    // injected there would land in ordinary code
    let source =
        fsharp
            """
            open System.IO
            let go (writer: TextWriter) (s: string) = task {
                let flushTwice () =
                    writer.Write(s)
                    writer.Write(s)
                flushTwice ()
                return 1
            }
            """

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``FR0119 the juxtaposed atomic argument is the common F# spelling`` () =
    let source =
        fsharp
            """
            open System.IO
            let push (writer: TextWriter) (s: string) = task {
                writer.Write s
                return 1
            }
            """

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! writer.WriteAsync s", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one juxtaposed suggestion, got %A" other

// ---- FR0049 Taskify: file-private boundary drains become task-returning ----

let private taskifyIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Taskify.find tree sourceText checkResults None

let private applyTaskify (source: string) (s: Taskify.Suggestion) =
    let lines = source.Split '\n'

    let offsetOf (line: int) (col: int) =
        (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

    s.Edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold
        (fun (acc: string) (r, _, replacement) ->
            let st = offsetOf r.StartLine r.StartColumn
            let en = offsetOf r.EndLine r.EndColumn
            acc.Substring(0, st) + replacement + acc.Substring en)
        source

[<Fact>]
let ``a private boundary drain becomes a task and its caller awaits`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let private fetch (x: int) =
                let t = Task.Run(fun () -> x)
                t.GetAwaiter().GetResult()
            let consume () = task {
                let s = fetch 1
                return s
            }
            """

    match taskifyIn source with
    | [ s ] ->
        Assert.Equal("fetch", s.Name)
        let patched = applyTaskify source s

        Assert.Contains(
            fsharp
                """
                    task {
                        let t = Task.Run(fun () -> x)
                        return! t
                    }
                """,
            patched
        )

        Assert.Contains("let! s = fetch 1", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one taskify suggestion, got %A" other

[<Fact>]
let ``an async caller bridges with Async.AwaitTask`` () =
    // `.Result` raised AggregateException already, as `Async.AwaitTask` does
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let private fetch (x: int) =
                let t = Task.Run(fun () -> x)
                t.Result
            let consume () = async {
                let s = fetch 2
                return s
            }
            """

    match taskifyIn source with
    | [ s ] ->
        let patched = applyTaskify source s
        Assert.Contains("let! s = Async.AwaitTask (fetch 2)", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one async-caller suggestion, got %A" other

[<Fact>]
let ``a return-position caller becomes return-bang`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let private fetch (x: int) =
                let t = Task.Run(fun () -> x)
                t.GetAwaiter().GetResult()
            let consume () = task {
                return fetch 3
            }
            """

    match taskifyIn source with
    | [ s ] ->
        let patched = applyTaskify source s
        Assert.Contains("return! fetch 3", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one return-position suggestion, got %A" other

[<Fact>]
let ``a public function is a wider refactor and stays`` () =
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    t.GetAwaiter().GetResult()
                let consume () = task {
                    let s = fetch 1
                    return s
                }
                """
        )
    )

[<Fact>]
let ``a caller outside any CE vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    t.GetAwaiter().GetResult()
                let consume () = fetch 1 + 1
                """
        )
    )

[<Fact>]
let ``a caller under a lambda inside the CE vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    t.GetAwaiter().GetResult()
                let consume () = task {
                    let xs = [ 1; 2 ] |> List.map (fun i -> fetch i)
                    return xs
                }
                """
        )
    )

[<Fact>]
let ``a blocking site under a lambda in the body vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private sum (xs: Task<int> list) =
                    xs |> List.map (fun t -> t.GetAwaiter().GetResult()) |> List.sum
                let consume () = task {
                    let s = sum []
                    return s
                }
                """
        )
    )

[<Fact>]
let ``an internal boundary drain taskifies across files under api-changes`` () =
    let sourceA =
        fsharp
            """
            module A
            let internal fetch (x: int) =
                let t = System.Threading.Tasks.Task.Run(fun () -> x)
                t.GetAwaiter().GetResult()
            """

    let sourceB =
        fsharp
            """
            module B
            let consume () = task {
                let s = A.fetch 1
                return s
            }
            """

    let treeA, sourceTextA, checkA, projectResults, _, _, recheck =
        parseAndCheckPair sourceA sourceB

    Scope.set { Scope.editor with ApiChanges = true }

    try
        match Taskify.find treeA sourceTextA checkA (Some projectResults) with
        | [ s ] ->
            let byFile =
                s.Edits
                |> List.groupBy (fun (r, _, _) -> System.IO.Path.GetFileName r.FileName)
                |> Map.ofList

            let apply (source: string) (es: (FSharp.Compiler.Text.range * string * string) list) =
                es
                |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
                |> List.fold (fun acc (r, _, rep) -> applyEdit acc r rep) source

            let patchedA = apply sourceA byFile.["A.fs"]
            let patchedB = apply sourceB byFile.["B.fs"]
            Assert.Contains("task {", patchedA)
            Assert.Contains("return! t", patchedA)
            Assert.Contains("let! s = A.fetch 1", patchedB)
            let errors = recheck patchedA patchedB
            Assert.True(Array.isEmpty errors, $"patched pair does not typecheck: %A{errors}")
        | other -> failwithf "Expected one internal taskify, got %A" other
    finally
        Scope.reset ()

[<Fact>]
let ``an internal drain without api-changes stays a note`` () =
    let sourceA =
        fsharp
            """
            module A
            let internal fetch2 (x: int) =
                let t = System.Threading.Tasks.Task.Run(fun () -> x)
                t.GetAwaiter().GetResult()
            """

    let sourceB =
        fsharp
            """
            module B
            let consume () = task {
                let s = A.fetch2 1
                return s
            }
            """

    let treeA, sourceTextA, checkA, projectResults, _, _, _ =
        parseAndCheckPair sourceA sourceB

    Assert.Empty(Taskify.find treeA sourceTextA checkA (Some projectResults))

[<Fact>]
let ``a fold whose body looks up a member on the accumulator hands the tuple over first`` () =
    // `xs |> List.fold (fun node x -> node.Append x) init` checks the lambda
    // before `init`, so `node.Append` meets an indeterminate type (Fable's
    // fable-library List.fs); `(init, xs) ||> List.fold ...` is checked
    // tuple-first and both types are known inside the lambda
    let source =
        fsharp
            """
            let f (xs: int list) =
                let mutable node = System.Text.StringBuilder()
                for x in xs do
                    node <- node.Append x
                node.ToString()
            """

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Contains("||> List.fold (fun node x -> node.Append x)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``a blocking call in a match arm of an async body, after use bindings, still gets its twin`` () =
    // CarmelNet's shape: `async { let! res = ... |> Async.Catch; match res with ... }`
    // with the blocking ReadToEnd two `use` bindings deep in an arm
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            open System.Net
            let f (client: Net.Http.HttpClient) =
                async {
                    let! res = async { return 1 } |> Async.Catch
                    match res with
                    | Choice1Of2 x -> return string x, None
                    | Choice2Of2 e when not (String.IsNullOrEmpty e.Message) -> return e.Message, Some e
                    | Choice2Of2 e ->
                        match e with
                        | :? WebException as wex when not (isNull wex.Response) ->
                            use stream = wex.Response.GetResponseStream()
                            use reader = new StreamReader(stream)
                            let err = reader.ReadToEnd()
                            return err, Some e
                        | _ -> return "", Some e
                }
            """

    match awaitableIn source with
    | [] -> failwith "Expected the ReadToEnd twin to be offered"
    | suggestions ->
        Assert.Contains(suggestions, fun s -> s.Fixes |> List.exists (fun (_, _, r) -> r = "ReadToEndAsync"))

let private variantHasTwin (source: string) =
    awaitableIn source
    |> List.exists (fun s -> s.Fixes |> List.exists (fun (_, _, r) -> r = "ReadToEndAsync"))

[<Fact>]
let ``variant A: plain let, no use, no match`` () =
    Assert.True(
        variantHasTwin (
            fsharp
                """
                module Test
                open System.IO
                let f (reader: StreamReader) =
                    async {
                        let err = reader.ReadToEnd()
                        return err
                    }
                """
        )
    )

[<Fact>]
let ``variant B: after use bindings`` () =
    Assert.True(
        variantHasTwin (
            fsharp
                """
                module Test
                open System.IO
                let f (stream: Stream) =
                    async {
                        use reader = new StreamReader(stream)
                        let err = reader.ReadToEnd()
                        return err
                    }
                """
        )
    )

[<Fact>]
let ``variant C: inside a match arm`` () =
    Assert.True(
        variantHasTwin (
            fsharp
                """
                module Test
                open System.IO
                let f (reader: StreamReader) (x: int option) =
                    async {
                        match x with
                        | Some _ ->
                            let err = reader.ReadToEnd()
                            return err
                        | None -> return ""
                    }
                """
        )
    )

[<Fact>]
let ``variant D: after a let-bang`` () =
    Assert.True(
        variantHasTwin (
            fsharp
                """
                module Test
                open System.IO
                let f (reader: StreamReader) =
                    async {
                        let! res = async { return 1 } |> Async.Catch
                        let err = reader.ReadToEnd()
                        return err
                    }
                """
        )
    )

[<Fact>]
let ``FR0057: the editor scaffold appends empty param tags after the last one`` () =
    let source =
        fsharp
            """
            module Test
            /// <summary>Scales.</summary>
            /// <param name="value">The value.</param>
            let scale (value: int) (factor: int) (offset: int) = value * factor + offset
            """

    match xmlDocsIn source with
    | [ s ] ->
        match s.Insertion with
        | Some(at, text) ->
            Assert.Equal(3, at.StartLine)

            Assert.Equal(
                fsharp
                    """

                    /// <param name="factor"></param>
                    /// <param name="offset"></param>
                    """,
                text
            )

            let patched = applyEdit source at text

            Assert.Equal(
                fsharp
                    """
                    module Test
                    /// <summary>Scales.</summary>
                    /// <param name="value">The value.</param>
                    /// <param name="factor"></param>
                    /// <param name="offset"></param>
                    let scale (value: int) (factor: int) (offset: int) = value * factor + offset
                    """,
                patched
            )
        | None -> failwith "Expected a scaffold insertion"
    | other -> failwithf "Expected exactly one doc-drift note, got %A" other

[<Fact>]
let ``FR0058: a recursive yield! in tail position is a loop, not a nested enumerator`` () =
    // FSharp.Data's CSV reader: `yield! readLines (n + 1)` as the body's
    // last step compiles to a jump
    Assert.Empty(
        recursiveSeqIn (
            fsharp
                """
                module Test
                let rec readLines (n: int) = seq {
                    yield n
                    yield! readLines (n + 1)
                }
                """
        )
    )

    Assert.Empty(
        recursiveSeqIn (
            fsharp
                """
                module Test
                let rec countDown n = seq {
                    yield n
                    if n > 0 then yield! countDown (n - 1) else ()
                }
                """
        )
    )

[<Fact>]
let ``FR0058: a recursive yield! under a for is still noted`` () =
    match
        recursiveSeqIn (
            fsharp
                """
                module Test
                type Node = { Value: int; Children: Node list }
                let rec walk (node: Node) = seq {
                    yield node.Value
                    for c in node.Children do
                        yield! walk c
                }
                """
        )
    with
    | [ s ] -> Assert.Equal("walk", s.FunctionName)
    | other -> failwithf "Expected exactly one recursive-seq note, got %A" other

[<Fact>]
let ``FR0058: a self-call yielding a plain value nests nothing`` () =
    // FSharp.Data's innerText': the recursion returns a string, not a sequence
    Assert.Empty(
        recursiveSeqIn (
            fsharp
                """
                module Test
                type Node = | Text of string | Elem of Node list
                let rec innerText (n: Node) =
                    match n with
                    | Text t -> t
                    | Elem content ->
                        seq {
                            for e in content do
                                yield innerText e
                        }
                        |> String.concat ""
                """
        )
    )

[<Fact>]
let ``FR0049: a blocking call inside a lambda within the computation is marked as such`` () =
    // FSharp.Data's CsvFile: `Func<_>(fun () -> ... |> Async.RunSynchronously)`
    // built inside async { } — the builder's bind cannot reach it
    match
        blockingIn (
            fsharp
                """
                let read () = async { return 1 }
                let f () = async {
                    let reader = System.Func<int>(fun () -> read () |> Async.RunSynchronously)
                    return reader.Invoke()
                }
                """
        )
    with
    | [ s ] ->
        Assert.Equal(Some "async", s.Builder)
        Assert.True(s.InLambda)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected one lambda-bound blocking site, got %A" other

[<Fact>]
let ``FR0020: an abstract member reached through an assignment's right-hand side is a ctor-time call`` () =
    // Fable's ObjectExprBase: `do x.Value <- this.dup x.contents`
    let _, ctorCalls, _ =
        objectRulesIn (
            fsharp
                """
                module Test
                [<AbstractClass>]
                type ObjectExprBase (x: int ref) as this =
                    do x.Value <- this.dup x.contents
                    abstract member dup: int -> int
                """
        )

    match ctorCalls with
    | [ c ] -> Assert.Equal("dup", c.MemberName)
    | other -> failwithf "Expected one ctor-time abstract call, got %A" other

[<Fact>]
let ``FR0054: a Dispose inside an interface block that raises is caught`` () =
    let _, _, raises =
        objectRulesIn (
            fsharp
                """
                module Test
                type R() =
                    interface System.IDisposable with
                        member _.Dispose() = failwith "simulated"
                """
        )

    match raises with
    | [ r ] -> Assert.Equal("Dispose", r.MemberName)
    | other -> failwithf "Expected one raise-in-Dispose finding, got %A" other

[<Fact>]
let ``FR0054: a pipe-shaped raise counts`` () =
    let _, _, raises =
        objectRulesIn (
            fsharp
                """
                module Test
                type R() =
                    override _.GetHashCode() = raise <| System.InvalidOperationException "no hash"
                """
        )

    match raises with
    | [ r ] -> Assert.Equal("GetHashCode", r.MemberName)
    | other -> failwithf "Expected one pipe-shaped raise finding, got %A" other

// ---- FR0055 offers ----

[<Fact>]
let ``FR0055: a pure division body gets the guard, and the catch goes`` () =
    let source =
        fsharp
            """
            module Test
            let ratio (total: int) (count: int) = try total / count with _ -> 0
            """

    match swallowedIn source with
    | [ s ] ->
        let guard = s.Offers |> List.find (fun o -> o.Label.StartsWith "Fix: guard")

        let patched =
            guard.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(
            fsharp
                """
                module Test
                let ratio (total: int) (count: int) = if count = 0 then 0 else total / count
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``FR0055: a one-call Parse body becomes TryParse`` () =
    let source =
        fsharp
            """
            module Test
            let parse (s: string) =
                try Some(System.Int32.Parse s) with _ -> None
            let parse2 (s: string) =
                try System.Int32.Parse s with _ -> 0
            """

    match swallowedIn source with
    | [ _; second ] ->
        let offer =
            second.Offers
            |> List.find (fun o -> o.Label.StartsWith "Fix: System.Int32.TryParse")

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                match System.Int32.TryParse s with
                    | true, parsed -> parsed
                    | false, _ -> 0
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0055: a Some-wrapped Parse body pairs with its None fallback`` () =
    let source =
        fsharp
            """
            module Test
            let parse (s: string) =
                try Some(System.Int32.Parse s) with _ -> None
            """

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Fix: System.Int32.TryParse")

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                match System.Int32.TryParse s with
                    | true, parsed -> Some parsed
                    | false, _ -> None
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one finding, got %A" other

let private parseControlFlowIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    SwallowedException.findParseControlFlow tree sourceText (Some check)

[<Fact>]
let ``FR0055: a Parse argument that may throw on its own - a Value on the way, a partial function, a checked conversion - keeps the catch; a KeyValuePair's Value or a Trim is offered TryParse``
    ()
    =
    let source =
        fsharp
            """
            module Test
            open System
            open System.Collections.Generic
            let a (o: string option) = try Int32.Parse(o.Value.Trim()) with _ -> 0
            let b (xs: string list) = try Int32.Parse(List.head xs) with _ -> 0
            let c (xs: string list) = try Int32.Parse(xs |> List.head) with _ -> 0
            let d (n: int64) = try Int32.Parse(string (Checked.int n)) with _ -> 0
            let e (kv: KeyValuePair<string, string>) = try Int32.Parse kv.Value with _ -> 0
            let f (s: string) = try Int32.Parse(s.Trim()) with _ -> 0
            let g (o: obj) = try Int32.Parse(o :?> string) with _ -> 0
            let h (m: Map<string, string>) = try Int32.Parse(Map.pick (fun k v -> if k = "a" then Some v else None) m) with _ -> 0
            """

    let found = parseControlFlowIn source |> List.sortBy (fun s -> s.Range.StartLine)
    Assert.Equal<int list>([ 4; 5; 6; 7; 8; 9; 10; 11 ], found |> List.map (fun s -> s.Range.StartLine))

    Assert.Equal<bool list>(
        [ true; true; true; true; false; false; true; true ],
        found |> List.map (fun s -> s.ArgumentMayThrow)
    )

    Assert.Equal<int list>([ 0; 0; 0; 0; 1; 1; 0; 0 ], found |> List.map (fun s -> s.Offers.Length))

[<Fact>]
let ``FR0055: a Parse caught narrowly for its own failures is TryParse as control flow`` () =
    let source =
        fsharp
            """
            module Test
            open System
            let parse (s: string) =
                try Int32.Parse s with :? FormatException | :? OverflowException -> 0
            let parse2 (s: string) =
                try
                    Some(Decimal.Parse s)
                with
                | :? FormatException
                | :? OverflowException as e -> None
            let parse3 (s: string) =
                try Some(Int32.Parse s) with
                | :? FormatException -> None
                | :? OverflowException -> None
            """

    match parseControlFlowIn source with
    | [ a; b; c ] ->
        Assert.Equal("Int32", a.TypeName)
        Assert.Equal(":? FormatException | :? OverflowException", a.PatternText)

        for s in [ a; b; c ] do
            let offer =
                s.Offers |> List.find (fun o -> o.Label.Contains ".TryParse instead of a catch")

            let patched =
                offer.Edits
                |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

            assertTypechecks "Patched source" patched

        let offer = b.Offers |> List.head

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                match Decimal.TryParse s with
                    | true, parsed -> Some parsed
                    | false, _ -> None
                """,
            patched
        )
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0055: a FormatException catch alone around a numeric parse is noted without the offer`` () =
    // CR0166's line: an overflow propagated here and would fall back after
    // the rewrite; a type that cannot overflow keeps the offer
    let source =
        fsharp
            """
            module Test
            open System
            let numeric (s: string) =
                try Int32.Parse s with :? FormatException -> 0
            let exact (s: string) =
                try Guid.Parse s with :? FormatException -> Guid.Empty
            let covered (s: string) =
                try Int32.Parse s with :? FormatException | :? OverflowException -> 0
            """

    match parseControlFlowIn source with
    | [ a; b; c ] ->
        Assert.Empty a.Offers
        Assert.NotEmpty b.Offers
        Assert.NotEmpty c.Offers
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0055: a narrow catch that does more than answer a value, or catches something else, stays quiet`` () =
    let source =
        fsharp
            """
            module Test
            open System
            let logged (s: string) (log: string -> unit) =
                try Int32.Parse s with :? FormatException as e -> log e.Message; 0
            let io (s: string) =
                try Int32.Parse s with :? IO.IOException -> 0
            let mixed (s: string) =
                try Some(Int32.Parse s) with
                | :? FormatException -> None
                | :? OverflowException -> Some 0
            let readsBinder (s: string) =
                try Int32.Parse s with e -> e.HResult
            let guarded (s: string) =
                try Int32.Parse s with :? FormatException when s.Length > 3 -> 0
            """

    Assert.Empty(parseControlFlowIn source)

[<Fact>]
let ``FR0168: a catch-all around a Parse is the same TryParse, with the swallow gone`` () =
    // CR0166 takes `catch (Exception)` and a bare `catch` the same way: the
    // rewrite drops the try, and the catch-all that hid every other failure
    let source =
        fsharp
            """
            module Test
            open System
            let catchAll (s: string) =
                try Int32.Parse s with _ -> 0
            let wrapped (s: string) =
                try Some(Guid.Parse s) with :? Exception -> None
            let unreadBinder (s: string) (fallback: decimal) =
                try Decimal.Parse s with ex -> fallback
            """

    match parseControlFlowIn source with
    | [ a; b; c ] ->
        for s in [ a; b; c ] do
            Assert.True(s.CatchAll, $"expected a catch-all at line {s.Range.StartLine}")
            Assert.NotEmpty s.Offers

        let patched =
            [ a; b; c ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold
                (fun acc s ->
                    s.Offers.Head.Edits
                    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) acc)
                source

        Assert.Contains(
            fsharp
                """
                    match Int32.TryParse s with
                    | true, parsed -> parsed
                    | false, _ -> 0
                """,
            patched
        )

        Assert.Contains(
            fsharp
                """
                    match Guid.TryParse s with
                    | true, parsed -> Some parsed
                    | false, _ -> None
                """,
            patched
        )

        Assert.Contains("| false, _ -> fallback", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0168: an argument that can throw on its own keeps the try, whatever the catch`` () =
    // the catch answered the argument's own exception with the fallback:
    // `s.Substring 5` on a short string, an index past the end, a numeric
    // conversion - TryParse would let it escape. `ArgumentOutOfRangeException`
    // IS an ArgumentException, so the narrow catch covered it too. A record
    // field, a module value, a user getter or a Trim are taken as reads:
    // the fix by default, a getter that throws the accepted residual
    let source =
        fsharp
            """
            module Test
            open System
            type R = { Text: string }
            module Defaults =
                let text = "1"
            let sub (s: string) =
                try Int32.Parse(s.Substring 5) with _ -> 0
            let index (args: string[]) =
                try Int32.Parse args.[1] with _ -> 0
            let narrow (s: string) =
                try Int32.Parse(s.Substring 5) with :? FormatException | :? OverflowException | :? ArgumentException -> 0
            let converted (x: float) =
                try Int32.Parse(string (int x)) with _ -> 0
            type C() =
                member _.Text = "1"
            let getter (c: C) =
                try Int32.Parse c.Text with _ -> 0
            let trimmed (s: string) =
                try Int32.Parse(s.Trim()) with _ -> 0
            let field (r: R) =
                try Int32.Parse r.Text with _ -> 0
            let moduleValue () =
                try Int32.Parse Defaults.text with _ -> 0
            """

    match parseControlFlowIn source with
    | [ sub; index; narrow; converted; getter; trimmed; field; moduleValue ] ->
        for s in [ sub; index; narrow; converted ] do
            Assert.True(s.ArgumentMayThrow, $"line {s.Range.StartLine}")
            Assert.Empty s.Offers

        for s in [ getter; trimmed; field; moduleValue ] do
            Assert.False(s.ArgumentMayThrow, $"line {s.Range.StartLine}")
            Assert.NotEmpty s.Offers
    | other -> failwithf "Expected eight findings, got %A" other

    // without the fix the catch-all stays FR0055's swallow
    let (sub: string) = "abc"

    Assert.Equal(
        0,
        (try
            System.Int32.Parse(sub.Substring 5)
         with _ ->
             0)
    )

    Assert.Throws<System.ArgumentOutOfRangeException>(fun () ->
        match System.Int32.TryParse(sub.Substring 5) with
        | true, v -> ignore v
        | false, _ -> ())
    |> ignore

[<Fact>]
let ``FR0168: a user member named like a throwing BCL one is a read, LINQ First is not`` () =
    // the throwing names (First, Last, Get, ...) are known of the BCL
    // and FSharp.Core: a user's own `Get` or `First` is a user getter, the
    // fix by default, as `c.Text` is
    let source =
        fsharp
            """
            module Test
            open System
            open System.Linq
            type Settings() =
                member _.Get(key: string) = key
                member _.First = "1"
                member _.Last = "2"
            let get (c: Settings) = try Int32.Parse(c.Get "port") with _ -> 0
            let first (c: Settings) = try Int32.Parse c.First with _ -> 0
            let last (c: Settings) = try Int32.Parse c.Last with _ -> 0
            let linq (xs: string list) = try Int32.Parse(xs.First()) with _ -> 0
            """

    match parseControlFlowIn source with
    | [ get; first; last; linq ] ->
        for s in [ get; first; last ] do
            Assert.False(s.ArgumentMayThrow, $"line {s.Range.StartLine}")
            Assert.NotEmpty s.Offers

        Assert.True(linq.ArgumentMayThrow)
        Assert.Empty linq.Offers
    | other -> failwithf "Expected four findings, got %A" other

[<Fact>]
let ``FR0168: a user Parse, Single or indexer throws by convention and keeps the try`` () =
    // Parse throws where TryParse answers, whoever declares it; Single and
    // Item throw on a miss as `xs.[i]` does - the catch answered those too
    let source =
        fsharp
            """
            module Test
            open System
            type Port =
                { Text: string }
                static member Parse(s: string) = if s = "" then failwith "empty" else { Text = s }
            type Bag() =
                member _.Single() = "1"
                member _.Item(i: int) = string i
            let parsed (s: string) = try Int32.Parse((Port.Parse s).Text) with _ -> 0
            let single (b: Bag) = try Int32.Parse(b.Single()) with _ -> 0
            let item (b: Bag) = try Int32.Parse(b.Item 3) with _ -> 0
            """

    match parseControlFlowIn source with
    | [ parsed; single; item ] ->
        for s in [ parsed; single; item ] do
            Assert.True(s.ArgumentMayThrow, $"line {s.Range.StartLine}")
            Assert.Empty s.Offers
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0168: a bare name is a read, a static property opened by open type included`` () =
    // a getter that throws is the accepted residual: the fix by default
    let source =
        fsharp
            """
            module Test
            open System
            type Cfg =
                static member Port: string = failwith "no config"
            open type Cfg
            let a () = try Int32.Parse Port with _ -> 0
            let b (port: string) = try Int32.Parse port with _ -> 0
            """

    match parseControlFlowIn source with
    | [ a; b ] ->
        for s in [ a; b ] do
            Assert.False(s.ArgumentMayThrow)
            Assert.NotEmpty s.Offers
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0168: a TimeSpan overflows, so a FormatException catch alone keeps the note`` () =
    let source =
        fsharp
            """
            module Test
            open System
            let narrow (s: string) =
                try TimeSpan.Parse s with :? FormatException -> TimeSpan.Zero
            let covered (s: string) =
                try TimeSpan.Parse s with :? FormatException | :? OverflowException -> TimeSpan.Zero
            """

    match parseControlFlowIn source with
    | [ narrow; covered ] ->
        Assert.Empty narrow.Offers
        Assert.NotEmpty covered.Offers
    | other -> failwithf "Expected two findings, got %A" other

    // the premise: Parse overflows where TryParse answers false
    Assert.Throws<System.OverflowException>(fun () -> System.TimeSpan.Parse "99999999.00:00:00" |> ignore)
    |> ignore

    Assert.False(fst (System.TimeSpan.TryParse "99999999.00:00:00"))

[<Fact>]
let ``FR0055: a file-IO body gets the narrower catch`` () =
    let source =
        fsharp
            """
            module Test
            let read (path: string) = try System.IO.File.ReadAllText path with ex -> ""
            """

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Alternative: catch the IO")

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("with (:? System.IO.IOException | :? System.UnauthorizedAccessException) as ex ->", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: a file that logs through MEL gets a log line in its own idiom`` () =
    let source =
        fsharp
            """
            module Test
            type ILogger =
                abstract LogError: exn * string * obj[] -> unit
            let work (logger: ILogger) (id: int) =
                logger.LogError(null, "started {Id}", [| box id |])
                try
                    printfn "%d" id
                with _ -> ()
            """

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Alternative: log it")

        let patched =
            offer.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.True(
            patched.Contains
                """logger.LogError(ex, "Exception: {Message} in method {Method} with parameter {id}", ex.Message, "work", id)""",
            patched
        )
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: the guard spells the zero of the divisor's type, never for a float, and stays away without a type`` () =
    let source =
        fsharp
            """
            module Test
            let a (total: float) (count: float) = try total / count with _ -> 0.0
            let b (total: int64) (count: int64) = try total / count with _ -> 0L
            let c (total: decimal) (count: decimal) = try total / count with _ -> 0m
            """

    let guards =
        swallowedIn source
        |> List.map (fun s ->
            s.Offers
            |> List.tryFind (fun o -> o.Label.StartsWith "Fix: guard")
            |> Option.map (fun o -> o.Edits |> List.map (fun (_, _, r) -> r) |> List.head))

    Assert.Equal<string option list>(
        // float division never throws: no guard to offer; decimal
        // arithmetic overflows, so the catch guarded more than the division
        [ None; Some "if count = 0L then 0L else total / count"; None ],
        guards
    )

    for r in guards |> List.choose id do
        let patched = source.Replace("try total / count with _ -> 0.0", r)
        ignore patched

    let untyped =
        let tree, sourceText =
            parse (
                fsharp
                    """
                    module Test
                    let a (total: int) (count: int) = try total / count with _ -> 0
                    """
            )

        SwallowedException.find tree sourceText None

    match untyped with
    | [ s ] -> Assert.Empty(s.Offers |> List.filter (fun o -> o.Label.StartsWith "Fix: guard"))
    | other -> failwithf "Expected one finding, got %A" other

// ---- FR0049: statement-position waits and Assert.Throws become binds ----

let private applyFixes (source: string) (fixes: (FSharp.Compiler.Text.range * string * string) list) =
    fixes
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``FR0049: a statement-position Wait inside task becomes do-bang`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task) = task {
                t.Wait()
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, "t.Wait()", "do! t") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the do! fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: WaitAll inside task becomes do-bang WhenAll`` () =
    let source =
        fsharp
            """
            let f (a: System.Threading.Tasks.Task) (b: System.Threading.Tasks.Task) = task {
                System.Threading.Tasks.Task.WaitAll(a, b)
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "do! System.Threading.Tasks.Task.WhenAll(a, b)") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the WhenAll fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a Wait on a generic task inside async awaits the upcast task`` () =
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task<int>) = async {
                t.Wait()
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "do! Async.AwaitTask (t :> System.Threading.Tasks.Task)") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the AwaitTask fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a final WaitAll of generic tasks has no bind shape`` () =
    // `let! _ =` cannot end a block, `do!` cannot take a Task<T[]>
    let source =
        fsharp
            """
            let f (a: System.Threading.Tasks.Task<int>) (b: System.Threading.Tasks.Task<int>) = task {
                System.Threading.Tasks.Task.WaitAll(a, b)
            }
            """

    match blockingIn source with
    | [ s ] -> Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a blocking call inside Assert.Throws moves with the assert`` () =
    let source =
        fsharp
            """
            module Xunit
            open System
            open System.Threading.Tasks
            type Assert =
                static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>
                static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>
            let f (t: Task<int>) = task {
                let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                return ex.Message
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.True s.InLambda

        match s.Fixes with
        | [ (_, "let", "let!"); (_, _, replacement) ] ->
            Assert.Equal(
                "Assert.ThrowsAsync<InvalidOperationException>(fun () -> t :> System.Threading.Tasks.Task)",
                replacement
            )

            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the let!-bind pair, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

// ---- FR0055: test files are quiet ----

[<Fact>]
let ``FR0055: a file that opens a test framework gets no notes`` () =
    // a test's `try ... with _ -> 0` is deliberate: the assertion after it
    // is the observation, and the guard would be noise
    let body = "let ratio (total: int) (count: int) = try total / count with _ -> 0"

    Assert.NotEmpty(
        swallowedIn (
            fsharp
                """
                module Tests
                module Xunit =
                    let marker = 1

                """
            + body
        )
    )

    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Tests
                module Xunit =
                    let marker = 1
                open Xunit

                """
            + body
        )
    )

[<Fact>]
let ``FR0049: an Assert.Throws inside a nested lambda stays advice`` () =
    // the `let ex =` sits in a List.iter callback: a `let!` there would not
    // compile, so the assert is left where it is
    let source =
        fsharp
            """
            module Xunit
            open System
            open System.Threading.Tasks
            type Assert =
                static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>
                static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>
            let f (ts: Task<int> list) = task {
                ts
                |> List.iter (fun t ->
                    let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())
                    ignore ex)
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.True s.InLambda
        Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a bounded Wait and a Result after WaitForExit outside a CE are the sync idiom`` () =
    // prismatic's scripts: stdout is read asynchronously, WaitForExit blocks,
    // then .Result drains a task that already completed
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Diagnostics
                let run (psi: ProcessStartInfo) =
                    use proc = Process.Start psi
                    let output = proc.StandardOutput.ReadToEndAsync()
                    proc.WaitForExit()
                    output.Result
                """
        )
    )

    Assert.Empty(blockingIn "let stop (t: System.Threading.Tasks.Task) = t.Wait(System.TimeSpan.FromSeconds 10.0)")

    // an unbounded Wait outside a CE is still the boundary note
    Assert.NotEmpty(blockingIn "let stop (t: System.Threading.Tasks.Task) = t.Wait()")

[<Fact>]
let ``FR0055: the IO-only catch is offered for a body that is the IO call, not a block that mentions a path`` () =
    // Kasino: a multi-line block computing a path, then calling native SDL —
    // narrowing to IOException would let the native failures through
    let block =
        fsharp
            """
            module Test
            let icon (dir: string) =
                try
                    let p = System.IO.Path.Combine(dir, "icon.png")
                    let handle = System.Runtime.InteropServices.GCHandle.Alloc(p)
                    handle.Free()
                with _ -> ()
            """

    match swallowedIn block with
    | [ s ] -> Assert.Empty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other

    let single =
        fsharp
            """
            module Test
            let firstFont (dir: string) =
                try System.IO.Directory.GetFiles(dir, "*.ttf") |> Array.tryHead with _ -> None
            """

    match swallowedIn single with
    | [ s ] -> Assert.NotEmpty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other


[<Fact>]
let ``FR0055: the log line lands above a fallback that already sits on its own line`` () =
    // prismatic: `with _ ->` then `false` on the next line gained a blank
    // line and an over-indented pair
    let source =
        fsharp
            """
            module Test
            type ILogger =
                abstract LogError: exn * string * obj[] -> unit
            let isActive (logger: ILogger) (pid: int) =
                logger.LogError(null, "started {Pid}", [| box pid |])
                try
                    pid > 0
                with _ ->
                    false
            """

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Alternative: log it")

        let patched =
            offer.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(
            fsharp
                """
                module Test
                type ILogger =
                    abstract LogError: exn * string * obj[] -> unit
                let isActive (logger: ILogger) (pid: int) =
                    logger.LogError(null, "started {Pid}", [| box pid |])
                    try
                        pid > 0
                    with ex ->
                        logger.LogError(ex, "Exception: {Message} in method {Method} with parameter {pid}", ex.Message, "isActive", pid)
                        false
                """,
            patched
        )

    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: a comment on the handler is the author's acknowledgement`` () =
    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (g: unit -> unit) =
                    try g () with _ -> () // best effort: the icon is cosmetic
                """
        )
    )

    Assert.Empty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (g: unit -> int) =
                    try g ()
                    with _ ->
                        0 // the length is not important
                """
        )
    )

    Assert.NotEmpty(
        swallowedIn (
            fsharp
                """
                module Test
                let f (g: unit -> int) =
                    try g () with _ -> 0
                """
        )
    )

[<Fact>]
let ``FR0055: the log line is offered only where its receiver is in scope`` () =
    // Fuuga: a `logger` parameter of one function was written into catches
    // of six functions that have none
    let source =
        fsharp
            """
            module Test
            type ILogger =
                abstract LogError: exn * string * obj[] -> unit
            let a (logger: ILogger) (id: int) =
                logger.LogError(null, "started {Id}", [| box id |])
                try id with _ -> 0
            let b (x: int) =
                try x with _ -> 0
            """

    match swallowedIn source with
    | [ inA; inB ] ->
        Assert.NotEmpty(inA.Offers |> List.filter (fun o -> o.Label.StartsWith "Alternative: log it"))
        Assert.Empty(inB.Offers |> List.filter (fun o -> o.Label.StartsWith "Alternative: log it"))
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0055: a multi-line body that reads a file and then parses it gets no IO-only catch`` () =
    // FSharp.Azure.Quantum's loadMolFile: the parse after the read throws
    // its own exceptions
    let source =
        fsharp
            """
            module Test
            let loadMolFile (path: string) =
                try
                    let content = System.IO.File.ReadAllText(path)
                    Some content.Length
                with
                | _ -> None
            """

    match swallowedIn source with
    | [ s ] -> Assert.Empty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other

// ---- FR0050 shape guards (Mibo, the compiler) ----

[<Fact>]
let ``FR0050: a fold followed by nothing but the accumulator collapses into the expression`` () =
    // `let flags = .. |> Array.fold ..` was left with a bare `flags` line
    // after it on Mibo and the compiler: binding and use are the expression
    let source =
        fsharp
            """
            let f (xs: int[]) =
                let mutable flags = 0
                for x in xs do
                    flags <- flags ||| x
                flags
            """

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal("xs |> Array.fold (fun flags x -> flags ||| x) 0", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText

        Assert.Equal(
            fsharp
                """
                let f (xs: int[]) =
                    xs |> Array.fold (fun flags x -> flags ||| x) 0
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``FR0050: an annotated mutable keeps its annotation on the folded binding`` () =
    // Mibo's `let mutable sum: IAdaptiveValue<int> = ..` lost its annotation
    let source =
        fsharp
            """
            let f (xs: int list) =
                let mutable total: int64 = 0L
                for x in xs do
                    total <- total + int64 x
                total
            """

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal("let total: int64 = xs |> List.fold (fun total x -> total + int64 x) 0L", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText

        Assert.EndsWith(
            fsharp
                """

                    total
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``FR0050: a fold that would land past column 100 is withheld`` () =
    let folds, _ =
        accumulationIn (
            fsharp
                """
                let f (xs: int list) =
                    let mutable accumulatedRunningTotalOfEverything = 1
                    for element in xs do
                        accumulatedRunningTotalOfEverything <- max accumulatedRunningTotalOfEverything (element % 7)
                    accumulatedRunningTotalOfEverything * 2
                """
        )

    Assert.Empty folds

// ---- FR0118 scheduling calls (suave's Tcp.fs) ----

[<Fact>]
let ``FR0118: Task.Run never gains the token`` () =
    // with an already-cancelled token Task.Run never runs the delegate,
    // so the socket bind and the cell completion inside it never happen
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System
                open System.Threading
                open System.Threading.Tasks
                let start (ct: CancellationToken) =
                    Task.Run(Func<Task>(fun () -> Task.CompletedTask))
                """
        )
    )

[<Fact>]
let ``FR0118: Task.Factory.StartNew never gains the token`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let start (ct: CancellationToken) =
                    Task.Factory.StartNew(fun () -> 1)
                """
        )
    )

[<Fact>]
let ``FR0118: an explicit None on Task.Run is the author's choice`` () =
    Assert.Empty(
        cancellationIn (
            fsharp
                """
                open System
                open System.Threading
                open System.Threading.Tasks
                let start (ct: CancellationToken) =
                    Task.Run(Func<Task>(fun () -> Task.CompletedTask), CancellationToken.None)
                """
        )
    )


// ---- FR0119 AwaitableOverload: Dispose has no awaitable twin (fantomas EndToEndTests.fs) ----

[<Fact>]
let ``FR0119 a Dispose statement inside task is never offered DisposeAsync`` () =
    // fantomas's EndToEndTests.fs: `File.Create(path).Dispose()` became
    // `do! File.Create(path).DisposeAsync()` — a ValueTask twin with no
    // work to await; Dispose stays Dispose
    let source =
        fsharp
            """
            open System.IO
            let touch (path: string) = task {
                File.Create(path).Dispose()
                return 1
            }
            """

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``FR0119 a stream flush inside task still becomes do-bang FlushAsync`` () =
    let source =
        fsharp
            """
            open System.IO
            let flush (stream: Stream) = task {
                stream.Flush()
                return 1
            }
            """

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! stream.FlushAsync()", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one FlushAsync suggestion, got %A" other

// ---- FR0049: tasks known complete, console blocking points, primitives ----

[<Fact>]
let ``FR0049: a Result read under its own completion probe never waits`` () =
    // suave's ValueTask fast path: the read happens only when the task is
    // already complete, the else branch awaits it
    let fastPath =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let read (vt: ValueTask<int>) : ValueTask<int> =
                if vt.IsCompletedSuccessfully then
                    ValueTask<int>(vt.Result + 1)
                else
                    ValueTask<int>(task {
                        let! n = vt
                        return n + 1
                    })
            """

    Assert.Empty(blockingIn fastPath)

    // conjoined, negated, and inside a task { } the same way
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (vt: ValueTask<int>) (fast: bool) =
                    if fast && vt.IsCompleted then vt.Result else 0
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (vt: ValueTask<int>) =
                    if not vt.IsCompletedSuccessfully then 0 else vt.Result
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (vt: ValueTask<int>) = task {
                    if vt.IsCompletedSuccessfully then
                        let _ = vt.Result
                        return 1
                    else
                        let! _ = vt
                        return 2
                }
                """
        )
    )

    // a probe on ANOTHER task proves nothing about this one
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (a: ValueTask<int>) (b: ValueTask<int>) =
                    if a.IsCompletedSuccessfully then b.Result else 0
                """
        )
    )

[<Fact>]
let ``FR0049: a Result read behind a probe in the same condition, or on a WhenAny winner, never waits`` () =
    // the right operand of && runs only when the probe held
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (t: Task<bool>) =
                    t.IsCompleted && t.Result
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (t: Task<bool>) =
                    not t.IsCompleted || t.Result
                """
        )
    )

    // the WhenAny race: the task compared equal to the winner is complete,
    // and the && keeps the read from running when the timer won
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let race (work: Task<bool>) (timer: Task) = task {
                    let! winner = Task.WhenAny(work, timer)
                    if winner = work && work.IsCompleted && work.Result then return 1 else return 0
                }
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let race (work: Task<bool>) (timer: Task) = task {
                    let! winner = Task.WhenAny(work, timer)
                    return winner = work && work.Result
                }
                """
        )
    )

    // `<>` proves nothing in the right operand, and || runs it when the
    // probe held, not when it failed
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let race (work: Task<bool>) (timer: Task) = task {
                    let! winner = Task.WhenAny(work, timer)
                    return winner <> work && work.Result
                }
                """
        )
    )

    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let read (t: Task<bool>) =
                    t.IsCompleted || t.Result
                """
        )
    )

[<Fact>]
let ``FR0049: the antecedent of a ContinueWith continuation is complete by definition`` () =
    // suave's ConnectionFacade and fantomas' LSPFantomasService: the lambda
    // form; suave's AsyncExtensions and FCS's AsyncMemoize: a named function
    // never a blocking note: only the AggregateException advice
    let onlyAntecedentAdvice (source: string) =
        Assert.All(blockingIn source, (fun s -> Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)))

    onlyAntecedentAdvice (
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let f (t: Task<int>) =
                t.ContinueWith(fun (ante: Task<int>) -> ante.Result + 1)
            """
    )

    onlyAntecedentAdvice (
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let f (t: Task<int>) =
                let routine (finished: Task<int>) =
                    if finished.IsFaulted then 0 else finished.Result
                t.ContinueWith(routine, TaskScheduler.Default)
            """
    )

    // another task drained inside the continuation still blocks
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (t: Task<int>) (other: Task<int>) =
                    t.ContinueWith(fun (ante: Task<int>) -> other.Result + 1)
                """
        )
    )

[<Fact>]
let ``FR0049: a wait in the finally block of an async is named as such and gets no fix`` () =
    // FCS's DiagnosticsLogger and BuildGraph: `do!` cannot appear in a
    // finally block, so the bind the plain message asks for cannot compile
    let source =
        fsharp
            """
            module Test
            open System.Threading.Tasks
            let f (t: Task) (work: Async<int>) = async {
                try
                    let! r = work
                    return r
                finally
                    t.Wait()
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(Some "async", s.Builder)
        Assert.True s.InFinally
        Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one finally-block site, got %A" other

[<Fact>]
let ``FR0049: the console's blocking point is not a boundary note`` () =
    // suave's Http2Demo main, fantomas' DaemonCommand runner (exit code
    // after the wait), and a script's top-level statements
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Program
                open System.Threading.Tasks
                [<EntryPoint>]
                let main argv =
                    let server = Task.Delay 10
                    server.Wait()
                    0
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Program
                open System.Threading.Tasks
                let runDaemon (closed: Task) : int =
                    closed.GetAwaiter().GetResult()
                    0
                """
        )
    )

    // the test harness checks every source as Test.fsx: top-level
    // statements, a for loop included, are the script's main
    Assert.Empty(
        blockingIn (
            fsharp
                """
                open System.Threading.Tasks
                let run (n: int) = Task.Delay n
                (run 1).Wait()
                for n in [ 1; 2 ] do
                    (run n).Wait()
                """
        )
    )

    // a value-returning helper, a lambda inside main, and a member are
    // boundaries of their own
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Program
                open System.Threading.Tasks
                let wait (t: Task<int>) = t.GetAwaiter().GetResult()
                [<EntryPoint>]
                let main argv = wait (Task.FromResult 1)
                """
        )
    )

    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Program
                open System.Threading.Tasks
                [<EntryPoint>]
                let main argv =
                    let handler = fun (t: Task) -> t.Wait()
                    handler (Task.Delay 1)
                    0
                """
        )
    )

    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Program
                open System.Threading.Tasks
                type Runner() =
                    member _.Run(t: Task) =
                        t.Wait()
                        0
                """
        )
    )

[<Fact>]
let ``FR0049: WaitAll with a timeout or a token outside a CE is the bounded idiom`` () =
    // Mibo's benchmark: `while not (Task.WaitAll(tasks, 1)) do pump ()`
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let pump (tasks: Task[]) =
                    while not (Task.WaitAll(tasks, 1)) do
                        ()
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let pump (tasks: Task[]) (cts: System.Threading.CancellationTokenSource) =
                    Task.WaitAll(tasks, cts.Token)
                """
        )
    )

    // two tasks params-style is the unbounded wait
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let join (a: Task) (b: Task) =
                    Task.WaitAll(a, b)
                """
        )
    )

[<Fact>]
let ``FR0049: a task complete from birth is drained without a wait`` () =
    // the test-fixture habit: `.Result` on a `Task.FromResult` stand-in
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let v = (Task.FromResult 1).Result
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f () =
                    let t = Task.FromResult 1
                    t.Result + 1
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let fixture = Task.FromResult 1
                let f () = task { return fixture.Result + 1 }
                """
        )
    )

    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f () =
                    let t = ValueTask.FromResult 1
                    t.GetAwaiter().GetResult()
                """
        )
    )

    // a task from anywhere else is not known complete
    Assert.NotEmpty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (make: unit -> Task<int>) =
                    let t = make ()
                    t.Result
                """
        )
    )

[<Fact>]
let ``FR0049: a Result read after the receiver's own Wait drains what was waited for`` () =
    // suave's Testing.send: `send.Wait(timeout, token)` is the bounded wait
    // two lines above the `send.Result` that only reads the outcome
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let send (t: Task<int>) (timeout: System.TimeSpan) =
                    let completed = t.Wait timeout
                    if not completed then failwith "timeout"
                    t.Result
                """
        )
    )

    // an unbounded Wait above keeps its own note; the read after it is quiet
    match
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (t: Task<int>) = task {
                    t.Wait()
                    return t.Result
                }
                """
        )
    with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected the Wait alone, got %A" other

[<Fact>]
let ``FR0049: a synchronisation primitive's wait inside a task is named and left to the author`` () =
    // Mibo's tests: `doneSignal.Wait()` before `do! worker` in task { }
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let f (doneSignal: ManualResetEventSlim) (worker: Task) = task {
                doneSignal.Wait()
                do! worker
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.PrimitiveWait "ManualResetEventSlim.Wait()", s.Kind)
        Assert.Equal(Some "task", s.Builder)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected one primitive wait, got %A" other

    match
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading
                let f (sem: SemaphoreSlim) (ev: ManualResetEvent) (th: Thread) = async {
                    sem.Wait()
                    ev.WaitOne() |> ignore
                    th.Join()
                    return 1
                }
                """
        )
        |> List.map (fun s -> s.Kind)
    with
    | [ SyncOverAsync.BlockKind.PrimitiveWait a
        SyncOverAsync.BlockKind.PrimitiveWait b
        SyncOverAsync.BlockKind.PrimitiveWait c ] ->
        Assert.Equal("SemaphoreSlim.Wait()", a)
        Assert.Equal("ManualResetEvent.WaitOne()", b)
        Assert.Equal("Thread.Join()", c)
    | other -> failwithf "Expected three primitive waits, got %A" other

    // outside a CE the primitives are ordinary synchronous code
    Assert.Empty(
        blockingIn (
            fsharp
                """
                module Test
                open System.Threading
                let f (doneSignal: ManualResetEventSlim) (th: Thread) =
                    doneSignal.Wait()
                    th.Join()
                """
        )
    )

[<Fact>]
let ``a thread-choreographed private drain is not taskified`` () =
    // the body waits on a signal and continues on that thread; task-returning
    // it would not — the same refusal as FR0142's
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let private fetch (x: int) =
                let signal = new ManualResetEventSlim(false)
                let t = Task.Run(fun () -> signal.Set(); x)
                signal.Wait()
                t.GetAwaiter().GetResult()
            let consume () = task {
                let s = fetch 1
                return s
            }
            """

    Assert.Empty(taskifyIn source)

[<Fact>]
let ``a thread-choreographed task body gets no async-overload rewrite`` () =
    let source =
        fsharp
            """
            open System.IO
            open System.Threading
            let head (reader: TextReader) = task {
                let signal = new ManualResetEventSlim(false)
                signal.Wait()
                let line = reader.ReadLine()
                return line
            }
            """

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a wait inside a thread-choreographed task body is noted without a fix`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let f () = task {
                let signal = new ManualResetEventSlim(false)
                let t = Task.Run(fun () -> signal.Set())
                signal.Wait()
                t.Wait()
                return 1
            }
            """

    match
        blockingIn source
        |> List.filter (fun s -> s.Kind = SyncOverAsync.BlockKind.TaskWait)
    with
    | [ s ] ->
        Assert.Equal(Some "task", s.Builder)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected one noted TaskWait site, got %A" other

[<Fact>]
let ``FR0049: Result on a ContinueWith antecedent is noted for its AggregateException, never as blocking`` () =
    let source =
        fsharp
            """
            open System.Threading.Tasks
            let f (t: Task<int>) =
                t.ContinueWith(fun (a: Task<int>) -> a.Result + 1)
            """

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)
        Assert.Empty s.AlternativeFixes

        // the continuation is a bind: the same task { let! } FR0049 writes
        // everywhere, never a GetAwaiter().GetResult() — the spelling the
        // rule exists to remove
        match s.Fixes with
        | [ (r, _, replacement) ] ->
            Assert.Equal(
                fsharp
                    """
                    task {
                            let! r = t
                            return r + 1
                        }
                    """,
                replacement
            )

            let patched = applyEdit source r replacement
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected one bind edit, got %A" other
    | other -> failwithf "Expected exactly one antecedent note, got %A" other

    // without a task builder (FSharp.Core before 6) ContinueWith IS the
    // bind: nothing is reported
    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(SyncOverAsync.findWith false tree sourceText checkResults)

    // a continuation that handles the antecedent itself keeps the note and
    // gets no rewrite; so does one handed a scheduler
    let handled =
        blockingIn (
            fsharp
                """
                open System.Threading.Tasks
                let f (t: Task<int>) =
                    t.ContinueWith(fun (a: Task<int>) -> if a.IsFaulted then 0 else a.Result + 1)
                """
        )

    Assert.All(handled, (fun s -> Assert.Empty s.Fixes))

    let scheduled =
        blockingIn (
            fsharp
                """
                open System.Threading.Tasks
                let f (t: Task<int>) =
                    t.ContinueWith((fun (a: Task<int>) -> a.Result + 1), TaskScheduler.Default)
                """
        )

    Assert.All(scheduled, (fun s -> Assert.Empty s.Fixes))

[<Fact>]
let ``FR0049: an antecedent read with no free binder name is noted without a rewrite`` () =
    // every candidate binder is already a name in the body: the note stands,
    // the rewrite steps aside (it must not raise out of the analyzer)
    let source =
        fsharp
            """
            open System.Threading.Tasks
            let f (t: Task<int>) (r: int) (result: int) (aValue: int) =
                t.ContinueWith(fun (a: Task<int>) -> a.Result + r + result + aValue)
            """

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one antecedent note, got %A" other

[<Fact>]
let ``FR0049: Task.Run around a RunSynchronously becomes Async.StartAsTask`` () =
    // Task.Run queues the lambda to the thread pool and hands back its Task -
    // Async.StartAsTask does exactly that without parking a pool thread on the
    // result, so the lambda (and the blocking wait inside it) goes away
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let! x = System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously)
                return x
            }
            """

    match blockingIn source with
    | [ s ] ->
        Assert.True(s.InLambda)

        match s.Fixes with
        | [ (_, _, "comp |> Async.StartAsTask") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the StartAsTask fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: an ignored Task.Run keeps do-bang through an upcast`` () =
    // `|> ignore` makes Task.Run return the non-generic Task that `do!` wants;
    // Async.StartAsTask returns Task<'T>, which `do!` refuses, so the fix
    // upcasts rather than changing the statement into a bind it cannot end on
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                do! System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously |> ignore)
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "(comp |> Async.StartAsTask) :> System.Threading.Tasks.Task") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the upcast StartAsTask fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a Task.Run lambda that does more than block keeps the note alone`` () =
    // the rewrite only holds when the lambda is nothing but the blocking call;
    // anything else in there still has to run on the pool
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let! x = System.Threading.Tasks.Task.Run(fun () -> let v = comp |> Async.RunSynchronously in v + 1)
                return x
            }
            """

    match blockingIn source with
    | [ s ] -> Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a thread-choreographed body still gets the Task.Run rewrite`` () =
    // the thread-bound veto withholds binds because a bind resumes elsewhere;
    // this rewrite adds no bind and moves no continuation, so it stands even
    // next to the SynchronizationContext that trips the veto
    let source =
        fsharp
            """
            let comp = async { return 1 }
            let f () = task {
                let ctx = System.Threading.SynchronizationContext.Current
                let! x = System.Threading.Tasks.Task.Run(fun () -> comp |> Async.RunSynchronously)
                return x + (if isNull ctx then 0 else 1)
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "comp |> Async.StartAsTask") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the StartAsTask fix to survive the veto, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a name merely ENDING in Thread is not thread choreography`` () =
    // the veto read "Thread(" as a substring, so ThrowIfNotOnUIThread() -
    // and every other VS threading helper, they are all spelled that way -
    // counted as choreography and withheld the fixes for a whole file
    let source =
        fsharp
            """
            let throwIfNotOnUIThread () = ()
            let f (t: System.Threading.Tasks.Task) = task {
                throwIfNotOnUIThread()
                t.Wait()
                return 1
            }
            """

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, "t.Wait()", "do! t") ] ->
            let patched = applyFixes source s.Fixes
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected the do! fix to survive the veto, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a real Thread construction is still thread choreography`` () =
    // the narrowing must not cost the case the veto exists for
    let source =
        fsharp
            """
            let f (t: System.Threading.Tasks.Task) = task {
                let worker = System.Threading.Thread(System.Threading.ThreadStart(fun () -> ()))
                worker.Start()
                t.Wait()
                return 1
            }
            """

    match blockingIn source with
    | [ s ] -> Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a bare Thread member is still thread choreography`` () =
    let source =
        fsharp
            """
            open System.Threading
            let f (t: System.Threading.Tasks.Task) = task {
                let id = Thread.CurrentThread.ManagedThreadId
                t.Wait()
                return id
            }
            """

    match blockingIn source with
    | [ s ] -> Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0168: a try in the middle of a line rewrites to a match whose arms compile`` () =
    let source =
        fsharp
            """
            module Test
            open System
            let parse (s: string) =
                let n = try Int32.Parse s with _ -> 0
                n + 1
            let inline' (s: string) = 1 + (try Int32.Parse s with _ -> 0)
            """

    match parseControlFlowIn source with
    | [ a; b ] ->
        let patched =
            [ a; b ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold
                (fun acc s ->
                    s.Offers.Head.Edits
                    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) acc)
                source

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected two findings, got %A" other

// ---- FR0119 AwaitableOverload: AwaitTask raises AggregateException ----

[<Fact>]
let ``FR0119 inside async a site under try-with keeps its blocking call`` () =
    // `Async.AwaitTask` surfaces a faulted task as AggregateException, so
    // `with :? IOException` would stop catching what ReadLine threw bare
    let source =
        fsharp
            """
            open System.IO
            let head (reader: TextReader) = async {
                try
                    let line = reader.ReadLine()
                    return line
                with :? IOException -> return ""
            }
            """

    Assert.Empty(awaitableIn source)

    // a try/with around the run of the computation catches the same way
    let outer =
        fsharp
            """
            open System.IO
            let head (reader: TextReader) =
                try
                    async {
                        let line = reader.ReadLine()
                        return line
                    }
                    |> Async.RunSynchronously
                with :? IOException -> ""
            """

    Assert.Empty(awaitableIn outer)

    // task { } awaits the bare exception: still fixed there
    let inTask =
        fsharp
            """
            open System.IO
            let head (reader: TextReader) = task {
                try
                    let line = reader.ReadLine()
                    return line
                with :? IOException -> return ""
            }
            """

    Assert.Single(awaitableIn inTask) |> ignore

// ---- FR0049 Taskify: closures in the body, AggregateException in async callers ----

[<Fact>]
let ``FR0049 taskify leaves a drain inside a local function or object expression alone`` () =
    // `let!` inside `let g () = ...` lands in a plain function — FS0750
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    let g () =
                        let r = t.Result
                        r + 1
                    g ()
                let consume () = task {
                    let s = fetch 1
                    return s
                }
                """
        )
    )

    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    let o =
                        { new Object() with
                            member _.ToString() =
                                let r = t.Result
                                string r }
                    o.ToString()
                let consume () = task {
                    let s = fetch 1
                    return s
                }
                """
        )
    )

    // a caller inside a local function of the CE cannot bind either
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    t.GetAwaiter().GetResult()
                let consume () = task {
                    let h () =
                        let s = fetch 1
                        s
                    return h ()
                }
                """
        )
    )

[<Fact>]
let ``FR0049 taskify keeps a GetResult drain whose caller is async`` () =
    // GetResult threw the task's exception bare; `Async.AwaitTask` raises
    // AggregateException, so the caller's `with :? IOException` stops catching
    Assert.Empty(
        taskifyIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let private fetch (x: int) =
                    let t = Task.Run(fun () -> x)
                    t.GetAwaiter().GetResult()
                let consume () = async {
                    let s = fetch 2
                    return s
                }
                """
        )
    )

// ---- FR0118 CancellationOverload: cleanup callbacks, handlers, shadowed names ----

[<Fact>]
let ``FR0118 no token is handed to a call inside the token's Register callback`` () =
    // the callback runs BECAUSE the token was cancelled: the call would
    // throw OperationCanceledException instead of cleaning up
    let source =
        fsharp
            """
            open System.IO
            open System.Threading
            let watch (s: Stream) (ct: CancellationToken) =
                ct.Register(fun () -> s.FlushAsync() |> ignore) |> ignore
                0
            """

    Assert.Empty(cancellationIn source)

[<Fact>]
let ``FR0118 a name shadowing the token is not taken for it`` () =
    // `ct` inside the comprehension is the string, not the token
    let source =
        fsharp
            """
            open System.Net.Http
            open System.Threading
            let fetch (client: HttpClient) (ct: CancellationToken) =
                [ for ct in [ "a" ] -> client.GetStringAsync("u") ]
            """

    Assert.Empty(cancellationIn source)

[<Fact>]
let ``FR0118 a loop inside a with handler gets no cancellation check`` () =
    // the handler is cleanup: a check there throws on the way out
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let f (ct: CancellationToken) (handle: int -> Task) = task {
                try
                    return 1
                with _ ->
                    let mutable i = 0
                    while i < 3 do
                        do! handle i
                        i <- i + 1
                    return 0
            }
            """

    Assert.Empty(unobservedLoopsIn source)

// ---- FR0053 HexString: an indexer or slice right after the chain ----

[<Fact>]
let ``FR0053 a trailing slice or indexer keeps the call parenthesised`` () =
    // the space form left `ToHexString hash[..7]`: the slice OF THE BYTES
    for tail in [ "[..7]"; ".[..7]"; "[0]"; ".[0]" ] do
        let source =
            $"module Test\nlet f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \"\"){tail}"

        match hexIn source with
        | [ s ] ->
            Assert.Equal("(System.Convert.ToHexString bytes)", s.ReplacementText)
            let patched = applyEdit source s.Range s.ReplacementText
            assertTypechecks "Patched source" patched
        | other -> failwithf "Expected exactly one hex suggestion for %s, got %A" tail other
