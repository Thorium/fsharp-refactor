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
        blockingIn
            "open System.Threading\nopen System.Threading.Tasks\nlet f () =\n    let signal = new ManualResetEventSlim(false)\n    let worker = Task.Run(fun () -> signal.Set())\n    signal.Wait()\n    worker.Wait()"
    )

    // the same wait without the choreography keeps its note
    match
        blockingIn "open System.Threading.Tasks\nlet g () =\n    let worker = Task.Run(fun () -> 1)\n    worker.Wait()"
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
    match blockingIn "let f () = async {\n    System.Threading.Thread.Sleep 100\n    return 1\n}" with
    | [ s ] ->
        match s.Fixes with
        | [ (r, _, replacement) ] ->
            Assert.Equal("do! Async.Sleep 100", replacement)

            let source =
                "let f () = async {\n    System.Threading.Thread.Sleep 100\n    return 1\n}"

            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | _ -> failwith "Expected a fix for Thread.Sleep"
    | other -> failwithf "Expected exactly one Sleep site, got %A" other

[<Fact>]
let ``Thread Sleep in sync code is legitimate`` () =
    Assert.Empty(blockingIn "let f () = System.Threading.Thread.Sleep 100")

[<Fact>]
let ``a user type with a Result property is not a task`` () =
    Assert.Empty(blockingIn "type R() =\n    member _.Result = 1\nlet f (r: R) = task { return r.Result }")

[<Fact>]
let ``binding with let-bang is fine`` () =
    Assert.Empty(blockingIn "let f (t: System.Threading.Tasks.Task<int>) = task {\n    let! x = t\n    return x\n}")

// ---- FR0050 / FR0051 Accumulation ----

let private accumulationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Accumulation.find tree sourceText checkResults

let private assertFold (source: string) (expectedReplacement: string) =
    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``sum accumulation becomes Seq sum`` () =
    assertFold
        "let f (xs: int list) =\n    let mutable total = 0\n    for x in xs do\n        total <- total + x\n    total * 2"
        "let total = xs |> List.sum"

[<Fact>]
let ``projected sum becomes sumBy`` () =
    assertFold
        "let f (xs: int list) =\n    let mutable total = 0\n    for x in xs do\n        total <- total + x * x\n    total"
        "xs |> List.sumBy (fun x -> x * x)"

[<Fact>]
let ``general combine becomes a fold`` () =
    assertFold
        "let f (xs: int list) =\n    let mutable best = 1\n    for x in xs do\n        best <- max best (x % 7)\n    best"
        "xs |> List.fold (fun best x -> max best (x % 7)) 1"

[<Fact>]
let ``reassignment after the loop keeps the mutable`` () =
    let folds, _ =
        accumulationIn
            "let f (xs: int list) =\n    let mutable total = 0\n    for x in xs do\n        total <- total + x\n    total <- total + 1\n    total"

    Assert.Empty folds

[<Fact>]
let ``counting a non-generic IEnumerable stays a loop`` () =
    // from the corpus (SQLProvider SeqValues): `for` accepts the non-generic
    // IEnumerable, Seq.sumBy needs seq<'T> — the rewrite would be FS0001
    let folds, _ =
        accumulationIn
            "let f (values: System.Collections.IEnumerable) =\n    let mutable count = 0\n    for v in values do\n        count <- count + 1\n    count"

    Assert.Empty folds

[<Fact>]
let ``quadratic list append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn
            "let f (xs: int list) =\n    let mutable acc: int list = []\n    for x in xs do\n        if x > 0 then acc <- acc @ [ x ]\n    acc"

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one quadratic note, got %A" other

[<Fact>]
let ``quadratic Array append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn
            "let f (xs: int list) =\n    let mutable acc: int[] = [||]\n    for x in xs do\n        if x > 0 then acc <- Array.append acc [| x |]\n    acc"

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
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one flag-loop suggestion, got %A" other

[<Fact>]
let ``a false flag set in a loop becomes exists`` () =
    assertFlagRewrite
        "let f (xs: int list) =\n    let mutable found = false\n    for x in xs do\n        if x > 3 then found <- true\n    found"
        "let found = xs |> List.exists (fun x -> x > 3)"

[<Fact>]
let ``an array source resolves to Array exists`` () =
    assertFlagRewrite
        "let f (xs: int[]) =\n    let mutable found = false\n    for x in xs do\n        if x > 3 then found <- true\n    found"
        "let found = xs |> Array.exists (fun x -> x > 3)"

[<Fact>]
let ``a true flag falsified in a loop becomes forall`` () =
    assertFlagRewrite
        "let f (xs: int list) =\n    let mutable ok = true\n    for x in xs do\n        if x < 0 then ok <- false\n    ok"
        "let ok = xs |> List.forall (fun x -> not (x < 0))"

[<Fact>]
let ``a negated predicate in the forall dual loses its not`` () =
    assertFlagRewrite
        "let valid (x: int) = x >= 0\nlet f (xs: int list) =\n    let mutable ok = true\n    for x in xs do\n        if not (valid x) then ok <- false\n    ok"
        "let ok = xs |> List.forall (fun x -> (valid x))"

[<Fact>]
let ``a second statement in the loop body keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn
            "let f (xs: int list) =\n    let mutable found = false\n    let mutable count = 0\n    for x in xs do\n        count <- count + 1\n        if x > 3 then found <- true\n    found"
    )

[<Fact>]
let ``a side-effecting predicate keeps the mutable`` () =
    // exists short-circuits — a predicate with visible effects would run
    // fewer times after the rewrite
    Assert.Empty(
        flagLoopsIn
            "let f (xs: int list) =\n    let mutable found = false\n    let mutable seen = 0\n    for x in xs do\n        if (seen <- seen + 1; x > 3) then found <- true\n    found, seen"
    )

[<Fact>]
let ``an else branch keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn
            "let g () = ()\nlet f (xs: int list) =\n    let mutable found = false\n    for x in xs do\n        if x > 3 then found <- true else g ()\n    found"
    )

[<Fact>]
let ``flag reassignment after the loop keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn
            "let f (xs: int list) =\n    let mutable found = false\n    for x in xs do\n        if x > 3 then found <- true\n    found <- found && xs.Length > 1\n    found"
    )

[<Fact>]
let ``a predicate reading the flag keeps the mutable`` () =
    Assert.Empty(
        flagLoopsIn
            "let f (xs: int list) =\n    let mutable found = false\n    for x in xs do\n        if not found && x > 3 then found <- true\n    found"
    )

[<Fact>]
let ``a non-generic IEnumerable source keeps the mutable`` () =
    // `for` accepts it; List/Array/Seq.exists do not
    Assert.Empty(
        flagLoopsIn
            "let f (values: System.Collections.IEnumerable) =\n    let mutable found = false\n    for v in values do\n        if hash v > 3 then found <- true\n    found"
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
    match hexIn "module Test\nlet f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \"\")" with
    | [ s ] -> Assert.Equal("System.Convert.ToHexString bytes", s.ReplacementText)
    | other -> failwithf "Expected exactly one hex suggestion, got %A" other


[<Fact>]
let ``a trailing member access keeps the call parenthesised`` () =
    // prismatic: the space form left `ToHexString hash.Substring(0, 16)`,
    // handing the substring OF THE BYTES to ToHexString
    let source =
        "module Test\nlet f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \"\").Substring(0, 16)"

    match hexIn source with
    | [ s ] ->
        Assert.Equal("(System.Convert.ToHexString bytes)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one hex suggestion, got %A" other

[<Fact>]

let ``other Replace arguments are left alone`` () =
    Assert.Empty(hexIn "module Test\nlet f (bytes: byte[]) = System.BitConverter.ToString(bytes).Replace(\"-\", \":\")")

// ---- FR0055 SwallowedException ----

let private swallowedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SwallowedException.find tree sourceText (Some checkResults)

[<Fact>]
let ``empty wildcard catch is noted`` () =
    match swallowedIn "module Test\nlet f (act: unit -> unit) =\n    try act ()\n    with _ -> ()" with
    | [ s ] -> Assert.Equal("_", s.PatternText)
    | other -> failwithf "Expected exactly one swallow note, got %A" other

[<Fact>]
let ``empty typed Exception catch is noted`` () =
    match
        swallowedIn "module Test\nlet f (act: unit -> unit) =\n    try act ()\n    with :? System.Exception -> ()"
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one typed swallow note, got %A" other

[<Fact>]
let ``handler that does something is fine`` () =
    Assert.Empty(
        swallowedIn "module Test\nlet f (act: unit -> unit) =\n    try act ()\n    with ex -> printfn \"%s\" ex.Message"
    )

[<Fact>]
let ``deliberately ignoring a specific exception is fine`` () =
    Assert.Empty(
        swallowedIn
            "module Test\nlet f (act: unit -> unit) =\n    try act ()\n    with :? System.OperationCanceledException -> ()"
    )

[<Fact>]
let ``a catch-all after a rethrown cancellation is not blind`` () =
    // the compiler's NameResolution: `:? OperationCanceledException ->
    // reraise ()` first, then `_ -> None`
    Assert.Empty(
        swallowedIn
            "module Test\nlet f (act: unit -> int) =\n    try\n        Some(act ())\n    with\n    | :? System.OperationCanceledException -> reraise ()\n    | _ -> None"
    )

[<Fact>]
let ``a catch-all followed by an unconditional failure converts the swallow into a failure`` () =
    // DiagnosticsLogger's exiter: `try Environment.Exit n with _ -> ()`
    // and then a failwith — the exception is replaced, not lost
    Assert.Empty(
        swallowedIn
            "module Test\nlet exit (n: int) : int =\n    try\n        System.Environment.Exit n\n    with _ ->\n        ()\n\n    failwith \"exit did not exit\""
    )

[<Fact>]
let ``a one-call teardown body is the best-effort release idiom`` () =
    // Suave's `try acceptSocket.Shutdown ... with _ -> ()`, `try
    // s.Dispose(); s <- null with _ -> ()`, `try File.Delete p with _ -> ()`
    let teardownOf (source: string) =
        match swallowedIn source with
        | [ s ] -> s.Teardown
        | other -> failwithf "Expected exactly one swallow note, got %A" other

    Assert.True(teardownOf "module Test\nlet close (s: System.IO.Stream) =\n    try s.Dispose() with _ -> ()")

    Assert.True(
        teardownOf
            "module Test\ntype T() =\n    let mutable s: System.IO.Stream = null\n    member _.Close() =\n        try\n            s.Dispose()\n            s <- null\n        with _ -> ()"
    )

    Assert.True(teardownOf "module Test\nlet cleanup (p: string) =\n    try System.IO.File.Delete p with ex -> ()")

    // a call to anything else is a swallow around real work
    Assert.False(teardownOf "module Test\nlet f (act: unit -> unit) =\n    try act () with _ -> ()")

    Assert.False(
        teardownOf
            "module Test\nlet f (s: System.IO.Stream) (bytes: byte[]) =\n    try s.Write(bytes, 0, bytes.Length) with _ -> ()"
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
        fallbackOf
            "module Test\nlet create (path: string) =\n    try\n        System.IO.Directory.CreateDirectory path |> ignore\n        path\n    with _ ->\n        path"
    )

    Assert.Equal(
        Some "(state, Completed None)",
        fallbackOf
            "module Test\ntype Step =\n    | Completed of int option\nlet run (state: int) (f: int -> int * Step) =\n    try f state\n    with _ -> (state, Completed None)"
    )

    Assert.Equal(
        Some "System.Int32.MaxValue",
        fallbackOf "module Test\nlet index (s: string) =\n    try int32 s\n    with _ -> System.Int32.MaxValue"
    )

    Assert.Equal(
        Some "System.DateTime.MaxValue",
        fallbackOf
            "module Test\nlet stamp (p: string) =\n    try\n        let fi = System.IO.FileInfo p\n        System.IO.File.GetLastWriteTime fi.FullName\n    with _ ->\n        System.DateTime.MaxValue"
    )

    // a tuple of plain names carries no default: it is a computed answer
    Assert.Empty(
        swallowedIn
            "module Test\nlet run (state: int) (other: int) (f: int -> int * int) =\n    try f state\n    with _ -> (state, other)"
    )

[<Fact>]
let ``a guard that never looks at the exception still swallows every one`` () =
    // fsdocs: `with _ when watch -> ()`
    match
        swallowedIn
            "module Test\nlet copy (watch: bool) (src: string) (dst: string) =\n    try System.IO.File.Copy(src, dst, true)\n    with _ when watch -> ()"
    with
    | [ s ] -> Assert.Equal("_ when watch", s.PatternText)
    | other -> failwithf "Expected exactly one guarded swallow note, got %A" other

    // a guard on the exception itself is a decision
    Assert.Empty(
        swallowedIn
            "module Test\nlet copy (src: string) (dst: string) =\n    try System.IO.File.Copy(src, dst, true)\n    with ex when ex.Message.Contains \"locked\" -> ()"
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
        probeOf "module Test\nlet has (p: string) =\n    try System.IO.File.Exists p\n    with _ -> false"
    )

    Assert.Equal(
        Some "Directory.Exists",
        probeOf
            "module Test\nlet has (p: string) =\n    (try\n        System.IO.Directory.Exists(p)\n     with _ ->\n        false)"
    )

    Assert.Equal(
        Some "File.GetLastWriteTime",
        probeOf
            "module Test\nlet stamp (p: string) =\n    try System.IO.File.GetLastWriteTime p\n    with _ -> System.DateTime.MaxValue"
    )

    // a body doing more than the probe is not a probe
    Assert.Equal(
        None,
        probeOf
            "module Test\nlet stamp (p: string) =\n    try\n        let fi = System.IO.FileInfo p\n        System.IO.File.GetLastWriteTime fi.FullName\n    with _ ->\n        System.DateTime.MaxValue"
    )

// ---- FR0054 RaiseInSpecialMember ----

let private objectRulesIn (source: string) =
    let tree, sourceText = parse source
    ObjectRules.find tree sourceText

[<Fact>]
let ``failwith inside GetHashCode is noted`` () =
    let _, _, raises =
        objectRulesIn
            "module Test\ntype T() =\n    override _.Equals(o) = false\n    override _.GetHashCode() = failwith \"no hash\""

    match raises with
    | [ s ] -> Assert.Equal("GetHashCode", s.MemberName)
    | other -> failwithf "Expected exactly one raise-in-special note, got %A" other

[<Fact>]
let ``ToString returning a value is fine`` () =
    let _, _, raises =
        objectRulesIn "module Test\ntype T() =\n    override _.ToString() = \"t\""

    Assert.Empty raises

// ---- FR0058 RecursiveSeq ----

let private recursiveSeqIn (source: string) =
    let tree, sourceText = parse source
    RecursiveSeq.find tree sourceText

[<Fact>]
let ``a rec function yielding itself through seq is noted`` () =
    match
        recursiveSeqIn
            "module Test\nlet rec countDown n = seq {\n    yield n\n    if n > 0 then yield! countDown (n - 1)\n    yield -1\n}"
    with
    | [ s ] ->
        Assert.Equal("countDown", s.FunctionName)
        Assert.Equal("seq", s.Builder)
    | other -> failwithf "Expected exactly one recursive-seq note, got %A" other

[<Fact>]
let ``self-reference via Seq collect inside the seq is also caught`` () =
    match
        recursiveSeqIn
            "module Test\nlet rec walk (xs: int list list) = seq {\n    yield xs.Length\n    yield! Seq.collect walk []\n}"
    with
    | [ s ] -> Assert.Equal("walk", s.FunctionName)
    | other -> failwithf "Expected exactly one collect-form note, got %A" other

[<Fact>]
let ``a non-recursive seq is fine`` () =
    Assert.Empty(recursiveSeqIn "module Test\nlet numbers n = seq {\n    for i in 1..n do\n        yield i * i\n}")

[<Fact>]
let ``recursion outside any seq is fine`` () =
    Assert.Empty(
        recursiveSeqIn "module Test\nlet rec fact n = if n <= 1 then 1 else n * fact (n - 1)\nlet s = seq { yield 1 }"
    )

// ---- FR0057 XmlDocParams ----

let private xmlDocsIn (source: string) =
    let tree, sourceText = parse source
    XmlDocParams.find tree sourceText

[<Fact>]
let ``a missing param tag is noted`` () =
    match
        xmlDocsIn
            "module Test\n/// <summary>Scales.</summary>\n/// <param name=\"value\">The value.</param>\nlet scale (value: int) (factor: int) = value * factor"
    with
    | [ s ] ->
        Assert.Equal("scale", s.BindingName)
        Assert.Equal<string list>([ "factor" ], s.MissingParams)
    | other -> failwithf "Expected exactly one doc-drift note, got %A" other

[<Fact>]
let ``fully documented parameters are fine`` () =
    Assert.Empty(
        xmlDocsIn
            "module Test\n/// <summary>Scales.</summary>\n/// <param name=\"value\">The value.</param>\n/// <param name=\"factor\">The factor.</param>\nlet scale (value: int) (factor: int) = value * factor"
    )

[<Fact>]
let ``undocumented functions are a style choice`` () =
    Assert.Empty(xmlDocsIn "module Test\n/// Scales a value.\nlet scale (value: int) (factor: int) = value * factor")

[<Fact>]
let ``a custom operation documents the DSL keyword not the signature`` () =
    Assert.Empty(
        xmlDocsIn
            "module Test\ntype Cfg() =\n    member _.Yield(_: unit) = 0\n    /// <summary>Sets the width.</summary>\n    /// <param name=\"w\">The width.</param>\n    [<CustomOperation \"width\">]\n    member _.Width(state: int, w: int) = state + w"
    )

[<Fact>]
let ``sync-over-async inside an object expression member is found`` () =
    // corpus regression: Dispose bodies in `{ new IDisposable with ... }`
    // hid GetResult calls from the walker
    match
        blockingIn
            "module Test\nopen System\nopen System.Threading.Tasks\nlet scope (t: Task) =\n    { new IDisposable with\n        member _.Dispose() = t.GetAwaiter().GetResult() }"
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one blocking note, got %A" other

[<Fact>]
let ``catch-all substituting an empty string is noted`` () =
    match swallowedIn "module Test\nlet f (read: unit -> string) =\n    try read ()\n    with _ -> \"\"" with
    | [ s ] -> Assert.Equal(Some "\"\"", s.FallbackText)
    | other -> failwithf "Expected exactly one fallback note, got %A" other

[<Fact>]
let ``catch-all substituting zero is noted`` () =
    match swallowedIn "module Test\nlet f (count: unit -> int) =\n    try count ()\n    with _ -> 0" with
    | [ s ] -> Assert.Equal(Some "0", s.FallbackText)
    | other -> failwithf "Expected exactly one zero-fallback note, got %A" other

[<Fact>]
let ``catch-all substituting defaultof is noted`` () =
    match
        swallowedIn
            "module Test\nlet f (get: unit -> string) =\n    try get ()\n    with _ -> Unchecked.defaultof<string>"
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected exactly one defaultof-fallback note, got %A" other

[<Fact>]
let ``the bool probe idiom stays quiet`` () =
    // `try ping (); true with _ -> false` — the failure IS the answer
    Assert.Empty(
        swallowedIn
            "module Test\nlet canPing (ping: unit -> unit) =\n    try\n        ping ()\n        true\n    with _ -> false"
    )

[<Fact>]
let ``the inverted did-it-throw probe stays quiet too`` () =
    Assert.Empty(
        swallowedIn
            "module Test\nlet throws (act: unit -> unit) =\n    try\n        act ()\n        false\n    with _ -> true"
    )

[<Fact>]
let ``a false fallback on a non-probe body is a disguise`` () =
    // the body computes a real bool; the catch-all rewrites failure as
    // `false`, indistinguishable from an honest negative
    match
        swallowedIn
            "module Test\nlet isValid (parse: string -> bool) (s: string) =\n    try parse s\n    with _ -> false"
    with
    | [ s ] -> Assert.Equal(Some "false", s.FallbackText)
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``a ValueNone fallback is a disguise`` () =
    match
        swallowedIn
            "module Test\nlet tryRead (read: unit -> int) =\n    try ValueSome(read ())\n    with _ -> ValueNone"
    with
    | [ s ] -> Assert.Equal(Some "ValueNone", s.FallbackText)
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``a specific exception with a default is a decision`` () =
    Assert.Empty(
        swallowedIn
            "module Test\nlet f (read: unit -> string) =\n    try read ()\n    with :? System.IO.FileNotFoundException -> \"\""
    )

[<Fact>]
let ``a string accumulator becomes String.concat, not a quadratic fold`` () =
    let folds, _ =
        accumulationIn
            "module Test\nlet joinAll (xs: string list) =\n    let mutable acc = \"\"\n    for x in xs do\n        acc <- acc + x\n    acc"

    match folds with
    | [ s ] -> Assert.Equal("xs |> String.concat \"\"", s.ReplacementText)
    | other -> failwithf "Expected exactly one string-concat fold, got %A" other

[<Fact>]
let ``a projected string accumulator maps then concats`` () =
    let folds, _ =
        accumulationIn
            "module Test\nlet render (xs: int list) =\n    let mutable acc = \"\"\n    for x in xs do\n        acc <- acc + string x\n    acc"

    match folds with
    | [ s ] -> Assert.Equal("xs |> List.map (fun x -> string x) |> String.concat \"\"", s.ReplacementText)
    | other -> failwithf "Expected exactly one mapped string concat, got %A" other

[<Fact>]
let ``a non-empty seed prefixes the concatenation`` () =
    let folds, _ =
        accumulationIn
            "module Test\nlet render (xs: string list) =\n    let mutable acc = \"head:\"\n    for x in xs do\n        acc <- acc + x\n    acc"

    match folds with
    | [ s ] -> Assert.Equal("\"head:\" + (xs |> String.concat \"\")", s.ReplacementText)
    | other -> failwithf "Expected exactly one seeded string concat, got %A" other

[<Fact>]
let ``ValueTask Result blocks like Task Result`` () =
    // post-core BCL async I/O returns ValueTask everywhere
    let suggestions =
        blockingIn "let f (vt: System.Threading.Tasks.ValueTask<int>) =\n    task {\n        return vt.Result\n    }"

    match suggestions with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskResult, s.Kind)
    | other -> failwithf "Expected exactly one ValueTask.Result note, got %A" other

[<Fact>]
let ``Task WaitAll is a blocking wait too`` () =
    let suggestions =
        blockingIn
            "let f (t1: System.Threading.Tasks.Task) =\n    task {\n        System.Threading.Tasks.Task.WaitAll [| t1 |]\n        return 1\n    }"

    match suggestions with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected exactly one WaitAll note, got %A" other

[<Fact>]
let ``a Thread.Sleep inside a nested seq gets no do-fix`` () =
    // `do!` in the seq body would call a Bind the seq builder lacks
    let suggestions =
        blockingIn
            "let f () =\n    async {\n        let xs = seq {\n            System.Threading.Thread.Sleep 100\n            yield 1\n        }\n        return Seq.length xs\n    }"

    Assert.NotEmpty suggestions
    Assert.True(suggestions |> List.forall (fun s -> s.Fixes.IsEmpty))

[<Fact>]
let ``a field-held concurrent queue count is an emptiness check too`` () =
    let suggestions =
        countsIn
            "type H() =\n    member val Queue = System.Collections.Concurrent.ConcurrentQueue<int>() with get\n    member this.Check() = this.Queue.Count = 0"

    match suggestions with
    | [ s ] -> Assert.Equal("this.Queue.IsEmpty", s.ReplacementText)
    | other -> failwithf "Expected exactly one count note, got %A" other

[<Fact>]
let ``a recursive member yielding itself through seq is noted`` () =
    // members are implicitly recursive — no `rec` keyword to find — and
    // OO-style tree APIs are where recursive seqs live
    let suggestions =
        recursiveSeqIn
            "module Test\ntype Node(children: Node list) =\n    member this.Descendants() : seq<int> = seq {\n        yield 1\n        for c in children do\n            yield! c.Descendants()\n    }"

    match suggestions with
    | [ s ] -> Assert.Equal("Descendants", s.FunctionName)
    | other -> failwithf "Expected exactly one recursive-member note, got %A" other

[<Fact>]
let ``quadratic List.append in a loop is noted`` () =
    let _, quadratics =
        accumulationIn
            "let f (xs: int list) =\n    let mutable acc: int list = []\n    for x in xs do\n        if x > 0 then acc <- List.append acc [ x ]\n    acc"

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one List.append note, got %A" other

[<Fact>]
let ``quadratic append through a ref cell is noted`` () =
    let _, quadratics =
        accumulationIn
            "let f (xs: int list) =\n    let acc = ref ([]: int list)\n    for x in xs do\n        acc.Value <- acc.Value @ [ x ]\n    acc.Value"

    match quadratics with
    | [ s ] -> Assert.Equal("acc", s.Name)
    | other -> failwithf "Expected exactly one ref-cell note, got %A" other

[<Fact>]
let ``a plain seq source still sums with the Seq module`` () =
    // the module-resolved output names List/Array when it can; a true
    // seq has nothing better than Seq.sum
    assertFold
        "let f (xs: int seq) =\n    let mutable total = 0\n    for x in xs do\n        total <- total + x\n    total"
        "xs |> Seq.sum"

[<Fact>]
let ``quadratic string building in a while loop is noted`` () =
    // measured: 57.8µs and 1MB per 1000 pieces against 1.6µs/4.6KB for a
    // StringBuilder — the worst string builder there is
    let _, quadratics =
        accumulationIn
            "let f (next: unit -> string option) =\n    let mutable acc = \"\"\n    let mutable go = true\n    while go do\n        match next () with\n        | Some s -> acc <- acc + s\n        | None -> go <- false\n    acc"

    match quadratics with
    | [ s ] ->
        Assert.Equal("acc", s.Name)
        Assert.Equal(Accumulation.QuadraticKind.Str, s.Kind)
    | other -> failwithf "Expected exactly one string-quadratic note, got %A" other

[<Fact>]
let ``numeric accumulation with plus is ordinary code`` () =
    let _, quadratics =
        accumulationIn
            "let f (next: unit -> int option) =\n    let mutable total = 0\n    let mutable go = true\n    while go do\n        match next () with\n        | Some n -> total <- total + n\n        | None -> go <- false\n    total"

    Assert.Empty quadratics

[<Fact>]
let ``the FR0050 string shape gets the fix, not the note`` () =
    // the fold fix rewrites this whole shape into one String.concat; a
    // note on the same site would nag about code the fix removes
    let folds, quadratics =
        accumulationIn
            "let render (xs: int list) =\n    let mutable acc = \"\"\n    for x in xs do\n        acc <- acc + string x\n    acc"

    Assert.Single folds |> ignore
    Assert.Empty quadratics

[<Fact>]
let ``a seq source materializes before String concat`` () =
    // the lazy-seq path through String.concat measured 42.7µs/194KB per
    // 1000 pieces against 2.6µs/2KB once materialized
    assertFold
        "let render (xs: int seq) =\n    let mutable acc = \"\"\n    for x in xs do\n        acc <- acc + string x\n    acc"
        "xs |> Seq.map (fun x -> string x) |> Seq.toArray |> String.concat \"\""

[<Fact>]
let ``a pure let prefix folds into the exists lambda`` () =
    // the opensSystem shape from our own code review: a let-bound
    // projection before the flag test is still an exists question
    assertFlagRewrite
        "let f (lines: string list) =\n    let mutable found = false\n    for l in lines do\n        let t = l.Trim()\n        if t = \"open System\" then found <- true\n    found"
        "let found = lines |> List.exists (fun l -> let t = l.Trim() in t = \"open System\")"

[<Fact>]
let ``a mutable let in the body keeps the flag loop`` () =
    Assert.Empty(
        flagLoopsIn
            "let f (xs: int list) =\n    let mutable found = false\n    for x in xs do\n        let mutable y = x + 1\n        if y > 3 then found <- true\n    found"
    )

[<Fact>]
let ``a GetResult binding inside task becomes a let bang bind`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = task {\n    let x = t.GetAwaiter().GetResult()\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (kwRange, _, "let!"); (rhsRange, _, receiver) ] ->
            Assert.Equal("t", receiver)
            let patched = applyEdit (applyEdit source rhsRange receiver) kwRange "let!"
            Assert.Contains("let! x = t", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
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
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
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
        "let f (t: System.Threading.Tasks.ValueTask<int>) = async {\n    let x = t.GetAwaiter().GetResult()\n    return x + 1\n}"

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a GetResult binding in a finally block keeps its hands off`` () =
    // let!/do! are illegal inside finally — the pre-existing Sleep fix
    // shared this hole
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = task {\n    try\n        return 1\n    finally\n        let x = t.GetAwaiter().GetResult()\n        ignore x\n}"

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``Thread Sleep in a finally block keeps its blocking form`` () =
    let source =
        "let f () = task {\n    try\n        return 1\n    finally\n        System.Threading.Thread.Sleep 100\n}"

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a type-annotated GetResult binding stays advice`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = task {\n    let x: int = t.GetAwaiter().GetResult()\n    return x + 1\n}"

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
        "let f (comp: Async<int>) = async {\n    let x = comp |> Async.RunSynchronously\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = comp", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one RunSynchronously site, got %A" other

[<Fact>]
let ``RunSynchronously binding inside task binds the async directly`` () =
    // the task builder's medium-priority overload binds Async<'T> with a
    // plain let! — no StartAsTask adapter needed
    let source =
        "let f (comp: Async<int>) = task {\n    let x = Async.RunSynchronously comp\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = comp", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one RunSynchronously site, got %A" other

[<Fact>]
let ``RunSynchronously with a timeout tuple stays advice`` () =
    let source =
        "let f (comp: Async<int>) = async {\n    let x = Async.RunSynchronously(comp, timeout = 100)\n    return x + 1\n}"

    for s in blockingIn source do
        Assert.Empty s.Fixes

[<Fact>]
let ``a GetResult binding inside async binds via AwaitTask`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = async {\n    let x = t.GetAwaiter().GetResult()\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = Async.AwaitTask t", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``a Result binding inside task becomes a plain bind`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = task {\n    let x = t.Result\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("let! x = t", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one Result site, got %A" other

[<Fact>]
let ``a Result binding on a call inside async parenthesizes the AwaitTask arg`` () =
    let source =
        "let g () = System.Threading.Tasks.Task.FromResult 2\nlet f () = async {\n    let x = (g ()).Result\n    return x + 1\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.NotEmpty s.Fixes
        let patched = applyAll source s.Fixes
        Assert.Contains("Async.AwaitTask (", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one Result site, got %A" other

[<Fact>]
let ``a ValueTask Result binding inside async stays advice`` () =
    // Async.AwaitTask has no ValueTask overload — no fix to offer there
    let source =
        "let f (t: System.Threading.Tasks.ValueTask<int>) = async {\n    let x = t.Result\n    return x + 1\n}"

    for s in blockingIn source do
        Assert.Empty s.Fixes

// ---- FR0118 CancellationOverload ----

let private cancellationIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    CancellationOverload.find tree sourceText checkResults

[<Fact>]
let ``an omitted token is appended from the in-scope parameter`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet pause (ct: CancellationToken) = task {\n    do! Task.Delay(100)\n    return 1\n}"

    match cancellationIn source with
    | [ s ] ->
        Assert.Equal(CancellationOverload.TokenGap.Omitted, s.Kind)
        Assert.Equal(", ct", s.Replacement)
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("Task.Delay(100, ct)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one token suggestion, got %A" other

[<Fact>]
let ``CancellationToken None is replaced by the in-scope token`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet pause (ct: CancellationToken) = task {\n    do! Task.Delay(100, CancellationToken.None)\n    return 1\n}"

    match cancellationIn source with
    | [ s ] ->
        Assert.Equal(CancellationOverload.TokenGap.NonePassed, s.Kind)
        let patched = applyEdit source s.Range s.Replacement
        Assert.Contains("Task.Delay(100, ct)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one propagation suggestion, got %A" other

[<Fact>]
let ``no token in scope means no suggestion`` () =
    Assert.Empty(
        cancellationIn "open System.Threading.Tasks\nlet pause () = task {\n    do! Task.Delay(100)\n    return 1\n}"
    )

[<Fact>]
let ``two tokens in scope make the choice a human call`` () =
    Assert.Empty(
        cancellationIn
            "open System.Threading\nopen System.Threading.Tasks\nlet pause (a: CancellationToken) (b: CancellationToken) = task {\n    do! Task.Delay(100)\n    return 1\n}"
    )

[<Fact>]
let ``a call already passing the token is left alone`` () =
    Assert.Empty(
        cancellationIn
            "open System.Threading\nopen System.Threading.Tasks\nlet pause (ct: CancellationToken) = task {\n    do! Task.Delay(100, ct)\n    return 1\n}"
    )

[<Fact>]
let ``a token passed as the PAYLOAD is not appended again`` () =
    // CreateLinkedTokenSource(ct) takes the token as its argument — a
    // params/two-token sibling overload would happily compile `(ct, ct)`
    Assert.Empty(
        cancellationIn
            "open System.Threading\nlet link (ct: CancellationToken) =\n    CancellationTokenSource.CreateLinkedTokenSource(ct)"
    )

[<Fact>]
let ``a NAMED argument defeats arity counting and vetoes the append`` () =
    // `cancellationToken = ct` may well BE the token; appending `, ct`
    // after a named argument is a syntax error besides
    Assert.Empty(
        cancellationIn
            "open System.Threading\nopen System.Threading.Tasks\ntype C() =\n    member _.Get(a: int) = Task.FromResult a\n    member _.Get(a: int, ct: CancellationToken) = Task.FromResult a\nlet f (c: C) (ct: CancellationToken) = task {\n    let! x = c.Get(a = 1)\n    return x\n}"
    )

[<Fact>]
let ``a method with no token overload is left alone`` () =
    Assert.Empty(
        cancellationIn "open System.Threading\nlet check (ct: CancellationToken) (s: string) = s.Contains(\"x\")"
    )

[<Fact>]
let ``a stored None binding is not rewritten`` () =
    // not an argument: replacing a binding's RHS rewrites intent the
    // scan cannot see
    Assert.Empty(
        cancellationIn
            "open System.Threading\nlet keep (ct: CancellationToken) =\n    let none = CancellationToken.None\n    none"
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
        "open System.IO\nlet head (reader: TextReader) = task {\n    let line = reader.ReadLine()\n    return line\n}"

    match awaitableIn source with
    | [ s ] ->
        Assert.Equal("ReadLine", s.MethodName)
        let patched = applyAwaitable source s
        Assert.Contains("let! line = reader.ReadLineAsync()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one awaitable suggestion, got %A" other


[<Fact>]
let ``a call nested in another binding's RHS is not a let-bang site`` () =
    // the prismatic shape: the call sits inside the CE's RANGE but not on
    // its statement spine, so `let!` there cannot compile — 21 rollbacks in
    // one sweep repo were all this
    let source =
        "open System.IO\nlet f (reader: TextReader) = task {\n    let pair =\n        let line = reader.ReadLine()\n        line, line.Length\n    return snd pair\n}"

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a statement nested in another binding's RHS is not a do-bang site`` () =
    let source =
        "open System.IO\nlet f (writer: TextWriter) (s: string) = task {\n    let n =\n        writer.Write(s)\n        1\n    return n\n}"

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a blocking statement inside task becomes do-bang`` () =
    let source =
        "open System.IO\nlet push (writer: TextWriter) (s: string) = task {\n    writer.Write(s)\n    return 1\n}"

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! writer.WriteAsync(s)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one statement suggestion, got %A" other

[<Fact>]
let ``inside async the twin bridges via AwaitTask`` () =
    let source =
        "open System.IO\nlet head (reader: TextReader) = async {\n    let line = reader.ReadLine()\n    return line\n}"

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("let! line = reader.ReadLineAsync() |> Async.AwaitTask", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one bridged suggestion, got %A" other

[<Fact>]
let ``outside any CE the blocking call is fine`` () =
    Assert.Empty(awaitableIn "open System.IO\nlet head (reader: TextReader) = reader.ReadLine()")

[<Fact>]
let ``inside a lambda within the task nothing fires`` () =
    Assert.Empty(
        awaitableIn
            "open System.IO\nlet all (readers: TextReader list) = task {\n    let lines = readers |> List.map (fun r -> r.ReadLine())\n    return lines\n}"
    )

[<Fact>]
let ``a method with no async twin is left alone`` () =
    Assert.Empty(awaitableIn "let f (s: string) = task {\n    let u = s.ToUpperInvariant()\n    return u\n}")

[<Fact>]
let ``FR0119 a local function inside the task is a plain function`` () =
    // its body is a closure the AST does not spell as a Lambda — a do!
    // injected there would land in ordinary code
    let source =
        "open System.IO\nlet go (writer: TextWriter) (s: string) = task {\n    let flushTwice () =\n        writer.Write(s)\n        writer.Write(s)\n    flushTwice ()\n    return 1\n}"

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``FR0119 the juxtaposed atomic argument is the common F# spelling`` () =
    let source =
        "open System.IO\nlet push (writer: TextWriter) (s: string) = task {\n    writer.Write s\n    return 1\n}"

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! writer.WriteAsync s", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
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
        "module Test\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = task {\n    let s = fetch 1\n    return s\n}"

    match taskifyIn source with
    | [ s ] ->
        Assert.Equal("fetch", s.Name)
        let patched = applyTaskify source s
        Assert.Contains("    task {\n        let t = Task.Run(fun () -> x)\n        return! t\n    }", patched)
        Assert.Contains("let! s = fetch 1", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one taskify suggestion, got %A" other

[<Fact>]
let ``an async caller bridges with Async.AwaitTask`` () =
    let source =
        "module Test\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = async {\n    let s = fetch 2\n    return s\n}"

    match taskifyIn source with
    | [ s ] ->
        let patched = applyTaskify source s
        Assert.Contains("let! s = Async.AwaitTask (fetch 2)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one async-caller suggestion, got %A" other

[<Fact>]
let ``a return-position caller becomes return-bang`` () =
    let source =
        "module Test\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = task {\n    return fetch 3\n}"

    match taskifyIn source with
    | [ s ] ->
        let patched = applyTaskify source s
        Assert.Contains("return! fetch 3", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one return-position suggestion, got %A" other

[<Fact>]
let ``a public function is a wider refactor and stays`` () =
    Assert.Empty(
        taskifyIn
            "module Test\nopen System.Threading.Tasks\nlet fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = task {\n    let s = fetch 1\n    return s\n}"
    )

[<Fact>]
let ``a caller outside any CE vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn
            "module Test\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = fetch 1 + 1"
    )

[<Fact>]
let ``a caller under a lambda inside the CE vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn
            "module Test\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\nlet consume () = task {\n    let xs = [ 1; 2 ] |> List.map (fun i -> fetch i)\n    return xs\n}"
    )

[<Fact>]
let ``a blocking site under a lambda in the body vetoes the rewrite`` () =
    Assert.Empty(
        taskifyIn
            "module Test\nopen System.Threading.Tasks\nlet private sum (xs: Task<int> list) =\n    xs |> List.map (fun t -> t.GetAwaiter().GetResult()) |> List.sum\nlet consume () = task {\n    let s = sum []\n    return s\n}"
    )

[<Fact>]
let ``an internal boundary drain taskifies across files under api-changes`` () =
    let sourceA =
        "module A\nlet internal fetch (x: int) =\n    let t = System.Threading.Tasks.Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()"

    let sourceB =
        "module B\nlet consume () = task {\n    let s = A.fetch 1\n    return s\n}"

    let treeA, sourceTextA, checkA, projectResults, _, _, recheck =
        parseAndCheckPair sourceA sourceB

    System.Environment.SetEnvironmentVariable("FSREF_API_CHANGES", "1")

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
        System.Environment.SetEnvironmentVariable("FSREF_API_CHANGES", null)

[<Fact>]
let ``an internal drain without api-changes stays a note`` () =
    let sourceA =
        "module A\nlet internal fetch2 (x: int) =\n    let t = System.Threading.Tasks.Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()"

    let sourceB =
        "module B\nlet consume () = task {\n    let s = A.fetch2 1\n    return s\n}"

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
        "let f (xs: int list) =\n    let mutable node = System.Text.StringBuilder()\n    for x in xs do\n        node <- node.Append x\n    node.ToString()"

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Contains("||> List.fold (fun node x -> node.Append x)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``a blocking call in a match arm of an async body, after use bindings, still gets its twin`` () =
    // CarmelNet's shape: `async { let! res = ... |> Async.Catch; match res with ... }`
    // with the blocking ReadToEnd two `use` bindings deep in an arm
    let source =
        "module Test\nopen System\nopen System.IO\nopen System.Net\nlet f (client: Net.Http.HttpClient) =\n    async {\n        let! res = async { return 1 } |> Async.Catch\n        match res with\n        | Choice1Of2 x -> return string x, None\n        | Choice2Of2 e when not (String.IsNullOrEmpty e.Message) -> return e.Message, Some e\n        | Choice2Of2 e ->\n            match e with\n            | :? WebException as wex when not (isNull wex.Response) ->\n                use stream = wex.Response.GetResponseStream()\n                use reader = new StreamReader(stream)\n                let err = reader.ReadToEnd()\n                return err, Some e\n            | _ -> return \"\", Some e\n    }"

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
        variantHasTwin
            "module Test\nopen System.IO\nlet f (reader: StreamReader) =\n    async {\n        let err = reader.ReadToEnd()\n        return err\n    }"
    )

[<Fact>]
let ``variant B: after use bindings`` () =
    Assert.True(
        variantHasTwin
            "module Test\nopen System.IO\nlet f (stream: Stream) =\n    async {\n        use reader = new StreamReader(stream)\n        let err = reader.ReadToEnd()\n        return err\n    }"
    )

[<Fact>]
let ``variant C: inside a match arm`` () =
    Assert.True(
        variantHasTwin
            "module Test\nopen System.IO\nlet f (reader: StreamReader) (x: int option) =\n    async {\n        match x with\n        | Some _ ->\n            let err = reader.ReadToEnd()\n            return err\n        | None -> return \"\"\n    }"
    )

[<Fact>]
let ``variant D: after a let-bang`` () =
    Assert.True(
        variantHasTwin
            "module Test\nopen System.IO\nlet f (reader: StreamReader) =\n    async {\n        let! res = async { return 1 } |> Async.Catch\n        let err = reader.ReadToEnd()\n        return err\n    }"
    )

[<Fact>]
let ``FR0057: the editor scaffold appends empty param tags after the last one`` () =
    let source =
        "module Test\n/// <summary>Scales.</summary>\n/// <param name=\"value\">The value.</param>\nlet scale (value: int) (factor: int) (offset: int) = value * factor + offset"

    match xmlDocsIn source with
    | [ s ] ->
        match s.Insertion with
        | Some(at, text) ->
            Assert.Equal(3, at.StartLine)
            Assert.Equal("\n/// <param name=\"factor\"></param>\n/// <param name=\"offset\"></param>", text)
            let patched = applyEdit source at text

            Assert.Equal(
                "module Test\n/// <summary>Scales.</summary>\n/// <param name=\"value\">The value.</param>\n/// <param name=\"factor\"></param>\n/// <param name=\"offset\"></param>\nlet scale (value: int) (factor: int) (offset: int) = value * factor + offset",
                patched
            )
        | None -> failwith "Expected a scaffold insertion"
    | other -> failwithf "Expected exactly one doc-drift note, got %A" other

[<Fact>]
let ``FR0058: a recursive yield! in tail position is a loop, not a nested enumerator`` () =
    // FSharp.Data's CSV reader: `yield! readLines (n + 1)` as the body's
    // last step compiles to a jump
    Assert.Empty(
        recursiveSeqIn "module Test\nlet rec readLines (n: int) = seq {\n    yield n\n    yield! readLines (n + 1)\n}"
    )

    Assert.Empty(
        recursiveSeqIn
            "module Test\nlet rec countDown n = seq {\n    yield n\n    if n > 0 then yield! countDown (n - 1) else ()\n}"
    )

[<Fact>]
let ``FR0058: a recursive yield! under a for is still noted`` () =
    match
        recursiveSeqIn
            "module Test\ntype Node = { Value: int; Children: Node list }\nlet rec walk (node: Node) = seq {\n    yield node.Value\n    for c in node.Children do\n        yield! walk c\n}"
    with
    | [ s ] -> Assert.Equal("walk", s.FunctionName)
    | other -> failwithf "Expected exactly one recursive-seq note, got %A" other

[<Fact>]
let ``FR0058: a self-call yielding a plain value nests nothing`` () =
    // FSharp.Data's innerText': the recursion returns a string, not a sequence
    Assert.Empty(
        recursiveSeqIn
            "module Test\ntype Node = | Text of string | Elem of Node list\nlet rec innerText (n: Node) =\n    match n with\n    | Text t -> t\n    | Elem content ->\n        seq {\n            for e in content do\n                yield innerText e\n        }\n        |> String.concat \"\""
    )

[<Fact>]
let ``FR0049: a blocking call inside a lambda within the computation is marked as such`` () =
    // FSharp.Data's CsvFile: `Func<_>(fun () -> ... |> Async.RunSynchronously)`
    // built inside async { } — the builder's bind cannot reach it
    match
        blockingIn
            "let read () = async { return 1 }\nlet f () = async {\n    let reader = System.Func<int>(fun () -> read () |> Async.RunSynchronously)\n    return reader.Invoke()\n}"
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
        objectRulesIn
            "module Test\n[<AbstractClass>]\ntype ObjectExprBase (x: int ref) as this =\n    do x.Value <- this.dup x.contents\n    abstract member dup: int -> int"

    match ctorCalls with
    | [ c ] -> Assert.Equal("dup", c.MemberName)
    | other -> failwithf "Expected one ctor-time abstract call, got %A" other

[<Fact>]
let ``FR0054: a Dispose inside an interface block that raises is caught`` () =
    let _, _, raises =
        objectRulesIn
            "module Test\ntype R() =\n    interface System.IDisposable with\n        member _.Dispose() = failwith \"simulated\""

    match raises with
    | [ r ] -> Assert.Equal("Dispose", r.MemberName)
    | other -> failwithf "Expected one raise-in-Dispose finding, got %A" other

[<Fact>]
let ``FR0054: a pipe-shaped raise counts`` () =
    let _, _, raises =
        objectRulesIn
            "module Test\ntype R() =\n    override _.GetHashCode() = raise <| System.InvalidOperationException \"no hash\""

    match raises with
    | [ r ] -> Assert.Equal("GetHashCode", r.MemberName)
    | other -> failwithf "Expected one pipe-shaped raise finding, got %A" other

// ---- FR0055 offers ----

[<Fact>]
let ``FR0055: a pure division body gets the guard, and the catch goes`` () =
    let source =
        "module Test\nlet ratio (total: int) (count: int) = try total / count with _ -> 0"

    match swallowedIn source with
    | [ s ] ->
        let guard = s.Offers |> List.find (fun o -> o.Label.StartsWith "Fix: guard")

        let patched =
            guard.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(
            "module Test\nlet ratio (total: int) (count: int) = if count = 0 then 0 else total / count",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one swallowed-exception finding, got %A" other

[<Fact>]
let ``FR0055: a one-call Parse body becomes TryParse`` () =
    let source =
        "module Test\nlet parse (s: string) =\n    try Some(System.Int32.Parse s) with _ -> None\nlet parse2 (s: string) =\n    try System.Int32.Parse s with _ -> 0"

    match swallowedIn source with
    | [ _; second ] ->
        let offer =
            second.Offers
            |> List.find (fun o -> o.Label.StartsWith "Fix: System.Int32.TryParse")

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("match System.Int32.TryParse s with\n    | true, v -> v\n    | _ -> 0", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0055: a file-IO body gets the narrower catch`` () =
    let source =
        "module Test\nlet read (path: string) = try System.IO.File.ReadAllText path with ex -> \"\""

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Alternative: catch the IO")

        let patched =
            offer.Edits
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("with (:? System.IO.IOException | :? System.UnauthorizedAccessException) as ex ->", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: a file that logs through MEL gets a log line in its own idiom`` () =
    let source =
        "module Test\ntype ILogger =\n    abstract LogError: exn * string * obj[] -> unit\nlet work (logger: ILogger) (id: int) =\n    logger.LogError(null, \"started {Id}\", [| box id |])\n    try\n        printfn \"%d\" id\n    with _ -> ()"

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
                "logger.LogError(ex, \"Exception: {Message} in method {Method} with parameter {id}\", ex.Message, \"work\", id)",
            patched
        )
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: the guard spells the zero of the divisor's type, never for a float, and stays away without a type`` () =
    let source =
        "module Test\nlet a (total: float) (count: float) = try total / count with _ -> 0.0\nlet b (total: int64) (count: int64) = try total / count with _ -> 0L\nlet c (total: decimal) (count: decimal) = try total / count with _ -> 0m"

    let guards =
        swallowedIn source
        |> List.map (fun s ->
            s.Offers
            |> List.tryFind (fun o -> o.Label.StartsWith "Fix: guard")
            |> Option.map (fun o -> o.Edits |> List.map (fun (_, _, r) -> r) |> List.head))

    Assert.Equal<string option list>(
        // float division never throws: no guard to offer
        [ None
          Some "if count = 0L then 0L else total / count"
          Some "if count = 0m then 0m else total / count" ],
        guards
    )

    for r in guards |> List.choose id do
        let patched = source.Replace("try total / count with _ -> 0.0", r)
        ignore patched

    let untyped =
        let tree, sourceText =
            parse "module Test\nlet a (total: int) (count: int) = try total / count with _ -> 0"

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
        "let f (t: System.Threading.Tasks.Task) = task {\n    t.Wait()\n    return 1\n}"

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, "t.Wait()", "do! t") ] ->
            let patched = applyFixes source s.Fixes
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected the do! fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: WaitAll inside task becomes do-bang WhenAll`` () =
    let source =
        "let f (a: System.Threading.Tasks.Task) (b: System.Threading.Tasks.Task) = task {\n    System.Threading.Tasks.Task.WaitAll(a, b)\n    return 1\n}"

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "do! System.Threading.Tasks.Task.WhenAll(a, b)") ] ->
            let patched = applyFixes source s.Fixes
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected the WhenAll fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a Wait on a generic task inside async awaits the upcast task`` () =
    let source =
        "let f (t: System.Threading.Tasks.Task<int>) = async {\n    t.Wait()\n    return 1\n}"

    match blockingIn source with
    | [ s ] ->
        match s.Fixes with
        | [ (_, _, "do! Async.AwaitTask (t :> System.Threading.Tasks.Task)") ] ->
            let patched = applyFixes source s.Fixes
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected the AwaitTask fix, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a final WaitAll of generic tasks has no bind shape`` () =
    // `let! _ =` cannot end a block, `do!` cannot take a Task<T[]>
    let source =
        "let f (a: System.Threading.Tasks.Task<int>) (b: System.Threading.Tasks.Task<int>) = task {\n    System.Threading.Tasks.Task.WaitAll(a, b)\n}"

    match blockingIn source with
    | [ s ] -> Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one blocking site, got %A" other

[<Fact>]
let ``FR0049: a blocking call inside Assert.Throws moves with the assert`` () =
    let source =
        "module Xunit\nopen System\nopen System.Threading.Tasks\ntype Assert =\n    static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>\n    static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>\nlet f (t: Task<int>) = task {\n    let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())\n    return ex.Message\n}"

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
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected the let!-bind pair, got %A" other
    | other -> failwithf "Expected exactly one blocking site, got %A" other

// ---- FR0055: test files are quiet ----

[<Fact>]
let ``FR0055: a file that opens a test framework gets no notes`` () =
    // a test's `try ... with _ -> 0` is deliberate: the assertion after it
    // is the observation, and the guard would be noise
    let body = "let ratio (total: int) (count: int) = try total / count with _ -> 0"

    Assert.NotEmpty(swallowedIn ("module Tests\nmodule Xunit =\n    let marker = 1\n" + body))
    Assert.Empty(swallowedIn ("module Tests\nmodule Xunit =\n    let marker = 1\nopen Xunit\n" + body))

[<Fact>]
let ``FR0049: an Assert.Throws inside a nested lambda stays advice`` () =
    // the `let ex =` sits in a List.iter callback: a `let!` there would not
    // compile, so the assert is left where it is
    let source =
        "module Xunit\nopen System\nopen System.Threading.Tasks\ntype Assert =\n    static member Throws<'E when 'E :> exn>(f: Action) : 'E = Unchecked.defaultof<'E>\n    static member ThrowsAsync<'E when 'E :> exn>(f: Func<Task>) : Task<'E> = Task.FromResult Unchecked.defaultof<'E>\nlet f (ts: Task<int> list) = task {\n    ts\n    |> List.iter (fun t ->\n        let ex = Assert.Throws<InvalidOperationException>(fun () -> t.Wait())\n        ignore ex)\n    return 1\n}"

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
        blockingIn
            "module Test\nopen System.Diagnostics\nlet run (psi: ProcessStartInfo) =\n    use proc = Process.Start psi\n    let output = proc.StandardOutput.ReadToEndAsync()\n    proc.WaitForExit()\n    output.Result"
    )

    Assert.Empty(blockingIn "let stop (t: System.Threading.Tasks.Task) = t.Wait(System.TimeSpan.FromSeconds 10.0)")

    // an unbounded Wait outside a CE is still the boundary note
    Assert.NotEmpty(blockingIn "let stop (t: System.Threading.Tasks.Task) = t.Wait()")

[<Fact>]
let ``FR0055: the IO-only catch is offered for a body that is the IO call, not a block that mentions a path`` () =
    // Kasino: a multi-line block computing a path, then calling native SDL —
    // narrowing to IOException would let the native failures through
    let block =
        "module Test\nlet icon (dir: string) =\n    try\n        let p = System.IO.Path.Combine(dir, \"icon.png\")\n        let handle = System.Runtime.InteropServices.GCHandle.Alloc(p)\n        handle.Free()\n    with _ -> ()"

    match swallowedIn block with
    | [ s ] -> Assert.Empty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other

    let single =
        "module Test\nlet firstFont (dir: string) =\n    try System.IO.Directory.GetFiles(dir, \"*.ttf\") |> Array.tryHead with _ -> None"

    match swallowedIn single with
    | [ s ] -> Assert.NotEmpty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other


[<Fact>]
let ``FR0055: the log line lands above a fallback that already sits on its own line`` () =
    // prismatic: `with _ ->` then `false` on the next line gained a blank
    // line and an over-indented pair
    let source =
        "module Test\ntype ILogger =\n    abstract LogError: exn * string * obj[] -> unit\nlet isActive (logger: ILogger) (pid: int) =\n    logger.LogError(null, \"started {Pid}\", [| box pid |])\n    try\n        pid > 0\n    with _ ->\n        false"

    match swallowedIn source with
    | [ s ] ->
        let offer =
            s.Offers |> List.find (fun o -> o.Label.StartsWith "Alternative: log it")

        let patched =
            offer.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal(
            "module Test\ntype ILogger =\n    abstract LogError: exn * string * obj[] -> unit\nlet isActive (logger: ILogger) (pid: int) =\n    logger.LogError(null, \"started {Pid}\", [| box pid |])\n    try\n        pid > 0\n    with ex ->\n        logger.LogError(ex, \"Exception: {Message} in method {Method} with parameter {pid}\", ex.Message, \"isActive\", pid)\n        false",
            patched
        )

    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: a comment on the handler is the author's acknowledgement`` () =
    Assert.Empty(
        swallowedIn
            "module Test\nlet f (g: unit -> unit) =\n    try g () with _ -> () // best effort: the icon is cosmetic"
    )

    Assert.Empty(
        swallowedIn
            "module Test\nlet f (g: unit -> int) =\n    try g ()\n    with _ ->\n        0 // the length is not important"
    )

    Assert.NotEmpty(swallowedIn "module Test\nlet f (g: unit -> int) =\n    try g () with _ -> 0")

[<Fact>]
let ``FR0055: the log line is offered only where its receiver is in scope`` () =
    // Fuuga: a `logger` parameter of one function was written into catches
    // of six functions that have none
    let source =
        "module Test\ntype ILogger =\n    abstract LogError: exn * string * obj[] -> unit\nlet a (logger: ILogger) (id: int) =\n    logger.LogError(null, \"started {Id}\", [| box id |])\n    try id with _ -> 0\nlet b (x: int) =\n    try x with _ -> 0"

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
        "module Test\nlet loadMolFile (path: string) =\n    try\n        let content = System.IO.File.ReadAllText(path)\n        Some content.Length\n    with\n    | _ -> None"

    match swallowedIn source with
    | [ s ] -> Assert.Empty(s.Offers |> List.filter (fun o -> o.Label.Contains "IO exceptions"))
    | other -> failwithf "Expected one finding, got %A" other

// ---- FR0050 shape guards (Mibo, the compiler) ----

[<Fact>]
let ``FR0050: a fold followed by nothing but the accumulator collapses into the expression`` () =
    // `let flags = .. |> Array.fold ..` was left with a bare `flags` line
    // after it on Mibo and the compiler: binding and use are the expression
    let source =
        "let f (xs: int[]) =\n    let mutable flags = 0\n    for x in xs do\n        flags <- flags ||| x\n    flags"

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal("xs |> Array.fold (fun flags x -> flags ||| x) 0", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal("let f (xs: int[]) =\n    xs |> Array.fold (fun flags x -> flags ||| x) 0", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``FR0050: an annotated mutable keeps its annotation on the folded binding`` () =
    // Mibo's `let mutable sum: IAdaptiveValue<int> = ..` lost its annotation
    let source =
        "let f (xs: int list) =\n    let mutable total: int64 = 0L\n    for x in xs do\n        total <- total + int64 x\n    total"

    match accumulationIn source with
    | [ s ], _ ->
        Assert.Equal("let total: int64 = xs |> List.fold (fun total x -> total + int64 x) 0L", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.EndsWith("\n    total", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one fold suggestion, got %A" other

[<Fact>]
let ``FR0050: a fold that would land past column 100 is withheld`` () =
    let folds, _ =
        accumulationIn
            "let f (xs: int list) =\n    let mutable accumulatedRunningTotalOfEverything = 1\n    for element in xs do\n        accumulatedRunningTotalOfEverything <- max accumulatedRunningTotalOfEverything (element % 7)\n    accumulatedRunningTotalOfEverything * 2"

    Assert.Empty folds

// ---- FR0118 scheduling calls (suave's Tcp.fs) ----

[<Fact>]
let ``FR0118: Task.Run never gains the token`` () =
    // with an already-cancelled token Task.Run never runs the delegate,
    // so the socket bind and the cell completion inside it never happen
    Assert.Empty(
        cancellationIn
            "open System\nopen System.Threading\nopen System.Threading.Tasks\nlet start (ct: CancellationToken) =\n    Task.Run(Func<Task>(fun () -> Task.CompletedTask))"
    )

[<Fact>]
let ``FR0118: Task.Factory.StartNew never gains the token`` () =
    Assert.Empty(
        cancellationIn
            "open System.Threading\nopen System.Threading.Tasks\nlet start (ct: CancellationToken) =\n    Task.Factory.StartNew(fun () -> 1)"
    )

[<Fact>]
let ``FR0118: an explicit None on Task.Run is the author's choice`` () =
    Assert.Empty(
        cancellationIn
            "open System\nopen System.Threading\nopen System.Threading.Tasks\nlet start (ct: CancellationToken) =\n    Task.Run(Func<Task>(fun () -> Task.CompletedTask), CancellationToken.None)"
    )


// ---- FR0119 AwaitableOverload: Dispose has no awaitable twin (fantomas EndToEndTests.fs) ----

[<Fact>]
let ``FR0119 a Dispose statement inside task is never offered DisposeAsync`` () =
    // fantomas's EndToEndTests.fs: `File.Create(path).Dispose()` became
    // `do! File.Create(path).DisposeAsync()` — a ValueTask twin with no
    // work to await; Dispose stays Dispose
    let source =
        "open System.IO\nlet touch (path: string) = task {\n    File.Create(path).Dispose()\n    return 1\n}"

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``FR0119 a stream flush inside task still becomes do-bang FlushAsync`` () =
    let source =
        "open System.IO\nlet flush (stream: Stream) = task {\n    stream.Flush()\n    return 1\n}"

    match awaitableIn source with
    | [ s ] ->
        let patched = applyAwaitable source s
        Assert.Contains("do! stream.FlushAsync()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one FlushAsync suggestion, got %A" other

// ---- FR0049: tasks known complete, console blocking points, primitives ----

[<Fact>]
let ``FR0049: a Result read under its own completion probe never waits`` () =
    // suave's ValueTask fast path: the read happens only when the task is
    // already complete, the else branch awaits it
    let fastPath =
        "module Test\nopen System.Threading.Tasks\nlet read (vt: ValueTask<int>) : ValueTask<int> =\n    if vt.IsCompletedSuccessfully then\n        ValueTask<int>(vt.Result + 1)\n    else\n        ValueTask<int>(task {\n            let! n = vt\n            return n + 1\n        })"

    Assert.Empty(blockingIn fastPath)

    // conjoined, negated, and inside a task { } the same way
    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet read (vt: ValueTask<int>) (fast: bool) =\n    if fast && vt.IsCompleted then vt.Result else 0"
    )

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet read (vt: ValueTask<int>) =\n    if not vt.IsCompletedSuccessfully then 0 else vt.Result"
    )

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet read (vt: ValueTask<int>) = task {\n    if vt.IsCompletedSuccessfully then\n        let _ = vt.Result\n        return 1\n    else\n        let! _ = vt\n        return 2\n}"
    )

    // a probe on ANOTHER task proves nothing about this one
    Assert.NotEmpty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet read (a: ValueTask<int>) (b: ValueTask<int>) =\n    if a.IsCompletedSuccessfully then b.Result else 0"
    )

[<Fact>]
let ``FR0049: the antecedent of a ContinueWith continuation is complete by definition`` () =
    // suave's ConnectionFacade and fantomas' LSPFantomasService: the lambda
    // form; suave's AsyncExtensions and FCS's AsyncMemoize: a named function
    // never a blocking note: only the AggregateException advice
    let onlyAntecedentAdvice (source: string) =
        Assert.All(blockingIn source, (fun s -> Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)))

    onlyAntecedentAdvice
        "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) =\n    t.ContinueWith(fun (ante: Task<int>) -> ante.Result + 1)"

    onlyAntecedentAdvice
        "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) =\n    let routine (finished: Task<int>) =\n        if finished.IsFaulted then 0 else finished.Result\n    t.ContinueWith(routine, TaskScheduler.Default)"

    // another task drained inside the continuation still blocks
    Assert.NotEmpty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) (other: Task<int>) =\n    t.ContinueWith(fun (ante: Task<int>) -> other.Result + 1)"
    )

[<Fact>]
let ``FR0049: a wait in the finally block of an async is named as such and gets no fix`` () =
    // FCS's DiagnosticsLogger and BuildGraph: `do!` cannot appear in a
    // finally block, so the bind the plain message asks for cannot compile
    let source =
        "module Test\nopen System.Threading.Tasks\nlet f (t: Task) (work: Async<int>) = async {\n    try\n        let! r = work\n        return r\n    finally\n        t.Wait()\n}"

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
        blockingIn
            "module Program\nopen System.Threading.Tasks\n[<EntryPoint>]\nlet main argv =\n    let server = Task.Delay 10\n    server.Wait()\n    0"
    )

    Assert.Empty(
        blockingIn
            "module Program\nopen System.Threading.Tasks\nlet runDaemon (closed: Task) : int =\n    closed.GetAwaiter().GetResult()\n    0"
    )

    // the test harness checks every source as Test.fsx: top-level
    // statements, a for loop included, are the script's main
    Assert.Empty(
        blockingIn
            "open System.Threading.Tasks\nlet run (n: int) = Task.Delay n\n(run 1).Wait()\nfor n in [ 1; 2 ] do\n    (run n).Wait()"
    )

    // a value-returning helper, a lambda inside main, and a member are
    // boundaries of their own
    Assert.NotEmpty(
        blockingIn
            "module Program\nopen System.Threading.Tasks\nlet wait (t: Task<int>) = t.GetAwaiter().GetResult()\n[<EntryPoint>]\nlet main argv = wait (Task.FromResult 1)"
    )

    Assert.NotEmpty(
        blockingIn
            "module Program\nopen System.Threading.Tasks\n[<EntryPoint>]\nlet main argv =\n    let handler = fun (t: Task) -> t.Wait()\n    handler (Task.Delay 1)\n    0"
    )

    Assert.NotEmpty(
        blockingIn
            "module Program\nopen System.Threading.Tasks\ntype Runner() =\n    member _.Run(t: Task) =\n        t.Wait()\n        0"
    )

[<Fact>]
let ``FR0049: WaitAll with a timeout or a token outside a CE is the bounded idiom`` () =
    // Mibo's benchmark: `while not (Task.WaitAll(tasks, 1)) do pump ()`
    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet pump (tasks: Task[]) =\n    while not (Task.WaitAll(tasks, 1)) do\n        ()"
    )

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet pump (tasks: Task[]) (cts: System.Threading.CancellationTokenSource) =\n    Task.WaitAll(tasks, cts.Token)"
    )

    // two tasks params-style is the unbounded wait
    Assert.NotEmpty(
        blockingIn "module Test\nopen System.Threading.Tasks\nlet join (a: Task) (b: Task) =\n    Task.WaitAll(a, b)"
    )

[<Fact>]
let ``FR0049: a task complete from birth is drained without a wait`` () =
    // the test-fixture habit: `.Result` on a `Task.FromResult` stand-in
    Assert.Empty(blockingIn "module Test\nopen System.Threading.Tasks\nlet v = (Task.FromResult 1).Result")

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet f () =\n    let t = Task.FromResult 1\n    t.Result + 1"
    )

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet fixture = Task.FromResult 1\nlet f () = task { return fixture.Result + 1 }"
    )

    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet f () =\n    let t = ValueTask.FromResult 1\n    t.GetAwaiter().GetResult()"
    )

    // a task from anywhere else is not known complete
    Assert.NotEmpty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet f (make: unit -> Task<int>) =\n    let t = make ()\n    t.Result"
    )

[<Fact>]
let ``FR0049: a Result read after the receiver's own Wait drains what was waited for`` () =
    // suave's Testing.send: `send.Wait(timeout, token)` is the bounded wait
    // two lines above the `send.Result` that only reads the outcome
    Assert.Empty(
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet send (t: Task<int>) (timeout: System.TimeSpan) =\n    let completed = t.Wait timeout\n    if not completed then failwith \"timeout\"\n    t.Result"
    )

    // an unbounded Wait above keeps its own note; the read after it is quiet
    match
        blockingIn
            "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) = task {\n    t.Wait()\n    return t.Result\n}"
    with
    | [ s ] -> Assert.Equal(SyncOverAsync.BlockKind.TaskWait, s.Kind)
    | other -> failwithf "Expected the Wait alone, got %A" other

[<Fact>]
let ``FR0049: a synchronisation primitive's wait inside a task is named and left to the author`` () =
    // Mibo's tests: `doneSignal.Wait()` before `do! worker` in task { }
    let source =
        "module Test\nopen System.Threading\nopen System.Threading.Tasks\nlet f (doneSignal: ManualResetEventSlim) (worker: Task) = task {\n    doneSignal.Wait()\n    do! worker\n}"

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.PrimitiveWait "ManualResetEventSlim.Wait()", s.Kind)
        Assert.Equal(Some "task", s.Builder)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected one primitive wait, got %A" other

    match
        blockingIn
            "module Test\nopen System.Threading\nlet f (sem: SemaphoreSlim) (ev: ManualResetEvent) (th: Thread) = async {\n    sem.Wait()\n    ev.WaitOne() |> ignore\n    th.Join()\n    return 1\n}"
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
        blockingIn
            "module Test\nopen System.Threading\nlet f (doneSignal: ManualResetEventSlim) (th: Thread) =\n    doneSignal.Wait()\n    th.Join()"
    )

[<Fact>]
let ``a thread-choreographed private drain is not taskified`` () =
    // the body waits on a signal and continues on that thread; task-returning
    // it would not — the same refusal as FR0142's
    let source =
        "module Test\nopen System.Threading\nopen System.Threading.Tasks\nlet private fetch (x: int) =\n    let signal = new ManualResetEventSlim(false)\n    let t = Task.Run(fun () -> signal.Set(); x)\n    signal.Wait()\n    t.GetAwaiter().GetResult()\nlet consume () = task {\n    let s = fetch 1\n    return s\n}"

    Assert.Empty(taskifyIn source)

[<Fact>]
let ``a thread-choreographed task body gets no async-overload rewrite`` () =
    let source =
        "open System.IO\nopen System.Threading\nlet head (reader: TextReader) = task {\n    let signal = new ManualResetEventSlim(false)\n    signal.Wait()\n    let line = reader.ReadLine()\n    return line\n}"

    Assert.Empty(awaitableIn source)

[<Fact>]
let ``a wait inside a thread-choreographed task body is noted without a fix`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet f () = task {\n    let signal = new ManualResetEventSlim(false)\n    let t = Task.Run(fun () -> signal.Set())\n    signal.Wait()\n    t.Wait()\n    return 1\n}"

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
        "open System.Threading.Tasks\nlet f (t: Task<int>) =\n    t.ContinueWith(fun (a: Task<int>) -> a.Result + 1)"

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)
        Assert.Empty s.AlternativeFixes

        // the continuation is a bind: the same task { let! } FR0049 writes
        // everywhere, never a GetAwaiter().GetResult() — the spelling the
        // rule exists to remove
        match s.Fixes with
        | [ (r, _, replacement) ] ->
            Assert.Equal("task {\n        let! r = t\n        return r + 1\n    }", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | other -> failwithf "Expected one bind edit, got %A" other
    | other -> failwithf "Expected exactly one antecedent note, got %A" other

    // without a task builder (FSharp.Core before 6) ContinueWith IS the
    // bind: nothing is reported
    let tree, sourceText, checkResults = parseAndCheck source
    Assert.Empty(SyncOverAsync.findWith false tree sourceText checkResults)

    // a continuation that handles the antecedent itself keeps the note and
    // gets no rewrite; so does one handed a scheduler
    let handled =
        blockingIn
            "open System.Threading.Tasks\nlet f (t: Task<int>) =\n    t.ContinueWith(fun (a: Task<int>) -> if a.IsFaulted then 0 else a.Result + 1)"

    Assert.All(handled, (fun s -> Assert.Empty s.Fixes))

    let scheduled =
        blockingIn
            "open System.Threading.Tasks\nlet f (t: Task<int>) =\n    t.ContinueWith((fun (a: Task<int>) -> a.Result + 1), TaskScheduler.Default)"

    Assert.All(scheduled, (fun s -> Assert.Empty s.Fixes))

[<Fact>]
let ``FR0049: an antecedent read with no free binder name is noted without a rewrite`` () =
    // every candidate binder is already a name in the body: the note stands,
    // the rewrite steps aside (it must not raise out of the analyzer)
    let source =
        "open System.Threading.Tasks\nlet f (t: Task<int>) (r: int) (result: int) (aValue: int) =\n    t.ContinueWith(fun (a: Task<int>) -> a.Result + r + result + aValue)"

    match blockingIn source with
    | [ s ] ->
        Assert.Equal(SyncOverAsync.BlockKind.AntecedentResult, s.Kind)
        Assert.Empty s.Fixes
    | other -> failwithf "Expected exactly one antecedent note, got %A" other
