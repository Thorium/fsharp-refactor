module FSharp.Refactor.Tests.HazardRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0159 IntDivisionToFloat ----

let private intDivisionsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    IntDivisionToFloat.find tree sourceText checkResults

[<Fact>]
let ``FR0159: a float conversion of an integer division converts the operands first`` () =
    let source =
        "module M\nlet average (sum: int) (count: int) = float (sum / count)\nlet ratio (done': int64) (total: int64) = 1.0m + decimal (done' / total) |> float\nlet share (hits: int) (all: int) = 100.0 * float (hits / all) ** 2.0"

    match intDivisionsIn source with
    | [ a; b; c ] ->
        Assert.Equal("float sum / float count", a.ReplacementText)
        Assert.False a.LikelyMeant
        Assert.Equal("(decimal done' / decimal total)", b.ReplacementText)
        Assert.Equal("(float hits / float all)", c.ReplacementText)

        let patched =
            [ a; b; c ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold (fun acc s -> applyEdit acc s.Range s.ReplacementText) source

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0159: a literal operand marks the truncation as possibly meant`` () =
    let source = "module M\nlet seconds (ms: int) = float (ms / 1000)"

    match intDivisionsIn source with
    | [ s ] ->
        Assert.True s.LikelyMeant
        Assert.Equal("float ms / float 1000", s.ReplacementText)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0159: a float division, a non-division and a shadowed conversion stay quiet`` () =
    let source =
        "module M\nlet a (x: float) (y: float) = float (x / y)\nlet b (x: int) (y: int) = float (x * y)\nlet c (x: int) (y: int) = float x / float y\nmodule Shadow =\n    let float (x: int) = string x\n    let d (x: int) (y: int) = float (x / y)"

    Assert.Empty(intDivisionsIn source)

// ---- FR0160 LostInnerException ----

let private lostInnersIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    LostInnerException.find tree sourceText checkResults

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``FR0160: a wrapper constructed without the caught exception gains it as the trailing argument`` () =
    let source =
        "module M\nexception ConfigError of string\ntype ConfigException(message: string, inner: exn) =\n    inherit System.Exception(message, inner)\n    new(message: string) = ConfigException(message, null)\nlet load (read: unit -> string) =\n    try read () with ex -> raise (ConfigException(\"bad config\"))\nlet load2 (read: unit -> string) =\n    try read () with _ -> raise (ConfigException \"bad config\")\nlet load3 (read: unit -> string) =\n    try read () with :? System.IO.IOException -> raise (System.InvalidOperationException(\"unreadable\"))"

    match lostInnersIn source with
    | [ a; b; c ] ->
        let patched = applyAll source (a.Edits @ b.Edits @ c.Edits)
        Assert.Contains("with ex -> raise (ConfigException(\"bad config\", ex))", patched)
        Assert.Contains("with ex -> raise (ConfigException(\"bad config\", ex))", patched)

        Assert.Contains(
            "with :? System.IO.IOException as ex -> raise (System.InvalidOperationException(\"unreadable\", ex))",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0160: a failwith that never reads the caught exception is the note`` () =
    let source =
        "module M\nlet load (read: unit -> string) =\n    try read () with _ -> failwith \"could not load\"\nlet load2 (read: unit -> string) =\n    try read () with ex -> failwithf \"could not load: %s\" ex.Message"

    match lostInnersIn source with
    | [ s ] ->
        Assert.Equal("failwith", s.Raised)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0160: a wrapper that carries the exception, or a type without the overload, stays quiet`` () =
    let source =
        "module M\ntype Flat(message: string) =\n    inherit System.Exception(message)\nlet a (read: unit -> string) =\n    try read () with ex -> raise (System.InvalidOperationException(\"unreadable\", ex))\nlet b (read: unit -> string) =\n    try read () with ex -> raise (Flat \"unreadable\")\nlet c (read: unit -> string) =\n    try read () with ex -> raise (System.AggregateException([| ex |]))\nlet d (read: unit -> string) = raise (System.InvalidOperationException \"outside a handler\")"

    Assert.Empty(lostInnersIn source)

// ---- FR0161 StructPropertyMutation ----

let private structMutationsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StructPropertyMutation.find tree sourceText checkResults

[<Fact>]
let ``FR0161: a mutating member called on the struct a property returns is noted`` () =
    let source =
        "module M\n[<Struct>]\ntype Counter =\n    val mutable N: int\n    member this.Bump() = this.N <- this.N + 1\n    member this.Value = this.N\ntype Holder() =\n    member val Counter = Counter() with get, set\nlet bump (h: Holder) =\n    h.Counter.Bump()\n    h.Counter.Value\nlet walk (h: Holder) (xs: ResizeArray<int>) =\n    let mutable e = xs.GetEnumerator()\n    e.MoveNext() |> ignore\n    h.Counter.Value"

    match structMutationsIn source with
    | [ s ] ->
        Assert.Equal("h.Counter", s.PropertyText)
        Assert.Equal("Bump", s.Method)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0161: a reading member, a class property and a local mutable stay quiet`` () =
    let source =
        "module M\ntype Counter() =\n    member val N = 0 with get, set\n    member this.Bump() = this.N <- this.N + 1\ntype Holder() =\n    member val Counter = Counter() with get, set\nlet bump (h: Holder) =\n    h.Counter.Bump()\n    h.Counter.N\nlet span (h: Holder) = h.Counter.ToString()"

    Assert.Empty(structMutationsIn source)

// ---- FR0162 LazyInit ----

let private lazyInitsIn (source: string) =
    let tree, sourceText = parse source
    LazyInit.find tree sourceText

[<Fact>]
let ``FR0162: a module mutable filled under an emptiness test is the racing lazy`` () =
    let source =
        "module M\nlet mutable private cache: int list option = None\nlet build () = [ 1; 2; 3 ]\nlet index () =\n    if cache.IsNone then\n        cache <- Some(build ())\n    cache.Value\nlet mutable private table: string = null\nlet lookup () =\n    match table with\n    | null ->\n        table <- \"built\"\n        table\n    | t -> t\nlet mutable private matched: int option = None\nlet value () =\n    match matched with\n    | None ->\n        matched <- Some 1\n        1\n    | Some v -> v\ntype Holder() =\n    static let mutable shared: obj = null\n    static member Shared =\n        if isNull shared then shared <- obj ()\n        shared"

    match lazyInitsIn source with
    | [ a; b; c; d ] ->
        Assert.Equal("cache", a.Name)
        Assert.Equal("table", b.Name)
        Assert.Equal("matched", c.Name)
        Assert.Equal("shared", d.Name)
    | other -> failwithf "Expected four findings, got %A" other

[<Fact>]
let ``FR0162: a locked store, a reset elsewhere, a non-empty start and a local mutable stay quiet`` () =
    let source =
        "module M\nlet private gate = obj ()\nlet mutable private cache: int option = None\nlet index () =\n    lock gate (fun () ->\n        if cache.IsNone then cache <- Some 1\n        cache.Value)\nlet mutable private table: string = null\nlet lookup () =\n    if isNull table then table <- \"built\"\n    table\nlet reset () = table <- null\nlet mutable private count = 0\nlet bump () =\n    if count = 0 then count <- 1\n    count\nlet local () =\n    let mutable seen: int option = None\n    if seen.IsNone then seen <- Some 1\n    seen\nlet mutable private holder: Lazy<string> = Unchecked.defaultof<Lazy<string>>\nlet reconnecting () =\n    if isNull holder || not holder.IsValueCreated || isNull holder.Value then\n        holder <- lazy \"built\"\n    holder.Force()"

    Assert.Empty(lazyInitsIn source)

// ---- FR0163 DroppedTimer ----

let private droppedTimersIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DroppedTimer.find tree sourceText checkResults

[<Fact>]
let ``FR0163: a threading timer piped to ignore or dropped as a statement is noted`` () =
    let source =
        "module M\nopen System.Threading\nlet start (tick: obj -> unit) =\n    new Timer(TimerCallback tick, null, 0, 1000) |> ignore\n    Timer(TimerCallback tick, null, 0, 1000) |> ignore\n    ignore (new Timer(TimerCallback tick, null, 0, 1000))\n    1"

    match droppedTimersIn source with
    | [ _; _; _ ] -> ()
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0163: a bound threading timer and a System.Timers.Timer stay quiet`` () =
    let source =
        "module M\nopen System.Threading\nlet start (tick: obj -> unit) =\n    use timer = new Timer(TimerCallback tick, null, 0, 1000)\n    let kept = new Timer(TimerCallback tick, null, 0, 1000)\n    let t = new System.Timers.Timer(1000.0)\n    t.Start()\n    new System.Timers.Timer(500.0) |> ignore\n    kept"

    Assert.Empty(droppedTimersIn source)

// ---- FR0164 EnumerationMutation ----

let private enumerationMutationsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    EnumerationMutation.find tree sourceText checkResults

[<Fact>]
let ``FR0164: a collection edited inside a for loop over itself walks a snapshot`` () =
    let source =
        "module M\nopen System.Collections.Generic\nlet prune (items: List<int>) =\n    for x in items do\n        if x < 0 then items.Remove x |> ignore\nlet grow (d: Dictionary<int, int>) =\n    for k in d.Keys do\n        d.Add(k + 100, k)\nlet overwrite (xs: ResizeArray<int>) =\n    for i in xs do\n        xs.[0] <- i"

    match enumerationMutationsIn source with
    | [ a; b; c ] ->
        Assert.Equal("Array.ofSeq items", a.ReplacementText)
        Assert.Equal("Remove", a.Mutation)
        Assert.Equal("Array.ofSeq d.Keys", b.ReplacementText)
        Assert.Equal("[k] <-", c.Mutation)

        // the first loop is the filter shape: the list's own RemoveAll
        // (CR0171's first fix); the other two are not
        match a.Filter, b.Filter, c.Filter with
        | Some(_, _, replacement), None, None -> Assert.Equal("items.RemoveAll(fun x -> x < 0) |> ignore", replacement)
        | other -> failwithf "Expected the filter fix on the first loop only, got %A" other

        let patched =
            [ a; b; c ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold (fun acc s -> applyEdit acc s.Range s.ReplacementText) source

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

        let (r, _, replacement) = a.Filter.Value
        let filtered = applyEdit source r replacement

        Assert.Contains(
            "let prune (items: List<int>) =\n    items.RemoveAll(fun x -> x < 0) |> ignore\nlet grow",
            filtered
        )

        Assert.True(typechecksCleanly filtered, $"Filtered source does not typecheck:\n%s{filtered}")
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0164: a body with more than the removal, or a condition naming the list, keeps the snapshot`` () =
    let source =
        "module M\nopen System.Collections.Generic\nlet prune (items: List<int>) (log: int -> unit) =\n    for x in items do\n        if x < 0 then\n            log x\n            items.Remove x |> ignore\nlet dedupe (items: List<int>) =\n    for x in items do\n        if items.IndexOf x > 0 then items.Remove x |> ignore"

    match enumerationMutationsIn source with
    | [ a; b ] ->
        Assert.True(a.Filter.IsNone, "a body doing more than removing is not a filter")
        Assert.True(b.Filter.IsNone, "a condition reading the list is not a filter")
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0164: a condition over a mutable or a Span, or a comment in the loop, keeps the snapshot`` () =
    // RemoveAll takes the condition as a closure: a `let mutable` in it is
    // FS0407, a Span FS0406. The filter rewrites the whole loop, so a
    // comment in it would be deleted; the snapshot's edit touches neither
    let source =
        "module M\nopen System\nopen System.Collections.Generic\nlet mutableLimit (items: List<int>) =\n    let mutable limit = 0\n    limit <- 3\n    for x in items do\n        if x < limit then items.Remove x |> ignore\nlet span (items: List<int>, s: ReadOnlySpan<int>) =\n    for x in items do\n        if x < s.Length then items.Remove x |> ignore\nlet commented (items: List<int>) =\n    for x in items do\n        // negative entries are stale\n        if x < 0 then items.Remove x |> ignore"

    Assert.True(typechecksCleanly source)

    match enumerationMutationsIn source with
    | [ a; b; c ] ->
        for s in [ a; b; c ] do
            Assert.True(s.Filter.IsNone, $"line {s.Range.StartLine}: no filter fix")
            Assert.Equal("Array.ofSeq items", s.ReplacementText)

        let patched =
            [ a; b; c ]
            |> List.sortByDescending (fun s -> s.Range.StartLine)
            |> List.fold (fun acc s -> applyEdit acc s.Range s.ReplacementText) source

        Assert.Contains("// negative entries are stale", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0164: a removal from a dictionary or set, an edit to another collection, and a concurrent one stay quiet`` () =
    let source =
        "module M\nopen System.Collections.Generic\nopen System.Collections.Concurrent\nlet prune (d: Dictionary<int, int>) (h: HashSet<int>) =\n    for KeyValue(k, v) in d do\n        if v < 0 then d.Remove k |> ignore\n        d.[k] <- v + 1\n    for x in h do\n        if x < 0 then h.Remove x |> ignore\nlet copy (src: List<int>) (dst: List<int>) =\n    for x in src do\n        dst.Add x\nlet bag (b: ConcurrentBag<int>) =\n    for x in b do\n        b.Add x\nlet immutable (xs: int list) (acc: List<int>) =\n    for x in xs do\n        acc.Add x"

    Assert.Empty(enumerationMutationsIn source)

// ---- the review's regressions ----

[<Fact>]
let ``FR0160: a named argument stands the fix down, and a curried failwithf is one note`` () =
    let source =
        "module M\nlet a (read: unit -> string) =\n    try read () with ex -> raise (System.ArgumentException(message = \"bad\"))\nlet b (read: unit -> string) (name: string) =\n    try read () with _ -> failwithf \"could not read %s for %d\" name 3"

    match lostInnersIn source with
    | [ s ] ->
        Assert.Equal("failwithf", s.Raised)
        Assert.Equal(5, s.Range.StartLine)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0159: a negative literal operand keeps its parentheses`` () =
    let source = "module M\nlet f (x: int) = float (x / -2)"

    match intDivisionsIn source with
    | [ s ] ->
        Assert.Equal("float x / float (-2)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0162: a store under a piped lock, a qualified reset and a test file stay quiet`` () =
    let source =
        "module M\nlet private gate = obj ()\nlet mutable private cache: int option = None\nlet index () =\n    lock gate <| fun () ->\n        if cache.IsNone then cache <- Some 1\n        cache.Value\nmodule Inner =\n    let mutable table: string = null\n    let lookup () =\n        if isNull table then table <- \"built\"\n        table\nlet reset () = Inner.table <- null"

    Assert.Empty(lazyInitsIn source)

    let test =
        "module T\nopen Xunit\nlet mutable private fixture: int option = None\nlet get () =\n    if fixture.IsNone then fixture <- Some 1\n    fixture.Value\n[<Fact>]\nlet ``reads`` () = Assert.Equal(1, get ())"

    Assert.Empty(lazyInitsIn test)

[<Fact>]
let ``FR0164: an interface-typed collection stays quiet, and the F# 6 indexer store is an edit`` () =
    let source =
        "module M\nopen System.Collections.Generic\nlet viaInterface (items: IList<int>) =\n    for x in items do\n        if x < 0 then items.Remove x |> ignore\nlet indexer (xs: ResizeArray<int>) =\n    for i in xs do\n        xs[0] <- i"

    match enumerationMutationsIn source with
    | [ s ] ->
        Assert.Equal("xs", s.Collection)
        Assert.Equal("[k] <-", s.Mutation)
    | other -> failwithf "Expected one finding, got %A" other


let private leaksIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MonitorLock.findLeaks tree sourceText checkResults
// ---- the C# twin's guards (CR0160–CR0171) ----

[<Fact>]
let ``FR0164: a mutation inside a lambda, a local function, or one that leaves the loop stays quiet`` () =
    let source =
        "module M\nopen System.Collections.Generic\nlet deferred (items: List<int>) (later: List<unit -> unit>) =\n    for x in items do\n        later.Add(fun () -> items.Remove x |> ignore)\nlet local (items: List<int>) =\n    for x in items do\n        let drop () = items.Remove x |> ignore\n        drop ()\nlet leaves (items: List<int>) =\n    for x in items do\n        if x < 0 then\n            items.Remove x |> ignore\n            failwith \"negative\"\nlet returns (items: List<int>) =\n    seq {\n        for x in items do\n            if x < 0 then\n                items.Remove x |> ignore\n                yield x\n    }\nlet shadowed (items: List<int>) (other: List<int>) =\n    for x in items do\n        let items = other\n        items.Remove x |> ignore"

    // the `seq` case still fires: a `yield` resumes the loop
    match enumerationMutationsIn source with
    | [ s ] -> Assert.Equal(17, s.Range.StartLine)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0160: a raise inside a lambda or a nested try, and a message reading the exception, stay quiet`` () =
    let source =
        "module M\nlet a (read: unit -> string) (items: int list) =\n    try read () with ex -> items |> List.iter (fun _ -> raise (System.InvalidOperationException(\"x\"))); \"\"\nlet b (read: unit -> string) =\n    try read () with ex -> failwithf \"%s\" ex.Message\nlet c (read: unit -> string) =\n    try read () with ex -> raise (System.InvalidOperationException(\"failed: \" + ex.Message))\nlet d (read: unit -> string) =\n    try read () with ex ->\n        try read () with _ -> raise (System.InvalidOperationException(\"inner\"))"

    // d: the inner handler binds nothing and IS a handler — its raise is
    // reported for the inner clause, with a fresh binder free in the whole
    // declaration (`ex` is taken)
    match lostInnersIn source with
    | [ s ] ->
        Assert.Equal(10, s.Range.StartLine)
        Assert.Equal("exn", s.Binder)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0159: a division under a rounding function or by one stays quiet`` () =
    let source =
        "module M\nlet a (x: int) (y: int) = floor (float (x / y))\nlet b (x: int) (y: int) = System.Math.Round(float (x / y))\nlet c (x: int) = float (x / 1)"

    Assert.Empty(intDivisionsIn source)

[<Fact>]
let ``FR0163: a local timer the scope never mentions again is dropped too`` () =
    let source =
        "module M\nopen System.Threading\nlet start (tick: obj -> unit) (keep: Timer -> unit) =\n    let forgotten = new Timer(TimerCallback tick, null, 0, 1000)\n    let _ = new Timer(TimerCallback tick, null, 0, 1000)\n    let passed = new Timer(TimerCallback tick, null, 0, 1000)\n    keep passed\n    let returned = new Timer(TimerCallback tick, null, 0, 1000)\n    returned"

    match droppedTimersIn source with
    | [ a; b ] ->
        Assert.Equal(4, a.Range.StartLine)
        Assert.Equal(5, b.Range.StartLine)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0123: the statements between the acquire and its release move under a try, the release into the finally`` () =
    let source =
        "module M =\n    let sem = new System.Threading.SemaphoreSlim(1)\n    let mutable count = 0\n    let bump (log: string -> unit) =\n        sem.Wait()\n        count <- count + 1\n        // the tally\n        log \"bumped\"\n        sem.Release() |> ignore\n        count\n    let awaited (t: System.Threading.Tasks.Task) =\n        task {\n            do! sem.WaitAsync()\n            do! t\n            sem.Release() |> ignore\n            return count\n        }"

    match leaksIn source with
    | [ a; b ] ->
        let patched =
            [ a; b ]
            |> List.choose (fun s -> s.Fix)
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            "        sem.Wait()\n        try\n            count <- count + 1\n            // the tally\n            log \"bumped\"\n        finally\n            sem.Release() |> ignore\n        count",
            patched
        )

        Assert.Contains(
            "            do! sem.WaitAsync()\n            try\n                do! t\n            finally\n                sem.Release() |> ignore\n            return count",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two leak notes, got %A" other

[<Fact>]
let ``FR0123: a binding between the acquire and the release that is read after, or no release in the block, leaves the note without a fix``
    ()
    =
    let source =
        "module M =\n    let sem = new System.Threading.SemaphoreSlim(1)\n    let mutable count = 0\n    let readAfter (compute: unit -> int) =\n        sem.Wait()\n        let v = compute ()\n        sem.Release() |> ignore\n        v + count\n    let elsewhere (compute: unit -> int) =\n        sem.Wait()\n        count <- compute ()\n        count\n    let bound (compute: unit -> int) =\n        sem.Wait()\n        let v = compute ()\n        count <- v\n        sem.Release() |> ignore"

    match leaksIn source with
    | [ a; b; c ] ->
        Assert.True(a.Fix.IsNone, "a binding read after the release cannot move under the try")
        Assert.True(b.Fix.IsNone, "no release in the block: nothing to put in a finally")
        // nothing follows the release, so the binding may move
        Assert.True(c.Fix.IsSome, "a binding nothing reads after the release moves under the try")
    | other -> failwithf "Expected three leak notes, got %A" other

// ---- FR0165 DateTimeKindMix ----

let private kindMixesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DateTimeKindMix.find tree sourceText checkResults

[<Fact>]
let ``FR0165: a local clock read compared with a UTC one is noted, directly and through a binding`` () =
    let source =
        "module M\nopen System\nlet startedUtc = DateTime.UtcNow\nlet expired () = DateTime.Now > startedUtc\nlet age () = DateTime.UtcNow - DateTime.Today\nlet cmp () = DateTime.Now.CompareTo startedUtc\nlet cmp2 () = DateTime.Compare(startedUtc.AddDays 1.0, DateTime.Today)\nlet local () =\n    let now = DateTime.Now\n    now.Date <= startedUtc"

    match kindMixesIn source with
    | [ a; b; c; d; e ] ->
        Assert.Equal(("DateTime.Now", "startedUtc", ">"), (a.LocalText, a.UtcText, a.Operation))
        Assert.Equal(("DateTime.Today", "DateTime.UtcNow", "-"), (b.LocalText, b.UtcText, b.Operation))
        Assert.Equal("CompareTo", c.Operation)
        Assert.Equal(("DateTime.Today", "startedUtc.AddDays 1.0", "Compare"), (d.LocalText, d.UtcText, d.Operation))
        Assert.Equal(("now.Date", "startedUtc", "<="), (e.LocalText, e.UtcText, e.Operation))
    | other -> failwithf "Expected five findings, got %A" other

[<Fact>]
let ``FR0165: an explicit kind, a mutable, a parameter, the offset idiom and one kind on both sides stay quiet`` () =
    let source =
        "module M\nopen System\nlet startedUtc = DateTime.UtcNow\nlet explicit () = DateTime.Now.ToUniversalTime() > startedUtc\nlet specified () = DateTime.SpecifyKind(DateTime.Now, DateTimeKind.Utc) > startedUtc\nlet mutable stamp = DateTime.Now\nlet reassigned () =\n    stamp <- DateTime.UtcNow\n    stamp > startedUtc\nlet param (t: DateTime) = t > startedUtc\nlet offset () = DateTime.Now - DateTime.UtcNow\nlet same () = DateTime.UtcNow > startedUtc && DateTime.Now > DateTime.Today\nlet span () = DateTime.Now - TimeSpan.FromHours 1.0 > DateTime.Today\nlet bound = DateTime.Now\nlet bound2 = 1\nlet twice () =\n    let bound = DateTime.UtcNow\n    bound > startedUtc"

    Assert.Empty(kindMixesIn source)

[<Fact>]
let ``FR0165: a parameter sharing a bound name, and durations computed in either kind, stay quiet`` () =
    // `now` is a local `let` in one function and a parameter in another: the
    // parameter is not that `let`; two durations differ by no offset at all
    let source =
        "module M\nopen System\nlet startedUtc = DateTime.UtcNow\nlet a () =\n    let now = DateTime.Now\n    now.Year\nlet b (now: DateTime) = now > startedUtc\nlet durations (t: DateTime) (u: DateTime) = DateTime.Now - t > DateTime.UtcNow - u\nlet subtracted (t: DateTime) = DateTime.Now.Subtract t > DateTime.UtcNow.Subtract startedUtc"

    Assert.Empty(kindMixesIn source)

[<Fact>]
let ``FR0165: a plain TimeSpan taken off a clock read keeps its kind`` () =
    let source =
        "module M\nopen System\nlet startedUtc = DateTime.UtcNow\nlet grace = TimeSpan.FromMinutes 5.0\nlet late () = DateTime.Now - grace > startedUtc\nlet late2 () = DateTime.Now.Subtract(TimeSpan.FromHours 1.0) > startedUtc"

    match kindMixesIn source with
    | [ a; b ] ->
        Assert.Equal("DateTime.Now - grace", a.LocalText)
        Assert.Equal("DateTime.Now.Subtract(TimeSpan.FromHours 1.0)", b.LocalText)
    | other -> failwithf "Expected two findings, got %A" other

// ---- FR0169 SeqEnumeratedTwice ----

let private seqTwiceIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SeqEnumeratedTwice.find tree sourceText checkResults

[<Fact>]
let ``FR0169: a seq parameter walked twice on one path is noted at the first site`` () =
    let source =
        "module M\nlet report (xs: int seq) =\n    if Seq.isEmpty xs then \"none\" else $\"{Seq.length xs} items\"\nlet total (ys: seq<int>) =\n    for y in ys do\n        printfn \"%d\" y\n    ys |> Seq.map ((+) 1) |> Seq.sum\nlet twice (zs: System.Collections.Generic.IEnumerable<int>) =\n    let first = List.ofSeq zs\n    let again = Seq.length zs\n    first.Length + again"

    match seqTwiceIn source with
    | [ a; b; c ] ->
        Assert.Equal("xs", a.ParameterName)
        Assert.Equal(3, a.Range.StartLine)
        Assert.Equal(3, a.SecondLine)
        Assert.Equal("ys", b.ParameterName)
        Assert.Equal(5, b.Range.StartLine)
        Assert.Equal(7, b.SecondLine)
        Assert.Equal("zs", c.ParameterName)
        Assert.Equal(10, c.SecondLine)
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0169: different arms, a lambda, a list parameter, a shadow and a single walk stay quiet`` () =
    let source =
        "module M\nlet arms (xs: int seq) (flag: bool) =\n    if flag then Seq.length xs else Seq.sum xs\nlet matched (xs: int seq) (n: int) =\n    match n with\n    | 0 -> Seq.isEmpty xs\n    | _ -> Seq.exists ((=) n) xs\nlet deferred (xs: int seq) (run: (unit -> int) -> int) =\n    run (fun () -> Seq.length xs) + Seq.sum xs\nlet list (xs: int list) =\n    if List.isEmpty xs then 0 else List.length xs + Seq.length xs\nlet shadowed (xs: int seq) =\n    let xs = List.ofSeq xs\n    if xs.IsEmpty then 0 else Seq.length xs\nlet once (xs: int seq) =\n    xs |> Seq.map ((+) 1) |> Seq.filter ((<) 2) |> Seq.toList\nlet lazyOnly (xs: int seq) =\n    let ys = Seq.map ((+) 1) xs\n    let zs = Seq.filter ((<) 2) xs\n    Seq.append ys zs"

    Assert.Empty(seqTwiceIn source)

[<Fact>]
let ``FR0169: a nested function's and a member's seq parameter are read in their own scope`` () =
    let source =
        "module M\nlet outer (n: int) =\n    let inner (xs: int seq) =\n        if Seq.isEmpty xs then n else Seq.length xs\n    inner [ 1 ]\ntype T() =\n    member _.Count(ys: int seq) =\n        let first = Seq.tryHead ys\n        Seq.length ys + (defaultArg first 0)"

    match seqTwiceIn source with
    | [ a; b ] ->
        Assert.Equal("xs", a.ParameterName)
        Assert.Equal("ys", b.ParameterName)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0169: an inferred seq parameter and a lazily built local are walked twice too; cheap sources are not`` () =
    // SQLProvider's `itms`: a Seq.collect chain tested for emptiness and then
    // read - the second walk repeats the reflection
    let source =
        "module M\nlet inferred xs = if Seq.isEmpty xs then 0 else Seq.length xs\nlet local (ys: int list) (keep: int -> bool) =\n    let itms = ys |> Seq.filter keep |> Seq.map ((+) 1)\n    if Seq.isEmpty itms then 0 else itms |> Seq.head\nlet cached (ys: int list) (keep: int -> bool) =\n    let itms = ys |> Seq.filter keep |> Seq.cache\n    if Seq.isEmpty itms then 0 else itms |> Seq.head\nlet coerced (ys: int list) =\n    let itms = ys :> seq<int>\n    if Seq.isEmpty itms then 0 else itms |> Seq.head\nlet once (ys: int list) (keep: int -> bool) =\n    let itms = ys |> Seq.filter keep\n    itms |> Seq.length"

    match seqTwiceIn source with
    | [ a; b ] ->
        Assert.Equal("xs", a.ParameterName)
        Assert.Equal("itms", b.ParameterName)
        Assert.Equal(5, b.Range.StartLine)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0169: a local seq inside a generic member of a class is walked twice (SQLProvider's fetchItem)`` () =
    let source =
        "module M\ntype G<'k>(distinctItem: obj) as this =\n    inherit ResizeArray<obj>([| distinctItem |])\n    member private __.fetchItem<'ret> (itemType: string) (columnName: string option) =\n        let filterColumnValues (columnValues: seq<string * obj>) =\n            columnValues |> Seq.filter (fun (s, k) -> s.Contains itemType)\n        let itms =\n            match box distinctItem with\n            | :? string -> filterColumnValues Seq.empty\n            | _ -> Seq.empty\n        let itm =\n            if Seq.isEmpty itms then failwith \"x\"\n            else itms |> Seq.head |> snd\n        unbox<'ret> itm\n    member __.Count2 = this.fetchItem<int> \"COUNT\" None"

    match seqTwiceIn source with
    | [ s ] ->
        Assert.Equal("itms", s.ParameterName)
        Assert.Equal(12, s.Range.StartLine)
        Assert.Equal(13, s.SecondLine)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0160: a one-string constructor taking a parameter name is not the message overload`` () =
    // ArgumentNullException(paramName) vs (message, innerException): the
    // appended `, ex` would turn the parameter NAME into the message
    let source =
        "module M\nlet a (read: unit -> string) =\n    try read () with ex -> raise (System.ArgumentNullException(\"s\"))\nlet b (read: unit -> string) =\n    try read () with ex -> raise (System.ArgumentOutOfRangeException(\"i\"))\nlet c (read: unit -> string) =\n    try read () with ex -> raise (System.ObjectDisposedException(\"conn\"))"

    Assert.Empty(lostInnersIn source |> List.filter (fun s -> not s.Edits.IsEmpty))
