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
        fsharp
            """
            module M
            let average (sum: int) (count: int) = float (sum / count)
            let ratio (done': int64) (total: int64) = 1.0m + decimal (done' / total) |> float
            let share (hits: int) (all: int) = 100.0 * float (hits / all) ** 2.0
            """

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

        assertTypechecks "Patched source" patched
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
        fsharp
            """
            module M
            let a (x: float) (y: float) = float (x / y)
            let b (x: int) (y: int) = float (x * y)
            let c (x: int) (y: int) = float x / float y
            module Shadow =
                let float (x: int) = string x
                let d (x: int) (y: int) = float (x / y)
            """

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
        fsharp
            """
            module M
            exception ConfigError of string
            type ConfigException(message: string, inner: exn) =
                inherit System.Exception(message, inner)
                new(message: string) = ConfigException(message, null)
            let load (read: unit -> string) =
                try read () with ex -> raise (ConfigException("bad config"))
            let load2 (read: unit -> string) =
                try read () with _ -> raise (ConfigException "bad config")
            let load3 (read: unit -> string) =
                try read () with :? System.IO.IOException -> raise (System.InvalidOperationException("unreadable"))
            """

    match lostInnersIn source with
    | [ a; b; c ] ->
        let patched = applyAll source (a.Edits @ b.Edits @ c.Edits)
        Assert.Contains("""with ex -> raise (ConfigException("bad config", ex))""", patched)
        Assert.Contains("""with ex -> raise (ConfigException("bad config", ex))""", patched)

        Assert.Contains(
            """with :? System.IO.IOException as ex -> raise (System.InvalidOperationException("unreadable", ex))""",
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0160: a failwith that never reads the caught exception is the note`` () =
    let source =
        fsharp
            """
            module M
            let load (read: unit -> string) =
                try read () with _ -> failwith "could not load"
            let load2 (read: unit -> string) =
                try read () with ex -> failwithf "could not load: %s" ex.Message
            """

    match lostInnersIn source with
    | [ s ] ->
        Assert.Equal("failwith", s.Raised)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0160: a wrapper that carries the exception, or a type without the overload, stays quiet`` () =
    let source =
        fsharp
            """
            module M
            type Flat(message: string) =
                inherit System.Exception(message)
            let a (read: unit -> string) =
                try read () with ex -> raise (System.InvalidOperationException("unreadable", ex))
            let b (read: unit -> string) =
                try read () with ex -> raise (Flat "unreadable")
            let c (read: unit -> string) =
                try read () with ex -> raise (System.AggregateException([| ex |]))
            let d (read: unit -> string) = raise (System.InvalidOperationException "outside a handler")
            """

    Assert.Empty(lostInnersIn source)

// ---- FR0161 StructPropertyMutation ----

let private structMutationsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StructPropertyMutation.find tree sourceText checkResults

[<Fact>]
let ``FR0161: a mutating member called on the struct a property returns is noted`` () =
    let source =
        fsharp
            """
            module M
            [<Struct>]
            type Counter =
                val mutable N: int
                member this.Bump() = this.N <- this.N + 1
                member this.Value = this.N
            type Holder() =
                member val Counter = Counter() with get, set
            let bump (h: Holder) =
                h.Counter.Bump()
                h.Counter.Value
            let walk (h: Holder) (xs: ResizeArray<int>) =
                let mutable e = xs.GetEnumerator()
                e.MoveNext() |> ignore
                h.Counter.Value
            """

    match structMutationsIn source with
    | [ s ] ->
        Assert.Equal("h.Counter", s.PropertyText)
        Assert.Equal("Bump", s.Method)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0161: a reading member, a class property and a local mutable stay quiet`` () =
    let source =
        fsharp
            """
            module M
            type Counter() =
                member val N = 0 with get, set
                member this.Bump() = this.N <- this.N + 1
            type Holder() =
                member val Counter = Counter() with get, set
            let bump (h: Holder) =
                h.Counter.Bump()
                h.Counter.N
            let span (h: Holder) = h.Counter.ToString()
            """

    Assert.Empty(structMutationsIn source)

// ---- FR0162 LazyInit ----

let private lazyInitsIn (source: string) =
    let tree, sourceText = parse source
    LazyInit.find tree sourceText

[<Fact>]
let ``FR0162: a module mutable filled under an emptiness test is the racing lazy`` () =
    let source =
        fsharp
            """
            module M
            let mutable private cache: int list option = None
            let build () = [ 1; 2; 3 ]
            let index () =
                if cache.IsNone then
                    cache <- Some(build ())
                cache.Value
            let mutable private table: string = null
            let lookup () =
                match table with
                | null ->
                    table <- "built"
                    table
                | t -> t
            let mutable private matched: int option = None
            let value () =
                match matched with
                | None ->
                    matched <- Some 1
                    1
                | Some v -> v
            type Holder() =
                static let mutable shared: obj = null
                static member Shared =
                    if isNull shared then shared <- obj ()
                    shared
            """

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
        fsharp
            """
            module M
            let private gate = obj ()
            let mutable private cache: int option = None
            let index () =
                lock gate (fun () ->
                    if cache.IsNone then cache <- Some 1
                    cache.Value)
            let mutable private table: string = null
            let lookup () =
                if isNull table then table <- "built"
                table
            let reset () = table <- null
            let mutable private count = 0
            let bump () =
                if count = 0 then count <- 1
                count
            let local () =
                let mutable seen: int option = None
                if seen.IsNone then seen <- Some 1
                seen
            let mutable private holder: Lazy<string> = Unchecked.defaultof<Lazy<string>>
            let reconnecting () =
                if isNull holder || not holder.IsValueCreated || isNull holder.Value then
                    holder <- lazy "built"
                holder.Force()
            """

    Assert.Empty(lazyInitsIn source)

// ---- FR0163 DroppedTimer ----

let private droppedTimersIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DroppedTimer.find tree sourceText checkResults

[<Fact>]
let ``FR0163: a threading timer piped to ignore or dropped as a statement is noted`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading
            let start (tick: obj -> unit) =
                new Timer(TimerCallback tick, null, 0, 1000) |> ignore
                Timer(TimerCallback tick, null, 0, 1000) |> ignore
                ignore (new Timer(TimerCallback tick, null, 0, 1000))
                1
            """

    match droppedTimersIn source with
    | [ _; _; _ ] -> ()
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0163: a bound threading timer and a System.Timers.Timer stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading
            let start (tick: obj -> unit) =
                use timer = new Timer(TimerCallback tick, null, 0, 1000)
                let kept = new Timer(TimerCallback tick, null, 0, 1000)
                let t = new System.Timers.Timer(1000.0)
                t.Start()
                new System.Timers.Timer(500.0) |> ignore
                kept
            """

    Assert.Empty(droppedTimersIn source)

// ---- FR0164 EnumerationMutation ----

let private enumerationMutationsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    EnumerationMutation.find tree sourceText checkResults

[<Fact>]
let ``FR0164: a collection edited inside a for loop over itself walks a snapshot`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            let prune (items: List<int>) =
                for x in items do
                    if x < 0 then items.Remove x |> ignore
            let grow (d: Dictionary<int, int>) =
                for k in d.Keys do
                    d.Add(k + 100, k)
            let overwrite (xs: ResizeArray<int>) =
                for i in xs do
                    xs.[0] <- i
            """

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

        assertTypechecks "Patched source" patched

        let (r, _, replacement) = a.Filter.Value
        let filtered = applyEdit source r replacement

        Assert.Contains(
            fsharp
                """
                let prune (items: List<int>) =
                    items.RemoveAll(fun x -> x < 0) |> ignore
                let grow
                """,
            filtered
        )

        assertTypechecks "Filtered source" filtered
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0164: a body with more than the removal, or a condition naming the list, keeps the snapshot`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            let prune (items: List<int>) (log: int -> unit) =
                for x in items do
                    if x < 0 then
                        log x
                        items.Remove x |> ignore
            let dedupe (items: List<int>) =
                for x in items do
                    if items.IndexOf x > 0 then items.Remove x |> ignore
            """

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
        fsharp
            """
            module M
            open System
            open System.Collections.Generic
            let mutableLimit (items: List<int>) =
                let mutable limit = 0
                limit <- 3
                for x in items do
                    if x < limit then items.Remove x |> ignore
            let span (items: List<int>, s: ReadOnlySpan<int>) =
                for x in items do
                    if x < s.Length then items.Remove x |> ignore
            let commented (items: List<int>) =
                for x in items do
                    // negative entries are stale
                    if x < 0 then items.Remove x |> ignore
            """

    assertTypechecks "Test input" source

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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0164: a let mutable in another function is not the condition's name`` () =
    // `limit` in `prune` is its parameter; the `let mutable limit` of
    // `count` is out of its scope and cannot be what the closure captures
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            let count (xs: int list) =
                let mutable limit = 0
                for x in xs do
                    limit <- limit + x
                limit
            let prune (items: List<int>) (limit: int) =
                for x in items do
                    if x < limit then items.Remove x |> ignore
            """

    match enumerationMutationsIn source with
    | [ s ] ->
        let (r, _, replacement) = s.Filter.Value
        Assert.Equal("items.RemoveAll(fun x -> x < limit) |> ignore", replacement)
        let filtered = applyEdit source r replacement
        assertTypechecks "Filtered source" filtered
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0164: a removal from a dictionary or set, an edit to another collection, and a concurrent one stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            open System.Collections.Concurrent
            let prune (d: Dictionary<int, int>) (h: HashSet<int>) =
                for KeyValue(k, v) in d do
                    if v < 0 then d.Remove k |> ignore
                    d.[k] <- v + 1
                for x in h do
                    if x < 0 then h.Remove x |> ignore
            let copy (src: List<int>) (dst: List<int>) =
                for x in src do
                    dst.Add x
            let bag (b: ConcurrentBag<int>) =
                for x in b do
                    b.Add x
            let immutable (xs: int list) (acc: List<int>) =
                for x in xs do
                    acc.Add x
            """

    Assert.Empty(enumerationMutationsIn source)

// ---- regressions ----

[<Fact>]
let ``FR0160: a named argument stands the fix down, and a curried failwithf is one note`` () =
    let source =
        fsharp
            """
            module M
            let a (read: unit -> string) =
                try read () with ex -> raise (System.ArgumentException(message = "bad"))
            let b (read: unit -> string) (name: string) =
                try read () with _ -> failwithf "could not read %s for %d" name 3
            """

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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0162: a store under a piped lock, a qualified reset and a test file stay quiet`` () =
    let source =
        fsharp
            """
            module M
            let private gate = obj ()
            let mutable private cache: int option = None
            let index () =
                lock gate <| fun () ->
                    if cache.IsNone then cache <- Some 1
                    cache.Value
            module Inner =
                let mutable table: string = null
                let lookup () =
                    if isNull table then table <- "built"
                    table
            let reset () = Inner.table <- null
            """

    Assert.Empty(lazyInitsIn source)

    let test =
        fsharp
            """
            module T
            open Xunit
            let mutable private fixture: int option = None
            let get () =
                if fixture.IsNone then fixture <- Some 1
                fixture.Value
            [<Fact>]
            let ``reads`` () = Assert.Equal(1, get ())
            """

    Assert.Empty(lazyInitsIn test)

[<Fact>]
let ``FR0164: an interface-typed collection stays quiet, and the F# 6 indexer store is an edit`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            let viaInterface (items: IList<int>) =
                for x in items do
                    if x < 0 then items.Remove x |> ignore
            let indexer (xs: ResizeArray<int>) =
                for i in xs do
                    xs[0] <- i
            """

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
        fsharp
            """
            module M
            open System.Collections.Generic
            let deferred (items: List<int>) (later: List<unit -> unit>) =
                for x in items do
                    later.Add(fun () -> items.Remove x |> ignore)
            let local (items: List<int>) =
                for x in items do
                    let drop () = items.Remove x |> ignore
                    drop ()
            let leaves (items: List<int>) =
                for x in items do
                    if x < 0 then
                        items.Remove x |> ignore
                        failwith "negative"
            let returns (items: List<int>) =
                seq {
                    for x in items do
                        if x < 0 then
                            items.Remove x |> ignore
                            yield x
                }
            let shadowed (items: List<int>) (other: List<int>) =
                for x in items do
                    let items = other
                    items.Remove x |> ignore
            """

    // the `seq` case still fires: a `yield` resumes the loop
    match enumerationMutationsIn source with
    | [ s ] -> Assert.Equal(17, s.Range.StartLine)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0160: a raise inside a lambda or a nested try, and a message reading the exception, stay quiet`` () =
    let source =
        fsharp
            """
            module M
            let a (read: unit -> string) (items: int list) =
                try read () with ex -> items |> List.iter (fun _ -> raise (System.InvalidOperationException("x"))); ""
            let b (read: unit -> string) =
                try read () with ex -> failwithf "%s" ex.Message
            let c (read: unit -> string) =
                try read () with ex -> raise (System.InvalidOperationException("failed: " + ex.Message))
            let d (read: unit -> string) =
                try read () with ex ->
                    try read () with _ -> raise (System.InvalidOperationException("inner"))
            """

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
        fsharp
            """
            module M
            let a (x: int) (y: int) = floor (float (x / y))
            let b (x: int) (y: int) = System.Math.Round(float (x / y))
            let c (x: int) = float (x / 1)
            """

    Assert.Empty(intDivisionsIn source)

[<Fact>]
let ``FR0163: a local timer the scope never mentions again is dropped too`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading
            let start (tick: obj -> unit) (keep: Timer -> unit) =
                let forgotten = new Timer(TimerCallback tick, null, 0, 1000)
                let _ = new Timer(TimerCallback tick, null, 0, 1000)
                let passed = new Timer(TimerCallback tick, null, 0, 1000)
                keep passed
                let returned = new Timer(TimerCallback tick, null, 0, 1000)
                returned
            """

    match droppedTimersIn source with
    | [ a; b ] ->
        Assert.Equal(4, a.Range.StartLine)
        Assert.Equal(5, b.Range.StartLine)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0123: the statements between the acquire and its release move under a try, the release into the finally`` () =
    let source =
        fsharp
            """
            module M =
                let sem = new System.Threading.SemaphoreSlim(1)
                let mutable count = 0
                let bump (log: string -> unit) =
                    sem.Wait()
                    count <- count + 1
                    // the tally
                    log "bumped"
                    sem.Release() |> ignore
                    count
                let awaited (t: System.Threading.Tasks.Task) =
                    task {
                        do! sem.WaitAsync()
                        do! t
                        sem.Release() |> ignore
                        return count
                    }
            """

    match leaksIn source with
    | [ a; b ] ->
        let patched =
            [ a; b ]
            |> List.choose (fun s -> s.Fix)
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                        sem.Wait()
                        try
                            count <- count + 1
                            // the tally
                            log "bumped"
                        finally
                            sem.Release() |> ignore
                        count
                """,
            patched
        )

        Assert.Contains(
            fsharp
                """
                            do! sem.WaitAsync()
                            try
                                do! t
                            finally
                                sem.Release() |> ignore
                            return count
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected two leak notes, got %A" other

[<Fact>]
let ``FR0123: a binding between the acquire and the release that is read after, or no release in the block, leaves the note without a fix``
    ()
    =
    let source =
        fsharp
            """
            module M =
                let sem = new System.Threading.SemaphoreSlim(1)
                let mutable count = 0
                let readAfter (compute: unit -> int) =
                    sem.Wait()
                    let v = compute ()
                    sem.Release() |> ignore
                    v + count
                let elsewhere (compute: unit -> int) =
                    sem.Wait()
                    count <- compute ()
                    count
                let bound (compute: unit -> int) =
                    sem.Wait()
                    let v = compute ()
                    count <- v
                    sem.Release() |> ignore
            """

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
        fsharp
            """
            module M
            open System
            let startedUtc = DateTime.UtcNow
            let expired () = DateTime.Now > startedUtc
            let age () = DateTime.UtcNow - DateTime.Today
            let cmp () = DateTime.Now.CompareTo startedUtc
            let cmp2 () = DateTime.Compare(startedUtc.AddDays 1.0, DateTime.Today)
            let local () =
                let now = DateTime.Now
                now.Date <= startedUtc
            """

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
        fsharp
            """
            module M
            open System
            let startedUtc = DateTime.UtcNow
            let explicit () = DateTime.Now.ToUniversalTime() > startedUtc
            let specified () = DateTime.SpecifyKind(DateTime.Now, DateTimeKind.Utc) > startedUtc
            let mutable stamp = DateTime.Now
            let reassigned () =
                stamp <- DateTime.UtcNow
                stamp > startedUtc
            let param (t: DateTime) = t > startedUtc
            let offset () = DateTime.Now - DateTime.UtcNow
            let same () = DateTime.UtcNow > startedUtc && DateTime.Now > DateTime.Today
            let span () = DateTime.Now - TimeSpan.FromHours 1.0 > DateTime.Today
            let bound = DateTime.Now
            let bound2 = 1
            let twice () =
                let bound = DateTime.UtcNow
                bound > startedUtc
            """

    Assert.Empty(kindMixesIn source)

[<Fact>]
let ``FR0165: a parameter sharing a bound name, and durations computed in either kind, stay quiet`` () =
    // `now` is a local `let` in one function and a parameter in another: the
    // parameter is not that `let`; two durations differ by no offset at all
    let source =
        fsharp
            """
            module M
            open System
            let startedUtc = DateTime.UtcNow
            let a () =
                let now = DateTime.Now
                now.Year
            let b (now: DateTime) = now > startedUtc
            let durations (t: DateTime) (u: DateTime) = DateTime.Now - t > DateTime.UtcNow - u
            let subtracted (t: DateTime) = DateTime.Now.Subtract t > DateTime.UtcNow.Subtract startedUtc
            """

    Assert.Empty(kindMixesIn source)

[<Fact>]
let ``FR0165: a plain TimeSpan taken off a clock read keeps its kind`` () =
    let source =
        fsharp
            """
            module M
            open System
            let startedUtc = DateTime.UtcNow
            let grace = TimeSpan.FromMinutes 5.0
            let late () = DateTime.Now - grace > startedUtc
            let late2 () = DateTime.Now.Subtract(TimeSpan.FromHours 1.0) > startedUtc
            """

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
        fsharp
            """
            module M
            let report (xs: int seq) =
                if Seq.isEmpty xs then "none" else $"{Seq.length xs} items"
            let total (ys: seq<int>) =
                for y in ys do
                    printfn "%d" y
                ys |> Seq.map ((+) 1) |> Seq.sum
            let twice (zs: System.Collections.Generic.IEnumerable<int>) =
                let first = List.ofSeq zs
                let again = Seq.length zs
                first.Length + again
            """

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
        fsharp
            """
            module M
            let arms (xs: int seq) (flag: bool) =
                if flag then Seq.length xs else Seq.sum xs
            let matched (xs: int seq) (n: int) =
                match n with
                | 0 -> Seq.isEmpty xs
                | _ -> Seq.exists ((=) n) xs
            let deferred (xs: int seq) (run: (unit -> int) -> int) =
                run (fun () -> Seq.length xs) + Seq.sum xs
            let list (xs: int list) =
                if List.isEmpty xs then 0 else List.length xs + Seq.length xs
            let shadowed (xs: int seq) =
                let xs = List.ofSeq xs
                if xs.IsEmpty then 0 else Seq.length xs
            let once (xs: int seq) =
                xs |> Seq.map ((+) 1) |> Seq.filter ((<) 2) |> Seq.toList
            let lazyOnly (xs: int seq) =
                let ys = Seq.map ((+) 1) xs
                let zs = Seq.filter ((<) 2) xs
                Seq.append ys zs
            """

    Assert.Empty(seqTwiceIn source)

[<Fact>]
let ``FR0169: a nested function's and a member's seq parameter are read in their own scope`` () =
    let source =
        fsharp
            """
            module M
            let outer (n: int) =
                let inner (xs: int seq) =
                    if Seq.isEmpty xs then n else Seq.length xs
                inner [ 1 ]
            type T() =
                member _.Count(ys: int seq) =
                    let first = Seq.tryHead ys
                    Seq.length ys + (defaultArg first 0)
            """

    match seqTwiceIn source with
    | [ a; b ] ->
        Assert.Equal("xs", a.ParameterName)
        Assert.Equal("ys", b.ParameterName)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0169: an inferred seq parameter and a lazily built local are walked twice too; cheap sources are not`` () =
    // a lazy Seq chain tested for emptiness and then read - the second
    // walk repeats the whole pipeline
    let source =
        fsharp
            """
            module M
            let inferred xs = if Seq.isEmpty xs then 0 else Seq.length xs
            let local (ys: int list) (keep: int -> bool) =
                let itms = ys |> Seq.filter keep |> Seq.map ((+) 1)
                if Seq.isEmpty itms then 0 else itms |> Seq.head
            let cached (ys: int list) (keep: int -> bool) =
                let itms = ys |> Seq.filter keep |> Seq.cache
                if Seq.isEmpty itms then 0 else itms |> Seq.head
            let coerced (ys: int list) =
                let itms = ys :> seq<int>
                if Seq.isEmpty itms then 0 else itms |> Seq.head
            let once (ys: int list) (keep: int -> bool) =
                let itms = ys |> Seq.filter keep
                itms |> Seq.length
            """

    match seqTwiceIn source with
    | [ a; b ] ->
        Assert.Equal("xs", a.ParameterName)
        Assert.Equal("itms", b.ParameterName)
        Assert.Equal(5, b.Range.StartLine)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0169: a local seq inside a generic member of a class is walked twice (SQLProvider's fetchItem)`` () =
    let source =
        fsharp
            """
            module M
            type G<'k>(distinctItem: obj) as this =
                inherit ResizeArray<obj>([| distinctItem |])
                member private __.fetchItem<'ret> (itemType: string) (columnName: string option) =
                    let filterColumnValues (columnValues: seq<string * obj>) =
                        columnValues |> Seq.filter (fun (s, k) -> s.Contains itemType)
                    let itms =
                        match box distinctItem with
                        | :? string -> filterColumnValues Seq.empty
                        | _ -> Seq.empty
                    let itm =
                        if Seq.isEmpty itms then failwith "x"
                        else itms |> Seq.head |> snd
                    unbox<'ret> itm
                member __.Count2 = this.fetchItem<int> "COUNT" None
            """

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
        fsharp
            """
            module M
            let a (read: unit -> string) =
                try read () with ex -> raise (System.ArgumentNullException("s"))
            let b (read: unit -> string) =
                try read () with ex -> raise (System.ArgumentOutOfRangeException("i"))
            let c (read: unit -> string) =
                try read () with ex -> raise (System.ObjectDisposedException("conn"))
            """

    Assert.Empty(lostInnersIn source |> List.filter (fun s -> not s.Edits.IsEmpty))
