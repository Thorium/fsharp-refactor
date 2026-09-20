/// The correctness rules around exceptions, arithmetic, clocks and locks:
/// FR0044 Reraise, FR0055 SwallowedException, FR0063 RaiseInFinally,
/// FR0064 ReservedException, FR0092 FailwithContext, FR0151
/// ExceptionDetail, FR0152 CachedFailure, FR0045 NaNComparison, FR0105
/// CheckedArithmetic, FR0136 EmptyGuid, FR0121 DateTimeRules, FR0134
/// DateTimeOffsetMigration, FR0123 MonitorLock (the semaphore leak too),
/// FR0046 WeakLock, FR0159 IntDivisionToFloat, FR0160 LostInnerException,
/// FR0162 LazyInit, FR0163 DroppedTimer, FR0165 DateTimeKindMix.
///
/// FR0120 CatchLogException is typed-gated to entities whose full name
/// starts with Microsoft.Extensions.Logging, Serilog or Logary, which a
/// script cannot declare; the harness's stub file (Typed.stubs) declares
/// the MEL logger and its extension methods ahead of the script for it.
module FSharp.Refactor.PropertyTests.Families.Correctness

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private shapes =
    [
        // FR0120: a handler logs a message without the exception it caught
        withFree
            "HandlerLogsWithoutException"
            [ "FR0120" ]
            (Gen.zip genWord (Gen.elements [ "LogError"; "LogWarning" ]))
            (fun (word, method) i ->
                $"let f{i} (logger: ILogger) (work: unit -> int) =\n    try\n        work ()\n    with ex ->\n        logger.{method}(\"{word} failed\")\n        0")
        // FR0044: `raise ex` in the handler that bound `ex`
        fixed' "RaiseCaught" [ "FR0044" ] (fun i ->
            $"let f{i} (act: unit -> int) =\n    try\n        act ()\n    with ex ->\n        printfn \"%%s\" ex.Message\n        raise ex")
        // FR0044: the typed handler with an as-binding
        fixed' "RaiseCaughtTyped" [ "FR0044" ] (fun i ->
            $"let f{i} (act: unit -> int) =\n    try\n        act ()\n    with :? IOException as ex ->\n        printfn \"%%s\" ex.Message\n        raise ex")
        // FR0044: inside a task the handler guards nothing, so the try/with goes
        withFree "RaiseCaughtInTask" [ "FR0044" ] genSmall (fun n i ->
            $"let f{i} (t: Task<int>) =\n    task {{\n        try\n            let! x = t\n            return x + {n}\n        with ex ->\n            return raise ex\n    }}")
        // FR0055: the empty catch-all
        withFree
            "EmptyCatchAll"
            [ "FR0055" ]
            (Gen.elements [ "_"; ":? Exception"; "_ when Console.IsOutputRedirected" ])
            (fun p i -> $"let f{i} (act: unit -> unit) =\n    try\n        act ()\n    with {p} -> ()")
        // FR0055: a division whose catch is really a zero guard
        withFree "DivisionFallback" [ "FR0055" ] genSmall (fun n i ->
            $"let f{i} (a: int) (b: int) =\n    try\n        a / b\n    with _ -> {n}")
        // FR0055: a Parse whose catch is really TryParse
        withFree "ParseFallback" [ "FR0055" ] genSmall (fun n i ->
            $"let f{i} (s: string) =\n    try\n        Int32.Parse s\n    with _ -> {n}")
        // FR0055: a one-line IO body, offered the narrower IO catch
        withFree "IoFallback" [ "FR0055" ] genWord (fun w i ->
            $"let f{i} (p: string) =\n    try\n        File.ReadAllText p\n    with _ -> \"{w}\"")
        // FR0055: the narrow catch that is TryParse as control flow
        withFree
            "NarrowParseCatch"
            [ "FR0055" ]
            (Gen.zip genSmall (Gen.elements [ ":? FormatException"; ":? FormatException | :? OverflowException" ]))
            (fun (n, pat) i -> $"let f{i} (s: string) =\n    try Int32.Parse s with {pat} -> {n}")
        // FR0055: the Some-wrapped Parse with its None fallback
        fixed' "WrappedParseFallback" [ "FR0055" ] (fun i ->
            $"let f{i} (s: string) =\n    try\n        Some(Int64.Parse s)\n    with :? FormatException -> None")
        // FR0159: a float of an integer division, two names or a literal
        withFree
            "IntDivisionWidened"
            [ "FR0159" ]
            (Gen.zip (Gen.elements [ "float"; "double"; "decimal"; "float32" ]) genSmall)
            (fun (conv, n) i ->
                $"let f{i} (sum: int) (count: int) = {conv} (sum / count)\nlet g{i} (ms: int64) = {conv} (ms / {n + 1}L) + {conv} 1")
        // FR0160: a wrapper raised without the caught exception, with and without a binder
        withFree
            "LostInner"
            [ "FR0160" ]
            (Gen.zip genWord (Gen.elements [ "ex"; "_"; ":? IOException" ]))
            (fun (w, pat) i ->
                $"let f{i} (read: unit -> string) =\n    try\n        read ()\n    with {pat} -> raise (InvalidOperationException(\"{w}\"))")
        // FR0159: a negative literal divisor keeps its parentheses in the fix
        withFree "IntDivisionNegativeLiteral" [ "FR0159" ] genSmall (fun n i ->
            $"let f{i} (x: int) = float (x / -{n + 1})")
        // FR0160: the failwith that never reads what it caught, plain and curried
        withFree
            "LostInnerFailwith"
            [ "FR0160" ]
            (Gen.zip genWord (Gen.elements [ true; false ]))
            (fun (w, curried) i ->
                if curried then
                    $"let f{i} (read: unit -> string) (name: string) =\n    try\n        read ()\n    with _ -> failwithf \"{w} %%s %%d\" name {i}"
                else
                    $"let f{i} (read: unit -> string) =\n    try\n        read ()\n    with _ -> failwith \"{w}\"")
        // FR0160: a named argument stands the fix down; the wrapper is still noted
        withFree "LostInnerNamedArg" [ "!FR0160" ] genWord (fun w i ->
            $"let f{i} (read: unit -> string) =\n    try\n        read ()\n    with ex -> raise (ArgumentException(message = \"{w}\"))")
        // FR0162: a module mutable filled under its own emptiness test — an
        // `if`, or the None arm of a match
        withFree "CheckThenAssign" [ "FR0162" ] (Gen.zip genSmall (Gen.elements [ true; false ])) (fun (n, matched) i ->
            if matched then
                $"module Cache{i} =\n    let mutable private slot: int option = None\n    let value () =\n        match slot with\n        | None ->\n            slot <- Some {n}\n            {n}\n        | Some v -> v"
            else
                $"module Cache{i} =\n    let mutable private slot: int option = None\n    let value () =\n        if slot.IsNone then\n            slot <- Some {n}\n        slot.Value")
        // FR0162 must stay quiet: the store sits under a lock, piped or applied
        withFree "CheckThenAssignLocked" [ "!FR0162" ] (Gen.elements [ true; false ]) (fun piped i ->
            let body = "if slot.IsNone then slot <- Some 1\n            slot.Value"

            if piped then
                $"module Cache{i} =\n    let private gate = obj ()\n    let mutable private slot: int option = None\n    let value () =\n        lock gate <| fun () ->\n            {body}"
            else
                $"module Cache{i} =\n    let private gate = obj ()\n    let mutable private slot: int option = None\n    let value () =\n        lock gate (fun () ->\n            {body})")
        // FR0165: a local clock read against a UTC one, directly or through a binding
        withFree "MixedDateTimeKinds" [ "FR0165" ] (Gen.elements [ ">"; "<="; "<>"; "-" ]) (fun op i ->
            $"module Clock{i} =\n    let startedUtc = DateTime.UtcNow\n    let check{i} () = DateTime.Now {op} startedUtc")
        // FR0165 must stay quiet: an explicit kind, one kind on both sides,
        // the machine's-offset idiom
        withFree "SameDateTimeKinds" [ "!FR0165" ] (Gen.elements [ true; false ]) (fun explicit' i ->
            if explicit' then
                $"module Clock{i} =\n    let startedUtc = DateTime.UtcNow\n    let check{i} () = DateTime.Now.ToUniversalTime() > startedUtc\n    let offset{i} () = DateTime.Now - DateTime.UtcNow"
            else
                $"module Clock{i} =\n    let started = DateTime.Now\n    let check{i} () = DateTime.Now.Date > started.Date")
        // FR0163: a threading timer dropped into ignore
        withFree "DroppedTimer" [ "FR0163" ] genSmall (fun n i ->
            $"let f{i} (tick: obj -> unit) =\n    new Timer(TimerCallback tick, null, 0, {n + 1}) |> ignore\n    {n}")
        // FR0163: a local timer the scope never mentions again
        withFree "ForgottenTimer" [ "FR0163" ] genSmall (fun n i ->
            $"let f{i} (tick: obj -> unit) =\n    let ticker = new Timer(TimerCallback tick, null, 0, {n + 1})\n    {n}")
        // FR0163 must stay quiet: the timer leaves the scope
        withFree "KeptTimer" [ "!FR0163" ] genSmall (fun n i ->
            $"let f{i} (tick: obj -> unit) (keep: Timer -> unit) =\n    let ticker = new Timer(TimerCallback tick, null, 0, {n + 1})\n    keep ticker\n    {n}")
        // FR0160 must stay quiet: the raise runs inside a lambda, and a
        // message that reads the exception is the author's choice
        withFree
            "LostInnerDeferred"
            [ "!FR0160" ]
            (Gen.zip genWord (Gen.elements [ true; false ]))
            (fun (w, lambda) i ->
                if lambda then
                    $"let f{i} (read: unit -> string) (xs: int list) =\n    try\n        read ()\n    with ex ->\n        xs |> List.iter (fun _ -> raise (InvalidOperationException(\"{w}\")))\n        \"\""
                else
                    $"let f{i} (read: unit -> string) =\n    try\n        read ()\n    with ex -> raise (InvalidOperationException(\"{w}: \" + ex.Message))")
        // FR0123: a semaphore slot taken with no finally
        withFree "SemaphoreLeak" [ "FR0123" ] genSmall (fun n i ->
            $"let f{i} (sem: SemaphoreSlim) (xs: List<int>) =\n    sem.Wait()\n    xs.Add {n}\n    sem.Release() |> ignore\n    xs.Count")
        // FR0123: the awaited acquire in a task
        withFree "SemaphoreLeakAsync" [ "FR0123" ] genSmall (fun n i ->
            $"let f{i} (sem: SemaphoreSlim) (t: Task<int>) =\n    task {{\n        do! sem.WaitAsync()\n        let! v = t\n        sem.Release() |> ignore\n        return v + {n}\n    }}")
        // FR0123 must stay quiet: the release sits in a finally the next
        // `let!` holds, or a `let` before the try (Fuuga's shapes)
        withFree "SemaphoreGuarded" [ "!FR0123" ] genSmall (fun n i ->
            $"let f{i} (sem: SemaphoreSlim) (t: Task<int>) (xs: List<int>) =\n    task {{\n        do! sem.WaitAsync()\n        let! v =\n            task {{\n                try return! t\n                finally sem.Release() |> ignore\n            }}\n        sem.Wait()\n        let mutable acquired = 0\n        try\n            xs.Add {n}\n            acquired <- 1\n        finally\n            sem.Release() |> ignore\n        return v + acquired\n    }}")
        // FR0063: a failwith inside finally
        withFree "RaiseInFinally" [ "FR0063" ] genWord (fun w i ->
            $"let f{i} (act: unit -> int) (cleanup: unit -> unit) =\n    try\n        act ()\n    finally\n        cleanup ()\n        failwith \"{w}\"")
        // FR0064: a reserved runtime exception raised by hand
        withFree
            "ReservedException"
            [ "FR0064" ]
            (Gen.elements [ "IndexOutOfRangeException"; "NullReferenceException"; "OutOfMemoryException" ])
            (fun t i -> $"let f{i} () : int = raise (System.{t} \"custom\")")
        // FR0092: a constant failwith message in a function with a printable parameter
        withFree "StaticFailwith" [ "FR0092" ] (Gen.zip genWord genSmall) (fun (w, n) i ->
            $"let f{i} (count: int) =\n    if count > {n} then\n        failwith \"{w}\"\n    else\n        count")
        // FR0151: a ReflectionTypeLoadException handler reading only .Message
        fixed' "LoaderMessageOnly" [ "FR0151" ] (fun i ->
            $"let f{i} (a: System.Reflection.Assembly) =\n    try\n        a.GetTypes() |> Array.length\n    with :? System.Reflection.ReflectionTypeLoadException as e ->\n        printfn \"%%s\" e.Message\n        0")
        // FR0151: the same handler rethrowing, offered the carry-on too
        fixed' "LoaderRethrow" [ "FR0151" ] (fun i ->
            $"let f{i} (a: System.Reflection.Assembly) : Type[] =\n    try\n        a.GetTypes()\n    with :? System.Reflection.ReflectionTypeLoadException as e ->\n        printfn \"%%s\" e.Message\n        reraise ()")
        // FR0151: WebException is the note without a fix
        withFree "WebMessageOnly" [ "FR0151" ] genSmall (fun n i ->
            $"let f{i} (act: unit -> int) =\n    try\n        act ()\n    with :? System.Net.WebException as wex ->\n        printfn \"%%s\" wex.Message\n        {n}")
        // FR0152: GetOrAdd over a Task-valued cache
        withFree "CachedTask" [ "FR0152" ] genSmall (fun n i ->
            $"let f{i} (cache: System.Collections.Concurrent.ConcurrentDictionary<string, Task<int>>) (k: string) =\n    cache.GetOrAdd(k, (fun _ -> Task.FromResult {n}))")
        // FR0152: GetOrAdd over a Lazy-valued cache
        withFree "CachedLazy" [ "FR0152" ] genSmall (fun n i ->
            $"let f{i} (cache: System.Collections.Concurrent.ConcurrentDictionary<string, Lazy<int>>) (k: string) =\n    cache.GetOrAdd(k, (fun _ -> lazy {n}))")
        // FR0045: equality against NaN in its spellings
        withFree
            "NaNEquality"
            [ "FR0045" ]
            (Gen.elements
                [
                    "float", "x = nan"
                    "float", "nan = x"
                    "float", "x <> Double.NaN"
                    "float", "x = System.Double.NaN"
                    "float32", "x = Single.NaN"
                    "float32", "x <> System.Single.NaN"
                ])
            (fun (t, e) i -> $"let f{i} (x: {t}) = {e}")
        // FR0105: a unit-conversion multiplier
        withFree "ScaleFactor" [ "FR0105" ] (Gen.elements [ "1_000_000"; "1000000"; "10_000_000" ]) (fun c i ->
            $"let f{i} (seconds: int) = seconds * {c}")
        // FR0105: a constant within a factor of two of the ceiling
        withFree "NearLimit" [ "FR0105" ] (Gen.elements [ "2_000_000_000"; "1_500_000_000" ]) (fun c i ->
            $"let f{i} (balance: int) = balance + {c}")
        // FR0105: arithmetic on the limit itself
        fixed' "LimitConstant" [ "FR0105" ] (fun i -> $"let f{i} (n: int) = Int32.MaxValue + n")
        // FR0136: the zero-argument Guid constructor
        withFree "EmptyGuid" [ "FR0136" ] (Gen.elements [ "Guid()"; "new Guid()"; "System.Guid()" ]) (fun e i ->
            $"let g{i} = {e}")
        // FR0121: a bare DateTime.Now
        fixed' "LocalNow" [ "FR0121" ] (fun i -> $"let f{i} () = DateTime.Now")
        // FR0121: Now read as an instant through Ticks
        fixed' "LocalNowTicks" [ "FR0121" ] (fun i -> $"let f{i} () = DateTime.Now.Ticks.ToString()")
        // FR0121: the timezone-random calendar cut
        withFree "UtcDateCut" [ "FR0121" ] (Gen.elements [ "DateTime.UtcNow.Date"; "DateTime.Today" ]) (fun e i ->
            $"let f{i} () = {e}")
        // FR0134: a file-private record whose DateTime field only ever holds UtcNow
        withFree "PrivateUtcField" [ "FR0134" ] genWord (fun w i ->
            $"module private M{i} =\n    type R{i} = {{ Seen: DateTime; Name: string }}\n    let mk{i} () = {{ Seen = DateTime.UtcNow; Name = \"{w}\" }}\n    let year{i} (r: R{i}) = r.Seen.Year\n    let newer{i} (a: R{i}) (b: R{i}) = a.Seen > b.Seen")
        // FR0123: the canonical Enter/try/finally/Exit
        withFree "MonitorEnterExit" [ "FR0123" ] genSmall (fun n i ->
            $"let f{i} (gate: obj) (xs: List<int>) =\n    Monitor.Enter gate\n    try\n        xs.Add {n}\n        xs.Count\n    finally\n        Monitor.Exit gate")
        // FR0123: a bare Enter is the leak note
        withFree "MonitorBareEnter" [ "FR0123" ] genSmall (fun n i ->
            $"let f{i} (gate: obj) (xs: List<int>) =\n    Monitor.Enter gate\n    xs.Add {n}\n    Monitor.Exit gate\n    xs.Count")
        // FR0046: a lock on a string literal, given a lock object before the binding
        withFree "LockOnString" [ "FR0046" ] genWord (fun w i ->
            $"let f{i} (xs: List<int>) = lock \"{w}\" (fun () -> xs.Add 1)")
        // FR0046: a lock on a Type object
        withFree "LockOnType" [ "FR0046" ] (Gen.elements [ "typeof<string>"; "typeof<int>" ]) (fun t i ->
            $"let f{i} (xs: List<int>) = lock {t} (fun () -> xs.Add 1)")
        // FR0046: a lock on a process-wide writer, the note without a fix
        withFree "LockOnStdout" [ "FR0046" ] (Gen.elements [ "stdout"; "stderr"; "Console.Out" ]) (fun t i ->
            $"let f{i} (s: string) = lock {t} (fun () -> printfn \"%%s\" s)")
    ]

let private fixes (code: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    code, [ for r, _, replacement in edits -> edit code r replacement ]

let family: Family =
    {
        Name = "Correctness"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    // FR0120: the exception goes first, as MEL and Serilog spell it
                    for s in CatchLogException.find c.Tree c.Source c.Check do
                        yield "FR0120", [ edit "FR0120" s.Range $"{s.ExceptionName}, " ]
                    for s in Reraise.find c.Tree c.Source c.Check do
                        match s.Removal with
                        | Some(r, _, replacement) -> yield "FR0044", [ edit "FR0044" r replacement ]
                        | None -> yield "FR0044", [ edit "FR0044" s.Range "reraise ()" ]
                    // every offer is its own edit set, as the editor applies them
                    for s in SwallowedException.find c.Tree c.Source (Some c.Check) do
                        for offer in s.Offers do
                            yield fixes "FR0055" offer.Edits
                    // the fix applies only under --api-changes; here that is off
                    if Visibility.apiChangesAllowed () then
                        for s in FailwithContext.find c.Tree c.Source c.Check do
                            yield
                                fixes
                                    "FR0092"
                                    ((s.Range, s.OriginalText, s.ReplacementText) :: Option.toList s.PatternEdit)
                    for s in ExceptionDetail.find c.Tree c.Source c.Check do
                        for r, _, replacement in Option.toList s.AlternativeFix do
                            yield "FR0151", [ edit "FR0151" r replacement ]

                        for r, _, replacement in Option.toList s.Fix do
                            yield "FR0151", [ edit "FR0151" r replacement ]
                    for s in NaNComparison.find c.Tree c.Source c.Check do
                        yield "FR0045", [ edit "FR0045" s.Range s.ReplacementText ]
                    for s in CheckedArithmetic.find c.Tree c.Source do
                        for r, _, replacement in Option.toList s.WidenFix do
                            yield "FR0105", [ edit "FR0105" r replacement ]

                        for r, _, replacement in Option.toList s.CheckedFix do
                            yield "FR0105", [ edit "FR0105" r replacement ]
                    for s in EmptyGuid.find c.Tree c.Source c.Check do
                        yield "FR0136", [ edit "FR0136" s.Range s.EmptyText ]
                        yield "FR0136", [ edit "FR0136" s.Range s.NewGuidText ]
                    for s in DateTimeRules.find c.Tree c.Source c.Check do
                        match s.Kind, s.FixRange with
                        | DateTimeRules.WallClockKind.LocalNow, Some r -> yield "FR0121", [ edit "FR0121" r "UtcNow" ]
                        | _ -> ()
                    for s in DateTimeOffsetMigration.find (Visibility.apiChangesAllowed ()) c.Tree c.Source do
                        if s.IsFilePrivate then
                            match DateTimeOffsetMigration.migrate c.Tree c.Source c.Check s with
                            | Some edits -> yield fixes "FR0134" edits
                            | None -> ()
                    for s in MonitorLock.find c.Tree c.Source c.Check do
                        for r, _, replacement in Option.toList s.Fix do
                            yield "FR0123", [ edit "FR0123" r replacement ]
                    for s in MonitorLock.findLeaks c.Tree c.Source c.Check do
                        for r, _, replacement in Option.toList s.Fix do
                            yield "FR0123", [ edit "FR0123" r replacement ]
                    // the narrow-catch TryParse rewrite, offered in the editor
                    for s in SwallowedException.findParseControlFlow c.Tree c.Source do
                        for offer in s.Offers do
                            yield fixes "FR0055" offer.Edits
                    // the editor offers the fix for a literal operand too
                    for s in IntDivisionToFloat.find c.Tree c.Source c.Check do
                        yield "FR0159", [ edit "FR0159" s.Range s.ReplacementText ]
                    for s in LostInnerException.find c.Tree c.Source c.Check do
                        if not s.Edits.IsEmpty then
                            yield fixes "FR0160" s.Edits
                    for s in WeakLock.find c.Tree c.Source c.Check do
                        if not s.Fix.IsEmpty then
                            yield fixes "FR0046" s.Fix
                ]
        Notes =
            fun c ->
                [
                    for s in SwallowedException.find c.Tree c.Source (Some c.Check) -> "FR0055", s.Range
                    let finallies, reserved = ExceptionRules.find c.Tree c.Source
                    for s in finallies -> "FR0063", s.Range
                    for s in reserved -> "FR0064", s.Range

                    if not (SwallowedException.isTestFile (AstIndex.ofTree c.Tree) c.Source) then
                        for s in FailwithContext.find c.Tree c.Source c.Check -> "FR0092", s.Range

                    for s in ExceptionDetail.find c.Tree c.Source c.Check -> "FR0151", s.Range
                    for s in CachedFailure.find c.Tree c.Source c.Check -> "FR0152", s.Range
                    for s in CheckedArithmetic.find c.Tree c.Source -> "FR0105", s.Range
                    for s in DateTimeRules.find c.Tree c.Source c.Check -> "FR0121", s.Range
                    for s in MonitorLock.find c.Tree c.Source c.Check -> "FR0123", s.Range
                    for s in MonitorLock.findLeaks c.Tree c.Source c.Check -> "FR0123", s.Range
                    for s in WeakLock.find c.Tree c.Source c.Check -> "FR0046", s.Range
                    for s in SwallowedException.findParseControlFlow c.Tree c.Source -> "FR0055", s.Range
                    for s in IntDivisionToFloat.find c.Tree c.Source c.Check -> "FR0159", s.Range
                    for s in LostInnerException.find c.Tree c.Source c.Check -> "FR0160", s.Range
                    for s in LazyInit.find c.Tree c.Source -> "FR0162", s.Range
                    for s in DroppedTimer.find c.Tree c.Source c.Check -> "FR0163", s.Range
                    for s in DateTimeKindMix.find c.Tree c.Source c.Check -> "FR0165", s.Range
                ]
    }
