/// FR0017 AsyncIgnore, FR0149 UnhandledStart, FR0029 TaskStateMachine,
/// FR0049 SyncOverAsync (with the taskify fix), FR0079 SingleAwaitable,
/// FR0142 TestReturnsTask, FR0118 CancellationOverload, FR0119
/// AwaitableOverload, FR0075 UseBinding, FR0150 EscapingUse: the async and
/// task computation rules.
///
/// FR0142 trusts a test attribute only when its declaring entity lives
/// under `Xunit.`, `NUnit.Framework.` or MSTest's namespace, which a
/// script cannot declare; the harness's stub file (Typed.stubs) declares
/// `Xunit.FactAttribute` ahead of the script for it.
///
/// Where the CLI keeps a finding advisory but the editor offers its fix
/// (FR0149's handler move, FR0079's single element, FR0150's move
/// inside), the fix is taken as an edit set: the fix exists and the
/// properties should hold it to the same standard.
module FSharp.Refactor.PropertyTests.Families.Async

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

/// n `let! xk = Task.FromResult k` lines at the given indent: eight of
/// them cross FR0029's size gate.
let private awaits (indent: string) (n: int) =
    [ for k in 1..n -> $"{indent}let! x{k} = Task.FromResult {k}" ]
    |> String.concat "\n"

let private shapes =
    [
        // FR0142: a test that drains an Async or a Task becomes a task-returning test
        withFree
            "BlockingTest"
            [ "FR0142" ]
            (Gen.zip
                genSmall
                (Gen.elements [ "let res = load () |> Async.RunSynchronously"; "let res = (fetch ()).Result" ]))
            (fun (n, drain) i ->
                $"module T{i} =\n    let load () = async {{ return {n} }}\n    let fetch () = Task.FromResult {n}\n\n    [<Xunit.Fact>]\n    let ``reads {i}`` () =\n        {drain}\n        if res <> {n} then failwith \"wrong\"")
        // FR0017: an Async value handed to ignore never runs
        withFree "AsyncIgnored" [ "FR0017" ] (Gen.elements [ "comp |> ignore"; "ignore comp" ]) (fun form i ->
            $"let f{i} (comp: Async<int>) = {form}")
        // FR0017: a fully applied call whose result is an Async
        withFree "AsyncCallIgnored" [ "FR0017" ] genSmall (fun n i ->
            $"let f{i} () =\n    let make (k: int) = async {{ return k + {n} }}\n    make {n} |> ignore")
        // FR0017: a ValueTask discarded is consumed by nobody
        fixed' "ValueTaskIgnored" [ "FR0017" ] (fun i -> $"let f{i} (vt: ValueTask<int>) = vt |> ignore")
        // FR0149: a started computation with no handler
        withFree "UnhandledStart" [ "FR0149" ] genWord (fun w i ->
            $"let f{i} () =\n    async {{\n        do! Async.Sleep 10\n        printfn \"{w}\"\n    }}\n    |> Async.Start")
        // FR0149: a looping body, where the handler's place is the author's choice
        withFree "UnhandledStartLoop" [ "FR0149" ] genSmall (fun n i ->
            $"let f{i} () =\n    async {{\n        while true do\n            do! Async.Sleep {n}\n    }}\n    |> Async.Start")
        // FR0149: a try around the start alone, whose handler moves inside
        withFree "UnhandledStartTry" [ "FR0149" ] genWord (fun w i ->
            $"let f{i} () =\n    try\n        async {{\n            do! Async.Sleep 10\n            printfn \"{w}\"\n        }}\n        |> Async.Start\n    with e ->\n        printfn \"%%s\" e.Message")
        // FR0149: StartImmediate with a token, the tupled form
        withFree "UnhandledStartImmediate" [ "FR0149" ] genSmall (fun n i ->
            $"let f{i} (token: CancellationToken) =\n    Async.StartImmediate(\n        async {{\n            do! Async.Sleep {n}\n            ()\n        }},\n        token\n    )")
        // FR0029: a let rec in the resumable body is a definite FS3511
        withFree "TaskLetRec" [ "FR0029" ] genSmall (fun n i ->
            $"let f{i} () = task {{\n    let rec loop (n: int) = if n = 0 then 0 else loop (n - 1)\n    let! c = Task.FromResult {n}\n    return loop c\n}}")
        // FR0029: leading plain lets of an oversized task hoist above the builder
        withFree "TaskHoistLets" [ "FR0029" ] genSmall (fun n i ->
            $"let f{i} () =\n    task {{\n        let a = {n}\n        let b = a * 2\n"
            + awaits "        " 8
            + "\n        return a + b + x1\n    }")
        // FR0029: every arm returns, so one return goes in front of the match
        withFree "TaskReturnHoist" [ "FR0029" ] genSmall (fun n i ->
            $"let f{i} (c: int) =\n    task {{\n        let! x = Task.FromResult {n}\n\n        match c with\n        | 1 -> return x\n        | _ -> return -1\n    }}")
        // FR0029: both arms await, so each becomes its own task; the fix
        // needs the builder on its own line, the same-line layout is advice
        withFree "TaskSplitBranches" [ "FR0029" ] (Gen.elements [ true; false ]) (fun ownLine i ->
            let head, indent =
                if ownLine then
                    $"let f{i} (cond: bool) =\n    task {{\n", "        "
                else
                    $"let f{i} (cond: bool) = task {{\n", "    "

            head
            + $"{indent}if cond then\n"
            + awaits (indent + "    ") 4
            + $"\n{indent}    return x1\n{indent}else\n"
            + awaits (indent + "    ") 4
            + $"\n{indent}    return x2\n"
            + (if ownLine then "    }" else "}"))
        // FR0029: forty non-awaiting lines after the last await extract
        fixed' "TaskLongTail" [ "FR0029" ] (fun i ->
            let tail =
                [
                    for k in 1..40 -> $"        let s{k} = " + (if k = 1 then "x1" else $"s{k - 1}") + " + 1"
                ]
                |> String.concat "\n"

            $"let f{i} () =\n    task {{\n"
            + awaits "        " 8
            + "\n"
            + tail
            + "\n        return s40\n    }")
        // FR0049: Thread.Sleep in statement position of an async
        withFree "SleepInAsync" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} () = async {{\n    Thread.Sleep {n}\n    return {n}\n}}")
        // FR0049: the same inside a task
        withFree "SleepInTask" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} () = task {{\n    Thread.Sleep {n}\n    return {n}\n}}")
        // FR0049: a `let x = t.Result` on the spine becomes a let!
        withFree "ResultLetInTask" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} (t: Task<int>) = task {{\n    let x = t.Result\n    return x + {n}\n}}")
        // FR0049: a statement-position Wait becomes do!
        fixed' "WaitInTask" [ "FR0049" ] (fun i -> $"let f{i} (t: Task) = task {{\n    t.Wait()\n    return 1\n}}")
        // FR0049: .Result inside an expression is advice
        withFree "ResultInReturn" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} (t: Task<int>) = task {{ return t.Result + {n} }}")
        // FR0049: RunSynchronously inside a task, in an expression (advice)
        fixed' "RunSynchronouslyInTask" [ "FR0049" ] (fun i ->
            $"let f{i} (comp: Async<int>) = task {{ return (comp |> Async.RunSynchronously) }}")
        // FR0049: bound on the spine, the task builder binds the Async directly
        withFree "RunSynchronouslyLet" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} (comp: Async<int>) = task {{\n    let x = Async.RunSynchronously comp\n    return x + {n}\n}}")
        // FR0049: Task.Run around a RunSynchronously is Async.StartAsTask
        fixed' "RunSynchronouslyInTaskRun" [ "FR0049" ] (fun i ->
            $"let f{i} (comp: Async<int>) = task {{\n    let! x = Task.Run(fun () -> comp |> Async.RunSynchronously)\n    return x\n}}")
        // FR0049: .Result on a ContinueWith antecedent becomes a bind
        withFree "AntecedentResult" [ "FR0049" ] genSmall (fun n i ->
            $"let f{i} (t: Task<int>) =\n    t.ContinueWith(fun (a: Task<int>) -> a.Result + {n})")
        // FR0049: GetResult is an antipattern outside any CE too
        fixed' "BoundaryGetResult" [ "FR0049" ] (fun i -> $"let f{i} (t: Task<int>) = t.GetAwaiter().GetResult()")
        // FR0049: a primitive's blocking wait inside a task
        fixed' "SemaphoreWaitInTask" [ "FR0049" ] (fun i ->
            $"let f{i} (gate: SemaphoreSlim) = task {{\n    gate.Wait()\n    return 1\n}}")
        // FR0049 taskify: a file-private drain and its one caller inside a
        // task; the fix rewrites both, so the shape holds both declarations
        withFree "Taskify" [ "FR0049" ] genSmall (fun n i ->
            $"let private fetch{i} (x: int) =\n    let t = Task.Run(fun () -> x)\n    t.GetAwaiter().GetResult()\n\nlet consume{i} () = task {{\n    let s = fetch{i} {n}\n    return s\n}}")
        // FR0079: WhenAll, WaitAll and Parallel over one element
        fixed' "WhenAllSingle" [ "FR0079" ] (fun i -> $"let f{i} (t: Task<int>) = Task.WhenAll [| t |]")
        fixed' "ParallelSingle" [ "FR0079" ] (fun i -> $"let f{i} (c: Async<int>) = Async.Parallel [ c ]")
        fixed' "WaitAllSingle" [ "FR0079" ] (fun i -> $"let f{i} (t: Task) = Task.WaitAll [| t |]")
        // FR0118: the in-scope token is omitted from a call that takes one
        withFree "TokenOmitted" [ "FR0118" ] genSmall (fun n i ->
            $"let f{i} (ct: CancellationToken) = task {{\n    do! Task.Delay({n})\n    return {n}\n}}")
        // FR0118: CancellationToken.None cuts the chain
        withFree "TokenNone" [ "FR0118" ] genSmall (fun n i ->
            $"let f{i} (ct: CancellationToken) = task {{\n    do! Task.Delay({n}, CancellationToken.None)\n    return {n}\n}}")
        // FR0118: a loop under the token that never observes it
        withFree "TokenUnobservedLoop" [ "FR0118" ] genSmall (fun n i ->
            $"let f{i} (ct: CancellationToken) (next: unit -> Task<int>) = task {{\n    let mutable total = 0\n    while total < {n + 1} do\n        let! v = next ()\n        total <- total + v\n    return total\n}}")
        // FR0118 must stay quiet: the loop steps a local built with the token
        withFree "TokenObservedThroughLocal" [ "!FR0118" ] genSmall (fun n i ->
            $"let f{i} (ct: CancellationToken) = task {{\n    let step () = Task.Delay({n + 1}, ct)\n    let mutable i = 0\n    while i < {n + 1} do\n        do! step ()\n        i <- i + 1\n    return i\n}}")
        // FR0119: a blocking read bound on the spine of a task
        fixed' "ReadLineInTask" [ "FR0119" ] (fun i ->
            $"let f{i} (reader: TextReader) = task {{\n    let line = reader.ReadLine()\n    return line\n}}")
        // FR0119: a blocking statement, parenthesised or juxtaposed
        withFree "WriteInTask" [ "FR0119" ] (Gen.elements [ "writer.Write(s)"; "writer.Write s" ]) (fun call i ->
            $"let f{i} (writer: TextWriter) (s: string) = task {{\n    {call}\n    return 1\n}}")
        // FR0119: inside async the twin bridges through Async.AwaitTask
        fixed' "ReadLineInAsync" [ "FR0119" ] (fun i ->
            $"let f{i} (reader: TextReader) = async {{\n    let line = reader.ReadLine()\n    return line\n}}")
        // FR0075: a local disposable nothing disposes, consumed in the scope
        withFree "LocalDisposable" [ "FR0075" ] genSmall (fun n i ->
            $"let f{i} (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    b + {n}")
        // FR0075: handed to a function, so the owner is the author's call
        fixed' "DisposableHandedOff" [ "FR0075" ] (fun i ->
            $"let f{i} (sink: FileStream -> unit) (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    sink stream")
        // FR0150: a use read by the task the scope hands back
        withFree "EscapingUse" [ "FR0150" ] genSmall (fun n i ->
            $"let f{i} () =\n    use cts = new CancellationTokenSource()\n\n    task {{\n        do! Task.Delay({n}, cts.Token)\n        return {n}\n    }}")
        // FR0150: the async twin of the same shape
        withFree "EscapingUseAsync" [ "FR0150" ] genSmall (fun n i ->
            $"let f{i} () =\n    use cts = new CancellationTokenSource()\n\n    async {{\n        do! Async.Sleep {n}\n        return cts.Token.IsCancellationRequested\n    }}")
        // FR0150: a statement between the use and the computation reads the
        // binder, so the move is withheld and the finding stays a note
        withFree "EscapingUseHeld" [ "FR0150" ] genSmall (fun n i ->
            $"let f{i} () =\n    use cts = new CancellationTokenSource()\n    let token = cts.Token\n\n    task {{\n        do! Task.Delay({n}, cts.Token)\n        return token.IsCancellationRequested\n    }}")
    ]

let private edits (code: string) (es: (FSharp.Compiler.Text.range * string * string) list) =
    [ for r, _, t in es -> edit code r t ]

let family: Family =
    {
        Name = "Async"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in AsyncIgnore.findUnhandledStart c.Tree c.Source c.Check do
                        match s.TryFix with
                        | Some(r, _, t) -> yield "FR0149", [ edit "FR0149" r t ]
                        | None -> ()
                    for s in TaskStateMachine.find c.Tree c.Source (Some c.Check) 40 false Set.empty do
                        if not s.Edits.IsEmpty then
                            yield "FR0029", [ for r, t in s.Edits -> edit "FR0029" r t ]
                    for s in SyncOverAsync.findWith true c.Tree c.Source c.Check do
                        if not s.Fixes.IsEmpty then
                            yield "FR0049", edits "FR0049" s.Fixes
                    for s in Taskify.find c.Tree c.Source c.Check None -> "FR0049", edits "FR0049" s.Edits
                    for s in SingleAwaitable.find c.Tree c.Source c.Check do
                        match s.Fix with
                        | Some(r, _, t) -> yield "FR0079", [ edit "FR0079" r t ]
                        | None -> ()
                    for s in TestReturnsTask.find c.Tree c.Source c.Check ->
                        "FR0142", [ edit "FR0142" s.Range s.ReplacementText ]
                    for s in CancellationOverload.find c.Tree c.Source c.Check ->
                        "FR0118", [ edit "FR0118" s.Range s.Replacement ]
                    for s in AwaitableOverload.find c.Tree c.Source c.Check -> "FR0119", edits "FR0119" s.Fixes
                    for s in UseBinding.find c.Tree c.Source c.Check do
                        match s.Fix with
                        | Some(_, replacement) -> yield "FR0075", [ edit "FR0075" s.Range replacement ]
                        | None -> ()
                    for s in UseBinding.findEscapingUse c.Tree c.Source c.Check do
                        if not s.Edits.IsEmpty then
                            yield "FR0150", edits "FR0150" s.Edits
                ]
        Notes =
            fun c ->
                [
                    for s in AsyncIgnore.find c.Tree c.Source c.Check -> "FR0017", s.Range
                    for s in CancellationOverload.findUnobservedLoops c.Tree c.Source c.Check -> "FR0118", s.Range
                    for s in AsyncIgnore.findUnhandledStart c.Tree c.Source c.Check do
                        if s.TryFix.IsNone then
                            yield "FR0149", s.Range
                    for s in TaskStateMachine.find c.Tree c.Source (Some c.Check) 40 false Set.empty do
                        if s.Edits.IsEmpty then
                            yield "FR0029", s.Range
                    for s in SyncOverAsync.findWith true c.Tree c.Source c.Check do
                        if s.Fixes.IsEmpty then
                            yield "FR0049", s.Range
                    for s in SingleAwaitable.find c.Tree c.Source c.Check do
                        if s.Fix.IsNone then
                            yield "FR0079", s.Range
                    for s in UseBinding.find c.Tree c.Source c.Check do
                        if s.Fix.IsNone then
                            yield "FR0075", s.Range
                    for s in UseBinding.findEscapingUse c.Tree c.Source c.Check do
                        if s.Edits.IsEmpty then
                            yield "FR0150", s.Range
                ]
    }
