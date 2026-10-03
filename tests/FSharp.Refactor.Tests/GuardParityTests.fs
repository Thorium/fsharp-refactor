/// The newer rules against the guards the older ones keep: compiler
/// directives, comments, and the shapes of one defect beyond its first
/// spelling.
module FSharp.Refactor.Tests.GuardParityTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private checkedSource (source: string) = parseAndCheck source

// ---- compiler directives: the parse tree shows one branch ----

[<Fact>]
let ``FR0177: a chain written across an #if is left alone`` () =
    let source =
        fsharp
            """
            module M
            let a (x: int) =
                x <> 1
                ||
            #if OTHER
                  x <> 3
            #else
                  x <> 2
            #endif
            """

    let tree, text, check = checkedSource source
    Assert.Empty(ConstantComparison.find tree text check)

[<Fact>]
let ``FR0178: a branch written across an #if is left alone`` () =
    let source =
        fsharp
            """
            module M
            let a (x: int option) =
                if x.IsNone then
            #if OTHER
                    0
            #else
                    x.Value
            #endif
                else
                    1
            """

    let tree, text, check = checkedSource source
    Assert.Empty(EmptyOptionValue.find tree text check)

[<Fact>]
let ``FR0181: a handler list written across an #if is left alone`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading.Tasks
            let a (work: Task) =
                try
                    work.Wait()
                with
            #if OTHER
                | :? AggregateException -> ()
            #endif
                | :? InvalidOperationException -> ()
            """

    let tree, text, check = checkedSource source
    Assert.Empty(WrappedCatch.find tree text check)

[<Fact>]
let ``FR0176: a constructor written across an #if is noted without a fix`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (now: DateTime) =
                DateTime(
                    now.Year,
            #if OTHER
                    now.Month,
            #else
                    now.AddMonths(-1).Month,
            #endif
                    25)
            """

    let tree, text, check = checkedSource source

    match DateParts.find tree text check with
    | [ s ] -> Assert.True s.Fix.IsNone
    | other -> failwithf "Expected one note, got %A" other

// ---- one defect, more than one spelling ----

[<Fact>]
let ``FR0178: a short-circuit test, a None arm and Option.get read the empty option too`` () =
    let source =
        fsharp
            """
            module M
            let a (x: int option) = x.IsNone && x.Value > 1
            let b (x: int option) = x.IsSome || x.Value > 1
            let c (x: int option) =
                match x with
                | Some v -> v
                | None -> x.Value
            let d (x: int option) = if x.IsNone then Option.get x else 0
            let e (x: int voption) =
                match x with
                | ValueNone -> x.Value
                | ValueSome v -> v
            """

    let tree, text, check = checkedSource source

    match EmptyOptionValue.find tree text check with
    | [ a; b; c; d; e ] ->
        Assert.Equal("x.IsNone", a.Test)
        Assert.Equal("x.IsSome", b.Test)
        Assert.Equal("x", c.Test)
        Assert.Equal("x.IsNone", d.Test)
        Assert.Equal("x", e.Test)
    | other -> failwithf "Expected five findings, got %A" other

[<Fact>]
let ``FR0178: the sound short-circuit, a Some arm and a guarded None arm stay quiet`` () =
    let source =
        fsharp
            """
            module M
            let a (x: int option) = x.IsSome && x.Value > 1
            let b (x: int option) = x.IsNone || x.Value > 1
            let c (x: int option) =
                match x with
                | Some _ -> x.Value
                | None -> 0
            let d (x: int option) (y: int option) =
                match x with
                | None -> y.Value
                | Some v -> v
            let e (x: int option) = if x.IsSome then Option.get x else 0
            """

    let tree, text, check = checkedSource source
    Assert.Empty(EmptyOptionValue.find tree text check)

[<Fact>]
let ``FR0179: an update bound to a wildcard is the same discard`` () =
    let source =
        fsharp
            """
            module M
            let a (index: Map<string, int>) =
                let _ = index.Add("k", 1)
                index
            let b (index: Map<string, int>) =
                let kept = index.Add("k", 1)
                kept
            let c (xs: int seq) =
                let _ = Set.ofSeq xs
                0
            """

    let tree, text, check = checkedSource source

    match DiscardedUpdate.find tree text check with
    | [ a ] -> Assert.Equal(("index.Add", "Map"), (a.CallName, a.Collection))
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0181: an F# exception pattern and Failure are handlers for the exception itself`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading.Tasks
            exception NotFound of string
            let a (work: Task) =
                try
                    work.Wait()
                    ""
                with
                | NotFound name -> name
            let b (work: Task<int>) =
                try
                    work.Result
                with
                | Failure message -> message.Length
            let c (compute: unit -> int) =
                try
                    compute ()
                with
                | NotFound _ -> 0
            """

    let tree, text, check = checkedSource source

    match WrappedCatch.find tree text check with
    | [ a; b ] ->
        Assert.Equal("NotFound", a.TypeText)
        Assert.Equal("Failure", b.TypeText)
        Assert.True(a.InnerOffer.IsNone && b.InnerOffer.IsNone)
    | other -> failwithf "Expected two findings, got %A" other

// ---- FR0049: a task read behind its own bounded wait ----

[<Fact>]
let ``FR0049: a read behind WaitAny over that one task drains a finished task`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading.Tasks
            let within (timeout: TimeSpan) (work: Async<int>) =
                let task = Async.StartAsTask work
                if Task.WaitAny([| (task :> Task) |], timeout) < 0 then
                    raise (TimeoutException())
                else
                    task.GetAwaiter().GetResult()
            let within2 (timeout: TimeSpan) (task: Task<int>) =
                if Task.WaitAny([| task :> Task |], timeout) >= 0 then task.Result else -1
            """

    let tree, text, check = checkedSource source

    // the reads, not the waits in front of them
    Assert.Empty(
        SyncOverAsync.find tree text check
        |> List.filter (fun s -> (text.GetLineString(s.Range.StartLine - 1)).Contains "Result")
    )

[<Fact>]
let ``FR0049: the wrong branch, two tasks in the wait, and no wait at all still block`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading.Tasks
            let a (timeout: TimeSpan) (task: Task<int>) =
                if Task.WaitAny([| task :> Task |], timeout) < 0 then task.Result else -1
            let b (timeout: TimeSpan) (task: Task<int>) (other: Task) =
                if Task.WaitAny([| task :> Task; other |], timeout) >= 0 then task.Result else -1
            let c (task: Task<int>) = task.GetAwaiter().GetResult()
            """

    let tree, text, check = checkedSource source

    let reads =
        SyncOverAsync.find tree text check
        |> List.filter (fun s -> (text.GetLineString(s.Range.StartLine - 1)).Contains "Result")

    Assert.Equal(3, reads.Length)
