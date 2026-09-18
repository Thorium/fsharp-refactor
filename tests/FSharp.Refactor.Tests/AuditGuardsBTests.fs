/// Audit guards, round B: five stand-downs of 0.8.23 narrowed back to the
/// condition the typed tree can prove, so every legitimate rewrite the
/// rule used to deliver comes back. FR0012's untyped name gate stands down
/// only inside a computation expression (where a custom operation can
/// live); FR0075 treats a CancellationTokenSource whose token goes
/// anywhere the scope does not see finish - a call, a constructor, a
/// field - as in flight, and keeps the fix for a token an awaited BCL
/// call observes; FR0029 hoists a `let` that may throw out of a task only
/// where the task VALUE stays with callers in reach, and reads a dotted
/// path as throwing unless the typed tree shows a field or a plain value;
/// FR0049 stands down on a parenthesised tail that hides a blocking site
/// rather than `let!`-binding it under `return (`; FR0012's map fusion
/// counts a user property, an extension property, `Lazy.Value` and an
/// interpolation hole as calls. Each item has its repro and the positive
/// shape beside it.
module FSharp.Refactor.Tests.AuditGuardsBTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private lines (xs: string list) = String.concat "\n" xs

let private assertTypechecks (source: string) =
    Assert.True(typechecksCleanly source, $"Fixture does not typecheck:\n%s{source}")

// ---- 1: FR0012 HintEngine, the untyped name gate ----

let private hintsTyped (source: string) =
    let tree, sourceText, check = parseAndCheck source
    HintEngine.find [] tree sourceText (Some check)

let private hintsUntyped (source: string) =
    let tree, sourceText = parse source
    HintEngine.find [] tree sourceText None

[<Fact>]
let ``FR0012: without a typed check a built-in hint fires outside a computation expression`` () =
    // the parse-only path used to stand every core-named hint down; a
    // custom operation is the one shape that fooled it, and it lives only
    // in a builder's body
    match hintsUntyped "module Test\nlet f (x: string) = x = null" with
    | [ s ] -> Assert.Equal("isNull x", s.ReplacementText)
    | other -> failwithf "Expected one null-comparison hint, got %A" other

    match hintsUntyped "module Test\nlet f (x: int) = id x" with
    | [ s ] -> Assert.Equal("x", s.ReplacementText)
    | other -> failwithf "Expected one id hint, got %A" other

[<Fact>]
let ``FR0012: without a typed check a core-named hint stands down inside a computation expression`` () =
    // FsCDK's `lifecycleRule { id "rule" }`: the builder's custom operation
    // matched `id x ===> x` by shape
    Assert.Empty(
        hintsUntyped (
            lines
                [
                    "module Test"
                    "type LifecycleBuilder() ="
                    "    member _.Yield(_: unit) = \"\""
                    "    [<CustomOperation(\"id\")>]"
                    "    member _.Id(_: string, name: string) = name"
                    "let lifecycleRule = LifecycleBuilder()"
                    "let rule = lifecycleRule { id \"rule\" }"
                ]
        )
    )

    // the same spelling of FSharp.Core's own `id` inside an async: the
    // untyped path cannot tell the two apart and stands down there ...
    let source = "module Test\nlet g (x: int) = async { return id x }"
    Assert.Empty(hintsUntyped source)

    // ... and the typed path proves it and fires
    match hintsTyped source with
    | [ s ] -> Assert.Equal("x", s.ReplacementText)
    | other -> failwithf "Expected one id hint, got %A" other

// ---- 2: FR0075 UseBinding, a token handed on ----

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

[<Fact>]
let ``FR0075: a CancellationTokenSource whose token a user function receives is advisory only`` () =
    // welendus: `requestNewLoan` hands the token to `Async.Start` for a
    // background search that outlives the scope; `use token` disposed the
    // source under it
    let source =
        lines
            [
                "module Test"
                "open System.Threading"
                "module Loans ="
                "    let requestNewLoan (amount: int) (ct: CancellationToken) (flag: bool) : Async<int> ="
                "        async {"
                "            Async.Start(async { do! Async.Sleep 10 }, ct)"
                "            return amount"
                "        }"
                "let run () ="
                "    async {"
                "        let token = new CancellationTokenSource()"
                "        token.CancelAfter 3300000"
                "        match! Loans.requestNewLoan 100 token.Token false with"
                "        | 0 -> return \"none\""
                "        | n -> return string n"
                "    }"
            ]

    assertTypechecks source

    match useBindingsIn source with
    | [ s ] ->
        Assert.Equal("token", s.Name)
        Assert.True(s.Fix.IsNone, $"Expected an advisory, got a fix: %A{s}")
        Assert.Equal(Some(UseBinding.Destination.TokenHanded "requestNewLoan"), s.Destination)
    | other -> failwithf "Expected one advisory for 'token', got %A" other

[<Fact>]
let ``FR0075: a token handed to Async.Start or to an unawaited BCL task is advisory only`` () =
    let source =
        lines
            [
                "module Test"
                "open System.Threading"
                "open System.Threading.Tasks"
                "let work = async { do! Async.Sleep 10 }"
                "let run () ="
                "    let cts = new CancellationTokenSource()"
                "    Async.Start(work, cts.Token)"
                "    1"
                "let run2 () ="
                "    let cts = new CancellationTokenSource()"
                "    Task.Delay(10, cts.Token) |> ignore"
                "    1"
            ]

    assertTypechecks source

    match useBindingsIn source |> List.sortBy (fun s -> s.Range.StartLine) with
    | [ a; b ] ->
        Assert.True(a.Fix.IsNone && b.Fix.IsNone, sprintf "Expected two advisories, got %A" [ a; b ])
        Assert.Equal(Some(UseBinding.Destination.TokenHanded "Start"), a.Destination)
        Assert.Equal(Some(UseBinding.Destination.TokenHanded "Delay"), b.Destination)
    | other -> failwithf "Expected two advisories for 'cts', got %A" other

[<Fact>]
let ``FR0075: a token an awaited BCL call observes keeps the fix`` () =
    // Task.Delay and HttpClient.GetAsync observe the token while they
    // run and start nothing of their own once awaited: the scope sees
    // them finish, and `use` is right
    let source =
        lines
            [
                "module Test"
                "open System.Threading"
                "open System.Threading.Tasks"
                "let run () ="
                "    task {"
                "        let cts = new CancellationTokenSource()"
                "        cts.CancelAfter 1000"
                "        do! Task.Delay(10, cts.Token)"
                "        let! n = Task.Run((fun () -> 1), cts.Token)"
                "        return n"
                "    }"
                "let sync () ="
                "    let cts = new CancellationTokenSource()"
                "    Task.Delay(10, cts.Token).Wait()"
                "    Task.Delay(10, cts.Token) |> Async.AwaitTask |> Async.RunSynchronously"
                "    1"
            ]

    assertTypechecks source

    match useBindingsIn source |> List.sortBy (fun s -> s.Range.StartLine) with
    | [ a; b ] ->
        Assert.True(Some("let", "use") = a.Fix, $"Expected a fix for the task's 'cts', got %A{a}")
        Assert.True(Some("let", "use") = b.Fix, $"Expected a fix for the sync 'cts', got %A{b}")
        let patched = applyEdit (applyEdit source b.Range "use") a.Range "use"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two use-binding fixes for 'cts', got %A" other

[<Fact>]
let ``FR0075: a token handed to a constructor or stored in a collection is advisory only`` () =
    // the worker's timer runs on the token after the scope has returned;
    // `use cts` disposed the source under it
    let constructed =
        lines
            [
                "module Test"
                "open System.Threading"
                "open System.Threading.Tasks"
                "type Worker(ct: CancellationToken) ="
                "    member _.Start() = Task.Delay(5000, ct) |> ignore"
                "let run () ="
                "    let cts = new CancellationTokenSource()"
                "    cts.CancelAfter 5000"
                "    let w = new Worker(cts.Token)"
                "    w.Start()"
                "    1"
            ]

    assertTypechecks constructed

    match useBindingsIn constructed with
    | [ s ] ->
        Assert.Equal("cts", s.Name)
        Assert.True(s.Fix.IsNone, $"Expected an advisory, got a fix: %A{s}")
        Assert.Equal(Some(UseBinding.Destination.TokenHanded "Worker"), s.Destination)
    | other -> failwithf "Expected one advisory for 'cts', got %A" other

    // a synchronous BCL call that is no blocking wait may store the token
    let stored =
        lines
            [
                "module Test"
                "open System.Threading"
                "let tokens = ResizeArray<CancellationToken>()"
                "let run () ="
                "    let cts = new CancellationTokenSource()"
                "    tokens.Add(cts.Token)"
                "    1"
            ]

    assertTypechecks stored

    match useBindingsIn stored with
    | [ s ] ->
        Assert.True(s.Fix.IsNone, $"Expected an advisory, got a fix: %A{s}")
        Assert.Equal(Some(UseBinding.Destination.TokenHanded "Add"), s.Destination)
    | other -> failwithf "Expected one advisory for 'cts', got %A" other

// ---- 3: FR0029 TaskStateMachine, hoisting out of an exposed task ----

/// n `let! xi = Task.FromResult i` lines at `indent`, enough to cross
/// the size gate.
let private awaits (indent: int) n =
    let pad = String.replicate indent " "

    [
        for i in 1..n -> $"{pad}let! x%d{i} = System.Threading.Tasks.Task.FromResult %d{i}"
    ]
    |> String.concat "\n"

let private hoistsIn (source: string) =
    let tree, sourceText = parse source

    TaskStateMachine.find tree sourceText None 4 false Set.empty
    |> List.choose (fun s ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.HoistPlainLets n -> Some(n, s.Edits)
        | _ -> None)

let private hoistsInTyped (source: string) =
    let tree, sourceText, check = parseAndCheck source

    TaskStateMachine.find tree sourceText (Some check) 4 false Set.empty
    |> List.choose (fun s ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.HoistPlainLets n -> Some(n, s.Edits)
        | _ -> None)

let private computeAndService =
    [
        "module Test"
        "open System.Threading.Tasks"
        "type ISvc ="
        "    abstract Run: int -> Task<int>"
        "let compute (x: int) = if x = 0 then failwith \"x\" else x"
    ]

[<Fact>]
let ``FR0029: a let that may throw stays inside an interface member's task`` () =
    // SQLProvider's ExecuteSprocCommandAsync: hoisted, the
    // IndexOutOfRangeException escaped synchronously past the caller's
    // Async.Catch, where the faulted Task had been caught
    let source =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    interface ISvc with"
                "        member _.Run (x: int) ="
                "            task {"
                "                let a = compute x"
                "                let b = a * 2"
                awaits 16 8
                "                return a + b + x1"
                "            }"
            ]
        )

    Assert.Empty(hoistsIn source)

    // a public member and a public function: the same callers out of reach
    let publicMember =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    member _.Run (x: int) ="
                "        task {"
                "            let a = compute x"
                awaits 12 8
                "            return a + x1"
                "        }"
            ]
        )

    Assert.Empty(hoistsIn publicMember)

    let publicFunction =
        lines (
            computeAndService
            @ [
                "let run (x: int) ="
                "    task {"
                "        let a = compute x"
                awaits 8 8
                "        return a + x1"
                "    }"
            ]
        )

    Assert.Empty(hoistsIn publicFunction)

[<Fact>]
let ``FR0029: a private helper still hoists a let that may throw`` () =
    let source =
        lines (
            computeAndService
            @ [
                "let private run (x: int) ="
                "    task {"
                "        let a = compute x"
                awaits 8 8
                "        return a + x1"
                "    }"
            ]
        )

    match hoistsIn source with
    | [ (1, edits) ] ->
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("let a = compute x", moved)
    | other -> failwithf "Expected one hoist of one let, got %A" other

    // a class's own let whose task only a private member hands on, and a
    // member marked private
    let classLet =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    let run (x: int) ="
                "        task {"
                "            let a = compute x"
                awaits 12 8
                "            return a + x1"
                "        }"
                "    member private _.Go x = run x"
            ]
        )

    match hoistsIn classLet with
    | [ (1, _) ] -> ()
    | other -> failwithf "Expected one hoist under the class let, got %A" other

    let privateMember =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    member private _.Run (x: int) ="
                "        task {"
                "            let a = compute x"
                awaits 12 8
                "            return a + x1"
                "        }"
            ]
        )

    match hoistsIn privateMember with
    | [ (1, _) ] -> ()
    | other -> failwithf "Expected one hoist under the private member, got %A" other

[<Fact>]
let ``FR0029: a confined binding whose task a public member hands out is exposed`` () =
    // `run` is a class let, and `svc.Go 0` is public: every caller of Go
    // gets the task, and hoisted, the throw comes synchronously
    let classLet =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    let run (x: int) ="
                "        task {"
                "            let a = compute x"
                awaits 12 8
                "            return a + x1"
                "        }"
                "    member _.Go x = run x"
            ]
        )

    Assert.Empty(hoistsIn classLet)

    // through another confined binding that a public member mentions
    let twoHops =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    let run (x: int) ="
                "        task {"
                "            let a = compute x"
                awaits 12 8
                "            return a + x1"
                "        }"
                "    let go (x: int) = run x"
                "    member _.Go x = go x"
            ]
        )

    Assert.Empty(hoistsIn twoHops)

    // a private function a public one returns
    let privateFunction =
        lines (
            computeAndService
            @ [
                "let private run (x: int) ="
                "    task {"
                "        let a = compute x"
                awaits 8 8
                "        return a + x1"
                "    }"
                "let go (x: int) = run x"
            ]
        )

    Assert.Empty(hoistsIn privateFunction)

    // mentioned by a private function alone, the callers stay in reach
    let privateChain =
        lines (
            computeAndService
            @ [
                "let private run (x: int) ="
                "    task {"
                "        let a = compute x"
                awaits 8 8
                "        return a + x1"
                "    }"
                "let private go (x: int) = run x"
            ]
        )

    match hoistsIn privateChain with
    | [ (1, _) ] -> ()
    | other -> failwithf "Expected one hoist under the private chain, got %A" other

[<Fact>]
let ``FR0029: a property read may throw where a record field cannot`` () =
    // `opt.Value` throws on None; a field read is a load. Both are dotted
    // names the untyped path once waved through together
    let fixture (binding: string) =
        lines (
            computeAndService
            @ [
                "type R = { Field: int }"
                "let opt: int option = Some 1"
                "let record = { Field = 1 }"
                "type Svc() ="
                "    interface ISvc with"
                "        member _.Run (x: int) ="
                "            task {"
                "                " + binding
                awaits 16 8
                "                return v + x + x1"
                "            }"
            ]
        )

    let viaProperty = fixture "let v = opt.Value"
    assertTypechecks viaProperty
    Assert.Empty(hoistsInTyped viaProperty)

    let viaField = fixture "let v = record.Field"
    assertTypechecks viaField

    match hoistsInTyped viaField with
    | [ (1, edits) ] ->
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("let v = record.Field", moved)
    | other -> failwithf "Expected one hoist of the field read, got %A" other

    // without the typed tree a dotted name is unproven
    Assert.Empty(hoistsIn viaField)

[<Fact>]
let ``FR0029: an exposed task hoists the lets that cannot throw and stops at the first that can`` () =
    let source =
        lines (
            computeAndService
            @ [
                "let run (x: int) ="
                "    task {"
                "        let a = 1"
                "        let b = a * 2"
                "        let c = compute b"
                awaits 8 8
                "        return a + b + c + x1"
                "    }"
            ]
        )

    match hoistsIn source with
    | [ (2, edits) ] ->
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("let a = 1", moved)
        Assert.Contains("let b = a * 2", moved)
        Assert.DoesNotContain("compute b", moved)
    | other -> failwithf "Expected one hoist of two lets, got %A" other

    // with the typed tree an FSharp.Core call over atoms cannot throw
    // either, and the interface member hoists it
    let typed =
        lines (
            computeAndService
            @ [
                "type Svc() ="
                "    interface ISvc with"
                "        member _.Run (x: int) ="
                "            task {"
                "                let s = string x"
                "                let d = 4 / x"
                awaits 16 8
                "                return s.Length + d + x1"
                "            }"
            ]
        )

    assertTypechecks typed

    match hoistsInTyped typed with
    | [ (1, edits) ] ->
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("let s = string x", moved)
        Assert.DoesNotContain("4 / x", moved)
    | other -> failwithf "Expected one hoist of the string let alone, got %A" other

// ---- 4: FR0049 Taskify, a blocking site inside a parenthesised tail ----

let private taskifyIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Taskify.find tree sourceText checkResults None

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

[<Fact>]
let ``FR0049: a parenthesised tail hiding a blocking site stands the body down`` () =
    // `return (` in front of the parentheses and `let!` inside them —
    // `return (let! r = t in r + 1)` — does not parse
    let source =
        lines
            [
                "module Test"
                "open System.Threading.Tasks"
                "let private fetch (x: int) ="
                "    let t = Task.Run(fun () -> x)"
                "    (let r = t.GetAwaiter().GetResult() in r + 1)"
                "let consume () = task {"
                "    let s = fetch 1"
                "    return s"
                "}"
            ]

    assertTypechecks source
    Assert.Empty(taskifyIn source)

[<Fact>]
let ``FR0049: a parenthesised tail with no blocking site is still returned whole`` () =
    let source =
        lines
            [
                "module Test"
                "open System.Threading.Tasks"
                "let private fetch (x: int) ="
                "    let t = Task.Run(fun () -> x)"
                "    let r = t.GetAwaiter().GetResult()"
                "    (let q = r in q + 1)"
                "let consume () = task {"
                "    let s = fetch 1"
                "    return s"
                "}"
            ]

    match taskifyIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Contains("return (let q = r in q + 1)", patched)
        Assert.Contains("let! r = t", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one taskify suggestion, got %A" other

// ---- 5: FR0012 HintEngine, property reads and interpolation in a fused mapper ----

[<Fact>]
let ``FR0012: map fusion counts a user property, Lazy.Value and an interpolation hole as calls`` () =
    // a getter runs its body, `Lazy.Value` forces the thunk, and a hole is
    // formatted by the value's own ToString: each is observable when the
    // fused composition interleaves the two sweeps
    Assert.Empty(
        hintsTyped
            "module Test\nlet f (xs: Lazy<int> list) = List.map string (List.map (fun (l: Lazy<int>) -> l.Value) xs)"
    )

    Assert.Empty(
        hintsTyped (
            lines
                [
                    "module Test"
                    "type C() ="
                    "    member _.P = (printfn \"p\"; 1)"
                    "let f (cs: C list) = List.map string (List.map (fun (c: C) -> c.P) cs)"
                ]
        )
    )

    Assert.Empty(
        hintsTyped
            "module Test\nlet f (xs: int list) = List.map (fun (s: string) -> s.Length) (List.map (fun (x: int) -> $\"{x}\") xs)"
    )

[<Fact>]
let ``FR0012: map fusion counts an extension member on a BCL type as a call`` () =
    // System.String is the apparent owner of `Loud` and `Shout`; the bodies
    // are the user's
    let extensionProperty =
        lines
            [
                "module Test"
                "type System.String with"
                "    member s.Loud ="
                "        printfn \"!\""
                "        s.Length"
                "let f (xs: int list) = List.map (fun (s: string) -> s.Loud) (List.map string xs)"
            ]

    assertTypechecks extensionProperty
    Assert.Empty(hintsTyped extensionProperty)

    let extensionMethod =
        lines
            [
                "module Test"
                "type System.String with"
                "    member s.Shout() ="
                "        printfn \"!\""
                "        s.Length"
                "let f (xs: int list) = List.map (fun (s: string) -> s.Shout()) (List.map string xs)"
            ]

    assertTypechecks extensionMethod
    Assert.Empty(hintsTyped extensionMethod)

[<Fact>]
let ``FR0012: map fusion still fuses a BCL property read`` () =
    // `s.Length` is System.String's: a read, not a call
    match
        hintsTyped "module Test\nlet f (xs: int list) = List.map (fun (s: string) -> s.Length) (List.map string xs)"
    with
    | [ s ] -> Assert.Equal("List.map (string >> (fun (s: string) -> s.Length)) xs", s.ReplacementText)
    | other -> failwithf "Expected one fusion hint, got %A" other
