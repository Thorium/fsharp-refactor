module FSharp.Refactor.Tests.TaskStateMachineTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private adviceIn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText None 4 false Set.empty

/// The same, with the `hoistReturnOnAsync` knob turned on.
let private adviceInAsyncOn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText None 4 true Set.empty


/// n `let! xi = Task.FromResult i` lines, enough to cross the size gate.
let private awaits n =
    [
        for i in 1..n -> $"    let! x%d{i} = System.Threading.Tasks.Task.FromResult %d{i}"
    ]
    |> String.concat "\n"

[<Fact>]
let ``let rec inside a task is flagged regardless of size`` () =
    let suggestions =
        adviceIn (
            fsharp
                """
                module Test
                let f () = task {
                    let rec loop (n: int) = if n = 0 then 0 else loop (n - 1)
                    let! c = System.Threading.Tasks.Task.FromResult 3
                    return loop c
                }
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal(TaskStateMachine.AdviceKind.HoistRecursiveFunction, s.Kind)
    | other -> failwithf "Expected exactly one let-rec advice, got %A" other

[<Fact>]
let ``let rec inside a nested lambda is not resumable code`` () =
    Assert.Empty(
        adviceIn (
            fsharp
                """
                module Test
                let f () = task {
                    let g = fun (n: int) -> (let rec loop m = if m = 0 then 0 else loop (m - 1) in loop n)
                    let! c = System.Threading.Tasks.Task.FromResult 3
                    return g c
                }
                """
        )
    )

[<Fact>]
let ``leading plain lets in an oversized task are counted`` () =
    let suggestions =
        adviceIn (
            fsharp
                """
                module Test
                let f () = task {
                    let a = 1
                    let b = 2

                """
            + awaits 8
            + "\n    return a + b + x1\n}"
        )

    match suggestions with
    | [ s ] -> Assert.Equal(TaskStateMachine.AdviceKind.HoistPlainLets 2, s.Kind)
    | other -> failwithf "Expected exactly one hoist advice, got %A" other

[<Fact>]
let ``a directive block below the branch blocks the hoist`` () =
    // the parse tree stops at the last arm the ACTIVE defines leave visible.
    // A `#if` opening right below it can hold further arms that another
    // configuration compiles, and the build check never sees them: it
    // compiles the one configuration in front of it, where the file is fine
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1

                    match c with
                    | 1 -> return x
                    | _ -> return -1
            #if EXTRA
                    | 2 -> return x + 100
            #endif
                }
            """

    Assert.Empty(
        adviceIn source
        |> List.filter (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)
    )

[<Fact>]
let ``a plain let under a try is never hoisted out of the handler`` () =
    // `let x = 4 / i` throws, and the handler is the whole point of writing it
    // there: lifting it above the builder would let the exception escape past
    // `with`. Only lets the try does not cover may travel
    let source =
        fsharp
            """
            module Test
            let i = 0
            let f () =
                task {
                    try
                        let x = 4 / i

            """
        + (awaits 8).Replace("    let!", "            let!")
        + fsharp
            """

                        return x1 + x
                    with _ -> return 42
                }
            """

    Assert.Empty(
        adviceIn source
        |> List.filter (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)
    )

[<Fact>]
let ``hoisting stops at the try, taking only the lets above it`` () =
    let source =
        fsharp
            """
            module Test
            let i = 0
            let f () =
                task {
                    let p = 1
                    try
                        let x = 4 / i

            """
        + (awaits 8).Replace("    let!", "            let!")
        + fsharp
            """

                        return x1 + x + p
                    with _ -> return 42
                }
            """

    match
        adviceIn source
        |> List.choose (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistPlainLets n -> Some(n, s.Edits)
            | _ -> None)
    with
    | [ (1, edits) ] ->
        // `p` moves, `x` stays under the handler
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("let p = 1", moved)
        Assert.DoesNotContain("4 / i", moved)
    | other -> failwithf "Expected one hoist of exactly one let, got %A" other

[<Fact>]
let ``a let whose own rhs is a try still hoists - the handler travels too`` () =
    let source =
        fsharp
            """
            module Test
            let i = 0
            let f () =
                task {
                    let r = try 4 / i with _ -> 0

            """
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        return x1 + r\n    }"

    match
        adviceIn source
        |> List.choose (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistPlainLets n -> Some(n, s.Edits)
            | _ -> None)
    with
    | [ (1, edits) ] ->
        let moved = edits |> List.map snd |> String.concat ""
        Assert.Contains("try 4 / i with _ -> 0", moved)
    | other -> failwithf "Expected one hoist of exactly one let, got %A" other

[<Fact>]
let ``oversized branching where both arms await suggests a split`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) = task {
                if cond then

            """
        + awaits 4
        + "\n        return x1\n    else\n"
        + awaits 4
        + "\n        return x2\n}"

    // the awaits helper indents for a plain task body; re-indent for branches
    let source = source.Replace("    let!", "        let!")

    match adviceIn source with
    | [ s ] -> Assert.Equal(TaskStateMachine.AdviceKind.SplitBranches, s.Kind)
    | other -> failwithf "Expected exactly one split advice, got %A" other

[<Fact>]
let ``long tail after the last await in an oversized task suggests extraction`` () =
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + fsharp
            """

                let b = x1 + 1
                let c = b * 2
                let d = c - 3
                let e = d + x2
                return e
            }
            """

    match adviceIn source with
    | [ s ] ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractTail lines -> Assert.True(lines >= 4)
        | other -> failwithf "Expected tail advice, got %A" other
    | other -> failwithf "Expected exactly one tail advice, got %A" other

[<Fact>]
let ``a lean task yields no advice`` () =
    Assert.Empty(
        adviceIn (
            fsharp
                """
                module Test
                let f () = task {
                    let a = 1
                    let! c = System.Threading.Tasks.Task.FromResult 3
                    return a + c
                }
                """
        )
    )

[<Fact>]
let ``a tail touching a local mutable is not extracted`` () =
    let source =
        fsharp
            """
            module Test
            let f () = task {
                let mutable acc = 0

            """
        + awaits 8
        + fsharp
            """

                acc <- acc + x1
                let s2 = acc + 2
                let s3 = s2 + 3
                let s4 = s3 + 4
                return s4
            }
            """

    let tails =
        adviceIn source
        |> List.filter (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    match tails with
    | [ s ] -> Assert.Empty s.Edits
    | other -> failwithf "Expected one tail advice, got %A" other

// ---- the automatic fixes ----

/// Apply a suggestion's (range, replacement) edits to the source text.
let private applyEdits (source: string) (edits: (FSharp.Compiler.Text.range * string) list) =
    let lines = source.Split '\n'

    let offsetOf (line: int) (col: int) =
        (lines |> Seq.take (line - 1) |> Seq.sumBy (fun l -> l.Length + 1)) + col

    // bottom-up so earlier offsets stay valid
    edits
    |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.fold
        (fun (acc: string) (r, replacement) ->
            let s = offsetOf r.StartLine r.StartColumn
            let e = offsetOf r.EndLine r.EndColumn
            acc.Substring(0, s) + replacement + acc.Substring e)
        source

let private editsOfKind kind (suggestions: TaskStateMachine.Suggestion list) =
    suggestions |> List.pick (fun s -> if kind s.Kind then Some s.Edits else None)

[<Fact>]
let ``leading plain lets hoist above the builder and the result typechecks`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                task {
                    let a = 1
                    let b = a * 2

            """
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        return a + b + x1\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits

    Assert.Contains(
        fsharp
            """
                let a = 1
                let b = a * 2
                task {
            """,
        patched
    )

    assertTypechecks "Patched source" patched

[<Fact>]
let ``the documenting comment block hoists with its binding`` () =
    // both /// runs above the let travel, blank line between them intact;
    // the blank line above the block stays inside the task
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

                    /// HERE WE GO WITH a

                    /// a value
                    let a = 1
                    let b = a * 2

            """
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        return a + b + x1\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits

    Assert.Contains(
        fsharp
            """
            /// HERE WE GO WITH a

                /// a value
                let a = 1
                let b = a * 2
                task {
            """,
        patched
    )

    assertTypechecks "Patched source" patched

[<Fact>]
let ``a mutable leading let stops the hoist before it`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                task {
                    let a = 1
                    let mutable m = a

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    m <- m + x1
                    return a + m
                }
            """

    match
        adviceIn source
        |> List.tryPick (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistPlainLets n -> Some(n, s.Edits)
            | _ -> None)
    with
    | Some(n, edits) ->
        // only `a` is hoistable; the fix must not carry the mutable along
        Assert.Equal(1, n)

        if not edits.IsEmpty then
            let patched = applyEdits source edits
            Assert.Contains("let mutable m", patched.Substring(patched.IndexOf "task {"))
            assertTypechecks "Patched source" patched
    | None -> () // no hoist advice at all is acceptable too

[<Fact>]
let ``the non-awaiting tail wraps into a local function and typechecks`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    // combine everything
                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    return s1 + s2 + s3
                }
            """

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("let runTail () =", patched)
    Assert.Contains("return runTail ()", patched)
    // the comment travels inside the wrapper region untouched
    Assert.Contains("// combine everything", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a return whose value hides behind a block comment keeps its keyword`` () =
    // `return (*{...*) transferdataNow` minus the
    // keyword puts the line's first token right of the comment, deeper than
    // the let above it, which the parser then reads as that let's
    // continuation. The plain closure stands down; the task-returning
    // wrapper, which keeps the `return`, is still fine
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    return (*{Sum = *) s1 + s2 + s3 //; }
                }
            """

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("return (*{Sum = *) s1 + s2 + s3", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``an already extracted tail is not wrapped again`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    let runTail () =
                        let s1 = x1 + 1
                        let s2 = s1 + 2
                        let s3 = s2 + 3
                        s1 + s2 + s3
                    return runTail ()
                }
            """

    let tails =
        adviceIn source
        |> List.filter (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    // the local function body is not resumable code: nothing left to shrink
    Assert.Empty tails

[<Fact>]
let ``a tiny tail after a binding whose bangs sit in a nested CE is not wrapped`` () =
    // the last bang lives inside a nested task in an earlier BINDING, so a
    // body-end-minus-bang-line count sees a big number while the actual
    // tail is two lines — wrapping them would re-wrap its own wrapper every
    // pass
    let source =
        "module Test\nlet f (cache: ResizeArray<int>) = task {\n"
        + awaits 8
        + fsharp
            """

                let inner =
                    task {
                        let! b = System.Threading.Tasks.Task.FromResult 9
                        return b + x1
                    }
                    |> fun t ->
                        let a = t
                        let b2 = a
                        let c = b2
                        c
                cache.Clear()
                return inner
            }
            """

    let tailEdits =
        adviceIn source
        |> List.collect (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail _ -> s.Edits
            | _ -> [])

    Assert.Empty tailEdits

[<Fact>]
let ``a tail that is already one wrapped thunk is never re-wrapped`` () =
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + fsharp
            """

                let inner =
                    task {
                        let! b = System.Threading.Tasks.Task.FromResult 9
                        return b + x1
                    }
                    |> fun t ->
                        let a = t
                        let b2 = a
                        let c = b2
                        c
                let runTail () =
                    ignore inner
                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    s1 + s2 + s3
                return runTail ()
            }
            """

    let tailEdits =
        adviceIn source
        |> List.collect (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail _ -> s.Edits
            | _ -> [])

    Assert.Empty tailEdits


[<Fact>]
let ``a tail holding a use never becomes a plain closure`` () =
    // `use` inside a CE binds to the builder's Using (DisposeAsync where the
    // type offers it); a plain closure would silently make it synchronous
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + fsharp
            """

                use r = new System.IO.MemoryStream()
                let s1 = x1 + 1
                let s2 = s1 + 2
                let s3 = s2 + 3
                return s1 + s2 + s3 + int r.Length
            }
            """

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    // either it stands down, or it uses the task-returning variant where the
    // `use` stays real CE syntax — never the plain closure form
    if not edits.IsEmpty then
        let patched = applyEdits source edits
        Assert.Contains("let runTail () = task {", patched)
        assertTypechecks "Patched source" patched

[<Fact>]
let ``a tail whose branches all return hoists the return instead of extracting`` () =
    // the hoist beats the task-returning wrapper on this tail: one keyword moves, no function is invented,
    // and the branches stop being separate exits through the builder
    let source =
        fsharp
            """
            module Test
            let f (c: bool) =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    if c then
                        return 0
                    else
                        let s2 = x1 + 2
                        let s3 = s2 + 3
                        return s3
                }
            """

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.DoesNotContain("let runTail () = task {", patched)
    Assert.Contains("return\n", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a one-line branch keeps its hoisted return on the same line`` () =
    // the closing `}` shares the branch's line, so `return` alone with the
    // payload underneath would leave the brace inside the payload's offside
    // context and the file would stop parsing
    let source =
        fsharp
            """
            module Test
            let g (c: bool) : System.Threading.Tasks.Task<bool> = task { return c }
            let f (c: bool) =
                task {
                    let! r =
                        task {
                            let! result = g c
                            if result then return None else return (Some "failed") }
                    return r
                }
            """

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.Contains("""return if result then None else (Some "failed") }""", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``an oversized if split produces two tasks and typechecks`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                task {
                    if cond then

            """
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        else\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x2\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.SplitBranches -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("if cond then task {", patched)
    Assert.Contains("} else task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``an elif chain stays advice only`` () =
    let source =
        fsharp
            """
            module Test
            let f (a: bool) (b: bool) =
                task {
                    if a then

            """
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        elif b then\n"
        + (awaits 4).Replace("    let!", "            let!")
        + fsharp
            """

                        return x2
                    else
                        return 0
                }
            """

    for s in adviceIn source do
        match s.Kind with
        | TaskStateMachine.AdviceKind.SplitBranches -> Assert.Empty s.Edits
        | _ -> ()

[<Fact>]
let ``a backgroundTask split keeps its builder`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                backgroundTask {
                    if cond then

            """
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        else\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x2\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.SplitBranches -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("if cond then backgroundTask {", patched)
    Assert.Contains("} else backgroundTask {", patched)
    Assert.DoesNotContain("then task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a split fires when only one arm awaits`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                task {
                    if cond then
                        let r = 0
                        return r
                    else

            """
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return x1\n    }"

    let suggestions = adviceIn source

    let edits =
        suggestions
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.SplitBranches -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("if cond then task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``the embedding-generator shape splits`` () =
    // private: under a public function the condition `inputs.Length = 0`
    // (a property read, a NullReferenceException on null) would move out
    // of the task and throw at the call - the split stays advice there
    let source =
        "module Probe\n"
        + "open System.Threading\nopen System.Threading.Tasks\n"
        + fsharp
            """
            let gate = new SemaphoreSlim(1)
            let inferenceLock = new SemaphoreSlim(4)
            let lockSlots = 4

            """
        + "let private generate (inputs: string[]) (ct: CancellationToken) : Task<int> =\n"
        + "    task {\n"
        + "        if inputs.Length = 0 then\n"
        + "            // zero-input contract: no model touch\n"
        + "            let result = 0\n"
        + "            return result\n"
        + "        else\n"
        + "            do! gate.WaitAsync ct\n"
        + "            let mutable acquired = 0\n"
        + "            try\n"
        + "                while acquired < lockSlots do\n"
        + "                    do! inferenceLock.WaitAsync ct\n"
        + "                    acquired <- acquired + 1\n"
        + "                do! Task.Delay(10, ct)\n"
        + "                do! Task.Delay(11, ct)\n"
        + "                do! Task.Delay(12, ct)\n"
        + "                do! Task.Delay(13, ct)\n"
        + "                do! Task.Delay(14, ct)\n"
        + "                do! Task.Delay(15, ct)\n"
        + "                do! Task.Delay(16, ct)\n"
        + "                let padded = inputs |> Array.map (fun s -> s.Length)\n"
        + "                let flat = padded |> Array.sum\n"
        + "                let a1 = flat + 1\n"
        + "                let a2 = a1 + 2\n"
        + "                let a3 = a2 + 3\n"
        + "                return a3\n"
        + "            finally\n"
        + "                if acquired > 0 then inferenceLock.Release acquired |> ignore\n"
        + "                gate.Release() |> ignore\n"
        + "    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.SplitBranches -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    // the then-arm's comment travels into its new task — the line-region
    // arm cut is what keeps the comment guard from holding the fix back
    Assert.Contains("// zero-input contract: no model touch", patched)
    Assert.Contains("if inputs.Length = 0 then task {", patched)
    Assert.Contains("} else task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``an early-return tail hoists its return ahead of the branch`` () =
    // the branch returns rule out a plain closure; hoisting the return is
    // cheaper than the task-returning wrapper: the lets stay
    // where they are and only the branch stops being an exit per arm
    let source =
        fsharp
            """
            module Test
            let f (flag: bool) =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    if flag then
                        return s1
                    else
                        return s2
                }
            """

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    // the bindings before the branch are untouched - nothing moved
    Assert.Contains("let s1 = x1 + 1", patched)
    Assert.DoesNotContain("let runTail () = task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``awaiting match arms stay advice without a fix`` () =
    // the documented split is the if/else body; a per-arm `return!
    // task { .. }` wrap would nest a machine into every awaiting arm, a
    // shape the doc never promised
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                task {
                    match cond with
                    | true ->

            """
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return x1\n        | false ->\n"
        + (awaits 8).Replace("    let!", "            let!").Replace("x", "y")
        + "\n            return y2\n    }"

    match
        adviceIn source
        |> List.filter (fun s -> s.Kind = TaskStateMachine.AdviceKind.SplitBranches)
    with
    | [ s ] -> Assert.Empty s.Edits
    | other -> failwithf "Expected one split advice, got %A" other

[<Fact>]
let ``awaiting match-bang arms stay advice without a fix`` () =
    let source =
        fsharp
            """
            module Test
            let g () = System.Threading.Tasks.Task.FromResult true
            let f () =
                task {
                    match! g () with
                    | true ->

            """
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return x1\n        | false ->\n"
        + (awaits 8).Replace("    let!", "            let!").Replace("x", "y")
        + "\n            return y2\n    }"

    match
        adviceIn source
        |> List.filter (fun s -> s.Kind = TaskStateMachine.AdviceKind.SplitBranches)
    with
    | [ s ] -> Assert.Empty s.Edits
    | other -> failwithf "Expected one split advice, got %A" other

[<Fact>]
let ``a match arm reading a foreign mutable keeps the note`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                task {
                    let mutable acc = 0
                    match cond with
                    | true ->

            """
        + (awaits 8).Replace("    let!", "            let!")
        + fsharp
            """

                        acc <- x1
                        return acc
                    | false ->

            """
        + (awaits 8).Replace("    let!", "            let!").Replace("x", "y")
        + "\n            return y2\n    }"

    let edits =
        adviceIn source
        |> List.tryPick (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.SplitBranches -> Some s.Edits
            | _ -> None)

    match edits with
    | Some e -> Assert.Empty e
    | None -> ()

// ---- the `use` guard on tail extraction ----
//
// A plain `use` inside a CE binds to the builder's Using (DisposeAsync
// where the type offers it, disposal ordered with the workflow). The
// closure variant of the tail wrap would re-bind it to a synchronous
// `using`, so a tail holding one must take the task-returning variant.

/// The tail-extraction edits for a body, or [] when the rule stands down.
let private tailEditsFor (source: string) =
    adviceIn source
    |> List.tryPick (fun s ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractTail _ -> Some s.Edits
        | _ -> None)
    |> Option.defaultValue []

/// The same body shape with and without a `use`, so the guard is the only
/// difference between the two outcomes.
let private tailBody (useLine: string) =
    "module Test\nlet f () = task {\n"
    + awaits 8
    + "\n"
    + useLine
    + fsharp
        """
            let s1 = x1 + 1
            let s2 = s1 + 2
            let s3 = s2 + 3
            return s1 + s2 + s3
        }
        """

[<Fact>]
let ``the control without a use takes the plain closure`` () =
    // proves the shape IS extractable, so the guard is what changes the
    // outcome in the tests below rather than some unrelated gate
    let patched = applyEdits (tailBody "") (tailEditsFor (tailBody ""))
    Assert.Contains("let runTail () =", patched)
    Assert.DoesNotContain("let runTail () = task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a leading use forces the task-returning variant`` () =
    let source = tailBody "    use r = new System.IO.MemoryStream()\n"
    let edits = tailEditsFor source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("let runTail () = task {", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a use in the middle of the tail is caught too`` () =
    // the guard scans the whole tail range, not just its first binding
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + fsharp
            """

                let s1 = x1 + 1
                use r = new System.IO.MemoryStream()
                let s2 = s1 + 2
                let s3 = s2 + 3
                return s1 + s2 + s3 + int r.Length
            }
            """

    let edits = tailEditsFor source

    if not edits.IsEmpty then
        let patched = applyEdits source edits
        Assert.Contains("let runTail () = task {", patched)
        assertTypechecks "Patched source" patched

[<Fact>]
let ``an async tail with a use keeps CE syntax as well`` () =
    let source =
        "module Test\nlet f () = async {\n"
        + ([ for i in 1..8 -> $"    let! x%d{i} = async {{ return %d{i} }}" ]
           |> String.concat "\n")
        + fsharp
            """

                use r = new System.IO.MemoryStream()
                let s1 = x1 + 1
                let s2 = s1 + 2
                let s3 = s2 + 3
                return s1 + s2 + s3 + int r.Length
            }
            """

    let edits = tailEditsFor source

    if not edits.IsEmpty then
        let patched = applyEdits source edits
        Assert.Contains("let runTail () = async {", patched)
        assertTypechecks "Patched source" patched

// ---- a hand-tuned hot path is not restructured ----

[<Fact>]
let ``a hot-path comment inside the binding keeps every move advice-only`` () =
    let source =
        fsharp
            """
            module Test
            let f (cond: bool) =
                // hot path: hand-tuned to avoid allocation
                task {
                    if cond then

            """
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        else\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x2\n    }"

    let suggestions = adviceIn source
    Assert.NotEmpty suggestions

    for s in suggestions do
        Assert.Empty s.Edits

[<Fact>]
let ``a perf comment outside the binding does not withhold the split`` () =
    let source =
        fsharp
            """
            module Test
            // perf notes for the module
            let f (cond: bool) =
                task {
                    if cond then

            """
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        else\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x2\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.SplitBranches -> true
            | _ -> false)

    Assert.NotEmpty edits

// ---- FR0029: the tail is the statement suffix after the last await ----

let private tailsIn (source: string) =
    adviceIn source
    |> List.filter (fun s ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractTail _ -> true
        | _ -> false)

[<Fact>]
let ``FR0029: exception handlers and a finally block after the last await are not a tail`` () =
    // `with ex -> raise ex` + `finally fs.Dispose()` + an Error arm after
    // the last `do!` — six lines of handlers, no business logic to extract
    let source =
        fsharp
            """
            module Test
            let f (fs: System.IO.Stream) (ok: bool) = task {

            """
        + awaits 8
        + fsharp
            """

                if ok then
                    try
                        try
                            do! System.Threading.Tasks.Task.Delay 1
                        with ex ->
                            raise ex
                    finally
                        fs.Dispose()
                else
                    failwith "error"
            }
            """

    Assert.Empty(tailsIn source)

[<Fact>]
let ``FR0029: a multi-line return-bang is an await, not lines that follow one`` () =
    // `return! (...) ctx` spanning five lines inside a `with` handler must
    // not count as a non-awaiting tail from its own first line
    let source =
        fsharp
            """
            module Test
            let handle (ctx: int) : System.Threading.Tasks.Task<int> = task { return ctx }
            let f (ctx: int) = task {

            """
        + awaits 8
        + fsharp
            """

                try
                    return x1
                with _ ->
                    return!
                        (
                            handle
                        ) ctx
            }
            """

    Assert.Empty(tailsIn source)

[<Fact>]
let ``FR0029: a loop body that re-awaits is not a tail and the note sits on the first statement`` () =
    // the last await is inside a `while`,
    // so every following line runs again before the next await
    let looping =
        "module Test\nlet f (log: string -> unit) = task {\n"
        + awaits 8
        + fsharp
            """

                let mutable go = true
                while go do
                    do! System.Threading.Tasks.Task.Delay 1
                    log "a"
                    log "b"
                    log "c"
                    log "d"
                    go <- false
            }
            """

    Assert.Empty(tailsIn looping)

    // a real tail is anchored on its first statement, not on the blank
    // line after the await
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + fsharp
            """


                let b = x1 + 1
                let c = b * 2
                let d = c - 3
                let e = d + x2
                return e
            }
            """

    match tailsIn source with
    | [ s ] ->
        Assert.Equal(TaskStateMachine.AdviceKind.ExtractTail 5, s.Kind)

        Assert.Equal(
            source.Split '\n'
            |> Array.findIndex (fun l -> l.Contains "let b = x1 + 1")
            |> (+) 1,
            s.Range.StartLine
        )

        Assert.Equal(4, s.Range.StartColumn)
    | other -> failwithf "Expected one tail advice, got %A" other

[<Fact>]
let ``FR0029: a tail inside the arm that holds the last await is advice only`` () =
    // the last `let!` sits in a match arm and a 20-line record
    // construction follows it there — counted, anchored on
    // the first statement, but not wrapped
    let source =
        "module Test\nlet f (ok: bool) = task {\n"
        + awaits 8
        + fsharp
            """

                match ok with
                | false -> return 0
                | true ->
                    let! y = System.Threading.Tasks.Task.FromResult 5
                    let b = y + 1
                    let c = b * 2
                    let d = c - 3
                    let e = d + x2
                    return e
            }
            """

    match tailsIn source with
    | [ s ] ->
        Assert.Equal(TaskStateMachine.AdviceKind.ExtractTail 5, s.Kind)
        Assert.Empty s.Edits
        Assert.Equal(8, s.Range.StartColumn)
    | other -> failwithf "Expected one tail advice, got %A" other

[<Fact>]
let ``the tail threshold is a parameter, not a constant`` () =
    // five non-awaiting lines: extracted at a threshold of four, left alone at
    // ten. The default is ten - four lines is a thin trade for a new function
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    let s4 = s3 + 4
                    return s4
                }
            """

    let tree, sourceText = parse source

    let kindsAt threshold =
        TaskStateMachine.find tree sourceText None threshold false Set.empty
        |> List.choose (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail n -> Some n
            | _ -> None)

    Assert.NotEmpty(kindsAt 4)
    Assert.Empty(kindsAt 10)

[<Fact>]
let ``async is left alone unless hoistReturnOnAsync is turned on`` () =
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                async {
                    let! x = async { return 1 }

                    match c with
                    | 1 -> return x
                    | _ -> return -1
                }
            """

    Assert.Empty(adviceIn source)

[<Fact>]
let ``hoistReturnOnAsync hoists the return in an async block`` () =
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                async {
                    let! x = async { return 1 }

                    match c with
                    | 1 -> return x
                    | _ -> return -1
                }
            """

    let hoists =
        adviceInAsyncOn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists

    Assert.Contains(
        fsharp
            """
            return

            """,
        patched
    )

    Assert.DoesNotContain("| 1 -> return x", patched)
    assertTypechecks "Patched source" patched

[<Fact>]
let ``hoistReturnOnAsync brings only the hoist, never the FS3511 advice`` () =
    // async has no resumable state machine, so nothing here may claim the
    // dynamic fallback: no let-rec advice, no let hoist, no branch split and
    // no tail extraction, however oversized the block is
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                async {
                    let a = 1
                    let b = 2

            """
        + (awaits 8)
            .Replace("System.Threading.Tasks.Task.FromResult", "async.Return")
            .Replace("    let!", "        let!")
        + fsharp
            """

                    let rec loop (n: int) = if n = 0 then 0 else loop (n - 1)
                    let s1 = x1 + a + b
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    let s4 = s3 + 4
                    return s4 + loop c
                }
            """

    let kinds = adviceInAsyncOn source |> List.map (fun s -> s.Kind)

    Assert.All(
        kinds,
        fun k ->
            match k with
            | TaskStateMachine.AdviceKind.HoistReturn _ -> ()
            | other -> failwithf "async should only ever get the hoist, got %A" other
    )

[<Fact>]
let ``a use inside the branch blocks the hoist`` () =
    // hoisting makes the branch the payload of one `return`, so it stops
    // being CE code and a `use` in it re-binds from the builder's Using to
    // the language's. A type offering both logs "async" before the hoist
    // and "sync" after it, compiling clean either way - nothing catches this
    // at build time
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1

                    match c with
                    | 1 ->
                        use ms = new System.IO.MemoryStream()
                        return int ms.Length + x
                    | _ -> return x
                }
            """

    Assert.Empty(
        adviceIn source
        |> List.filter (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)
    )

[<Fact>]
let ``a use ahead of the branch still hoists - it stays CE code`` () =
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    use ms = new System.IO.MemoryStream()

                    match c with
                    | 1 -> return int ms.Length + x
                    | _ -> return x
                }
            """

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    assertTypechecks "Patched source" patched

[<Fact>]
let ``a tail closing on a bare return extracts as a plain closure`` () =
    // `return` alone on its line with the value beneath it. A strip that
    // handles only `return <value>` on ONE line would fall through to the
    // task-returning variant and buy a second state machine for a tail that
    // awaits nothing
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + fsharp
            """

                    let s1 = x1 + 1
                    let s2 = s1 + 2
                    let s3 = s2 + 3
                    let s4 = s3 + 4
                    return
                        s4,
                        s3
                }
            """

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.DoesNotContain("runTail () = task {", patched)
    Assert.Contains("return runTail ()", patched)
    assertTypechecks "Patched source" patched


[<Fact>]
let ``the tail extraction is a quickfix or nothing, never a note`` () =
    // `runTail` invents a name for code whose only sin was sitting after the
    // last await. Telling someone WITHOUT a problem about it helps no one, so
    // below the bar the rule says nothing at all; above it, it fixes. The
    // compiler settles which bar applies: FS3511 names the task or it does not
    let source =
        fsharp
            """
            module Test
            let f () =
                task {

            """
        + (awaits 8).Replace("    let!", "        let!")
        + "\n"
        + ([ for i in 1..12 -> $"        let s%d{i} = x1 + %d{i}" ] |> String.concat "\n")
        + "\n        return s12\n    }"

    let tree, sourceText = parse source

    let tails threshold warnedLines =
        TaskStateMachine.find tree sourceText None threshold false warnedLines
        |> List.choose (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail _ -> Some s.Edits
            | _ -> None)

    // the tail is twelve lines; a high bar and no warning means SILENCE, not a note
    Assert.Empty(tails 40 Set.empty)

    // the compiler warned about this task (`task {` is on line 3): it fixes
    match tails 40 (Set.singleton 3) with
    | [ edits ] -> Assert.NotEmpty edits
    | other -> failwithf "Expected one tail fix, got %A" other

    // a warning about a DIFFERENT task licenses nothing here
    Assert.Empty(tails 40 (Set.singleton 99))

    // and a repository that lowers the bar itself gets the fix, unwarned
    match tails 4 Set.empty with
    | [ edits ] -> Assert.NotEmpty edits
    | other -> failwithf "Expected one tail fix, got %A" other

[<Fact>]
let ``a two-line member header keeps its leading lets inside the builder`` () =
    // test fixtures: `[<Fact>] member test.` on one line, the backticked
    // name and `()=` on the next, the builder undented below the name. Lets
    // hoisted to the builder's column are offside of the name line, so the
    // advice carries no edit here
    let source =
        fsharp
            """
            module Test
            type Tests() =
                [<Xunit.Fact>] member test.
                 ``a test`` ()=
                    task {
                        let a = 1
                        let b = a * 2

            """
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return a + b + x1\n        }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)

    Assert.Empty edits
