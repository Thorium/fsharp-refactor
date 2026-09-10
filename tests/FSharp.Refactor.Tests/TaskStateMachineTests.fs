module FSharp.Refactor.Tests.TaskStateMachineTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private adviceIn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText 4 false Set.empty

/// The same, with the `hoistReturnOnAsync` knob turned on.
let private adviceInAsyncOn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText 4 true Set.empty


/// n `let! xi = Task.FromResult i` lines, enough to cross the size gate.
let private awaits n =
    [ for i in 1..n -> $"    let! x%d{i} = System.Threading.Tasks.Task.FromResult %d{i}" ]
    |> String.concat "\n"

[<Fact>]
let ``let rec inside a task is flagged regardless of size`` () =
    let suggestions =
        adviceIn
            "module Test\nlet f () = task {\n    let rec loop (n: int) = if n = 0 then 0 else loop (n - 1)\n    let! c = System.Threading.Tasks.Task.FromResult 3\n    return loop c\n}"

    match suggestions with
    | [ s ] -> Assert.Equal(TaskStateMachine.AdviceKind.HoistRecursiveFunction, s.Kind)
    | other -> failwithf "Expected exactly one let-rec advice, got %A" other

[<Fact>]
let ``let rec inside a nested lambda is not resumable code`` () =
    Assert.Empty(
        adviceIn
            "module Test\nlet f () = task {\n    let g = fun (n: int) -> (let rec loop m = if m = 0 then 0 else loop (m - 1) in loop n)\n    let! c = System.Threading.Tasks.Task.FromResult 3\n    return g c\n}"
    )

[<Fact>]
let ``leading plain lets in an oversized task are counted`` () =
    let suggestions =
        adviceIn (
            "module Test\nlet f () = task {\n    let a = 1\n    let b = 2\n"
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
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n\n        match c with\n        | 1 -> return x\n        | _ -> return -1\n#if EXTRA\n        | 2 -> return x + 100\n#endif\n    }"

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
        "module Test\nlet i = 0\nlet f () =\n    task {\n        try\n            let x = 4 / i\n"
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return x1 + x\n        with _ -> return 42\n    }"

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
        "module Test\nlet i = 0\nlet f () =\n    task {\n        let p = 1\n        try\n            let x = 4 / i\n"
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            return x1 + x + p\n        with _ -> return 42\n    }"

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
        "module Test\nlet i = 0\nlet f () =\n    task {\n        let r = try 4 / i with _ -> 0\n"
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
        "module Test\nlet f (cond: bool) = task {\n    if cond then\n"
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
        + "\n    let b = x1 + 1\n    let c = b * 2\n    let d = c - 3\n    let e = d + x2\n    return e\n}"

    match adviceIn source with
    | [ s ] ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractTail lines -> Assert.True(lines >= 4)
        | other -> failwithf "Expected tail advice, got %A" other
    | other -> failwithf "Expected exactly one tail advice, got %A" other

[<Fact>]
let ``a lean task yields no advice`` () =
    Assert.Empty(
        adviceIn
            "module Test\nlet f () = task {\n    let a = 1\n    let! c = System.Threading.Tasks.Task.FromResult 3\n    return a + c\n}"
    )

[<Fact>]
let ``a tail touching a local mutable is not extracted`` () =
    let source =
        "module Test\nlet f () = task {\n    let mutable acc = 0\n"
        + awaits 8
        + "\n    acc <- acc + x1\n    let s2 = acc + 2\n    let s3 = s2 + 3\n    let s4 = s3 + 4\n    return s4\n}"

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
        "module Test\nlet f () =\n    task {\n        let a = 1\n        let b = a * 2\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        return a + b + x1\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("    let a = 1\n    let b = a * 2\n    task {", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``the documenting comment block hoists with its binding`` () =
    // both /// runs above the let travel, blank line between them intact;
    // the blank line above the block stays inside the task
    let source =
        "module Test\nlet f () =\n    task {\n\n        /// HERE WE GO WITH a\n\n        /// a value\n        let a = 1\n        let b = a * 2\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        return a + b + x1\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistPlainLets _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("/// HERE WE GO WITH a\n\n    /// a value\n    let a = 1\n    let b = a * 2\n    task {", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a mutable leading let stops the hoist before it`` () =
    let source =
        "module Test\nlet f () =\n    task {\n        let a = 1\n        let mutable m = a\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        m <- m + x1\n        return a + m\n    }"

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
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | None -> () // no hoist advice at all is acceptable too

[<Fact>]
let ``the non-awaiting tail wraps into a local function and typechecks`` () =
    let source =
        "module Test\nlet f () =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        // combine everything\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        let s3 = s2 + 3\n        return s1 + s2 + s3\n    }"

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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``an already extracted tail is not wrapped again`` () =
    let source =
        "module Test\nlet f () =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        let runTail () =\n            let s1 = x1 + 1\n            let s2 = s1 + 2\n            let s3 = s2 + 3\n            s1 + s2 + s3\n        return runTail ()\n    }"

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
    // the management-portal doom-loop shape: the last bang lives inside a
    // nested task in an earlier BINDING, so the old body-end-minus-bang-line
    // count saw a big number while the actual tail was two lines — it
    // wrapped them, and then re-wrapped its own wrapper every pass
    let source =
        "module Test\nlet f (cache: ResizeArray<int>) = task {\n"
        + awaits 8
        + "\n    let inner =\n        task {\n            let! b = System.Threading.Tasks.Task.FromResult 9\n            return b + x1\n        }\n        |> fun t ->\n            let a = t\n            let b2 = a\n            let c = b2\n            c\n    cache.Clear()\n    return inner\n}"

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
        + "\n    let inner =\n        task {\n            let! b = System.Threading.Tasks.Task.FromResult 9\n            return b + x1\n        }\n        |> fun t ->\n            let a = t\n            let b2 = a\n            let c = b2\n            c\n    let runTail () =\n        ignore inner\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        let s3 = s2 + 3\n        s1 + s2 + s3\n    return runTail ()\n}"

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
        + "\n    use r = new System.IO.MemoryStream()\n    let s1 = x1 + 1\n    let s2 = s1 + 2\n    let s3 = s2 + 3\n    return s1 + s2 + s3 + int r.Length\n}"

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
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a tail whose branches all return hoists the return instead of extracting`` () =
    // this was the task-returning wrapper's case. The hoist is the better
    // answer to the same tail: one keyword moves, no function is invented,
    // and the branches stop being separate exits through the builder
    let source =
        "module Test\nlet f (c: bool) =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        if c then\n            return 0\n        else\n            let s2 = x1 + 2\n            let s3 = s2 + 3\n            return s3\n    }"

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.DoesNotContain("let runTail () = task {", patched)
    Assert.Contains("return\n", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a one-line branch keeps its hoisted return on the same line`` () =
    // CompanyHub.fs had thirteen of these. The closing `}` shares the
    // branch's line, so `return` alone with the payload underneath left the
    // brace inside the payload's offside context and the file stopped parsing
    let source =
        "module Test\nlet g (c: bool) : System.Threading.Tasks.Task<bool> = task { return c }\nlet f (c: bool) =\n    task {\n        let! r =\n            task {\n                let! result = g c\n                if result then return None else return (Some \"failed\") }\n        return r\n    }"

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.Contains("return if result then None else (Some \"failed\") }", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``an oversized if split produces two tasks and typechecks`` () =
    let source =
        "module Test\nlet f (cond: bool) =\n    task {\n        if cond then\n"
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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``an elif chain stays advice only`` () =
    let source =
        "module Test\nlet f (a: bool) (b: bool) =\n    task {\n        if a then\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x1\n        elif b then\n"
        + (awaits 4).Replace("    let!", "            let!")
        + "\n            return x2\n        else\n            return 0\n    }"

    for s in adviceIn source do
        match s.Kind with
        | TaskStateMachine.AdviceKind.SplitBranches -> Assert.Empty s.Edits
        | _ -> ()

[<Fact>]
let ``a backgroundTask split keeps its builder`` () =
    let source =
        "module Test\nlet f (cond: bool) =\n    backgroundTask {\n        if cond then\n"
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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a split fires when only one arm awaits`` () =
    let source =
        "module Test\nlet f (cond: bool) =\n    task {\n        if cond then\n            let r = 0\n            return r\n        else\n"
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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``the embedding-generator shape splits`` () =
    let source =
        "module Probe\n"
        + "open System.Threading\nopen System.Threading.Tasks\n"
        + "let gate = new SemaphoreSlim(1)\nlet inferenceLock = new SemaphoreSlim(4)\nlet lockSlots = 4\n"
        + "let generate (inputs: string[]) (ct: CancellationToken) : Task<int> =\n"
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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``an early-return tail hoists its return ahead of the branch`` () =
    // the branch returns rule out a plain closure, and used to earn the
    // task-returning wrapper. Hoisting the return is cheaper: the lets stay
    // where they are and only the branch stops being an exit per arm
    let source =
        "module Test\nlet f (flag: bool) =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        if flag then\n            return s1\n        else\n            return s2\n    }"

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
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``awaiting match arms stay advice without a fix`` () =
    // the documented split is the if/else body; the per-arm `return!
    // task { .. }` wrap once nested a machine into every awaiting arm of
    // suave's HttpOutput.fs, a shape the doc never promised
    let source =
        "module Test\nlet f (cond: bool) =\n    task {\n        match cond with\n        | true ->\n"
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
        "module Test\nlet g () = System.Threading.Tasks.Task.FromResult true\nlet f () =\n    task {\n        match! g () with\n        | true ->\n"
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
        "module Test\nlet f (cond: bool) =\n    task {\n        let mutable acc = 0\n        match cond with\n        | true ->\n"
        + (awaits 8).Replace("    let!", "            let!")
        + "\n            acc <- x1\n            return acc\n        | false ->\n"
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
    + "    let s1 = x1 + 1\n    let s2 = s1 + 2\n    let s3 = s2 + 3\n    return s1 + s2 + s3\n}"

[<Fact>]
let ``the control without a use takes the plain closure`` () =
    // proves the shape IS extractable, so the guard is what changes the
    // outcome in the tests below rather than some unrelated gate
    let patched = applyEdits (tailBody "") (tailEditsFor (tailBody ""))
    Assert.Contains("let runTail () =", patched)
    Assert.DoesNotContain("let runTail () = task {", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a leading use forces the task-returning variant`` () =
    let source = tailBody "    use r = new System.IO.MemoryStream()\n"
    let edits = tailEditsFor source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("let runTail () = task {", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a use in the middle of the tail is caught too`` () =
    // the guard scans the whole tail range, not just its first binding
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + "\n    let s1 = x1 + 1\n    use r = new System.IO.MemoryStream()\n    let s2 = s1 + 2\n    let s3 = s2 + 3\n    return s1 + s2 + s3 + int r.Length\n}"

    let edits = tailEditsFor source

    if not edits.IsEmpty then
        let patched = applyEdits source edits
        Assert.Contains("let runTail () = task {", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``an async tail with a use keeps CE syntax as well`` () =
    let source =
        "module Test\nlet f () = async {\n"
        + ([ for i in 1..8 -> $"    let! x%d{i} = async {{ return %d{i} }}" ]
           |> String.concat "\n")
        + "\n    use r = new System.IO.MemoryStream()\n    let s1 = x1 + 1\n    let s2 = s1 + 2\n    let s3 = s2 + 3\n    return s1 + s2 + s3 + int r.Length\n}"

    let edits = tailEditsFor source

    if not edits.IsEmpty then
        let patched = applyEdits source edits
        Assert.Contains("let runTail () = async {", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- a hand-tuned hot path is not restructured (suave's HttpOutput.fs) ----

[<Fact>]
let ``a hot-path comment inside the binding keeps every move advice-only`` () =
    let source =
        "module Test\nlet f (cond: bool) =\n    // hot path: hand-tuned to avoid allocation\n    task {\n        if cond then\n"
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
        "module Test\n// perf notes for the module\nlet f (cond: bool) =\n    task {\n        if cond then\n"
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
    // suave's Combinators: `with ex -> raise ex` + `finally fs.Dispose()`
    // + an Error arm followed the last `do!` — six lines of handlers, no
    // business logic to extract
    let source =
        "module Test\nlet f (fs: System.IO.Stream) (ok: bool) = task {\n"
        + awaits 8
        + "\n    if ok then\n        try\n            try\n                do! System.Threading.Tasks.Task.Delay 1\n            with ex ->\n                raise ex\n        finally\n            fs.Dispose()\n    else\n        failwith \"error\"\n}"

    Assert.Empty(tailsIn source)

[<Fact>]
let ``FR0029: a multi-line return-bang is an await, not lines that follow one`` () =
    // suave's Proxy: `return! (...) ctx` spanning five lines inside a `with`
    // handler counted as a non-awaiting tail from its own first line
    let source =
        "module Test\nlet handle (ctx: int) : System.Threading.Tasks.Task<int> = task { return ctx }\nlet f (ctx: int) = task {\n"
        + awaits 8
        + "\n    try\n        return x1\n    with _ ->\n        return!\n            (\n                handle\n            ) ctx\n}"

    Assert.Empty(tailsIn source)

[<Fact>]
let ``FR0029: a loop body that re-awaits is not a tail and the note sits on the first statement`` () =
    // suave's ConnectionHealthChecker: the last await is inside a `while`,
    // so every following line runs again before the next await
    let looping =
        "module Test\nlet f (log: string -> unit) = task {\n"
        + awaits 8
        + "\n    let mutable go = true\n    while go do\n        do! System.Threading.Tasks.Task.Delay 1\n        log \"a\"\n        log \"b\"\n        log \"c\"\n        log \"d\"\n        go <- false\n}"

    Assert.Empty(tailsIn looping)

    // a real tail is anchored on its first statement, not on the blank
    // line after the await
    let source =
        "module Test\nlet f () = task {\n"
        + awaits 8
        + "\n\n    let b = x1 + 1\n    let c = b * 2\n    let d = c - 3\n    let e = d + x2\n    return e\n}"

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
    // suave's ConnectionFacade: the last `let!` sits in a match arm and a
    // 20-line record construction follows it there — counted, anchored on
    // the first statement, but not wrapped
    let source =
        "module Test\nlet f (ok: bool) = task {\n"
        + awaits 8
        + "\n    match ok with\n    | false -> return 0\n    | true ->\n        let! y = System.Threading.Tasks.Task.FromResult 5\n        let b = y + 1\n        let c = b * 2\n        let d = c - 3\n        let e = d + x2\n        return e\n}"

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
        "module Test\nlet f () =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        let s3 = s2 + 3\n        let s4 = s3 + 4\n        return s4\n    }"

    let tree, sourceText = parse source

    let kindsAt threshold =
        TaskStateMachine.find tree sourceText threshold false Set.empty
        |> List.choose (fun s ->
            match s.Kind with
            | TaskStateMachine.AdviceKind.ExtractTail n -> Some n
            | _ -> None)

    Assert.NotEmpty(kindsAt 4)
    Assert.Empty(kindsAt 10)

[<Fact>]
let ``async is left alone unless hoistReturnOnAsync is turned on`` () =
    let source =
        "module Test\nlet f (c: int) =\n    async {\n        let! x = async { return 1 }\n\n        match c with\n        | 1 -> return x\n        | _ -> return -1\n    }"

    Assert.Empty(adviceIn source)

[<Fact>]
let ``hoistReturnOnAsync hoists the return in an async block`` () =
    let source =
        "module Test\nlet f (c: int) =\n    async {\n        let! x = async { return 1 }\n\n        match c with\n        | 1 -> return x\n        | _ -> return -1\n    }"

    let hoists =
        adviceInAsyncOn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.Contains("return\n", patched)
    Assert.DoesNotContain("| 1 -> return x", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``hoistReturnOnAsync brings only the hoist, never the FS3511 advice`` () =
    // async has no resumable state machine, so nothing here may claim the
    // dynamic fallback: no let-rec advice, no let hoist, no branch split and
    // no tail extraction, however oversized the block is
    let source =
        "module Test\nlet f (c: int) =\n    async {\n        let a = 1\n        let b = 2\n"
        + (awaits 8)
            .Replace("System.Threading.Tasks.Task.FromResult", "async.Return")
            .Replace("    let!", "        let!")
        + "\n        let rec loop (n: int) = if n = 0 then 0 else loop (n - 1)\n        let s1 = x1 + a + b\n        let s2 = s1 + 2\n        let s3 = s2 + 3\n        let s4 = s3 + 4\n        return s4 + loop c\n    }"

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
    // the language's. A type offering both logged "async" before the hoist
    // and "sync" after it, compiling clean either way - nothing would have
    // caught this at build time
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n\n        match c with\n        | 1 ->\n            use ms = new System.IO.MemoryStream()\n            return int ms.Length + x\n        | _ -> return x\n    }"

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
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        use ms = new System.IO.MemoryStream()\n\n        match c with\n        | 1 -> return int ms.Length + x\n        | _ -> return x\n    }"

    let hoists =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.HoistReturn _ -> true
            | _ -> false)

    Assert.NotEmpty hoists
    let patched = applyEdits source hoists
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a tail closing on a bare return extracts as a plain closure`` () =
    // management-portal's APIs.fs: `return` alone on its line with the value
    // beneath it. The strip only handled `return <value>` on ONE line, so this
    // fell through to the task-returning variant and bought a second state
    // machine for a tail that awaits nothing
    let source =
        "module Test\nlet f () =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        let s3 = s2 + 3\n        let s4 = s3 + 4\n        return\n            s4,\n            s3\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.DoesNotContain("runTail () = task {", patched)
    Assert.Contains("return runTail ()", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")


[<Fact>]
let ``the tail extraction is a quickfix or nothing, never a note`` () =
    // `runTail` invents a name for code whose only sin was sitting after the
    // last await. Telling someone WITHOUT a problem about it helps no one, so
    // below the bar the rule says nothing at all; above it, it fixes. The
    // compiler settles which bar applies: FS3511 names the task or it does not
    let source =
        "module Test\nlet f () =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n"
        + ([ for i in 1..12 -> $"        let s%d{i} = x1 + %d{i}" ] |> String.concat "\n")
        + "\n        return s12\n    }"

    let tree, sourceText = parse source

    let tails threshold warnedLines =
        TaskStateMachine.find tree sourceText threshold false warnedLines
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
