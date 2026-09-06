module FSharp.Refactor.Tests.TaskStateMachineTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private adviceIn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText

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
let ``a tail with branch returns extracts as a task-returning function`` () =
    // once the old hands-off case: branch returns cannot ride a plain
    // closure, but the task-returning wrapper carries them
    let source =
        "module Test\nlet f (c: bool) =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        if c then\n            return 0\n        else\n            let s2 = x1 + 2\n            let s3 = s2 + 3\n            return s3\n    }"

    for s in adviceIn source do
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractTail _ ->
            Assert.NotEmpty s.Edits
            let patched = applyEdits source s.Edits
            Assert.Contains("let runTail () = task {", patched)
            Assert.Contains("return! runTail ()", patched)
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | _ -> ()

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
let ``an awaiting try-finally suffix becomes its own task function`` () =
    let source =
        "module Test\nopen System.Threading\nopen System.Threading.Tasks\n"
        + "let gate = new SemaphoreSlim(1)\nlet lockSlots = 4\nlet inferenceLock = new SemaphoreSlim(4)\n"
        + "let f (xs: int[]) (ct: CancellationToken) : Task<int> =\n    task {\n        do! gate.WaitAsync ct\n        let mutable acquired = 0\n        try\n            while acquired < lockSlots do\n                do! inferenceLock.WaitAsync ct\n                acquired <- acquired + 1\n            do! Task.Delay(10, ct)\n            do! Task.Delay(11, ct)\n            do! Task.Delay(12, ct)\n            do! Task.Delay(13, ct)\n            do! Task.Delay(14, ct)\n            do! Task.Delay(15, ct)\n            let a1 = xs.Length + 1\n            let a2 = a1 + 2\n            return a2\n        finally\n            if acquired > 0 then inferenceLock.Release acquired |> ignore\n            gate.Release() |> ignore\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractAwaitingSuffix _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("let runRest () =", patched)
    Assert.Contains("return! runRest ()", patched)
    // the mutable moves WITH the block, so the closure never captures a
    // foreign one; early returns stay legal inside the new task body
    Assert.Contains("let mutable acquired = 0", patched.Substring(patched.IndexOf "runRest"))
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``a suffix referencing a prefix let-bang binding stays advice`` () =
    // `r` is bound by the remaining prefix; the extracted function would
    // live outside the CE and could not see it
    let source =
        "module Test\nopen System.Threading.Tasks\n"
        + "let f () : Task<int> =\n    task {\n        let! r = Task.FromResult 1\n        do! Task.Delay 1\n        do! Task.Delay 2\n        do! Task.Delay 3\n        do! Task.Delay 4\n        do! Task.Delay 5\n        do! Task.Delay 6\n        do! Task.Delay 7\n        try\n            do! Task.Delay 8\n            do! Task.Delay 9\n            let a1 = r + 1\n            let a2 = a1 + 2\n            let a3 = a2 + 3\n            let a4 = a3 + 4\n            return a4\n        finally\n            ignore r\n    }"

    for s in adviceIn source do
        match s.Kind with
        | TaskStateMachine.AdviceKind.ExtractAwaitingSuffix _ -> Assert.Empty s.Edits
        | _ -> ()

[<Fact>]
let ``an early-return tail extracts as a task-returning local function`` () =
    // branch-shaped returns rule out the plain-closure wrap (a closure has
    // no `return`); the task-returning variant keeps them legal and the
    // outer machine still sheds the lines
    let source =
        "module Test\nlet f (flag: bool) =\n    task {\n"
        + (awaits 8).Replace("    let!", "        let!")
        + "\n        let s1 = x1 + 1\n        let s2 = s1 + 2\n        if flag then\n            return s1\n        else\n            return s1 + s2\n    }"

    let edits =
        adviceIn source
        |> editsOfKind (function
            | TaskStateMachine.AdviceKind.ExtractTail _ -> true
            | _ -> false)

    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("let runTail () = task {", patched)
    Assert.Contains("return! runTail ()", patched)
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
            source.Split('\n')
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
