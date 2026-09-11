/// Audit fixes: FR0029's return hoist over a payload that continues below
/// its keyword line (A2) or a branch holding a string literal spanning
/// lines (B1); FR0047's editor fix for a Dispose that still uses the field
/// (C6); `Text.reindentBlock`'s literal guard and FR0149's handler move (C7).
module FSharp.Refactor.Tests.AuditHoistTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- helpers ----

let private adviceIn (source: string) =
    let tree, sourceText = parse source
    TaskStateMachine.find tree sourceText 4 false Set.empty

let private hoistEditsIn (source: string) =
    adviceIn source
    |> List.collect (fun s ->
        match s.Kind with
        | TaskStateMachine.AdviceKind.HoistReturn _ -> s.Edits
        | _ -> [])

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

let private designIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ObjectDesign.find true tree sourceText checkResults

let private unhandledStartsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AsyncIgnore.findUnhandledStart tree sourceText checkResults

// ---- A2: FR0029 return hoist, payload continuing below the keyword line ----

[<Fact>]
let ``FR0029: a record payload continuing below its return keeps its field alignment`` () =
    // stripping `return ` pulled the first payload line 7 columns left while
    // its continuation stayed put: `Y = 2` then read as an argument of `x`
    let source =
        "module Test\ntype R = { X: int; Y: int }\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 ->\n            return { X = x\n                     Y = 2 }\n        | _ -> return { X = 0; Y = 0 }\n    }"

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    // `{` now sits where `return` was, and `Y` moved with `X`
    Assert.Contains("                { X = x\n                  Y = 2 }", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0029: a list payload continuing below its return keeps its element alignment`` () =
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 ->\n            return [ x\n                     2 ]\n        | _ -> return []\n    }"

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("                [ x\n                  2 ]", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0029: a continuation line with less indentation than the strip removes withholds the hoist`` () =
    // a continuation the parser lets undent (a lambda body) would land left
    // of the arm once the payload moves: nothing is emitted rather than a skew
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 ->\n            return [ 1 ] |> List.map (fun v ->\n                v + x)\n        | _ -> return []\n    }"

    Assert.True(typechecksCleanly source, "the fixture itself must compile")
    Assert.Empty(hoistEditsIn source)

[<Fact>]
let ``FR0029: a single-line record payload still hoists`` () =
    let source =
        "module Test\ntype R = { X: int; Y: int }\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 -> return { X = x; Y = 2 }\n        | _ -> return { X = 0; Y = 0 }\n    }"

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.Contains("return\n            match c with\n            | 1 -> { X = x; Y = 2 }", patched)
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- B1: FR0029 return hoist over a string literal spanning lines ----

[<Fact>]
let ``FR0029: a triple-quoted string spanning lines inside the branch withholds the hoist`` () =
    // every line of the branch gains four columns - inside the literal that
    // is a change to the string's value, and the program still compiles
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 -> return \"\"\"first\nsecond\"\"\"\n        | _ -> return \"x\"\n    }"

    Assert.True(typechecksCleanly source, "the fixture itself must compile")
    Assert.Empty(hoistEditsIn source)

[<Fact>]
let ``FR0029: a plain string spanning lines inside the branch withholds the hoist`` () =
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 ->\n            let s = \"first\nsecond\"\n            return s + string x\n        | _ -> return \"x\"\n    }"

    Assert.True(typechecksCleanly source, "the fixture itself must compile")
    Assert.Empty(hoistEditsIn source)

[<Fact>]
let ``FR0029: a single-line string in the branch still hoists`` () =
    let source =
        "module Test\nlet f (c: int) =\n    task {\n        let! x = System.Threading.Tasks.Task.FromResult 1\n        match c with\n        | 1 -> return \"one\"\n        | _ -> return string x\n    }"

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- C6: FR0047 editor fix for a Dispose that still uses the field ----

[<Fact>]
let ``FR0047: a Dispose that only cancels the field disposes it after the cancel`` () =
    // `cts.Dispose(); cts.Cancel()` compiles and throws ObjectDisposedException
    let source =
        "module Test\nopen System\nopen System.Threading\ntype Service =\n    interface\n        inherit IDisposable\n        abstract Run: unit -> unit\n    end\ntype Impl() =\n    let cts = new CancellationTokenSource()\n    interface Service with\n        member _.Dispose() = cts.Cancel()\n        member _.Run() = ()"

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        let r, _, replacement = s.Fix.Value
        let patched = applyEdit source r replacement
        Assert.Contains("member _.Dispose() = cts.Cancel()\n                             cts.Dispose()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: a mentioning Dispose whose last line carries a comment offers no fix`` () =
    let source =
        "module Test\nopen System\nopen System.Threading\ntype Impl() =\n    let cts = new CancellationTokenSource()\n    interface IDisposable with\n        member _.Dispose() = cts.Cancel() // stop the work first"

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        Assert.True(s.Fix.IsNone, "a trailing comment would travel onto the appended line")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: a mentioning Dispose closing on a branch offers no fix`` () =
    let source =
        "module Test\nopen System\nopen System.Threading\ntype Impl() =\n    let cts = new CancellationTokenSource()\n    interface IDisposable with\n        member _.Dispose() =\n            if cts.IsCancellationRequested then () else cts.Cancel()"

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        Assert.True(s.Fix.IsNone, "only a plain closing statement takes the appended call")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: an untouched field is still disposed first in Dispose`` () =
    let source =
        "module Test\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let reader = new StreamReader(stream)\n    interface System.IDisposable with\n        member _.Dispose() =\n            reader.Dispose()"

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.False s.MentionedOnly
        let r, _, replacement = s.Fix.Value
        let patched = applyEdit source r replacement
        Assert.Contains("stream.Dispose()\n            reader.Dispose()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one undisposed-field finding, got %A" other

// ---- C7: Text.reindentBlock literal guard ----

[<Fact>]
let ``reindentBlock refuses a block whose continuation is inside a triple-quoted string`` () =
    Assert.True(
        (Text.reindentBlock 8 4 "let banner = \"\"\"line one\nline two\"\"\"\n    printfn \"%s\" banner").IsNone
    )

[<Fact>]
let ``reindentBlock refuses plain and verbatim strings spanning lines and block comments`` () =
    Assert.True((Text.reindentBlock 8 4 "let s = \"a\nb\"\n    printfn \"%s\" s").IsNone)
    Assert.True((Text.reindentBlock 8 4 "let s = @\"a\nb\"\n    printfn \"%s\" s").IsNone)
    Assert.True((Text.reindentBlock 8 4 "let s = $\"\"\"a\nb\"\"\"\n    printfn \"%s\" s").IsNone)
    Assert.True((Text.reindentBlock 8 4 "(* a\n   b *)\n    printfn \"x\"").IsNone)

[<Fact>]
let ``reindentBlock still moves a block of single-line literals, chars and line comments`` () =
    // a `"` in a line comment or a `'"'` char opens no string
    Assert.Equal(
        Some "        let q = '\"' // say \"hi\"\n        printfn \"%c\" q",
        Text.reindentBlock 8 4 "let q = '\"' // say \"hi\"\n    printfn \"%c\" q"
    )

// ---- C7: FR0149 handler move ----

[<Fact>]
let ``FR0149: a handler that reraises offers no move`` () =
    // inside the computation the handler is a closure: FS0413
    let source =
        "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message\n        reraise ()"

    match unhandledStartsIn source with
    | [ s ] ->
        Assert.True s.WrappedInTry
        Assert.True(s.TryFix.IsNone, "reraise cannot travel into the computation")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a comment outside the moved body and handler offers no move`` () =
    let withComment (line: string) =
        "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n"
        + line
        + "            let! _ = work ()\n            ()\n        }\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn (withComment "            // fire and forget\n") with
    | [ s ] -> Assert.True(s.TryFix.IsNone, "the comment beside `async {` would be dropped")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

    let afterBrace =
        "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            ()\n        } // detached\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn afterBrace with
    | [ s ] -> Assert.True(s.TryFix.IsNone, "the comment after `}` would be dropped")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a body holding a string spanning lines offers no move`` () =
    let source =
        "let run () =\n    try\n        async {\n            let banner = \"\"\"line one\nline two\"\"\"\n            printfn \"%s\" banner\n        }\n        |> Async.Start\n    with e -> printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] -> Assert.True(s.TryFix.IsNone, "re-indenting the body would edit the literal")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a printfn handler with a comment inside the body still moves`` () =
    let source =
        "let work () = async { return 1 }\nlet run () =\n    try\n        async {\n            let! _ = work ()\n            // done\n            ()\n        }\n        |> Async.Start\n    with e ->\n        printfn \"%s\" e.Message"

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement
            Assert.Contains("            // done\n", patched)

            Assert.Contains(
                "        with e ->\n            printfn \"%s\" e.Message\n    }\n    |> Async.Start",
                patched
            )

            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other
