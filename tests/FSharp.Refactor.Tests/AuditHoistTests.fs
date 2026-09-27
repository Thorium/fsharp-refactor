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
    TaskStateMachine.find tree sourceText None 4 false Set.empty

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
        fsharp
            """
            module Test
            type R = { X: int; Y: int }
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 ->
                        return { X = x
                                 Y = 2 }
                    | _ -> return { X = 0; Y = 0 }
                }
            """

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    // `{` now sits where `return` was, and `Y` moved with `X`
    Assert.Contains(
        fsharp
            """
                            { X = x
                              Y = 2 }
            """,
        patched
    )

    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0029: a list payload continuing below its return keeps its element alignment`` () =
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 ->
                        return [ x
                                 2 ]
                    | _ -> return []
                }
            """

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits

    Assert.Contains(
        fsharp
            """
                            [ x
                              2 ]
            """,
        patched
    )

    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

[<Fact>]
let ``FR0029: a continuation line with less indentation than the strip removes withholds the hoist`` () =
    // a continuation the parser lets undent (a lambda body) would land left
    // of the arm once the payload moves: nothing is emitted rather than a skew
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 ->
                        return [ 1 ] |> List.map (fun v ->
                            v + x)
                    | _ -> return []
                }
            """

    Assert.True(typechecksCleanly source, "the fixture itself must compile")
    Assert.Empty(hoistEditsIn source)

[<Fact>]
let ``FR0029: a single-line record payload still hoists`` () =
    let source =
        fsharp
            """
            module Test
            type R = { X: int; Y: int }
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 -> return { X = x; Y = 2 }
                    | _ -> return { X = 0; Y = 0 }
                }
            """

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits

    Assert.Contains(
        fsharp
            """
            return
                        match c with
                        | 1 -> { X = x; Y = 2 }
            """,
        patched
    )

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
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 ->
                        let s = "first
            second"
                        return s + string x
                    | _ -> return "x"
                }
            """

    Assert.True(typechecksCleanly source, "the fixture itself must compile")
    Assert.Empty(hoistEditsIn source)

[<Fact>]
let ``FR0029: a single-line string in the branch still hoists`` () =
    let source =
        fsharp
            """
            module Test
            let f (c: int) =
                task {
                    let! x = System.Threading.Tasks.Task.FromResult 1
                    match c with
                    | 1 -> return "one"
                    | _ -> return string x
                }
            """

    let edits = hoistEditsIn source
    Assert.NotEmpty edits
    let patched = applyEdits source edits
    Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

// ---- C6: FR0047 editor fix for a Dispose that still uses the field ----

[<Fact>]
let ``FR0047: a Dispose that only cancels the field disposes it after the cancel`` () =
    // `cts.Dispose(); cts.Cancel()` compiles and throws ObjectDisposedException
    let source =
        fsharp
            """
            module Test
            open System
            open System.Threading
            type Service =
                interface
                    inherit IDisposable
                    abstract Run: unit -> unit
                end
            type Impl() =
                let cts = new CancellationTokenSource()
                interface Service with
                    member _.Dispose() = cts.Cancel()
                    member _.Run() = ()
            """

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        let r, _, replacement = s.Fix.Value
        let patched = applyEdit source r replacement

        Assert.Contains(
            fsharp
                """
                member _.Dispose() = cts.Cancel()
                                             cts.Dispose()
                """,
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: a mentioning Dispose whose last line carries a comment offers no fix`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.Threading
            type Impl() =
                let cts = new CancellationTokenSource()
                interface IDisposable with
                    member _.Dispose() = cts.Cancel() // stop the work first
            """

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        Assert.True(s.Fix.IsNone, "a trailing comment would travel onto the appended line")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: a mentioning Dispose closing on a branch offers no fix`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.Threading
            type Impl() =
                let cts = new CancellationTokenSource()
                interface IDisposable with
                    member _.Dispose() =
                        if cts.IsCancellationRequested then () else cts.Cancel()
            """

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.True s.MentionedOnly
        Assert.True(s.Fix.IsNone, "only a plain closing statement takes the appended call")
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0047: an untouched field is still disposed first in Dispose`` () =
    // independent of what the body disposes (a reader over the stream would
    // put the stream last: ObjectDesignTests)
    let source =
        fsharp
            """
            module Test
            open System.IO
            type Holder(path: string) =
                let stream = new FileStream(path, FileMode.Open)
                let log = new FileStream(path + ".log", FileMode.Open)
                interface System.IDisposable with
                    member _.Dispose() =
                        log.Dispose()
            """

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.False s.MentionedOnly
        let r, _, replacement = s.Fix.Value
        let patched = applyEdit source r replacement

        Assert.Contains(
            fsharp
                """
                stream.Dispose()
                            log.Dispose()
                """,
            patched
        )

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
    Assert.True(
        (Text.reindentBlock
            8
            4
            (fsharp
                """
                let s = "a
                b"
                    printfn "%s" s
                """))
            .IsNone
    )

    Assert.True(
        (Text.reindentBlock
            8
            4
            (fsharp
                """
                let s = @"a
                b"
                    printfn "%s" s
                """))
            .IsNone
    )

    Assert.True((Text.reindentBlock 8 4 "let s = $\"\"\"a\nb\"\"\"\n    printfn \"%s\" s").IsNone)

    Assert.True(
        (Text.reindentBlock
            8
            4
            (fsharp
                """
                (* a
                   b *)
                    printfn "x"
                """))
            .IsNone
    )

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
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                try
                    async {
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
                    reraise ()
            """

    match unhandledStartsIn source with
    | [ s ] ->
        Assert.True s.WrappedInTry
        Assert.True(s.TryFix.IsNone, "reraise cannot travel into the computation")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

[<Fact>]
let ``FR0149: a comment outside the moved body and handler offers no move`` () =
    let withComment (line: string) =
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                try
                    async {

            """
        + line
        + fsharp
            """
                        let! _ = work ()
                        ()
                    }
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
            """

    match
        unhandledStartsIn (
            withComment (
                fsharp
                    """
                                // fire and forget

                    """
            )
        )
    with
    | [ s ] -> Assert.True(s.TryFix.IsNone, "the comment beside `async {` would be dropped")
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other

    let afterBrace =
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                try
                    async {
                        let! _ = work ()
                        ()
                    } // detached
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
            """

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
        fsharp
            """
            let work () = async { return 1 }
            let run () =
                try
                    async {
                        let! _ = work ()
                        // done
                        ()
                    }
                    |> Async.Start
                with e ->
                    printfn "%s" e.Message
            """

    match unhandledStartsIn source with
    | [ s ] ->
        match s.TryFix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement

            Assert.Contains(
                fsharp
                    """
                                // done

                    """,
                patched
            )

            Assert.Contains(
                fsharp
                    """
                            with e ->
                                printfn "%s" e.Message
                        }
                        |> Async.Start
                    """,
                patched
            )

            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the move-the-handler-inside fix"
    | other -> failwithf "Expected exactly one unhandled-start note, got %A" other
