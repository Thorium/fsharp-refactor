/// Audit fixes for the exception rules (report 06-exceptions): FR0044's
/// closure and rebinding blind spots, FR0055's unbound log binder, impure
/// guard operands and failure-carrying tuples, FR0151's interpolated
/// read, statement-position rethrow and one-message double fix.
module FSharp.Refactor.Tests.AuditExceptionTests

open Xunit
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// A negative test on a typed rule proves nothing when the input has a
/// type error: every typed rule returns [] on errors. So the input is
/// checked first.
let private assertTypechecks (source: string) =
    Assert.True(typechecksCleanly source, $"Test input does not typecheck:\n%s{source}")

// ---- FR0044 Reraise: A5 rebinding, B11 closures ----

let private reraiseIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    Reraise.find tree sourceText checkResults

let private assertReraise (source: string) =
    match reraiseIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range "reraise ()"
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one reraise suggestion, got %d: %A" (List.length other) other

let private assertNoReraise (source: string) =
    assertTypechecks source
    Assert.Empty(reraiseIn source)

[<Fact>]
let ``FR0044: a match arm rebinding the exception name raises the inner one`` () =
    // the report's repro: `reraise ()` compiles here but rethrows the OUTER
    // exception, where `raise ex` threw the unwrapped one
    assertNoReraise
        "let f (act: unit -> int) (unwrap: exn -> exn option) =\n    try act ()\n    with ex ->\n        match unwrap ex with\n        | Some ex -> raise ex\n        | None -> 0"

[<Fact>]
let ``FR0044: a for loop rebinding the exception name raises the loop's one`` () =
    assertNoReraise
        "let f (act: unit -> int) (inner: exn -> exn list) =\n    try act ()\n    with ex ->\n        for ex in inner ex do\n            raise ex\n        0"

[<Fact>]
let ``FR0044: a function clause rebinding the exception name stays put`` () =
    assertNoReraise
        "let f (act: unit -> int) (unwrap: exn -> exn option) =\n    try act ()\n    with ex ->\n        unwrap ex |> (function Some ex -> raise ex | None -> 0)"

[<Fact>]
let ``FR0044: a match arm on something else still gets reraise`` () =
    // a match inside the handler is not a closure: reraise () compiles there
    assertReraise
        "let f (act: unit -> int) (code: int) =\n    try act ()\n    with ex ->\n        match code with\n        | 1 -> raise ex\n        | _ -> 0"

[<Fact>]
let ``FR0044: a local function in the handler is a closure`` () =
    // `let helper () = reraise ()` is FS0413: not directly in the handler
    assertNoReraise
        "let f (act: unit -> int) =\n    try act ()\n    with ex ->\n        let helper () = raise ex\n        helper ()"

[<Fact>]
let ``FR0044: an object-expression member in the handler is a closure`` () =
    assertNoReraise
        "let f (act: unit -> int) =\n    try act ()\n    with ex ->\n        let d = { new System.IDisposable with member _.Dispose() = raise ex }\n        d.Dispose()\n        0"

[<Fact>]
let ``FR0044: a lazy in the handler is a closure`` () =
    assertNoReraise
        "let f (act: unit -> int) =\n    try act ()\n    with ex ->\n        let l = lazy (raise ex)\n        l.Value"

[<Fact>]
let ``FR0044: a list comprehension in the handler is a closure`` () =
    assertNoReraise
        "let f (act: unit -> int) =\n    try act ()\n    with ex ->\n        [ for i in 1 .. 2 -> raise ex ] |> List.sum"

[<Fact>]
let ``FR0044: a plain value binding and an if in the handler still get reraise`` () =
    // a value binding is no closure, and an if is fine: the direct shape
    // keeps its offer
    assertReraise
        "let f (act: unit -> int) (strict: bool) =\n    try act ()\n    with ex ->\n        let msg = ex.Message\n        if strict then raise ex else msg.Length"

// ---- FR0055 SwallowedException: C1 log binder, C2 guard purity, E1 failure slots ----

let private swallowedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SwallowedException.find tree sourceText (Some checkResults)

let private guardOf (s: SwallowedException.Suggestion) =
    s.Offers |> List.tryFind (fun o -> o.Label.StartsWith "Fix: guard")

let private assertNoGuard (source: string) =
    assertTypechecks source

    match swallowedIn source with
    | [ s ] -> Assert.True((guardOf s).IsNone, $"no guard expected, got %A{guardOf s}")
    | other -> failwithf "Expected one finding, got %A" other

let private assertGuard (source: string) (expected: string) =
    match swallowedIn source with
    | [ s ] ->
        match guardOf s with
        | Some o ->
            let r, _, replacement = List.exactlyOne o.Edits
            Assert.Equal(expected, replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the guard offer"
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: an option Value operand can throw, so no guard`` () =
    // the report's repro: `None.Value` escapes where the catch returned 0
    assertNoGuard "module Test\nlet ratio (total: int option) (count: int) = try total.Value / count with _ -> 0"

[<Fact>]
let ``FR0055: a string Length operand is a property, so no guard`` () =
    assertNoGuard "module Test\nlet ratio (s: string) (count: int) = try s.Length / count with _ -> 0"

[<Fact>]
let ``FR0055: under open Checked the arithmetic itself throws, so no guard`` () =
    assertNoGuard
        "module Test\nopen Microsoft.FSharp.Core.Operators.Checked\nlet ratio (a: int) (b: int) = try a * 2 / b with _ -> 0"

[<Fact>]
let ``FR0055: decimal arithmetic overflows, so no guard`` () =
    assertNoGuard "module Test\nlet ratio (a: decimal) (b: decimal) = try a / b with _ -> 0m"

[<Fact>]
let ``FR0055: plain parameters still get the guard`` () =
    assertGuard "module Test\nlet ratio (a: int) (b: int) = try a / b with _ -> 0" "if b = 0 then 0 else a / b"

[<Fact>]
let ``FR0055: record fields are pure operands and keep the guard`` () =
    assertGuard
        "module Test\ntype R = { Total: int; Count: int }\nlet ratio (r: R) = try r.Total / r.Count with _ -> 0"
        "if r.Count = 0 then 0 else r.Total / r.Count"

[<Fact>]
let ``FR0055: a tuple carrying Error reports the failure, not a disguised result`` () =
    // the report's repro: `Error "step failed"` IS the failure report
    let source =
        "module Test\nlet step (state: int) (f: int -> int * Result<int, string>) =\n    try f state\n    with _ -> (state, Error \"step failed\")"

    assertTypechecks source
    Assert.Empty(swallowedIn source)

[<Fact>]
let ``FR0055: Choice2Of2 and Failure slots carry the failure too`` () =
    let source =
        "module Test\nlet a (state: int) (f: int -> int * Choice<int, string>) =\n    try f state\n    with _ -> (state, Choice2Of2 \"\")\nlet b (state: int) (f: int -> int * exn) =\n    try f state\n    with _ -> (state, Failure \"\")"

    assertTypechecks source
    Assert.Empty(swallowedIn source)

[<Fact>]
let ``FR0055: a tuple carrying a zero is still a disguised result`` () =
    let source =
        "module Test\nlet step (state: int) (f: int -> int * int) =\n    try f state\n    with _ -> (state, 0)"

    match swallowedIn source with
    | [ s ] -> Assert.Equal(Some "(state, 0)", s.FallbackText)
    | other -> failwithf "Expected one finding, got %A" other

let private applyOffer (source: string) (offer: SwallowedException.Offer) =
    offer.Edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

let private logOfferIn (source: string) =
    match swallowedIn source with
    | [ s ] -> s.Offers |> List.tryFind (fun o -> o.Label.StartsWith "Alternative: log it")
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0055: the log offer on a bare Exception type test binds the exception`` () =
    // the report's repro: the log line said `ex`, the pattern bound nothing
    let source =
        "module Test\ntype Logger() =\n    member _.LogError(ex: exn, message: string, [<System.ParamArray>] args: obj[]) = ()\nlet work (logger: Logger) (id: int) =\n    logger.LogError(null, \"started {Id}\", id)\n    try printfn \"%d\" id\n    with :? System.Exception -> ()"

    assertTypechecks source

    match logOfferIn source with
    | Some offer ->
        let patched = applyOffer source offer
        Assert.Contains("with :? System.Exception as ex ->", patched)
        Assert.Contains("logger.LogError(ex, ", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | None -> failwith "Expected the log offer"

[<Fact>]
let ``FR0055: the log offer on a wildcard still binds and typechecks`` () =
    let source =
        "module Test\ntype Logger() =\n    member _.LogError(ex: exn, message: string, [<System.ParamArray>] args: obj[]) = ()\nlet work (logger: Logger) (id: int) =\n    logger.LogError(null, \"started {Id}\", id)\n    try printfn \"%d\" id\n    with _ -> ()"

    match logOfferIn source with
    | Some offer ->
        let patched = applyOffer source offer
        Assert.Contains("with ex ->", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | None -> failwith "Expected the log offer"

[<Fact>]
let ``FR0055: the log offer picks a binder the function does not already use`` () =
    // `ex` is the int parameter: binding the exception to it would make the
    // log line's `{ex}` parameter the exception
    let source =
        "module Test\ntype Logger() =\n    member _.LogError(ex: exn, message: string, [<System.ParamArray>] args: obj[]) = ()\nlet work (logger: Logger) (ex: int) =\n    logger.LogError(null, \"started {Ex}\", ex)\n    try printfn \"%d\" ex\n    with _ -> ()"

    match logOfferIn source with
    | Some offer ->
        let patched = applyOffer source offer
        Assert.Contains("with exn ->", patched)
        Assert.Contains("logger.LogError(exn, ", patched)
        Assert.Contains("exn.Message, \"work\", ex)", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | None -> failwith "Expected the log offer"

// ---- FR0151 ExceptionDetail: C3 interpolated read, C4 rethrow position and two messages ----

let private exceptionDetailIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ExceptionDetail.find tree sourceText checkResults

let private handlerOf (body: string) =
    "module M\nopen System\nopen System.Reflection\nlet run (a: Assembly) (strict: bool) (log: string -> unit) : Type[] =\n    try\n        a.GetTypes()\n    with :? ReflectionTypeLoadException as e ->\n"
    + body

[<Fact>]
let ``FR0151: a Message read inside an interpolated string is reported but not fixed`` () =
    // the report's repro: the replacement carries `"; "`, which a `$"..."`
    // hole may not hold (FS3373)
    let source = handlerOf "        log $\"load failed: {e.Message}\"\n        [||]"
    assertTypechecks source

    match exceptionDetailIn source with
    | [ s ] -> Assert.True(s.Fix.IsNone, "no Message fix inside a $\"...\" hole")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a plain Message read keeps its fix`` () =
    let source = handlerOf "        log e.Message\n        [||]"

    match exceptionDetailIn source with
    | [ s ] ->
        match s.Fix with
        | Some(r, _, replacement) ->
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the Message fix"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a statement-position rethrow gets no carry-on fix`` () =
    // the report's repro: `if strict then <Type[]>` mid-body is FS0001
    let source =
        handlerOf "        log e.Message\n        if strict then reraise ()\n        [||]"

    assertTypechecks source

    match exceptionDetailIn source with
    | [ s ] ->
        Assert.True(s.AlternativeFix.IsNone, "no carry-on fix for a statement-position rethrow")
        Assert.True(s.Fix.IsSome, "the Message fix stays")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a deliberate wrap is not a rethrow`` () =
    let source =
        handlerOf "        log e.Message\n        raise (InvalidOperationException(\"types\", e))"

    assertTypechecks source

    match exceptionDetailIn source with
    | [ s ] -> Assert.True(s.AlternativeFix.IsNone, "a wrap changes the thrown type: no carry-on fix")
    | other -> failwithf "Expected one suggestion, got %A" other

let private assertCarryOn (source: string) =
    match exceptionDetailIn source with
    | [ s ] ->
        match s.AlternativeFix with
        | Some(r, _, replacement) ->
            Assert.Contains("e.Types", replacement)
            let patched = applyEdit source r replacement
            Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
        | None -> failwith "Expected the carry-on alternative fix"
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0151: a tail reraise still gets the carry-on fix`` () =
    assertCarryOn (handlerOf "        log e.Message\n        reraise ()")

[<Fact>]
let ``FR0151: a tail raise of the handler's own binder gets the carry-on fix`` () =
    assertCarryOn (handlerOf "        log e.Message\n        raise e")

[<Fact>]
let ``FR0151: a rethrow in the tail if's branch gets the carry-on fix`` () =
    assertCarryOn (handlerOf "        log e.Message\n        if strict then reraise () else [||]")

let private checker = FSharpChecker.Create()

/// The editor analyzer's messages for a script, through the SDK context the
/// hosts build.
let private editorMessages (source: string) (analyzer: EditorContext -> Async<Message list>) =
    let sourceText = SourceText.ofString source

    let options, _ =
        checker.GetProjectOptionsFromScript("Test.fsx", sourceText, assumeDotNetFramework = false)
        |> Async.RunSynchronously

    let parseResults, answer =
        checker.ParseAndCheckFileInProject("Test.fsx", source.GetHashCode(), sourceText, options)
        |> Async.RunSynchronously

    let checkResults =
        match answer with
        | FSharpCheckFileAnswer.Succeeded r -> r
        | FSharpCheckFileAnswer.Aborted -> failwith "typechecking aborted"

    let context: EditorContext =
        { FileName = "Test.fsx"
          SourceText = sourceText
          ParseFileResults = parseResults
          // no keepAssemblyContents on this checker, and the rule reads
          // the check results, not the typed tree
          TypedTree = None
          CheckFileResults = Some checkResults
          CheckProjectResults = None
          ProjectOptions = AnalyzerProjectOptions.BackgroundCompilerOptions options
          AnalyzerIgnoreRanges = Map.empty }

    analyzer context |> Async.RunSynchronously

[<Fact>]
let ``FR0151: the carry-on and the Message fix are two messages, carry-on first`` () =
    // an editor applies every fix of a message as one action: both in one
    // message would rewrite the handler twice
    let source = handlerOf "        log e.Message\n        reraise ()"

    let messages =
        editorMessages source Analyzers.exceptionDetailEditorAnalyzer
        |> List.filter (fun m -> m.Code = "FR0151")

    match messages with
    | [ carryOn; detail ] ->
        let carryOnFix = List.exactlyOne carryOn.Fixes
        Assert.Contains("e.Types", carryOnFix.ToText)
        let detailFix = List.exactlyOne detail.Fixes
        Assert.Contains("LoaderExceptions", detailFix.ToText)
        Assert.StartsWith("Alternative:", detail.Message)
    | other -> failwithf "Expected two FR0151 messages, got %A" other
