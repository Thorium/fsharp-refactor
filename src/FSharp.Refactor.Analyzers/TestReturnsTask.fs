/// Refactoring (FR0142, fix): a test that BLOCKS on async work returns the
/// work instead.
///
///     [<Fact>]                                [<Fact>]
///     let ``reads`` () =                      let ``reads`` () =
///         let res = load () |> Async.RunSynchronously      task {
///         Assert.Equal(1, res.X)        →          let! res = load () |> Async.StartImmediateAsTask
///                                                  Assert.Equal(1, res.X)
///                                              }
///                                              :> System.Threading.Tasks.Task
///
/// xUnit, NUnit 3+ and MSTest all run a `Task`-returning test and await it,
/// so the thread that ran the test is free while the work is in flight
/// instead of parked in `RunSynchronously`, `.Result`, `.Wait()` or
/// `GetAwaiter().GetResult()`. A test method's shape is the framework's
/// business, not a consumer's — no API changes.
///
/// Safety rules:
///   - the binding carries a test attribute of a framework that awaits
///     `Task` (Fact, Theory, Test, TestCase, TestMethod); FsCheck's
///     `Property` and Expecto's builders are not that
///   - no return type annotation, and the body is not already a `task`/
///     `async` computation
///   - only blocking sites on the body's own statement spine move: a
///     `let x = <blocking>` becomes `let! x = <awaitable>`, a discarded
///     `<blocking> |> ignore` becomes `let! _ = <awaitable>`, a `t.Wait()`
///     becomes `do! t` (a `Task<T>` upcast to `Task` first), and a final
///     blocking statement of a unit-returning test becomes `do!`. Anything
///     nested — inside a lambda, a match arm, a nested CE — leaves the
///     test alone
///   - when the whole body is one blocking expression — the xUnit habit
///     `async { ... } |> Async.RunSynchronously` — there is no block at
///     all: the awaitable is the test, `... |> Async.StartImmediateAsTask
///     :> System.Threading.Tasks.Task`
///   - `Task.WaitAll(a, b)` becomes `do! Task.WhenAll(a, b)`, and
///     `Assert.Throws<E>(fun () -> <blocking>)` becomes the framework's
///     async assert with the lambda returning the awaitable — a bind for
///     xUnit and MSTest, a plain replacement for NUnit, whose ThrowsAsync
///     returns the exception itself. The shapes and their proofs live in
///     BlockingSites, shared with FR0049
///   - `Async.RunSynchronously` must be FSharp.Core's, and a `.Result` /
///     `.Wait()` / `GetResult()` receiver must be a Task or ValueTask,
///     both proven by the typed tree
///   - the body starts on its own line under the `=`, so it can be
///     re-indented into the `task { }` block as written
module FSharp.Refactor.TestReturnsTask

open System
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text
open FSharp.Refactor.BlockingSites

type Suggestion =
    {
        /// The test's name, for the message.
        Name: string
        /// The whole body — replaced by the `task { }` block.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// How many blocking sites became binds.
        Sites: int
    }

/// State that OUTLIVES a single test: a module-level `let mutable`, or a
/// `static let mutable` on a type that holds tests.
///
/// A synchronous test owns its thread from start to finish. A
/// `Task`-returning one releases it at every `let!`, and that changes how
/// much really runs at once: xUnit runs test collections in parallel
/// against a bounded pool, so blocking tests are partly serialised by
/// thread starvation alone. Freeing the threads lets collections that
/// always COULD have raced actually do so. The race was latent before this
/// rewrite; the rewrite is what makes it show up, on someone else's
/// machine, intermittently, in a test suite whose whole job is to be
/// trustworthy.
///
/// So a test that touches such a binding is left alone. Nothing here is a
/// correctness fix — it is a test that finishes sooner — and a missed one
/// costs nothing worth having.
let private sharedMutableNames (index: AstIndex.Index) =
    set
        [ for _, decl in index.Decls do
              match decl with
              | SynModuleDecl.Let(bindings = bindings) ->
                  for SynBinding(isMutable = isMutable; headPat = p) in bindings do
                      if isMutable then
                          yield! patBoundNames p
              | SynModuleDecl.Types(typeDefns = defns) ->
                  for SynTypeDefn(typeRepr = repr) in defns do
                      match repr with
                      | SynTypeDefnRepr.ObjectModel(members = objMembers) ->
                          for m in objMembers do
                              match m with
                              | SynMemberDefn.LetBindings(bindings = bs; isStatic = true) ->
                                  for SynBinding(isMutable = isMutable; headPat = p) in bs do
                                      if isMutable then
                                          yield! patBoundNames p
                              | _ -> ()
                      | _ -> ()
              | _ -> () ]

/// Setters whose effect is the PROCESS, not the caller — the same hazard
/// without a name of its own to look for. A test that changes the current
/// directory or an environment variable and reads it back is racing every
/// other test that does, the moment they genuinely overlap.
let private processGlobalSetters =
    [ "Environment.SetEnvironmentVariable"
      "Directory.SetCurrentDirectory"
      "Console.SetOut"
      "Console.SetError"
      "Console.SetIn"
      "CurrentCulture"
      "CurrentUICulture" ]

/// Does this FILE install global state by reflection?
///
/// The hardest version of the shared-state problem, and a real one: a mock
/// harness that swaps out a library's private static holders —
///
///     typeof<Marker>.DeclaringType
///         .GetProperty("contextHolder", BindingFlags.NonPublic ||| BindingFlags.Static)
///         .SetValue(null, lazyReadContext)
///
/// — then puts them back on Dispose. There is no `<-` to find and no name
/// this file declares; the state lives in another assembly, reached
/// through a string. Neither the syntax nor the typed tree can see it.
///
/// `BindingFlags` is the tell, and it is asked of the whole file rather
/// than of one test body: the harness is a helper class, and the tests
/// that depend on it only ever say `use ctx = new MockDatabaseContext(...)`.
/// Every test in such a file is order-dependent whether or not it names
/// the machinery, so none of them is converted.
let private installsGlobalStateByReflection (source: ISourceText) =
    let text = source.GetSubTextString(0, source.Length)
    text.Contains "BindingFlags"

/// Everything this test ASSIGNS to that is not one of its own locals.
///
/// The shared setting is often not in the test file at all — it is a
/// `let mutable` or a settable static property in the library under test,
/// which each test configures its own way. No scan of this file can see
/// that declaration, so the question is asked of the typed tree instead:
/// resolve what the assignment targets and ask whether it is a local. A
/// target that will not resolve counts as shared, since the reason to look
/// was to find out.
///
/// `obj.Property <- v` is left out deliberately: the receiver is usually a
/// local the test just built, and flagging every `sb.Capacity <- 10` would
/// cost far more than it saves.
let private assignsBeyondItself
    (index: AstIndex.Index)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (body: SynExpr)
    =
    index.Exprs
    |> Array.exists (fun (_, e) ->
        match e with
        | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)) when
            not ids.IsEmpty && Range.rangeContainsRange body.Range e.Range
            ->
            let target = List.last ids
            let lineText = source.GetLineString(target.idRange.EndLine - 1)

            match
                check.GetSymbolUseAtLocation(
                    target.idRange.EndLine,
                    target.idRange.EndColumn,
                    lineText,
                    [ target.idText ]
                )
            with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as v -> v.IsModuleValueOrMember
                | _ -> true
            | None -> true
        | _ -> false)

/// Does this test read or write state that outlives it? Either direction
/// counts: a reader races a writer just as a writer races a writer.
///
/// One gap worth naming: a test that only READS a setting declared in
/// another assembly, whose writer lives in a different test file, is not
/// caught — nothing in this file says the two are related. Holding the
/// WRITERS back is what shrinks the exposure, and writers are caught
/// wherever their target is declared.
let private touchesSharedState
    (index: AstIndex.Index)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (shared: Set<string>)
    (body: SynExpr)
    =
    let text = textOfRange source body.Range

    (not shared.IsEmpty
     && shared |> Set.exists (fun name -> Regex.IsMatch(text, identifierPattern name)))
    || processGlobalSetters |> List.exists text.Contains
    || assignsBeyondItself index source check body

let private testAttributes =
    set [ "Test"; "Fact"; "Theory"; "TestCase"; "TestMethod" ]

/// The frameworks known to await a `Task`-returning test. A same-named
/// attribute from anywhere else — a home-grown `TestAttribute` with a
/// reflection runner, say — would get a Task nobody awaits, and every
/// failure inside it would vanish.
let private awaitingFrameworks =
    [ "Xunit."
      "NUnit.Framework."
      "Microsoft.VisualStudio.TestTools.UnitTesting." ]

let private hasTestAttribute (check: FSharpCheckFileResults) (source: ISourceText) (attributes: SynAttributes) =
    attributes
    |> List.collect (fun l -> l.Attributes)
    |> List.exists (fun a ->
        match a.TypeName with
        | SynLongIdent(id = ids) when not ids.IsEmpty ->
            let last = List.last ids
            let n = last.idText

            (testAttributes.Contains n || testAttributes.Contains(n.Replace("Attribute", "")))
            && (let declared =
                    match symbolAt check source last with
                    | Some(:? FSharpEntity as e) -> e.TryFullName
                    | Some(:? FSharpMemberOrFunctionOrValue as v) ->
                        v.DeclaringEntity |> Option.bind (fun e -> e.TryFullName)
                    | _ -> None

                declared
                |> Option.exists (fun full -> awaitingFrameworks |> List.exists full.StartsWith))
        | _ -> false)

/// Does this test's body evaluate to unit? The final expression of a
/// unit-typed body may become a `do!`; a value-typed one has no bind shape.
let private returnsUnit (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    match valueAt check source id with
    | Some v ->
        (try
            isUnitType v.ReturnParameter.Type
         with _ -> // fsharpanalyzer: ignore-line FR0055
             false)
    | None -> false

/// One edit inside the body: (range, replacement).
type private Edit = range * string

/// A statement position: a discarded blocking call becomes `let! _ =`, a
/// unit-typed one `do!`. In FINAL position the blocking result IS the
/// test's result: `do!` when the test returns unit, otherwise there is no
/// bind shape and the rewrite stops.
let private statementEdit
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (bodyIsUnit: bool)
    (e: SynExpr)
    (isLast: bool)
    =
    // a prefix in front of the expression moves its first line right; its
    // continuation lines — a pipe opening a new line at the statement's own
    // column — must follow, or the operator lands offside (Fuuga)
    let prefixed (prefix: string) (text: string) =
        prefix + text.Replace("\n", "\n" + String(' ', prefix.Length))

    match e with
    | Ignored inner ->
        match blockingOf check source inner with
        // a discarded result the typed tree proves unit is a `do!`; any
        // other stays `let! _ =` — no `Async.Ignore` to read past
        | Some b when b.NoBind -> Some [ (b.Site, b.Awaitable) ]
        | Some b when b.UnitResult -> Some [ (e.Range, prefixed "do! " b.DoText) ]
        // a block cannot end on a bind: a final discarded site gets the
        // `()` the `ignore` used to supply, at the statement's own column
        | Some b when isLast ->
            Some [ (e.Range, prefixed "let! _ = " b.Awaitable + $"\n{String(' ', e.Range.StartColumn)}()") ]
        | Some b -> Some [ (e.Range, prefixed "let! _ = " b.Awaitable) ]
        | None -> Some []
    | _ ->
        match blockingOf check source e with
        | Some b when b.NoBind -> Some [ (b.Site, b.Awaitable) ]
        | Some b when b.UnitResult || (isLast && bodyIsUnit) -> Some [ (e.Range, prefixed "do! " b.DoText) ]
        | Some _ when isLast -> None
        | Some b -> Some [ (e.Range, prefixed "let! _ = " b.Awaitable) ]
        | None -> Some []

/// Walk the body's statement spine collecting the edits that turn each
/// blocking statement into a bind. None when a blocking site sits where a
/// bind cannot go (a final expression whose result is not unit).
let rec private spineEdits
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (bodyIsUnit: bool)
    (e: SynExpr)
    (isLast: bool)
    : Edit list option =
    let spineEdits = spineEdits check source bodyIsUnit
    let statementEdit = statementEdit check source bodyIsUnit

    match e with
    | LetOrUseE lou when not lou.IsBang ->
        let own =
            match lou.Bindings with
            // `let mutable x = <blocking>` has no `let! mutable` form, and
            // a local FUNCTION's body is a closure: `let f () = <blocking>`
            // runs when f is called, not here
            | [ SynBinding(isMutable = false; headPat = pat; expr = rhs; trivia = trivia) ] when
                not lou.IsUse
                && (match pat with
                    | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> false
                    | _ -> true)
                ->
                match blockingOf check source rhs with
                // `let x = t.Wait()` binds unit; `let! x = t` would retype
                // x — that site stays as it is
                // NUnit's ThrowsAsync hands back the exception: the call
                // is replaced, the `let` stays
                | Some b when b.NoBind -> Some [ (b.Site, b.Awaitable) ]
                | Some b when not b.BindsValue -> Some []
                | Some b ->
                    // `let x = <blocking>` → `let! x = <awaitable>`; the
                    // `!` moves the expression one column right, and a
                    // continuation line aligned with it must follow
                    let kw = trivia.LeadingKeyword.Range
                    Some [ (kw, "let!"); (b.Site, b.Awaitable.Replace("\n", "\n ")) ]
                | None -> Some []
            | _ -> Some []

        match own, spineEdits lou.Body isLast with
        | Some a, Some b -> Some(a @ b)
        | _ -> None
    | SynExpr.Sequential(expr1 = a; expr2 = b) ->
        match statementEdit a false, spineEdits b isLast with
        | Some x, Some y -> Some(x @ y)
        | _ -> None
    // `match <blocking> with` → `match! <awaitable> with`; the arms are
    // not on the spine, so a blocking site inside one stays
    | SynExpr.Match(expr = scrutinee; trivia = trivia) ->
        match blockingOf check source scrutinee with
        | Some b when b.NoBind -> Some [ (b.Site, b.Awaitable) ]
        | Some b -> Some [ (trivia.MatchKeyword, "match!"); (b.Site, b.Awaitable.Replace("\n", "\n ")) ]
        | None -> Some []
    | last -> statementEdit last true



/// A body holding a lock or a thread-bound handle across the work: after
/// a bind the rest may run on another thread, and `Monitor.Exit` or
/// `ReleaseMutex` from the wrong thread throws.
// thread choreography: a test that hands work to a thread and waits on a
// signal continues on the SAME thread after the wait; `do!` resumes
// wherever the test framework posts (Mibo's thread-affine adaptive graphs:
// four tests failed, eleven turned flaky). The predicate lives in
// BlockingSites, shared with FR0049's boundary note
let private threadBound = BlockingSites.threadBound

/// Does the body already run as a computation, or return a Task?
let private alreadyComputation (body: SynExpr) =
    match stripParens body with
    | SynExpr.App(funcExpr = SynExpr.Ident b; argExpr = SynExpr.ComputationExpr _) ->
        b.idText = "task" || b.idText = "async" || b.idText = "backgroundTask"
    | SynExpr.Upcast _ -> true
    | _ -> false

/// Apply edits to the body text (bottom-up), re-indent every line by four,
/// and wrap in `task { ... } :> System.Threading.Task` at the body's own
/// indentation.
let private wrapBody (source: ISourceText) (bodyRange: range) (edits: Edit list) =
    let bodyText = textOfRange source bodyRange
    let start = bodyRange.Start

    // an edit's position relative to the body text: line starts are read
    // off the body text itself (a `\r` before the break stays inside its
    // line), and the first line begins at the body's own column
    let lineStarts =
        let starts = ResizeArray<int>([ 0 ])

        for i in 0 .. bodyText.Length - 1 do
            if bodyText.[i] = '\n' then
                starts.Add(i + 1)

        starts

    let offsetOf (p: pos) =
        let relativeLine = p.Line - start.Line

        let column =
            if relativeLine = 0 then
                p.Column - start.Column
            else
                p.Column

        lineStarts.[relativeLine] + column

    let edited =
        edits
        |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
        |> List.fold
            (fun (text: string) (r, replacement) ->
                let s = offsetOf r.Start
                let e = offsetOf r.End
                text.Substring(0, s) + replacement + text.Substring e)
            bodyText

    let indent = String(' ', start.Column)
    let inner = indent + "    "

    let lines =
        edited.Replace("\r\n", "\n").Split '\n'
        |> Array.mapi (fun i line ->
            // lines after the first carry their original leading columns;
            // the first sits at the body column, which the text lost
            if System.String.IsNullOrWhiteSpace line then ""
            elif i = 0 then inner + line
            else "    " + line)

    // the upcast shares the closing brace's line: on a line of its own it
    // is offside of the `task` expression and does not parse
    String.concat
        "\n"
        ([ indent + "task {" ]
         @ List.ofArray lines
         @ [ indent + "} :> System.Threading.Tasks.Task" ])

/// Every test binding in the file: module-level lets and type members.
let private testBindings (index: AstIndex.Index) =
    [ for _, decl in index.Decls do
          match decl with
          | SynModuleDecl.Let(bindings = bindings) ->
              for b in bindings do
                  yield b
          | SynModuleDecl.Types(typeDefns = defns) ->
              for SynTypeDefn(members = members; typeRepr = repr) in defns do
                  for m in members do
                      match m with
                      | SynMemberDefn.Member(memberDefn = b) -> yield b
                      | _ -> ()

                  match repr with
                  | SynTypeDefnRepr.ObjectModel(members = objMembers) ->
                      for m in objMembers do
                          match m with
                          | SynMemberDefn.Member(memberDefn = b) -> yield b
                          | _ -> ()
                  | _ -> ()
          | _ -> () ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree
        let shared = sharedMutableNames index
        let reflectionHarness = installsGlobalStateByReflection source

        [ for binding in testBindings index do
              match binding with
              | SynBinding(attributes = attributes; headPat = headPat; returnInfo = None; expr = body) when
                  hasTestAttribute check source attributes
                  && not (alreadyComputation body)
                  && not (threadBound source body)
                  && not reflectionHarness
                  && not (touchesSharedState index source check shared body)
                  ->
                  let nameIdent =
                      match headPat with
                      | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
                      | _ -> None

                  // the body must open on its own line, under the header,
                  // so its lines re-indent as written
                  let ownLine =
                      body.Range.StartLine > headPat.Range.EndLine
                      && (source.GetLineString(body.Range.StartLine - 1)).Substring(0, body.Range.StartColumn).Trim() = ""

                  match nameIdent with
                  | Some id ->
                      let bodyIsUnit = returnsUnit check source id

                      // a comment trailing the last expression belongs to
                      // that line; left outside the replaced range it
                      // resurfaced after `} :> Task` (Mibo's Tests.fs)
                      let bodyRange =
                          let lastLine = source.GetLineString(body.Range.EndLine - 1)
                          let rest = lastLine.Substring(min body.Range.EndColumn lastLine.Length)

                          if rest.TrimStart().StartsWith "//" then
                              Range.mkRange
                                  body.Range.FileName
                                  body.Range.Start
                                  (Position.mkPos body.Range.EndLine lastLine.Length)
                          else
                              body.Range

                      let suggestion replacement sites =
                          { Name = id.idText
                            Range = bodyRange
                            OriginalText = textOfRange source bodyRange
                            ReplacementText = replacement
                            Sites = sites }

                      match blockingOf check source body with
                      // the whole body blocks on one thing — `async { ... }
                      // |> Async.RunSynchronously` — so the awaitable IS the
                      // test: no block, just the upcast
                      | Some b when not b.NoBind && (b.UnitResult || bodyIsUnit) ->
                          let trailing =
                              (textOfRange source bodyRange).Substring((textOfRange source body.Range).Length)

                          yield suggestion $"{b.Awaitable} :> System.Threading.Tasks.Task{trailing}" 1
                      | Some _ -> ()
                      | None ->
                          // re-indenting the body would also re-indent the
                          // inside of a string literal that spans lines —
                          // a triple-quoted expected value, say — and that
                          // compiles with different content
                          let spansLinesInBody (r: range) =
                              r.StartLine <> r.EndLine && Range.rangeContainsRange body.Range r

                          let multiLineString =
                              (index.Exprs
                               |> Seq.exists (fun (_, e) ->
                                   match e with
                                   | SynExpr.Const(SynConst.String _, r)
                                   | SynExpr.Const(SynConst.Bytes _, r)
                                   | SynExpr.InterpolatedString(range = r) -> spansLinesInBody r
                                   | _ -> false))
                              || (index.Pats
                                  |> Seq.exists (fun (_, p) ->
                                      match p with
                                      | SynPat.Const(SynConst.String _, r)
                                      | SynPat.Const(SynConst.Bytes _, r) -> spansLinesInBody r
                                      | _ -> false))

                          if ownLine && not multiLineString then
                              match spineEdits check source bodyIsUnit body true with
                              | Some edits when not edits.IsEmpty ->
                                  let sites =
                                      edits |> List.filter (fun (_, t) -> t <> "let!" && t <> "match!") |> List.length

                                  yield
                                      suggestion
                                          ((wrapBody source bodyRange edits).Substring body.Range.StartColumn)
                                          sites
                              | _ -> ()
                  | None -> ()
              | _ -> () ]
