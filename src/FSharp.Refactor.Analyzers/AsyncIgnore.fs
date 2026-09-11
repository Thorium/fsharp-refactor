/// Diagnostic (correctness): `ignore` applied to an Async value discards the
/// computation without ever running it.
///
///     comp |> ignore      // comp never executes — almost always a bug
///     ignore comp
///
/// No automatic fix is offered: the right repair depends on intent —
/// `do! comp |> Async.Ignore` awaits and discards the result,
/// `Async.Start comp` fires and forgets — and only the author knows which.
///
/// Typed rule: the operand must be a simple identifier whose type resolves to
/// FSharp.Core's Async<'T> (shadowing-proof); the file must have no type
/// errors.
module FSharp.Refactor.AsyncIgnore

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        /// The discarded computation's name, for the message.
        Name: string
        /// A ValueTask rather than an Async: it is already running, but
        /// its outcome — result and failure alike — is lost, and a pooled
        /// ValueTask must be consumed exactly once.
        IsValueTask: bool
    }

[<Literal>]
let private AsyncTypeName = "Microsoft.FSharp.Control.FSharpAsync`1"

[<Literal>]
let private ValueTaskTypeName = "System.Threading.Tasks.ValueTask"

/// `ignore x` / `x |> ignore` — the operand, parens stripped.
[<return: Struct>]
let private (|Ignored|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = IdentName "ignore"; argExpr = arg) -> ValueSome(stripParens arg)
    | PipeApp(arg, IdentName "ignore") -> ValueSome(stripParens arg)
    | _ -> ValueNone

/// The head identifier of an application spine and how many arguments were
/// applied to it: `f a b` → (f, 2); `x.M(a)` → (M, 1); `x |> g` → (g, 1).
/// Real fire-and-forget bugs are written as a direct call ignored —
/// `saveUserAsync user |> ignore` — almost never as a named binding.
[<TailCall>]
let rec private headAndDepth (depth: int) (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner) -> headAndDepth depth inner
    // a pipe IS an App(isInfix = false) at the outer node, so this arm must
    // come first or `x |> makeAsync` dead-ends in the operator application
    | PipeApp(_, rhs) -> headAndDepth (depth + 1) rhs
    | SynExpr.App(isInfix = false; funcExpr = f) -> headAndDepth (depth + 1) f
    | SynExpr.TypeApp(expr = inner) -> headAndDepth depth inner
    | SynExpr.Ident id -> ValueSome(id, depth)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids, depth)
    | _ -> ValueNone

/// Find Async values discarded with plain ignore.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    // Async (cold: never runs) or ValueTask (hot, but single-consumption
    // and its failure unobservable); a plain Task discarded is a different
    // conversation, and not this rule's
    let discardable (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t

            if not t.HasTypeDefinition then
                ValueNone
            else
                match t.TypeDefinition.TryFullName with
                | Some AsyncTypeName -> ValueSome false
                | Some full when full = ValueTaskTypeName || full = ValueTaskTypeName + "`1" -> ValueSome true
                | _ -> ValueNone
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            ValueNone

    let resolve (ident: Ident) =
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value -> ValueSome value
            | _ -> ValueNone
        | None -> ValueNone

    // a bare name: its own type is Async. An application: the head must be
    // FULLY applied (partial application ignores a function, a different
    // mistake) and its final return type Async.
    let ignoredComputation (operand: SynExpr) =
        match operand with
        | SynExpr.Ident ident ->
            match resolve ident with
            | ValueSome value ->
                match discardable value.FullType with
                | ValueSome isValueTask -> ValueSome(ident, isValueTask)
                | ValueNone -> ValueNone
            | ValueNone -> ValueNone
        | SynExpr.App _ ->
            match headAndDepth 0 operand with
            | ValueSome(headIdent, applied) when applied > 0 ->
                match resolve headIdent with
                | ValueSome value ->
                    // groups must be KNOWN and consumed: a function-typed
                    // PARAMETER reports zero groups while its ReturnParameter
                    // may still be the final Async — trusting that would flag
                    // a partial application of it
                    let fullyApplied =
                        try
                            let groups = value.CurriedParameterGroups.Count
                            groups > 0 && groups <= applied
                        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                            false

                    if fullyApplied then
                        match discardable value.ReturnParameter.Type with
                        | ValueSome isValueTask -> ValueSome(headIdent, isValueTask)
                        | ValueNone -> ValueNone
                    else
                        ValueNone
                | ValueNone -> ValueNone
            | _ -> ValueNone
        | _ -> ValueNone

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | Ignored operand ->
                    match ignoredComputation operand with
                    | ValueSome(ident, isValueTask) ->
                        suggestions.Add
                            { Range = expr.Range
                              OriginalText = textOfRange source expr.Range
                              Name = ident.idText
                              IsValueTask = isValueTask }
                    | ValueNone -> ()
                | _ -> () }

    if OptionModule.hasErrors check then
        []
    else
        AstIndex.replay collector parseTree
        List.ofSeq suggestions

/// FR0149 (correctness, note): a computation handed to `Async.Start` runs
/// on the thread pool with NOBODY to observe its failure — no caller to
/// return to, no Task to fault, no awaiter to rethrow into.
///
/// Measured, not assumed (fsi, FSharp.Core 9):
///
///     try async { failwith "y" } |> Async.Start with _ -> ()
///     // Unhandled exception. System.Exception: y  — the process DIES
///
/// FSharp.Core rethrows the failure through `ExceptionDispatchInfo` on the
/// pool thread, where an unhandled exception terminates the process. It is
/// not a silent stop, and the `try/with` around the CALL catches nothing:
/// the work never runs on that thread. `Async.StartImmediate` differs only
/// up to the first await — before it the exception does surface at the
/// call site, past it the pool has it and the process dies the same way.
/// For contrast, `Async.StartAsTask` puts the failure in the Task and
/// `Async.RunSynchronously` raises it on the calling thread; both are
/// observable, so neither is reported here.
///
/// CloudAgent's message listener is the shape in the wild: an exception
/// out of `GetNextAgent` takes the process with it, while the
/// `IDisposable` it handed back still looks alive.
///
/// Handled means the failure has somewhere to go:
///   - the started body IS a `try ... with` — one that covers everything
///     the computation does, not a fragment of it, or
///   - `Async.Catch` appears in the body AND a match handles both
///     `Choice1Of2` and `Choice2Of2`. Producing the `Choice` is not
///     handling it; only consuming it is, so an `Async.Catch` whose
///     result is dropped still reports.
///
/// Only a body this file can SEE is judged: an inline `async { }`, or a
/// one-hop binding in the same file. A computation built elsewhere is
/// nobody's guess here and stays quiet.
/// No fix is offered, and the reason is not laziness: the repair is a
/// handler, and its BODY is the design decision — logging (whose idiom
/// varies), letting the process die, or retrying. Worse, WHERE the handler
/// goes changes the behaviour: around a polling loop's body it ends the
/// loop on the first failure, while inside the loop it keeps polling. The
/// note names that choice rather than guessing it.
type StartSuggestion =
    {
        Range: range
        /// "Async.Start" / "Async.StartImmediate", for the message.
        Starter: string
        /// The body loops: a handler wrapped around the whole computation
        /// still stops it on the first failure, so the handler usually
        /// belongs INSIDE the loop (CloudAgent's listener polls forever).
        LoopsInBody: bool
        /// A `try ... with` encloses the START CALL. It reads as covering
        /// the work and catches nothing of it — the computation runs on
        /// the pool, and the handler is on this thread. Worth saying
        /// explicitly: a wrapper that looks like protection is worse than
        /// no wrapper at all.
        WrappedInTry: bool
        /// When that try/with wraps the start and NOTHING else, the handler
        /// was written for this computation alone, so it can be moved
        /// inside it verbatim: the one shape where this rule has a repair
        /// rather than a question. Editor-offered — it restructures.
        TryFix: (range * string * string) option
    }

/// `Async.Start` / `Async.StartImmediate` as a called path: the method
/// ident and the printable name.
[<return: Struct>]
let private (|StarterPath|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        ids.Length >= 2
        && ids.[ids.Length - 2].idText = "Async"
        && ((List.last ids).idText = "Start" || (List.last ids).idText = "StartImmediate")
        ->
        ValueSome(List.last ids, "Async." + (List.last ids).idText)
    | _ -> ValueNone

/// The `async { body }` of a computation expression literal.
[<return: Struct>]
let private (|AsyncLiteral|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
        builder.idText = "async"
        ->
        ValueSome body
    | _ -> ValueNone

/// Find computations started with no way to report a failure. Requires
/// typed check results: the starter must be FSharp.Core's.
let findUnhandledStart
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : StartSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree
        let comments = lazy (commentsWithText parseTree source)

        let isCoreAsync (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value ->
                    (OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp.Control"
                | _ -> false
            | None -> false

        // every `let name = async { ... }` in this file, for the one-hop
        // lookup: `Async.Start listener` where the listener is built above
        let asyncBindings =
            let ofBindings (bindings: SynBinding list) =
                bindings
                |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
                    match p, rhs with
                    | SynPat.Named(ident = SynIdent(ident = id)), AsyncLiteral body -> Some(id.idText, body)
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ f ])), AsyncLiteral body -> Some(f.idText, body)
                    | _ -> None)

            [ for _, e in index.Exprs do
                  match e with
                  | LetOrUseE lou when not lou.IsBang -> yield! ofBindings lou.Bindings
                  | _ -> ()
              for _, d in index.Decls do
                  match d with
                  | SynModuleDecl.Let(bindings = bindings) -> yield! ofBindings bindings
                  | _ -> () ]
            |> Map.ofList

        // the started computation's body, when this file can see it
        let bodyOf (comp: SynExpr) =
            match comp with
            | AsyncLiteral body -> Some body
            | _ ->
                let rec headName (e: SynExpr) =
                    match stripParens e with
                    | SynExpr.Ident id -> Some id.idText
                    | SynExpr.App(isInfix = false; funcExpr = f) -> headName f
                    | _ -> None

                headName comp |> Option.bind (fun n -> Map.tryFind n asyncBindings)

        let within (r: range) (e: SynExpr) = Range.rangeContainsRange r e.Range

        let handled (body: SynExpr) =
            match stripParens body with
            | SynExpr.TryWith _ -> true
            | _ ->
                let catches =
                    index.Exprs
                    |> Array.exists (fun (_, e) ->
                        within body.Range e
                        && (match e with
                            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                ids.Length >= 2
                                && ids.[ids.Length - 2].idText = "Async"
                                && (List.last ids).idText = "Catch"
                            | _ -> false))

                let choiceArms =
                    index.Exprs
                    |> Array.collect (fun (_, e) ->
                        if within body.Range e then
                            match e with
                            | SynExpr.Match(clauses = cs)
                            | SynExpr.MatchBang(clauses = cs)
                            | SynExpr.MatchLambda(matchClauses = cs) ->
                                cs
                                |> List.choose (fun (SynMatchClause(pat = p)) ->
                                    match p with
                                    | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                        Some (List.last ids).idText
                                    | _ -> None)
                                |> Array.ofList
                            | _ -> [||]
                        else
                            [||])

                catches
                && Array.contains "Choice1Of2" choiceArms
                && Array.contains "Choice2Of2" choiceArms

        [ for path, expr in index.Exprs do
              let started =
                  match expr with
                  // Async.Start comp / Async.Start(comp, token)
                  | SynExpr.App(isInfix = false; funcExpr = StarterPath(ident, name); argExpr = arg) ->
                      let comp =
                          match stripParens arg with
                          | SynExpr.Tuple(exprs = first :: _) -> first
                          | a -> a

                      Some(ident, name, comp)
                  // comp |> Async.Start
                  | PipeApp(comp, StarterPath(ident, name)) -> Some(ident, name, comp)
                  | _ -> None

              match started with
              | Some(ident, name, comp) when isCoreAsync ident ->
                  match bodyOf comp with
                  | Some body when not (handled body) ->
                      let loops =
                          index.Exprs
                          |> Array.exists (fun (_, e) ->
                              within body.Range e
                              && (match e with
                                  | SynExpr.While _
                                  | SynExpr.For _
                                  | SynExpr.ForEach _ -> true
                                  | _ -> false))

                      // a try/with around the START, in this scope: it reads
                      // as covering the work and catches nothing of it
                      let wrappedInTry =
                          path
                          |> List.takeWhile (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.Lambda _ | SynExpr.MatchLambda _ | SynExpr.ObjExpr _) ->
                                  false
                              | SyntaxNode.SynBinding _ -> false
                              | _ -> true)
                          |> List.exists (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.TryWith(tryExpr = tryBody)) ->
                                  Range.rangeContainsRange tryBody.Range expr.Range
                              | _ -> false)

                      // The try/with wraps the start and NOTHING else, so its
                      // handler was written for this computation and nowhere
                      // else: move it inside, where it can actually fire. The
                      // handler travels verbatim — every clause, typed
                      // patterns and guards included — which the Async.Catch
                      // spelling could not do (it also does not typecheck
                      // piped into Async.Start: Start wants Async<unit>,
                      // Catch yields Async<Choice<_, exn>>).
                      let tryFix =
                          path
                          |> List.tryPick (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.TryWith(tryExpr = tryBody; trivia = trivia) as tryExpr) when
                                  Range.equals (stripParens tryBody).Range expr.Range
                                  ->
                                  Some(tryExpr, trivia)
                              | _ -> None)
                          |> Option.bind (fun (tryExpr, trivia) ->
                              // only an inline async { } can take the handler
                              // in, and only a single-argument start keeps the
                              // call faithful (a token argument would be lost)
                              let singleArgument =
                                  match expr with
                                  | SynExpr.App(isInfix = false; argExpr = arg) ->
                                      match stripParens arg with
                                      | SynExpr.Tuple _ -> false
                                      | _ -> true
                                  | _ -> true

                              // the handler lands inside the computation,
                              // where the compiler makes it a closure: a
                              // `reraise ()` there is FS0413, not a rethrow
                              let rethrows =
                                  System.Text.RegularExpressions.Regex.IsMatch(
                                      textOfRange source trivia.WithToEndRange,
                                      @"\b(reraise|rethrow)\b"
                                  )

                              // the rewrite is rebuilt from the body and the
                              // handler alone: a comment anywhere else in the
                              // try - beside `async {`, after the last
                              // statement, between `}` and the start - would
                              // be dropped with it
                              let commentDropped (body: SynExpr) =
                                  comments.Value
                                  |> List.exists (fun (r, _) ->
                                      Range.rangeContainsRange tryExpr.Range r
                                      && not (Range.rangeContainsRange body.Range r)
                                      && not (Range.rangeContainsRange trivia.WithToEndRange r))

                              match comp with
                              | AsyncLiteral body when
                                  singleArgument
                                  && not (spansDirective source tryExpr.Range)
                                  && not rethrows
                                  && not (commentDropped body)
                                  ->
                                  let baseColumn = tryExpr.Range.StartColumn
                                  let indent = System.String(' ', baseColumn)

                                  let bodyBlock =
                                      reindentBlock
                                          (baseColumn + 8)
                                          body.Range.StartColumn
                                          (textOfRange source body.Range)

                                  let handlerBlock =
                                      reindentBlock
                                          (baseColumn + 4)
                                          trivia.WithKeyword.StartColumn
                                          (textOfRange source trivia.WithToEndRange)

                                  match bodyBlock, handlerBlock with
                                  | Some bodyBlock, Some handlerBlock ->
                                      let replacement =
                                          "async {\n"
                                          + indent
                                          + "    try\n"
                                          + bodyBlock
                                          + "\n"
                                          + handlerBlock
                                          + "\n"
                                          + indent
                                          + "}\n"
                                          + indent
                                          + "|> "
                                          + name

                                      Some(tryExpr.Range, textOfRange source tryExpr.Range, replacement)
                                  | _ -> None
                              | _ -> None)

                      { Range = expr.Range
                        Starter = name
                        LoopsInBody = loops
                        WrappedInTry = wrappedInTry
                        TryFix = tryFix }
                  | _ -> ()
              | _ -> () ]
