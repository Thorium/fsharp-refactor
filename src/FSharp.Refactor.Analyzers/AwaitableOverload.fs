/// FR0119 (fix): a synchronous call inside `task { }` where the typed
/// tree proves an async twin exists — the preventive half of FR0049:
/// instead of flagging sync-over-async after the fact, take the
/// asynchronous road while the code is already in a task.
///
///     task {                                   task {
///         let line = reader.ReadLine()   →         let! line = reader.ReadLineAsync()
///         writer.Flush()                           do! writer.FlushAsync()
///
/// Typed gates:
///   - the resolved method's declaring entity offers `<Name>Async` with
///     the SAME parameter-type prefix (an extra trailing OPTIONAL
///     CancellationToken is fine — FR0118 hands it the token on the next
///     pass) and a Task-shaped return: `T` → `Task<T>`/`ValueTask<T>`,
///     `unit` → `Task`/`ValueTask`
///   - `let x = ...` bindings become `let!` (simple named pattern, no
///     annotation); statement position becomes `do!` only when the twin
///     returns the NON-generic Task
///   - inside `async { }` the same rewrite bridges with
///     `|> Async.AwaitTask` — real Task twins only there, AwaitTask has
///     no ValueTask overload
///   - never inside a lambda, a nested CE, a finally block or an
///     exception handler
///   - never `Dispose` → `DisposeAsync`: a ValueTask twin with nothing
///     to await behind it
module FSharp.Refactor.AwaitableOverload

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// (range, original, replacement) edits: the binding keyword or
        /// statement prefix, plus the method name gaining its suffix.
        Fixes: (range * string * string) list
        MethodName: string
    }

let private ceBuilders = set [ "task"; "backgroundTask"; "async" ]

[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

let private parameterShapes (displayContext: FSharpDisplayContext) (mfv: FSharpMemberOrFunctionOrValue) =
    try
        match mfv.CurriedParameterGroups |> List.ofSeq with
        | [ group ] -> Some [ for p in group -> p.Type.Format displayContext ]
        | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

let private isOptionalCancellationToken (m: FSharpMemberOrFunctionOrValue) =
    try
        let last = m.CurriedParameterGroups |> Seq.collect id |> Seq.last

        last.IsOptionalArg
        && (match last.Type.StripAbbreviations().TypeDefinition.TryFullName with
            | Some full -> full = "System.Threading.CancellationToken"
            | None -> false)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

let private returnFullName (m: FSharpMemberOrFunctionOrValue) =
    try
        match m.ReturnParameter.Type.StripAbbreviations().TypeDefinition.TryFullName with
        | Some full -> full
        | None -> ""
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        ""

/// The async twin's return must wrap the original's: `T` → `Task<T>` /
/// `ValueTask<T>`, `unit` → `Task`/`ValueTask`. Compared structurally —
/// formatted names depend on what happens to be open at the call site.
let private returnsWrapped
    (displayContext: FSharpDisplayContext)
    (orig: FSharpMemberOrFunctionOrValue)
    (twin: FSharpMemberOrFunctionOrValue)
    =
    try
        let origFormat = orig.ReturnParameter.Type.Format displayContext

        match returnFullName twin with
        | "System.Threading.Tasks.Task"
        | "System.Threading.Tasks.ValueTask" -> origFormat = "unit"
        | n when
            n.StartsWith "System.Threading.Tasks.Task`"
            || n.StartsWith "System.Threading.Tasks.ValueTask`"
            ->
            twin.ReturnParameter.Type.StripAbbreviations().GenericArguments
            |> Seq.tryHead
            |> Option.map (fun inner -> inner.Format displayContext = origFormat)
            |> Option.defaultValue false
        | _ -> false
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// Does the twin return the NON-generic Task — the only shape `do!` binds.
let private returnsPlainTask (twin: FSharpMemberOrFunctionOrValue) =
    match returnFullName twin with
    | "System.Threading.Tasks.Task"
    | "System.Threading.Tasks.ValueTask" -> true
    | _ -> false

/// Async.AwaitTask exists for real Tasks only.
let private returnsRealTask (twin: FSharpMemberOrFunctionOrValue) =
    let n = returnFullName twin
    n = "System.Threading.Tasks.Task" || n.StartsWith "System.Threading.Tasks.Task`"

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // bodies choreographed around a thread (a signal, a Thread,
        // Interlocked): a bind there moves the continuation off the thread
        // the code waited on — the same refusal as FR0142's and FR0049's
        let threadBoundBodies =
            index.Exprs
            |> Array.collect (fun (path, _) ->
                path
                |> List.choose (fun node ->
                    match node with
                    | SyntaxNode.SynBinding(SynBinding(expr = body)) -> Some body
                    | _ -> None)
                |> Array.ofList)
            |> Array.distinctBy (fun body -> body.Range)
            |> Array.filter (BlockingSites.threadBound source)
            |> Array.map (fun body -> body.Range)

        // task/async CE bodies with their builder, for scoping and for
        // picking the bind bridge
        let ces =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                    ceBuilders.Contains builder
                    ->
                    Some(builder, body.Range)
                | _ -> None)

        // Every CE's own STATEMENT SPINE: the chain of let/use/sequential
        // nodes hanging directly off its body. `let!` and `do!` are legal
        // only there — a call nested inside ANOTHER binding's right-hand
        // side sits inside the CE's range but not on its spine, and
        // rewriting its `let` to `let!` cannot compile. That was 21 of the
        // rollbacks in one sweep repo, all of this shape:
        //     async {
        //         let pair =
        //             ...
        //             let json = File.ReadAllText p   // NOT on the spine
        let spineRanges =
            let acc = ResizeArray<range>()

            let rec walk (e: SynExpr) =
                acc.Add e.Range

                match e with
                | LetOrUseE lou -> walk lou.Body
                | SynExpr.Sequential(expr1 = a; expr2 = b) ->
                    acc.Add a.Range
                    walk b
                // control flow whose branches are statement positions of
                // the same CE: a `let!` is as legal in a match arm, an if
                // branch, a try body or a loop body as at the top of the
                // block. CarmelNet's `match res with | Choice2Of2 e -> ...
                // let err = reader.ReadToEnd()` sat two arms deep and was
                // never seen. A `with` handler and a `finally` stay out —
                // the bind gate below excludes them on purpose
                | SynExpr.Match(clauses = clauses)
                | SynExpr.MatchBang(clauses = clauses) ->
                    for SynMatchClause(resultExpr = result) in clauses do
                        walk result
                | SynExpr.IfThenElse(thenExpr = thenExpr; elseExpr = elseExpr) ->
                    walk thenExpr
                    elseExpr |> Option.iter walk
                | SynExpr.TryWith(tryExpr = body)
                | SynExpr.TryFinally(tryExpr = body)
                | SynExpr.ForEach(bodyExpr = body)
                | SynExpr.For(doBody = body)
                | SynExpr.While(doExpr = body)
                | SynExpr.Paren(expr = body) -> walk body
                | _ -> ()

            for _, e in index.Exprs do
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                    ceBuilders.Contains builder
                    ->
                    walk body
                | _ -> ()

            acc.ToArray()

        let onSpine (r: range) =
            spineRanges |> Array.exists (fun s -> Range.equals s r)

        let lambdaRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.Lambda _
                | SynExpr.MatchLambda _ -> [| e.Range |]
                // a LOCAL FUNCTION's body is a closure too, but its AST is
                // a binding with argument patterns, not a Lambda node — a
                // do!/let! injected there would land in a plain function
                | LetOrUseE lou when not lou.IsBang ->
                    lou.Bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))) ->
                            Some b.RangeOfBindingWithRhs
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])

        let otherCeRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.ComputationExpr(expr = body) -> Some body.Range
                | SynExpr.ArrayOrListComputed(expr = body) -> Some body.Range
                | _ -> None)

        let noBindRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.TryFinally(finallyExpr = f) -> [| f.Range |]
                | SynExpr.TryWith(withCases = cases) ->
                    cases
                    |> List.map (fun (SynMatchClause(resultExpr = result)) -> result.Range)
                    |> Array.ofList
                | _ -> [||])

        // the INNERMOST enclosing task/async body a site sits directly in:
        // its builder decides the bridge. Nothing inside a lambda, nested
        // CE, finally, or handler qualifies
        let directBuilder (r: range) =
            if noBindRanges |> Array.exists (fun z -> Range.rangeContainsRange z r) then
                None
            else
                ces
                |> Array.filter (fun (_, ceRange) ->
                    Range.rangeContainsRange ceRange r
                    && not (
                        lambdaRanges
                        |> Array.exists (fun l -> Range.rangeContainsRange ceRange l && Range.rangeContainsRange l r)
                    )
                    && not (
                        otherCeRanges
                        |> Array.exists (fun other ->
                            Range.rangeContainsRange ceRange other
                            && not (Range.equals other ceRange)
                            && Range.rangeContainsRange other r)
                    ))
                |> Array.sortBy (fun (_, ceRange) -> ceRange.EndLine - ceRange.StartLine, ceRange.EndColumn)
                |> Array.tryHead
                |> Option.map fst

        // the plain `let` whose entire RHS is `target` — the let! shape
        let bindingKeywordFor (target: range) =
            index.Exprs
            |> Array.tryPick (fun (_, e) ->
                match e with
                | LetOrUseE lou when not (lou.IsBang || lou.IsUse || lou.IsRecursive) ->
                    match lou.Bindings with
                    | [ SynBinding(
                            isMutable = false
                            returnInfo = None
                            headPat = SynPat.Named _
                            expr = rhs
                            trivia = btrivia) ] when Range.equals rhs.Range target ->
                        // the let node's own range travels too: only a
                        // binding ON THE CE SPINE may become `let!`
                        Some(btrivia.LeadingKeyword.Range, e.Range)
                    | _ -> None
                | _ -> None)

        // statement position: a direct sequential element of the CE chain
        let isStatement (target: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.Sequential(expr1 = a) -> Range.equals a.Range target
                | _ -> false)

        [ for _, expr in index.Exprs do
              match expr with
              | SynExpr.App(isInfix = false; funcExpr = CallIdent methodId; argExpr = args) when
                  not (methodId.idText.EndsWith "Async")
                  // `Dispose` → `DisposeAsync` never pays: the twin returns
                  // ValueTask (outside the Task/Task<T> gate the rule
                  // documents) and there is nothing to await — fantomas's
                  // EndToEndTests.fs had `File.Create(f).Dispose()` turned
                  // into `do! File.Create(f).DisposeAsync()`
                  && methodId.idText <> "Dispose"
                  ->
                  let tupled =
                      match args with
                      | SynExpr.Const(SynConst.Unit, _) -> Some 0
                      | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> Some es.Length
                      | SynExpr.Paren _ -> Some 1
                      // juxtaposed atomic argument — `writer.Write s` — is
                      // the common F# spelling; the rewrite only touches the
                      // keyword and the name, so the arg shape can stay
                      | SynExpr.Const _
                      | SynExpr.Ident _
                      | SynExpr.LongIdent _ -> Some 1
                      | _ -> None

                  match tupled, directBuilder expr.Range with
                  | Some arity, Some builder ->
                      let lineText = source.GetLineString(methodId.idRange.EndLine - 1)

                      let resolved =
                          check.GetSymbolUseAtLocation(
                              methodId.idRange.EndLine,
                              methodId.idRange.EndColumn,
                              lineText,
                              [ methodId.idText ]
                          )

                      match resolved with
                      | Some symbolUse ->
                          match symbolUse.Symbol with
                          | :? FSharpMemberOrFunctionOrValue as mfv when mfv.IsMember && not mfv.IsProperty ->
                              let ctx = symbolUse.DisplayContext

                              let twin =
                                  match parameterShapes ctx mfv with
                                  | Some ps when ps.Length = arity ->
                                      (try
                                          match mfv.DeclaringEntity with
                                          | Some entity ->
                                              entity.MembersFunctionsAndValues
                                              |> Seq.tryFind (fun m ->
                                                  m.DisplayName = mfv.DisplayName + "Async"
                                                  && returnsWrapped ctx mfv m
                                                  && (match parameterShapes ctx m with
                                                      | Some mps when mps.Length = arity -> mps = ps
                                                      | Some mps when mps.Length = arity + 1 ->
                                                          List.truncate arity mps = ps && isOptionalCancellationToken m
                                                      | _ -> false))
                                          | None -> None
                                       with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                           None)
                                  | _ -> None

                              // async { } bridges via Async.AwaitTask, which
                              // has no ValueTask overload — real Task only
                              let twin =
                                  match builder, twin with
                                  | "async", Some m when not (returnsRealTask m) -> None
                                  | _ -> twin

                              match twin with
                              | Some twinM ->
                                  let renameFix = methodId.idRange, methodId.idText, methodId.idText + "Async"

                                  let bridgeFixes =
                                      if builder = "async" then
                                          let atEnd = Range.mkRange expr.Range.FileName expr.Range.End expr.Range.End

                                          [ atEnd, "", " |> Async.AwaitTask" ]
                                      else
                                          []

                                  match bindingKeywordFor expr.Range with
                                  | Some(kw, letRange) when textOfRange source kw = "let" && onSpine letRange ->
                                      { Range = expr.Range
                                        Fixes = [ kw, "let", "let!"; renameFix ] @ bridgeFixes
                                        MethodName = methodId.idText }
                                  | Some _ -> ()
                                  | None ->
                                      // statement position takes do! — but
                                      // only a NON-generic Task binds there,
                                      // and only ON the CE's own spine
                                      if isStatement expr.Range && onSpine expr.Range && returnsPlainTask twinM then
                                          let at = Range.mkRange expr.Range.FileName expr.Range.Start expr.Range.Start

                                          { Range = expr.Range
                                            Fixes = [ at, "", "do! "; renameFix ] @ bridgeFixes
                                            MethodName = methodId.idText }
                              | None -> ()
                          | _ -> ()
                      | None -> ()
                  | _ -> ()
              | _ -> () ]
        |> List.filter (fun s ->
            not (
                threadBoundBodies
                |> Array.exists (fun body -> Range.rangeContainsRange body s.Range)
            ))
