/// Refactoring (correctness, CA2200): re-raising a caught exception with
/// `raise` resets its stack trace; `reraise ()` preserves it.
///
///     try ... with ex ->        try ... with ex ->
///         log ex           →        log ex
///         raise ex                  reraise ()
///
/// Losing the original stack trace is the classic way production bugs
/// become undiagnosable, so this fix intentionally changes the observable
/// stack trace — back to the one the code meant to keep.
///
/// Safety rules:
///   - the raised identifier is bound by the handler's own pattern and is
///     not rebound in between
///   - the raise site is lexically in the handler: not inside a lambda,
///     local function, object expression, `lazy`, comprehension,
///     computation expression, quotation or nested try (where `reraise`
///     would not compile — FS0413 — or would refer to a different
///     exception)
///   - the try-with itself is not inside a computation expression:
///     `task { try ... with ex -> raise ex }` desugars the handler into a
///     lambda passed to builder.TryWith, where `reraise ()` is FS0413
///   - `raise` resolves (typed check results) to FSharp.Core
module FSharp.Refactor.Reraise

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        /// The exception identifier, for the message.
        ExceptionName: string
        /// Inside a computation expression, where `reraise ()` is not
        /// allowed: a `try ... with ex -> raise ex` whose only arm
        /// rethrows guards nothing — the edit replaces the whole try/with
        /// with its body, and an unmatched exception then propagates with
        /// its trace intact. None for the ordinary `reraise ()` rewrite.
        Removal: (range * string * string) option
    }

/// Find `raise ex` sites in with-handlers. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // sub-ranges of `r` where reraise () would not compile or would
        // mean a different exception. FS0413 allows `reraise ()` DIRECTLY
        // in the handler only: every closure spelling is out — a lambda, a
        // local function (`let helper () = raise ex` compiles to its own
        // closure, a plain value binding does not), an object-expression
        // member, `lazy`, a comprehension, a computation expression, a
        // quotation — and so is a nested try. A `for`, a `match` and an
        // `if` inside the handler are fine.
        let opaqueRangesIn (r: range) =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                if not (Range.rangeContainsRange r e.Range) then
                    [||]
                else
                    match e with
                    | SynExpr.Lambda _
                    | SynExpr.MatchLambda _
                    | SynExpr.ComputationExpr _
                    | SynExpr.ArrayOrListComputed _
                    | SynExpr.ObjExpr _
                    | SynExpr.Lazy _
                    | SynExpr.Quote _
                    | SynExpr.TryWith _
                    | SynExpr.TryFinally _ -> [| e.Range |]
                    | LetOrUseE lou ->
                        lou.Bindings
                        |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
                            match p with
                            | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> Some rhs.Range
                            | _ when lou.IsRecursive -> Some rhs.Range
                            | _ -> None)
                        |> Array.ofList
                    | _ -> [||])

        // is `name` rebound inside `r`? A let/use, a lambda parameter, a
        // match arm (`| Some ex -> raise ex` raises the INNER exception), a
        // `function` clause, a nested handler or a loop binder — any of
        // them makes `raise ex` a different object from the one caught
        let reboundIn (name: string) (r: range) =
            let binds (p: SynPat) = patBoundNames p |> List.contains name

            index.Exprs
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (match e with
                    | LetOrUseE lou -> lou.Bindings |> List.exists (fun (SynBinding(headPat = p)) -> binds p)
                    | SynExpr.Lambda(parsedData = Some(pats, _)) -> pats |> List.exists binds
                    | SynExpr.Match(clauses = cs)
                    | SynExpr.MatchBang(clauses = cs)
                    | SynExpr.MatchLambda(matchClauses = cs)
                    | SynExpr.TryWith(withCases = cs) -> cs |> List.exists (fun (SynMatchClause(pat = p)) -> binds p)
                    | SynExpr.ForEach(pat = p) -> binds p
                    | SynExpr.For(ident = id) -> id.idText = name
                    | _ -> false))

        // A try-with whose nearest deferring ancestor is a computation
        // expression desugars into builder.TryWith(body, handler) — the
        // handler becomes a lambda, where reraise () is FS0413. A lambda or
        // object-expression member between the two resets to ordinary code.
        let inComputationExpr (path: SyntaxNode list) =
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.ComputationExpr _)
                | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed _) -> Some true
                | SyntaxNode.SynExpr(SynExpr.Lambda _)
                | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
                | SyntaxNode.SynExpr(SynExpr.ObjExpr _) -> Some false
                | _ -> None)
            |> Option.defaultValue false

        // a string literal spanning lines inside the try would be
        // re-indented with the body
        let multiLineStringIn (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.Const(SynConst.String _, sr)
                | SynExpr.InterpolatedString(range = sr) -> sr.StartLine <> sr.EndLine && Range.rangeContainsRange r sr
                | _ -> false)

        // the try's body, laid out where the try stood: its first line
        // takes the try's place, its continuation lines move by the same
        // amount (which they must have room for when it is negative)
        let bodyInPlace (tryExpr: SynExpr) (body: SynExpr) =
            let text = textOfRange source body.Range

            if isSingleLine tryExpr.Range then
                Some text
            elif multiLineStringIn tryExpr.Range then
                None
            else
                let shift = tryExpr.Range.StartColumn - body.Range.StartColumn
                let lines = text.Split '\n'
                let continuation = lines |> Array.skip 1
                let leading (l: string) = l.Length - l.TrimStart().Length

                if
                    shift < 0
                    && continuation
                       |> Array.exists (fun l -> not (System.String.IsNullOrWhiteSpace l) && leading l < -shift)
                then
                    None
                else
                    let moved =
                        continuation
                        |> Array.map (fun l ->
                            if System.String.IsNullOrWhiteSpace l then ""
                            elif shift >= 0 then System.String(' ', shift) + l
                            else l.Substring(-shift))

                    Some(String.concat "\n" (Array.append [| lines.[0] |] moved))

        [ for path, expr in index.Exprs do
              match expr with
              // inside a computation expression `reraise ()` is FS0413,
              // and a handler that only rethrows guards nothing: the
              // try/with goes, and the exception propagates with its
              // trace intact (suave's Combinators.fs, twice)
              | SynExpr.TryWith(
                  tryExpr = body
                  withCases = [ SynMatchClause(
                                    pat = SynPat.Named(ident = SynIdent(ident = exId))
                                    whenExpr = None
                                    resultExpr = handler) ]) when
                  inComputationExpr path
                  // `raise ex` where the computation returns unit, `return
                  // raise ex` / `return! raise ex` where it returns a value
                  && (let rethrow (e: SynExpr) =
                          match stripParens e with
                          | SynExpr.App(isInfix = false; funcExpr = SingleIdent raiseId; argExpr = raised) ->
                              raiseId.idText = "raise"
                              && (match stripParens raised with
                                  | SynExpr.Ident r -> r.idText = exId.idText
                                  | _ -> false)
                              && OptionModule.resolvesToCoreOperator check source raiseId
                          | _ -> false

                      match handler with
                      | SynExpr.YieldOrReturn(expr = inner)
                      | SynExpr.YieldOrReturnFrom(expr = inner) -> rethrow inner
                      | e -> rethrow e)
                  && not (spansDirective source expr.Range)
                  ->
                  match bodyInPlace expr body with
                  | Some replacement ->
                      { Range = expr.Range
                        OriginalText = textOfRange source expr.Range
                        ExceptionName = exId.idText
                        Removal = Some(expr.Range, textOfRange source expr.Range, replacement) }
                  | None -> ()
              | SynExpr.TryWith(withCases = clauses) when not (inComputationExpr path) ->
                  for SynMatchClause(pat = pat; resultExpr = handler) in clauses do
                      let exNames = patBoundNames pat |> Set.ofList

                      if not exNames.IsEmpty then
                          let opaque = opaqueRangesIn handler.Range

                          for _, e in index.Exprs do
                              match e with
                              | SynExpr.App(isInfix = false; funcExpr = SingleIdent raiseId; argExpr = arg) when
                                  raiseId.idText = "raise"
                                  && Range.rangeContainsRange handler.Range e.Range
                                  && not (opaque |> Array.exists (fun o -> Range.rangeContainsRange o e.Range))
                                  ->
                                  match stripParens arg with
                                  | SynExpr.Ident exId when
                                      exNames.Contains exId.idText
                                      && not (reboundIn exId.idText handler.Range)
                                      && OptionModule.resolvesToCoreOperator check source raiseId
                                      ->
                                      { Range = e.Range
                                        OriginalText = textOfRange source e.Range
                                        ExceptionName = exId.idText
                                        Removal = None }
                                  | _ -> ()
                              | _ -> ()
              | _ -> () ]
