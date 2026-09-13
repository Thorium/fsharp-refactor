/// Refactoring: strip computation-expression wrapping that does nothing.
///
///     async { return! comp }                          →  comp
///     async { let! v = comp in return v }             →  comp
///     async { return e } |> Async.RunSynchronously    →  e
///     Async.RunSynchronously (async { return e })     →  e
///     task { return x }                               →  Task.FromResult(x)
///
/// Only *type-preserving* strips are offered: the first two keep the
/// `Async<'T>` type (monad right-identity), and in the runner form the
/// wrapper and the immediate run cancel out. Rewriting `async { return e }`
/// alone to `e` would change the expression's type and is deliberately out of
/// scope (that is a signature change, not a cleanup).
///
/// Safety rules:
///   - the stripped computation in the first two forms must be a bare
///     identifier — evaluating it early has no effects
///   - `use!` is never stripped (its disposal would be lost)
///   - in the runner form the returned expression must be single-line and
///     safe to inline at an arbitrary expression position
///   - the `task` form requires the returned expression to be a bare
///     identifier or constant (an expression that throws would produce a
///     faulted task in the CE but throw synchronously from Task.FromResult)
///     and the file to `open System.Threading.Tasks` so `Task.FromResult`
///     resolves; `task { return! ... }` is never touched because its
///     overloads also accept Async and stripping could change the type
module FSharp.Refactor.CeStrip

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type StripKind =
    /// `async { return! comp }` / `async { let! v = comp in return v }`
    | Forwarded
    /// `async { return e } |> Async.RunSynchronously`
    | WithRunner
    /// `task { return x }` → `Task.FromResult(x)`
    | TaskFromResult
    /// `return! task { return! X }` — the wrapper machine is a no-op
    /// around its single return statement; the inner statement IS the
    /// arm. Each strip removes one layer, so nesting unwinds pass by
    /// pass.
    | ReturnBangIdentity
    /// `let runTailN () = B in runTailN ()` — a tool-generated tail
    /// thunk wrapping nothing but another tail thunk (or, since the wrap
    /// now sizes correctly, a tail too small to have deserved one). The
    /// thunk is nullary, non-rec and called exactly where it is defined,
    /// so the binding IS its body. Each strip removes one layer.
    | ThunkIdentity

type Suggestion =
    {
        /// Range of the expression the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        Kind: StripKind
    }

/// A bare simple identifier — evaluating it has no side effects. Dotted
/// paths are deliberately excluded: `Service.Current` can be a static
/// property whose getter runs user code, and stripping the wrapper would
/// move that evaluation from per-run to construction time.
[<return: Struct>]
let private (|BareIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident _ -> ValueSome e
    | _ -> ValueNone

/// `async { body }`
[<return: Struct>]
let private (|AsyncCe|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
        builder.idText = "async"
        ->
        ValueSome body
    | _ -> ValueNone

/// `task { body }`
[<return: Struct>]
let private (|TaskCe|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
        builder.idText = "task"
        ->
        ValueSome body
    | _ -> ValueNone

/// An expression whose evaluation cannot throw: a simple identifier or a
/// literal constant.
[<return: Struct>]
let private (|NonThrowing|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.Const _ -> ValueSome e
    | _ -> ValueNone

/// All `open` targets in the file, as dotted strings.
let private collectOpens (parseTree: ParsedInput) : Set<string> =
    let opens = ResizeArray<string>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(_path, decl) =
                match decl with
                | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                    opens.Add(ids |> List.map (fun i -> i.idText) |> String.concat ".")
                | _ -> () }

    AstIndex.replay collector parseTree
    Set.ofSeq opens

/// A name the FR0029 tail wrap generates: runTail, runTail2, runTail3...
/// Only these are collapsed — a human's own immediately-invoked thunk may
/// be making a deliberate point.
let private isRunTailName (name: string) =
    name.StartsWith "runTail" && name.Substring 7 |> Seq.forall System.Char.IsDigit

let private isUnitPat (p: SynPat) =
    match p with
    | SynPat.Paren(SynPat.Const(SynConst.Unit, _), _)
    | SynPat.Const(SynConst.Unit, _) -> true
    | _ -> false

/// Does this expression hold a plain `use` (not `use!`) anywhere in its
/// statement chain? Nested lambdas and CEs are not descended into: a `use`
/// inside one of those already owns its own scope.
let rec private containsPlainUse (e: SynExpr) =
    match e with
    | LetOrUseE lou when lou.IsUse && not lou.IsBang -> true
    | LetOrUseE lou -> containsPlainUse lou.Body
    | SynExpr.Sequential(expr1 = e1; expr2 = e2) -> containsPlainUse e1 || containsPlainUse e2
    | _ -> false

/// The expression a statement chain ends in.
[<TailCall>]
let rec private terminalExpr (e: SynExpr) =
    match e with
    | SynExpr.Sequential(expr2 = e2) -> terminalExpr e2
    | LetOrUseE lou when not lou.IsBang -> terminalExpr lou.Body // a plain `use` is walked THROUGH: the terminal sits past it
    | e -> e

/// The builder of the computation expression a statement sits in: the
/// nearest `{ }` on the path and the identifier applied to it.
[<TailCall>]
let rec private enclosingBuilder (path: SyntaxNode list) : string option =
    match path with
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.Ident builder)) :: _ ->
        Some builder.idText
    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: _ -> None
    | _ :: rest -> enclosingBuilder rest
    | [] -> None

/// Does `return! inner { return v }` in a CE of `outer` mean `return v`?
/// Only where the outer builder's `return!` hands the inner computation's
/// result through unchanged: FSharp.Core's `task`/`backgroundTask` accept a
/// `Task<'T>` or an `Async<'T>` and yield `'T`; `async` accepts an
/// `Async<'T>`. Any other builder may route `return!` through a `Source`
/// or `ReturnFrom` overload that converts — FsToolkit's
/// `cancellableTaskResult { return! async { return Choice1Of2 x } }` turns
/// the Choice into a Result on the way, and `return Choice1Of2 x` is a
/// type error there; where the types happen to coincide the strip silently
/// bypasses the overload under test. Withheld for every name not listed.
let private returnBangPassesThrough (outer: string option) (inner: string) =
    match outer with
    | Some("task" | "backgroundTask") -> inner = "task" || inner = "backgroundTask" || inner = "async"
    | Some "async" -> inner = "async"
    | _ -> false

/// `Async.RunSynchronously`
[<return: Struct>]
let private (|RunSynchronously|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when
        m.idText = "Async" && f.idText = "RunSynchronously"
        ->
        ValueSome()
    | _ -> ValueNone

/// The computation a do-nothing async body forwards to, if any:
/// `return! comp` or `let! v = comp in return v` with comp a bare identifier.
let private forwardedComputation (body: SynExpr) : SynExpr option =
    match body with
    | SynExpr.YieldOrReturnFrom(expr = BareIdent comp) -> Some comp
    | LetOrUseE lou when lou.IsBang && not lou.IsUse ->
        match lou.Bindings, lou.Body with
        | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = v)); expr = BareIdent comp) ],
          SynExpr.YieldOrReturn(expr = SynExpr.Ident returned) when returned.idText = v.idText -> Some comp
        | _ -> None
    | _ -> None

/// `async { return e }` — the returned expression.
[<return: Struct>]
let private (|ReturnOnly|_|) (e: SynExpr) =
    match e with
    | AsyncCe(SynExpr.YieldOrReturn(expr = returned)) -> ValueSome returned
    | _ -> ValueNone

/// Lines that lie INSIDE a multi-line string or interpolation — their
/// leading whitespace is content, and the dedents must not touch it.
let private multiLineLiteralLines (parseTree: ParsedInput) : Set<int> =
    let lines = ResizeArray<int>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, e) =
                match e with
                | SynExpr.Const(SynConst.String _, r)
                | SynExpr.InterpolatedString(range = r) when r.EndLine > r.StartLine ->
                    lines.AddRange(seq { r.StartLine + 1 .. r.EndLine })
                | _ -> () }

    AstIndex.replay collector parseTree
    Set.ofSeq lines

/// Find do-nothing async/task wrappings.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()
    let opens = collectOpens parseTree
    let literalLines = multiLineLiteralLines parseTree

    let add (range: range) (replacementText: string) (kind: StripKind) =
        suggestions.Add
            { Range = range
              OriginalText = textOfRange source range
              ReplacementText = replacementText
              Kind = kind }

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                // async { return e } |> Async.RunSynchronously
                | PipeApp(ReturnOnly returned, RunSynchronously)
                // Async.RunSynchronously (async { return e })
                | SynExpr.App(funcExpr = RunSynchronously; argExpr = SynExpr.Paren(expr = ReturnOnly returned)) when
                    isSingleLine returned.Range && isSafeInline returned
                    ->
                    // parenthesize unless atomic: the strip site can sit inside
                    // a tuple or as an operand of a tighter operator, where a
                    // bare `a + b` or `1, 2` would regroup silently
                    add expr.Range (atomicText source returned) StripKind.WithRunner
                // async { return! comp } / async { let! v = comp in return v }
                | AsyncCe body ->
                    forwardedComputation body
                    |> Option.iter (fun comp -> add expr.Range (textOfRange source comp.Range) StripKind.Forwarded)
                // task { return x }
                | TaskCe(SynExpr.YieldOrReturn(expr = NonThrowing returned)) when
                    opens.Contains "System.Threading.Tasks"
                    ->
                    add
                        expr.Range
                        (sprintf "Task.FromResult(%s)" (textOfRange source returned.Range))
                        StripKind.TaskFromResult
                // return! task { <single return statement> } — the wrapper
                // machine is a no-op; the inner statement IS the arm. Only
                // inside a builder known to pass the inner result through
                // unchanged (see returnBangPassesThrough)
                | SynExpr.YieldOrReturnFrom(
                    expr = SynExpr.App(funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = inner))) when
                    returnBangPassesThrough (enclosingBuilder path) builder.idText
                    && (match inner with
                        | SynExpr.YieldOrReturn _
                        | SynExpr.YieldOrReturnFrom _ -> true
                        | _ -> false)
                    ->
                    // rebuild the inner statement's text, dedented from its
                    // wrapped depth back to the wrapper's column where the
                    // lines allow; verbatim where they do not (still parses:
                    // deeper is never offside)
                    let shift = inner.Range.StartColumn - expr.Range.StartColumn

                    let text =
                        if inner.Range.StartLine = inner.Range.EndLine then
                            textOfRange source inner.Range
                        else
                            [ for l in inner.Range.StartLine .. inner.Range.EndLine ->
                                  let line = source.GetLineString(l - 1)

                                  let line =
                                      if l = inner.Range.EndLine then
                                          line.Substring(0, min line.Length inner.Range.EndColumn)
                                      else
                                          line

                                  if l = inner.Range.StartLine then
                                      line.Substring inner.Range.StartColumn
                                  elif
                                      shift > 0
                                      && line.Length >= shift
                                      && line.Substring(0, shift).Trim() = ""
                                      && not (literalLines.Contains l)
                                  then
                                      line.Substring shift
                                  else
                                      line ]
                            |> String.concat "\n"

                    add expr.Range text StripKind.ReturnBangIdentity
                // let runTailN () = B in runTailN () — the tail thunk wraps
                // nothing worth a thunk; the binding IS its body. One layer
                // per pass, so runTail3(runTail2(runTail)) unwinds fully.
                | LetOrUseE lou when not (lou.IsBang || lou.IsUse) ->
                    match lou.Bindings, lou.Body with
                    | [ SynBinding(
                            headPat = SynPat.LongIdent(
                                longDotId = SynLongIdent(id = [ f ]); argPats = SynArgPats.Pats [ unitPat ])
                            expr = thunkBody) ],
                      thunkCall when
                        isRunTailName f.idText
                        && isUnitPat unitPat
                        // only UNJUSTIFIED wraps collapse: a body under the
                        // tail wrap's own four-line threshold, or a body
                        // that is nothing but another thunk (nested
                        // damage). A four-plus-line body is the wrap FR0029
                        // meant to make — collapsing it would hand the two
                        // rules an eternal wrap/unwrap oscillation (seen
                        // live on management-portal Domain.fs before this
                        // gate)
                        && (thunkBody.Range.EndLine - thunkBody.Range.StartLine + 1 < 4
                            // ... or the body holds a `use`, which a plain
                            // closure must never own: inside the CE it binds
                            // to the builder's Using (DisposeAsync where the
                            // type offers it), and a closure silently makes
                            // it synchronous. FR0029 refuses to build this
                            // shape now, so collapsing it CURES code that an
                            // older version already wrote — prevention alone
                            // cannot reach a change that is committed. No
                            // oscillation: re-extraction takes the
                            // task-returning variant, which this rule does
                            // not collapse.
                            || containsPlainUse thunkBody
                            || (match thunkBody with
                                // ... or the body is NOTHING BUT another
                                // immediately-invoked thunk (nested damage).
                                // A body that merely STARTS with a thunk and
                                // carries more statements is a justified
                                // wrap — collapsing it would reopen the
                                // wrap/unwrap oscillation from the other side
                                | LetOrUseE innerLou when not innerLou.IsBang ->
                                    match innerLou.Bindings, innerLou.Body with
                                    | [ SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ innerF ]))) ],
                                      SynExpr.App(
                                          funcExpr = SynExpr.Ident innerG; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
                                        isRunTailName innerF.idText && innerG.idText = innerF.idText
                                    | _ -> false
                                | _ -> false))
                        ->
                        // `return f ()` needs the return re-seated on the
                        // body's terminal expression; `f ()` needs nothing
                        let returnTerminal =
                            match thunkCall with
                            | SynExpr.App(funcExpr = SynExpr.Ident g; argExpr = SynExpr.Const(SynConst.Unit, _)) when
                                g.idText = f.idText
                                ->
                                Some None
                            | SynExpr.YieldOrReturn(
                                expr = SynExpr.App(funcExpr = SynExpr.Ident g; argExpr = SynExpr.Const(SynConst.Unit, _))) when
                                g.idText = f.idText
                                ->
                                match terminalExpr thunkBody with
                                // a branching terminal would need a return
                                // in every branch — out of scope
                                | SynExpr.IfThenElse _
                                | SynExpr.Match _
                                | SynExpr.MatchBang _
                                | SynExpr.TryWith _
                                | SynExpr.TryFinally _
                                | SynExpr.While _
                                | SynExpr.For _
                                | SynExpr.ForEach _ -> None
                                | t when t.Range.StartLine = t.Range.EndLine -> Some(Some t.Range)
                                | _ -> None
                            | _ -> None

                        match returnTerminal with
                        | Some terminal when
                            thunkBody.Range.StartLine > f.idRange.EndLine
                            && not (spansDirective source thunkBody.Range)
                            ->
                            let inner = thunkBody.Range
                            let shift = inner.StartColumn - expr.Range.StartColumn

                            let text =
                                [ for l in inner.StartLine .. inner.EndLine ->
                                      let line = source.GetLineString(l - 1)

                                      let line =
                                          if l = inner.EndLine then
                                              line.Substring(0, min line.Length inner.EndColumn)
                                          else
                                              line

                                      let line =
                                          match terminal with
                                          | Some tr when l = tr.StartLine && tr.StartColumn <= line.Length ->
                                              line.Insert(tr.StartColumn, "return ")
                                          | _ -> line

                                      if l = inner.StartLine then
                                          line.Substring(min line.Length inner.StartColumn)
                                      elif
                                          shift > 0
                                          && line.Length >= shift
                                          && line.Substring(0, shift).Trim() = ""
                                          && not (literalLines.Contains l)
                                      then
                                          line.Substring shift
                                      else
                                          line ]
                                |> String.concat "\n"

                            add expr.Range text StripKind.ThunkIdentity
                        | _ -> ()
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree

    suggestions
    |> Seq.filter (fun s -> not (spansDirective source s.Range))
    |> List.ofSeq
