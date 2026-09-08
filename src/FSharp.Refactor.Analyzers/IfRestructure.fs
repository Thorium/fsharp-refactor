/// Three if-shape refactorings:
///
/// 1. `else if` flattens to `elif` (FR0111, fix): a nested if written as
///    the whole else-branch, when the `else` sits at the outer if's
///    column, is the elif that was meant.
///
/// 2. An if/elif chain comparing ONE identifier against distinct literals
///    becomes a match (FR0112, fix):
///
///        if x = 1 then a             match x with
///        elif x = 2 then b      →    | 1 -> a
///        else c                      | 2 -> b
///                                    | _ -> c
///
///    The scrutinee must be a bare identifier — a call re-evaluated per
///    comparison today would be evaluated once after the rewrite, which is
///    only the same thing when there is nothing to re-evaluate.
///
/// 3. Nested ifs merge into one `&&` (FR0113, fix), in the two shapes that
///    preserve semantics exactly:
///      - identical else-branches:
///        `if a then (if b then X else E) else E` → `if a && b then X else E`
///        (exactly one of the branches runs either way, so even an
///        effectful E is unchanged)
///      - no else at all, unit result:
///        `if a then (if b then X)` → `if a && b then X`
///    The tempting third shape — inner if WITHOUT else while the outer HAS
///    one — is deliberately absent: `if a && b then X else E` would run E
///    where the original ran nothing.
module FSharp.Refactor.IfRestructure

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string }

/// Parenthesize a condition whose top is `||` before it joins an `&&`:
/// precedence would otherwise regroup it.
let private conditionText (source: ISourceText) (cond: SynExpr) =
    let text = textOfRange source cond.Range

    match stripParens cond with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op)) when op.idText = "op_BooleanOr" ->
        match cond with
        | SynExpr.Paren _ -> text
        | _ -> $"({text})"
    | _ -> text

// ---- FR0111: else if -> elif ----

let findElseIf (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // a string literal spanning lines keeps its columns: dedenting the
    // block it sits in would rewrite the string
    let multiLineLiterals =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.Const(SynConst.String _, _)
            | SynExpr.InterpolatedString _ when not (isSingleLine e.Range) -> Some e.Range
            | _ -> None)

    [ for _, expr in index.Exprs do
          match expr with
          | SynExpr.IfThenElse(elseExpr = Some(SynExpr.IfThenElse(trivia = innerTrivia) as innerIf); trivia = trivia) ->
              match trivia.ElseKeyword, innerTrivia.IfKeyword with
              | Some elseKw, ifKw when
                  not innerTrivia.IsElif
                  // the else must own the if AND sit where elif may sit:
                  // at the outer if's column (offside rules for elif)
                  && elseKw.StartColumn = expr.Range.StartColumn
                  // only whitespace between `else` and `if` — a comment
                  // there would be swallowed
                  && (let between =
                          textOfRange source (Range.mkRange elseKw.FileName elseKw.End ifKw.Start)

                      System.String.IsNullOrWhiteSpace between)
                  ->
                  // the nested if's block — its then-body, elif chain and
                  // else — sat one level deeper than the `else` that owned
                  // it; under `elif` that level is gone, so every line of
                  // the block moves left by the difference (fsharplint's
                  // AstInfo.fs, suave's Bytes.fs kept the old depth and a
                  // trailing `else` deeper than its `elif`). An `if` on the
                  // `else`'s own line is already laid out for the flat form.
                  let dedent =
                      if ifKw.StartLine > elseKw.StartLine then
                          ifKw.StartColumn - elseKw.StartColumn
                      else
                          0

                  let tail =
                      textOfRange source (Range.mkRange ifKw.FileName ifKw.End innerIf.Range.End)

                  let lines = tail.Split '\n'

                  let movable =
                      dedent > 0
                      && lines
                         |> Array.skip 1
                         |> Array.forall (fun l ->
                             System.String.IsNullOrWhiteSpace l
                             || (l.Length >= dedent && System.String.IsNullOrWhiteSpace(l.Substring(0, dedent))))
                      && not (
                          multiLineLiterals
                          |> Array.exists (fun r -> Range.rangeContainsRange innerIf.Range r)
                      )

                  if movable then
                      let replaceRange = Range.mkRange elseKw.FileName elseKw.Start innerIf.Range.End

                      let moved =
                          lines
                          |> Array.mapi (fun i l ->
                              if i = 0 then l
                              elif l.Length >= dedent then l.Substring dedent
                              else l.TrimStart())
                          |> String.concat "\n"

                      { Range = replaceRange
                        OriginalText = textOfRange source replaceRange
                        ReplacementText = "elif" + moved }
                  else
                      let replaceRange = Range.mkRange elseKw.FileName elseKw.Start ifKw.End

                      { Range = replaceRange
                        OriginalText = textOfRange source replaceRange
                        ReplacementText = "elif" }
              | _ -> ()
          | _ -> () ]

// ---- FR0112: equality chain -> match ----

/// `<ident> = <literal>` — the identifier and the literal's source text.
[<return: Struct>]
let private (|IdentEqualsLiteral|_|) (source: ISourceText) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
        op.idText = "op_Equality"
        ->
        match stripParens lhs, stripParens rhs with
        | SynExpr.Ident id, (SynExpr.Const(constant = c) as lit)
        | (SynExpr.Const(constant = c) as lit), SynExpr.Ident id ->
            match c with
            | SynConst.Int32 _
            | SynConst.Int64 _
            | SynConst.Char _
            // verbatim/triple-quoted literals are valid match patterns and
            // the rewrite splices the ORIGINAL text, prefix included
            | SynConst.String(synStringKind = SynStringKind.Regular)
            | SynConst.String(synStringKind = SynStringKind.Verbatim)
            | SynConst.String(synStringKind = SynStringKind.TripleQuote) ->
                ValueSome(op, id, textOfRange source lit.Range)
            | _ -> ValueNone
        | _ -> ValueNone
    | _ -> ValueNone

let findEqualityChains
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharp.Compiler.CodeAnalysis.FSharpCheckFileResults)
    : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [ for _, expr in index.Exprs do
          match expr with
          // only chain HEADS: elif links carry IsElif and are skipped; a
          // plain if nested in another's else yields an inner suggestion
          // too, which the overlap hold-back resolves in the outer's favor
          | SynExpr.IfThenElse(trivia = trivia) when not trivia.IsElif ->
              // walk the elif chain collecting (op, ident, literal, branch)
              let rec collect acc (e: SynExpr) =
                  match e with
                  | SynExpr.IfThenElse(ifExpr = cond; thenExpr = t; elseExpr = Some els) ->
                      match (|IdentEqualsLiteral|_|) source cond with
                      | ValueSome(op, id, lit) when isSingleLine t.Range -> collect ((op, id, lit, t) :: acc) els
                      | _ -> None
                  // an else-less trailing if means the chain has NO terminal
                  // else: its text starts with `elif`, which would splice a
                  // keyword into the wildcard arm — caught adversarially, the
                  // apply-side rollback contained it, an editor would not have
                  | SynExpr.IfThenElse(elseExpr = None) -> None
                  | finalElse when isSingleLine finalElse.Range -> Some(List.rev acc, finalElse)
                  | _ -> None

              match collect [] expr with
              | Some(arms, finalElse) when arms.Length >= 2 ->
                  let (_, firstId, _, _) = List.head arms

                  let sameIdent =
                      arms |> List.forall (fun (_, id, _, _) -> id.idText = firstId.idText)

                  let literals = arms |> List.map (fun (_, _, lit, _) -> lit)
                  let distinct = (List.distinct literals).Length = literals.Length

                  // every `=` must be FSharp.Core's — a custom operator can
                  // mean anything, and match patterns use structural
                  // equality
                  let coreEquality =
                      arms
                      |> List.forall (fun (op, _, _, _) -> OptionModule.resolvesToCoreOperator check source op)

                  if sameIdent && distinct && coreEquality then
                      let indent = String.replicate expr.Range.StartColumn " "

                      let armLines =
                          arms
                          |> List.map (fun (_, _, lit, t) -> $"{indent}| {lit} -> {textOfRange source t.Range}")
                          |> String.concat "\n"

                      let replacement =
                          $"match {firstId.idText} with\n{armLines}\n{indent}| _ -> {textOfRange source finalElse.Range}"

                      if not (spansDirective source expr.Range) then
                          { Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = replacement }
              | _ -> ()
          | _ -> () ]

// ---- FR0113: nested if merge ----

let findNestedIfMerges (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [ for _, expr in index.Exprs do
          match expr with
          | SynExpr.IfThenElse(ifExpr = outerCond; thenExpr = thenBranch; elseExpr = outerElse; trivia = trivia) when
              not trivia.IsElif && isSingleLine outerCond.Range
              ->
              match stripParens thenBranch, outerElse with
              // same else on both levels
              | SynExpr.IfThenElse(
                  ifExpr = innerCond; thenExpr = innerThen; elseExpr = Some innerElse; trivia = innerTrivia),
                Some outerElseExpr when
                  not innerTrivia.IsElif
                  && isSingleLine innerCond.Range
                  && isSingleLine innerThen.Range
                  && isSingleLine innerElse.Range
                  && isSingleLine outerElseExpr.Range
                  && textOfRange source innerElse.Range = textOfRange source outerElseExpr.Range
                  ->
                  let a = conditionText source outerCond
                  let b = conditionText source innerCond

                  let replacement =
                      if isSingleLine expr.Range then
                          $"if {a} && {b} then {textOfRange source innerThen.Range} else {textOfRange source innerElse.Range}"
                      else
                          let indent = String.replicate expr.Range.StartColumn " "

                          $"if {a} && {b} then\n{indent}    {textOfRange source innerThen.Range}\n{indent}else\n{indent}    {textOfRange source innerElse.Range}"

                  if not (spansDirective source expr.Range) then
                      { Range = expr.Range
                        OriginalText = textOfRange source expr.Range
                        ReplacementText = replacement }
              // no else anywhere: unit-typed, nothing to lose
              | SynExpr.IfThenElse(ifExpr = innerCond; thenExpr = innerThen; elseExpr = None; trivia = innerTrivia),
                None when
                  not innerTrivia.IsElif
                  && isSingleLine innerCond.Range
                  && isSingleLine innerThen.Range
                  ->
                  let a = conditionText source outerCond
                  let b = conditionText source innerCond

                  let replacement =
                      if isSingleLine expr.Range then
                          $"if {a} && {b} then {textOfRange source innerThen.Range}"
                      else
                          let indent = String.replicate expr.Range.StartColumn " "
                          $"if {a} && {b} then\n{indent}    {textOfRange source innerThen.Range}"

                  if not (spansDirective source expr.Range) then
                      { Range = expr.Range
                        OriginalText = textOfRange source expr.Range
                        ReplacementText = replacement }
              | _ -> ()
          | _ -> () ]

// ---- FR0114: pyramid-of-doom flip (default off) ----

/// A large then-branch behind a small else reads bottom-heavy; flipping
/// puts the short exit first. `not` conditions unwrap instead of double
/// negating. Default OFF: happy-path-first is the opposite house style in
/// plenty of teams.
let findPyramidFlips
    (thenAtLeast: int)
    (elseAtMost: int)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [ for _, expr in index.Exprs do
          match expr with
          | SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenBranch; elseExpr = Some elseBranch; trivia = trivia) when
              not trivia.IsElif
              && isSingleLine cond.Range
              // flipping across an elif chain is a different rewrite
              && (match elseBranch with
                  | SynExpr.IfThenElse _ -> false
                  | _ -> true)
              && (thenBranch.Range.EndLine - thenBranch.Range.StartLine + 1) >= thenAtLeast
              && (elseBranch.Range.EndLine - elseBranch.Range.StartLine + 1) <= elseAtMost
              // both branches on their own lines at the same depth, so the
              // blocks swap verbatim
              && thenBranch.Range.StartLine > expr.Range.StartLine
              && elseBranch.Range.StartColumn = thenBranch.Range.StartColumn
              && not (spansDirective source expr.Range)
              ->
              let negated =
                  match stripParens cond with
                  | SynExpr.App(funcExpr = SingleIdent notId; argExpr = inner) when notId.idText = "not" ->
                      textOfRange source (stripParens inner).Range
                  | _ -> $"not ({textOfRange source cond.Range})"

              let indent = String.replicate expr.Range.StartColumn " "
              let branchIndent = String.replicate thenBranch.Range.StartColumn " "

              let replacement =
                  $"if {negated} then\n{branchIndent}{textOfRange source elseBranch.Range}\n{indent}else\n{branchIndent}{textOfRange source thenBranch.Range}"

              { Range = expr.Range
                OriginalText = textOfRange source expr.Range
                ReplacementText = replacement }
          | _ -> () ]

// ---- FR0115: base case first behind a compound guard (note) ----

type GuardOrderNote = { Range: range; Variable: string }

/// The wildcard arm is an ERROR arm: it raises, fails, or returns a
/// None/Error-shaped failure. Only then is the guarded arm ahead of it
/// the base case the note talks about — a wildcard computing a value
/// (`| _ -> None, fmtPos` in FCS's CheckFormatStrings, a fallback probe
/// in fsdocs' ProjectCracker, a lexer state's next state) is an
/// ordinary alternative, and there is nothing to invert.
let private isFailureArm (arm: SynExpr) =
    let failing =
        set
            [ "raise"
              "failwith"
              "failwithf"
              "invalidArg"
              "invalidOp"
              "nullArg"
              "reraise"
              "exit" ]

    let rec head (e: SynExpr) =
        match e with
        | SynExpr.App(funcExpr = f) -> head f
        | SynExpr.TypeApp(expr = inner)
        | SynExpr.Paren(expr = inner) -> head inner
        | SynExpr.Ident id -> Some id.idText
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idText
        | _ -> None

    let rec last (e: SynExpr) =
        match e with
        | SynExpr.Sequential(expr2 = e2) -> last e2
        | SynExpr.Paren(expr = inner) -> last inner
        | _ -> e

    match last arm with
    | SynExpr.Ident id -> id.idText = "None" || id.idText = "ValueNone"
    | SynExpr.App _ as app ->
        match head app with
        | Some name -> failing.Contains name || name = "Error"
        | None -> false
    | _ -> false

/// `match v with | x when a && b -> base | _ -> err`: the base case hides
/// first behind a compound guard, and every new error condition must be
/// threaded into it. Inverting — error guards first, base case as the
/// final wildcard — reads top-down and extends by appending. Advice only:
/// which case is "the base" is intent — so the wildcard must visibly be
/// the error arm (see isFailureArm).
let findGuardOrderNotes (parseTree: ParsedInput) (source: ISourceText) : GuardOrderNote list =
    let index = AstIndex.ofTree parseTree

    [ for _, expr in index.Exprs do
          match expr with
          | SynExpr.Match(
              clauses = [ SynMatchClause(pat = SynPat.Named(ident = SynIdent(ident = v)); whenExpr = Some guard)
                          SynMatchClause(pat = SynPat.Wild _; resultExpr = errArm) ])
          | SynExpr.MatchBang(
              clauses = [ SynMatchClause(pat = SynPat.Named(ident = SynIdent(ident = v)); whenExpr = Some guard)
                          SynMatchClause(pat = SynPat.Wild _; resultExpr = errArm) ])
          | SynExpr.MatchLambda(
              matchClauses = [ SynMatchClause(pat = SynPat.Named(ident = SynIdent(ident = v)); whenExpr = Some guard)
                               SynMatchClause(pat = SynPat.Wild _; resultExpr = errArm) ]) ->
              match stripParens guard with
              | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                  op.idText = "op_BooleanAnd"
                  && textOfRange source lhs.Range |> fun t -> t.Contains v.idText
                  && textOfRange source rhs.Range |> fun t -> t.Contains v.idText
                  && isFailureArm errArm
                  ->
                  { Range = expr.Range
                    Variable = v.idText }
              | _ -> ()
          | _ -> () ]
