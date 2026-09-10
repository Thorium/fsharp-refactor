/// Refactoring advice for FS3511 ("this state machine is not statically
/// compilable"): oversized or `let rec`-carrying `task { }` bodies fall
/// back to the slow dynamic state-machine implementation at build time.
///
/// FS3511 itself is emitted during code generation, which the checker
/// never runs — no analyzer can observe the diagnostic. What IS statically
/// knowable:
///
///   - a `let rec` in the resumable body is a definite FS3511 producer
///   - very large bodies (many awaits, long span) are the at-risk shape
///
/// For flagged tasks the advice points at the shrinking moves:
///
///   a) plain `let`s before the first await add state-machine fields:
///      hoist them out before the builder
///   b) an if/match whose branches each await: give every branch its own
///      smaller `task { }` and pick between them outside
///   c) a long non-awaiting tail after the last await: extract it into a
///      plain function
///
/// Three of the moves now carry automatic fixes, each shaped so the moved
/// text stays verbatim wherever possible:
///
///   a) leading plain lets hoist ABOVE the builder line (dedented to its
///      column). Caveat: a throw in hoisted code now surfaces at the call
///      instead of faulting the returned Task — the same trade the advice
///      always asked for.
///   b) the non-awaiting tail wraps into a LOCAL function defined inside
///      the CE and called as its last statement. A nested function's body
///      is not resumable code (this rule itself treats lambdas as opaque),
///      so the state machine shrinks — and because the function stays in
///      scope, closures capture every CE local: no parameters, no type
///      annotations, no inference risk.
///   c) a body that IS an if/else whose both arms await splits into
///      `if c then task { .. } else task { .. }` — arm text verbatim.
///      With leading lets present, (a) goes first and the multi-pass loop
///      brings (c) around on the next pass. A `match` body is advice only.
///
/// None of the fixes touches a binding whose comments speak of allocation,
/// a hot path, perf or a fast path: that code was tuned by hand.
module FSharp.Refactor.TaskStateMachine

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type AdviceKind =
    /// A let rec sits in the resumable body — a definite FS3511.
    | HoistRecursiveFunction
    /// N plain lets before the first await can move out of the task.
    | HoistPlainLets of count: int
    /// Two or more branches await; each can be its own task.
    | SplitBranches
    /// Every branch of the closing expression returns; one `return`
    /// in front of the whole match replaces N exits through the builder.
    | HoistReturn of armCount: int
    /// N lines of non-awaiting code follow the last await.
    | ExtractTail of lineCount: int

type Suggestion =
    {
        Range: range
        Kind: AdviceKind
        /// (range, replacement) pairs when the advice carries an automatic
        /// fix; empty when the edit stays the author's call.
        Edits: (range * string) list
    }

/// Builder names whose computation expressions compile to state machines.
let private taskBuilders = set [ "task"; "backgroundTask" ]

/// `async` has no resumable state machine and so no FS3511 cliff: only the
/// return hoist - which is about generated code size, not the fallback -
/// applies to it, and only when `hoistReturnOnAsync` is turned on.
let private asyncBuilders = set [ "async" ]

/// Awaits at or above this count mark a task as at risk of FS3511.
[<Literal>]
let private BangThreshold = 8

/// Body line spans at or above this mark a task as at risk of FS3511.
[<Literal>]
let private LineThreshold = 60

let private isBangExpr (e: SynExpr) =
    match e with
    | LetOrUseE lou -> lou.IsBang
    | SynExpr.DoBang _
    | SynExpr.YieldOrReturnFrom _
    | SynExpr.MatchBang _ -> true
    | _ -> false

/// A binding a hoist can move: no attributes, not mutable (a closure in
/// the remaining body could not capture it once hoisted), not inline.
let private hoistable (binding: SynBinding) =
    match binding with
    | SynBinding(attributes = []; isMutable = false; isInline = false) -> true
    | _ -> false

/// Leading non-bang lets of a CE body: their count, the first binding's
/// range, and the rest of the body. Stops at the first binding a hoist
/// could not carry, so the count is exactly what the fix can move.
[<TailCall>]
let rec private peelPlainLets (count: int) (firstRange: range option) (e: SynExpr) =
    match e with
    | LetOrUseE lou when
        not (lou.IsBang || lou.IsUse || lou.IsRecursive)
        && lou.Bindings |> List.forall hoistable
        ->
        let firstRange =
            match firstRange, lou.Bindings with
            | None, binding :: _ -> Some binding.RangeOfBindingWithRhs
            | _ -> firstRange

        peelPlainLets (count + List.length lou.Bindings) firstRange lou.Body
    | _ -> count, firstRange, e

/// Only whitespace sits left of the range on its start line.
let private startsOwnLine (source: ISourceText) (r: range) =
    r.StartColumn = 0
    || (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = ""

let private leadingSpaces (line: string) =
    line.Length - line.TrimStart(' ').Length

let private isBlank (line: string) = System.String.IsNullOrWhiteSpace line

/// Lines of the file from `startLine` to `endLine` inclusive (1-based).
let private linesOf (source: ISourceText) (startLine: int) (endLine: int) =
    [ for l in startLine..endLine -> source.GetLineString(l - 1) ]

/// Re-indenting moved text is only safe when no line's leading whitespace
/// belongs to a string literal: multi-line strings travel verbatim-only.
let private multiLineStringSafe (lines: string list) =
    lines
    |> List.forall (fun l -> not ((l.Contains "\"\"\"") || (l.Contains "@\"")))

/// The textual probe above misses PLAIN literals spanning lines ("line1
/// <newline> line2" is legal F#) — the AST sees them exactly.
let private spansMultiLineLiteral (index: AstIndex.Index) (startLine: int) (endLine: int) =
    index.Exprs
    |> Array.exists (fun (_, e) ->
        (match e with
         | SynExpr.Const(SynConst.String _, _)
         | SynExpr.InterpolatedString _ -> true
         | _ -> false)
        && e.Range.StartLine < e.Range.EndLine
        && e.Range.StartLine <= endLine
        && e.Range.EndLine >= startLine)

/// Shift every non-blank line left by `n` columns; None when any line has
/// less indentation than that.
let private dedentBy (n: int) (lines: string list) =
    if n = 0 then
        Some lines
    elif lines |> List.forall (fun l -> isBlank l || leadingSpaces l >= n) then
        Some(lines |> List.map (fun l -> if isBlank l then "" else l.Substring n))
    else
        None

/// Extend a moved region's start upward over the comment block that
/// documents it: contiguous `//`/`///` lines, crossing blank lines only
/// when another comment line sits above them. Doc comments travel with
/// the code they describe; stray blank lines above the block stay put.
let private extendUpOverComments (source: ISourceText) (floorLine: int) (startLine: int) =
    let line n = source.GetLineString(n - 1)
    let isComment (l: string) = l.TrimStart().StartsWith "//"

    let mutable top = startLine
    let mutable probe = startLine - 1

    while probe > floorLine && (isComment (line probe) || isBlank (line probe)) do
        if isComment (line probe) then
            top <- probe

        probe <- probe - 1

    top

/// The terminal expression of a CE statement chain.
[<TailCall>]
let rec private terminalOf (e: SynExpr) =
    match e with
    | LetOrUseE lou when not lou.IsBang -> terminalOf lou.Body
    | SynExpr.Sequential(expr2 = b) -> terminalOf b
    | t -> t

/// A fresh function name for extracted code: the base name, or a numbered
/// variant when the file already uses that identifier.
/// The tail wrap's own output: a single nullary local function immediately
/// called (or returned). Wrapping THAT again — runTail2 around runTail,
/// runTail3 around runTail2 — sheds nothing from the state machine and
/// never converges; seen live three layers deep on management-portal.
let private alreadyWrappedTail (tail: SynExpr) =
    match tail with
    | LetOrUseE lou when not lou.IsBang ->
        match lou.Bindings, lou.Body with
        | [ SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ f ]); argPats = SynArgPats.Pats [ _ ])) ],
          (SynExpr.App(funcExpr = SynExpr.Ident g) | SynExpr.YieldOrReturn(
              expr = SynExpr.App(funcExpr = SynExpr.Ident g)) | SynExpr.YieldOrReturnFrom(
              expr = SynExpr.App(funcExpr = SynExpr.Ident g))) -> f.idText = g.idText
        | _ -> false
    | _ -> false

/// Comment text marking code the author tuned by hand.
let private handTunedPattern =
    Regex(@"\balloc|hot[ -]?path|\bperf|fast[ -]?path", RegexOptions.IgnoreCase ||| RegexOptions.Compiled)

let private freshName (source: ISourceText) (baseName: string) =
    let full =
        String.concat "\n" [ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ]

    [ baseName; baseName + "2"; baseName + "3" ]
    |> List.tryFind (fun candidate -> not (Regex.IsMatch(full, identifierPattern candidate)))

/// Advice for tasks that provably (let rec) or plausibly (size) hit FS3511.
/// `tailLines`: how many non-awaiting lines after the last await earn the
/// tail extraction. Configurable because the shed is a judgement call -
/// four lines is a small win for a new function, ten is a clear one:
///     { "FR0029": { "tailLines": 10 } }
let find (parseTree: ParsedInput) (source: ISourceText) (tailLines: int) (hoistReturnOnAsync: bool) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let containsBang (r: range) =
        index.Exprs
        |> Array.exists (fun (_, e) -> isBangExpr e && Range.rangeContainsRange r e.Range)

    /// A plain `use` inside a CE binds to the BUILDER's Using — in task and
    /// async that means DisposeAsync where the type offers it, and disposal
    /// ordered with the workflow. Lifting such a span into a plain closure
    /// silently re-binds it to a synchronous `using`, so movement stops at
    /// one (G-Research's GRA-DISPBEFOREASYNC names the same hazard).
    let containsUse (r: range) =
        index.Exprs
        |> Array.exists (fun (_, e) ->
            match e with
            | LetOrUseE lou -> lou.IsUse && Range.rangeContainsRange r e.Range
            | _ -> false)

    // the suffix of a CE's statement chain that follows its last awaiting
    // step (the one on `lastBangLine`), paired with whether the chain had
    // to descend into a branch to reach it: on the body's own spine, or —
    // when the spine ends in a match, an if or a try whose BODY holds the
    // last await — on the spine of that branch. Exception handlers and
    // finally blocks are not a tail (they are not business logic to
    // extract), and neither is a loop body (it re-awaits every
    // iteration); None when no step awaits
    let rec tailAfterLastBang (lastBangLine: int) (descended: bool) (e: SynExpr) : (SynExpr * bool) option =
        let holdsLast (r: range) =
            r.StartLine <= lastBangLine && lastBangLine <= r.EndLine

        let into = tailAfterLastBang lastBangLine

        match e with
        | LetOrUseE lou when not lou.IsBang ->
            match into descended lou.Body with
            | Some t -> Some t
            | None ->
                if lou.Bindings |> List.exists (fun b -> containsBang b.RangeOfBindingWithRhs) then
                    Some(lou.Body, descended)
                else
                    None
        | LetOrUseE lou -> // a let!/use! step: what follows is its body
            match into descended lou.Body with
            | Some t -> Some t
            | None -> Some(lou.Body, descended)
        | SynExpr.Sequential(expr1 = a; expr2 = b) ->
            match into descended b with
            | Some t -> Some t
            | None ->
                if isBangExpr a || containsBang a.Range then
                    Some(b, descended)
                else
                    None
        | SynExpr.Match(clauses = clauses)
        | SynExpr.MatchBang(clauses = clauses) ->
            clauses
            |> List.tryPick (fun (SynMatchClause(resultExpr = result)) ->
                if holdsLast result.Range then into true result else None)
        | SynExpr.IfThenElse(thenExpr = thenExpr; elseExpr = elseExpr) ->
            [ Some thenExpr; elseExpr ]
            |> List.tryPick (fun branch ->
                match branch with
                | Some b when holdsLast b.Range -> into true b
                | _ -> None)
        | SynExpr.TryWith(tryExpr = body)
        | SynExpr.TryFinally(tryExpr = body) when holdsLast body.Range -> into true body
        | _ -> None

    // an await of THIS task's resumable code inside the range
    let resumableBangIn (inResumableBody: range -> bool) (r: range) =
        index.Exprs
        |> Array.exists (fun (_, e) -> isBangExpr e && inResumableBody e.Range && Range.rangeContainsRange r e.Range)

    // LOCAL mutable bindings anywhere in the file, with where they are
    // declared: a closure cannot capture one (read or write), so a block
    // becoming a local function must not mention any declared OUTSIDE
    // itself — its own mutables move with it and stay legal. Module-level
    // mutables are static fields and capture fine, but they are
    // declarations, not exprs, so they never land in this set — the
    // over-approximation is only that a same-named local in another
    // function also blocks
    let localMutables =
        index.Exprs
        |> Array.collect (fun (_, e) ->
            match e with
            | LetOrUseE lou when not lou.IsBang ->
                lou.Bindings
                |> List.choose (fun b ->
                    match b with
                    | SynBinding(isMutable = true; headPat = SynPat.Named(ident = SynIdent(ident = id))) ->
                        Some(id.idText, b.RangeOfBindingWithRhs)
                    | _ -> None)
                |> Array.ofList
            | _ -> [||])

    let mentionsForeignMutable (blockRange: range) (text: string) =
        localMutables
        |> Array.exists (fun (name, declRange) ->
            not (Range.rangeContainsRange blockRange declRange)
            && Regex.IsMatch(text, identifierPattern name))

    // every identifier a pattern binds; None when the pattern has a shape
    // this walk does not understand (then nothing may rely on the answer)
    let rec patIdents (p: SynPat) : string list option =
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> Some [ id.idText ]
        | SynPat.Wild _ -> Some []
        | SynPat.Typed(pat = inner) -> patIdents inner
        | SynPat.Paren(pat = inner) -> patIdents inner
        | SynPat.Tuple(elementPats = els) ->
            els
            |> List.map patIdents
            |> List.fold
                (fun acc cur ->
                    match acc, cur with
                    | Some a, Some c -> Some(a @ c)
                    | _ -> None)
                (Some [])
        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> Some [ id.idText ]
        | _ -> None

    let comments = commentsWithText parseTree source

    [ for path, expr in index.Exprs do
          match expr with
          | SynExpr.App(
              isInfix = false; funcExpr = fe & IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
              taskBuilders.Contains builder
              || (hoistReturnOnAsync && asyncBuilders.Contains builder)
              ->
              // a hand-tuned hot path is not restructured behind the
              // author's back: a comment inside the enclosing binding
              // that speaks of allocation, a hot path, perf or a fast
              // path (suave's HttpOutput.fs) keeps every move advice-only
              let enclosingRange =
                  path
                  |> List.tryPick (fun node ->
                      match node with
                      | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                      | _ -> None)
                  |> Option.defaultValue expr.Range

              let handTuned =
                  comments
                  |> List.exists (fun (r, text) ->
                      Range.rangeContainsRange enclosingRange r && handTunedPattern.IsMatch text)

              let withhold (edits: (range * string) list) = if handTuned then [] else edits

              // sub-ranges whose contents are not this task's resumable code
              let opaqueRanges =
                  index.Exprs
                  |> Array.choose (fun (_, e) ->
                      match e with
                      | SynExpr.Lambda _
                      | SynExpr.ComputationExpr _ when Range.rangeContainsRange body.Range e.Range -> Some e.Range
                      | _ -> None)

              let inResumableBody (r: range) =
                  Range.rangeContainsRange body.Range r
                  && not (opaqueRanges |> Array.exists (fun o -> Range.rangeContainsRange o r))

              let recursiveLets =
                  index.Exprs
                  |> Array.filter (fun (_, e) ->
                      match e with
                      | LetOrUseE lou -> lou.IsRecursive && not lou.IsBang && inResumableBody e.Range
                      | _ -> false)

              let bangCount =
                  index.Exprs
                  |> Array.filter (fun (_, e) -> isBangExpr e && inResumableBody e.Range)
                  |> Array.length

              let bodyLines = body.Range.EndLine - body.Range.StartLine + 1

              // every OTHER advice here argues from FS3511, which only
              // resumable code can hit; on `async` the return hoist is the
              // whole of the rule
              let isAsync = asyncBuilders.Contains builder

              for _, letRec in (if isAsync then Array.empty else recursiveLets) do
                  match letRec with
                  | LetOrUseE lou ->
                      match lou.Bindings with
                      | binding :: _ ->
                          { Range = binding.RangeOfBindingWithRhs
                            Kind = AdviceKind.HoistRecursiveFunction
                            Edits = [] }
                      | [] -> ()
                  | _ -> ()

              // the return hoist is NOT about state-machine size: it
              // trades N exits through the builder for one, which is worth
              // the same in a twelve-line task as a hundred-line one. It
              // therefore sits OUTSIDE the oversized-task gate below
              let mutable hoistOffered = false

              // terminalOf stops at a `let!` by design; the closing
              // expression of a task body sits past every binding,
              // bang or not
              let rec closingOf (e: SynExpr) =
                  match e with
                  | LetOrUseE lou -> closingOf lou.Body
                  | SynExpr.Sequential(expr2 = b) -> closingOf b
                  | t -> t

              // e) a branch whose every LEAF returns can take one `return`
              // in front of it instead: the branch becomes an ordinary
              // expression, handed to the builder once, and the machine
              // sheds a resumption point per arm.
              //
              // Nothing moves — the branch stays where it is, one keyword
              // travels and the block gains an indent level. That is what
              // makes this safe where extracting a function was not: no
              // binding changes the order it is inferred in, and nothing is
              // captured.
              //
              // Found at any depth, and an awaiting arm blocks only ITSELF.
              // `if a then (if wed then return x else return y) else (do!
              // t; return z)` cannot hoist whole — the else awaits — but
              // the inner branch is clean and hoists on its own.
              // `match!` counts as a branch for DESCENT: it is a bang, so it
              // can never be hoisted itself, but its arms are where the
              // hoistable branch usually lives - `task { match! auth with
              // ... }` is the shape most of this codebase is written in, and
              // missing it hid every candidate beneath one
              let branchResults (e: SynExpr) =
                  match e with
                  | SynExpr.Match(clauses = cs)
                  | SynExpr.MatchBang(clauses = cs) -> Some(cs |> List.map (fun (SynMatchClause(resultExpr = r)) -> r))
                  | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some e2) -> Some [ t; e2 ]
                  | _ -> None

              // every leaf of a branch tree, as the position of its `return`
              // keyword — None as soon as one leaf is not a plain `return
              // <expr>` whose payload starts on the keyword's own line.
              // closingOf, not terminalOf: an arm opening with `let!` has its
              // branch AFTER the binding, and terminalOf stops at a bang
              let rec leafReturns (e: SynExpr) =
                  match closingOf e with
                  | SynExpr.YieldOrReturn(flags = (false, true); expr = payload; range = r) when
                      payload.Range.StartLine = r.StartLine
                      ->
                      Some [ r.StartLine, r.StartColumn ]
                  | inner ->
                      match branchResults inner with
                      | Some arms ->
                          let parts = arms |> List.map leafReturns

                          if parts |> List.forall Option.isSome then
                              Some(parts |> List.choose id |> List.concat)
                          else
                              None
                      | None -> None

              // the OUTERMOST hoistable branches: stop descending once one
              // qualifies, so a branch and its own child are never both
              // rewritten
              let rec hoistSites (e: SynExpr) =
                  match branchResults e with
                  | None -> []
                  | Some arms ->
                      match (if containsBang e.Range then None else leafReturns e) with
                      | Some starts when
                          not (spansDirective source e.Range)
                          && not (directiveFollows source e.Range)
                          // hoisting makes the branch the payload of one
                          // `return`, so it stops being CE code: a `use`
                          // inside it re-binds from the builder's Using to
                          // the language's, DisposeAsync silently becoming
                          // Dispose. Measured, not assumed - a type offering
                          // both logged "async" before and "sync" after
                          && not (containsUse e.Range)
                          && startsOwnLine source e.Range
                          ->
                          [ e, starts ]
                      | _ -> arms |> List.collect (fun arm -> hoistSites (closingOf arm))

              for site, starts in hoistSites (closingOf body) do
                  let positions = Set.ofList starts
                  let lines = linesOf source site.Range.StartLine site.Range.EndLine

                  let lastLine = List.length lines - 1

                  let rewritten =
                      lines
                      |> List.mapi (fun i line ->
                          let lineNo = site.Range.StartLine + i

                          // whatever follows the branch on its closing line -
                          // the enclosing `}`, most often - is outside the
                          // replaced range and stays in the file; re-emitting
                          // it here would give the file two of them
                          let line =
                              if i = lastLine && site.Range.EndColumn < line.Length then
                                  line.Substring(0, site.Range.EndColumn)
                              else
                                  line

                          // a one-line `if c then return a else return b`
                          // carries TWO keywords on the same line, so every
                          // one has to go - right to left, or removing the
                          // first would shift the column of the second
                          let stripped =
                              positions
                              |> Set.toList
                              |> List.filter (fun (l, _) -> l = lineNo)
                              |> List.map snd
                              |> List.sortDescending
                              |> List.fold
                                  (fun (acc: string) col ->
                                      if col + 6 <= acc.Length && acc.Substring(col, 6) = "return" then
                                          acc.Substring(0, col) + (acc.Substring(col + 6)).TrimStart()
                                      else
                                          acc)
                                  line
                              |> fun s -> if isBlank s then "" else s.TrimEnd()

                          if isBlank stripped then "" else "    " + stripped)

                  // a branch that fitted on one line has to keep `return` on
                  // that line: `return` alone with the payload below opens an
                  // offside context the payload's own line never closes, so a
                  // trailing `}` - or the next `else` - lands inside it
                  let hoisted =
                      match rewritten with
                      | [ single ] -> "return " + single.TrimStart()
                      | _ -> "return\n" + String.concat "\n" rewritten

                  hoistOffered <- true

                  { Range = site.Range
                    Kind = AdviceKind.HoistReturn starts.Length
                    Edits = withhold [ site.Range, hoisted ] }

              // the shrink advice only for genuinely oversized tasks
              if not isAsync && (bangCount >= BangThreshold || bodyLines >= LineThreshold) then
                  let fileName = body.Range.FileName
                  let taskIndentText = String.replicate fe.Range.StartColumn " "

                  // a) leading plain lets — the fix hoists their lines above
                  // the builder, dedented to its column. A throw in hoisted
                  // code surfaces at the call instead of faulting the Task;
                  // that trade is the advice itself
                  let letCount, firstLetRange, rest = peelPlainLets 0 None body

                  match firstLetRange with
                  | Some r when letCount > 0 ->
                      let hoistEdits =
                          // the binding's documenting comment block (blank
                          // lines between comment runs included) moves too
                          let startLine = extendUpOverComments source fe.Range.StartLine r.StartLine
                          let endLineExcl = rest.Range.StartLine

                          if
                              startsOwnLine source fe.Range
                              && startLine > fe.Range.StartLine
                              && endLineExcl > startLine
                              // the last moved binding must not spill onto
                              // the rest's line: whole lines move or nothing
                              && startsOwnLine source rest.Range
                          then
                              let movedLines = linesOf source startLine (endLineExcl - 1)

                              // the region's first CODE line must be the let
                              // itself and sets the dedent: FCS includes ///
                              // doc comments in the binding's range, and the
                              // extension above adds plain // blocks
                              let letLine =
                                  movedLines
                                  |> List.tryFind (fun l -> not (isBlank l || l.TrimStart().StartsWith "//"))
                                  |> Option.defaultValue ""

                              let movedRange =
                                  Range.mkRange fileName (Position.mkPos startLine 0) (Position.mkPos endLineExcl 0)

                              match dedentBy (leadingSpaces letLine - fe.Range.StartColumn) movedLines with
                              | Some dedented when
                                  letLine.TrimStart().StartsWith "let "
                                  && multiLineStringSafe movedLines
                                  && not (spansMultiLineLiteral index startLine (endLineExcl - 1))
                                  && not (spansDirective source movedRange)
                                  ->
                                  [ Range.mkRange fileName fe.Range.Start fe.Range.Start,
                                    (String.concat "\n" dedented).TrimStart() + "\n" + taskIndentText
                                    movedRange, "" ]
                              | _ -> []
                          else
                              []

                      { Range = r
                        Kind = AdviceKind.HoistPlainLets letCount
                        Edits = withhold hoistEdits }
                  | _ -> ()

                  // b) branching — when the body IS the if (letCount 0; pass
                  // order lets (a) clear the lets first), the fix splits it
                  // into a task per arm, arm text verbatim. One awaiting arm
                  // is enough: a synchronous arm becomes a trivially static
                  // `task { return .. }`, and the big arm gets its own
                  // smaller machine
                  match rest with
                  | SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenExpr; elseExpr = Some elseExpr; trivia = trivia) when
                      containsBang thenExpr.Range || containsBang elseExpr.Range
                      ->
                      let splitEdits =
                          let lineTailBlank (r: range) =
                              (source.GetLineString(r.EndLine - 1)).Substring(r.EndColumn).Trim() = ""

                          // `task { .. } |> f` or `.ContinueWith ..` binds
                          // tighter than a bare if/else would: leave those
                          let noContinuationAfter =
                              lineTailBlank expr.Range
                              && (seq { expr.Range.EndLine + 1 .. source.GetLineCount() }
                                  |> Seq.map (fun l -> (source.GetLineString(l - 1)).Trim())
                                  |> Seq.tryFind (fun t -> t <> "")
                                  |> Option.forall (fun t ->
                                      not (t.StartsWith '|' || t.StartsWith '.' || t.StartsWith ":>")))

                          // the arms are cut as LINE regions between four
                          // anchors — the `if .. then` header, the `else`
                          // keyword line, and the CE's closing brace line —
                          // so every comment line in the replaced span lands
                          // in one arm or the other by construction (a
                          // comment above an arm would otherwise sit outside
                          // the arm expression's range and be dropped, and
                          // the comment guard would hold the whole fix back)
                          let elseKwLine =
                              match trivia.ElseKeyword with
                              | Some ek when (source.GetLineString(ek.StartLine - 1)).Trim() = "else" ->
                                  Some ek.StartLine
                              | _ -> None

                          let ifLine = rest.Range.StartLine
                          let closeLine = expr.Range.EndLine

                          match elseExpr, elseKwLine with
                          | SynExpr.IfThenElse _, _ -> [] // elif chains stay advice
                          | _, Some elseKwLine when
                              letCount = 0
                              && startsOwnLine source fe.Range
                              // the if directly follows `task {`: no line of
                              // the replaced span sits outside the arms
                              && ifLine = fe.Range.StartLine + 1
                              && isSingleLine cond.Range
                              && (source.GetLineString(cond.Range.EndLine - 1)).TrimEnd().EndsWith "then"
                              && thenExpr.Range.StartLine > cond.Range.EndLine
                              && elseKwLine > thenExpr.Range.EndLine
                              && elseExpr.Range.StartLine > elseKwLine
                              && startsOwnLine source thenExpr.Range
                              && startsOwnLine source elseExpr.Range
                              && lineTailBlank thenExpr.Range
                              && lineTailBlank elseExpr.Range
                              && (source.GetLineString(closeLine - 1)).Trim() = "}"
                              && elseExpr.Range.EndLine < closeLine
                              && noContinuationAfter
                              && not (spansDirective source expr.Range)
                              ->
                              // arms re-home one level under their new task;
                              // verbatim when a dedent would not be safe
                              let armText (startLine: int) (endLine: int) =
                                  let lines = linesOf source startLine endLine

                                  let indent =
                                      lines
                                      |> List.filter (isBlank >> not)
                                      |> List.map leadingSpaces
                                      |> List.fold min System.Int32.MaxValue

                                  let shift = indent - (fe.Range.StartColumn + 4)

                                  match (if shift > 0 then dedentBy shift lines else None) with
                                  | Some d when multiLineStringSafe lines -> String.concat "\n" d
                                  | _ -> String.concat "\n" lines

                              // the arms keep the ORIGINAL builder — a
                              // backgroundTask split into plain tasks would
                              // silently lose its thread-pool start
                              [ Range.mkRange fileName (Position.mkPos fe.Range.StartLine 0) expr.Range.End,
                                taskIndentText
                                + "if "
                                + textOfRange source cond.Range
                                + $" then {builder} {{\n"
                                + armText (ifLine + 1) (elseKwLine - 1)
                                + "\n"
                                + taskIndentText
                                + $"}} else {builder} {{\n"
                                + armText (elseKwLine + 1) (closeLine - 1)
                                + "\n"
                                + taskIndentText
                                + "}" ]
                          | _ -> []

                      { Range = rest.Range
                        Kind = AdviceKind.SplitBranches
                        Edits = withhold splitEdits }
                  | SynExpr.Match(clauses = clauses)
                  | SynExpr.MatchBang(clauses = clauses) when
                      (clauses
                       |> List.filter (fun (SynMatchClause(resultExpr = result)) -> containsBang result.Range)
                       |> List.length)
                      >= 2
                      ->
                      // a match stays ADVICE: the documented split is the
                      // if/else body, arms cut as line regions into two
                      // tasks. The per-arm `return! task { .. }` wrap this
                      // once carried nested a machine inside every awaiting
                      // arm of suave's HttpOutput.fs — a shape the doc
                      // never promised, on a hand-tuned hot path
                      { Range = rest.Range
                        Kind = AdviceKind.SplitBranches
                        Edits = [] }
                  | _ -> ()

                  // c) a long non-awaiting tail after the last await — the
                  // fix wraps it in a LOCAL function inside the CE (a nested
                  // function's body is not resumable code) and calls it as
                  // the last statement; closures capture every CE local, so
                  // no parameters and no type annotations
                  let lastBangLine =
                      index.Exprs
                      |> Array.fold
                          (fun acc (_, e) ->
                              if isBangExpr e && inResumableBody e.Range then
                                  max acc e.Range.StartLine
                              else
                                  acc)
                          0

                  // the tail is the statement suffix after the last await,
                  // never a line count from that await to the closing
                  // brace: a multi-line `return!` argument, the `with`
                  // and `finally` of a try, and a `while` body that
                  // re-awaits are not non-awaiting code (suave's Proxy,
                  // Combinators and ConnectionHealthChecker)

                  let tail =
                      if lastBangLine > 0 then
                          tailAfterLastBang lastBangLine false body
                          |> Option.filter (fun (t, _) -> not (resumableBangIn inResumableBody t.Range))
                      else
                          None

                  match tail with
                  | Some(tail, descended) ->
                      // local function definitions in the tail compile to
                      // closures, not resumable code — they weigh nothing,
                      // and NOT counting them is what makes the extraction
                      // converge instead of re-wrapping its own output
                      let functionDefLines (r: range) =
                          index.Exprs
                          |> Array.sumBy (fun (_, e) ->
                              match e with
                              | LetOrUseE lou when not lou.IsBang && Range.rangeContainsRange r e.Range ->
                                  lou.Bindings
                                  |> List.sumBy (fun b ->
                                      match b with
                                      | SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))) ->
                                          let br = b.RangeOfBindingWithRhs
                                          br.EndLine - br.StartLine + 1
                                      | _ -> 0)
                              | _ -> 0)

                      // the note sits on the first non-awaiting statement,
                      // where the author can act on it — not on the blank
                      // or `with` line after the await
                      let noteRange = tail.Range

                      let tailLineCount =
                          tail.Range.EndLine - tail.Range.StartLine + 1 - functionDefLines tail.Range

                      // a tail that IS one `return <expr>` is already a single
                      // exit: the payload is ordinary code, not resumable, so
                      // extracting it sheds source lines and no state-machine
                      // states. It is also what the return hoist leaves behind,
                      // and wrapping that would undo the point of hoisting
                      let tailIsSingleReturn =
                          match tail with
                          | SynExpr.YieldOrReturn(flags = (false, true)) -> true
                          | _ -> false

                      if tailLineCount >= tailLines && not tailIsSingleReturn then
                          let tailEdits =
                              // a tail reached through a branch stays
                              // advice: the wrap is proven on the spine only
                              // the return hoist is the better answer to the
                              // same tail - one keyword instead of a new
                              // function - so the wrap stands down where it applies
                              match
                                  (if descended || hoistOffered then None else Some tail), freshName source "runTail"
                              with
                              | Some tail, Some fnName when
                                  not (containsBang tail.Range)
                                  && startsOwnLine source tail.Range
                                  && tail.Range.EndLine > tail.Range.StartLine
                                  && not (spansDirective source tail.Range)
                                  // size the WRAP by the tail's own extent, not
                                  // tailLineCount: the last bang can sit inside
                                  // a nested CE in an earlier binding, and that
                                  // anchor once inflated a 2-line tail into a
                                  // wrap that then re-wrapped itself every pass
                                  && tail.Range.EndLine - tail.Range.StartLine + 1 - functionDefLines tail.Range >= 4
                                  && not (alreadyWrappedTail tail)
                                  ->
                                  let returns =
                                      index.Exprs
                                      |> Array.filter (fun (_, e) ->
                                          match e with
                                          | SynExpr.YieldOrReturn _ ->
                                              Range.rangeContainsRange tail.Range e.Range && inResumableBody e.Range
                                          | _ -> false)

                                  let terminal = terminalOf tail

                                  let terminalReturn =
                                      match terminal with
                                      | SynExpr.YieldOrReturn _ -> Some terminal.Range
                                      | _ -> None

                                  let returnShapeOk =
                                      match terminalReturn with
                                      | Some tr ->
                                          returns.Length = 1 && Range.equals (returns |> Array.head |> snd).Range tr
                                      | None -> returns.Length = 0

                                  let tailLines = linesOf source tail.Range.StartLine tail.Range.EndLine
                                  let tailIndent = leadingSpaces (List.head tailLines)
                                  let ind = String.replicate tailIndent " "

                                  // strip the terminal `return` so the value
                                  // expression becomes the function's result
                                  let strippedLines =
                                      match terminalReturn with
                                      | Some tr ->
                                          let i = tr.StartLine - tail.Range.StartLine
                                          let line = List.item i tailLines

                                          if line.Substring(tr.StartColumn).StartsWith "return " then
                                              tailLines
                                              |> List.mapi (fun j l ->
                                                  if j = i then
                                                      l.Substring(0, tr.StartColumn) + l.Substring(tr.StartColumn + 7)
                                                  else
                                                      l)
                                              |> Some
                                          else
                                              None
                                      | None -> Some tailLines

                                  let closureEdits =
                                      match strippedLines with
                                      | Some lines when
                                          returnShapeOk
                                          && multiLineStringSafe lines
                                          && not (spansMultiLineLiteral index tail.Range.StartLine tail.Range.EndLine)
                                          && not (mentionsForeignMutable tail.Range (String.concat "\n" lines))
                                          // a `use` may not become a plain
                                          // closure `using`: fall through to
                                          // the task-returning variant below,
                                          // where it stays real CE syntax
                                          && not (containsUse tail.Range)
                                          ->
                                          let indented =
                                              lines
                                              |> List.map (fun l -> if isBlank l then "" else "    " + l)
                                              |> String.concat "\n"

                                          let call =
                                              match terminalReturn with
                                              | Some _ -> $"return {fnName} ()"
                                              | None -> $"{fnName} ()"

                                          [ Range.mkRange
                                                fileName
                                                (Position.mkPos tail.Range.StartLine 0)
                                                tail.Range.End,
                                            $"{ind}let {fnName} () =\n{indented}\n{ind}{call}" ]
                                      | _ -> []

                                  if not closureEdits.IsEmpty then
                                      closureEdits
                                  elif
                                      // EARLY RETURNS in the tail: a plain
                                      // closure cannot carry them, but a
                                      // task-returning local function can —
                                      // the tail stays a REAL task body
                                      // (returns and use bindings legal),
                                      // consumed with return!, and the outer
                                      // machine sheds the lines all the same
                                      multiLineStringSafe tailLines
                                      && not (spansMultiLineLiteral index tail.Range.StartLine tail.Range.EndLine)
                                      && not (mentionsForeignMutable tail.Range (String.concat "\n" tailLines))
                                  then
                                      let indented =
                                          tailLines
                                          |> List.map (fun l -> if isBlank l then "" else "    " + l)
                                          |> String.concat "\n"

                                      [ Range.mkRange fileName (Position.mkPos tail.Range.StartLine 0) tail.Range.End,
                                        $"{ind}let {fnName} () = {builder} {{\n{indented}\n{ind}}}\n{ind}return! {fnName} ()" ]
                                  else
                                      []
                              | _ -> []


                          { Range = noteRange
                            Kind = AdviceKind.ExtractTail tailLineCount
                            Edits = withhold tailEdits }
                  | None -> ()
          | _ -> () ]
