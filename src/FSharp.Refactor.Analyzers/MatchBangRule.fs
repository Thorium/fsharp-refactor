/// Refactoring (modernization, F# 4.5+): a `let!` whose binder exists only
/// to be matched collapses into `match!`.
///
///     async {                          async {
///         let! x = fetch ()                match! fetch () with
///         match x with            →        | Some v -> ...
///         | Some v -> ...                  | None -> ...
///         | None -> ...                }
///     }
///
/// Safety rules:
///   - the `let!` binds a single simple name (no `use!`, no `and!`, no
///     pattern destructuring) and the continuation is exactly the match
///   - the binder is the match scrutinee and appears NOWHERE else — a use
///     inside a clause body would dangle once the binding is gone
///   - the bound expression and the binding line are single-line, and the
///     `let!` owns its whole line so the line delete removes exactly it —
///     together with any blank lines between it and the match, so no empty
///     line is left where the binding was
module FSharp.Refactor.MatchBangRule

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `let!` binding, where the hint anchors.
        Range: range
        Name: string
        /// (range, original, replacement) edits: delete the let! line,
        /// rewrite `match x` into `match! comp`.
        Edits: (range * string * string) list
    }

/// The computation's text, parenthesized only when its shape could regroup
/// against the following keyword (a trailing lambda, if, match, try) — an
/// application like `fetch ()` stays bare.
let private computationText (source: ISourceText) (comp: SynExpr) =
    let text = textOfRange source comp.Range
    if isSafeInline comp then text else $"({text})"

/// Every mention of `name` (read or assigned) inside `r`, except at
/// `exceptRange`.
let private mentionedInside (index: AstIndex.Index) (r: range) (exceptRange: range) (name: string) =
    index.Exprs
    |> Array.exists (fun (_, e) ->
        match e with
        | SynExpr.Ident id when id.idText = name ->
            Range.rangeContainsRange r id.idRange
            && not (Range.equals id.idRange exceptRange)
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when firstId.idText = name ->
            Range.rangeContainsRange r firstId.idRange
        | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) when firstId.idText = name ->
            Range.rangeContainsRange r e.Range
        | _ -> false)

/// The trailing statements of a sequential chain, flattened in order.
[<TailCall>]
let rec private sequentialChainLoop (acc: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.Sequential(expr1 = e1; expr2 = e2) -> sequentialChainLoop (e1 :: acc) e2
    | last -> List.rev (last :: acc)

/// Find the F# 8 `while!` idiom (FR0078): the announcement's three-part
/// shape, and ONLY that shape — `while!` re-evaluates its condition every
/// iteration, so a lone `let! c = cond` + `while c do` is NOT equivalent
/// (it loops on a stale bool) and never matches.
///
///     let! first = check ()               while! check () do
///     let mutable go = first         →        body
///     while go do
///         body
///         let! next = check ()
///         go <- next
///
/// Gates: the three binders are used nowhere beyond their roles, the two
/// condition computations are textually identical, and every deleted
/// binding owns its whole line.
let findWhileBang (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let ownsItsLine (r: range) (expectedPrefix: string) (text: string) =
        isSingleLine r
        && (source.GetLineString(r.StartLine - 1)).Trim() = $"{expectedPrefix}{text}"

    let fullLineDelete (r: range) =
        let range =
            Range.mkRange r.FileName (Position.mkPos r.StartLine 0) (Position.mkPos (r.StartLine + 1) 0)

        range, textOfRange source range, ""

    [ for _, expr in index.Exprs do
          match expr with
          | LetOrUseE louBang when louBang.IsBang && not louBang.IsUse ->
              match louBang.Bindings, louBang.Body with
              | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = first)); expr = comp0) as bang0 ],
                LetOrUseE louMut when not (louMut.IsBang || louMut.IsUse) && isSingleLine comp0.Range ->
                  match louMut.Bindings, louMut.Body with
                  | [ SynBinding(
                          isMutable = true
                          headPat = SynPat.Named(ident = SynIdent(ident = cond))
                          expr = SynExpr.Ident firstUse) as mutBinding ],
                    SynExpr.While(whileExpr = SynExpr.Ident whileCond; doExpr = loopBody) when
                      firstUse.idText = first.idText && whileCond.idText = cond.idText
                      ->
                      // the loop body's LAST statement must re-bind the same
                      // computation into the condition
                      match List.rev (sequentialChainLoop [] loopBody) with
                      | LetOrUseE rebind :: keptRev when rebind.IsBang && not rebind.IsUse ->
                          match rebind.Bindings, rebind.Body with
                          | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = next)); expr = compN) as bangN ],
                            SynExpr.LongIdentSet(SynLongIdent(id = [ setTarget ]), SynExpr.Ident setValue, setRange) when
                              setTarget.idText = cond.idText
                              && setValue.idText = next.idText
                              && textOfRange source comp0.Range = textOfRange source compN.Range
                              && not keptRev.IsEmpty
                              ->
                              // binder-role exclusivity: first only feeds the
                              // mutable, cond only drives the loop + set,
                              // next only feeds the set — and NONE of them
                              // may appear inside the condition computation
                              // (`let! next = step go` would leave `step go`
                              // referencing a deleted binder)
                              let checkRanges =
                                  comp0.Range :: compN.Range :: (keptRev |> List.map (fun e -> e.Range))

                              let mentionedInKept name =
                                  index.Exprs
                                  |> Array.exists (fun (_, e) ->
                                      match e with
                                      | SynExpr.Ident id when id.idText = name ->
                                          checkRanges |> List.exists (fun r -> Range.rangeContainsRange r id.idRange)
                                      | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when
                                          firstId.idText = name
                                          ->
                                          checkRanges
                                          |> List.exists (fun r -> Range.rangeContainsRange r firstId.idRange)
                                      | _ -> false)

                              let bang0Text = textOfRange source bang0.RangeOfBindingWithRhs
                              let mutText = textOfRange source mutBinding.RangeOfBindingWithRhs
                              let bangNText = textOfRange source bangN.RangeOfBindingWithRhs

                              if
                                  not (mentionedInKept first.idText)
                                  && not (mentionedInKept cond.idText)
                                  && not (mentionedInKept next.idText)
                                  // a BANG binding's range INCLUDES `let!`;
                                  // a plain binding's starts at the pattern
                                  && ownsItsLine bang0.RangeOfBindingWithRhs "" bang0Text
                                  && ownsItsLine mutBinding.RangeOfBindingWithRhs "let mutable " mutText
                                  && ownsItsLine bangN.RangeOfBindingWithRhs "" bangNText
                                  && isSingleLine setRange
                                  && (source.GetLineString(setRange.StartLine - 1)).Trim() = textOfRange source setRange
                              then
                                  let whileHeader =
                                      Range.mkRange expr.Range.FileName louMut.Body.Range.Start whileCond.idRange.End

                                  let edits =
                                      [ fullLineDelete bang0.RangeOfBindingWithRhs
                                        fullLineDelete mutBinding.RangeOfBindingWithRhs
                                        whileHeader,
                                        textOfRange source whileHeader,
                                        $"while! {computationText source comp0}"
                                        fullLineDelete bangN.RangeOfBindingWithRhs
                                        fullLineDelete setRange ]

                                  if
                                      textOfRange source whileHeader = $"while {cond.idText}"
                                      && not (edits |> List.exists (fun (r, _, _) -> spansDirective source r))
                                  then
                                      { Range = whileHeader
                                        Name = cond.idText
                                        Edits = edits }
                          | _ -> ()
                      | _ -> ()
                  | _ -> ()
              | _ -> ()
          | _ -> () ]

/// Find let!-then-match shapes. Parse-only.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [ for _, expr in index.Exprs do
          match expr with
          | LetOrUseE lou when lou.IsBang && not lou.IsUse ->
              match lou.Bindings, lou.Body with
              | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = binder)); expr = comp) as binding ],
                SynExpr.Match(expr = SynExpr.Ident scrutinee; trivia = { MatchKeyword = matchKeyword }) when
                  scrutinee.idText = binder.idText
                  && isSingleLine comp.Range
                  && isSingleLine binding.RangeOfBindingWithRhs
                  // the binder must appear only as the scrutinee
                  && not (mentionedInside index lou.Body.Range scrutinee.idRange binder.idText)
                  ->
                  let letLine = binding.RangeOfBindingWithRhs.StartLine
                  // a BANG binding's range INCLUDES the `let!` keyword
                  let bindingText = textOfRange source binding.RangeOfBindingWithRhs

                  // `let!` owns its whole line → the line delete is exact
                  if (source.GetLineString(letLine - 1)).Trim() = bindingText then
                      // the blank lines the author kept between the `let!`
                      // and its match go with the binding: left behind they
                      // open the computation with an empty line (`task {`,
                      // then nothing — fantomas's EndToEndTests) or double
                      // the gap above the match (fsharplint's TestApi.fs)
                      let matchLine = lou.Body.Range.StartLine
                      let mutable removeEnd = letLine + 1

                      while removeEnd < matchLine && (source.GetLineString(removeEnd - 1)).Trim() = "" do
                          removeEnd <- removeEnd + 1

                      let removeRange =
                          Range.mkRange
                              binding.RangeOfBindingWithRhs.FileName
                              (Position.mkPos letLine 0)
                              (Position.mkPos removeEnd 0)

                      let edits =
                          [ removeRange, textOfRange source removeRange, ""
                            matchKeyword, textOfRange source matchKeyword, "match!"
                            scrutinee.idRange, scrutinee.idText, computationText source comp ]

                      if not (edits |> List.exists (fun (r, _, _) -> spansDirective source r)) then
                          { Range = binding.RangeOfBindingWithRhs
                            Name = binder.idText
                            Edits = edits }
              | _ -> ()
          | _ -> () ]
