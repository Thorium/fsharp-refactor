/// Refactoring: an IsSome test followed by .Value access is a pattern
/// match without the throwing accessor.
///
///     if x.IsSome then x.Value + 1 else 0
///         →  match x with | Some v -> v + 1 | None -> 0
///
/// `.Value` throws when the option is None; after the rewrite the value is
/// only in scope where it exists. The `IsNone`, `not x.IsSome`, `x = None`
/// and `x <> None` forms are the same test (the comparison ones swap
/// branches like IsNone), an else-less unit `if` gains `| None -> ()`, and
/// a ValueOption receiver spells the cases ValueSome/ValueNone. A test
/// whose branch reads the payload is a match in disguise, whichever way
/// it is spelled: `Option.isSome x` beside `x.Value` is what this rule
/// exists to remove, so FR0010 never produces it there.
///
/// Branches on one line each give a one-line match; a branch laid out
/// over lines gives a match laid out over lines, each arm's body under
/// its clause at the `if`'s indentation plus four.
///
/// Safety rules:
///   - the receiver is a plain identifier that resolves (typed check
///     results) to FSharp.Core's option or voption — a custom type with
///     its own IsSome/Value members never matches
///   - the None-arm must not itself touch `.Value` (that code throws
///     today — not ours to rewrite), and the Some-arm must use it at
///     least once
///   - the multi-line form needs the `if` to open its own line, no
///     string literal spanning lines inside (re-indenting would change
///     it), no `elif` arm, and no match or try opening the Some arm (it
///     would take the `| None` clause)
///   - the binder name (`v`, falling back to `<x>Value`) must not appear
///     anywhere in the expression
module FSharp.Refactor.OptionMatch

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string }

/// "Some"/"None" or "ValueSome"/"ValueNone" for the receiver's type.
let private caseNamesFor (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            try
                let t = OptionModule.stripAbbreviations value.FullType

                if not t.HasTypeDefinition then
                    None
                else
                    match t.TypeDefinition.TryFullName with
                    | Some name when name.StartsWith "Microsoft.FSharp.Core.FSharpOption`" -> Some("Some", "None")
                    | Some name when name.StartsWith "Microsoft.FSharp.Core.FSharpValueOption`" ->
                        Some("ValueSome", "ValueNone")
                    | _ -> None
            with OptionModule.FcsSymbolFailure ->
                None
        | _ -> None
    | None -> None

/// `x.IsSome` / `x.IsNone` / `Option.isSome x` / `x |> Option.isSome` /
/// `not <any of those>` → (x, negated). The module-function spelling is
/// common in code ported from match-heavy style and tests the same thing.
[<return: Struct>]
let private (|OptionTest|_|) (e: SynExpr) =
    let (|ModuleTest|_|) (f: SynExpr) =
        match f with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; fn ])) when
            m.idText = "Option" || m.idText = "ValueOption"
            ->
            match fn.idText with
            | "isSome" -> Some false
            | "isNone" -> Some true
            | _ -> None
        | _ -> None

    // `x <> None` / `x = None` (either order, ValueNone too): the same
    // test spelled as a comparison. The receiver's option type, proven
    // by the caller, is what makes `None` FSharp.Core's case here
    let (|NoneCompared|_|) (e: SynExpr) =
        let isNone (e: SynExpr) =
            match e with
            | SynExpr.Ident n -> n.idText = "None" || n.idText = "ValueNone"
            | _ -> false

        match e with
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = l); argExpr = r) when
            op.idText = "op_Equality" || op.idText = "op_Inequality"
            ->
            let negated = op.idText = "op_Equality"

            match l, r with
            | SynExpr.Ident x, n when isNone n -> Some(x, negated)
            | n, SynExpr.Ident x when isNone n -> Some(x, negated)
            | _ -> None
        | _ -> None

    let rec test (e: SynExpr) =
        match e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ x; prop ])) when prop.idText = "IsSome" ->
            ValueSome(x, false)
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ x; prop ])) when prop.idText = "IsNone" ->
            ValueSome(x, true)
        | SynExpr.App(isInfix = false; funcExpr = ModuleTest negated; argExpr = SynExpr.Ident x) ->
            ValueSome(x, negated)
        | PipeApp(SynExpr.Ident x, ModuleTest negated) -> ValueSome(x, negated)
        | NoneCompared(x, negated) -> ValueSome(x, negated)
        | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = inner) ->
            match test (stripParens inner) with
            | ValueSome(x, negated) -> ValueSome(x, not negated)
            | ValueNone -> ValueNone
        | _ -> ValueNone

    test e

/// The operands of a same-operator boolean chain, left to right:
/// `a && b && c` yields [a; b; c].
[<TailCall>]
let rec private flattenBoolLoop (opName: string) (acc: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent o; argExpr = l); argExpr = r) when o.idText = opName ->
        flattenBoolLoop opName (r :: acc) l
    | leaf -> leaf :: acc

/// Find IsSome/Value conditionals. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // is `name` rebound anywhere inside `r` (lambda parameter, let,
        // match clause, loop pattern)? substituting under a shadow would
        // change which value the binder refers to
        let shadowedIn (name: string) (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (let boundPats =
                        match e with
                        | SynExpr.Lambda(parsedData = Some(pats, _)) -> pats
                        | LetOrUseE lou -> lou.Bindings |> List.map (fun (SynBinding(headPat = p)) -> p)
                        | SynExpr.Match(clauses = clauses)
                        | SynExpr.MatchBang(clauses = clauses)
                        | SynExpr.MatchLambda(matchClauses = clauses) ->
                            clauses |> List.map (fun (SynMatchClause(pat = p)) -> p)
                        | SynExpr.ForEach(pat = p) -> [ p ]
                        | _ -> []

                    boundPats |> List.exists (fun p -> patBoundNames p |> List.contains name)))

        // `x.Value` prefixes inside `r`: the sub-range covering `x.Value`
        let valueUses (x: string) (r: range) =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: second :: _)) when
                    first.idText = x
                    && second.idText = "Value"
                    && Range.rangeContainsRange r e.Range
                    ->
                    Some(Range.mkRange e.Range.FileName e.Range.Start second.idRange.End)
                | _ -> None)

        [ for path, expr in index.Exprs do
              match expr with
              // x.IsSome && p₁ && p₂ → x |> Option.exists (fun v -> p₁ && p₂)
              // x.IsNone || p₁ || p₂ → x |> Option.forall (fun v -> p₁ || p₂)
              | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = _); argExpr = _) when
                  (op.idText = "op_BooleanAnd" || op.idText = "op_BooleanOr")
                  // inside query { } / <@ @> the IsSome/IsNone property
                  // shape IS what the quotation's translator recognizes
                  && not (insideQuotedCode path)
                  && isSingleLine expr.Range
                  // only the OUTERMOST chain node; inner nodes re-visit it
                  && (match path with
                      | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent parentOp))) :: _
                      | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SingleIdent parentOp)) :: _ ->
                          parentOp.idText <> op.idText
                      | _ -> true)
                  ->
                  match flattenBoolLoop op.idText [] expr with
                  | OptionTest(x, negated) :: (_ :: _ as preds) when
                      // && needs the POSITIVE test, || the negative one
                      (op.idText = "op_BooleanAnd") = not negated
                      && preds |> List.sumBy (fun p -> (valueUses x.idText p.Range).Length) > 0
                      && preds |> List.forall (fun p -> not (shadowedIn x.idText p.Range))
                      // the predicates move into a fabricated lambda, where
                      // capturing a mutable local was FS0407 before F# 10
                      && preds
                         |> List.forall (fun p ->
                             not (OptionModule.capturesMutableLocal (AstIndex.ofTree parseTree) p.Range))
                      ->
                      match caseNamesFor check source x with
                      | Some(someCase, _) ->
                          let wholeText = textOfRange source expr.Range

                          let binder =
                              [ "v"; $"{x.idText}Value" ]
                              |> List.tryFind (fun name ->
                                  not (Regex.IsMatch(wholeText, @"\b" + Regex.Escape name + @"\b")))

                          match binder with
                          | Some binder ->
                              let substituted (operand: SynExpr) =
                                  valueUses x.idText operand.Range
                                  |> Array.sortByDescending (fun r -> r.StartColumn)
                                  |> Array.fold
                                      (fun (text: string) (r: range) ->
                                          let start = r.StartColumn - operand.Range.StartColumn
                                          let length = r.EndColumn - r.StartColumn
                                          text.Remove(start, length).Insert(start, binder))
                                      (textOfRange source operand.Range)

                              let moduleName = if someCase = "Some" then "Option" else "ValueOption"

                              let fn, sep =
                                  if op.idText = "op_BooleanAnd" then
                                      "exists", " && "
                                  else
                                      "forall", " || "

                              let joined = preds |> List.map substituted |> String.concat sep

                              { Range = expr.Range
                                OriginalText = wholeText
                                ReplacementText = $"{x.idText} |> {moduleName}.{fn} (fun {binder} -> {joined})" }
                          | None -> ()
                      | None -> ()
                  | _ -> ()
              | SynExpr.IfThenElse(ifExpr = OptionTest(x, negated); thenExpr = t; elseExpr = els; trivia = trivia) when
                  not (trivia.IsElif || insideQuotedCode path)
                  ->
                  let someArm, noneArm = if negated then els, Some t else Some t, els

                  // one-line branches keep the `if`'s place on its line;
                  // a branch laid out over lines becomes a match laid out
                  // over lines, which needs the `if` to open its own line
                  let oneLine =
                      isSingleLine t.Range && (els |> Option.forall (fun e -> isSingleLine e.Range))

                  let ownLine =
                      (source.GetLineString(expr.Range.StartLine - 1)).Substring(0, expr.Range.StartColumn).Trim() = ""

                  // an `elif` arm's range starts at its keyword — spliced
                  // after `| None ->` that is a syntax error, not a branch
                  let isElif (e: SynExpr) =
                      match e with
                      | SynExpr.IfThenElse(trivia = tr) -> tr.IsElif
                      | _ -> false

                  // re-indenting a branch would re-indent the inside of a
                  // string literal spanning lines
                  let multiLineString =
                      index.Exprs
                      |> Array.exists (fun (_, e) ->
                          match e with
                          | SynExpr.Const(SynConst.String _, r)
                          | SynExpr.InterpolatedString(range = r) ->
                              r.StartLine <> r.EndLine && Range.rangeContainsRange expr.Range r
                          | _ -> false)

                  let armsFit =
                      if oneLine then
                          (someArm |> Option.forall isSafeInline)
                          && (noneArm |> Option.forall isSafeInline)
                      else
                          ownLine
                          && not multiLineString
                          && not (someArm |> Option.exists isElif)
                          && not (noneArm |> Option.exists isElif)
                          // a match or try opening the Some arm would take
                          // the `| None` clause for one of its own
                          && (match someArm with
                              | Some(SynExpr.Match _ | SynExpr.MatchBang _ | SynExpr.MatchLambda _ | SynExpr.TryWith _) ->
                                  false
                              | _ -> true)

                  match someArm with
                  | Some someExpr when
                      armsFit
                      && (valueUses x.idText someExpr.Range).Length > 0
                      && not (shadowedIn x.idText someExpr.Range)
                      && (noneArm |> Option.forall (fun n -> (valueUses x.idText n.Range).Length = 0))
                      ->
                      match caseNamesFor check source x with
                      | Some(someCase, noneCase) ->
                          let wholeText = textOfRange source expr.Range

                          let binder =
                              [ "v"; $"{x.idText}Value" ]
                              |> List.tryFind (fun name ->
                                  not (Regex.IsMatch(wholeText, @"\b" + Regex.Escape name + @"\b")))

                          match binder with
                          | Some binder ->
                              // substitute x.Value prefixes right-to-left,
                              // by offset in the branch's own text (a
                              // branch may span lines)
                              let substituted (branch: SynExpr) =
                                  let text = textOfRange source branch.Range

                                  let lineStarts =
                                      let starts = ResizeArray<int>([ 0 ])

                                      for i in 0 .. text.Length - 1 do
                                          if text.[i] = '\n' then
                                              starts.Add(i + 1)

                                      starts

                                  let offsetOf (p: pos) =
                                      let relativeLine = p.Line - branch.Range.StartLine

                                      let column =
                                          if relativeLine = 0 then
                                              p.Column - branch.Range.StartColumn
                                          else
                                              p.Column

                                      lineStarts.[relativeLine] + column

                                  valueUses x.idText branch.Range
                                  |> Array.sortByDescending (fun r -> r.StartLine, r.StartColumn)
                                  |> Array.fold
                                      (fun (text: string) (r: range) ->
                                          let start = offsetOf r.Start
                                          let length = offsetOf r.End - start
                                          text.Remove(start, length).Insert(start, binder))
                                      text

                              if oneLine then
                                  let noneText =
                                      noneArm
                                      |> Option.map (fun n -> textOfRange source n.Range)
                                      |> Option.defaultValue "()"

                                  let replacement =
                                      sprintf
                                          "match %s with | %s %s -> %s | %s -> %s"
                                          x.idText
                                          someCase
                                          binder
                                          (substituted someExpr)
                                          noneCase
                                          noneText

                                  { Range = expr.Range
                                    OriginalText = wholeText
                                    ReplacementText = replacement }
                              else
                                  let indent = System.String(' ', expr.Range.StartColumn)
                                  let inner = indent + "    "

                                  // a branch's first line goes under its
                                  // clause; its continuation lines move by
                                  // the same amount, which they must have
                                  // room for when that amount is negative
                                  let laidOut (branch: SynExpr) (text: string) =
                                      let shift = expr.Range.StartColumn + 4 - branch.Range.StartColumn
                                      let lines = text.Split '\n'
                                      let continuation = lines |> Array.skip 1

                                      let leading (l: string) = l.Length - l.TrimStart().Length

                                      if
                                          shift < 0
                                          && continuation
                                             |> Array.exists (fun l ->
                                                 not (System.String.IsNullOrWhiteSpace l) && leading l < -shift)
                                      then
                                          None
                                      else
                                          let moved =
                                              continuation
                                              |> Array.map (fun l ->
                                                  if System.String.IsNullOrWhiteSpace l then ""
                                                  elif shift >= 0 then System.String(' ', shift) + l
                                                  else l.Substring(-shift))

                                          Some(String.concat "\n" (Array.append [| inner + lines.[0] |] moved))

                                  let noneBlock =
                                      match noneArm with
                                      | Some n -> laidOut n (textOfRange source n.Range)
                                      | None -> Some(inner + "()")

                                  match laidOut someExpr (substituted someExpr), noneBlock with
                                  | Some someBlock, Some noneBlock ->
                                      { Range = expr.Range
                                        OriginalText = wholeText
                                        ReplacementText =
                                          $"match {x.idText} with\n{indent}| {someCase} {binder} ->\n{someBlock}\n{indent}| {noneCase} ->\n{noneBlock}" }
                                  | _ -> ()
                          | None -> ()
                      | None -> ()
                  | _ -> ()
              | _ -> () ]
    |> List.filter (fun s -> not (spansDirective source s.Range))
