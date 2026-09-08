/// Refactoring (performance/idiom): a loop whose whole body is a single
/// ResizeArray Add of the loop variable is one AddRange call.
///
///     for x in xs do acc.Add x            →  acc.AddRange xs
///
/// AddRange enumerates the source once in the order the loop did, so the
/// rewrite is behavior-preserving; when the source has a known count it
/// also pre-sizes the backing array.
///
/// A PROJECTED body (`acc.Add(x * 2)`, `acc.Add(f())`) stays a loop. The
/// `AddRange(xs |> Seq.map (fun x -> ..))` spelling it used to get has no
/// gain to offer: Seq.map allocates an enumerator and a closure, and
/// AddRange over a non-ICollection source enumerates item by item exactly
/// as the loop did — suave's `for f in xs do acc.Add(f())` came out as
/// `acc.AddRange((List.rev xs) |> Seq.map (fun f -> f()))`, longer, slower
/// and doubly parenthesised.
///
/// Safety rules:
///   - the loop body is exactly `acc.Add x` / `acc.Add(x)` of the loop
///     variable — any other statement or argument leaves the loop alone
///   - `Add` must resolve (typed check results) to
///     System.Collections.Generic.List`1.Add: HashSet.Add and friends have
///     different semantics and often no AddRange
///   - source, receiver, and argument are single-line
///   - the file must have no type errors
module FSharp.Refactor.AddRange

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string }

/// `recv.Add arg` — the Add identifier, the receiver's text range end, and
/// the argument.
[<return: Struct>]
let private (|AddCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) as recv; argExpr = arg) when
        ids.Length >= 2 && (List.last ids).idText = "Add" && isSingleLine recv.Range
        ->
        let addIdent = List.last ids

        let receiverRange =
            Range.mkRange
                recv.Range.FileName
                recv.Range.Start
                (Position.mkPos addIdent.idRange.StartLine (addIdent.idRange.StartColumn - 1))

        ValueSome(addIdent, receiverRange, arg)
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ addIdent ]))
        argExpr = arg) when addIdent.idText = "Add" && isSingleLine receiver.Range ->
        ValueSome(addIdent, receiver.Range, arg)
    | _ -> ValueNone

/// Does the Add identifier resolve to List<'T>.Add?
let private resolvesToListAdd (check: FSharpCheckFileResults) (source: ISourceText) (addIdent: Ident) =
    let r = addIdent.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ addIdent.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            (OptionModule.enclosingFullName value).StartsWith "System.Collections.Generic.List`"
        | _ -> false
    | None -> false

/// Find accumulate-only loops over List<'T>. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for _, expr in index.Exprs do
              match expr with
              | SynExpr.ForEach(pat = pat; enumExpr = enumExpr; bodyExpr = body) when isSingleLine enumExpr.Range ->
                  let body =
                      match body with
                      | SynExpr.Do(expr = inner) -> inner
                      | other -> other

                  match body with
                  | AddCall(addIdent, receiverRange, arg) when
                      isSingleLine arg.Range
                      && resolvesToListAdd check source addIdent
                      // the RECEIVER must be the same list on every
                      // iteration: `columns[tile.Position.X].Add tile` picks
                      // a list PER element, and `columns[tile.Position.X]
                      // .AddRange tiles` leaves `tile` undefined (Nu's
                      // Twenty 48 Gameplay)
                      && (let receiver = textOfRange source receiverRange

                          patNames pat
                          |> List.forall (fun name ->
                              not (
                                  System.Text.RegularExpressions.Regex.IsMatch(
                                      receiver,
                                      $@"\b{System.Text.RegularExpressions.Regex.Escape name}\b"
                                  )
                              )))
                      ->
                      let receiverText = textOfRange source receiverRange
                      let element = stripParens arg

                      // A RANGE source needs its own spelling, and the choice
                      // is measured, not cosmetic:
                      //   `xs.AddRange (a .. b)` does not even parse — F#
                      //   reads a parenthesised range after a member as
                      //   INDEXER syntax (FS0751);
                      //   `seq { a .. b }` parses but is 4-6x SLOWER than the
                      //   loop it replaces (a seq CE is not ICollection, so
                      //   AddRange enumerates item by item);
                      //   `[| a .. b |]` IS ICollection, so AddRange sizes
                      //   once and copies — 1.7x faster than the loop, and
                      //   allocating less than its growth-doubling reallocs.
                      let rangeSource =
                          match stripParens enumExpr with
                          | SynExpr.IndexRange _ as range -> Some(textOfRange source range.Range)
                          | _ -> None

                      let replacement =
                          match element, pat with
                          | SynExpr.Ident v, SynPat.Named(ident = SynIdent(ident = loopVar)) when
                              v.idText = loopVar.idText
                              ->
                              match rangeSource with
                              | Some range -> Some $"{receiverText}.AddRange [| {range} |]"
                              // argumentText parenthesises a non-atomic
                              // source exactly once (`acc.AddRange (List.rev
                              // xs)`) and never wraps one that is already
                              // parenthesised
                              | None -> Some(receiverText + ".AddRange " + argumentText source enumExpr)
                          // a projected body stays a loop: the Seq.map
                          // spelling measured no faster than the loop over
                          // a range (3-8x slower) and no faster elsewhere
                          // (suave's `acc.Add(f())` shape)
                          | _ -> None

                      match replacement with
                      | Some replacementText ->
                          { Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = replacementText }
                      | None -> ()
                  | _ -> ()
              | _ -> () ]
    |> List.filter (fun s -> not (spansDirective source s.Range))
