/// Two accumulation refactorings:
///
/// 1. Mutable accumulator loop → fold/sum (FR0050, fix):
///
///        let mutable total = 0                let total = xs |> List.sum
///        for x in xs do               →
///            total <- total + x
///
///    The general shape becomes `<M>.fold (fun acc x -> ...) init xs` —
///    the same expression evaluated with the same bindings in the same
///    order, so the rewrite is behavior-preserving; `sum`/`sumBy`
///    specializations fire when the combine is FSharp.Core's `+` over a
///    zero initializer. The module matches the source's RESOLVED kind:
///    measured, `List.sum`/`Array.sum` run level with the mutable loop
///    while `Seq.sum` is ~50% slower on a list — which is why this is an
///    IDIOM rule (same shape, nicer spelling), not a performance one.
///
/// 2. Quadratic append in a loop (FR0051, note): `acc <- acc @ [x]` or
///    `acc <- Array.append acc [| x |]` copies the accumulator on every
///    iteration — O(n²). Accumulate into a ResizeArray, or cons (`::`)
///    and `List.rev` once at the end.
module FSharp.Refactor.Accumulation

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type FoldSuggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string }

/// What is being accumulated quadratically — the advice differs.
[<RequireQualifiedAccess>]
type QuadraticKind =
    /// `acc <- acc @ [x]` / `Array.append acc [| x |]`: ResizeArray, or
    /// cons and reverse once.
    | Collection
    /// `acc <- acc + s` on a STRING in a loop: the worst builder measured
    /// (57.8µs and 1MB for 1000 pieces, against 1.6µs/4.6KB for a
    /// StringBuilder) — StringBuilder, or collect and String.concat once.
    | Str

type QuadraticSuggestion =
    {
        Range: range
        /// The accumulator's name, for the message.
        Name: string
        Kind: QuadraticKind
    }

/// A loop pattern usable as a lambda parameter.
let private lambdaPatText (source: ISourceText) (pat: SynPat) =
    let text = textOfRange source pat.Range

    match pat with
    | SynPat.Named _
    | SynPat.Wild _
    | SynPat.Paren _ -> ValueSome text
    | SynPat.Tuple _ -> ValueSome $"({text})"
    | _ -> ValueNone

let private isZeroLike (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Int32 0, _)
    | SynExpr.Const(SynConst.Double 0.0, _) -> true
    | _ -> false

// does any expression inside `r` mention `name`?
let private mentionsIn (index: AstIndex.Index) (name: string) (r: range) =
    index.Exprs
    |> Array.exists (fun (_, e) ->
        match e with
        | SynExpr.Ident id when id.idText = name -> Range.rangeContainsRange r id.idRange
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when firstId.idText = name ->
            Range.rangeContainsRange r firstId.idRange
        | _ -> false)

/// Is the type (after abbreviations) IEnumerable<'T>, or something that
/// implements it? A `for` loop also accepts the NON-generic IEnumerable and
/// duck-typed GetEnumerator sources, which `Seq.fold`/`Seq.sum` do not — so
/// the rewrite must prove the source is a real seq<'T>, not assume it.
let private isGenericSeqType (t: FSharpType) =
    let seqName = "System.Collections.Generic.IEnumerable`1"

    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (let td = t.TypeDefinition

            td.IsArrayType
            || td.TryFullName = Some seqName
            || td.AllInterfaces
               |> Seq.exists (fun i -> i.HasTypeDefinition && i.TypeDefinition.TryFullName = Some seqName))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The identifier to resolve for a loop source: `xs`, `db.Orders`, `x.A.B`.
[<return: Struct>]
let private (|SourcePathLastIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// The collection MODULE matching the loop source's kind, or ValueNone
/// when the source is not provably a generic sequence at all (a `for`
/// loop also accepts the non-generic IEnumerable and duck-typed
/// GetEnumerator sources, which no Seq/List/Array function does — better
/// to skip a valid rewrite than to break one of those).
///
/// The kind matters beyond correctness: measured (1000 ints, Release),
/// the mutable loop runs ~2.2µs, `List.sum`/`Array.sum` match it — and
/// `Seq.sum` takes ~3.4µs, a PESSIMIZATION dressed as a cleanup. So the
/// rewrite names the concrete module whenever the type is known and only
/// falls back to Seq for a plain seq.
let private collectionModule (check: FSharpCheckFileResults) (source: ISourceText) (src: SynExpr) : string voption =
    let rec stripInstance (t: FSharpType) =
        if t.IsAbbreviation then
            stripInstance t.AbbreviatedType
        else
            t

    let moduleOfType (ident: Ident) =
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                let t =
                    try
                        value.ReturnParameter.Type
                    with _ ->
                        value.FullType

                (try
                    let t = stripInstance t

                    if t.HasTypeDefinition && t.TypeDefinition.IsArrayType then
                        ValueSome "Array"
                    elif
                        t.HasTypeDefinition
                        && t.TypeDefinition.TryFullName = Some "Microsoft.FSharp.Collections.FSharpList`1"
                    then
                        ValueSome "List"
                    elif isGenericSeqType t then
                        ValueSome "Seq"
                    else
                        ValueNone
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     ValueNone)
            | _ -> ValueNone
        | None -> ValueNone

    match stripParens src with
    | SynExpr.ArrayOrList(isArray = isArray) -> ValueSome(if isArray then "Array" else "List")
    | SynExpr.ArrayOrListComputed(isArray = isArray) -> ValueSome(if isArray then "Array" else "List")
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op)) when
        op.idText = "op_Range" || op.idText = "op_RangeStep"
        ->
        ValueSome "Seq"
    | SourcePathLastIdent id -> moduleOfType id
    | SynExpr.App(funcExpr = SourcePathLastIdent id) -> moduleOfType id
    | _ -> ValueNone

let private insideLoop (path: SyntaxNode list) =
    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.For _)
        | SyntaxNode.SynExpr(SynExpr.ForEach _)
        | SyntaxNode.SynExpr(SynExpr.While _) -> true
        | _ -> false)

/// Find both accumulation shapes. Requires typed check results (the
/// sum/sumBy specialization checks that `+` is FSharp.Core's).
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : FoldSuggestion list * QuadraticSuggestion list =
    let folds = ResizeArray<FoldSuggestion>()
    let quadratics = ResizeArray<QuadraticSuggestion>()

    if OptionModule.hasErrors check then
        [], []
    else
        let index = AstIndex.ofTree parseTree

        for path, expr in index.Exprs do
            match expr with
            // FR0050: let mutable acc = init; for pat in src do acc <- rhs; rest
            | LetOrUseE lou when
                not (lou.IsBang || lou.IsUse)
                && (match lou.Bindings with
                    | [ SynBinding(isMutable = true) ] -> true
                    | _ -> false)
                ->
                match lou.Bindings, lou.Body with
                | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = acc)); returnInfo = retInfo; expr = init) ],
                  SynExpr.Sequential(
                      expr1 = SynExpr.ForEach(pat = pat; enumExpr = src; bodyExpr = loopBody) as forEach; expr2 = rest) ->
                    let loopBody =
                        match loopBody with
                        | SynExpr.Do(expr = inner) -> inner
                        | other -> other

                    // an annotated `let mutable acc: T = init` carries the
                    // annotation as return info AND wraps init in a Typed
                    // node; the fold reads the bare initializer
                    let init =
                        match init with
                        | SynExpr.Typed(expr = inner) -> inner
                        | other -> other

                    match loopBody with
                    | SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), rhs, _) when
                        target.idText = acc.idText
                        && isSingleLine rhs.Range
                        && isSingleLine src.Range
                        && isSingleLine init.Range
                        && isSafeInline rhs
                        // acc must not be re-assigned in the continuation
                        && not (Regex.IsMatch(textOfRange source rest.Range, identifierPattern acc.idText + @"\s*<-"))
                        ->
                        // one resolution, not one in the guard and another
                        // for the module name — GetSymbolUseAtLocation is
                        // the expensive step of this whole rule
                        match lambdaPatText source pat, collectionModule check source src with
                        | ValueSome patText, ValueSome m ->
                            let srcText = atomicText source src

                            let replacementBody =
                                match rhs with
                                // acc + e with FSharp.Core's (+) over zero
                                | SynExpr.App(
                                    funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident lhsId)
                                    argExpr = e) when
                                    op.idText = "op_Addition"
                                    && lhsId.idText = acc.idText
                                    && isZeroLike init
                                    && not (mentionsIn index acc.idText e.Range)
                                    && OptionModule.resolvesToCoreOperator check source op
                                    ->
                                    match stripParens e with
                                    | SynExpr.Ident v when (patBoundNames pat |> List.tryExactlyOne) = Some v.idText ->
                                        $"{srcText} |> {m}.sum"
                                    | _ -> $"{srcText} |> {m}.sumBy (fun {patText} -> {textOfRange source e.Range})"
                                // acc + e over a STRING accumulator: a fold
                                // of (+) would still be O(n²) in allocations,
                                // String.concat builds the result once
                                | SynExpr.App(
                                    funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident lhsId)
                                    argExpr = e) when
                                    op.idText = "op_Addition"
                                    && lhsId.idText = acc.idText
                                    && (match stripParens init with
                                        | SynExpr.Const(SynConst.String _, _) -> true
                                        | _ -> false)
                                    && not (mentionsIn index acc.idText e.Range)
                                    && OptionModule.resolvesToCoreOperator check source op
                                    ->
                                    let mapped =
                                        match stripParens e with
                                        | SynExpr.Ident v when (patBoundNames pat |> List.tryExactlyOne) = Some v.idText ->
                                            srcText
                                        | _ -> $"{srcText} |> {m}.map (fun {patText} -> {textOfRange source e.Range})"

                                    // a LAZY seq through String.concat hits the slow
                                    // IEnumerable path — measured 42.7µs/194KB for 1000
                                    // pieces against 2.6µs/2KB once materialized — so a
                                    // plain-seq source gets a Seq.toArray first
                                    let concatenated =
                                        if m = "Seq" then
                                            $"{mapped} |> Seq.toArray |> String.concat \"\""
                                        else
                                            $"{mapped} |> String.concat \"\""

                                    match stripParens init with
                                    | SynExpr.Const(SynConst.String("", _, _), _) -> concatenated
                                    | _ -> $"{atomicText source init} + ({concatenated})"
                                | _ ->
                                    let body = textOfRange source rhs.Range

                                    // `xs |> M.fold (fun acc x -> acc.Add x) init` checks the
                                    // lambda BEFORE `init`, so a member lookup on the
                                    // accumulator meets an indeterminate type — "Lookup on
                                    // object of indeterminate type based on information
                                    // prior to this program point" (Fable's fable-library
                                    // List.fs, `node <- node.AppendConsNoTail x`). The
                                    // double-pipe form hands the tuple over first, so both
                                    // types are known inside the lambda; the mutable loop
                                    // it replaces knew them from `let mutable acc = init`
                                    if body.Contains($"{acc.idText}.") then
                                        $"({atomicText source init}, {srcText}) ||> {m}.fold (fun {acc.idText} {patText} -> {body})"
                                    else
                                        $"{srcText} |> {m}.fold (fun {acc.idText} {patText} -> {body}) {atomicText source init}"

                            // `let mutable sum: IAdaptiveValue<int> = ..`
                            // carries its annotation as the binding's
                            // return info; the folded binding keeps it
                            // (Mibo lost one and inferred something else)
                            let annotation =
                                match retInfo with
                                | Some(SynBindingReturnInfo(typeName = t)) when isSingleLine t.Range ->
                                    Some(textOfRange source t.Range)
                                | _ -> None

                            // when the loop is followed by nothing but the
                            // accumulator itself — `let flags = .. |>
                            // Array.fold ..` with a bare `flags` line after
                            // it, the shape left on Mibo and the compiler —
                            // the fold expression IS the result: binding
                            // and trailing use collapse into it. An
                            // annotated binding keeps its `let`, since the
                            // annotation may be what makes it typecheck
                            let trailingUseOnly =
                                annotation.IsNone
                                && (match rest with
                                    | SynExpr.Ident r -> r.idText = acc.idText
                                    | _ -> false)

                            let editRange, replacement =
                                if trailingUseOnly then
                                    Range.mkRange expr.Range.FileName expr.Range.Start rest.Range.End, replacementBody
                                else
                                    let annotated =
                                        match annotation with
                                        | Some t -> $"{acc.idText}: {t}"
                                        | None -> acc.idText

                                    Range.mkRange expr.Range.FileName expr.Range.Start forEach.Range.End,
                                    $"let {annotated} = {replacementBody}"

                            // a fold that lands as a 150-character line is
                            // not the cleanup it claims to be
                            if
                                not (spansDirective source editRange)
                                && expr.Range.StartColumn + replacement.Length <= 100
                            then
                                folds.Add
                                    { Range = editRange
                                      OriginalText = textOfRange source editRange
                                      ReplacementText = replacement }
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
            // FR0051: quadratic append inside a loop — `acc <- acc @ [x]`,
            // the module spellings List.append/Array.append, and the
            // ref-cell form `acc.Value <- acc.Value @ [x]`
            | SynExpr.LongIdentSet(SynLongIdent(id = ([ _ ] | [ _; _ ]) as accIds), rhs, _) when
                insideLoop path
                && (match accIds with
                    | [ _ ] -> true
                    | [ _; v ] -> v.idText = "Value"
                    | _ -> false)
                ->
                let acc = List.head accIds

                let isAcc (e: SynExpr) =
                    match e with
                    | SynExpr.Ident i -> i.idText = acc.idText
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ i; v ])) ->
                        i.idText = acc.idText && v.idText = "Value"
                    | _ -> false

                let quadratic =
                    match rhs with
                    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = _) when
                        op.idText = "op_Append" && isAcc lhs
                        ->
                        true
                    | SynExpr.App(
                        funcExpr = SynExpr.App(
                            funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = a1)
                        argExpr = a2) when
                        (m.idText = "Array" || m.idText = "List")
                        && f.idText = "append"
                        && (isAcc a1 || isAcc a2)
                        ->
                        true
                    | _ -> false

                if quadratic then
                    quadratics.Add
                        { Range = expr.Range
                          Name = acc.idText
                          Kind = QuadraticKind.Collection }
                else
                    // `acc <- acc + s` on a STRING: quadratic copying, the
                    // worst string builder measured. `+` on numbers is the
                    // most ordinary code there is, so the accumulator must
                    // PROVABLY be a string (typed resolution)
                    let stringQuadratic =
                        match rhs with
                        // the appended operand must not be a NUMERIC literal:
                        // `i <- i + 1` is the most common statement in any
                        // loop, and resolving symbols for every counter
                        // increment put this rule at the top of the
                        // slow-analyzer list. A string accumulator never has
                        // a numeric literal on the right.
                        | SynExpr.App(
                            funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = appended) when
                            op.idText = "op_Addition"
                            && isAcc lhs
                            && (match stripParens appended with
                                | SynExpr.Const(
                                    constant = SynConst.Int32 _ | SynConst.Int64 _ | SynConst.Double _ | SynConst.Single _ | SynConst.Decimal _ | SynConst.Byte _ | SynConst.UInt32 _ | SynConst.UInt64 _ | SynConst.Int16 _ | SynConst.UInt16 _ | SynConst.SByte _) ->
                                    false
                                | _ -> true)
                            ->
                            // string-ness first: it is the selective check
                            // (few accumulators are strings, almost every
                            // (+) is FSharp.Core's), so the second
                            // resolution rarely runs
                            (let r = acc.idRange
                             let lineText = source.GetLineString(r.EndLine - 1)

                             match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ acc.idText ]) with
                             | Some symbolUse ->
                                 match symbolUse.Symbol with
                                 | :? FSharpMemberOrFunctionOrValue as value ->
                                     (try
                                         let t = OptionModule.stripAbbreviations value.FullType

                                         t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.String"
                                      with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                          false)
                                 | _ -> false
                             | None -> false)
                            && OptionModule.resolvesToCoreOperator check source op
                        | _ -> false

                    if stringQuadratic then
                        quadratics.Add
                            { Range = expr.Range
                              Name = acc.idText
                              Kind = QuadraticKind.Str }
            | _ -> ()

        // FR0050's fold fix already rewrites its exact shape into a single
        // String.concat — a note on the same site would nag about code the
        // fix is about to remove
        let quadratics =
            quadratics
            |> Seq.filter (fun q ->
                q.Kind = QuadraticKind.Collection
                || not (folds |> Seq.exists (fun f -> Range.rangeContainsRange f.Range q.Range)))

        List.ofSeq folds, List.ofSeq quadratics

// ---- FR0107: mutable flag loop → exists/forall ----

/// May the predicate be evaluated FEWER times than the loop evaluated it?
/// `exists` short-circuits where the flag loop kept iterating, so unlike
/// FR0050's fold (same evaluations, same order) this rewrite is only safe
/// when the predicate visibly does nothing but answer: any assignment,
/// sequencing, statement-shaped construct or `ignore` anywhere inside it
/// disqualifies the whole loop. A heuristic, not a purity proof — it errs
/// toward silence.
let private effectFreeIn (index: AstIndex.Index) (r: range) =
    index.Exprs
    |> Array.forall (fun (_, e) ->
        not (Range.rangeContainsRange r e.Range)
        || (match e with
            | SynExpr.Set _
            | SynExpr.LongIdentSet _
            | SynExpr.DotSet _
            | SynExpr.DotIndexedSet _
            | SynExpr.NamedIndexedPropertySet _
            | SynExpr.DotNamedIndexedPropertySet _
            | SynExpr.Sequential _
            | SynExpr.Do _
            | SynExpr.DoBang _
            | SynExpr.While _
            | SynExpr.For _
            | SynExpr.ForEach _
            | SynExpr.TryWith _
            | SynExpr.TryFinally _
            | SynExpr.LetOrUse _ -> false
            | SynExpr.Ident id -> id.idText <> "ignore"
            | _ -> true))

/// Mutable boolean flag set inside a loop → exists/forall (FR0107, fix):
///
///     let mutable found = false          let found =
///     for x in xs do              →          xs |> List.exists (fun x -> p x)
///         if p x then found <- true
///
/// The `true`-initialized dual becomes `forall` with the predicate
/// negated. Gates: the loop body is EXACTLY the one `if`, no `else`; the
/// assigned literal is the initializer's opposite; the predicate never
/// mentions the flag, passes `effectFreeIn`, and fits one line; nothing
/// reassigns the flag after the loop; and the source resolves to a real
/// List/Array/Seq the same way FR0050's fold does. `exists`/`forall`
/// short-circuit, so the rewrite does the same or less work — never more.
let findFlagLoops (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : FoldSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for _, expr in index.Exprs do
              match expr with
              | LetOrUseE lou when not (lou.IsBang || lou.IsUse) ->
                  match lou.Bindings, lou.Body with
                  | [ SynBinding(isMutable = true; headPat = SynPat.Named(ident = SynIdent(ident = flag)); expr = init) ],
                    SynExpr.Sequential(
                        expr1 = SynExpr.ForEach(pat = pat; enumExpr = src; bodyExpr = loopBody) as forEach; expr2 = rest) ->
                      let loopBody =
                          match loopBody with
                          | SynExpr.Do(expr = inner) -> inner
                          | other -> other

                      // a prefix of PURE let-bindings folds into the lambda:
                      //     for l in xs do
                      //         let t = f l
                      //         if t = "x" then found <- true
                      // is still an exists question — the lets ride along as
                      // `fun l -> let t = f l in t = "x"`. Each binding must
                      // be immutable, single-line, effect-free, and silent
                      // about the flag
                      let rec unwrapLets acc body =
                          match body with
                          | LetOrUseE innerLet when
                              not (innerLet.IsBang || innerLet.IsUse)
                              && (match innerLet.Bindings with
                                  | [ SynBinding(isMutable = false; headPat = letPat; expr = rhs) ] ->
                                      isSingleLine rhs.Range
                                      && isSingleLine letPat.Range
                                      && effectFreeIn index rhs.Range
                                      && not (mentionsIn index flag.idText rhs.Range)
                                  | _ -> false)
                              ->
                              match innerLet.Bindings with
                              | [ SynBinding(headPat = letPat; expr = rhs) ] ->
                                  unwrapLets
                                      ((textOfRange source letPat.Range, textOfRange source rhs.Range) :: acc)
                                      innerLet.Body
                              | _ -> List.rev acc, body
                          | other -> List.rev acc, other

                      let letPrefix, loopBody = unwrapLets [] loopBody

                      match stripParens init, loopBody with
                      | SynExpr.Const(SynConst.Bool initVal, _),
                        SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenBranch; elseExpr = None) ->
                          match stripParens thenBranch with
                          | SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), assigned, _) when
                              target.idText = flag.idText
                              && (match stripParens assigned with
                                  | SynExpr.Const(SynConst.Bool b, _) -> b = not initVal
                                  | _ -> false)
                              && isSingleLine cond.Range
                              && isSingleLine src.Range
                              && not (mentionsIn index flag.idText cond.Range)
                              && effectFreeIn index cond.Range
                              // the flag must not be re-assigned in the continuation
                              && not (
                                  Regex.IsMatch(textOfRange source rest.Range, identifierPattern flag.idText + @"\s*<-")
                              )
                              ->
                              match lambdaPatText source pat, collectionModule check source src with
                              | ValueSome patText, ValueSome m ->
                                  let srcText = atomicText source src
                                  let condText = textOfRange source cond.Range

                                  let lets =
                                      letPrefix
                                      |> List.map (fun (name, rhs) -> $"let {name} = {rhs} in ")
                                      |> String.concat ""

                                  let call =
                                      if initVal then
                                          // starts true, falsified by cond:
                                          // the loop computes forall (not cond)
                                          let negated =
                                              match stripParens cond with
                                              | SynExpr.App(funcExpr = SingleIdent notId; argExpr = inner) when
                                                  notId.idText = "not"
                                                  ->
                                                  textOfRange source inner.Range
                                              | _ -> $"not ({condText})"

                                          $"{srcText} |> {m}.forall (fun {patText} -> {lets}{negated})"
                                      else
                                          $"{srcText} |> {m}.exists (fun {patText} -> {lets}{condText})"

                                  let editRange = Range.mkRange expr.Range.FileName expr.Range.Start forEach.Range.End

                                  if not (spansDirective source editRange) then
                                      { Range = editRange
                                        OriginalText = textOfRange source editRange
                                        ReplacementText = $"let {flag.idText} = {call}" }
                              | _ -> ()
                          | _ -> ()
                      | _ -> ()
                  | _ -> ()
              | _ -> () ]
