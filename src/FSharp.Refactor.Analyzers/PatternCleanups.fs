/// Three pattern-level cleanups in the ReSharper tradition:
///
/// 1. Cons of empty (FR0087): the pattern `x :: []` is `[ x ]`.
/// 2. All-wildcard case fields (FR0088): `Case(_, _)` matches exactly
///    what `Case _` matches; the field arity is noise. Typed-gated to
///    real union cases — a parameterized active pattern's arguments are
///    not field patterns.
/// 3. Tuple in a list literal (FR0089, note): `[ 1, 2 ]` is a
///    single-tuple list — `,` builds a tuple, `;` separates elements.
///    The classic paste-from-C# trap; advice only, single-tuple lists are
///    sometimes intended.
module FSharp.Refactor.PatternCleanups

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type ConsSuggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string }

type WildFieldsSuggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string
      CaseName: string }

type TupleInListSuggestion =
    {
        /// The editor's fix: the elements separated by `;`.
        Fix: range * string * string
        Range: range
        /// Element count of the accidental tuple.
        Elements: int
    }

/// The field count of the union case the identifier names, None for
/// anything else. The count matters: `Case(_)` on a case that takes NO
/// data is accepted, but `Case _` is not ("Pattern discard is not allowed
/// for union case that takes no data" — fsharplint's SynMemberKind
/// matches), so a nullary case drops the wildcard altogether.
let private unionCaseFields (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpUnionCase as uc ->
            (try
                Some uc.Fields.Count
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 None)
        | _ -> None
    | None -> None

/// Find all three. Requires typed check results for the union-case gate.
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : ConsSuggestion list * WildFieldsSuggestion list * TupleInListSuggestion list =
    let index = AstIndex.ofTree parseTree
    let conses = ResizeArray<ConsSuggestion>()
    let wilds = ResizeArray<WildFieldsSuggestion>()
    let tuples = ResizeArray<TupleInListSuggestion>()
    let hasErrors = OptionModule.hasErrors check

    for _, p in index.Pats do
        match p with
        // FR0087: x :: []
        | SynPat.ListCons(lhsPat = lhs; rhsPat = SynPat.ArrayOrList(_, [], _)) when
            isSingleLine p.Range && not ((textOfRange source lhs.Range).Contains ';')
            ->
            conses.Add
                { Range = p.Range
                  OriginalText = textOfRange source p.Range
                  ReplacementText = $"[ {textOfRange source lhs.Range} ]" }
        // FR0088: Case(_, _) — every field a wildcard
        | SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats [ SynPat.Paren(inner, _) ]) when
            not ids.IsEmpty
            && not hasErrors
            && (match inner with
                | SynPat.Tuple(elementPats = elems) when elems.Length >= 2 ->
                    elems
                    |> List.forall (fun e ->
                        match e with
                        | SynPat.Wild _ -> true
                        | _ -> false)
                | SynPat.Wild _ -> true
                | _ -> false)
            ->
            match unionCaseFields check source (List.last ids) with
            | Some fields ->
                let caseEnd = (List.last ids).idRange.End
                let editRange = Range.mkRange p.Range.FileName caseEnd p.Range.End

                wilds.Add
                    { Range = editRange
                      OriginalText = textOfRange source editRange
                      // a nullary case takes no wildcard at all
                      ReplacementText = if fields = 0 then "" else " _"
                      CaseName = (List.last ids).idText }
            | None -> ()
        | _ -> ()

    // FR0089: [ 1, 2 ] — the whole literal is one tuple. Only ALL-NUMERIC
    // tuples fire: that is the paste-trap shape, while a single tuple of
    // expressions ([ range, text, code ]) or of strings
    // ([ "SearchValues", "Create" ]) is a deliberate one-element table
    // `grid[0, 1, 2]` is INDEXING, not a literal. Since F# 6 that spells
    // as an ATOMIC application of a bracket to the thing before it — the
    // same parse shape as a list — so the atomic flag is what separates
    // them (`f [1; 2]`, with a space, is a real argument and NonAtomic).
    // The `.[ ]` spelling never reached here; the modern one it
    // recommends did, and TorchSharp code is nothing but multi-dimensional
    // indexing: 6 false notes in Fuuga's EvalTests alone.
    let inIndexPosition (path: SyntaxNode list) (e: SynExpr) =
        match path with
        | SyntaxNode.SynExpr(SynExpr.App(flag = ExprAtomicFlag.Atomic; argExpr = arg)) :: _ -> arg.Range = e.Range
        | _ -> false

    // A literal whose EXPECTED type is a tuple collection is the one-entry
    // table it looks like: `Map.ofList [ k, v ]`, `dict [ 1, 1 ]`, a user
    // function taking `(int * int) list`, or an annotation spelling the
    // tuple out (Mibo: 37 such notes, every one a one-entry map). The
    // literal's OWN type is always a tuple list, so the slot it fills —
    // the resolved parameter, or the annotation — is what is asked.
    let rec synTypeHasTuple (t: SynType) =
        match t with
        | SynType.Tuple _ -> true
        | SynType.Paren(innerType = inner)
        | SynType.Array(elementType = inner) -> synTypeHasTuple inner
        | SynType.App(typeName = name; typeArgs = args) -> synTypeHasTuple name || args |> List.exists synTypeHasTuple
        | _ -> false

    let typeHasTuple (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t

            t.IsTupleType
            || t.IsStructTupleType
            || t.GenericArguments
               |> Seq.exists (fun a ->
                   let a = OptionModule.stripAbbreviations a
                   a.IsTupleType || a.IsStructTupleType)
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    // the function head and how many arguments are already applied
    // before the slot: `f a [..]` and `[..] |> f a` both fill position 1
    let rec unwind (fn: SynExpr) (applied: int) =
        match fn with
        | SynExpr.App(isInfix = false; funcExpr = inner) -> unwind inner (applied + 1)
        | SynExpr.Paren(expr = inner)
        | SynExpr.TypeApp(expr = inner) -> unwind inner applied
        | SynExpr.Ident id -> Some(id, applied)
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids, applied)
        | _ -> None

    let parameterExpectsTuple (fn: SynExpr) (tupledIndex: int option) =
        match unwind fn 0 with
        | Some(head, position) ->
            let r = head.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ head.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        let groups = mfv.CurriedParameterGroups

                        if position < groups.Count then
                            let group = groups.[position]

                            match tupledIndex with
                            | Some i when i < group.Count -> typeHasTuple group.[i].Type
                            | Some _ -> false
                            | None -> group.Count = 1 && typeHasTuple group.[0].Type
                        else
                            false
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false
        | None -> false

    let expectsTuples (path: SyntaxNode list) (e: SynExpr) =
        let isE (x: SynExpr) = x.Range = e.Range

        match path with
        // f [ k, v ]  /  f (a, [ k, v ])  /  f ([ k, v ])
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = fn; argExpr = arg)) :: _ when isE arg ->
            parameterExpectsTuple fn None
        | SyntaxNode.SynExpr(SynExpr.Paren(expr = inner)) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; funcExpr = fn)) :: _ when isE inner -> parameterExpectsTuple fn None
        | SyntaxNode.SynExpr(SynExpr.Tuple(exprs = elems)) :: SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; funcExpr = fn)) :: _ -> parameterExpectsTuple fn (elems |> List.tryFindIndex isE)
        // [ k, v ] |> f a
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = IdentName "op_PipeRight"; argExpr = arg)) :: SyntaxNode.SynExpr(SynExpr.App(
            argExpr = fn)) :: _ when isE arg -> parameterExpectsTuple fn None
        // ([ k, v ] : (int * int) list)  /  let xs: (int * int) list = [ k, v ]
        | SyntaxNode.SynExpr(SynExpr.Typed(expr = inner; targetType = ty)) :: _ when isE inner -> synTypeHasTuple ty
        | SyntaxNode.SynBinding(SynBinding(returnInfo = Some(SynBindingReturnInfo(typeName = ty)); expr = body)) :: _ when
            isE body
            ->
            synTypeHasTuple ty
        | _ -> false

    for path, e in index.Exprs do
        match e with
        | SynExpr.ArrayOrListComputed(expr = SynExpr.Tuple(isStruct = false; exprs = elems)) when
            not (inIndexPosition path e)
            && not (expectsTuples path e)
            && elems.Length >= 2
            && elems
               |> List.forall (fun el ->
                   match el with
                   | SynExpr.Const(SynConst.Int32 _, _)
                   | SynExpr.Const(SynConst.Int64 _, _)
                   | SynExpr.Const(SynConst.Double _, _)
                   | SynExpr.Const(SynConst.Single _, _)
                   | SynExpr.Const(SynConst.Decimal _, _) -> true
                   | _ -> false)
            ->
            // the editor's fix: the same elements separated by `;` — the
            // list the author most likely meant
            let original = textOfRange source e.Range

            let opening, closing =
                if original.StartsWith "[|" then
                    "[| ", " |]"
                else
                    "[ ", " ]"

            let separated =
                opening
                + (elems |> List.map (fun el -> textOfRange source el.Range) |> String.concat "; ")
                + closing

            tuples.Add
                { Fix = (e.Range, original, separated)
                  Range = e.Range
                  Elements = elems.Length }
        | _ -> ()

    List.ofSeq conses, List.ofSeq wilds, List.ofSeq tuples
