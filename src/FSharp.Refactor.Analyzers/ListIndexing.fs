/// Diagnostic (performance): positional indexing into an F# LIST inside a
/// loop.
///
///     let names : string list = ...
///     for i in 0 .. count - 1 do
///         printfn "%s" names.[i]      // each access walks i cons cells
///
/// `xs.[i]` looks like an array access and is O(i) on a list — in a loop
/// that is the quietest quadratic in F#, and the shape LLMs produce
/// constantly because `[ ]` literals make lists which they then index like
/// Python lists. Advice only: the right repair is iterating directly (the
/// canonical `for i in 0 .. xs.Length - 1` shape gets an automatic fix
/// from FR0101), or converting once with List.toArray when random access
/// is really needed.
///
/// Typed rule: the receiver must resolve to FSharpList — arrays,
/// ResizeArray and dictionaries share the same syntax and are fine. The
/// `List.item`/`List.nth` spellings pin the type by module name. Constant
/// indexes are skipped (`xs.[0]` is a deliberate head access), and so is a
/// receiver bound inside the loop — by a let, a lambda parameter or a
/// match arm's pattern (a fresh short list per iteration is a different
/// story).
///
/// `xs.Length` / `List.length xs` on a list is the same walk — O(n) per
/// call, with nothing to show for it — so a loop-invariant list's length
/// read inside a loop body gets the same note (`while i < xs.Length`,
/// Mibo's `count / (points.Length - 1)` per segment). A loop HEADER
/// (`for i in 0 .. xs.Length - 1`) evaluates once and is fine.
module FSharp.Refactor.ListIndexing

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type AccessKind =
    /// `xs.[i]`, `xs[i]`, `List.item i xs`.
    | Index
    /// `xs.Length`, `List.length xs`.
    | Length

type Suggestion =
    {
        Range: range
        /// The indexed list's source text, for the message.
        CollectionText: string
        Kind: AccessKind
    }

/// Is the expression evaluated once, in a loop's header — a `for` bound
/// or a `for ... in` source — rather than per iteration in its body? A
/// `while` condition IS per iteration and does not count as a header.
let private inLoopHeader (path: SyntaxNode list) (r: range) =
    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.For(identBody = start; toBody = finish)) ->
            Range.rangeContainsRange start.Range r
            || Range.rangeContainsRange finish.Range r
        | SyntaxNode.SynExpr(SynExpr.ForEach(enumExpr = source)) -> Range.rangeContainsRange source.Range r
        | _ -> false)

[<return: Struct>]
let private (|Path|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome(id, id, id.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.head ids, List.last ids, identText ids)
    | _ -> ValueNone

let private isConstIndex (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const _ -> true
    | _ -> false

/// The walk a small bound keeps constant: `xs[i % 13]` (Kasino's rank
/// table) never walks past the modulus, and a loop `for i in 0 .. 3` over
/// the index never walks past its literal end. A bounded walk is a
/// constant cost, not the quadratic the rule hunts.
[<Literal>]
let private smallBound = 64

let private isSmallInt (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const(SynConst.Int32 n, _) -> n <= smallBound
    | _ -> false

let private boundedIndex (path: SyntaxNode list) (idx: SynExpr) =
    match stripParens idx with
    | SynExpr.App(
        funcExpr = SynExpr.App(
            isInfix = true; funcExpr = (SynExpr.Ident op | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ]))))
        argExpr = modulus) when op.idText = "op_Modulus" -> isSmallInt modulus
    | SynExpr.Ident i ->
        path
        |> List.exists (fun node ->
            match node with
            | SyntaxNode.SynExpr(SynExpr.For(ident = v; toBody = upper)) -> v.idText = i.idText && isSmallInt upper
            | SyntaxNode.SynExpr(SynExpr.ForEach(
                pat = SynPat.Named(ident = SynIdent(ident = v)); enumExpr = SynExpr.IndexRange(expr2 = Some upper))) ->
                v.idText = i.idText && isSmallInt upper
            | _ -> false)
    | _ -> false

/// Find list indexing inside loops. Requires typed check results for the
/// receiver's type.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let resolvesToList (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            let rec stripInstance (t: FSharpType) =
                if t.IsAbbreviation then
                    stripInstance t.AbbreviatedType
                else
                    t

            let isListType (t: FSharpType) =
                try
                    let t = stripInstance t

                    t.HasTypeDefinition
                    && t.TypeDefinition.TryFullName = Some "Microsoft.FSharp.Collections.FSharpList`1"
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    false

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value ->
                    isListType (
                        try
                            value.ReturnParameter.Type
                        with _ ->
                            value.FullType
                    )
                | :? FSharpField as field -> isListType field.FieldType
                | _ -> false
            | None -> false

        [ for path, expr in index.Exprs do
              let candidate =
                  match expr with
                  // xs.[i] and the F#6 xs[i]
                  | SynExpr.DotIndexedGet(objectExpr = Path(root, last, text); indexArgs = idx) when
                      not (isConstIndex idx)
                      ->
                      Some(root, last, text, true, Some idx)
                  | SynExpr.App(
                      flag = ExprAtomicFlag.Atomic
                      funcExpr = Path(root, last, text)
                      argExpr = SynExpr.ArrayOrListComputed(expr = idx)) when not (isConstIndex idx) ->
                      Some(root, last, text, true, Some idx)
                  // List.item i xs / xs |> List.item i (nth likewise) —
                  // the module name pins the type, no resolution needed
                  | SynExpr.App(
                      funcExpr = SynExpr.App(
                          funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = idx)
                      argExpr = Path(root, last, text)) when
                      m.idText = "List"
                      && (f.idText = "item" || f.idText = "nth")
                      && not (isConstIndex idx)
                      ->
                      Some(root, last, text, false, Some idx)
                  | PipeApp(Path(root, last, text),
                            SynExpr.App(
                                funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = idx)) when
                      m.idText = "List"
                      && (f.idText = "item" || f.idText = "nth")
                      && not (isConstIndex idx)
                      ->
                      Some(root, last, text, false, Some idx)
                  // xs.Length — the receiver is the path minus its last
                  // segment; List.length xs / xs |> List.length
                  | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                      ids.Length >= 2 && (List.last ids).idText = "Length"
                      ->
                      let receiver = ids |> List.take (ids.Length - 1)
                      Some(List.head receiver, List.last receiver, identText receiver, true, None)
                  | SynExpr.App(
                      funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                      argExpr = Path(root, last, text)) when m.idText = "List" && f.idText = "length" ->
                      Some(root, last, text, false, None)
                  | PipeApp(Path(root, last, text), SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))) when
                      m.idText = "List" && f.idText = "length"
                      ->
                      Some(root, last, text, false, None)
                  | _ -> None

              match candidate with
              | Some(root, last, text, needsTypeProof, idx) ->
                  match LoopPerf.loopBinders path with
                  | ValueSome binders when
                      not (binders.Contains root.idText)
                      && not (inLoopHeader path expr.Range)
                      && not (idx |> Option.exists (boundedIndex path))
                      && (not needsTypeProof || resolvesToList last)
                      ->
                      { Range = expr.Range
                        CollectionText = text
                        Kind =
                          match idx with
                          | Some _ -> AccessKind.Index
                          | None -> AccessKind.Length }
                  | _ -> ()
              | None -> () ]
