/// Refactoring: the Python `range(len(xs))` loop, in F# clothing.
///
///     for i in 0 .. xs.Length - 1 do        for item in xs do
///         process xs.[i]              →         process item
///
/// The index buys nothing when its every use is `xs.[i]`: iterating
/// directly reads better, drops the per-access bounds arithmetic — and on
/// an F# LIST it turns an accidental O(n²) (each `.[i]` walks i cons
/// cells) into the O(n) the author meant. This is the highest-frequency
/// first-draft shape LLMs produce when porting Python.
///
/// Safety rules (all syntactic):
///   - the bound is literally `0 .. <xs>.Length - 1` (or an
///     `Array/List/Seq.length <xs> - 1` spelling), and <xs> is the SAME
///     path the body indexes
///   - every use of the index variable in the body is exactly `<xs>.[i]`
///     or `<xs>[i]` — an index used as a value wants iteri, which changes
///     shape enough to be the author's call
///   - nothing in the body writes an element (`<xs>.[i] <- ...` needs the
///     index), assigns the collection or the index, or rebinds either name
module FSharp.Refactor.IndexedLoop

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole `for` loop, for the message anchor.
        Range: range
        /// The collection's source text, for the message.
        CollectionText: string
        /// Header + one edit per indexed use.
        Edits: (range * string * string) list
    }

/// A name or dotted path, as (root ident, joined text).
[<return: Struct>]
let private (|Path|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome(id, id.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.head ids, identText ids)
    | _ -> ValueNone

/// `<xs>.Length` or `Array/List/Seq.length <xs>` — the collection's text.
[<return: Struct>]
let private (|LengthOfColl|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 && (List.last ids).idText = "Length" ->
        ValueSome(identText (ids |> List.take (ids.Length - 1)))
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
        argExpr = Path(_, collText)) when
        (m.idText = "Array" || m.idText = "List" || m.idText = "Seq")
        && f.idText = "length"
        ->
        ValueSome collText
    | _ -> ValueNone

/// `<len> - 1` — the collection whose length is being decremented.
[<return: Struct>]
let private (|LengthMinusOne|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SingleIdent minus; argExpr = LengthOfColl collText)
        argExpr = SynExpr.Const(SynConst.Int32 1, _)) when minus.idText = "op_Subtraction" -> ValueSome collText
    | _ -> ValueNone

/// `0 .. <xs>.Length - 1` — the collection's text. A for-loop's range
/// parses as SynExpr.IndexRange; the operator application covers other
/// spellings.
[<return: Struct>]
let private (|ZeroToLengthMinusOne|_|) (e: SynExpr) =
    match e with
    | SynExpr.IndexRange(expr1 = Some(SynExpr.Const(SynConst.Int32 0, _)); expr2 = Some(LengthMinusOne collText)) ->
        ValueSome collText
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SingleIdent range; argExpr = SynExpr.Const(SynConst.Int32 0, _))
        argExpr = LengthMinusOne collText) when range.idText = "op_Range" -> ValueSome collText
    | _ -> ValueNone

/// Find index-based loops whose index only ever indexes the bound
/// collection.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    for path, expr in index.Exprs do
        match expr with
        | SynExpr.ForEach(
            pat = SynPat.Named(ident = SynIdent(ident = i))
            enumExpr = ZeroToLengthMinusOne collText & enumExpr
            bodyExpr = body) when not (spansDirective source expr.Range) ->
            let collRoot = collText.Split('.').[0]

            let inBody (r: range) = Range.rangeContainsRange body.Range r

            let sameColl (e: SynExpr) =
                match e with
                | Path(_, text) -> text = collText
                | _ -> false

            let isIndexIdent (e: SynExpr) =
                match stripParens e with
                | SynExpr.Ident id -> id.idText = i.idText
                | _ -> false

            // every `<xs>.[i]` / `<xs>[i]` in the body: its whole range and
            // the range of the index ident inside it
            let indexedUses =
                index.Exprs
                |> Array.choose (fun (_, e) ->
                    match e with
                    | SynExpr.DotIndexedGet(objectExpr = o; indexArgs = idx) when
                        inBody e.Range && sameColl o && isIndexIdent idx
                        ->
                        Some(e.Range, (stripParens idx).Range)
                    | SynExpr.App(
                        flag = ExprAtomicFlag.Atomic; funcExpr = o; argExpr = SynExpr.ArrayOrListComputed(expr = idx)) when
                        inBody e.Range && sameColl o && isIndexIdent idx
                        ->
                        Some(e.Range, (stripParens idx).Range)
                    | _ -> None)

            let indexIdentRanges = indexedUses |> Array.map snd

            // every mention of the index variable in the body
            let indexMentions =
                index.Exprs
                |> Array.choose (fun (_, e) ->
                    match e with
                    | SynExpr.Ident id when id.idText = i.idText && inBody id.idRange -> Some id.idRange
                    | _ -> None)

            let onlyIndexes =
                indexMentions.Length > 0
                && indexMentions
                   |> Array.forall (fun m -> indexIdentRanges |> Array.exists (fun r -> Range.equals r m))

            // nothing may write an element or assign the collection or the
            // index inside the body
            let mutates =
                index.Exprs
                |> Array.exists (fun (_, e) ->
                    inBody e.Range
                    && (match e with
                        | SynExpr.DotIndexedSet(objectExpr = o) -> sameColl o
                        // the F#6 spelling of the same element write
                        | SynExpr.Set(targetExpr = t) ->
                            (match stripParens t with
                             | SynExpr.App(
                                 flag = ExprAtomicFlag.Atomic; funcExpr = o; argExpr = SynExpr.ArrayOrListComputed _) ->
                                 sameColl o
                             | _ -> false)
                        | SynExpr.LongIdentSet(SynLongIdent(id = first :: _), _, _) ->
                            first.idText = collRoot || first.idText = i.idText
                        | _ -> false))

            // ...and nothing may REBIND either name: a nested `for i in`,
            // a lambda, a let, or a match pattern shadowing `i` makes the
            // inner `xs.[i]` a different index — rewriting it to the outer
            // element would silently change behavior. Every binder goes
            // through a Named pattern, so one scan covers all of them.
            let rebinds =
                index.Pats
                |> Array.exists (fun (_, p) ->
                    Range.rangeContainsRange body.Range p.Range
                    && (match p with
                        | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = i.idText || id.idText = collRoot
                        | _ -> false))

            // ...nor may the body take the ADDRESS of the element: `let
            // sprite = &sprites[index]` wants an inref into the array, and a
            // `for sprite in sprites` element is a copy, so every
            // `&sprite.Field` after it reads "ByRefKinds.InOut does not match
            // ByRefKinds.In" (Nu's Renderer2d)
            let addressTaken =
                index.Exprs
                |> Array.exists (fun (_, e) ->
                    match e with
                    | SynExpr.AddressOf(expr = inner) ->
                        inBody e.Range
                        && indexedUses
                           |> Array.exists (fun (useRange, _) -> Range.equals useRange (stripParens inner).Range)
                    | _ -> false)

            let disqualified = mutates || rebinds || addressTaken

            if onlyIndexes && not disqualified then
                let loopText = textOfRange source expr.Range

                // the element is `item`, or `item2`, `item3`... when a name
                // is already taken: mentioned inside the loop, or bound by
                // anything on the path to it — a parameter, an outer loop,
                // a let, a lambda, a match arm. Mibo's Spatial2DTests had
                // `for x in 0 .. 4 do` around the loop, and the `x` chosen
                // then shadowed it.
                let enclosingNames =
                    path
                    |> List.collect (fun node ->
                        match node with
                        | SyntaxNode.SynBinding(SynBinding(headPat = p)) -> patNames p
                        | SyntaxNode.SynMatchClause(SynMatchClause(pat = p)) -> patNames p
                        | SyntaxNode.SynExpr e ->
                            match e with
                            | LetOrUseE lou ->
                                lou.Bindings |> List.collect (fun (SynBinding(headPat = p)) -> patNames p)
                            | SynExpr.ForEach(pat = p) -> patNames p
                            | SynExpr.For(ident = id) -> [ id.idText ]
                            | SynExpr.Lambda(parsedData = Some(pats, _)) -> pats |> List.collect patNames
                            | _ -> []
                        | _ -> [])
                    |> Set.ofList

                let taken (name: string) =
                    enclosingNames.Contains name || Regex.IsMatch(loopText, identifierPattern name)

                let element =
                    Seq.append (Seq.singleton "item") (Seq.initInfinite (fun n -> $"item{n + 2}"))
                    |> Seq.find (fun name -> not (taken name))

                let headerRange =
                    Range.mkRange expr.Range.FileName expr.Range.Start enumExpr.Range.End

                let headerEdit =
                    headerRange, textOfRange source headerRange, $"for {element} in {collText}"

                let useEdits =
                    indexedUses
                    |> Array.map (fun (useRange, _) -> useRange, textOfRange source useRange, element)
                    |> Array.toList

                suggestions.Add
                    { Range = expr.Range
                      CollectionText = collText
                      Edits = headerEdit :: useEdits }
        | _ -> ()

    List.ofSeq suggestions
