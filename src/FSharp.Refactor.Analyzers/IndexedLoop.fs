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
/// Safety rules:
///   - the bound is literally `0 .. <xs>.Length - 1` (or an
///     `Array/List/Seq.length <xs> - 1` spelling), and <xs> is the SAME
///     path the body indexes
///   - <xs> is proven (typed) an array, an F# list, a string, a
///     ResizeArray or an IList<'T> — a type enumerated in index order. A
///     `.Length` and an indexer alone do not make `for item in xs` compile
///     (StringBuilder has no enumerator)
///   - the body touches <xs> only through `<xs>.[i]`: the bound was read
///     once where an enumerator checks every step, so an `xs.Add` in the
///     body turns into "Collection was modified", and a call handed `xs`
///     may do the same
///   - every use of the index variable in the body is exactly `<xs>.[i]`
///     or `<xs>[i]` — an index used as a value wants iteri, which changes
///     shape enough to be the author's call
///   - nothing in the body writes an element (`<xs>.[i] <- ...` needs the
///     index), assigns the collection or the index, or rebinds either name
///
/// When the body opens with `let name = xs.[i]` and that is the index's
/// only use, the loop variable is `name` and the alias line goes.
module FSharp.Refactor.IndexedLoop

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
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

/// Which sources `for item in xs` may replace the indexed loop over.
[<RequireQualifiedAccess>]
type SourceGate =
    /// Any enumerable: on .NET a string enumerates its characters.
    | Any
    /// A Fable project: a STRING source stays indexed, since Fable's Rust
    /// target has no string enumerator (SQLProvider.Fable's Query.fs said
    /// so in a comment and the rule rewrote the loop anyway). The typed
    /// tree tells a string from a collection; without one every source
    /// may be a string and the rule stands down.
    | NoStrings of FSharpCheckFileResults option

/// A name or dotted path, as (root ident, joined text, last ident).
[<return: Struct>]
let private (|Path|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome(id, id.idText, id)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.head ids, identText ids, List.last ids)
    | _ -> ValueNone

/// `<xs>.Length` or `Array/List/Seq.length <xs>` — the collection's text
/// and the identifier that names it (its last, for the typed tree).
[<return: Struct>]
let private (|LengthOfColl|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 && (List.last ids).idText = "Length" ->
        let coll = ids |> List.take (ids.Length - 1)
        ValueSome(identText coll, List.last coll)
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
        argExpr = Path(_, collText, collIdent)) when
        (m.idText = "Array" || m.idText = "List" || m.idText = "Seq")
        && f.idText = "length"
        ->
        ValueSome(collText, collIdent)
    | _ -> ValueNone

/// `<len> - 1` — the collection whose length is being decremented.
[<return: Struct>]
let private (|LengthMinusOne|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SingleIdent minus; argExpr = LengthOfColl coll)
        argExpr = SynExpr.Const(SynConst.Int32 1, _)) when minus.idText = "op_Subtraction" -> ValueSome coll
    | _ -> ValueNone

/// `0 .. <xs>.Length - 1` — the collection's text. A for-loop's range
/// parses as SynExpr.IndexRange; the operator application covers other
/// spellings.
[<return: Struct>]
let private (|ZeroToLengthMinusOne|_|) (e: SynExpr) =
    match e with
    | SynExpr.IndexRange(expr1 = Some(SynExpr.Const(SynConst.Int32 0, _)); expr2 = Some(LengthMinusOne coll)) ->
        ValueSome coll
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SingleIdent range; argExpr = SynExpr.Const(SynConst.Int32 0, _))
        argExpr = LengthMinusOne coll) when range.idText = "op_Range" -> ValueSome coll
    | _ -> ValueNone

/// May the collection this identifier names be a string? Proven not when
/// the typed tree resolves it to a value, property or field whose type is
/// anything but System.String; unresolved, it may.
let private mayBeString (check: FSharpCheckFileResults) (source: ISourceText) (collIdent: Ident) =
    let isString (t: FSharpType) =
        let t = OptionModule.stripAbbreviations t
        t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.String"

    match OptionModule.symbolOfIdent check source collIdent with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            isString (resultTypeOf value)
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             true)
    | Some(:? FSharpField as field) ->
        (try
            isString field.FieldType
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             true)
    | _ -> true

/// Does the collection this identifier names enumerate, in index order?
/// Proven for an array, an F# list, a string, a ResizeArray and an
/// IList<'T>; a type with `.Length` and an indexer but no enumerator
/// (StringBuilder) or one of its own enumeration order answers no, as
/// does a name FCS cannot type.
let private enumeratesInIndexOrder (check: FSharpCheckFileResults) (source: ISourceText) (collIdent: Ident) =
    let inOrder (t: FSharpType) =
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.IsArrayType
            || (match t.TypeDefinition.TryFullName with
                | Some("System.String" | "Microsoft.FSharp.Collections.FSharpList`1" | "System.Collections.Generic.List`1" | "System.Collections.Generic.IList`1") ->
                    true
                | _ -> false))

    match OptionModule.symbolOfIdent check source collIdent with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            inOrder (resultTypeOf value)
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | Some(:? FSharpField as field) ->
        (try
            inOrder field.FieldType
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// Find index-based loops whose index only ever indexes the bound
/// collection, over the sources the gate admits — and, given check
/// results, only over a source proven to enumerate in index order.
let private findIn
    (parseTree: ParsedInput)
    (source: ISourceText)
    (gate: SourceGate)
    (check: FSharpCheckFileResults option)
    : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let admitted (collIdent: Ident) =
        (match gate with
         | SourceGate.Any -> true
         | SourceGate.NoStrings(Some check) -> not (mayBeString check source collIdent)
         | SourceGate.NoStrings None -> false)
        && (match check with
            | Some check -> enumeratesInIndexOrder check source collIdent
            | None -> true)

    let suggestions: Suggestion list =
        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.ForEach(
                    pat = SynPat.Named(ident = SynIdent(ident = i))
                    enumExpr = ZeroToLengthMinusOne(collText, collIdent) & enumExpr
                    bodyExpr = body) when not (spansDirective source expr.Range) && admitted collIdent ->
                    let collRoot = collText.Split('.').[0]

                    let inBody (r: range) = Range.rangeContainsRange body.Range r

                    let sameColl (e: SynExpr) =
                        match e with
                        | Path(_, text, _) -> text = collText
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
                                flag = ExprAtomicFlag.Atomic
                                funcExpr = o
                                argExpr = SynExpr.ArrayOrListComputed(expr = idx)) when
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
                                         flag = ExprAtomicFlag.Atomic
                                         funcExpr = o
                                         argExpr = SynExpr.ArrayOrListComputed _) -> sameColl o
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
                                | SynPat.Named(ident = SynIdent(ident = id)) ->
                                    id.idText = i.idText || id.idText = collRoot
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
                                   |> Array.exists (fun (useRange, _) ->
                                       Range.equals useRange (stripParens inner).Range)
                            | _ -> false)

                    // ...nor may the body touch the collection other than
                    // through `xs.[i]`: the bound was read ONCE, where an
                    // enumerator checks every step — `xs.Add` inside a `for
                    // item in xs` throws "Collection was modified", and a
                    // call handing `xs` on may do the same
                    let collSegments = collText.Split('.').Length

                    let touchesCollection =
                        index.Exprs
                        |> Array.exists (fun (_, e) ->
                            inBody e.Range
                            && not (indexedUses |> Array.exists (fun (u, _) -> Range.rangeContainsRange u e.Range))
                            && (match e with
                                | SynExpr.Ident id -> id.idText = collText
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                    ids.Length >= collSegments && identText (List.take collSegments ids) = collText
                                | _ -> false))

                    let disqualified = mutates || rebinds || addressTaken || touchesCollection

                    if onlyIndexes && not disqualified then
                        let loopText = textOfRange source expr.Range

                        // names bound by anything on the path to the loop — a
                        // parameter, an outer loop, a let, a lambda, a match arm.
                        // Mibo's Spatial2DTests had `for x in 0 .. 4 do` around the
                        // loop, and the `x` chosen then shadowed it.
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

                        // `let mChar = path.[i]` as the body's first statement and
                        // the index's ONLY use is the element already named: the
                        // loop variable takes that name and the alias line goes
                        // (Giraffe's FormatExpressions kept `for item in path do
                        // let mChar = item`). The binder must be a plain name — no
                        // type, no mutable, no attribute — that nothing around the
                        // loop already binds, and the rest of the body must start
                        // on its own line at the let's column with only whitespace
                        // in between, so dropping the let's span leaves the body in
                        // place.
                        let alias =
                            match body with
                            | LetOrUseE lou when not ((lou.IsUse || lou.IsBang) || lou.IsRecursive) ->
                                match lou.Bindings, indexedUses with
                                | [ SynBinding(
                                        attributes = []
                                        isMutable = false
                                        headPat = SynPat.Named(ident = SynIdent(ident = name); isThisVal = false)
                                        returnInfo = None
                                        expr = rhs) ],
                                  [| useRange, _ |] when
                                    indexMentions.Length = 1
                                    && Range.equals useRange (stripParens rhs).Range
                                    && name.idText <> i.idText
                                    && name.idText <> collRoot
                                    && not (enclosingNames.Contains name.idText)
                                    && lou.Body.Range.StartLine > rhs.Range.EndLine
                                    && lou.Body.Range.StartColumn = lou.Range.StartColumn
                                    && System.String.IsNullOrWhiteSpace(
                                        textOfRange
                                            source
                                            (Range.mkRange lou.Range.FileName rhs.Range.End lou.Body.Range.Start)
                                    )
                                    ->
                                    Some(
                                        name.idText,
                                        Range.mkRange lou.Range.FileName lou.Range.Start lou.Body.Range.Start
                                    )
                                | _ -> None
                            | _ -> None

                        let headerRange =
                            Range.mkRange expr.Range.FileName expr.Range.Start enumExpr.Range.End

                        let headerEdit element =
                            headerRange, textOfRange source headerRange, $"for {element} in {collText}"

                        match alias with
                        | Some(element, aliasRange) ->
                            {
                                Range = expr.Range
                                CollectionText = collText
                                Edits = [ headerEdit element; aliasRange, textOfRange source aliasRange, "" ]
                            }
                        | None ->
                            // the element is `item`, or `item2`, `item3`... when a
                            // name is already taken: mentioned inside the loop, or
                            // bound by anything on the path to it
                            let taken (name: string) =
                                enclosingNames.Contains name || Regex.IsMatch(loopText, identifierPattern name)

                            let element =
                                Seq.append (Seq.singleton "item") (Seq.initInfinite (fun n -> $"item{n + 2}"))
                                |> Seq.find (taken >> not)

                            let useEdits =
                                indexedUses
                                |> Array.map (fun (useRange, _) -> useRange, textOfRange source useRange, element)
                                |> Array.toList

                            {
                                Range = expr.Range
                                CollectionText = collText
                                Edits = headerEdit element :: useEdits
                            }
                | _ -> ()
        ]

    suggestions

/// Find index-based loops whose index only ever indexes the bound
/// collection, over the sources the gate admits. Parse-only: the source's
/// type is not proven; the analyzers run findChecked.
let findWith (parseTree: ParsedInput) (source: ISourceText) (gate: SourceGate) : Suggestion list =
    findIn parseTree source gate None

/// findWith over a source proven (typed) to enumerate in index order —
/// what the analyzers run, CLI and editor alike.
let findChecked
    (parseTree: ParsedInput)
    (source: ISourceText)
    (gate: SourceGate)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    findIn parseTree source gate (Some check)

/// Find index-based loops whose index only ever indexes the bound
/// collection, over any source (.NET).
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    findWith parseTree source SourceGate.Any
