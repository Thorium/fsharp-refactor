/// Refactoring: drop a redundant `.ToString()` inside an interpolated string.
///
///     $"{x.ToString()} items"   →   $"{x} items"
///
/// String interpolation formats the value the same way, so the call only
/// adds noise (and boxes early). Calls with arguments — `x.ToString("d")` —
/// carry format/culture information and are never touched.
///
/// Guards: the fill has no typed hole before it (`%s{...}` pins a string)
/// and no .NET format after it (`{x.ToString():N2}` formats a string,
/// which ignores `N2`; `{x:N2}` would apply it); and the interpolated
/// string is proven a STRING by the typed tree. Typed as a
/// FormattableString (`FormattableString.Invariant $"..."`, an annotation,
/// a parameter) the hole's argument is the value itself: `Invariant`
/// formats `{x}` with the invariant culture where `x.ToString()` used the
/// current one, and a consumer reading the arguments (a SQL parameter)
/// sees another type. Proof: every enclosing call up to the owning binding
/// resolves to a callee whose signature names no FormattableString or
/// IFormattable, no annotation on the way names one, the binding's own
/// type names neither, and nothing between is a construct whose expected
/// type is not read here (a record field, a constructor, an object
/// expression, a property set). Anything unproven stands down.
module FSharp.Refactor.InterpToString

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole fill expression `x.ToString()`.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// `<receiver>.ToString()` — returns the receiver's text, or None for any
/// other shape (including ToString with arguments).
let private toStringReceiver (source: ISourceText) (e: SynExpr) : string option =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
        match funcExpr with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
            ids.Length >= 2 && (List.last ids).idText = "ToString"
            ->
            let front = ids.[.. ids.Length - 2]

            let receiverRange =
                Range.mkRange e.Range.FileName (List.head front).idRange.Start (List.last front).idRange.End

            Some(textOfRange source receiverRange)
        | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ name ])) when name.idText = "ToString" ->
            Some(textOfRange source receiver.Range)
        | _ -> None
    | _ -> None

let private namesFormattable (text: string) =
    text.Contains "FormattableString" || text.Contains "IFormattable"

/// Is the interpolated string at the head of `path` provably typed
/// `string`? See the module comment for the walk.
let private provenString (check: FSharpCheckFileResults) (source: ISourceText) (path: SyntaxNode list) =
    let symbolAt (id: Ident) =
        try
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
        with _ -> // an unreadable symbol proves nothing; fsharpanalyzer: ignore-line FR0055
            None

    // the resolved symbol's type names no FormattableString; unresolved,
    // or not a value, proves nothing
    let typedPlainly (id: Ident) =
        match symbolAt id with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                (try
                    not (namesFormattable (v.FullType.Format symbolUse.DisplayContext))
                 with _ -> // fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false
        | None -> false

    let rec calleeIdent (e: SynExpr) =
        match e with
        | SynExpr.App(funcExpr = f) -> calleeIdent f
        | SynExpr.TypeApp(expr = inner)
        | SynExpr.Paren(expr = inner) -> calleeIdent inner
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    let annotationPlain (t: SynType) =
        not (namesFormattable (textOfRange source t.Range))

    let rec walk (nodes: SyntaxNode list) =
        match nodes with
        // the top of a module: no expected type reaches here
        | []
        | SyntaxNode.SynModule _ :: _ -> true
        | SyntaxNode.SynBinding(SynBinding(headPat = headPat; returnInfo = returnInfo)) :: _ ->
            let returnPlain =
                match returnInfo with
                | Some(SynBindingReturnInfo(typeName = t)) -> annotationPlain t
                | None -> true

            let rec headIdent (p: SynPat) =
                match p with
                | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
                | SynPat.Typed(pat = inner; targetType = t) when annotationPlain t -> headIdent inner
                | SynPat.Paren(inner, _) -> headIdent inner
                | _ -> None

            returnPlain
            && (match headIdent headPat with
                | Some id -> typedPlainly id
                | None -> false)
        | SyntaxNode.SynExpr e :: rest ->
            match e with
            | SynExpr.App(funcExpr = callee) ->
                (match calleeIdent callee with
                 | Some id -> typedPlainly id
                 | None -> false)
                && walk rest
            | SynExpr.Typed(targetType = t) -> annotationPlain t && walk rest
            | SynExpr.Paren _
            | SynExpr.Tuple _
            | SynExpr.IfThenElse _
            | SynExpr.Match _
            | SynExpr.MatchBang _
            | SynExpr.Sequential _
            | SynExpr.LetOrUse _
            | SynExpr.TryWith _
            | SynExpr.TryFinally _
            | SynExpr.Lambda _
            | SynExpr.MatchLambda _
            | SynExpr.ArrayOrList _
            | SynExpr.ArrayOrListComputed _
            | SynExpr.ComputationExpr _
            | SynExpr.YieldOrReturn _
            | SynExpr.YieldOrReturnFrom _
            | SynExpr.Do _
            | SynExpr.Lazy _ -> walk rest
            | _ -> false
        | SyntaxNode.SynMatchClause _ :: rest -> walk rest
        | _ -> false

    walk path

/// Find `.ToString()` calls used as interpolation fills. Fills under a
/// typed hole (`%s{x.ToString()}`) are left alone: the specifier pins the
/// fill's type, so dropping the conversion would not typecheck. Without
/// the typed tree nothing proves the string's type, and nothing is found.
let find (check: FSharpCheckFileResults option) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr, check with
                | SynExpr.InterpolatedString(contents = parts), Some check ->
                    // only consulted when a candidate fill is found
                    let isString = lazy (provenString check source path)
                    let mutable precededBySpecifier = false

                    for part in parts do
                        match part with
                        | SynInterpolatedStringPart.String(value = lead) ->
                            precededBySpecifier <- endsWithFormatSpecifier lead
                        | SynInterpolatedStringPart.FillExpr(fillExpr = fill; qualifiers = format) ->
                            if not precededBySpecifier && format.IsNone && isSingleLine fill.Range then
                                match toStringReceiver source fill with
                                | Some receiverText when isString.Value ->
                                    suggestions.Add
                                        {
                                            Range = fill.Range
                                            OriginalText = textOfRange source fill.Range
                                            ReplacementText = receiverText
                                        }
                                | _ -> ()

                            precededBySpecifier <- false
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
