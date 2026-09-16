/// Four ReSharper-tradition redundancy fixes:
///
/// 1. Attribute suffix (FR0082): `[<SerializableAttribute>]` →
///    `[<Serializable>]` — the compiler resolves the short form.
/// 2. Attribute parens (FR0083): `[<Foo()>]` → `[<Foo>]` — an empty
///    argument list on an attribute says nothing.
/// 3. Redundant backticks (FR0084): ``` ``name`` ``` where `name` is a
///    plain identifier and not a keyword — the quoting does nothing, at
///    this use site independently of any other.
/// 4. Hole-free interpolation (FR0086): `$"just text"` → `"just text"` —
///    without fills the `$` only costs reader attention. Skipped when the
///    text contains braces (they would need unescaping from `{{`/`}}`).
module FSharp.Refactor.RedundantSyntax

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type Kind =
    | AttributeSuffix
    | AttributeParens
    | Backticks
    | HoleFreeInterpolation

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        Kind: Kind
    }

let private plainIdent = Regex(@"^[A-Za-z_][A-Za-z0-9_']*$", RegexOptions.Compiled)

let private keywords =
    Set.ofList FSharp.Compiler.Tokenization.FSharpKeywords.KeywordNames

/// A backtick-quoted ident whose quoting does nothing. An underscore-only
/// name stays quoted: bare `_` is the wildcard, not a binder.
let private redundantBackticks (source: ISourceText) (ident: Ident) =
    plainIdent.IsMatch ident.idText
    && ident.idText.TrimStart '_' <> ""
    && not (keywords.Contains ident.idText)
    && isSingleLine ident.idRange
    && textOfRange source ident.idRange = $"``{ident.idText}``"

/// `check` is the typed tree when the host has one: FR0086 then reads a
/// callee's signature instead of assuming every argument position may
/// expect a FormattableString.
let find (check: FSharpCheckFileResults option) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    // a type declared in this file under the SHORT name would win the
    // attribute lookup after trimming (attribute resolution tries the
    // exact name before appending "Attribute")
    let fileTypeNames =
        index.Decls
        |> Array.collect (fun (_, decl) ->
            match decl with
            | SynModuleDecl.Types(typeDefns = defns) ->
                defns
                |> List.choose (fun (SynTypeDefn(typeInfo = SynComponentInfo(longId = ids))) ->
                    ids |> List.tryLast |> Option.map (fun i -> i.idText))
                |> Array.ofList
            | _ -> [||])
        |> Set.ofArray

    for _, attr in index.Attributes do
        // FR0082: the Attribute suffix
        match attr.TypeName with
        | SynLongIdent(id = ids) when not ids.IsEmpty ->
            let last = List.last ids
            let text = last.idText

            if
                text.EndsWith "Attribute"
                && text.Length > "Attribute".Length
                && not (fileTypeNames.Contains(text.Substring(0, text.Length - "Attribute".Length)))
                && textOfRange source last.idRange = text
            then
                suggestions.Add
                    {
                        Range = last.idRange
                        OriginalText = text
                        ReplacementText = text.Substring(0, text.Length - "Attribute".Length)
                        Kind = Kind.AttributeSuffix
                    }
        | _ -> ()

        // FR0083: the empty argument list
        match attr.ArgExpr with
        | SynExpr.Const(SynConst.Unit, unitRange) when textOfRange source unitRange = "()" ->
            suggestions.Add
                {
                    Range = unitRange
                    OriginalText = "()"
                    ReplacementText = ""
                    Kind = Kind.AttributeParens
                }
        | _ -> ()

    // Is a FormattableString (or IFormattable) EXPECTED here? An interpolated
    // string converts to one when the context asks for it — a type
    // annotation, or a method parameter — and a plain string never does:
    // `let s3: FormattableString = $"""I have no holes"""` lost its `$` and
    // stopped compiling (Fable's StringTests). A method argument is
    // treated as expecting one whenever the callee looks like a method,
    // since only the typed tree could say otherwise and this rule is
    // syntactic.
    let expectsFormattable (path: SyntaxNode list) =
        let namesFormattable (t: SynType) =
            let text = textOfRange source t.Range
            text.Contains "FormattableString" || text.Contains "IFormattable"

        // the callee of the application this argument sits in: `f` in
        // `f a $"..."`, `x.M` in `x.M($"...")`
        let rec calleeIdent (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = f) -> calleeIdent f
            | SynExpr.TypeApp(expr = inner)
            | SynExpr.Paren(expr = inner) -> calleeIdent inner
            | SynExpr.Ident id -> Some id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | _ -> None

        // does the resolved callee take a FormattableString anywhere? With
        // the typed tree the answer is read off its signature — printfn's
        // format parameter is not one, and the `$` goes. Without it, or
        // when the callee does not resolve, ANY application keeps the `$`:
        // Ionide's `Log.setMessageI $"..."` is an F# function whose
        // parameter is a FormattableString, and nothing in its spelling
        // says so (FsAutoComplete's AdaptiveServerState)
        let calleeTakesFormattable (callee: SynExpr) =
            match check, calleeIdent callee with
            | Some(check: FSharpCheckFileResults), Some id ->
                (try
                    let r = id.idRange
                    let lineText = source.GetLineString(r.EndLine - 1)

                    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                    | Some symbolUse ->
                        match symbolUse.Symbol with
                        | :? FSharpMemberOrFunctionOrValue as v ->
                            let signature = v.FullType.Format symbolUse.DisplayContext
                            signature.Contains "FormattableString" || signature.Contains "IFormattable"
                        | _ -> true
                    | None -> true
                 with _ -> // an unreadable callee keeps the `$`; fsharpanalyzer: ignore-line FR0055
                     true)
            | _ -> true

        let rec inArguments (nodes: SyntaxNode list) =
            match nodes with
            | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest
            | SyntaxNode.SynExpr(SynExpr.Tuple _) :: rest -> inArguments rest
            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = callee)) :: _ -> calleeTakesFormattable callee
            // a constructor's overloads are not read here: kept
            | SyntaxNode.SynExpr(SynExpr.New _) :: _ -> true
            | _ -> false

        inArguments path
        || path
           |> List.exists (fun node ->
               match node with
               | SyntaxNode.SynExpr(SynExpr.Typed(targetType = t)) -> namesFormattable t
               | SyntaxNode.SynBinding(SynBinding(returnInfo = Some(SynBindingReturnInfo(typeName = t)))) ->
                   namesFormattable t
               | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.Typed(targetType = t))) -> namesFormattable t
               | _ -> false)

    // FR0084: redundant backticks at use sites and binder sites — each
    // strip is independently valid, backticks are optional quoting
    for path, e in index.Exprs do
        match e with
        | SynExpr.Ident ident when redundantBackticks source ident ->
            suggestions.Add
                {
                    Range = ident.idRange
                    OriginalText = textOfRange source ident.idRange
                    ReplacementText = ident.idText
                    Kind = Kind.Backticks
                }
        | SynExpr.InterpolatedString(contents = parts) when
            parts
            |> List.forall (fun p ->
                match p with
                | SynInterpolatedStringPart.String _ -> true
                | SynInterpolatedStringPart.FillExpr _ -> false)
            ->
            // FR0086: no holes — drop the `$` unless braces would need
            // unescaping, or a `%%` its un-doubling ('%' escapes in
            // interpolated strings but not in plain ones)
            let text = textOfRange source e.Range

            if
                not (text.Contains '{' || text.Contains '}' || text.Contains '%')
                && text.Contains '$'
                && not (expectsFormattable path)
            then
                // every `$` of the opener goes: a `$$"""…"""` (F# 8) with
                // no hole is as plain a string as a `$"…"` with none
                let first = text.IndexOf '$'
                let mutable last = first

                while last + 1 < text.Length && text.[last + 1] = '$' do
                    last <- last + 1

                suggestions.Add
                    {
                        Range = e.Range
                        OriginalText = text
                        ReplacementText = text.Remove(first, last - first + 1)
                        Kind = Kind.HoleFreeInterpolation
                    }
        | _ -> ()

    for _, p in index.Pats do
        match p with
        | SynPat.Named(ident = SynIdent(ident = ident)) when redundantBackticks source ident ->
            suggestions.Add
                {
                    Range = ident.idRange
                    OriginalText = textOfRange source ident.idRange
                    ReplacementText = ident.idText
                    Kind = Kind.Backticks
                }
        | _ -> ()

    List.ofSeq suggestions
