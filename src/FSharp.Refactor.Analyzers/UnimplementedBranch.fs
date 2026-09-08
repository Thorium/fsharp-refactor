/// Refactoring (correctness): a match branch that says it is unfinished and
/// then returns a plausible value.
///
///     match method with
///     | Gauss cf  -> solveGauss cf
///     | Seidel cf -> solveSeidel cf
///     | Jordan ->
///         // Not supported yet
///         None
///
/// The `None` is indistinguishable from a legitimate "no result", so every
/// caller takes the not-found branch and the gap surfaces somewhere else
/// entirely, as bad data rather than as a missing feature. `raise
/// (NotImplementedException())` says the one true thing at the one place that
/// knows it. FR0077 already writes exactly that when it stubs out missing
/// interface members; this finds the ones written by hand.
///
/// What makes the signal reliable is WHERE the comment sits. Between the
/// arrow and the value it describes that branch and nothing else, so the
/// everyday
///
///     // TODO: cache this
///     let lookup k = map.TryFind k
///
/// never matches: its comment is nowhere near a branch body. And the shape
/// alone is not enough either, because this is correct, idiomatic code:
///
///     | Unknown -> None       // genuinely has no area
///
/// So every placeholder needs the comment to accuse it — `null` and
/// `Unchecked.defaultof<_>` included. They looked like values nobody
/// produces on purpose, until the corpus produced them on purpose:
/// `| [] -> Unchecked.defaultof<'T>` is the entire contract of a
/// SingleOrDefault, and `| null -> null` passes a sentinel through.
///
/// The fix is safe to apply here in a way it would not be for a whole
/// function body: the sibling branches already fix the type, so substituting
/// `raise` (which returns `'a`) disturbs no inference.
module FSharp.Refactor.UnimplementedBranch

open System
open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the placeholder value, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// Phrases that say the branch is unfinished rather than merely noteworthy.
/// "TODO" and "FIXME" alone are absent on purpose: they mark future work of
/// every kind, most of it nothing to do with the value below them.
let private stubPhrases =
    [ "not implemented"
      "not yet implemented"
      "notimplemented"
      "unimplemented"
      "not supported"
      "not yet supported"
      "unsupported"
      "not finished"
      "not done yet"
      "todo: implement"
      "fixme: implement" ]

/// Commented-OUT code is not a note about the branch. The F# compiler's
/// ServiceInterfaceStubGenerator.fs had
///
///     | _ -> //debug "Unsupported case with %A and %A" t ts
///         None
///
/// — a silenced trace line whose "Unsupported" is a string the print once
/// carried, above a `None` that IS the partial pattern's no-match result.
/// A comment that opens with an identifier applied to a string literal or
/// to a parenthesised argument, or that carries a format hole or a print
/// call, reads as code.
let private codeMarkers = [ "%a"; "printf"; "debug" ]

let private looksLikeCode (comment: string) =
    let body =
        comment.Trim().TrimStart('/').TrimStart('(').TrimStart('*').TrimEnd(')').TrimEnd('*').Trim()

    let lower = body.ToLowerInvariant()

    codeMarkers |> List.exists lower.Contains
    || Regex.IsMatch(body, @"^[A-Za-z_][\w.]*(\s*""|\()")

let private saysUnfinished (comment: string) =
    let text = comment.ToLowerInvariant()
    stubPhrases |> List.exists text.Contains && not (looksLikeCode comment)

/// Values that stand in for a result. All of them are ordinary values that
/// only a comment turns into evidence — `null` and `Unchecked.defaultof`
/// included: `| [] -> Unchecked.defaultof<'T>` is the entire CONTRACT of a
/// SingleOrDefault, and `| null -> null` passes a sentinel through, both
/// found in the corpus. No value shape accuses itself.
let private isPlaceholder (e: SynExpr) =
    match e with
    | SynExpr.Null _ -> true
    | SynExpr.App(funcExpr = SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))))
    | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        ids |> List.map (fun i -> i.idText) |> String.concat "." = "Unchecked.defaultof"
        ->
        true
    | SynExpr.Ident id when id.idText = "None" || id.idText = "ValueNone" -> true
    | SynExpr.ArrayOrList(exprs = []) -> true
    | SynExpr.Const(constant = c) ->
        match c with
        | SynConst.String(text = "") -> true
        | SynConst.Int32 0
        | SynConst.Int64 0L
        | SynConst.Double 0.0 -> true
        // `| X -> false // Not supported yet` — the comment gate keeps
        // ordinary boolean tables quiet, so both literals may accuse
        | SynConst.Bool _ -> true
        | _ -> false
    // a qualified spelling — `Option.None`, `ValueOption.ValueNone`
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
        match (List.last ids).idText with
        | "None"
        | "ValueNone" -> true
        | _ -> false
    | _ -> false

/// Every comment in the file, as (range, text).
let private commentsOf (parseTree: ParsedInput) (source: ISourceText) =
    let ranges =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(trivia = trivia)) ->
            trivia.CodeComments
            |> List.map (fun comment ->
                match comment with
                | CommentTrivia.LineComment r -> r
                | CommentTrivia.BlockComment r -> r)
        | ParsedInput.SigFile _ -> []

    ranges |> List.map (fun r -> r, textOfRange source r)

/// Does a comment sit between this branch's arrow and its value, saying the
/// branch is unfinished?
let private accusedBy (comments: (range * string) list) (arrow: range) (body: range) =
    comments
    |> List.exists (fun (r, text) ->
        let afterArrow =
            r.StartLine > arrow.EndLine
            || (r.StartLine = arrow.EndLine && r.StartColumn >= arrow.EndColumn)

        let beforeBody =
            r.EndLine < body.StartLine
            || (r.EndLine = body.StartLine && r.EndColumn <= body.StartColumn)

        afterArrow && beforeBody && saysUnfinished text)

/// Find match branches whose whole body is a stand-in result.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()
    let comments = lazy (commentsOf parseTree source)

    // `None`/`ValueNone` is the LEGITIMATE no-match result of a partial
    // active pattern `(|X|_|)` and of a function declared to return an
    // option — whatever a comment above it says, replacing it with a raise
    // turns "did not match" into a crash. The F# compiler's
    // ServiceInterfaceStubGenerator.fs lost exactly that arm of a partial
    // pattern. Syntactic only: a declared `: 'T option`/`voption` return
    // (or the active-pattern name) is the evidence; inferred option
    // returns stay eligible — that is the rule's own example shape.
    let optionByContract (path: SyntaxNode list) (matchRange: range) =
        let optionType = Regex(@"\b(option|voption|Option|ValueOption)\b")

        path
        |> List.choose (fun node ->
            match node with
            | SyntaxNode.SynBinding(SynBinding(headPat = headPat; returnInfo = returnInfo) as b) when
                Range.rangeContainsRange b.RangeOfBindingWithRhs matchRange
                ->
                Some(b.RangeOfBindingWithRhs, headPat, returnInfo)
            | _ -> None)
        // the innermost enclosing binding is the one whose result this is
        |> List.sortBy (fun (r, _, _) -> r.EndLine - r.StartLine, r.EndColumn - r.StartColumn)
        |> List.tryHead
        |> Option.map (fun (_, headPat, returnInfo) ->
            let headName =
                match headPat with
                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText
                | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText
                | _ -> ""

            let partialActivePattern = headName.StartsWith '|' && headName.EndsWith "|_|"

            let declaredOption =
                match returnInfo, headPat with
                | Some(SynBindingReturnInfo(typeName = t)), _ -> optionType.IsMatch(textOfRange source t.Range)
                | None, SynPat.Typed(targetType = t) -> optionType.IsMatch(textOfRange source t.Range)
                | _ -> false

            partialActivePattern || declaredOption)
        |> Option.defaultValue false

    let isNone (e: SynExpr) =
        match e with
        | SynExpr.Ident id -> id.idText = "None" || id.idText = "ValueNone"
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
            (match (List.last ids).idText with
             | "None"
             | "ValueNone" -> true
             | _ -> false)
        | _ -> false

    let consider (path: SyntaxNode list) (matchRange: range) (clauses: SynMatchClause list) =
        let noneIsContract = lazy (optionByContract path matchRange)

        // a lookup table of constants is data, not a stub: only accuse a
        // branch whose siblings are actually computing something
        let siblingsCompute =
            clauses
            |> List.exists (fun (SynMatchClause(resultExpr = body)) ->
                not (isPlaceholder body)
                && match body with
                   | SynExpr.App _
                   | SynExpr.LetOrUse _
                   | SynExpr.IfThenElse _
                   | SynExpr.Match _ -> true
                   | _ -> false)

        if siblingsCompute then
            for SynMatchClause(resultExpr = body; trivia = trivia) in clauses do
                match isPlaceholder body, trivia.ArrowRange with
                | true, Some arrow when not (isNone body && noneIsContract.Value) ->
                    if accusedBy comments.Value arrow body.Range then
                        suggestions.Add
                            { Range = body.Range
                              OriginalText = textOfRange source body.Range
                              ReplacementText =
                                (let prefix = if opensSystemNamespace source then "" else "System."
                                 $"raise ({prefix}NotImplementedException())") }
                | _ -> ()

    for path, expr in index.Exprs do
        match expr with
        | SynExpr.Match(clauses = clauses)
        | SynExpr.MatchBang(clauses = clauses)
        | SynExpr.MatchLambda(matchClauses = clauses) -> consider path expr.Range clauses
        | _ -> ()

    List.ofSeq suggestions
