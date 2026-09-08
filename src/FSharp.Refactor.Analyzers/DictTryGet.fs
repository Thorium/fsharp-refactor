/// Refactoring: replace a ContainsKey-then-indexer double lookup with a
/// single TryGetValue.
///
///     if d.ContainsKey key then f d.[key] else fallback
///         →
///     match d.TryGetValue key with
///     | true, value -> f value
///     | _ -> fallback
///
/// Besides the second hash lookup, on ConcurrentDictionary the original is a
/// race: the key can disappear between the two calls.
///
/// Safety rules:
///   - the container's type must resolve to a known BCL dictionary
///     (Dictionary, IDictionary, IReadOnlyDictionary, SortedDictionary,
///     ConcurrentDictionary) or F# Map — Map gets the option-idiom rewrite
///     (`match m.TryFind k with | Some value -> ... | None -> ...`); unknown
///     types may lack the lookup member entirely
///   - the key must be a pure atom: it was evaluated twice and will be
///     evaluated once, which must not change behavior
///   - the then-branch must use the indexer (`d.[key]` or `d[key]`) at least
///     once, and the else-branch must not use it at all
///   - `value` must not already occur in the spliced branch text (it
///     becomes the found-arm's binder); the then-branch must be
///     single-line; elif positions are skipped IN PLACE — but an
///     if/elif/.../else chain still converges: the outer if rewrites
///     alone, carrying the elif chain verbatim into the fallthrough arm
///     with its leading `elif` spelled back to `if`, and the next
///     fix-then-reanalyze pass peels the next level
///   - the file must have no type errors
module FSharp.Refactor.DictTryGet

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole if-expression, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// True when the container is a ConcurrentDictionary (the message
        /// mentions the race).
        Concurrent: bool
    }

let private dictionaryTypes =
    set
        [ "System.Collections.Generic.Dictionary`2"
          "System.Collections.Generic.IDictionary`2"
          "System.Collections.Generic.IReadOnlyDictionary`2"
          "System.Collections.Generic.SortedDictionary`2"
          "System.Collections.Concurrent.ConcurrentDictionary`2" ]

[<Literal>]
let private FSharpMapType = "Microsoft.FSharp.Collections.FSharpMap`2"

[<Literal>]
let private ConcurrentDictionaryType =
    "System.Collections.Concurrent.ConcurrentDictionary`2"

/// `<container>.ContainsKey <key>` — returns the container segments and the
/// key expression (parens stripped).
[<return: Struct>]
let private (|ContainsKeyCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2 && (List.last ids).idText = "ContainsKey"
        ->
        ValueSome(ids.[.. ids.Length - 2], stripParens arg)
    | _ -> ValueNone

let private pathText (ids: Ident list) =
    ids |> List.map (fun i -> i.idText) |> String.concat "."

/// A suggestion for the check-then-add shape (FR0018).
type TryAddSuggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        /// True for ConcurrentDictionary, where check-then-add is a race.
        Concurrent: bool
    }

/// Only these have a TryAdd member.
let private tryAddTypes =
    set [ "System.Collections.Generic.Dictionary`2"; ConcurrentDictionaryType ]

/// `container.[key] <- value` or F# 6 `container[key] <- value`.
[<return: Struct>]
let private (|IndexerSet|_|) (e: SynExpr) =
    match e with
    | SynExpr.DotIndexedSet(objectExpr = o; indexArgs = idx; valueExpr = v) -> ValueSome(o, stripParens idx, v)
    | SynExpr.Set(
        targetExpr = SynExpr.App(
            flag = ExprAtomicFlag.Atomic; funcExpr = o; argExpr = SynExpr.ArrayOrListComputed(expr = idx))
        rhsExpr = v) -> ValueSome(o, stripParens idx, v)
    | _ -> ValueNone

/// All indexer accesses of the container with the given key inside an
/// expression: `d.[k]` and F# 6 `d[k]`. Matching is textual on container and
/// key, which is safe because both are constrained to atoms.
[<TailCall>]
let rec private indexerLoop
    (isMatch: SynExpr -> SynExpr -> bool)
    (uses: ResizeArray<range>)
    (pending: SynExpr list)
    : unit =
    match pending with
    | [] -> ()
    | e :: rest ->
        match e with
        | SynExpr.DotIndexedGet(objectExpr = o; indexArgs = idx) when isMatch o idx ->
            uses.Add e.Range
            indexerLoop isMatch uses rest
        | SynExpr.App(flag = ExprAtomicFlag.Atomic; funcExpr = f; argExpr = SynExpr.ArrayOrListComputed(expr = idx)) when
            isMatch f idx
            ->
            uses.Add e.Range
            indexerLoop isMatch uses rest
        | SynExpr.Paren(expr = inner) -> indexerLoop isMatch uses (inner :: rest)
        | SynExpr.App(funcExpr = f; argExpr = a) -> indexerLoop isMatch uses (f :: a :: rest)
        | SynExpr.Tuple(exprs = es)
        | SynExpr.ArrayOrList(exprs = es) -> indexerLoop isMatch uses (es @ rest)
        | SynExpr.IfThenElse(ifExpr = c; thenExpr = t; elseExpr = els) ->
            indexerLoop isMatch uses (c :: t :: (Option.toList els) @ rest)
        | SynExpr.Typed(expr = inner) -> indexerLoop isMatch uses (inner :: rest)
        | SynExpr.DotGet(expr = inner) -> indexerLoop isMatch uses (inner :: rest)
        | SynExpr.InterpolatedString(contents = parts) ->
            let fills =
                parts
                |> List.choose (fun part ->
                    match part with
                    | SynInterpolatedStringPart.FillExpr(fillExpr = fill) -> Some fill
                    | _ -> None)

            indexerLoop isMatch uses (fills @ rest)
        | _ -> indexerLoop isMatch uses rest

let private indexerUses (source: ISourceText) (container: string) (key: string) (root: SynExpr) : range list =
    let uses = ResizeArray<range>()

    let isMatch (objectExpr: SynExpr) (indexExpr: SynExpr) =
        textOfRange source objectExpr.Range = container
        && textOfRange source (stripParens indexExpr).Range = key

    indexerLoop isMatch uses [ root ]
    List.ofSeq uses

/// Replace single-line subranges of a single-line region with `value`.
let private substitute (source: ISourceText) (region: range) (uses: range list) : string option =
    if not (isSingleLine region) then
        None
    elif uses |> List.exists (fun u -> u.StartLine <> region.StartLine) then
        None
    else
        let text = textOfRange source region

        let replaced =
            uses
            |> List.sortByDescending (fun u -> u.StartColumn)
            |> List.fold
                (fun (t: string) (u: range) ->
                    t.Substring(0, u.StartColumn - region.StartColumn)
                    + "value"
                    + t.Substring(u.EndColumn - region.StartColumn))
                text

        Some replaced

/// Find ContainsKey-then-indexer patterns rewritable to TryGetValue.
/// Requires typed check results for the dictionary-type gate.
let private containerTypeName (source: ISourceText) (check: FSharpCheckFileResults) (containerIds: Ident list) =
    let last = List.last containerIds
    let r = last.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    let fullNameOf (t: FSharpType) =
        let t = OptionModule.stripAbbreviations t

        if t.HasTypeDefinition then
            t.TypeDefinition.TryFullName
        else
            None

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ last.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> fullNameOf value.FullType
        | :? FSharpField as field -> fullNameOf field.FieldType
        | _ -> None
    | None -> None

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()
    let containerTypeName = containerTypeName source check

    // shared by the if-form and the `match d.ContainsKey k with true/false` form
    // A multi-line else-branch (an elif CHAIN above all) is carried into
    // the fallthrough arm VERBATIM, re-indented, with a leading `elif`
    // spelled back to `if` — which the next fix-then-reanalyze pass then
    // rewrites in turn, peeling the chain one level per pass. Returns None
    // when a continuation line cannot take the shift.
    let reindentedElse (elseExpr: SynExpr) (targetColumn: int) =
        let raw = textOfRange source elseExpr.Range
        let delta = targetColumn - elseExpr.Range.StartColumn
        let lines = raw.Replace("\r", "").Split '\n'

        let shifted =
            [ for i, line in Seq.indexed lines ->
                  if i = 0 then
                      let line =
                          if line.StartsWith "elif" then
                              "if" + line.Substring 4
                          else
                              line

                      Some(String.replicate targetColumn " " + line)
                  elif System.String.IsNullOrWhiteSpace line then
                      Some ""
                  elif delta >= 0 then
                      Some(String.replicate delta " " + line)
                  elif line.Length >= -delta && line.Substring(0, -delta).Trim() = "" then
                      Some(line.Substring(-delta))
                  else
                      None ]

        if shifted |> List.contains None then
            None
        else
            Some(shifted |> List.choose id |> String.concat "\n")

    let handleCandidate (whole: SynExpr) (containerIds: Ident list) (keyExpr: SynExpr) thenExpr elseExpr =
        let elseIsInline = isSingleLine (elseExpr: SynExpr).Range && isSafeInline elseExpr

        if
            isPureAtom keyExpr
            && isSingleLine (thenExpr: SynExpr).Range
            && isSafeInline thenExpr
            && (elseIsInline || not (spansDirective source whole.Range))
        then
            let container = pathText containerIds
            let key = textOfRange source keyExpr.Range
            let thenUses = indexerUses source container key thenExpr
            let elseUses = indexerUses source container key elseExpr

            let mentionsValue =
                // `value` becomes the found-arm's binder; the fallthrough
                // arm binds nothing, but the inline emission splices both
                // texts, so the inline path keeps the historical check
                Regex.IsMatch(textOfRange source thenExpr.Range, @"\bvalue\b")
                || (elseIsInline && Regex.IsMatch(textOfRange source elseExpr.Range, @"\bvalue\b"))

            if not thenUses.IsEmpty && elseUses.IsEmpty && not mentionsValue then
                match containerTypeName containerIds with
                | Some typeName when dictionaryTypes.Contains typeName || typeName = FSharpMapType ->
                    match substitute source thenExpr.Range thenUses with
                    | Some thenText ->
                        let elseText = textOfRange source elseExpr.Range

                        // F# Map's idiom is TryFind returning an option;
                        // BCL dictionaries use TryGetValue's out-tuple
                        let header, foundPat, missingPat =
                            if typeName = FSharpMapType then
                                sprintf "match %s.TryFind %s with" container (argumentText source keyExpr),
                                "Some value",
                                "None"
                            else
                                sprintf "match %s.TryGetValue %s with" container (argumentText source keyExpr),
                                "true, value",
                                "_"

                        let replacement =
                            if elseIsInline && isSingleLine whole.Range then
                                Some $"%s{header} | %s{foundPat} -> %s{thenText} | %s{missingPat} -> %s{elseText}"
                            elif elseIsInline then
                                let indent = String.replicate whole.Range.StartColumn " "

                                Some(
                                    sprintf
                                        "%s\n%s| %s -> %s\n%s| %s -> %s"
                                        header
                                        indent
                                        foundPat
                                        thenText
                                        indent
                                        missingPat
                                        elseText
                                )
                            else
                                // multi-line else (an elif chain above all):
                                // the fallthrough arm carries it verbatim,
                                // and the next pass peels the next level
                                let indent = String.replicate whole.Range.StartColumn " "

                                reindentedElse elseExpr (whole.Range.StartColumn + 4)
                                |> Option.map (fun elseBlock ->
                                    sprintf
                                        "%s\n%s| %s -> %s\n%s| %s ->\n%s"
                                        header
                                        indent
                                        foundPat
                                        thenText
                                        indent
                                        missingPat
                                        elseBlock)

                        match replacement with
                        | Some replacement ->
                            suggestions.Add
                                { Range = whole.Range
                                  OriginalText = textOfRange source whole.Range
                                  ReplacementText = replacement
                                  Concurrent = typeName = ConcurrentDictionaryType }
                        | None -> ()
                    | None -> ()
                | _ -> ()

    let (|TruePat|_|) (p: SynPat) =
        match p with
        | SynPat.Const(SynConst.Bool true, _) -> Some()
        | _ -> None

    let (|FalsePat|_|) (p: SynPat) =
        match p with
        | SynPat.Const(SynConst.Bool false, _) -> Some()
        | _ -> None

    let (|AnyPat|_|) (p: SynPat) =
        match p with
        | TruePat
        | FalsePat
        | SynPat.Wild _ -> Some()
        | _ -> None

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.IfThenElse(
                    ifExpr = ContainsKeyCall(containerIds, keyExpr)
                    thenExpr = thenExpr
                    elseExpr = Some elseExpr
                    trivia = trivia) when not trivia.IsElif ->
                    handleCandidate expr containerIds keyExpr thenExpr elseExpr
                | SynExpr.Match(expr = ContainsKeyCall(containerIds, keyExpr); clauses = clauses) ->
                    match clauses |> List.map simpleClause with
                    | [ Some(TruePat, thenExpr); Some(AnyPat, elseExpr) ] ->
                        handleCandidate expr containerIds keyExpr thenExpr elseExpr
                    | [ Some(FalsePat, elseExpr); Some(AnyPat, thenExpr) ] ->
                        handleCandidate expr containerIds keyExpr thenExpr elseExpr
                    | _ -> ()
                | _ -> () }

    if OptionModule.hasErrors check then
        []
    else
        AstIndex.replay collector parseTree
        List.ofSeq suggestions

/// Find the check-then-add shape (FR0018): `if not (d.ContainsKey k) then
/// d.[k] <- v` becomes a single `d.TryAdd(k, v) |> ignore`. On
/// ConcurrentDictionary the original is a race; on Dictionary it is a double
/// lookup. The value must be a pure atom — TryAdd evaluates it always, where
/// the original evaluated it only when the key was absent.
let findTryAdd (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : TryAddSuggestion list =
    let suggestions = ResizeArray<TryAddSuggestion>()
    let containerTypeName = containerTypeName source check

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.IfThenElse(
                    ifExpr = SynExpr.App(
                        isInfix = false
                        funcExpr = IdentName "not"
                        argExpr = SynExpr.Paren(expr = ContainsKeyCall(containerIds, keyExpr)))
                    thenExpr = IndexerSet(setObj, setKey, setValue)
                    elseExpr = None
                    trivia = trivia) when
                    not trivia.IsElif
                    && isPureAtom keyExpr
                    && isPureAtom (stripParens setValue)
                    && textOfRange source setObj.Range = pathText containerIds
                    && textOfRange source setKey.Range = textOfRange source keyExpr.Range
                    ->
                    match containerTypeName containerIds with
                    | Some typeName when tryAddTypes.Contains typeName ->
                        let replacement =
                            sprintf
                                "%s.TryAdd(%s, %s) |> ignore"
                                (pathText containerIds)
                                (textOfRange source keyExpr.Range)
                                (textOfRange source (stripParens setValue).Range)

                        suggestions.Add
                            { Range = expr.Range
                              OriginalText = textOfRange source expr.Range
                              ReplacementText = replacement
                              Concurrent = typeName = ConcurrentDictionaryType }
                    | _ -> ()
                | _ -> () }

    if OptionModule.hasErrors check then
        []
    else
        AstIndex.replay collector parseTree
        List.ofSeq suggestions
