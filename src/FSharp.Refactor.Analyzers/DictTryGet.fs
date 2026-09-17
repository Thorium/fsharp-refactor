/// Refactoring: replace a ContainsKey-then-indexer double lookup with a
/// single TryGetValue.
///
///     if d.ContainsKey key then f d.[key] else fallback
///         →
///     match d.TryGetValue key with
///     | true, value -> f value
///     | false, _ -> fallback
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
        [
            "System.Collections.Generic.Dictionary`2"
            "System.Collections.Generic.IDictionary`2"
            "System.Collections.Generic.IReadOnlyDictionary`2"
            "System.Collections.Generic.SortedDictionary`2"
            "System.Collections.Concurrent.ConcurrentDictionary`2"
        ]

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
let private fullNameOf (t: FSharpType) =
    let t = OptionModule.stripAbbreviations t

    if t.HasTypeDefinition then
        t.TypeDefinition.TryFullName
    else
        None

/// The container's resolved type (abbreviations stripped), or None where
/// the last segment is neither a value nor a field.
let private containerType (source: ISourceText) (check: FSharpCheckFileResults) (containerIds: Ident list) =
    let last = List.last containerIds
    let r = last.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ last.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> Some(OptionModule.stripAbbreviations value.FullType)
        | :? FSharpField as field -> Some(OptionModule.stripAbbreviations field.FieldType)
        | _ -> None
    | None -> None

let private containerTypeName (source: ISourceText) (check: FSharpCheckFileResults) (containerIds: Ident list) =
    containerType source check containerIds |> Option.bind fullNameOf

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
            [
                for i, line in Seq.indexed lines ->
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
                        None
            ]

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
                                // the miss arm is spelled out: `false, _`
                                // says what it matches, where a bare `_`
                                // reads as "anything else" on a two-case
                                // tuple
                                sprintf "match %s.TryGetValue %s with" container (argumentText source keyExpr),
                                "true, value",
                                "false, _"

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
                                {
                                    Range = whole.Range
                                    OriginalText = textOfRange source whole.Range
                                    ReplacementText = replacement
                                    Concurrent = typeName = ConcurrentDictionaryType
                                }
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
                | _ -> ()
        }

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
                            {
                                Range = expr.Range
                                OriginalText = textOfRange source expr.Range
                                ReplacementText = replacement
                                Concurrent = typeName = ConcurrentDictionaryType
                            }
                    | _ -> ()
                | _ -> ()
        }

    if OptionModule.hasErrors check then
        []
    else
        AstIndex.replay collector parseTree
        List.ofSeq suggestions

// ---- FR0154: the store after a TryGetValue miss becomes GetOrAdd ----

/// A suggestion for the TryGetValue-then-store shape (FR0154).
type GetOrAddSuggestion =
    {
        /// The miss arm's body, replaced by the GetOrAdd call; the match and
        /// its hit arm stay, so the hit path keeps TryGetValue's speed. For a
        /// deferred value (see Deferred) the whole match, and the message alone.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// `xs.GetOrAdd(key, fun _ ->` - the message spells the Lazy shape with it.
        Head: string
        /// The factory expression when the miss arm computes the value in one
        /// expression that CALLS something (`compute ()`, `load key`), the case
        /// where running it once across concurrent misses can matter; None for
        /// a pure spelling (`key * 2`) or a body of several lets.
        Factory: string option
        /// The value is a Task, ValueTask or Async: two concurrent misses start
        /// two of them and one is thrown away already running, which GetOrAdd
        /// alone does not change - a `Lazy` value does. Note only: the value
        /// type changes and every reader with it.
        Deferred: bool
    }

/// A value type whose computation is DEFERRED - a Task, ValueTask or
/// Async: two concurrent misses start two of them and one runs to waste,
/// which GetOrAdd's atomic add does not change. Reported without a fix,
/// the message naming the `Lazy` value that starts it once.
let private deferredValueTypes =
    set
        [
            "System.Threading.Tasks.Task"
            "System.Threading.Tasks.Task`1"
            "System.Threading.Tasks.ValueTask"
            "System.Threading.Tasks.ValueTask`1"
            "Microsoft.FSharp.Control.FSharpAsync`1"
        ]

/// A value type the rule leaves alone: a Lazy REMEMBERS a failure and is
/// FR0152's subject once it sits behind GetOrAdd, and a function value
/// would make the lambda argument ambiguous with GetOrAdd's plain-value
/// overload.
let private refusedValueTypes = set [ "System.Lazy`1" ]

/// What the rule can do for a container, by its value type.
[<RequireQualifiedAccess>]
type private ValueKind =
    | Plain
    | Deferred
    | Refused

/// `<container>.TryGetValue <key>` / `<container>.TryGetValue(<key>)` —
/// the container segments and the key expression (parens stripped). The
/// out-parameter spelling `TryGetValue(key, &v)` carries a tuple with an
/// address-of and never passes the key gate.
[<return: Struct>]
let private (|TryGetValueCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2 && (List.last ids).idText = "TryGetValue"
        ->
        ValueSome(ids.[.. ids.Length - 2], stripParens arg)
    | _ -> ValueNone

[<TailCall>]
let rec private stripPatParens (p: SynPat) =
    match p with
    | SynPat.Paren(inner, _) -> stripPatParens inner
    | _ -> p

/// `true, x` — the hit arm's binder.
let private hitBinder (p: SynPat) =
    match stripPatParens p with
    | SynPat.Tuple(elementPats = [ SynPat.Const(SynConst.Bool true, _); SynPat.Named(ident = SynIdent(ident = x)) ]) ->
        Some x.idText
    | _ -> None

/// `false, _` — the miss arm spelled out.
let private isExplicitMiss (p: SynPat) =
    match stripPatParens p with
    | SynPat.Tuple(elementPats = [ SynPat.Const(SynConst.Bool false, _); SynPat.Wild _ ]) -> true
    | _ -> false

/// `false, _` or a trailing `_` — the miss arm.
let private isMissPattern (p: SynPat) =
    match stripPatParens p with
    | SynPat.Wild _ -> true
    | p -> isExplicitMiss p

/// The key is evaluated once in the rewrite where the original evaluated
/// it in the lookup and again in the store: pure atoms only, alone or as a
/// tuple.
let private isSimpleKey (e: SynExpr) =
    match e with
    | SynExpr.Tuple(isStruct = false; exprs = es) -> es |> List.forall isPureAtom
    | _ -> isPureAtom e

/// Does this `let` bind the name, as `let res = ...` or `let res: T = ...`?
let private bindsName (name: string) (SynBinding(headPat = p)) =
    match stripPatParens p with
    | SynPat.Named(ident = SynIdent(ident = id))
    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))) -> id.idText = name
    | _ -> false

/// The miss arm's shape: plain `let` bindings, then the store statement,
/// then the stored name alone. Yields the bindings, the store and the name.
[<TailCall>]
let rec private missArmShape (lets: SynBinding list) (e: SynExpr) =
    match e with
    | LetOrUseE lou when not (lou.IsUse || lou.IsBang || lou.IsRecursive) -> missArmShape (lets @ lou.Bindings) lou.Body
    | SynExpr.Sequential(expr1 = store; expr2 = IdentName last) -> ValueSome(lets, store, last)
    | _ -> ValueNone

/// The name a store statement puts under the looked-up key, for the
/// spellings that store exactly the computed value there and nothing else:
/// `xs.[key] <- res`, `xs[key] <- res`, `xs.TryAdd(key, res) |> ignore` and
/// `xs.AddOrUpdate(key, res, fun _ _ -> res)`.
let private storedIdent (source: ISourceText) (container: string) (key: string) (e: SynExpr) : string option =
    let sameKey (k: SynExpr) =
        textOfRange source (stripParens k).Range = key

    let sameCall (ids: Ident list) (name: string) (k: SynExpr) =
        ids.Length >= 2
        && (List.last ids).idText = name
        && pathText ids.[.. ids.Length - 2] = container
        && sameKey k

    // `... |> ignore` discards the bool TryAdd and the value AddOrUpdate
    // return; the statement is the call either way
    let unignored =
        match e with
        | SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_PipeRight"; argExpr = inner)
            argExpr = IdentName "ignore") -> inner
        | e -> e

    match unignored with
    | IndexerSet(o, k, IdentName v) when textOfRange source o.Range = container && sameKey k -> Some v
    | SynExpr.App(
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        argExpr = SynExpr.Paren(expr = SynExpr.Tuple(exprs = [ k; IdentName v ]))) when sameCall ids "TryAdd" k ->
        Some v
    | SynExpr.App(
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        argExpr = SynExpr.Paren(
            expr = SynExpr.Tuple(exprs = [ k; IdentName v; SynExpr.Lambda(parsedData = Some(_, IdentName updated)) ]))) when
        sameCall ids "AddOrUpdate" k && updated = v
        ->
        Some v
    | _ -> None

let private reraiseRegex = Regex @"\breraise\b"

/// Find the TryGetValue-then-store shape on a ConcurrentDictionary:
///
///     match xs.TryGetValue key with        match xs.TryGetValue key with
///     | true, x -> x                       | true, x -> x
///     | false, _ ->                   →    | false, _ -> xs.GetOrAdd(key, fun _ -> compute ())
///         let res = compute ()
///         xs.[key] <- res
///         res
///
/// Only the miss arm changes: the store after the miss is the window for
/// another thread to store first, after which two callers hold two
/// different values for the same key; GetOrAdd's add is atomic, so every
/// caller holds the value the dictionary holds. The factory runs outside
/// the dictionary's locks, as the original arm did, so under contention it
/// may still run twice. The match and its hit arm stay because the hit
/// path is the one a cache takes almost every time, and there TryGetValue
/// is a lock-free read (2.1 ns, nothing allocated) where GetOrAdd with a
/// lambda allocates the delegate on every call (7.3 ns, 64 B; measured in
/// benchmarks/PerfClaims). A miss arm of several `let`s keeps them, as the
/// lambda's body.
///
/// Safety rules:
///   - the container resolves to ConcurrentDictionary — the only one of
///     the dictionaries with GetOrAdd — and its value type is no Task,
///     ValueTask, Lazy, Async or function (see wrapperValueTypes)
///   - the key is a pure atom or a tuple of them, spelled the same in the
///     lookup and the store
///   - the hit arm is `true, x -> x` exactly; the miss arm is `false, _`,
///     or a trailing `_`; it binds the stored name with a plain `let` and
///     ends in the store followed by that name alone
///   - the store sits alone on its line and the arm starts a line of its
///     own, so the lines can move verbatim into the lambda
///   - the arm reads no mutable local or byref of the enclosing scope
///     (FS0407 inside the lambda) and no `reraise` (FS0413)
///   - the match spans no `#if`, and the file has no type errors
let findGetOrAdd
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : GetOrAddSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let valueKind (t: FSharpType) =
            try
                match List.ofSeq t.GenericArguments with
                | [ _; v ] ->
                    let v = OptionModule.stripAbbreviations v

                    if v.IsFunctionType then
                        ValueKind.Refused
                    else
                        match fullNameOf v with
                        | Some n when deferredValueTypes.Contains n -> ValueKind.Deferred
                        | Some n when refusedValueTypes.Contains n -> ValueKind.Refused
                        | Some _ -> ValueKind.Plain
                        | None -> ValueKind.Refused
                | _ -> ValueKind.Refused
            with OptionModule.FcsSymbolFailure ->
                ValueKind.Refused

        let concurrentValueKind (containerIds: Ident list) =
            match containerType source check containerIds with
            | Some t when fullNameOf t = Some ConcurrentDictionaryType -> valueKind t
            | _ -> ValueKind.Refused

        // the factory CALLS something: an application whose head is no
        // operator, or a constructor - `key * 2` is neither
        let rec headOf (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = f) -> headOf f
            | SynExpr.Paren(expr = inner) -> headOf inner
            | _ -> e

        let callsSomething (e: SynExpr) =
            index.Exprs
            |> Seq.exists (fun (_, sub) ->
                Range.rangeContainsRange e.Range sub.Range
                && (match sub with
                    | SynExpr.App _ ->
                        // an operator is a LongIdent of one `op_` segment
                        (match headOf sub with
                         | SynExpr.Ident id
                         | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> not (id.idText.StartsWith "op_")
                         | _ -> true)
                    | SynExpr.New _ -> true
                    | _ -> false))

        // hit arm first with any miss arm, or the explicit `false, _` miss
        // arm first (a leading `_` would take the hit case too)
        let arms (clauses: SynMatchClause list) =
            match clauses |> List.map simpleClause with
            | [ Some(hitPat, hitBody); Some(missPat, missBody) ] when isMissPattern missPat ->
                Some(hitPat, hitBody, missBody)
            | [ Some(missPat, missBody); Some(hitPat, hitBody) ] when isExplicitMiss missPat ->
                Some(hitPat, hitBody, missBody)
            | _ -> None

        let lineOf (l: int) = source.GetLineString(l - 1)

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.Match(expr = TryGetValueCall(containerIds, keyExpr); clauses = clauses) when
                    isSimpleKey keyExpr && not (spansDirective source expr.Range)
                    ->
                    match arms clauses with
                    | Some(hitPat, IdentName returned, missBody) when hitBinder hitPat = Some returned ->
                        let container = pathText containerIds
                        let key = textOfRange source keyExpr.Range
                        let armText = textOfRange source missBody.Range

                        // the store is matched by TEXT: a let in the arm
                        // rebinding the container's head or a key name would
                        // make the same spelling a different target
                        let shadowsTarget (lets: SynBinding list) =
                            let keyNames =
                                match keyExpr with
                                | SynExpr.Ident id -> [ id.idText ]
                                | SynExpr.Tuple(exprs = es) ->
                                    es
                                    |> List.choose (fun e ->
                                        match e with
                                        | SynExpr.Ident id -> Some id.idText
                                        | _ -> None)
                                | _ -> []

                            (List.head containerIds).idText :: keyNames
                            |> List.exists (fun name -> lets |> List.exists (bindsName name))

                        match missArmShape [] missBody with
                        | ValueSome(lets, store, stored) when
                            lets |> List.exists (bindsName stored)
                            && not (shadowsTarget lets)
                            && storedIdent source container key store = Some stored
                            && isSingleLine store.Range
                            && (lineOf store.Range.StartLine).Trim() = textOfRange source store.Range
                            && (lineOf missBody.Range.StartLine).Substring(0, missBody.Range.StartColumn).Trim() = ""
                            && not (reraiseRegex.IsMatch armText)
                            && not (OptionModule.capturesMutableLocal index missBody.Range)
                            && not (OptionModule.capturesByRefLike check index source missBody.Range)
                            && concurrentValueKind containerIds <> ValueKind.Refused
                            ->
                            let keyArg = argumentText source keyExpr
                            let head = $"{container}.GetOrAdd({keyArg}, fun _ ->"
                            let deferred = concurrentValueKind containerIds = ValueKind.Deferred

                            let factory =
                                match lets with
                                | [ SynBinding(expr = rhs) ] when isSingleLine rhs.Range && callsSomething rhs ->
                                    Some(textOfRange source rhs.Range)
                                | _ -> None

                            let replacement =
                                match lets with
                                | [ SynBinding(expr = rhs) ] when
                                    isSingleLine rhs.Range
                                    && isSafeInline rhs
                                    && missBody.Range.EndLine - missBody.Range.StartLine = 2
                                    && not (armText.Contains "//")
                                    && not (armText.Contains "(*")
                                    ->
                                    // `let res = compute ()` / store / `res`:
                                    // the factory is the computation itself
                                    Some $"{head} {textOfRange source rhs.Range})"
                                | _ ->
                                    // the arm's lines, minus the store, move
                                    // into the lambda body under the match
                                    // the last line stops at the arm's end:
                                    // what follows there - a paren closing an
                                    // enclosing expression, a trailing comment -
                                    // is outside the replaced range and stays
                                    let body =
                                        [
                                            for l in missBody.Range.StartLine .. missBody.Range.EndLine do
                                                if l <> store.Range.StartLine then
                                                    let line = lineOf l

                                                    let line =
                                                        if l = missBody.Range.EndLine then
                                                            line.Substring(0, missBody.Range.EndColumn)
                                                        else
                                                            line

                                                    if l = missBody.Range.StartLine then
                                                        line.Substring missBody.Range.StartColumn
                                                    else
                                                        line
                                        ]
                                        |> String.concat "\n"

                                    reindentBlock (missBody.Range.StartColumn + 4) missBody.Range.StartColumn body
                                    |> Option.map (fun block -> $"{head}\n{block})")

                            match replacement with
                            | Some _ when deferred ->
                                {
                                    Range = expr.Range
                                    OriginalText = textOfRange source expr.Range
                                    ReplacementText = ""
                                    Head = head
                                    Factory = factory
                                    Deferred = true
                                }
                            | Some replacement ->
                                {
                                    Range = missBody.Range
                                    OriginalText = armText
                                    ReplacementText = replacement
                                    Head = head
                                    Factory = factory
                                    Deferred = false
                                }
                            | None -> ()
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]
