/// Refactoring: hand-rolled string emptiness tests become the BCL
/// predicates that say what they mean.
///
///     isNull x || x = ""            →  String.IsNullOrEmpty x
///     x = null || x = ""            →  String.IsNullOrEmpty x
///     not (isNull x) && x <> ""     →  not (String.IsNullOrEmpty x)
///     isNull x || x.Trim() = ""     →  String.IsNullOrWhiteSpace x
///     x.Trim() = ""                 →  String.IsNullOrWhiteSpace x   (editor)
///     String.IsNullOrEmpty (x.Trim())  →  String.IsNullOrWhiteSpace x  (editor)
///
/// The guarded forms are EXACT rewrites: null short-circuits the `||` to
/// true exactly as IsNullOrEmpty/IsNullOrWhiteSpace answer true, and
/// `Trim()`'s no-argument overload strips precisely the Char.IsWhiteSpace
/// set that IsNullOrWhiteSpace tests — so the CLI applies them freely,
/// and the Trim spellings stop allocating a trimmed copy per call.
///
/// The BARE Trim forms differ on one input: null throws in the original
/// and answers true in the rewrite. Treating null as blank is almost
/// always the intent, but it is a behavior change only a human should
/// sign off, so those ride as editor actions and the CLI only points.
///
/// The subject must be a bare identifier or dotted path (a pure read —
/// it is written twice in the trigger and once in the replacement).
module FSharp.Refactor.StringEmptiness

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        /// True: exact rewrite, CLI-applied. False: the bare-Trim form —
        /// null behavior changes, editor-only.
        Guarded: bool
        /// Which predicate the replacement uses, for the message.
        WhiteSpace: bool
    }

/// A name that can be respelled from its idText alone — backticked names
/// lose their ticks in idText and would come back uncompilable.
let private isPlainIdent (s: string) =
    s.Length > 0
    && (System.Char.IsLetter s[0] || s[0] = '_')
    && s |> Seq.forall (fun c -> System.Char.IsLetterOrDigit c || c = '_' || c = '\'')

/// A pure-read subject: identifier or dotted path. Yields its source text.
[<return: Struct>]
let private (|Subject|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident i when isPlainIdent i.idText -> ValueSome i.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        not ids.IsEmpty && ids |> List.forall (fun i -> isPlainIdent i.idText)
        ->
        ValueSome(ids |> List.map (fun i -> i.idText) |> String.concat ".")
    | _ -> ValueNone

/// `subject.Trim()` with the no-argument overload — the one whose
/// whitespace set matches IsNullOrWhiteSpace.
[<return: Struct>]
let private (|TrimOf|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = UnitConst) when
        ids.Length >= 2 && (List.last ids).idText = "Trim"
        ->
        ValueSome(ids[.. ids.Length - 2] |> List.map (fun i -> i.idText) |> String.concat ".")
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.DotGet(expr = Subject s; longDotId = SynLongIdent(id = [ m ]))
        argExpr = UnitConst) when m.idText = "Trim" -> ValueSome s
    | _ -> ValueNone

[<return: Struct>]
let private (|EmptyString|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.String(text = ""), _) -> ValueSome()
    | _ -> ValueNone

/// `op x y` for a named infix operator.
[<return: Struct>]
let private (|Infix|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName op; argExpr = lhs); argExpr = rhs) ->
        ValueSome(op, stripParens lhs, stripParens rhs)
    | _ -> ValueNone

/// `isNull x` / `x = null` / `null = x` — the subject tested for null.
[<return: Struct>]
let private (|NullCheck|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = IdentName "isNull"; argExpr = arg) ->
        match stripParens arg with
        | Subject s -> ValueSome s
        | _ -> ValueNone
    | Infix("op_Equality", Subject s, SynExpr.Null _)
    | Infix("op_Equality", SynExpr.Null _, Subject s) -> ValueSome s
    | _ -> ValueNone

/// `not (isNull x)` / `x <> null` / `null <> x`.
[<return: Struct>]
let private (|NotNullCheck|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = arg) ->
        match stripParens arg with
        | NullCheck s -> ValueSome s
        | _ -> ValueNone
    | Infix("op_Inequality", Subject s, SynExpr.Null _)
    | Infix("op_Inequality", SynExpr.Null _, Subject s) -> ValueSome s
    | _ -> ValueNone

/// `x = ""` / `x.Trim() = ""` / `x.Trim().Length = 0` — the subject and
/// whether the test is whitespace-wide (Trim-based).
[<return: Struct>]
let private (|EmptyCheck|_|) (e: SynExpr) =
    match e with
    | Infix("op_Equality", Subject s, EmptyString)
    | Infix("op_Equality", EmptyString, Subject s) -> ValueSome(s, false)
    | Infix("op_Equality", TrimOf s, EmptyString)
    | Infix("op_Equality", EmptyString, TrimOf s) -> ValueSome(s, true)
    | Infix("op_Equality", SynExpr.DotGet(expr = TrimOf s; longDotId = SynLongIdent(id = [ l ])), ZeroConst) when
        l.idText = "Length"
        ->
        ValueSome(s, true)
    | _ -> ValueNone

/// `x <> ""` / `x.Trim() <> ""`.
[<return: Struct>]
let private (|NonEmptyCheck|_|) (e: SynExpr) =
    match e with
    | Infix("op_Inequality", Subject s, EmptyString)
    | Infix("op_Inequality", EmptyString, Subject s) -> ValueSome(s, false)
    | Infix("op_Inequality", TrimOf s, EmptyString)
    | Infix("op_Inequality", EmptyString, TrimOf s) -> ValueSome(s, true)
    | _ -> ValueNone

/// `String.IsNullOrEmpty arg` — with or without the System prefix.
[<return: Struct>]
let private (|IsNullOrEmptyCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2
        && (List.last ids).idText = "IsNullOrEmpty"
        && ids[ids.Length - 2].idText = "String"
        ->
        ValueSome(stripParens arg)
    | _ -> ValueNone

/// Find hand-rolled emptiness tests.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()
    let index = AstIndex.ofTree parseTree

    // inside query { } or a quotation the expression belongs to a
    // TRANSLATOR (SQL above all), which may know `||` and `=` but not
    // String.IsNullOrEmpty — the whole rule stands down there
    let translatedRanges =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = IdentName "query"; argExpr = SynExpr.ComputationExpr(expr = body)) ->
                Some body.Range
            | SynExpr.Quote(quotedExpr = q) -> Some q.Range
            | _ -> None)

    let inTranslatedContext (r: range) =
        translatedRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

    // FSharp.Core's String MODULE shadows the System.String type until the
    // file opens System, and the module has no IsNullOrEmpty — the
    // qualified spelling always resolves
    let prefix = if opensSystemNamespace source then "" else "System."

    let add (range: range) (replacement: string) (guarded: bool) (whiteSpace: bool) =
        suggestions.Add
            {
                Range = range
                OriginalText = textOfRange source range
                ReplacementText = replacement
                Guarded = guarded
                WhiteSpace = whiteSpace
            }

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                if isSingleLine expr.Range && not (inTranslatedContext expr.Range) then
                    match expr with
                    // isNull x || x = "" — the null check LEADS, so null
                    // short-circuits before anything dereferences: exact
                    | Infix("op_BooleanOr", NullCheck a, EmptyCheck(b, ws)) when a = b ->
                        let predicate = if ws then "IsNullOrWhiteSpace" else "IsNullOrEmpty"
                        add expr.Range $"{prefix}String.{predicate} {a}" true ws
                    // x = "" || isNull x — exact only while the leading
                    // test cannot throw: `null = ""` is false, but
                    // `null.Trim()` throws where the rewrite answers true,
                    // so the Trim spellings in this order ride editor-only
                    | Infix("op_BooleanOr", EmptyCheck(b, ws), NullCheck a) when a = b ->
                        let predicate = if ws then "IsNullOrWhiteSpace" else "IsNullOrEmpty"
                        add expr.Range $"{prefix}String.{predicate} {a}" (not ws) ws
                    // not (isNull x) && x <> "" — null short-circuits to
                    // false before the dereference: exact
                    | Infix("op_BooleanAnd", NotNullCheck a, NonEmptyCheck(b, ws)) when a = b ->
                        let predicate = if ws then "IsNullOrWhiteSpace" else "IsNullOrEmpty"
                        add expr.Range $"not ({prefix}String.{predicate} {a})" true ws
                    // x <> "" && not (isNull x) — same order caveat as the
                    // or-form: Trim on the left throws first on null
                    | Infix("op_BooleanAnd", NonEmptyCheck(b, ws), NotNullCheck a) when a = b ->
                        let predicate = if ws then "IsNullOrWhiteSpace" else "IsNullOrEmpty"
                        add expr.Range $"not ({prefix}String.{predicate} {a})" (not ws) ws
                    // String.IsNullOrEmpty (x.Trim()) — trims a copy just
                    // to test it; null behavior changes (throw → true)
                    | IsNullOrEmptyCall(TrimOf s) -> add expr.Range $"{prefix}String.IsNullOrWhiteSpace {s}" false true
                    // bare x.Trim() = "" / x.Trim().Length = 0
                    | EmptyCheck(s, true) -> add expr.Range $"{prefix}String.IsNullOrWhiteSpace {s}" false true
                    | NonEmptyCheck(s, true) -> add expr.Range $"not ({prefix}String.IsNullOrWhiteSpace {s})" false true
                    | _ -> ()
        }

    AstIndex.replay collector parseTree

    // an or-form contains a bare Trim-check as its operand; the outer
    // rewrite subsumes the inner one whichever way each is gated
    let allSuggestions = List.ofSeq suggestions

    allSuggestions
    |> List.filter (fun s ->
        not (
            allSuggestions
            |> List.exists (fun outer ->
                not (Range.equals outer.Range s.Range)
                && Range.rangeContainsRange outer.Range s.Range)
        ))
    |> List.filter (fun s -> not (spansDirective source s.Range))
