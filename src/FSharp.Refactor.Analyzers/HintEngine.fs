/// Refactoring: a term-rewriting hint engine compatible with FSharpLint's
/// hint syntax.
///
/// A rule is a single line `lhs ===> rhs`, both sides ordinary F# expressions
/// where a single-letter lowercase identifier is a metavariable binding any
/// subexpression, and everything else must match literally:
///
///     not (a = b) ===> a <> b
///     List.sum (List.map f x) ===> List.sumBy f x
///     x = null ===> isNull x
///
/// Both sides are parsed with the F# compiler itself, so operator and literal
/// shapes need no special syntax; matching is structural unification with
/// parentheses transparent on both sides. A metavariable occurring twice must
/// bind textually identical expressions.
///
/// Safety rules beyond FSharpLint:
///   - a rule whose right side drops or duplicates a metavariable only fires
///     when that binding is a pure atom (`false && f ()` is never rewritten
///     to `false` — it would drop the effect of `f ()`)
///   - substituted bindings are parenthesized unless atomic
///   - the whole replacement is parenthesized when the matched expression was
///     an operand of an enclosing application
///   - a rule comparing a metavariable against a bool literal (`x = true`)
///     only fires when the binding is provably bool: `o = true` also
///     type-checks for `o : obj` (the literal subsumes to obj), where
///     dropping the comparison would not compile
///
/// The built-in rules are curated (see `defaultRules`); repositories can add
/// their own via `hints.add` in fsharprefactor.json. Invalid rules are
/// skipped silently.
module FSharp.Refactor.HintEngine

open System
open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting

open FSharp.Refactor.Text

/// A replacement that is just a name or a dotted path needs no parentheses
/// when it lands in an operand position. Built once: this is consulted for
/// every hint of every file, and constructing it there re-parsed the pattern
/// every time — which is what our own FR0015 flags.
let private plainOperand = System.Text.RegularExpressions.Regex @"^[\w.]+$"

type Suggestion =
    {
        /// Range of the matched expression, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The rule that produced the suggestion, e.g. "not (a = b) ===> a <> b".
        Rule: string
    }

/// A parsed, validated rule.
type Hint =
    private
        {
            RuleText: string
            Lhs: SynExpr
            /// Verbatim right-side text from the rule.
            RhsText: string
            /// Metavariable occurrences in the right side: name and its
            /// character span within RhsText, in descending position order.
            RhsVarSpans: (string * int * int) list
            /// The occurrences (by span start) that sit as operands of a
            /// boolean `&&` or `||` on the right side, with that operator's
            /// text. An operand is bracketed by precedence, not like an
            /// argument: `not ((List.isEmpty a) && (List.isEmpty b))` is
            /// what the De Morgan rules produced before this distinction.
            RhsBoolOperandSpans: Map<int, string>
            /// Metavariables that must bind pure atoms because the right side
            /// drops or duplicates them.
            PureOnlyVars: Set<string>
            /// Metavariables the left side compares against a bool LITERAL.
            /// `x = true` type-checks with x : obj too (the literal subsumes
            /// to obj), so dropping the comparison demands typed proof that
            /// the binding really is bool.
            BoolTypedVars: Set<string>
            /// Metavariables of NaN-sensitive rules: an ordering flip
            /// (`not (a > b) ===> a <= b`), a `compare` collapse, or a
            /// sort-to-min. All of these change the answer when a float NaN
            /// is involved — `not (nan > limit)` is true, `nan <= limit` is
            /// false — so the bindings need typed proof they are not floats.
            NotFloatVars: Set<string>
            /// Coarse first-token key of the left side, for indexing.
            HeadKey: string
            /// The metavariable that is the LAST argument of a right side
            /// shaped `f args x` — the one a pipeline hands over. When the
            /// matched code was a pipeline whose head binds it, the rewrite
            /// is rendered back as a pipeline, `x |> f args`: rendered as
            /// the application `f args x`, a lambda among `args` is
            /// type-checked before `x`, and a member lookup on its
            /// parameter meets an indeterminate type. Fable's UnionTests,
            /// Nu's WorldModuleEntity and PethostBackup's Util all lost
            /// `xs |> M.map (fun x -> x.Member) |> M.concat` this way.
            PipeTail: string option
        }

let private isMetaVar (name: string) =
    name.Length = 1 && Char.IsLower name.[0]

[<return: Struct>]
let private (|MetaVar|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident ident when isMetaVar ident.idText -> ValueSome ident.idText
    | _ -> ValueNone

/// Structural equality of the constant kinds that appear in rules (SynConst
/// itself carries NoEquality).
let private constEq (a: SynConst) (b: SynConst) =
    match a, b with
    | SynConst.Bool x, SynConst.Bool y -> x = y
    | SynConst.Int32 x, SynConst.Int32 y -> x = y
    | SynConst.Int64 x, SynConst.Int64 y -> x = y
    | SynConst.Double x, SynConst.Double y -> x = y
    | SynConst.Char x, SynConst.Char y -> x = y
    | SynConst.String(s1, k1, _), SynConst.String(s2, k2, _) -> s1 = s2 && k1 = k2
    | SynConst.Unit, SynConst.Unit -> true
    | _ -> false

/// The coarse first-token key used to index rules and prefilter candidates.
[<TailCall>]
let rec private headKey (e: SynExpr) : string =
    match e with
    | SynExpr.Paren(expr = inner) -> headKey inner
    | SynExpr.App(funcExpr = f) -> headKey f
    | SynExpr.Ident ident -> ident.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> identText ids
    | SynExpr.Const _ -> "#const"
    | SynExpr.Tuple _ -> "#tuple"
    | SynExpr.ArrayOrList _ -> "#list"
    | SynExpr.Null _ -> "#null"
    | _ -> "#other"

/// Unify pending pattern/target pairs, filling `bindings`. Consistency of
/// repeated metavariables is checked on the target source text.
[<TailCall>]
let rec private unifyLoop
    (source: ISourceText)
    (bindings: Dictionary<string, SynExpr>)
    (pending: (SynExpr * SynExpr) list)
    : bool =
    match pending with
    | [] -> true
    | (pat, target) :: rest ->
        match pat, target with
        | SynExpr.Paren(expr = p), _ -> unifyLoop source bindings ((p, target) :: rest)
        | _, SynExpr.Paren(expr = t) -> unifyLoop source bindings ((pat, t) :: rest)
        | MetaVar v, t ->
            match bindings.TryGetValue v with
            | true, existing ->
                textOfRange source existing.Range = textOfRange source t.Range
                && unifyLoop source bindings rest
            | false, _ ->
                bindings.[v] <- t
                unifyLoop source bindings rest
        | SynExpr.Ident a, SynExpr.Ident b -> a.idText = b.idText && unifyLoop source bindings rest
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = a)), SynExpr.LongIdent(longDotId = SynLongIdent(id = b)) ->
            identText a = identText b && unifyLoop source bindings rest
        | SynExpr.Ident a, SynExpr.LongIdent(longDotId = SynLongIdent(id = [ b ]))
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ a ])), SynExpr.Ident b ->
            a.idText = b.idText && unifyLoop source bindings rest
        | SynExpr.Const(c1, _), SynExpr.Const(c2, _) -> constEq c1 c2 && unifyLoop source bindings rest
        | SynExpr.Null _, SynExpr.Null _ -> unifyLoop source bindings rest
        // pipe normalization: `lhs |> rhs` in the TARGET matches an
        // application-shaped pattern as `rhs lhs` (patterns that are pipes
        // themselves keep structural matching)
        | (SynExpr.App _ as p), PipeApp(lhs, rhs) when
            (match p with
             | PipeApp _ -> false
             | _ -> true)
            ->
            unifyLoop
                source
                bindings
                ((p, SynExpr.App(ExprAtomicFlag.NonAtomic, false, rhs, lhs, target.Range))
                 :: rest)
        | SynExpr.App(funcExpr = pf; argExpr = pa), SynExpr.App(funcExpr = tf; argExpr = ta) ->
            unifyLoop source bindings ((pf, tf) :: (pa, ta) :: rest)
        | SynExpr.Tuple(exprs = ps), SynExpr.Tuple(exprs = ts) ->
            ps.Length = ts.Length && unifyLoop source bindings (List.zip ps ts @ rest)
        | SynExpr.ArrayOrList(isArray = pa; exprs = ps), SynExpr.ArrayOrList(isArray = ta; exprs = ts) ->
            pa = ta
            && ps.Length = ts.Length
            && unifyLoop source bindings (List.zip ps ts @ rest)
        | SynExpr.ArrayOrListComputed(isArray = pa; expr = p), SynExpr.ArrayOrListComputed(isArray = ta; expr = t) ->
            pa = ta && unifyLoop source bindings ((p, t) :: rest)
        | SynExpr.Sequential(expr1 = p1; expr2 = p2), SynExpr.Sequential(expr1 = t1; expr2 = t2) ->
            unifyLoop source bindings ((p1, t1) :: (p2, t2) :: rest)
        | _ -> false

/// Unify the rule's left side against a target expression.
let private unify (source: ISourceText) (bindings: Dictionary<string, SynExpr>) (pat: SynExpr) (target: SynExpr) =
    unifyLoop source bindings [ pat, target ]

/// Metavariable occurrences in the pending expressions, accumulated in order.
[<TailCall>]
let rec private collectVarsLoop (acc: ResizeArray<string * range>) (pending: SynExpr list) =
    match pending with
    | [] -> ()
    | e :: rest ->
        match e with
        | MetaVar v ->
            acc.Add(v, e.Range)
            collectVarsLoop acc rest
        | SynExpr.Paren(expr = inner) -> collectVarsLoop acc (inner :: rest)
        | SynExpr.App(funcExpr = f; argExpr = a) -> collectVarsLoop acc (f :: a :: rest)
        | SynExpr.Tuple(exprs = es)
        | SynExpr.ArrayOrList(exprs = es) -> collectVarsLoop acc (es @ rest)
        | SynExpr.ArrayOrListComputed(expr = inner) -> collectVarsLoop acc (inner :: rest)
        | SynExpr.Sequential(expr1 = e1; expr2 = e2) -> collectVarsLoop acc (e1 :: e2 :: rest)
        | _ -> collectVarsLoop acc rest

/// All metavariable occurrences in an expression tree.
let private collectVars (e: SynExpr) : (string * range) list =
    let acc = ResizeArray()
    collectVarsLoop acc [ e ]
    List.ofSeq acc

// Rule sides are parsed as `let __h = <side>`; the side's text starts at this
// column on line 1.
[<Literal>]
let private ParsePrefix = "let __h = "

let private parseChecker = lazy (FSharpChecker.Create(keepAssemblyContents = false))

/// Parse one side of a rule as an expression, or None for anything invalid.
let private parseSide (text: string) : SynExpr option =
    if String.IsNullOrWhiteSpace text || text.Contains '\n' then
        None
    else
        let sourceText = SourceText.ofString (ParsePrefix + text)

        let parsingOptions =
            { FSharpParsingOptions.Default with
                SourceFiles = [| "Hint.fsx" |] }

        let result =
            // cold path: rules parse once per session and are cached
            parseChecker.Value.ParseFile("Hint.fsx", sourceText, parsingOptions)
            // fsharplint:disable-next-line NoAsyncRunSynchronouslyInLibrary
            |> Async.RunSynchronously

        if result.ParseHadErrors then
            None
        else
            match result.ParseTree with
            | ParsedInput.ImplFile(ParsedImplFileInput(
                contents = [ SynModuleOrNamespace(decls = [ SynModuleDecl.Let(bindings = [ SynBinding(expr = expr) ]) ]) ])) ->
                Some expr
            | _ -> None

/// Parse a `lhs ===> rhs` rule; invalid rules yield None.
let parseRule (rule: string) : Hint option =
    match rule.Split([| "===>" |], StringSplitOptions.None) with
    | [| lhsText; rhsText |] ->
        let lhsText = lhsText.Trim()
        let rhsText = rhsText.Trim()

        match parseSide lhsText, parseSide rhsText with
        | Some lhs, Some rhs ->
            let lhsVars = collectVars lhs
            let rhsVars = collectVars rhs
            let lhsNames = lhsVars |> List.map fst |> Set.ofList

            // right side must not invent variables
            if rhsVars |> List.exists (fun (v, _) -> not (lhsNames.Contains v)) then
                None
            else
                let rhsCounts = rhsVars |> List.countBy fst |> Map.ofList

                let pureOnly =
                    lhsNames
                    |> Set.filter (fun v ->
                        // dropped (None) or duplicated: pure atoms only
                        rhsCounts.TryFind v
                        |> Option.forall (fun n -> n > (lhsVars |> List.filter (fun (n', _) -> n' = v) |> List.length)))

                let spans =
                    rhsVars
                    |> List.map (fun (v, r) -> v, r.StartColumn - ParsePrefix.Length, r.EndColumn - ParsePrefix.Length)
                    |> List.sortByDescending (fun (_, s, _) -> s)

                // `a || b` is App(App(op, a), b) with the inner application
                // marked infix; a metavariable on either side is an operand
                let boolOperandSpans =
                    let acc = Dictionary<int, string>()

                    let rec walk (e: SynExpr) =
                        match e with
                        | SynExpr.Paren(expr = inner) -> walk inner
                        | SynExpr.App(
                            isInfix = false
                            funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs)
                            argExpr = rhs) when op.idText = "op_BooleanAnd" || op.idText = "op_BooleanOr" ->
                            let opText = if op.idText = "op_BooleanAnd" then "&&" else "||"

                            for side in [ lhs; rhs ] do
                                match side with
                                | MetaVar _ -> acc.[side.Range.StartColumn - ParsePrefix.Length] <- opText
                                | _ -> walk side
                        | SynExpr.App(funcExpr = f; argExpr = a) ->
                            walk f
                            walk a
                        | _ -> ()

                    walk rhs
                    acc |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq

                let boolTyped =
                    match lhs with
                    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = a); argExpr = b) when
                        op.idText = "op_Equality" || op.idText = "op_Inequality"
                        ->
                        match stripParens a, stripParens b with
                        | MetaVar v, SynExpr.Const(SynConst.Bool _, _)
                        | SynExpr.Const(SynConst.Bool _, _), MetaVar v -> Set.singleton v
                        | _ -> Set.empty
                    | _ -> Set.empty

                // heads whose rewrite goes wrong on float NaN: ordering
                // operators under a flip, compare collapses, sorts replaced
                // by min/max. Equality (`not (a = b) ===> a <> b`) is
                // NaN-sound and deliberately absent.
                let nanSensitiveHeads =
                    set
                        [ "op_GreaterThan"
                          "op_GreaterThanOrEqual"
                          "op_LessThan"
                          "op_LessThanOrEqual"
                          "compare"
                          "sort"
                          "sortBy"
                          "sortDescending"
                          "sortByDescending" ]

                let notFloat =
                    let acc = HashSet<string>()

                    let addVarsIn e =
                        for v, _ in collectVars e do
                            acc.Add v |> ignore

                    let rec walk e =
                        let rec spine e args =
                            match e with
                            | SynExpr.Paren(expr = inner) -> spine inner args
                            | SynExpr.App(funcExpr = f; argExpr = a) -> spine f (a :: args)
                            | head -> head, args

                        match e with
                        | SynExpr.Paren(expr = inner) -> walk inner
                        | SynExpr.App _ ->
                            let head, args = spine e []

                            let headName =
                                match head with
                                | SynExpr.Ident id -> Some id.idText
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                    Some (List.last ids).idText
                                | _ -> None

                            if headName |> Option.exists nanSensitiveHeads.Contains then
                                args |> List.iter addVarsIn

                            args |> List.iter walk
                        | _ -> ()

                    walk lhs
                    Set.ofSeq acc

                // `f args x` with a plain (non-operator) function head: the
                // final argument is what a pipeline would hand over
                let pipeTail =
                    let rec plainHead (e: SynExpr) =
                        match e with
                        | SynExpr.App(isInfix = false; funcExpr = f) -> plainHead f
                        | SynExpr.Ident id -> not (id.idText.StartsWith "op_")
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                            not ((List.last ids).idText.StartsWith "op_")
                        | _ -> false

                    match rhs with
                    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = MetaVar v) when plainHead f -> Some v
                    | _ -> None

                Some
                    { RuleText = $"{lhsText} ===> {rhsText}"
                      Lhs = lhs
                      RhsText = rhsText
                      RhsVarSpans = spans
                      RhsBoolOperandSpans = boolOperandSpans
                      PureOnlyVars = pureOnly
                      BoolTypedVars = boolTyped
                      NotFloatVars = notFloat
                      HeadKey = headKey lhs
                      PipeTail = pipeTail }
        | _ -> None
    | _ -> None

/// The built-in rule set: FSharpLint-style hints curated for safety. Rules
/// already covered by other analyzers (length = 0, if-bool identities) and
/// rules that change how often a function argument is evaluated are excluded.
let defaultRules =
    [ "not (a = b) ===> a <> b"
      "not (a <> b) ===> a = b"
      "not (a > b) ===> a <= b"
      "not (a >= b) ===> a < b"
      "not (a < b) ===> a >= b"
      "not (a <= b) ===> a > b"
      "not (not x) ===> x"
      "not a && not b ===> not (a || b)"
      "not a || not b ===> not (a && b)"
      "compare x y = 0 ===> x = y"
      "compare x y <> 0 ===> x <> y"
      "compare x y < 0 ===> x < y"
      "compare x y <= 0 ===> x <= y"
      "compare x y > 0 ===> x > y"
      "compare x y >= 0 ===> x >= y"
      "List.head (List.sort x) ===> List.min x"
      "List.head (List.sortBy f x) ===> List.minBy f x"
      "List.map f (List.map g x) ===> List.map (g >> f) x"
      "Array.map f (Array.map g x) ===> Array.map (g >> f) x"
      "Seq.map f (Seq.map g x) ===> Seq.map (g >> f) x"
      "List.rev (List.rev x) ===> x"
      "Array.rev (Array.rev x) ===> x"
      "List.map id x ===> x"
      "Array.map id x ===> x"
      "List.concat (List.map f x) ===> List.collect f x"
      "Array.concat (Array.map f x) ===> Array.collect f x"
      "Seq.concat (Seq.map f x) ===> Seq.collect f x"
      // one-element-of-transformed shapes: same result, no full scan/sort.
      // head-of-filter → find is deliberately absent: the empty-input
      // exception types differ (ArgumentException vs KeyNotFoundException)
      "List.tryHead (List.filter f x) ===> List.tryFind f x"
      "Array.tryHead (Array.filter f x) ===> Array.tryFind f x"
      "Seq.tryHead (Seq.filter f x) ===> Seq.tryFind f x"
      "List.head (List.sort x) ===> List.min x"
      "Array.head (Array.sort x) ===> Array.min x"
      "Seq.head (Seq.sort x) ===> Seq.min x"
      "List.head (List.sortBy f x) ===> List.minBy f x"
      "Array.head (Array.sortBy f x) ===> Array.minBy f x"
      "Seq.head (Seq.sortBy f x) ===> Seq.minBy f x"
      "List.head (List.sortDescending x) ===> List.max x"
      "Array.head (Array.sortDescending x) ===> Array.max x"
      "List.head (List.sortByDescending f x) ===> List.maxBy f x"
      "Array.head (Array.sortByDescending f x) ===> Array.maxBy f x"
      "List.head (List.rev x) ===> List.last x"
      "Array.head (Array.rev x) ===> Array.last x"
      "List.item 0 x ===> List.head x"
      "Seq.item 0 x ===> Seq.head x"
      "Array.item 0 x ===> Array.head x"
      "List.isEmpty (List.filter f x) ===> not (List.exists f x)"
      "Array.isEmpty (Array.filter f x) ===> not (Array.exists f x)"
      "Seq.isEmpty (Seq.filter f x) ===> not (Seq.exists f x)"
      "not (List.isEmpty (List.filter f x)) ===> List.exists f x"
      "not (Array.isEmpty (Array.filter f x)) ===> Array.exists f x"
      "not (Seq.isEmpty (Seq.filter f x)) ===> Seq.exists f x"
      "x = true ===> x"
      "true = a ===> a"
      "false = a ===> not a"
      "a <> true ===> not a"
      "a <> false ===> a"
      "true <> a ===> not a"
      "false <> a ===> a"
      "true && x ===> x"
      "false || x ===> x"
      // `fold (+) 0` -> `sum` is NOT here: the fold adds unchecked and
      // wraps, `sum` adds checked and throws OverflowException (Mibo's
      // Tests.fs; verified in fsi on [| Int32.MaxValue; 1 |])
      "List.sum (List.map f x) ===> List.sumBy f x"
      "Array.sum (Array.map f x) ===> Array.sumBy f x"
      "Seq.sum (Seq.map f x) ===> Seq.sumBy f x"
      "List.average (List.map f x) ===> List.averageBy f x"
      "Array.average (Array.map f x) ===> Array.averageBy f x"
      "Seq.average (Seq.map f x) ===> Seq.averageBy f x"
      "id x ===> x"
      "id >> f ===> f"
      "f >> id ===> f"
      "x = null ===> isNull x"
      "null = x ===> isNull x"
      "x <> null ===> not (isNull x)"
      "null <> x ===> not (isNull x)"
      "Array.append a (Array.append b c) ===> Array.concat [| a; b; c |]" ]

let private defaultHints = lazy (defaultRules |> List.choose parseRule)

/// Parse a list of rule strings into usable hints (invalid ones skipped) and
/// index them together with the defaults by their head key.
let private indexHints (extraRules: string list) : Map<string, Hint list> =
    defaultHints.Value @ (extraRules |> List.choose parseRule)
    |> List.groupBy (fun h -> h.HeadKey)
    |> Map.ofList

let private extraCache =
    System.Collections.Concurrent.ConcurrentDictionary<string list, Map<string, Hint list>>()

/// Operators whose application is boolean by construction.
let private boolOperators =
    set
        [ "op_Equality"
          "op_Inequality"
          "op_LessThan"
          "op_GreaterThan"
          "op_LessThanOrEqual"
          "op_GreaterThanOrEqual"
          "op_BooleanAnd"
          "op_BooleanOr" ]

/// The resolved type of an operand — a name's own type, a call or
/// projection's return type. ValueNone for anything unresolvable (a lambda,
/// a literal, a complex expression).
let private resolvedOperandType
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (e: SynExpr)
    : FSharpType voption =
    let resolve (ident: Ident) =
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                ValueSome(
                    try
                        value.ReturnParameter.Type
                    with _ ->
                        value.FullType
                )
            | :? FSharpField as field -> ValueSome field.FieldType
            | _ -> ValueNone
        | None -> ValueNone

    let lastIdentOf (e: SynExpr) =
        match e with
        | SynExpr.Ident id -> ValueSome id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
        | _ -> ValueNone

    match stripParens e with
    | SynExpr.App(funcExpr = f) -> (lastIdentOf f) |> ValueOption.bind resolve
    | stripped -> (lastIdentOf stripped) |> ValueOption.bind resolve

/// Is the expression provably of type bool — syntactically boolean (a
/// comparison, a logical operator, `not`, a literal), or a name or call
/// whose resolved symbol type is System.Boolean?
let private isProvablyBool (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) : bool =
    match stripParens e with
    | SynExpr.Const(SynConst.Bool _, _) -> true
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op)) when boolOperators.Contains op.idText -> true
    | SynExpr.App(funcExpr = SingleIdent f) when f.idText = "not" -> true
    | _ ->
        match resolvedOperandType check source e with
        | ValueSome t ->
            (try
                let t = OptionModule.stripAbbreviations t
                t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Boolean"
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | ValueNone -> false

/// Is the expression provably NOT a float (nor a collection of or projection
/// to floats)? Non-float literals qualify syntactically; anything else needs
/// its resolved type — including, for a function value like a sortBy key
/// projection, the eventual return type — to name no System.Double/Single.
let private isProvablyNotFloat (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) : bool =
    let floatNames = set [ "System.Double"; "System.Single" ]

    // instance-level stripping: the ENTITY's AbbreviatedType is the open
    // generic (list<int> would strip to FSharpList<'T>, losing the int),
    // and the generic arguments are exactly what this check needs
    let rec stripInstance (t: FSharpType) =
        if t.IsAbbreviation then
            stripInstance t.AbbreviatedType
        else
            t

    let rec notFloatType (t: FSharpType) =
        try
            let t = stripInstance t

            if t.IsFunctionType then
                notFloatType (Seq.last t.GenericArguments)
            elif t.IsGenericParameter then
                false
            elif not t.HasTypeDefinition then
                false
            else
                not (t.TypeDefinition.TryFullName |> Option.exists floatNames.Contains)
                && t.GenericArguments |> Seq.forall notFloatType
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    match stripParens e with
    | SynExpr.Const(constant = c) ->
        match c with
        | SynConst.Double _
        | SynConst.Single _ -> false
        | _ -> true
    | _ -> (resolvedOperandType check source e) |> ValueOption.exists notFloatType

/// Find all expressions matched by a rule. `extraRules` come from the
/// repository configuration; results are cached per distinct rule list.
/// Rules whose firing needs type information (BoolTypedVars) stay silent
/// when `check` is None or the file has type errors.
/// An overloaded .NET method used as a FIRST-CLASS VALUE resolves only
/// because something nearby pins its argument type first:
///
///     logFiles |> Array.sortByDescending File.GetLastWriteTime |> Array.head
///
/// works because the pipe fixes the element type before the method group
/// is checked. Collapsing that to `Array.maxBy File.GetLastWriteTime
/// logFiles` checks the projection while the element type is still
/// unknown, and F# answers "a unique overload for method
/// 'GetLastWriteTime' could not be determined". Found live on prismatic.
///
/// No hint may move such a binding. Adding the annotation that would
/// rescue it is a different, much larger fix, and a rule that is not sure
/// is better left unsaid.
let private isOverloadedMethodGroup (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length > 1 ->
        let last = List.last ids
        let r = last.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ last.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as m ->
                match m.DeclaringEntity with
                | Some entity ->
                    try
                        entity.MembersFunctionsAndValues
                        |> Seq.filter (fun sibling -> sibling.LogicalName = m.LogicalName)
                        |> Seq.truncate 2
                        |> Seq.length > 1
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        false
                | None -> false
            | _ -> false
        | None -> false
    | _ -> false

/// An `=` that might be a NAMED ARGUMENT rather than a comparison.
///
/// F# parses `Timer(period, AutoReset = true)` with the named argument as an
/// ordinary equality — only the type checker ever knows better. A hint that
/// rewrites `x = true` to `x` therefore turns a property assignment into a
/// stray identifier: "The value or constructor 'AutoReset' is not defined",
/// and the constructor is suddenly handed two positional arguments. Found on
/// Fuuga's LspClient.
///
/// Position is the only syntactic signal available here — the engine runs
/// under --parse-only, where no symbol can be resolved — so an equality
/// sitting directly in a call's argument list is left alone. That costs the
/// rewrite of a genuine comparison passed as an argument, `f (x = true)`,
/// which is the cheaper mistake: a fix not offered rather than a file that
/// stops compiling.
let private maybeNamedArgument (path: SyntaxNode list) (e: SynExpr) =
    let isEquality =
        match e with
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SynExpr.Ident op)) -> op.idText = "op_Equality"
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])))) ->
            op.idText = "op_Equality"
        | _ -> false

    let rec insideCallArguments nodes =
        match nodes with
        // the argument list itself, and the tuple of arguments within it
        | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest
        | SyntaxNode.SynExpr(SynExpr.Tuple _) :: rest -> insideCallArguments rest
        | SyntaxNode.SynExpr(SynExpr.New _) :: _ -> true
        | SyntaxNode.SynExpr(SynExpr.App _) :: _ -> true
        | _ -> false

    isEquality && insideCallArguments path

/// The text of a bound expression placed as an operand of `&&` or `||` —
/// where the De Morgan rules put each matched side. An ARGUMENT is
/// bracketed unless atomic; an OPERAND needs brackets only where the
/// grammar or the reader does: an infix expression of lower or equal
/// precedence, a lambda, a match, an if, a tuple. A function application,
/// a method call, a dotted access and a name all stand bare beside `&&`
/// and `||` — the sweep found `not ((List.isEmpty a) && (List.isEmpty b))`
/// and `not ((json.ContainsKey "Case") && (json.ContainsKey "Fields"))`,
/// which read worse than the code they replaced.
let private boolOperandText (source: ISourceText) (op: string) (bound: SynExpr) =
    let inner = stripParens bound
    let text = textOfRange source inner.Range

    let infixOperator (e: SynExpr) =
        match e with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = opExpr)) ->
            Some((textOfRange source opExpr.Range).Trim())
        | _ -> None

    // `&&` binds tighter than `||`: an `&&` operand under `||` stands bare,
    // an `||` operand under `&&` keeps its brackets, and equal precedence
    // keeps them too so the grouping stays visible
    let lowOrEqualPrecedence (opText: string) =
        match opText with
        | "||"
        | "or"
        | ":=" -> true
        | "&&"
        | "&" -> op = "&&"
        | _ -> false

    let bare =
        isSafeInline inner
        && (match inner with
            | SynExpr.Ident _
            | SynExpr.LongIdent _
            | SynExpr.Const _
            | SynExpr.DotGet _
            | SynExpr.DotIndexedGet _
            | SynExpr.TypeApp _
            | SynExpr.Record _
            | SynExpr.AnonRecd _
            | SynExpr.ArrayOrList _
            | SynExpr.ArrayOrListComputed _
            | SynExpr.InterpolatedString _
            | SynExpr.Null _
            | SynExpr.TypeTest _ -> true
            | SynExpr.App _ -> infixOperator inner |> Option.forall (lowOrEqualPrecedence >> not)
            | _ -> false)

    if bare then text else $"({text})"

let find
    (extraRules: string list)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults option)
    : Suggestion list =
    let typedCheck = check |> Option.filter (OptionModule.hasErrors >> not)

    // attribute arguments are constant/property-assignment territory:
    // `[<DllImport(..., SetLastError = true)>]` is not an equality to
    // simplify (the property even RESOLVES to a bool field, so the typed
    // gate alone waves it through — found live on Fuuga), and a rewrite
    // that introduces a call would not compile there at all. No hint
    // fires inside one.
    let attributeArgRanges =
        (AstIndex.ofTree parseTree).Attributes
        |> Array.map (fun (_, a) -> a.ArgExpr.Range)

    let inAttributeArg (r: range) =
        attributeArgRanges |> Array.exists (fun a -> Range.rangeContainsRange a r)

    let index = extraCache.GetOrAdd(extraRules, indexHints)
    let suggestions = ResizeArray<Suggestion>()
    let matchedRanges = HashSet<string>()

    let tryRules (path: SyntaxNode list) (expr: SynExpr) (hints: Hint list) =
        for hint in hints do
            let bindings = Dictionary<string, SynExpr>()

            if unify source bindings hint.Lhs expr then
                let pureOk =
                    hint.PureOnlyVars
                    |> Set.forall (fun v ->
                        match bindings.TryGetValue v with
                        | true, bound -> isPureAtom (stripParens bound)
                        | false, _ -> true)

                // a top-level `=` directly inside application parens is
                // indistinguishable from a NAMED ARGUMENT (`Foo(Flag = true)`);
                // rewriting one would break the call, so equality-headed rules
                // never fire in that position
                let namedArgumentPosition =
                    hint.HeadKey = "op_Equality"
                    && (match path with
                        | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App _) :: _
                        | SyntaxNode.SynExpr(SynExpr.Tuple _) :: SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App _) :: _ ->
                            true
                        | _ -> false)

                let typedVarsOk (vars: Set<string>) (prove: FSharpCheckFileResults -> ISourceText -> SynExpr -> bool) =
                    vars.IsEmpty
                    || (match typedCheck with
                        | Some c ->
                            vars
                            |> Set.forall (fun v ->
                                match bindings.TryGetValue v with
                                | true, bound -> prove c source bound
                                | false, _ -> false)
                        | None -> false)

                let boolTypedOk =
                    typedVarsOk hint.BoolTypedVars isProvablyBool
                    && typedVarsOk hint.NotFloatVars isProvablyNotFloat

                // only the bindings the RHS actually re-places can be moved
                let movesOverloadedMethodGroup =
                    match typedCheck with
                    | Some c ->
                        hint.RhsVarSpans
                        |> List.exists (fun (v, _, _) ->
                            match bindings.TryGetValue v with
                            | true, bound -> isOverloadedMethodGroup c source (stripParens bound)
                            | false, _ -> false)
                    | None -> false

                let rangeKey = expr.Range.ToString()

                if
                    pureOk
                    && boolTypedOk
                    && not movesOverloadedMethodGroup
                    && not namedArgumentPosition
                    && not (inAttributeArg expr.Range)
                    && matchedRanges.Add rangeKey
                then
                    let substitute (spans: (string * int * int) list) (template: string) =
                        spans
                        |> List.fold
                            (fun (text: string) (v, s, e) ->
                                let inserted =
                                    match hint.RhsBoolOperandSpans.TryFind s with
                                    | Some op -> boolOperandText source op bindings.[v]
                                    | None -> argumentText source bindings.[v]

                                text.Substring(0, s) + inserted + text.Substring e)
                            template

                    // the innermost head of a pipeline: the `xs` of
                    // `xs |> M.map f |> M.concat`
                    let rec pipelineHead (e: SynExpr) =
                        match e with
                        | PipeApp(lhs, _) -> pipelineHead lhs
                        | other -> other

                    // matched a PIPELINE, and the right side ends with the
                    // metavariable that pipeline's head binds: render it back
                    // as a pipeline, so `xs` is typed before the lambda is
                    // checked — `xs |> M.collect f`, not `M.collect f xs`
                    let piped =
                        match expr, hint.PipeTail, hint.RhsVarSpans with
                        | PipeApp _, Some tail, (v, s, e) :: earlier when
                            v = tail
                            && hint.RhsText.Substring(e).Trim() = ""
                            && (match bindings.TryGetValue v with
                                | true, bound ->
                                    Range.equals (stripParens bound).Range (stripParens (pipelineHead expr)).Range
                                | _ -> false)
                            ->
                            let stages = substitute earlier (hint.RhsText.Substring(0, s).TrimEnd())
                            Some $"{textOfRange source (pipelineHead expr).Range} |> {stages}"
                        | _ -> None

                    let replacement =
                        match piped with
                        | Some text -> text
                        | None -> substitute hint.RhsVarSpans hint.RhsText

                    let inOperandPosition =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.App(argExpr = arg)) :: _ -> arg.Range = expr.Range
                        | _ -> false

                    let replacement =
                        if inOperandPosition && not (plainOperand.IsMatch replacement) then
                            $"({replacement})"
                        else
                            replacement

                    suggestions.Add
                        { Range = expr.Range
                          OriginalText = textOfRange source expr.Range
                          ReplacementText = replacement
                          Rule = hint.RuleText }

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                // unification sees through parens, so matching the Paren
                // wrapper would duplicate the inner node's match
                | SynExpr.Paren _ -> ()
                | _ ->
                    // rewriting inside a quotation changes the AST the
                    // quotation reifies — never touch quoted code
                    let insideQuotation =
                        path
                        |> List.exists (fun node ->
                            match node with
                            | SyntaxNode.SynExpr(SynExpr.Quote _) -> true
                            | _ -> false)

                    if
                        isSingleLine expr.Range
                        && not insideQuotation
                        && not (maybeNamedArgument path expr)
                    then
                        index.TryFind(headKey expr) |> Option.iter (tryRules path expr)

                        // a pipelined expression can also match rules indexed
                        // under the pipe's right side (pipe normalization)
                        match expr with
                        | PipeApp(_, rhs) -> index.TryFind(headKey rhs) |> Option.iter (tryRules path expr)
                        | _ -> () }

    AstIndex.replay collector parseTree

    // when matches nest (`not (List.isEmpty (List.filter ...))` also contains
    // an isEmpty-filter match), keep only the outermost one
    let all = List.ofSeq suggestions

    all
    |> List.filter (fun s ->
        all
        |> List.exists (fun outer -> outer.Range <> s.Range && Range.rangeContainsRange outer.Range s.Range)
        |> not)
