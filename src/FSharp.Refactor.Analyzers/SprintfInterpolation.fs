/// Refactoring: a fully applied sprintf is a typed interpolated string.
///
///     sprintf "asdf %s: %d" name count   →  $"asdf %s{name}: %d{count}"
///
/// The interpolation keeps every format specifier exactly as written, so
/// the output goes through the same printf formatting and is
/// byte-identical — the gain is reading the arguments in place.
///
/// Safety rules:
///   - the format is a regular single-line string literal with no `{`/`}`
///     (they would need escaping) and only value specifiers — `%a`/`%t`
///     (function-taking) and `*` widths leave the call alone
///   - sprintf is fully applied: one simple argument (identifier, dotted
///     path, or non-string constant) per specifier; partial applications
///     never match because their argument count differs
module FSharp.Refactor.SprintfInterpolation

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// A `%` specifier in a printf format: flags, width, precision, type.
let private specifierRegex =
    Regex(@"%[-+0# ]*[0-9]*(\.[0-9]+)?[a-zA-Z*]", RegexOptions.Compiled)

/// Value-producing specifier type characters we can splice; `%a`/`%t`
/// take function arguments and `*` widths take an extra argument.
let private isValueSpecifier (c: char) = "sdiuxXobcfFeEgGMAO".Contains c

/// The sprintf application spine: the sprintf identifier and the
/// argument list.
[<TailCall>]
let rec private collectSpine (args: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) -> collectSpine (a :: args) f
    | SingleIdent id when id.idText = "sprintf" -> ValueSome(id, args)
    // the qualified spelling resolves to the same function
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ printfId; id ])) when
        printfId.idText = "Printf" && id.idText = "sprintf"
        ->
        ValueSome(id, args)
    | _ -> ValueNone

/// A simple argument that reads well inside `{...}` and cannot contain
/// braces or nested quotes.
let private simpleArg (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.LongIdent _ -> true
    | SynExpr.Const(SynConst.String _, _) -> false
    | SynExpr.Const _ -> true
    | _ -> false

/// The head of an application spine: `f` in `f a (b) c`, the operator in
/// `a + (b)`. A type application (`x.M<int> (b)`) has no plain head.
[<TailCall>]
let rec private spineHead (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = f) -> spineHead f
    | SynExpr.TypeApp _ -> ValueNone
    | other -> ValueSome other

/// The head names a curried function, a union case or an active pattern —
/// something whose argument may stand bare — rather than a method,
/// constructor or property, whose parenthesised argument is its call.
let private appliesPlainFunction (check: FSharpCheckFileResults) (source: ISourceText) (app: SynExpr) =
    let idents =
        match spineHead app with
        | ValueSome(SynExpr.Ident id) -> [ id ]
        | ValueSome(SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) -> ids
        | _ -> []

    match List.tryLast idents with
    | None -> false
    | Some last ->
        let r = last.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match
            check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, idents |> List.map (fun i -> i.idText))
        with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                try
                    not (value.IsMember || value.IsConstructor)
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    false
            | :? FSharpUnionCase
            | :? FSharpActivePatternCase -> true
            | _ -> false
        | None -> false

/// Whether the parentheses around the application only wrap it, so the
/// interpolated string can stand bare in their place: `Expect.throws f
/// (sprintf "…" x)` reads `Expect.throws f $"…"`. They stay where they may
/// be doing more — a method's or constructor's argument list (`c.M(sprintf
/// …)` is a call, `c.M $"…"` a different shape), a receiver
/// (`(…).Length`), an indexer — and under any parent not known to take the
/// atom as it is.
let private parenOnlyWraps (check: FSharpCheckFileResults) (source: ISourceText) (parent: SyntaxNode) (paren: range) =
    match parent with
    | SyntaxNode.SynBinding _
    | SyntaxNode.SynMatchClause _ -> true
    | SyntaxNode.SynExpr e ->
        match e with
        | SynExpr.App(flag = ExprAtomicFlag.Atomic) -> false
        | SynExpr.App(isInfix = false; argExpr = arg) when Range.equals arg.Range paren ->
            appliesPlainFunction check source e
        | SynExpr.App(isInfix = true; argExpr = arg) when Range.equals arg.Range paren ->
            appliesPlainFunction check source e
        | SynExpr.Paren _
        | SynExpr.Tuple _
        | SynExpr.ArrayOrList _
        | SynExpr.ArrayOrListComputed _
        | SynExpr.Record _
        | SynExpr.AnonRecd _
        | SynExpr.Sequential _
        | SynExpr.IfThenElse _
        | SynExpr.Match _
        | SynExpr.MatchBang _
        | SynExpr.TryWith _
        | SynExpr.TryFinally _
        | SynExpr.Lambda _
        | SynExpr.LetOrUse _
        | SynExpr.YieldOrReturn _
        | SynExpr.YieldOrReturnFrom _
        | SynExpr.Typed _
        | SynExpr.Upcast _
        | SynExpr.Downcast _
        | SynExpr.InferredUpcast _
        | SynExpr.InferredDowncast _
        | SynExpr.Lazy _
        | SynExpr.Assert _
        | SynExpr.Do _
        | SynExpr.DoBang _
        | SynExpr.While _
        | SynExpr.For _
        | SynExpr.ForEach _
        | SynExpr.ComputationExpr _
        | SynExpr.LongIdentSet _ -> true
        | _ -> false
    | _ -> false

/// Find fully applied simple sprintf calls. Requires typed check results
/// (`sprintf` itself must resolve to FSharp.Core, not a shadow).
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [
        for path, expr in index.Exprs do
            match expr with
            | SynExpr.App(isInfix = false) when isSingleLine expr.Range ->
                match collectSpine [] expr with
                | ValueSome(sprintfId,
                            (SynExpr.Const(SynConst.String(_, SynStringKind.Regular, _), _) as fmtExpr :: args)) when
                    not args.IsEmpty
                    && args |> List.forall simpleArg
                    && OptionModule.resolvesToCoreOperator check source sprintfId
                    ->
                    let fmtSource = textOfRange source fmtExpr.Range
                    let fmt = fmtSource.Substring(1, fmtSource.Length - 2)

                    let specifiers =
                        specifierRegex.Matches fmt
                        |> Seq.filter (fun m ->
                            // an even run of % before the match means the
                            // leading % is itself escaped (%%)
                            let mutable run = 0
                            let mutable i = m.Index - 1

                            while i >= 0 && fmt.[i] = '%' do
                                run <- run + 1
                                i <- i - 1

                            run % 2 = 0)
                        |> List.ofSeq

                    let spliceable =
                        not (fmt.Contains '{')
                        && not (fmt.Contains '}')
                        && specifiers.Length = args.Length
                        && specifiers
                           |> List.forall (fun m -> isValueSpecifier fmt.[m.Index + m.Length - 1])

                    if spliceable then
                        let builder = System.Text.StringBuilder()
                        let mutable cursor = 0

                        for m, arg in List.zip specifiers args do
                            builder
                                .Append(fmt.Substring(cursor, m.Index - cursor))
                                .Append(m.Value)
                                .Append('{')
                                .Append(textOfRange source arg.Range)
                                .Append
                                '}'
                            |> ignore

                            cursor <- m.Index + m.Length

                        builder.Append(fmt.Substring cursor) |> ignore

                        // parentheses that only wrapped the application go
                        // with it (farmer's `(sprintf "Should have thrown for
                        // %d" days)` was left as `($"…")`)
                        let editRange =
                            match path with
                            | SyntaxNode.SynExpr(SynExpr.Paren(expr = inner; range = parenRange)) :: parent :: _ when
                                Range.equals inner.Range expr.Range
                                && isSingleLine parenRange
                                && parenOnlyWraps check source parent parenRange
                                ->
                                parenRange
                            | _ -> expr.Range

                        // an operator touching the paren would swallow the
                        // `$`: SQLProvider's `~~(sprintf "..." x)` became
                        // `~~$"..."`, and `~~$` is an operator name, and an
                        // invalid one. A space keeps the two apart
                        let touchesOperator =
                            editRange.StartColumn > 0
                            && (let line = source.GetLineString(editRange.StartLine - 1)
                                "!%&*+-./<=>?@^|~:$".Contains line.[editRange.StartColumn - 1])

                        {
                            Range = editRange
                            OriginalText = textOfRange source editRange
                            ReplacementText = (if touchesOperator then " $\"" else "$\"") + builder.ToString() + "\""
                        }
                | _ -> ()
            | _ -> ()
    ]
