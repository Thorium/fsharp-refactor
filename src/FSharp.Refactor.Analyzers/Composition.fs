/// Refactoring: extract a function composition from a lambda.
///
///     xs |> List.map (fun x -> x |> f |> g)      →  xs |> List.map (f >> g)
///     xs |> List.map (fun x -> g (f x))          →  xs |> List.map (f >> g)
///     xs |> List.map (fun x -> x |> List.map f |> List.filter g)
///                                                →  xs |> List.map (List.map f >> List.filter g)
///
/// Safety rules:
///   - only lambdas that are directly parenthesized, i.e. used as arguments;
///     a `let h = fun x -> ...` binding is left alone (rewriting it to
///     `let h = f >> g` changes generalization under the value restriction)
///   - single unannotated parameter, at least two composed stages
///   - no stage may mention the parameter (checked conservatively on the
///     stage's source text, so shadowing tricks never produce a wrong rewrite)
///   - the lambda and its stages must be single-line, and the line the
///     composition lands on must stay within 100 columns; stages that are
///     not plain applications are parenthesized in the output
///
/// Known caveat: a stage that is a partial application (`x |> h y`) is
/// evaluated per invocation in the lambda but once at construction in the
/// composition; for the overwhelmingly common pure partial applications
/// (`List.map f`) this is unobservable, but a function that runs effects
/// before returning its closure would run them fewer times.
module FSharp.Refactor.Composition

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
        /// Range of the whole lambda, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// The longest line a composition may produce; a longer one, and the
/// multi-line lambda it came from, read better than the rewrite.
[<Literal>]
let private MaxLineLength = 100

/// A stage that can be written bare between `>>`s: an identifier or a plain
/// (non-infix) curried application of one, e.g. `f`, `List.map`, `List.map f`.
[<TailCall>]
let rec private isPlainApplication (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.LongIdent _
    | SynExpr.Const _
    | SynExpr.Paren _
    | SynExpr.DotGet _ -> true
    | SynExpr.App(isInfix = true) -> false
    | SynExpr.TypeApp(expr = inner) -> isPlainApplication inner
    | SynExpr.App(funcExpr = funcExpr) -> isPlainApplication funcExpr
    | _ -> false

[<TailCall>]
let rec private pipeStagesLoop (param: string) (e: SynExpr) (acc: SynExpr list) =
    match e with
    | PipeApp(lhs, rhs) -> pipeStagesLoop param lhs (rhs :: acc)
    | SynExpr.Ident ident when ident.idText = param -> Some acc
    | _ -> None

/// `fun x -> x |> stage1 |> stage2 |> ...` — stages in composition order.
let private pipeStages (param: string) (e: SynExpr) : SynExpr list option = pipeStagesLoop param e []

/// `fun x -> g (f x)` — functions in composition order (innermost first).
[<TailCall>]
let rec private applicationStagesLoop (param: string) (e: SynExpr) (acc: SynExpr list) =
    match stripParens e with
    | SynExpr.Ident ident when ident.idText = param -> Some acc
    // the funcExpr must not itself be an infix application: `1 + x` parses as
    // App(App(op, 1), x), and peeling x off would leave the invalid stage `1 +`
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true)) -> None
    | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = argExpr) ->
        applicationStagesLoop param argExpr (funcExpr :: acc)
    | _ -> None

/// `fun x -> g (f x)` — functions in composition order (innermost first).
let private applicationStages (param: string) (body: SynExpr) : SynExpr list option =
    applicationStagesLoop param body []

let private stageText (source: ISourceText) (stage: SynExpr) =
    let text = textOfRange source stage.Range
    if isPlainApplication stage then text else $"({text})"

/// A BARE operator cannot be spliced in where a function reference goes.
/// Prefix negation is `~-` in the tree but just `-` in the source, so
/// `fun i -> d.AddDays -i` came out as `- >> d.AddDays` — not a wrong
/// composition but not an expression at all, and it took the rest of the
/// file's parse down with it (found on FSharp.Finance.Personal). The
/// parenthesised `(~-) >> d.AddDays` would compile, but a composition
/// spelled out of operators is not the readability this rule exists to buy,
/// so the lambda simply stays.
///
/// Read off the SOURCE rather than the node kind: the same operator arrives
/// as an Ident or a LongIdent depending on how it was written, and the
/// question is only whether the text can stand on its own. An operator the
/// author already wrote in parens (`(+) 1`) reads as a normal application
/// and passes, which is right — that form composes fine.
let private isOperatorStage (source: ISourceText) (stage: SynExpr) =
    let text = (textOfRange source stage.Range).Trim()

    text.Length = 0
    || not (System.Char.IsLetter text[0] || text[0] = '_' || text[0] = '(' || text[0] = '[')

/// Conservative free-variable check: reject the rewrite if the parameter name
/// appears anywhere in the stage's text (over-approximates, which is the safe
/// direction).
let private mentionsParam (param: string) (text: string) =
    Regex.IsMatch(text, sprintf @"\b%s\b" (Regex.Escape param))

/// Does this stage name a .NET MEMBER rather than a function value? A method
/// is not first class in F#. `SwitchCase.switchCase (transformGuard e)` is a
/// CALL, but `transformGuard >> SwitchCase.switchCase` needs the method as a
/// value — and where it is overloaded, or declared with optional parameters
/// (`static member switchCase(?test, ?body, ?loc)`), that is a different
/// thing entirely. On Fable's Fable2Babel the composition typed as `unit`
/// where an `Expression` was wanted and the file stopped compiling. The same
/// lesson FR0012 learned from `Path.GetFileName`, which carries two overloads
/// and cannot be passed by name either.
///
/// Nothing syntactic separates `SwitchCase.switchCase` from `List.map`, so
/// this needs the typed tree — which is why the rule no longer runs under
/// --parse-only.
let private isMemberStage (check: FSharpCheckFileResults) (source: ISourceText) (stage: SynExpr) =
    let rec headIdent (e: SynExpr) =
        match stripParens e with
        | SynExpr.Ident i -> Some i
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | SynExpr.App(funcExpr = f) -> headIdent f
        | SynExpr.TypeApp(expr = inner) -> headIdent inner
        | _ -> None

    match headIdent stage with
    | Some ident ->
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                (try
                    value.IsMember
                 with _ -> // a symbol we cannot interrogate is one we do not compose; fsharpanalyzer: ignore-line FR0055
                     true)
            | _ -> false
        | None -> false
    | None -> false

/// Find all parenthesized lambdas that are pipelines or nested applications of
/// their parameter and can be rewritten as `f >> g` compositions.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let suggestions = ResizeArray<Suggestion>()

        // a lambda handed to an [<InlineIfLambda>] parameter is inlined at
        // the call; a composition in its place is a closure the callee can
        // no longer inline (Mibo's filterA and section, in a library built
        // around zero allocations)
        let rec headOf (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = f) -> headOf f
            | SynExpr.TypeApp(expr = inner) -> headOf inner
            | SynExpr.Ident id -> Some id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | _ -> None

        let calleeTakesInlineLambda (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App(funcExpr = f)) :: _ ->
                match headOf f with
                | Some id ->
                    let r = id.idRange
                    let lineText = source.GetLineString(r.EndLine - 1)

                    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                    | Some symbolUse ->
                        match symbolUse.Symbol with
                        | :? FSharpMemberOrFunctionOrValue as v ->
                            (try
                                v.CurriedParameterGroups
                                |> Seq.concat
                                |> Seq.exists (fun p ->
                                    p.Attributes
                                    |> Seq.exists (fun a -> a.AttributeType.DisplayName = "InlineIfLambdaAttribute"))
                             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                 false)
                        | _ -> false
                    | None -> false
                | None -> false
            | _ -> false

        let collector =
            { new SyntaxCollectorBase() with
                override _.WalkExpr(path, expr) =
                    match expr with
                    | SynExpr.Lambda(parsedData = Some([ SynPat.Named(ident = SynIdent(ident = param)) ], body)) ->
                        // genuine argument position only: a parenthesized lambda
                        // bound by a let (`let h = (fun x -> ...)`) is generalized,
                        // while the composition it would become is an application
                        // and falls under the value restriction
                        let isArgument =
                            match path with
                            | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App _) :: _ -> true
                            | _ -> false

                        if isArgument then
                            let stages =
                                match pipeStages param.idText body with
                                | Some stages -> Some stages
                                | None -> applicationStages param.idText body

                            match stages with
                            | Some stages when
                                List.length stages >= 2
                                // a lambda the author laid out over several
                                // lines was laid out that way to be read;
                                // folded into one composition it came out as
                                // a 170-column line on fantomas's Context.fs
                                && isSingleLine expr.Range
                                && not (calleeTakesInlineLambda path)
                                && stages |> List.forall (fun s -> isSingleLine s.Range)
                                && stages |> List.forall (isOperatorStage source >> not)
                                && stages |> List.forall (isMemberStage check source >> not)
                                && stages
                                   |> List.forall (fun s ->
                                       not (mentionsParam param.idText (textOfRange source s.Range)))
                                ->
                                let replacement = stages |> List.map (stageText source) |> String.concat " >> "

                                // the lambda's line, with the composition in
                                // its place — past 100 columns the rewrite
                                // is no longer the readability it exists for
                                let producedLineLength =
                                    (source.GetLineString(expr.Range.StartLine - 1)).Length
                                    - (expr.Range.EndColumn - expr.Range.StartColumn)
                                    + replacement.Length

                                if producedLineLength <= MaxLineLength then
                                    suggestions.Add
                                        { Range = expr.Range
                                          OriginalText = textOfRange source expr.Range
                                          ReplacementText = replacement }
                            | _ -> ()
                    | _ -> () }

        AstIndex.replay collector parseTree
        List.ofSeq suggestions
