/// Refactoring: rewrite manual Ok/Error matching with Result-module functions.
///
///     match r with | Ok v -> Ok (f v)  | Error e -> Error e     →  r |> Result.map (fun v -> f v)
///     match r with | Ok v -> f v       | Error e -> Error e     →  r |> Result.bind (fun v -> f v)
///     match r with | Ok v -> Ok v      | Error e -> Error (g e) →  r |> Result.mapError (fun e -> g e)
///     match r with | Ok v -> Ok v      | Error e -> Error e     →  r
///     match r with | Ok _ -> true      | Error _ -> false       →  r |> Result.isOk
///     match r with | Ok _ -> false     | Error _ -> true        →  r |> Result.isError
///     match r with | Ok v -> v         | Error _ -> d           →  r |> Result.defaultValue d
///     match r with | Ok v -> f v       | Error _ -> ()          →  r |> Result.iter (fun v -> f v)
///     match r with | Ok v -> g v       | Error e -> d           →  r |> Result.map (fun v -> g v) |> Result.defaultWith (fun e -> d)
///
/// `Result.defaultWith` receives the error, so defaults that mention the
/// error's bound variable are supported. Non-atomic defaults always use
/// `defaultWith` to preserve the original laziness. Requires the Result
/// module functions from FSharp.Core 7+.
///
/// Clause order may be reversed. Safety rules mirror the Option analyzer:
/// two guard-free clauses, single-line parts, Ok/Error must resolve to
/// FSharp.Core's Result cases, and the file must have no type errors.
///
/// Readability rules: the rewrite is a single line, and it is withheld
/// when that line would pass 100 columns, when an arm is not a single
/// simple expression (a tuple, a lambda, a pipeline, applications nested
/// in applications), or when the map lambda would return unit —
/// `Result.map (fun _ -> ())` is never an improvement. Fantomas's Daemon
/// had a readable three-line match turned into a 190-character line
/// carrying two closures.
module FSharp.Refactor.ResultModule

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole match expression, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The module function used, e.g. "Result.map", or "" for identity.
        Target: string
    }

/// `Ok v` / `Error e` as a pattern: the case ident and the bound variable.
let private casePat (caseName: string) (p: SynPat) =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ caseIdent ]); argPats = SynArgPats.Pats [ arg ]) when
        caseIdent.idText = caseName
        ->
        boundVar arg |> Option.map (fun v -> caseIdent, v)
    | _ -> None

/// `Ok <e>` / `Error <e>` as an expression.
let private caseApp (caseName: string) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.Ident caseIdent; argExpr = arg) when caseIdent.idText = caseName -> Some arg
    | _ -> None

/// The error clause rewraps its own bound variable: `Error e -> Error e`.
let private rewrapsError (errorVar: string option) (errorBody: SynExpr) =
    match caseApp "Error" errorBody, errorVar with
    | Some(IdentName e), Some v -> e = v
    | _ -> false

/// `defaultValue d` for pure atoms with an unused error, else
/// `defaultWith (fun e -> d)` (the thunk receives the error).
let private defaultCall (source: ISourceText) (errorVar: string option) (defaultBody: SynExpr) =
    let mentionsError =
        match errorVar with
        | Some v ->
            System.Text.RegularExpressions.Regex.IsMatch(
                textOfRange source defaultBody.Range,
                @"\b" + System.Text.RegularExpressions.Regex.Escape v + @"\b"
            )
        | None -> false

    if isPureAtom defaultBody && not mentionsError then
        sprintf "Result.defaultValue %s" (atomicText source defaultBody), "Result.defaultValue"
    else
        let param = if mentionsError then lambdaParam errorVar else "_"

        sprintf "Result.defaultWith (fun %s -> %s)" param (textOfRange source (stripParens defaultBody).Range),
        "Result.defaultWith"

/// Decide the rewrite for an Ok/Error match, given the normalized parts.
let private rewrite
    (source: ISourceText)
    (scrutinee: SynExpr)
    (okVar: string option)
    (okBody: SynExpr)
    (errorVar: string option)
    (errorBody: SynExpr)
    : (string * string) option =
    let pipeSource = atomicText source scrutinee

    let (|OkApp|_|) = caseApp "Ok"
    let (|ErrorApp|_|) = caseApp "Error"

    match okBody, errorBody with
    // ... | Error e -> Error e
    | OkApp(IdentName v), _ when Some v = okVar && rewrapsError errorVar errorBody ->
        // Ok v -> Ok v | Error e -> Error e: the match is the scrutinee itself
        Some(textOfRange source scrutinee.Range, "")
    | OkApp inner, _ when rewrapsError errorVar errorBody ->
        let body = textOfRange source (stripParens inner).Range
        Some(sprintf "%s |> Result.map (fun %s -> %s)" pipeSource (lambdaParam okVar) body, "Result.map")
    | body, _ when rewrapsError errorVar errorBody ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> Result.bind (fun %s -> %s)" pipeSource (lambdaParam okVar) bodyText, "Result.bind")
    // Ok v -> Ok v | Error e -> Error (g e)
    | OkApp(IdentName v), ErrorApp errorInner when Some v = okVar ->
        let body = textOfRange source (stripParens errorInner).Range
        Some(sprintf "%s |> Result.mapError (fun %s -> %s)" pipeSource (lambdaParam errorVar) body, "Result.mapError")
    | BoolConst true, BoolConst false -> Some($"%s{pipeSource} |> Result.isOk", "Result.isOk")
    | BoolConst false, BoolConst true -> Some($"%s{pipeSource} |> Result.isError", "Result.isError")
    | IdentName v, defaultBody when Some v = okVar ->
        let call, target = defaultCall source errorVar defaultBody
        Some($"%s{pipeSource} |> %s{call}", target)
    | body, UnitConst ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> Result.iter (fun %s -> %s)" pipeSource (lambdaParam okVar) bodyText, "Result.iter")
    // the map+default combo, but not when a branch itself constructs a case:
    // the rewrite would still typecheck, yet the original match reads better
    | (OkApp _ | ErrorApp _), _
    | _, (OkApp _ | ErrorApp _) -> None
    | body, defaultBody ->
        let bodyText = textOfRange source (stripParens body).Range
        let call, target = defaultCall source errorVar defaultBody

        Some(
            sprintf "%s |> Result.map (fun %s -> %s) |> %s" pipeSource (lambdaParam okVar) bodyText call,
            $"Result.map + {target}"
        )

/// The longest line a rewrite may produce: past this the one-liner reads
/// worse than the match it replaces.
[<Literal>]
let private MaxLineLength = 100

/// An arm body that stays readable once it moves into a lambda: a value,
/// a field, a call with plain arguments, an operator expression over
/// those. A tuple, a lambda, a pipeline, or an application nested inside
/// an application's argument read worse squeezed into
/// `Result.map (fun v -> ...)` than they did on their own match line.
let rec private isSimpleArm (depth: int) (e: SynExpr) : bool =
    match e with
    | SynExpr.Paren(expr = inner) -> isSimpleArm depth inner
    | SynExpr.Ident _
    | SynExpr.LongIdent _
    | SynExpr.Const _
    | SynExpr.Null _
    | SynExpr.DotGet _
    | SynExpr.DotIndexedGet _
    | SynExpr.InterpolatedString _
    | SynExpr.ArrayOrList _
    | SynExpr.Record _
    | SynExpr.TypeApp _ -> true
    | PipeApp _ -> false
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) ->
        not (op.idText.StartsWith "op_Pipe" || op.idText.StartsWith "op_Compose")
        && isSimpleArm depth lhs
        && isSimpleArm depth rhs
    | SynExpr.App(isInfix = false) ->
        let rec spine (e: SynExpr) (args: SynExpr list) =
            match e with
            | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) -> spine f (a :: args)
            | head -> head, args

        let head, args = spine e []

        let headOk =
            match head with
            | SynExpr.Ident _
            | SynExpr.LongIdent _
            | SynExpr.DotGet _
            | SynExpr.TypeApp _ -> true
            | _ -> false

        // `f (g x)` is fine; `f (g (h x))` is a chain the match laid out better
        depth < 2
        && headOk
        && args
           |> List.forall (fun a ->
               match a with
               | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> es |> List.forall (isSimpleArm (depth + 1))
               | _ -> isSimpleArm (depth + 1) a)
    | _ -> false

/// The line the match sits on, once the rewrite replaces it: what precedes
/// the match on its first line, the replacement, what follows it on its
/// last line.
let private producedLineLength (source: ISourceText) (m: range) (replacement: string) =
    let firstLine = source.GetLineString(m.StartLine - 1)
    let lastLine = source.GetLineString(m.EndLine - 1)
    let prefix = firstLine.Substring(0, min m.StartColumn firstLine.Length)

    let suffix =
        if m.EndColumn <= lastLine.Length then
            lastLine.Substring m.EndColumn
        else
            ""

    prefix.Length + replacement.Length + suffix.Length

/// Would this body, as the map lambda's result, be unit? Syntactically
/// `()`, or a call whose function the typed tree says returns unit —
/// `log FantomasLogLevel.Error $"..."` on fantomas's Daemon. A partial
/// application reads as unit-returning too, which withholds a rewrite
/// that would have been legal; the safe direction.
let private returnsUnit (check: FSharpCheckFileResults) (source: ISourceText) (body: SynExpr) =
    let rec isUnit (t: FSharpType) =
        try
            if t.IsAbbreviation then
                isUnit t.AbbreviatedType
            else
                t.HasTypeDefinition
                && (t.TypeDefinition.TryFullName
                    |> Option.exists (fun n -> n = "Microsoft.FSharp.Core.Unit" || n = "Microsoft.FSharp.Core.unit"))
        with _ -> // fsharpanalyzer: ignore-line FR0055
            false

    let rec headIdent (e: SynExpr) =
        match e with
        | SynExpr.Paren(expr = inner)
        | SynExpr.TypeApp(expr = inner) -> headIdent inner
        | SynExpr.App(isInfix = false; funcExpr = f) -> headIdent f
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    match stripParens body with
    | UnitConst -> true
    | SynExpr.App _ as app ->
        match headIdent app with
        | Some id ->
            (try
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as v when v.IsFunction || v.IsMember ->
                        isUnit v.ReturnParameter.Type
                    | _ -> false
                | None -> false
             with _ -> // fsharpanalyzer: ignore-line FR0055
                 false)
        | None -> false
    | _ -> false

/// A candidate found syntactically; the case idents still need resolving
/// against the typed results before the suggestion is emitted.
type private Candidate =
    {
        MatchRange: range
        OkIdent: Ident
        ErrorIdent: Ident
        Replacement: string
        Target: string
        /// The body the rewrite's `Result.map` lambda would return, when it
        /// has one: gated on the typed tree so a unit-typed map never fires.
        MapBody: SynExpr option
    }

let private findCandidates (parseTree: ParsedInput) (source: ISourceText) : Candidate list =
    let candidates = ResizeArray<Candidate>()

    let (|OkPat|_|) = casePat "Ok"
    let (|ErrorPat|_|) = casePat "Error"

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.Match(expr = scrutinee; clauses = clauses; range = m) ->
                    // see OptionModule: replacements must be parenthesized when
                    // the match sat unparenthesized as an infix operand
                    let inOperandPosition =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.App(argExpr = arg)) :: _ -> arg.Range = m
                        | _ -> false

                    let normalized =
                        match clauses |> List.map simpleClause with
                        | [ Some(OkPat(okIdent, okVar), okBody); Some(ErrorPat(errorIdent, errorVar), errorBody) ]
                        | [ Some(ErrorPat(errorIdent, errorVar), errorBody); Some(OkPat(okIdent, okVar), okBody) ] ->
                            Some(okIdent, okVar, okBody, errorIdent, errorVar, errorBody)
                        | _ -> None

                    match normalized with
                    | Some(okIdent, okVar, okBody, errorIdent, errorVar, errorBody) when
                        isSingleLine scrutinee.Range
                        && isSingleLine okBody.Range
                        && isSingleLine errorBody.Range
                        && isPlainBody okBody
                        && isPlainBody errorBody
                        && isSimpleArm 0 okBody
                        && isSimpleArm 0 errorBody
                        && not (OptionModule.capturesMutableLocal (AstIndex.ofTree parseTree) okBody.Range)
                        && not (OptionModule.capturesMutableLocal (AstIndex.ofTree parseTree) errorBody.Range)
                        && not (OptionModule.implicitYieldPosition path)
                        ->
                        match rewrite source scrutinee okVar okBody errorVar errorBody with
                        | Some(replacement, target) ->
                            let replacement =
                                if
                                    inOperandPosition
                                    && not (System.Text.RegularExpressions.Regex.IsMatch(replacement, @"^[\w.]+$"))
                                then
                                    $"({replacement})"
                                else
                                    replacement

                            // what the `Result.map` lambda returns: the
                            // unwrapped `Ok` payload, or the whole ok arm
                            // in the map + default combination
                            let mapBody =
                                if target = "Result.map" then caseApp "Ok" okBody
                                elif target.StartsWith "Result.map + " then Some okBody
                                else None

                            if producedLineLength source m replacement <= MaxLineLength then
                                candidates.Add
                                    { MatchRange = m
                                      OkIdent = okIdent
                                      ErrorIdent = errorIdent
                                      Replacement = replacement
                                      Target = target
                                      MapBody = mapBody }
                        | None -> ()
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq candidates

/// Find Ok/Error matches that can be rewritten with Result-module functions.
/// Requires typed check results; emits nothing when the file has type errors.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        findCandidates parseTree source
        |> List.filter (fun c ->
            not (spansDirective source c.MatchRange)
            && OptionModule.resolvesToCoreCase check source "Microsoft.FSharp.Core.Result<" c.OkIdent
            && OptionModule.resolvesToCoreCase check source "Microsoft.FSharp.Core.Result<" c.ErrorIdent
            && not (c.MapBody |> Option.exists (returnsUnit check source)))
        |> List.map (fun c ->
            { Range = c.MatchRange
              OriginalText = textOfRange source c.MatchRange
              ReplacementText = c.Replacement
              Target = c.Target })
