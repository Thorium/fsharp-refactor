/// Refactoring (slide 6, single-file variant): swap a private two-parameter
/// function to data-last order when call sites show the eta-blocking shape.
///
///     let private scale x k = x * k        let private scale k x = x * k
///     xs |> List.map (fun x -> scale x 2)  xs |> List.map (scale 2)
///
/// The lambda `fun x -> f x k` is the tell: the varying value arrives first,
/// so the call cannot be partially applied. Swapping the parameters makes
/// the function pipeline-friendly and collapses those lambdas.
///
/// Safety rules:
///   - the function is `private` at module level with exactly two curried
///     parameters, so the typed check results enumerate every call site
///   - at least one call site is `fun x -> f x k` (otherwise the swap is
///     churn); the captured `k` must be a pure atom, because the rewrite
///     `f k` evaluates it once instead of per call
///   - every other use is a direct application `f a b` where at least one
///     argument is a pure atom (swapping argument evaluation order must be
///     unobservable); anything else — partial application, pipe, use as a
///     value — suppresses the suggestion entirely
///   - the file must have no type errors (call shapes are trusted from the
///     typed uses)
module FSharp.Refactor.ParamOrder

open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The function being reordered, for the diagnostic message.
        FunctionName: string
        /// Range of the definition's parameter list, where the hint anchors.
        DefRange: range
        /// Definition edits followed by one edit per call site
        /// ((range, original, replacement)).
        Edits: (range * string * string) list
    }

/// A module-level `let private f p1 p2 = ...` definition.
type private Candidate =
    { Ident: Ident
      Param1: SynPat
      Param2: SynPat }

/// Parameter shapes we can swap verbatim: `a`, `_`, `(a: int)`.
let private isSimpleParam (p: SynPat) =
    match p with
    | SynPat.Named _
    | SynPat.Wild _
    | SynPat.Paren(pat = SynPat.Typed(pat = SynPat.Named _)) -> true
    | _ -> false

let private findCandidatesIn (scope: Visibility.Scope) (parseTree: ParsedInput) : Candidate list =
    let candidates = ResizeArray<Candidate>()
    let scopeMatches = Visibility.scopeMatches scope

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(path, decl) =
                match decl with
                | SynModuleDecl.Let(bindings = bindings) ->
                    for SynBinding(headPat = headPat) in bindings do
                        match headPat with
                        | SynPat.LongIdent(
                            longDotId = SynLongIdent(id = [ ident ])
                            accessibility = accessibility
                            argPats = SynArgPats.Pats [ p1; p2 ]) when
                            isSimpleParam p1
                            && isSimpleParam p2
                            && isSingleLine p1.Range
                            && isSingleLine p2.Range
                            && scopeMatches path accessibility
                            ->
                            candidates.Add
                                { Ident = ident
                                  Param1 = p1
                                  Param2 = p2 }
                        | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq candidates

let private findCandidates (parseTree: ParsedInput) : Candidate list =
    findCandidatesIn Visibility.Scope.Private parseTree

/// How the function identifier is applied at one position in the file.
type private AppSite =
    /// `f a b` (possibly over-applied further; extra args are untouched).
    | TwoArgs of a1: SynExpr * a2: SynExpr
    /// `f a` with nothing more — a partial application.
    | OneArg

/// The function position of an application: a bare name, or a qualified one
/// (`LibA.scale`, how another file names it). Yields its range, whose end
/// coincides with the end of the typed symbol use.
[<return: Struct>]
let private (|FuncRange|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.LongIdent _ -> ValueSome e.Range
    | _ -> ValueNone

/// Every `f ...` application in the file, keyed by the end position of the
/// function identifier so each typed use resolves with one lookup.
let private collectApplications (parseTree: ParsedInput) =
    let apps = Dictionary<int * int, AppSite>()
    // `fun x -> f x k` sites: lambda range, the function's own range (so the
    // collapsed call keeps whatever qualification it was written with), and
    // the captured argument
    let lambdas = Dictionary<int * int, range * range * SynExpr>()

    let key (r: range) = r.EndLine, r.EndColumn

    let index = AstIndex.ofTree parseTree

    // does any identifier expression inside `r` refer to `name`?
    let mentions (name: string) (r: range) =
        index.Exprs
        |> Array.exists (fun (_, e) ->
            match e with
            | SynExpr.Ident id when id.idText = name -> Range.rangeContainsRange r id.idRange
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when firstId.idText = name ->
                Range.rangeContainsRange r e.Range
            | _ -> false)

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.App(isInfix = false; funcExpr = FuncRange funcRange; argExpr = a1)
                    argExpr = a2) -> apps.[key funcRange] <- TwoArgs(a1, a2)
                | SynExpr.App(isInfix = false; funcExpr = FuncRange funcRange; argExpr = _) ->
                    // the inner node of an `f a b` chain is visited too;
                    // only a lone `f a` is a partial application
                    let partOfChain =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = parentFunc)) :: _ -> parentFunc.Range = expr.Range
                        | _ -> false

                    if not partOfChain then
                        apps.[key funcRange] <- OneArg
                | SynExpr.Lambda(parsedData = Some([ SynPat.Named(ident = SynIdent(ident = x)) ], lambdaBody)) when
                    isSingleLine expr.Range
                    ->
                    match stripParens lambdaBody with
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.App(
                            isInfix = false; funcExpr = FuncRange funcRange; argExpr = SynExpr.Ident dataArg)
                        argExpr = captured) when
                        dataArg.idText = x.idText
                        && isPureAtom captured
                        && not (mentions x.idText captured.Range)
                        ->
                        lambdas.[key funcRange] <- (expr.Range, funcRange, captured)
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    apps, lambdas

/// The swap edits for one direct application `f a b` → `f b a`, or None when
/// the use is not swappable.
let private callEdits (source: ISourceText) (funcEnd: pos) (a1: SynExpr) (a2: SynExpr) =
    if
        isSingleLine a1.Range
        && isSingleLine a2.Range
        && (isPureAtom (stripParens a1) || isPureAtom (stripParens a2))
    then
        let text1 = textOfRange source a1.Range
        let text2 = textOfRange source a2.Range

        // `f(a) b`: the first argument touches the identifier, so the
        // incoming text needs a separating space
        let touching = funcEnd = a1.Range.Start
        let replacement1 = (if touching then " " else "") + text2

        Some [ a1.Range, text1, replacement1; a2.Range, text2, text1 ]
    else
        None

/// One file's application and lambda indexes plus its source, as the shared
/// builder needs them for whichever file a use lives in.
type private Artifacts = Dictionary<int * int, AppSite> * Dictionary<int * int, range * range * SynExpr> * ISourceText

/// The shared tail of both variants: turn a candidate and its uses into a
/// suggestion, reading each use through its own file's artifacts.
///
/// All-or-nothing — one unrewritable use suppresses the whole suggestion,
/// because a call site left in the old order would not compile against the
/// swapped definition. At least one eta-blocking lambda must be present, or
/// the swap is pure churn.
let private buildSuggestion
    (candidate: Candidate)
    (defSource: ISourceText)
    (artifactsFor: string -> Artifacts option)
    (uses: FSharpSymbolUse array)
    : Suggestion option =
    let siteResults =
        uses
        |> Array.map (fun u ->
            match artifactsFor u.Range.FileName with
            | None -> None
            | Some(apps, lambdas, useSource) ->
                let useKey = u.Range.EndLine, u.Range.EndColumn

                match lambdas.TryGetValue useKey with
                | true, (lambdaRange, funcRange, captured) ->
                    // `fun x -> f x k` collapses to `f k`, keeping whatever
                    // qualification the call site wrote (`LibA.f k`)
                    Some(
                        true,
                        [ lambdaRange,
                          textOfRange useSource lambdaRange,
                          textOfRange useSource funcRange + " " + argumentText useSource captured ]
                    )
                | _ ->
                    match apps.TryGetValue useKey with
                    | true, TwoArgs(a1, a2) ->
                        callEdits useSource u.Range.End a1 a2 |> Option.map (fun edits -> false, edits)
                    | _ -> None)

    let lambdaCount =
        siteResults
        |> Array.sumBy (function
            | Some(true, _) -> 1
            | _ -> 0)

    if lambdaCount = 0 || siteResults |> Array.exists Option.isNone then
        None
    else
        let p1Text = textOfRange defSource candidate.Param1.Range
        let p2Text = textOfRange defSource candidate.Param2.Range

        let touching = candidate.Ident.idRange.End = candidate.Param1.Range.Start

        let defEdits =
            [ candidate.Param1.Range, p1Text, (if touching then " " else "") + p2Text
              candidate.Param2.Range, p2Text, p1Text ]

        let edits =
            defEdits @ (siteResults |> Array.toList |> List.collect (Option.get >> snd))

        // a use nested inside another use's argument (`f (fun x -> f x k) b`)
        // cannot be spliced atomically
        if rangesNest (edits |> List.map (fun (r, _, _) -> r)) then
            None
        else
            Some
                { FunctionName = candidate.Ident.idText
                  DefRange = Range.unionRanges candidate.Param1.Range candidate.Param2.Range
                  Edits = edits }

/// Are the two parameters of DIFFERENT concrete types?
///
/// This matters only once the function leaves the project. Inside it, the
/// all-or-nothing rule is exhaustive: every use is rewritten or nothing is.
/// Outside it — a public function, or an internal one reached through
/// InternalsVisibleTo — there are call sites we can neither see nor fix.
/// With different parameter types those call sites stop COMPILING, which is
/// a loud, immediate failure the consumer cannot miss. With interchangeable
/// types (`f (x: string) (y: string)`) they keep compiling and silently
/// pass their arguments the wrong way round, which is exactly the kind of
/// invisible breakage this project refuses to cause.
///
/// Generic parameters count as interchangeable: a caller may well have
/// instantiated both to the same type.
let private hasDistinctParamTypes (symbol: FSharpSymbol) =
    try
        match symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            match value.CurriedParameterGroups |> Seq.concat |> List.ofSeq with
            | [ p1; p2 ] ->
                let t1 = OptionModule.stripAbbreviations p1.Type
                let t2 = OptionModule.stripAbbreviations p2.Type

                not t1.IsGenericParameter
                && not t2.IsGenericParameter
                && t1.Format FSharpDisplayContext.Empty <> t2.Format FSharpDisplayContext.Empty
            | _ -> false
        | _ -> false
    with OptionModule.FcsSymbolFailure ->
        false

/// The PROJECT-WIDE (API-changing) variant: internal/public two-parameter
/// functions defined in `defFile`, with call-site edits wherever the project
/// uses them — each edit's range names its own file. Driven only by the
/// apply tool under --api-changes; any use in a file the caller cannot
/// supply suppresses the suggestion, and the two parameters must have
/// different concrete types (see hasDistinctParamTypes). Public
/// definitions, and internal ones of an assembly with InternalsVisibleTo
/// friends, are reshaped only as far as `outside` says their callers have
/// been read (TupleParams.reshapableScopes).
let findApiChanges
    (defFile: FileContext)
    (check: FSharpCheckFileResults)
    (project: FSharpCheckProjectResults)
    (fileLookup: string -> FileContext option)
    /// Call sites OUTSIDE this project's compilation — a script that
    /// `#load`s the defining file, a sibling project that references the
    /// assembly — and how far the host's reading of them reaches.
    (outside: Visibility.Outside)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        // a definition worth asking about at all, before the host is asked
        // what it read (TupleParams has the same gate, and the reason)
        let anyCandidate =
            [ Visibility.Scope.Assembly; Visibility.Scope.Exported ]
            |> List.exists (fun scope -> not (findCandidatesIn scope defFile.ParseTree).IsEmpty)

        match
            (if anyCandidate then
                 TupleParams.reshapableScopes project outside
                 |> List.collect (fun scope -> findCandidatesIn scope defFile.ParseTree)
             else
                 [])
        with
        | [] -> []
        | candidates ->
            // per-file indexes, built lazily as uses arrive
            let byFile = Dictionary<string, Artifacts option>()

            let artifactsFor (fileName: string) =
                match byFile.TryGetValue fileName with
                | true, cached -> cached
                | false, _ ->
                    let built =
                        fileLookup fileName
                        |> Option.map (fun ctx ->
                            let apps, lambdas = collectApplications ctx.ParseTree
                            apps, lambdas, ctx.Source)

                    byFile.[fileName] <- built
                    built

            candidates
            |> List.choose (fun candidate ->
                let r = candidate.Ident.idRange
                let lineText = defFile.Source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ candidate.Ident.idText ]) with
                | None -> None
                | Some symbolUse when hasDistinctParamTypes symbolUse.Symbol ->
                    let uses =
                        // a `#load`ing script or a sibling project is a real call site
                        // that `project` cannot see. Missing one is the single thing this
                        // rule cannot survive: the definition changes shape and the
                        // caller stops compiling.
                        Array.append (project.GetUsesOfSymbol symbolUse.Symbol) (outside.Uses symbolUse.Symbol)
                        |> Array.filter (fun u -> not u.IsFromDefinition)

                    buildSuggestion candidate defFile.Source artifactsFor uses
                | Some _ -> None)

/// Find private data-first two-parameter functions with eta-blocking lambda
/// call sites, and build the definition + call-site edits. Requires typed
/// check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        match findCandidates parseTree with
        | [] -> []
        | candidates ->

            // collected only when the file actually has candidates
            let apps, lambdas = collectApplications parseTree
            let artifactsFor _ = Some(apps, lambdas, source)

            candidates
            |> List.choose (fun candidate ->
                let r = candidate.Ident.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ candidate.Ident.idText ]) with
                | None -> None
                | Some symbolUse ->
                    // a private binding is named only inside this file, so
                    // its in-file uses are every use there is — no need for
                    // the distinct-parameter-types guard the API variant
                    // needs
                    let uses =
                        check.GetUsesOfSymbolInFile symbolUse.Symbol
                        |> Array.filter (fun u -> not u.IsFromDefinition)

                    buildSuggestion candidate source artifactsFor uses)
