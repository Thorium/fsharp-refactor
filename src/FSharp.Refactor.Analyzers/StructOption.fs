/// Refactoring (performance): a private function that returns Option
/// allocates a heap cell per call; ValueOption is a struct.
///
///     let private tryParse s =              let private tryParse s =
///         if ok s then Some (conv s)   →        if ok s then ValueSome (conv s)
///         else None                             else ValueNone
///     match tryParse x with                 match tryParse x with
///     | Some v -> ...                       | ValueSome v -> ...
///     | None -> ...                         | ValueNone -> ...
///
/// The definition's result-position constructors and every call site's
/// match patterns are rewritten together in one fix.
///
/// Safety rules:
///   - the function is `private` at module level, so the typed check
///     results enumerate every call site
///   - every result position of the body is a `Some ...`/`None`
///     constructor (typed-gated to FSharp.Core's option) or a recursive
///     self-call; an explicit return-type annotation skips the candidate
///   - every external use is a fully applied call sitting directly as a
///     `match` scrutinee whose clauses use only Some/None/wildcard
///     patterns — a use as a first-class value (List.tryPick f), an
///     argument to an Option-taking API, or a `let`-bound result keeps
///     the option type load-bearing and suppresses the suggestion
module FSharp.Refactor.StructOption

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        FunctionName: string
        /// The definition binding, where the hint anchors.
        DefRange: range
        /// Constructor and pattern edits ((range, original, replacement)).
        Edits: (range * string * string) list
    }

/// A module-level `let private f args = body` candidate.
type private Candidate =
    {
        Ident: Ident
        ParamCount: int
        Body: SynExpr
        DefRange: range
        IsRecursive: bool
    }

let private findCandidates (parseTree: ParsedInput) : Candidate list =
    let candidates = ResizeArray<Candidate>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(_path, decl) =
                match decl with
                | SynModuleDecl.Let(isRecursive = isRec; bindings = bindings) ->
                    for binding in bindings do
                        match binding with
                        | SynBinding(
                            headPat = SynPat.LongIdent(
                                longDotId = SynLongIdent(id = [ ident ])
                                accessibility = Some(SynAccess.Private _)
                                argPats = SynArgPats.Pats args)
                            returnInfo = None
                            expr = body) when not args.IsEmpty ->
                            candidates.Add
                                {
                                    Ident = ident
                                    ParamCount = args.Length
                                    Body = body
                                    DefRange = binding.RangeOfBindingWithRhs
                                    IsRecursive = isRec
                                }
                        | _ -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq candidates

/// All result-position expressions of a body (worklist over the tails).
[<TailCall>]
let rec private resultsLoop (acc: SynExpr list) (pending: SynExpr list) =
    match pending with
    | [] -> acc
    | e :: rest ->
        match e with
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner) -> resultsLoop acc (inner :: rest)
        | LetOrUseE lou when not lou.IsBang -> resultsLoop acc (lou.Body :: rest)
        | SynExpr.Sequential(expr2 = e2) -> resultsLoop acc (e2 :: rest)
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = els) -> resultsLoop acc (t :: (Option.toList els) @ rest)
        | SynExpr.Match(clauses = clauses) ->
            let results = clauses |> List.map (fun (SynMatchClause(resultExpr = r)) -> r)
            resultsLoop acc (results @ rest)
        | other -> resultsLoop (other :: acc) rest

/// The spine head identifier and argument count of an application.
[<TailCall>]
let rec private spineLoop (count: int) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f) -> spineLoop (count + 1) f
    | SynExpr.Ident id -> ValueSome(id, count)
    | _ -> ValueNone

/// Pattern scan of one match clause: Some/None head-ident edits, or None
/// when the clause uses a disqualifying shape.
let private clauseEdits (source: ISourceText) (pat: SynPat) : (range * string * string) list option =
    let edits = ResizeArray()
    let mutable ok = true
    let mutable pending = [ pat ]

    while not pending.IsEmpty && ok do
        match pending with
        | [] -> ()
        | p :: rest ->
            pending <- rest

            match p with
            | SynPat.Wild _ -> ()
            | SynPat.Paren(inner, _) -> pending <- inner :: pending
            | SynPat.Or(lhsPat = l; rhsPat = r) -> pending <- l :: r :: pending
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ caseId ])) when
                caseId.idText = "Some" || caseId.idText = "None"
                ->
                let replacement = if caseId.idText = "Some" then "ValueSome" else "ValueNone"
                edits.Add(caseId.idRange, textOfRange source caseId.idRange, replacement)
            | _ -> ok <- false

    if ok then Some(List.ofSeq edits) else None

/// Find private option-returning functions whose whole use graph can move
/// to ValueOption. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        match findCandidates parseTree with
        | [] -> []
        | candidates ->
            let index = AstIndex.ofTree parseTree

            // match-scrutinee uses: spine-head ident end position →
            // (arg count, clause patterns)
            let matchUses =
                let d =
                    System.Collections.Generic.Dictionary<int * int, int * SynMatchClause list>()

                for _, e in index.Exprs do
                    match e with
                    | SynExpr.Match(expr = scrut; clauses = clauses) ->
                        match spineLoop 0 (stripParens scrut) with
                        | ValueSome(headId, count) when count > 0 ->
                            d.[(headId.idRange.EndLine, headId.idRange.EndColumn)] <- (count, clauses)
                        | _ -> ()
                    | _ -> ()

                d

            candidates
            |> List.choose (fun candidate ->
                // 1. every result position is Some/None (core) or self-call
                let results = resultsLoop [] [ candidate.Body ]

                let defEdits =
                    results
                    |> List.map (fun result ->
                        match stripParens result with
                        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident someId) when
                            someId.idText = "Some"
                            && OptionModule.resolvesToCoreCase
                                check
                                source
                                OptionModule.optionConfig.CoreFullNamePrefix
                                someId
                            ->
                            Some [ someId.idRange, textOfRange source someId.idRange, "ValueSome" ]
                        | SynExpr.Ident noneId when
                            noneId.idText = "None"
                            && OptionModule.resolvesToCoreCase
                                check
                                source
                                OptionModule.optionConfig.CoreFullNamePrefix
                                noneId
                            ->
                            Some [ noneId.idRange, textOfRange source noneId.idRange, "ValueNone" ]
                        | other ->
                            // a recursive tail call returns the same type
                            match spineLoop 0 other with
                            | ValueSome(headId, n) when
                                candidate.IsRecursive
                                && headId.idText = candidate.Ident.idText
                                && n = candidate.ParamCount
                                ->
                                Some []
                            | _ -> None)

                if defEdits |> List.exists Option.isNone then
                    None
                else
                    // 2. every external use is a compatible match scrutinee
                    let r = candidate.Ident.idRange
                    let lineText = source.GetLineString(r.EndLine - 1)

                    match
                        check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ candidate.Ident.idText ])
                    with
                    | None -> None
                    | Some symbolUse ->
                        let uses =
                            check.GetUsesOfSymbolInFile symbolUse.Symbol
                            |> Array.filter (fun u ->
                                not u.IsFromDefinition
                                // self-calls inside the body keep the type
                                && not (Range.rangeContainsRange candidate.DefRange u.Range))

                        let useEdits =
                            uses
                            |> Array.map (fun u ->
                                match matchUses.TryGetValue((u.Range.EndLine, u.Range.EndColumn)) with
                                | true, (count, clauses) when count = candidate.ParamCount ->
                                    let perClause =
                                        clauses |> List.map (fun (SynMatchClause(pat = p)) -> clauseEdits source p)

                                    if perClause |> List.exists Option.isNone then
                                        None
                                    else
                                        Some(perClause |> List.choose id |> List.concat)
                                | _ -> None)

                        if useEdits |> Array.exists Option.isNone || uses.Length = 0 then
                            None
                        else
                            let edits =
                                (defEdits |> List.choose id |> List.concat)
                                @ (useEdits |> Array.choose id |> List.concat)

                            // all-or-nothing: one edit crossing an #if/#else
                            // boundary poisons the whole migration
                            if edits |> List.exists (fun (r, _, _) -> spansDirective source r) then
                                None
                            else
                                Some
                                    {
                                        FunctionName = candidate.Ident.idText
                                        DefRange = candidate.Ident.idRange
                                        Edits = edits
                                    })
