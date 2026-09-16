/// Refactoring: complete an incomplete DU match by adding the missing
/// cases as explicit arms (FR0110, fix).
///
///     match color with            match color with
///     | Red -> "r"           →    | Red -> "r"
///     | Green -> "g"              | Green -> "g"
///                                 | Blue -> raise (System.NotImplementedException())
///
/// The dual of FR0072: that rule expands a wildcard hiding one or two real
/// cases, this one closes a match that has no wildcard at all — the FS0025
/// warning shape. The added arm raises, FR0100-style, so the gap reports
/// itself instead of silently returning something plausible.
///
/// Safety rules:
///   - every clause must cover its cases TOTALLY (bare case names, fields
///     as wildcards, or-patterns fine); any literal, guard-only case use,
///     variable or partial pattern makes coverage unknowable — skipped
///   - clauses carrying `when` guards do not count as covering their case
///     (the guard may reject), but their presence is fine
///   - the scrutinee's type must resolve to an F# union, all covered names
///     must belong to it, and at most three cases may be missing — past
///     that, a wildcard arm was probably the intent
///   - multi-line matches only: each clause starts its own line, and the
///     new arms adopt the last clause's `|` column
///
/// This module also hosts FR0117 (fix): ADJACENT arms with identical
/// single-line bodies and no guards fold into one or-pattern arm —
///
///     | 1 -> true                 | 1
///     | 2 -> true            →    | 2
///     | 3 -> true                 | 3 -> true
///     | _ -> false                | _ -> false
///
/// Match order is semantics in F#: only a CONTIGUOUS run merges, in
/// place, so the same patterns are tried in the same order. Patterns
/// must provably bind nothing (or-patterns demand identical bindings,
/// and a lowercase lone identifier is conventionally a binder).
module FSharp.Refactor.MissingCases

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Zero-width range at the end of the last clause — the arms are
        /// INSERTED, nothing is replaced.
        Range: range
        InsertText: string
        MissingCases: string list
    }

/// A pattern that always matches whatever it is applied to.
[<TailCall>]
let rec private isTotalLoop (pending: SynPat list) : bool =
    match pending with
    | [] -> true
    | p :: rest ->
        match p with
        | SynPat.Wild _
        | SynPat.Named _ -> isTotalLoop rest
        | SynPat.Paren(inner, _)
        | SynPat.Typed(pat = inner)
        | SynPat.Attrib(pat = inner) -> isTotalLoop (inner :: rest)
        | SynPat.Tuple(elementPats = ps) -> isTotalLoop (ps @ rest)
        | _ -> false

/// The case idents a clause pattern covers totally, or None when the
/// pattern is anything but plain total case coverage.
[<TailCall>]
let rec private coveredLoop (acc: Ident list list) (pending: SynPat list) : Ident list list option =
    match pending with
    | [] -> Some(List.rev acc)
    | p :: rest ->
        match p with
        | SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats args) when
            not ids.IsEmpty && isTotalLoop args
            ->
            coveredLoop (ids :: acc) rest
        | SynPat.Paren(inner, _) -> coveredLoop acc (inner :: rest)
        | SynPat.Or(lhsPat = l; rhsPat = r) -> coveredLoop acc (l :: r :: rest)
        | _ -> None

let private unionCasesOf (check: FSharpCheckFileResults) (source: ISourceText) (caseIdent: Ident) =
    let r = caseIdent.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ caseIdent.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpUnionCase as unionCase ->
            try
                let t = OptionModule.stripAbbreviations unionCase.ReturnType

                if t.HasTypeDefinition && t.TypeDefinition.IsFSharpUnion then
                    Some [ for c in t.TypeDefinition.UnionCases -> c.Name, c.Fields.Count > 0 ]
                else
                    None
            with OptionModule.FcsSymbolFailure ->
                None
        | _ -> None
    | None -> None

/// Find incomplete DU matches with no catch-all. Requires typed check
/// results for the union lookup.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.Match(clauses = clauses)
                | SynExpr.MatchBang(clauses = clauses)
                | SynExpr.MatchLambda(matchClauses = clauses) when not clauses.IsEmpty ->
                    // any total (wildcard/variable) clause completes the match
                    let anyCatchAll =
                        clauses
                        |> List.exists (fun (SynMatchClause(pat = p)) ->
                            match p with
                            | SynPat.Wild _
                            | SynPat.Named _ -> true
                            | _ -> false)

                    let unguarded =
                        clauses |> List.filter (fun (SynMatchClause(whenExpr = g)) -> g.IsNone)

                    let covered =
                        unguarded |> List.map (fun (SynMatchClause(pat = p)) -> coveredLoop [] [ p ])

                    // guarded clauses must still be PLAIN case patterns, or
                    // coverage of the whole match is beyond this rule
                    let guardedParseable =
                        clauses
                        |> List.forall (fun (SynMatchClause(pat = p; whenExpr = g)) ->
                            g.IsNone || (coveredLoop [] [ p ]) |> Option.isSome)

                    if
                        not anyCatchAll
                        && guardedParseable
                        && not covered.IsEmpty
                        && covered |> List.forall Option.isSome
                    then
                        let coveredIdents = covered |> List.choose id |> List.concat

                        match coveredIdents with
                        | first :: _ ->
                            match unionCasesOf check source (List.last first) with
                            | Some allCases ->
                                let coveredNames =
                                    coveredIdents |> List.map (fun ids -> (List.last ids).idText) |> Set.ofList

                                let missing =
                                    allCases |> List.filter (fun (name, _) -> not (coveredNames.Contains name))

                                let qualifier =
                                    first
                                    |> List.rev
                                    |> List.tail
                                    |> List.rev
                                    |> List.map (fun i -> i.idText + ".")
                                    |> String.concat ""

                                let lastClause = List.last clauses
                                let lastLine = source.GetLineString(lastClause.Range.EndLine - 1)
                                let firstLine = source.GetLineString(lastClause.Range.StartLine - 1)
                                let barColumn = firstLine.IndexOf '|'

                                // every covered name must belong to THIS union
                                // (same-named cases of another DU would slip
                                // through the name-set comparison otherwise)
                                if
                                    coveredNames
                                    |> Set.forall (fun n -> allCases |> List.exists (fun (c, _) -> c = n))
                                    && not missing.IsEmpty
                                    && missing.Length <= 3
                                    // multi-line matches only, clause starting
                                    // its line at a findable bar
                                    && barColumn >= 0
                                    && firstLine.Substring(0, barColumn).Trim() = ""
                                    // nothing trails the last clause on its
                                    // final line
                                    && lastLine.Length <= lastClause.Range.EndColumn
                                then
                                    let indent = String.replicate barColumn " "

                                    let insertText =
                                        missing
                                        |> List.map (fun (name, hasFields) ->
                                            let pattern =
                                                if hasFields then
                                                    $"{qualifier}{name} _"
                                                else
                                                    $"{qualifier}{name}"

                                            let prefix = if opensSystemNamespace source then "" else "System."
                                            $"\n{indent}| {pattern} -> raise ({prefix}NotImplementedException())")
                                        |> String.concat ""

                                    let insertAt =
                                        Range.mkRange
                                            lastClause.Range.FileName
                                            lastClause.Range.End
                                            lastClause.Range.End

                                    {
                                        Range = insertAt
                                        InsertText = insertText
                                        MissingCases = missing |> List.map fst
                                    }
                            | None -> ()
                        | [] -> ()
                | _ -> ()
        ]

// ---- FR0117: adjacent same-result arms fold into one or-pattern ----

type ArmMerge =
    {
        /// From the first merged clause's `|` to the last clause's end.
        ReplaceRange: range
        NewText: string
        /// How many arms folded.
        Count: int
    }

/// A pattern that provably binds nothing — or-patterns demand identical
/// bindings across alternatives, so only these may merge. A lone
/// identifier is a union case only by convention (uppercase); a
/// lowercase one is treated as a binder and refused.
let rec private bindsNothing (p: SynPat) =
    match p with
    | SynPat.Const _ -> true
    | SynPat.Paren(pat = inner) -> bindsNothing inner
    | SynPat.Or(lhsPat = l; rhsPat = r) -> bindsNothing l && bindsNothing r
    | SynPat.Tuple(elementPats = els) -> els |> List.forall bindsNothing
    | SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats args) when
        args |> List.forall bindsNothing
        ->
        match ids with
        | [ single ] -> single.idText.Length > 0 && System.Char.IsUpper single.idText.[0]
        | _ -> not ids.IsEmpty
    | _ -> false

/// Adjacent guard-free arms whose single-line bodies read identically:
/// each contiguous run becomes one or-pattern arm, order untouched.
let findMergeableArms (parseTree: ParsedInput) (source: ISourceText) : ArmMerge list =
    let index = AstIndex.ofTree parseTree

    // one traversal for the file; an arm's comments are read out of this
    let allComments = commentsWithText parseTree source

    let clauseView (SynMatchClause(pat = p; whenExpr = w; resultExpr = r; trivia = t) as clause) =
        let barOnOwnLine =
            match t.BarRange with
            | Some bar ->
                bar.StartColumn = 0
                || (source.GetLineString(bar.StartLine - 1)).Substring(0, bar.StartColumn).Trim() = ""
            | None -> false

        let qualifies = w.IsNone && bindsNothing p && isSingleLine r.Range && barOnOwnLine

        clause, p, r, t, qualifies

    // contiguous qualifying runs sharing one body text
    let rec runs
        acc
        (views: (SynMatchClause * SynPat * SynExpr * FSharp.Compiler.SyntaxTrivia.SynMatchClauseTrivia * bool) list)
        =
        match views with
        | [] -> List.rev acc
        | ((_, _, r0, _, true) as head) :: rest ->
            let body = (textOfRange source r0.Range).Trim()

            let sameBody =
                rest
                |> List.takeWhile (fun (_, _, rj, _, qj) -> qj && (textOfRange source rj.Range).Trim() = body)

            let run = head :: sameBody
            runs (run :: acc) (rest |> List.skip sameBody.Length)
        | _ :: rest -> runs acc rest

    [
        for _, expr in index.Exprs do
            let clauses =
                match expr with
                | SynExpr.Match(clauses = cs)
                | SynExpr.MatchBang(clauses = cs)
                | SynExpr.MatchLambda(matchClauses = cs) -> cs
                | _ -> []

            if clauses.Length >= 2 then
                for run in runs [] (clauses |> List.map clauseView) do
                    if run.Length >= 2 then
                        let (SynMatchClause(trivia = firstTrivia), _, _, _, _) = List.head run
                        let (lastClause, _, lastResult, _, _) = List.last run

                        match firstTrivia.BarRange with
                        | Some bar ->
                            let replaceRange = Range.mkRange bar.FileName bar.Start lastClause.Range.End

                            if not (spansDirective source replaceRange) then
                                let indent = String.replicate bar.StartColumn " "
                                let bodyIndent = indent + "    "
                                let body = (textOfRange source lastResult.Range).Trim()

                                // Each arm's own comment travels with its own
                                // pattern. An arm that carries a comment is an
                                // arm the author considered a distinct case,
                                // whatever its body currently says, and folding
                                // the arms while dropping the comments would
                                // delete the only thing telling the merged
                                // cases apart. F# accepts comments between the
                                // alternatives of an or-pattern, and fantomas
                                // keeps them there.
                                //
                                // A comment BETWEEN two arms belongs to neither
                                // range and is not reproduced; the fix is then
                                // held back by the comment guard, which is the
                                // right answer rather than a silent loss.
                                // ...but only the comments we are NOT already
                                // reproducing. The pattern and the surviving body
                                // are spliced verbatim, so a comment inside either
                                // travels with that text; hoisting it as well
                                // printed `1 (* why *) + 1` with the comment three
                                // times over. It compiles, so no build check would
                                // ever have caught it
                                let commentsIn (r: range) (verbatim: range list) =
                                    allComments
                                    |> List.filter (fun (cr, _) ->
                                        Range.rangeContainsRange r cr
                                        && not (verbatim |> List.exists (fun v -> Range.rangeContainsRange v cr)))
                                    |> List.sortBy (fun (cr, _) -> cr.StartLine, cr.StartColumn)
                                    |> List.map snd

                                let lines =
                                    [
                                        for i, (clause, pat, armResult, _, _) in List.indexed run do
                                            let prefix = if i = 0 then "" else indent
                                            let patText = textOfRange source pat.Range

                                            // the pattern is spliced verbatim, and so
                                            // is the surviving body — and the rule only
                                            // fires when the bodies are textually
                                            // IDENTICAL, so a comment inside a discarded
                                            // body is the same comment the survivor
                                            // already carries. Hoisting either one just
                                            // says it twice
                                            let armComments = commentsIn clause.Range [ pat.Range; armResult.Range ]

                                            if i = run.Length - 1 then
                                                // the last arm keeps the body, so its
                                                // comment stays above it
                                                if List.isEmpty armComments then
                                                    $"{prefix}| {patText} -> {body}"
                                                else
                                                    $"{prefix}| {patText} ->"

                                                    for c in armComments do
                                                        $"{bodyIndent}{c}"

                                                    $"{bodyIndent}{body}"
                                            else
                                                $"{prefix}| {patText}"

                                                for c in armComments do
                                                    $"{indent}{c}"
                                    ]

                                {
                                    ReplaceRange = replaceRange
                                    NewText = String.concat "\n" lines
                                    Count = run.Length
                                }
                        | None -> ()
    ]
