/// Refactoring (design): a DU match whose wildcard stands in for just one
/// or two concrete cases hides them behind an "open else" — when the union
/// grows, the new case silently falls into `_` instead of raising an
/// incomplete-match warning.
///
///     type T = A | B | C | D
///     match t with                       match t with
///     | A -> ...                         | A -> ...
///     | B -> ...                    →    | B -> ...
///     | C -> ...                         | C -> ...
///     | _ -> fallback                    | D -> fallback
///
/// Safety rules:
///   - the scrutinized type resolves (typed check results) to an F# union;
///     enums never match — they are open sets by design
///   - every explicit clause covers its case TOTALLY: bare case, or case
///     whose payload pattern is only binders/wildcards — a literal payload
///     (`D 3`) leaves the case partially covered and skips the match
///   - no clause carries a `when` guard (guards break coverage reasoning)
///   - the wildcard is a plain `_`, is the last clause, and hides at most
///     two cases (purging a long tail would bloat the match)
module FSharp.Refactor.ExpandWildcard

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The wildcard pattern, replaced by the explicit cases.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The case names the wildcard was hiding.
        HiddenCases: string list
    }

/// A pattern that matches every value of its shape: binders and wildcards
/// only.
[<TailCall>]
let rec private isTotalLoop (pending: SynPat list) =
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

/// The case idents (full dotted paths) a clause pattern covers totally, or
/// None when any part covers only partially. Or-patterns yield several.
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

let private coveredCases (p: SynPat) = coveredLoop [] [ p ]

/// The union cases of the type this case ident belongs to, or None when it
/// is not an F# union case.
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
                    Some(t.TypeDefinition, [ for c in t.TypeDefinition.UnionCases -> c.Name, c.Fields.Count > 0 ])
                else
                    None
            with OptionModule.FcsSymbolFailure ->
                None
        | _ -> None
    | None -> None

/// The other unions the file can see — this project's files up to here and
/// the referenced assemblies — with their case names. A hidden case written
/// BARE resolves to whichever union declared that name last: suave's
/// Http2.fs matched a Result, and `Error` there is ScanResult.Error from an
/// earlier file of the project. A case another union also names is written
/// qualified (`Result.Error _`), which is right in every scope.
let private unionsInScope (check: FSharpCheckFileResults) =
    let rec unions (entities: FSharpEntity seq) =
        seq {
            for e in entities do
                let isUnion, nested =
                    try
                        e.IsFSharpUnion, (e.NestedEntities :> FSharpEntity seq)
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        false, Seq.empty

                if isUnion then
                    yield e

                yield! unions nested
        }

    // only a PUBLIC union of another assembly reaches this file (FSharp.Core
    // keeps an internal Result-like union whose `Error` would otherwise
    // qualify every Result match)
    let ofAssembly (a: FSharpAssembly) =
        try
            unions a.Contents.Entities
            |> Seq.filter (fun e ->
                try
                    e.Accessibility.IsPublic
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    false)
            |> List.ofSeq
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            []

    let own =
        try
            unions check.PartialAssemblySignature.Entities |> List.ofSeq
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            []

    let referenced =
        try
            check.ProjectContext.GetReferencedAssemblies() |> List.collect ofAssembly
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            []

    own @ referenced
    |> List.map (fun e ->
        e,
        (try
            e.UnionCases |> Seq.map (fun c -> c.Name) |> Set.ofSeq
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             Set.empty))

let private caseNamedElsewhere (unions: (FSharpEntity * Set<string>) list) (union: FSharpEntity) (name: string) =
    unions
    |> List.exists (fun (e, cases) ->
        cases.Contains name
        && not (
            try
                e.IsEffectivelySameAs union
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                true
        ))

/// Find near-total DU matches hiding one or two cases behind `_`. Requires
/// typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree
        let unions = lazy (unionsInScope check)

        [ for _, expr in index.Exprs do
              match expr with
              | SynExpr.Match(clauses = clauses)
              | SynExpr.MatchBang(clauses = clauses)
              | SynExpr.MatchLambda(matchClauses = clauses) when clauses.Length >= 2 ->
                  let unguarded =
                      clauses |> List.forall (fun (SynMatchClause(whenExpr = g)) -> g.IsNone)

                  let explicitClauses, lastClause = List.splitAt (clauses.Length - 1) clauses

                  match lastClause with
                  | [ SynMatchClause(pat = SynPat.Wild wildRange) ] when unguarded ->
                      let covered =
                          explicitClauses |> List.map (fun (SynMatchClause(pat = p)) -> coveredCases p)

                      if covered |> List.forall Option.isSome then
                          let coveredIdents = covered |> List.choose id |> List.concat

                          match coveredIdents with
                          | first :: _ ->
                              match unionCasesOf check source (List.last first) with
                              | Some(union, allCases) ->
                                  let coveredNames =
                                      coveredIdents |> List.map (fun ids -> (List.last ids).idText) |> Set.ofList

                                  let missing =
                                      allCases |> List.filter (fun (name, _) -> not (coveredNames.Contains name))

                                  // a [<RequireQualifiedAccess>] union needs
                                  // its qualifier: reuse the first clause's,
                                  // which provably compiles in this scope
                                  let clauseQualifier =
                                      first
                                      |> List.rev
                                      |> List.tail
                                      |> List.rev
                                      |> List.map (fun i -> i.idText + ".")
                                      |> String.concat ""

                                  // ...and a bare name another union in scope
                                  // also declares needs the union's own
                                  let qualifier =
                                      if
                                          clauseQualifier = ""
                                          && missing
                                             |> List.exists (fun (name, _) ->
                                                 caseNamedElsewhere unions.Value union name)
                                      then
                                          union.DisplayName + "."
                                      else
                                          clauseQualifier

                                  // every explicit name must belong to this
                                  // union, and 1-2 cases are hidden
                                  if
                                      coveredNames.Count = coveredIdents.Length
                                      && (allCases |> List.length) - missing.Length = coveredNames.Count
                                      && not missing.IsEmpty
                                      && missing.Length <= 2
                                  then
                                      let cases =
                                          missing
                                          |> List.map (fun (name, hasFields) ->
                                              if hasFields then
                                                  $"{qualifier}{name} _"
                                              else
                                                  $"{qualifier}{name}")

                                      // two short cases share the wildcard's line;
                                      // when that line would run past 100 columns
                                      // each case takes its own line under the
                                      // clause's `|`, the last one keeping the `->`
                                      let joined = String.concat " | " cases
                                      let lineText = source.GetLineString(wildRange.StartLine - 1)
                                      let before = lineText.Substring(0, wildRange.StartColumn)
                                      let after = lineText.Substring wildRange.EndColumn
                                      let barIndex = before.LastIndexOf '|'

                                      let replacement =
                                          if
                                              cases.Length > 1
                                              && (before + joined + after).Length > 100
                                              && barIndex >= 0
                                              && before.Substring(0, barIndex).Trim() = ""
                                          then
                                              let bar = "\n" + System.String(' ', barIndex) + "| "
                                              String.concat bar cases
                                          else
                                              joined

                                      { Range = wildRange
                                        OriginalText = textOfRange source wildRange
                                        ReplacementText = replacement
                                        HiddenCases = missing |> List.map fst }
                              | None -> ()
                          | [] -> ()
                  | _ -> ()
              | _ -> () ]
