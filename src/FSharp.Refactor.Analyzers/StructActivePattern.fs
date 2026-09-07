/// Refactoring (performance): give a trivial partial active pattern a struct
/// return, avoiding an option allocation on every match attempt.
///
///     let (|Even|_|) n =                      [<return: Struct>]
///         if n % 2 = 0 then Some n else None  let (|Even|_|) n =
///                                                 if n % 2 = 0 then ValueSome n else ValueNone
///
/// Pattern-MATCH sites are unchanged — the attribute only changes the
/// representation — which is what makes this rewrite safe for the ordinary
/// use of an active pattern. Requires F# 6+.
///
/// It is not free for every other use: an explicit invocation
/// (`match (|Even|_| ) 4 with Some v -> ...`) or a first-class one
/// (`List.choose (|Even|_|) xs`) sees `voption` instead of `option`. Inside
/// the assembly the compiler catches that immediately; outside it, nothing
/// does — so the pattern must be invisible outside this assembly, unless
/// the caller opted in with `--api-changes` (see Visibility.isInScope).
///
/// Safety rules:
///   - module-level, single-binding partial active pattern `(|P|_|)`
///   - private/internal, or nested in a private/internal module, unless
///     API changes were allowed
///   - no existing attributes on the binding and no return-type annotation
///     (an `option` annotation would need to become `voption`)
///   - every result position in the body must be a literal `Some e` or `None`
///     (reached through if/match/let/sequential/parens); any other result
///     shape skips the suggestion
///   - `Some`/`None` must resolve to FSharp.Core's option cases
module FSharp.Refactor.StructActivePattern

open System
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

/// A single text edit: range, original text, replacement text.
type Edit =
    { Range: range
      Original: string
      Replacement: string }

type Suggestion =
    {
        /// The active pattern's name text, e.g. "|Even|_|".
        PatternName: string
        /// Range of the pattern name, where the hint is anchored.
        NameRange: range
        /// The attribute insertion followed by one edit per Some/None token.
        Edits: Edit list
    }

/// Walk the result positions of the pending bodies, recording every literal
/// Some/None case token. Returns false if any result position has another
/// shape.
[<TailCall>]
let rec private collectResultsLoop (acc: ResizeArray<range * string>) (pending: SynExpr list) : bool =
    match pending with
    | [] -> true
    | e :: rest ->
        match e with
        | SynExpr.Paren(expr = inner) -> collectResultsLoop acc (inner :: rest)
        | SynExpr.App(funcExpr = SynExpr.Ident someIdent) when someIdent.idText = "Some" ->
            acc.Add(someIdent.idRange, "ValueSome")
            collectResultsLoop acc rest
        | SynExpr.Ident ident when ident.idText = "None" ->
            acc.Add(ident.idRange, "ValueNone")
            collectResultsLoop acc rest
        | SynExpr.IfThenElse(thenExpr = thenExpr; elseExpr = Some elseExpr) ->
            collectResultsLoop acc (thenExpr :: elseExpr :: rest)
        | SynExpr.Match(clauses = clauses)
        // a point-free `let (|P|_|) = function ...` body: the clause
        // results are the pattern's result positions all the same
        | SynExpr.MatchLambda(matchClauses = clauses) ->
            let results =
                clauses |> List.map (fun (SynMatchClause(resultExpr = result)) -> result)

            collectResultsLoop acc (results @ rest)
        | LetOrUseE lou when not lou.IsBang -> collectResultsLoop acc (lou.Body :: rest)
        | SynExpr.Sequential(expr2 = expr2) -> collectResultsLoop acc (expr2 :: rest)
        | _ -> false

let private collectResults (acc: ResizeArray<range * string>) (e: SynExpr) : bool = collectResultsLoop acc [ e ]

let private isPartialActivePatternName (name: string) = Regex.IsMatch(name, @"^\|.+\|_\|$")

/// Find trivial partial active patterns that can get [<return: Struct>].
/// Requires typed check results for the Some/None gate.
let find
    (allowApiChanges: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()
    let index = AstIndex.ofTree parseTree

    // an explicit or first-class invocation in this file — `(|P|_|) x`,
    // `List.choose (|P|_|)` — sees the option the pattern returns: the F#
    // compiler's Spreads.fs calls its module-level (|NestedUpdate|_|) from a
    // local pattern of the same name and matches the result against Some.
    // The representation change would reach it, so the pattern stays
    let invokedAsFunction (name: string) =
        index.Exprs
        |> Array.exists (fun (_, e) ->
            match e with
            | SynExpr.Ident id -> id.idText = name
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> not ids.IsEmpty && (List.last ids).idText = name
            | _ -> false)

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(path, decl) =
                match decl with
                | SynModuleDecl.Let(
                    bindings = [ SynBinding(
                                     attributes = []
                                     returnInfo = None
                                     accessibility = bindingAccess
                                     headPat = SynPat.LongIdent(
                                         longDotId = SynLongIdent(id = [ nameIdent ]); accessibility = patAccess)
                                     expr = body) ]) when
                    isPartialActivePatternName nameIdent.idText
                    // `let private (|P|_|)` parses its modifier onto the
                    // pattern, not the binding — check both
                    // named, not plain: a signature file may write
                    // `val private ( |P|_| ) : ... option`, and giving the
                    // implementation a voption return alone does not compile
                    && Visibility.isInScopeNamed allowApiChanges path [ bindingAccess; patAccess ] nameIdent.idText
                    && not (invokedAsFunction nameIdent.idText)
                    ->
                    let results = ResizeArray<range * string>()

                    // the attribute line lands at the decl's start line, so
                    // that line must be the decl's own (a one-line nested
                    // module or `;;`-chained decl would get the attribute
                    // spliced against the WRONG construct)
                    let ownLine =
                        decl.Range.StartColumn = 0
                        || (source.GetLineString(decl.Range.StartLine - 1)).Substring(0, decl.Range.StartColumn).Trim() = ""

                    if ownLine && collectResults results body && results.Count > 0 then
                        // below any XML doc, so the attribute sits against
                        // the binding it marks
                        let insertPos = attributeInsertPos source decl.Range
                        let indent = String(' ', insertPos.Column)

                        let insertEdit =
                            { Range = Range.mkRange decl.Range.FileName insertPos insertPos
                              Original = ""
                              Replacement = "[<return: Struct>]\n" + indent }

                        let tokenEdits =
                            results
                            |> Seq.map (fun (r, replacement) ->
                                { Range = r
                                  Original = textOfRange source r
                                  Replacement = replacement })
                            |> List.ofSeq

                        let gated =
                            tokenEdits
                            |> List.forall (fun e ->
                                let ident = Ident(e.Original, e.Range)

                                OptionModule.resolvesToCoreCase check source "Microsoft.FSharp.Core.Option<" ident)

                        if gated then
                            suggestions.Add
                                { PatternName = nameIdent.idText
                                  NameRange = nameIdent.idRange
                                  Edits = insertEdit :: tokenEdits }
                | _ -> () }

    if OptionModule.hasErrors check then
        []
    else
        AstIndex.replay collector parseTree
        List.ofSeq suggestions
