/// The FR0093 fix: migrate a FILE-PRIVATE record field from a reference
/// tuple to a struct tuple, rewriting every use in the same edit set.
///
///     type private P = { A: int * int }         A: struct (int * int)
///     { A = (1, 2) }                            { A = struct (1, 2) }
///     { A = x, y }                              { A = struct (x, y) }
///     match p.A with | (x, y) -> ..             | struct (x, y) -> ..
///     let (x, y) = p.A                          let struct (x, y) = p.A
///     p.A = (3, 4)                              p.A = struct (3, 4)
///
/// Sound only because the type is strictly file-private: the file's typed
/// results enumerate every use. All-or-nothing: every construction must
/// assign a LITERAL tuple (an arbitrary expression of tuple type would
/// change type under it), every read must destructure into a literal
/// tuple pattern (or compare against a literal tuple) — `fst`/`snd`, a
/// binder, or the field passed along whole all start dataflow this scan
/// does not follow, and any one of them keeps the field a note.
module FSharp.Refactor.StructTupleMigration

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// `(a, b)` or bare `a, b` as a constructing EXPRESSION: the edits that
/// spell `struct ` onto it. None for anything but a literal tuple.
let private tupleExprEdits (source: ISourceText) (e: SynExpr) : (range * string * string) list option =
    match e with
    | SynExpr.Paren(expr = SynExpr.Tuple(isStruct = false)) ->
        let at = Range.mkRange e.Range.FileName e.Range.Start e.Range.Start
        Some [ at, "", "struct " ]
    | SynExpr.Tuple(isStruct = false) ->
        Some [ e.Range, textOfRange source e.Range, $"struct ({textOfRange source e.Range})" ]
    | _ -> None

/// `(a, b)` / bare / `_` as a PATTERN, or-patterns included.
let rec private tuplePatEdits (source: ISourceText) (p: SynPat) : (range * string * string) list option =
    match p with
    | SynPat.Paren(pat = SynPat.Tuple(isStruct = false)) ->
        let at = Range.mkRange p.Range.FileName p.Range.Start p.Range.Start
        Some [ at, "", "struct " ]
    | SynPat.Tuple(isStruct = false) ->
        Some [ p.Range, textOfRange source p.Range, $"struct ({textOfRange source p.Range})" ]
    | SynPat.Wild _ -> Some []
    | SynPat.Or(lhsPat = l; rhsPat = r) ->
        match tuplePatEdits source l, tuplePatEdits source r with
        | Some a, Some b -> Some(a @ b)
        | _ -> None
    | _ -> None

let private matchClauseEdits (source: ISourceText) (clauses: SynMatchClause list) =
    clauses
    |> List.fold
        (fun acc (SynMatchClause(pat = p)) ->
            match acc, tuplePatEdits source p with
            | Some a, Some b -> Some(a @ b)
            | _ -> None)
        (Some [])

let private isEqualityOp (e: SynExpr) =
    match e with
    | SynExpr.Ident op -> op.idText = "op_Equality" || op.idText = "op_Inequality"
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) ->
        op.idText = "op_Equality" || op.idText = "op_Inequality"
    | _ -> false

/// A per-file classifier: given THAT file's parse tree and source, maps
/// one symbol use to its edits — or None when the use falls outside the
/// provably-rewritable shapes.
let classifierFor
    (parseTree: ParsedInput)
    (source: ISourceText)
    : FSharpSymbolUse -> (range * string * string) list option =
    let index = AstIndex.ofTree parseTree

    // record construction sites, field-name position -> assigned expr
    let constructionRhs =
        [ for _, e in index.Exprs do
              match e with
              | SynExpr.Record(recordFields = fields) ->
                  for SynExprRecordField(fieldName = (SynLongIdent(id = ids), _); expr = rhs) in fields do
                      if not ids.IsEmpty then
                          yield (List.last ids).idRange, rhs
              | _ -> () ]
        |> List.map (fun (r, rhs) -> (r.StartLine, r.StartColumn), rhs)
        |> dict

    // record patterns, field-name position -> inner pattern
    let patternInner =
        [ for _, p in index.Pats do
              match p with
              | SynPat.Record(fieldPats = fieldPats) ->
                  for NamePatPairField(fieldName = SynLongIdent(id = fids); pat = inner) in fieldPats do
                      if not fids.IsEmpty then
                          let fr = (List.last fids).idRange
                          yield (fr.StartLine, fr.StartColumn), inner
              | _ -> () ]
        |> dict

    let nodeAt (r: range) =
        index.Exprs
        |> Array.filter (fun (_, e) -> Range.rangeContainsRange e.Range r)
        |> Array.sortBy (fun (_, e) ->
            (e.Range.EndLine - e.Range.StartLine) * 10000
            + (e.Range.EndColumn - e.Range.StartColumn))
        |> Array.tryHead

    fun (u: FSharpSymbolUse) ->
        let key = u.Range.StartLine, u.Range.StartColumn

        match constructionRhs.TryGetValue key with
        | true, Some rhs -> tupleExprEdits source rhs
        | true, None -> None
        | _ ->
            match patternInner.TryGetValue key with
            | true, inner -> tuplePatEdits source inner
            | _ ->
                match nodeAt u.Range with
                | None -> None
                | Some(path, access) ->
                    match path with
                    // match p.A with | (x, y) -> ..
                    | SyntaxNode.SynExpr(SynExpr.Match(expr = scrutinee; clauses = clauses)) :: _
                    | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.Match(
                        expr = scrutinee; clauses = clauses)) :: _ when
                        Range.rangeContainsRange scrutinee.Range access.Range
                        ->
                        matchClauseEdits source clauses
                    // p.A = (3, 4) / (3, 4) <> p.A — the literal side
                    // migrates with the field
                    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = opE; argExpr = lhs) as partial) :: rest when
                        isEqualityOp opE && Range.equals lhs.Range access.Range
                        ->
                        // our side is the LHS; the full comparison is
                        // one level up, carrying the RHS
                        (match rest with
                         | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f; argExpr = rhs)) :: _ when
                             Range.equals f.Range partial.Range
                             ->
                             tupleExprEdits source rhs
                         | _ -> None)
                    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = opE; argExpr = lhs))) :: _ when
                        isEqualityOp opE && Range.rangeContainsRange lhs.Range access.Range |> not
                        ->
                        // our side is the RHS; the literal is the LHS
                        tupleExprEdits source lhs
                    | _ ->
                        // `let (x, y) = p.A` — the enclosing binding
                        // destructures the read directly
                        path
                        |> List.tryPick (fun node ->
                            match node with
                            | SyntaxNode.SynBinding(SynBinding(headPat = hp; expr = rhs)) when
                                Range.rangeContainsRange rhs.Range access.Range
                                && Range.equals (stripParens rhs).Range (stripParens access).Range
                                ->
                                Some hp
                            | _ -> None)
                        |> Option.bind (tuplePatEdits source)

/// The field's typed symbol at its defining ident.
let private fieldSymbol
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (fieldIdRange: range)
    (fieldName: string)
    =
    let lineText = source.GetLineString(fieldIdRange.EndLine - 1)

    match check.GetSymbolUseAtLocation(fieldIdRange.EndLine, fieldIdRange.EndColumn, lineText, [ fieldName ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpField as f -> ValueSome(f :> FSharpSymbol)
        | _ -> ValueNone
    | None -> ValueNone

/// Collect classified use edits into the all-or-nothing set. A field with
/// ZERO uses stays a note: nothing proves the shape.
let private collectEdits (typeEdit: range * string * string) (classified: (range * string * string) list option[]) =
    if classified.Length > 0 && classified |> Array.forall Option.isSome then
        let seen = System.Collections.Generic.HashSet<string * int * int>()

        typeEdit :: (classified |> Array.toList |> List.collect Option.get)
        |> List.filter (fun (r, _, _) -> seen.Add(r.FileName, r.StartLine, r.StartColumn))
        |> Some
    else
        None

/// Compute the single-file edit set for one field, or None when any use
/// falls outside the provably-rewritable shapes.
let migrate
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (fieldIdRange: range)
    (fieldName: string)
    (tupleTypeRange: range)
    : (range * string * string) list option =
    if OptionModule.hasErrors check then
        None
    else
        let typeText = textOfRange source tupleTypeRange
        let typeEdit = tupleTypeRange, typeText, $"struct ({typeText})"

        match fieldSymbol check source fieldIdRange fieldName with
        | ValueNone -> None
        | ValueSome symbol ->
            let uses =
                check.GetUsesOfSymbolInFile symbol
                |> Array.filter (fun u -> not u.IsFromDefinition)

            collectEdits typeEdit (uses |> Array.map (classifierFor parseTree source))

/// The PROJECT-WIDE edit set for an internal field: every use across the
/// project classified against its own file's parse tree (supplied by the
/// host through ProjectSources — unavailable hosts get None), one
/// all-or-nothing set spanning files.
let migrateProject
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (projectCheck: FSharpCheckProjectResults)
    (fieldIdRange: range)
    (fieldName: string)
    (tupleTypeRange: range)
    : (range * string * string) list option =
    if OptionModule.hasErrors check || not (ProjectSources.available ()) then
        None
    else
        let typeText = textOfRange source tupleTypeRange
        let typeEdit = tupleTypeRange, typeText, $"struct ({typeText})"

        match fieldSymbol check source fieldIdRange fieldName with
        | ValueNone -> None
        | ValueSome symbol ->
            let thisFile = System.IO.Path.GetFullPath(fieldIdRange.FileName).ToLowerInvariant()

            let classifiers =
                System.Collections.Generic.Dictionary<
                    string,
                    (FSharpSymbolUse -> (range * string * string) list option) option
                 >()

            let classifierForFile (path: string) =
                let key = System.IO.Path.GetFullPath(path).ToLowerInvariant()

                match classifiers.TryGetValue key with
                | true, c -> c
                | _ ->
                    let c =
                        if key = thisFile then
                            Some(classifierFor parseTree source)
                        else
                            ProjectSources.tryParse path
                            |> Option.map (fun (tree, src) -> classifierFor tree src)

                    classifiers.[key] <- c
                    c

            let classified =
                // a `#load`ing script is a real call site the project
                // cannot see, and no build check covers it: missing one is
                // the single thing this migration cannot survive
                Array.append (projectCheck.GetUsesOfSymbol symbol) (ProjectSources.outsideUsesOf symbol)
                |> Array.filter (fun u -> not u.IsFromDefinition)
                |> Array.map (fun u ->
                    match classifierForFile u.Range.FileName with
                    | Some classify -> classify u
                    | None -> None)

            collectEdits typeEdit classified
