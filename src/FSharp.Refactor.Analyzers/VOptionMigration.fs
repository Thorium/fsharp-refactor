/// The FR0069 fix: migrate a FILE-PRIVATE record field from `T option`
/// to `T voption`, rewriting every use in the same edit set.
///
///     type private Row = { Seen: DateTime option }        voption
///     { Seen = Some now }                              ValueSome now
///     { row with Seen = None }                         ValueNone
///     match row.Seen with Some d -> .. | None -> ..    ValueSome/ValueNone
///     row.Seen |> Option.map f                         ValueOption.map
///     defaultArg row.Seen fallback                     defaultValueArg
///     row.Seen.IsSome / .IsNone / .Value               unchanged
///
/// Sound only because the type is strictly file-private: F# private means
/// the enclosing module of THIS file, so the file's own typed results
/// enumerate every use — nothing outside can see the field. The whole
/// migration is all-or-nothing: every use must be one of the shapes above
/// (verified against the typed symbol, never by name), or the suggestion
/// stays a note. A use that BINDS the option value (`let x = row.Seen`,
/// `| x -> ..`) starts dataflow this scan does not follow — bail.
module FSharp.Refactor.VOptionMigration

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// Option-module functions whose ValueOption twins have identical
/// signatures and semantics.
let private parityFunctions =
    set
        [ "map"
          "map2"
          "map3"
          "bind"
          "iter"
          "filter"
          "exists"
          "forall"
          "contains"
          "count"
          "defaultValue"
          "defaultWith"
          "fold"
          "foldBack"
          "get"
          "isSome"
          "isNone"
          "toArray"
          "toList"
          "toNullable"
          "toObj"
          "orElse"
          "orElseWith"
          "flatten" ]

/// Members voption shares with option — access sites need no edit.
let private sharedMembers = set [ "IsSome"; "IsNone"; "Value" ]

/// An operator expression's compiled name — infix operators parse as a
/// one-segment LongIdent carrying the original notation.
let private opName (e: SynExpr) =
    match e with
    | SynExpr.Ident op -> Some op.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) -> Some op.idText
    | _ -> None

let private isPipeOp (e: SynExpr) = opName e = Some "op_PipeRight"

let private isEqualityOp (e: SynExpr) =
    match opName e with
    | Some("op_Equality" | "op_Inequality") -> true
    | _ -> false

/// The function position of an application chain.
[<TailCall>]
let rec private headOf (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = f) -> headOf f
    | SynExpr.Paren(expr = inner) -> headOf inner
    | SynExpr.TypeApp(expr = inner) -> headOf inner
    | h -> h

/// `Some`/`None` as a constructing EXPRESSION: the edit for its ident.
let private constructionEdit (e: SynExpr) : (range * string * string) option =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident someId) when someId.idText = "Some" ->
        Some(someId.idRange, "Some", "ValueSome")
    | SynExpr.Ident noneId when noneId.idText = "None" -> Some(noneId.idRange, "None", "ValueNone")
    | _ -> None

/// `Some p`/`None`/`_` as a match PATTERN, or-patterns included; None when
/// the pattern is anything else (a binder starts untracked dataflow).
let rec private patternEdits (p: SynPat) : (range * string * string) list option =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats [ _ ]) when id.idText = "Some" ->
        Some [ id.idRange, "Some", "ValueSome" ]
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) when id.idText = "None" ->
        Some [ id.idRange, "None", "ValueNone" ]
    | SynPat.Wild _ -> Some []
    | SynPat.Paren(pat = inner) -> patternEdits inner
    | SynPat.Or(lhsPat = l; rhsPat = r) ->
        match patternEdits l, patternEdits r with
        | Some a, Some b -> Some(a @ b)
        | _ -> None
    | _ -> None

/// Every clause of the match must destructure with Some/None/wildcard.
let private matchClauseEdits (clauses: SynMatchClause list) : (range * string * string) list option =
    clauses
    |> List.fold
        (fun acc (SynMatchClause(pat = p)) ->
            match acc, patternEdits p with
            | Some a, Some b -> Some(a @ b)
            | _ -> None)
        (Some [])

[<return: Struct>]
let inline private (|IsPipeOp|_|) input =
    if isPipeOp input then ValueSome input else ValueNone

[<return: Struct>]
let inline private (|IsEqualityOp|_|) input =
    if isEqualityOp input then ValueSome input else ValueNone

/// A per-file classifier: given THAT file's parse tree and source, maps
/// one symbol use to its edits — or None when the use falls outside the
/// provably-rewritable shapes. Cross-file migrations build one classifier
/// per file the uses land in.
let classifierFor
    (fieldName: string)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : FSharpSymbolUse -> (range * string * string) list option =
    let index = AstIndex.ofTree parseTree

    // record construction sites, field-name range -> assigned expr
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

    // record patterns, field-name range -> inner pattern
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

    // smallest expression containing a range, with its ancestors
    let nodeAt (r: range) =
        index.Exprs
        |> Array.filter (fun (_, e) -> Range.rangeContainsRange e.Range r)
        |> Array.sortBy (fun (_, e) ->
            (e.Range.EndLine - e.Range.StartLine) * 10000
            + (e.Range.EndColumn - e.Range.StartColumn))
        |> Array.tryHead

    // a use consumed through an application chain: climb while the
    // head stays a pipe, then classify the head that consumes it
    let rec classifyApp (path: SyntaxNode list) (current: SynExpr) : (range * string * string) list option =
        match path with
        | SyntaxNode.SynExpr(SynExpr.Paren _ as paren) :: rest -> classifyApp rest paren
        | SyntaxNode.SynExpr(SynExpr.App _ as app) :: rest ->
            match headOf app with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when
                m.idText = "Option" && parityFunctions.Contains f.idText
                ->
                Some [ m.idRange, "Option", "ValueOption" ]
            | SynExpr.Ident d when d.idText = "defaultArg" -> Some [ d.idRange, "defaultArg", "defaultValueArg" ]
            | IsEqualityOp eqHead ->
                // `field = None` / `None <> field`: the None literal
                // must migrate with the field. The FULL comparison
                // carries both operands; a partial (just the infix
                // node wrapping our side) climbs one more level
                match app with
                | SynExpr.App(funcExpr = SynExpr.App(funcExpr = opE; argExpr = lhs); argExpr = rhs) when
                    isEqualityOp opE
                    ->
                    match lhs, rhs with
                    | SynExpr.Ident noneId, _
                    | _, SynExpr.Ident noneId when noneId.idText = "None" ->
                        Some [ noneId.idRange, "None", "ValueNone" ]
                    | _ -> None
                | _ -> classifyApp rest app
            | IsPipeOp pipeHead ->
                match app, current with
                | SynExpr.App(funcExpr = infixPart), c when Range.equals infixPart.Range c.Range ->
                    // we were the piped VALUE: the receiving side is
                    // the full pipe's argExpr — classify its head
                    match app with
                    | SynExpr.App(argExpr = receiver) ->
                        match headOf receiver with
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when
                            m.idText = "Option" && parityFunctions.Contains f.idText
                            ->
                            Some [ m.idRange, "Option", "ValueOption" ]
                        | _ -> None
                    | _ -> None
                | _ ->
                    // still inside the lhs of the pipe: keep climbing
                    classifyApp rest app
            | _ -> None
        | _ -> None

    fun (u: FSharpSymbolUse) ->
        let key = u.Range.StartLine, u.Range.StartColumn

        match constructionRhs.TryGetValue key with
        | true, Some rhs -> constructionEdit rhs |> Option.map List.singleton
        | true, None -> None
        | _ ->
            match patternInner.TryGetValue key with
            | true, inner -> patternEdits inner
            | _ ->
                match nodeAt u.Range with
                | Some(path, access) ->
                    // the access node may already END in a shared
                    // member: `row.Seen.IsSome` is one LongIdent
                    let viaSharedMember =
                        match access with
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                            let last = (List.last ids).idText
                            sharedMembers.Contains last && last <> fieldName
                        | _ -> false

                    if viaSharedMember then
                        Some []
                    else
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.DotGet(longDotId = SynLongIdent(id = [ m ]))) :: _ when
                            sharedMembers.Contains m.idText
                            ->
                            Some []
                        | SyntaxNode.SynExpr(SynExpr.Match(expr = scrutinee; clauses = clauses)) :: _
                        | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.Match(
                            expr = scrutinee; clauses = clauses)) :: _ when
                            Range.rangeContainsRange scrutinee.Range access.Range
                            ->
                            matchClauseEdits clauses
                        | appPath -> classifyApp appPath access
                | None -> None

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
        | :? FSharpField as f -> Some(f :> FSharpSymbol)
        | _ -> None
    | None -> None

/// The type edit itself: `option` -> `voption`.
let private typeEditFor (source: ISourceText) (optionNameRange: range) =
    match textOfRange source optionNameRange with
    | "option" -> Some(optionNameRange, "option", "voption")
    | "Option" -> Some(optionNameRange, "Option", "ValueOption")
    | _ -> None

/// Collect classified use edits into the all-or-nothing set, deduplicated
/// by position (or-patterns classify one range twice).
let private collectEdits (typeEdit: range * string * string) (classified: (range * string * string) list option[]) =
    if classified |> Array.forall Option.isSome then
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
    (optionNameRange: range)
    : (range * string * string) list option =
    if OptionModule.hasErrors check then
        None
    else
        match typeEditFor source optionNameRange, fieldSymbol check source fieldIdRange fieldName with
        | Some typeEdit, Some symbol ->
            let uses =
                check.GetUsesOfSymbolInFile symbol
                |> Array.filter (fun u -> not u.IsFromDefinition)

            collectEdits typeEdit (uses |> Array.map (classifierFor fieldName parseTree source))
        | _ -> None

/// The PROJECT-WIDE edit set for an internal field: every use across the
/// project classified against its own file's parse tree (supplied by the
/// host through ProjectSources — unavailable hosts get None), one
/// all-or-nothing set spanning files. The caller gates on --api-changes;
/// the CLI additionally holds cross-file groups back without the flag.
let migrateProject
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (projectCheck: FSharpCheckProjectResults)
    (fieldIdRange: range)
    (fieldName: string)
    (optionNameRange: range)
    : (range * string * string) list option =
    if OptionModule.hasErrors check || not (ProjectSources.available ()) then
        None
    else
        match typeEditFor source optionNameRange, fieldSymbol check source fieldIdRange fieldName with
        | Some typeEdit, Some symbol ->
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
                            Some(classifierFor fieldName parseTree source)
                        else
                            ProjectSources.tryParse path
                            |> Option.map (fun (tree, src) -> classifierFor fieldName tree src)

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

            if classified.Length = 0 then
                None
            else
                collectEdits typeEdit classified
        | _ -> None
