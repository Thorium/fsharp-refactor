/// FR0134 (fix, OFF by default): migrate a contained record field from/// `DateTime` to `DateTimeOffset`, rewriting every use in one edit set.
///
///     type private Row = { Seen: DateTime }        Seen: DateTimeOffset
///     { Seen = DateTime.UtcNow }                   DateTimeOffset.UtcNow
///     r.Seen.Year, r.Seen.AddDays 1.0              unchanged — parity members
///     a.Seen < b.Seen, a.Seen - b.Seen             unchanged — same semantics
///
/// DateTimeOffset records the instant AND the clock that produced it —
/// the server-timezone accidents FR0121 warns about stop being possible.
/// The classifier is deliberately strict, because this migration is only
/// behavior-preserving inside a narrow envelope:
///   - every construction assigns DateTime.UtcNow / .Now / .MinValue /
///     .MaxValue — and Now and UtcNow never mix on one field (DateTime
///     comparisons ignore Kind; mixing was already a bug, and fixing it
///     silently is still a behavior change to bail on)
///   - every read is a parity member (Year..Second, Add*/Subtract,
///     DayOfWeek...), a comparison against the same field on another
///     value, or a subtraction of two field reads. `.Date` returns
///     DateTime (type escapes), and ToString formats differently — both
///     bail, as does any dataflow the scan cannot follow.
///
/// OFF by default: even inside the envelope this is a modernization with
/// serialization-shape consequences the repository owner should opt into
/// (`"FR0134": true`). File-private types only in this first cut — the
/// classifier machinery extends to internal-over-ProjectSources when
/// the envelope has proven itself.
module FSharp.Refactor.DateTimeOffsetMigration

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        FieldName: string
        TypeName: string
        IsFilePrivate: bool
        FieldIdRange: range
        /// The `DateTime` type name's own range — the type edit target.
        TypeNameRange: range
    }

/// Members whose value and type are identical on both clocks (for a
/// field whose writes never mix Now and UtcNow).
let private parityMembers =
    set
        [ "Year"
          "Month"
          "Day"
          "Hour"
          "Minute"
          "Second"
          "Millisecond"
          "DayOfWeek"
          "DayOfYear"
          "Ticks"
          "TimeOfDay"
          "AddDays"
          "AddHours"
          "AddMinutes"
          "AddSeconds"
          "AddMilliseconds"
          "AddTicks"
          "AddMonths"
          "AddYears"
          "Add"
          "Subtract"
          "CompareTo"
          "Equals" ]

let private comparisonOps =
    set
        [ "op_LessThan"
          "op_GreaterThan"
          "op_LessThanOrEqual"
          "op_GreaterThanOrEqual"
          "op_Equality"
          "op_Inequality"
          "op_Subtraction" ]

/// The record fields typed `DateTime` in contained record types.
let find (allowApiChanges: bool) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [ for path, decl in index.Decls do
          match decl with
          | SynModuleDecl.Types(typeDefns = defns) ->
              for SynTypeDefn(typeInfo = SynComponentInfo(longId = typeIds; accessibility = access); typeRepr = repr) in
                  defns do
                  match repr with
                  | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Record(recordFields = fields)) when
                      Visibility.isInScopeNamedPath allowApiChanges path [ access ] typeIds
                      ->
                      let isFilePrivate =
                          (match access with
                           | Some(SynAccess.Private _) -> true
                           | _ -> false)
                          || path
                             |> List.exists (fun node ->
                                 match node with
                                 | SyntaxNode.SynModule(SynModuleDecl.NestedModule(
                                     moduleInfo = SynComponentInfo(accessibility = Some(SynAccess.Private _)))) -> true
                                 | _ -> false)

                      for SynField(idOpt = idOpt; fieldType = fieldType) in fields do
                          match fieldType, idOpt with
                          | SynType.LongIdent(SynLongIdent(id = tids)), Some fieldId when
                              not tids.IsEmpty && (List.last tids).idText = "DateTime"
                              ->
                              { Range = fieldType.Range
                                FieldName = fieldId.idText
                                TypeName = typeIds |> List.map (fun i -> i.idText) |> String.concat "."
                                IsFilePrivate = isFilePrivate
                                FieldIdRange = fieldId.idRange
                                TypeNameRange = (List.last tids).idRange }
                          | _ -> ()
                  | _ -> ()
          | _ -> () ]

/// A per-file classifier plus the write sources it saw — Now and UtcNow
/// must not mix across the WHOLE migration, so the caller collects them.
/// `isFieldUseAt` confirms a position is a use of THIS field's symbol (a
/// same-named field on another type must not count as a sound comparison
/// operand), and `isSystemDateTimeIdent` confirms a `DateTime` prefix
/// really is System.DateTime — a shadowing fake-clock module would take
/// the rewrite, compile, and silently switch to the real clock.
let classifierFor
    (fieldName: string)
    (isFieldUseAt: int * int -> bool)
    (isSystemDateTimeIdent: string list -> Ident -> bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : (FSharpSymbolUse -> ((range * string * string) list * string list) option) =
    let index = AstIndex.ofTree parseTree

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

    let nodeAt (r: range) =
        index.Exprs
        |> Array.filter (fun (_, e) -> Range.rangeContainsRange e.Range r)
        |> Array.sortBy (fun (_, e) ->
            (e.Range.EndLine - e.Range.StartLine) * 10000
            + (e.Range.EndColumn - e.Range.StartColumn))
        |> Array.tryHead

    // `DateTime.UtcNow` / `DateTime.Now` / `DateTime.MinValue` /
    // `DateTime.MaxValue` as a construction RHS: the DateTime prefix
    // becomes DateTimeOffset, and the write source is recorded
    let constructionEdit (e: SynExpr) =
        match stripParens e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
            let last = (List.last ids).idText
            let dt = ids.[ids.Length - 2]

            if
                dt.idText = "DateTime"
                && isSystemDateTimeIdent (ids |> List.truncate (ids.Length - 1) |> List.map _.idText) dt
            then
                let src =
                    match last with
                    | "UtcNow" -> Some "utc"
                    | "Now" -> Some "local"
                    | "MinValue"
                    | "MaxValue" -> Some "neutral"
                    | _ -> None

                src |> Option.map (fun s -> [ dt.idRange, "DateTime", "DateTimeOffset" ], [ s ])
            else
                None
        | _ -> None

    // is the OTHER comparison operand a read of THIS field — by symbol,
    // not by name (Other.Seen must not vouch for Row.Seen)
    let isSameFieldRead (e: SynExpr) =
        match stripParens e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
            let last = List.last ids

            last.idText = fieldName
            && isFieldUseAt (last.idRange.StartLine, last.idRange.StartColumn)
        | SynExpr.DotGet(longDotId = SynLongIdent(id = [ id ])) ->
            id.idText = fieldName
            && isFieldUseAt (id.idRange.StartLine, id.idRange.StartColumn)
        | _ -> false

    let opName (e: SynExpr) =
        match e with
        | SynExpr.Ident op -> Some op.idText
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) -> Some op.idText
        | _ -> None

    fun (u: FSharpSymbolUse) ->
        let key = u.Range.StartLine, u.Range.StartColumn

        match constructionRhs.TryGetValue key with
        | true, Some rhs -> constructionEdit rhs
        | true, None -> None
        | _ ->
            match nodeAt u.Range with
            | None -> None
            | Some(path, access) ->
                // r.Seen.Year — the parity member rides the same LongIdent
                let viaParityMember =
                    match access with
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                        let last = (List.last ids).idText
                        parityMembers.Contains last && last <> fieldName
                    | _ -> false

                if viaParityMember then
                    Some([], [])
                else
                    match path with
                    | SyntaxNode.SynExpr(SynExpr.DotGet(longDotId = SynLongIdent(id = [ m ]))) :: _ when
                        parityMembers.Contains m.idText
                        ->
                        Some([], [])
                    // a.Seen < b.Seen / a.Seen - b.Seen: both operands
                    // migrate together, so the comparison stays sound
                    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = opE; argExpr = lhs)) :: rest when
                        (opName opE |> Option.exists comparisonOps.Contains)
                        && Range.equals (stripParens lhs).Range (stripParens access).Range
                        ->
                        (match rest with
                         | SyntaxNode.SynExpr(SynExpr.App(argExpr = rhs)) :: _ when isSameFieldRead rhs -> Some([], [])
                         | _ -> None)
                    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = opE; argExpr = lhs))) :: _ when
                        (opName opE |> Option.exists comparisonOps.Contains) && isSameFieldRead lhs
                        ->
                        Some([], [])
                    | _ -> None

/// The single-file edit set, or None when any use escapes the envelope.
let migrate
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (s: Suggestion)
    : (range * string * string) list option =
    if OptionModule.hasErrors check then
        None
    else
        let symbol =
            let lineText = source.GetLineString(s.FieldIdRange.EndLine - 1)

            match
                check.GetSymbolUseAtLocation(
                    s.FieldIdRange.EndLine,
                    s.FieldIdRange.EndColumn,
                    lineText,
                    [ s.FieldName ]
                )
            with
            | Some symbolUse ->
                match symbolUse.Symbol with
                // the field must REALLY be System.DateTime — a user-defined
                // DateTime type would take the rewrite syntactically and
                // break, with no build net on the editor path
                | :? FSharpField as f when
                    (try
                        f.FieldType.StripAbbreviations().TypeDefinition.TryFullName = Some "System.DateTime"
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                    ->
                    Some(f :> FSharpSymbol)
                | _ -> None
            | None -> None

        match symbol with
        | None -> None
        | Some symbol ->
            let uses =
                check.GetUsesOfSymbolInFile symbol
                |> Array.filter (fun u -> not u.IsFromDefinition)

            // containment, not start-equality: a use range can cover the
            // qualifier (`b.Seen`), while the classifier asks about the
            // field ident's own position
            let isFieldUseAt (line: int, col: int) =
                let pos = Position.mkPos line col
                uses |> Array.exists (fun u -> Range.rangeContainsPos u.Range pos)

            let isSystemDateTimeIdent (names: string list) (id: Ident) =
                let lineText = source.GetLineString(id.idRange.EndLine - 1)

                match check.GetSymbolUseAtLocation(id.idRange.EndLine, id.idRange.EndColumn, lineText, names) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpEntity as e ->
                        (try
                            e.TryFullName = Some "System.DateTime"
                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                             false)
                    | _ -> false
                | None -> false

            let classify =
                classifierFor s.FieldName isFieldUseAt isSystemDateTimeIdent parseTree source

            let classified = uses |> Array.map classify

            if classified.Length > 0 && classified |> Array.forall Option.isSome then
                let editSets = classified |> Array.toList |> List.collect (Option.get >> fst)
                let sources = classified |> Array.toList |> List.collect (Option.get >> snd)

                let clocks = sources |> List.filter (fun c -> c <> "neutral") |> List.distinct

                // at least one real write pins the clock; mixed clocks bail
                if clocks.Length = 1 then
                    let typeEdit = s.TypeNameRange, "DateTime", "DateTimeOffset"
                    let seen = System.Collections.Generic.HashSet<int * int>()

                    typeEdit :: editSets
                    |> List.filter (fun (r, _, _) -> seen.Add(r.StartLine, r.StartColumn))
                    |> Some
                else
                    None
            else
                None
