/// Refactoring (FR0145, fix): a record expression that leaves fields
/// unassigned does not compile (FS0764); the fix adds the missing fields,
/// each with the default its type makes obvious, or a placeholder that
/// reports itself.
///
///     { Name = "x"; Retries = 3 }      →      { Name = "x"; Retries = 3; Tags = []; Timeout = None }
///
/// The compiler names the gap exactly — `No assignment given for field
/// 'UseKvCache' of type 'Fuuga.OnnxExport.OnnxExportConfig'` — and the
/// record's own field labels resolve to the type even while the
/// expression is incomplete, so the missing fields and their types are
/// read off the typed tree. A record that gained a field after its
/// constructions were written is exactly this shape (Fuuga's examples).
///
/// The default follows the field's type: `None` / `ValueNone` for an
/// option, `[]`, `[||]`, `Map.empty`, `Set.empty`, `Seq.empty` for a
/// collection, `()` for unit. Those are the empty values the field would
/// have had before it existed, and they are applied. Anything else — a
/// bool, a number, a string, a record — is a decision: it gets
/// `raise (System.NotImplementedException "Field")`, which compiles and
/// fails the moment the record is built, so the TODO cannot be missed.
/// The apply tool never auto-applies a placeholder (unlike a member stub,
/// it fires on construction, not on a call); the editor offers it.
///
/// Like FR0077, this runs ONLY on files with type errors — that is its
/// input — and only where FS0764 sits on the record expression.
///
/// Safety rules:
///   - the record is a construction, not a copy-and-update (`{ r with }`
///     needs no completeness)
///   - at least one field is assigned, so a label resolves the type and
///     the layout has an anchor
///   - the entity resolves to an F# record whose fields are readable
module FSharp.Refactor.RecordFields

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Zero-width, after the last assigned field.
        Range: range
        /// The missing fields with their obvious defaults, placeholders
        /// where none is obvious.
        InsertText: string
        /// The same fields with zero values instead of placeholders: the
        /// literal zero for a primitive (`false`, `0`, `0.0`, `0m`),
        /// `Unchecked.defaultof<_>` for anything else — the editor's
        /// second offer, never the apply tool's
        ZeroInsertText: string
        /// True when every missing field got an obvious default: the
        /// apply tool may take this one.
        AllObvious: bool
        TypeName: string
        Missing: string list
    }

let private assignedNames (fields: SynExprRecordField list) =
    fields
    |> List.choose (fun (SynExprRecordField(fieldName = (SynLongIdent(id = ids), _))) ->
        if ids.IsEmpty then None else Some (List.last ids).idText)
    |> Set.ofList

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if not (OptionModule.hasErrors check) then
        []
    else
        // only records the compiler itself flagged as incomplete
        let incomplete =
            check.Diagnostics
            |> Array.filter (fun d -> d.ErrorNumber = 764)
            |> Array.map (fun d -> d.Range)

        if incomplete.Length = 0 then
            []
        else
            let index = AstIndex.ofTree parseTree

            [
                for _, expr in index.Exprs do
                    match expr with
                    | SynExpr.Record(copyInfo = None; recordFields = fields) when
                        not fields.IsEmpty
                        && incomplete |> Array.exists (fun r -> Range.rangeContainsRange expr.Range r)
                        ->
                        // the first label resolves the record type even while
                        // the expression is incomplete
                        let firstLabel =
                            fields
                            |> List.tryPick (fun (SynExprRecordField(fieldName = (SynLongIdent(id = ids), _))) ->
                                if ids.IsEmpty then None else Some(List.last ids))

                        let entity =
                            firstLabel
                            |> Option.bind (fun id ->
                                let r = id.idRange
                                let lineText = source.GetLineString(r.EndLine - 1)

                                match
                                    check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
                                with
                                | Some symbolUse ->
                                    match symbolUse.Symbol with
                                    | :? FSharpField as f -> f.DeclaringEntity
                                    | _ -> None
                                | None -> None)

                        match entity with
                        | Some entity when entity.IsFSharpRecord ->
                            let assigned = assignedNames fields

                            let missing =
                                [
                                    for f in entity.FSharpFields do
                                        if not (assigned.Contains f.Name) then
                                            yield
                                                f.Name,
                                                TypeDefaults.obviousDefault f.FieldType,
                                                TypeDefaults.zeroDefault f.FieldType
                                ]

                            if not missing.IsEmpty then
                                // layout follows the last assigned field: on
                                // its own line, the new ones go one per line
                                // at its column; inline, they follow with `;`
                                let (SynExprRecordField(fieldName = (SynLongIdent(id = lastIds), _); expr = lastExpr)) =
                                    List.last fields

                                let lastLabel = List.last lastIds

                                let lastEnd =
                                    match lastExpr with
                                    | Some e -> e.Range.End
                                    | None -> lastLabel.idRange.End

                                let multiLine =
                                    fields.Length = 1 && expr.Range.StartLine <> lastLabel.idRange.StartLine
                                    || fields.Length > 1
                                       && (let (SynExprRecordField(fieldName = (SynLongIdent(id = firstIds), _))) =
                                               List.head fields

                                           (List.last firstIds).idRange.StartLine <> lastLabel.idRange.StartLine)

                                let layout (entries: string list) =
                                    if multiLine then
                                        let indent = String.replicate lastLabel.idRange.StartColumn " "
                                        entries |> List.map (fun e -> "\n" + indent + e) |> String.concat ""
                                    else
                                        entries |> List.map (fun e -> "; " + e) |> String.concat ""

                                let placeholders =
                                    missing
                                    |> List.map (fun (name, obvious, _) ->
                                        let value =
                                            match obvious with
                                            | Some d -> d
                                            | None -> $"raise (System.NotImplementedException \"{name}\")"

                                        $"{name} = {value}")

                                let zeros =
                                    missing
                                    |> List.map (fun (name, obvious, zero) ->
                                        let value =
                                            match obvious with
                                            | Some d -> d
                                            | None -> zero

                                        $"{name} = {value}")

                                yield
                                    {
                                        Range = Range.mkRange expr.Range.FileName lastEnd lastEnd
                                        InsertText = layout placeholders
                                        ZeroInsertText = layout zeros
                                        AllObvious = missing |> List.forall (fun (_, d, _) -> d.IsSome)
                                        TypeName = entity.DisplayName
                                        Missing = missing |> List.map (fun (n, _, _) -> n)
                                    }
                        | _ -> ()
                    | _ -> ()
            ]
