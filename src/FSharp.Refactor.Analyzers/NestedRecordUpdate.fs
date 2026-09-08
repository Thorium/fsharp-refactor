/// Refactoring (modernization, F# 8): updating a nested record field no
/// longer needs a copy-and-update per level.
///
///     { r with X = { r.X with Y = v } }        →  { r with X.Y = v }
///     { r with X = { r.X with Y = v; Z = w } } →  { r with X.Y = v; X.Z = w }
///
/// and recursively for deeper chains rooted at the same source.
///
/// Safety rules:
///   - the inner copy source must be exactly the outer source extended by
///     the field's own path (`r` → `r.X`), compared ident-by-ident — any
///     other source is a genuine cross-record copy and stays
///   - every flattened value is single-line (the values splice verbatim
///     into a `;`-joined field list)
///   - the path head must not collide with a TYPE name: in the flattened
///     syntax `{ r with Config.Value = v }`, a type named Config in scope
///     wins resolution over the field and the fix would not compile — the
///     `{ Config: Config }` field-named-after-its-type pattern is common,
///     so the field's own type name (typed check results) and every type
///     declared in the file are both checked
///   - the rule only reports when the project's language version allows
///     the syntax (gated at registration); no edit crosses a directive
module FSharp.Refactor.NestedRecordUpdate

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.EditorServices
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The nested field being flattened (fix replaces this range).
        Range: range
        OriginalText: string
        ReplacementText: string
        /// e.g. "X.Y" for the message.
        Path: string
    }

/// The ident texts of a bare or dotted identifier expression.
let private identPath (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> Some [ id.idText ]
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some(ids |> List.map (fun i -> i.idText))
    | _ -> None

/// A flattened field: its dotted path, its value, and the line its name
/// was written on — the line structure of the original is kept.
type private Leaf =
    { Path: string
      Value: SynExpr
      Line: int }

/// Flatten record fields into (dotted-path, value-expr) leaves, walking
/// nested copy-and-updates whose source matches `basePath` + the field
/// path. Returns None when any part is not flattenable.
[<TailCall>]
let rec private flattenLoop
    (basePath: string list)
    (acc: Leaf list)
    (pending: (string list * SynExprRecordField) list)
    : Leaf list option =
    match pending with
    | [] -> Some(List.rev acc)
    | (prefix, field) :: rest ->
        match field with
        | SynExprRecordField(fieldName = (SynLongIdent(id = fieldIds), _); expr = Some value) when not fieldIds.IsEmpty ->
            let fieldPath = prefix @ (fieldIds |> List.map (fun i -> i.idText))

            match value with
            | SynExpr.Record(copyInfo = Some(innerBase, _); recordFields = innerFields) when
                identPath innerBase = Some(basePath @ fieldPath) && not innerFields.IsEmpty
                ->
                flattenLoop basePath acc ((innerFields |> List.map (fun f -> fieldPath, f)) @ rest)
            | _ when isSingleLine value.Range ->
                let leaf =
                    { Path = String.concat "." fieldPath
                      Value = value
                      Line = (List.head fieldIds).idRange.StartLine }

                flattenLoop basePath (leaf :: acc) rest
            | _ -> None
        | _ -> None

let private flattenField (basePath: string list) (field: SynExprRecordField) = flattenLoop basePath [] [ [], field ]

/// The display name of the field's own type, resolved at the field ident.
let private fieldTypeName (check: FSharpCheckFileResults) (source: ISourceText) (fieldId: Ident) =
    let r = fieldId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ fieldId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpField as field ->
            try
                let t = field.FieldType

                if t.HasTypeDefinition then
                    Some t.TypeDefinition.DisplayName
                else
                    None
            with OptionModule.FcsSymbolFailure ->
                None
        | _ -> None
    | None -> None

/// Does the path head name a MODULE, NAMESPACE or TYPE in scope at the
/// record expression — anything F# would resolve ahead of the field?
///
/// `{ menu with Settings.RandomCardBacks = v }` is fine while `Settings` is
/// only a field. Nu's Kasino declares the field as `Settings:
/// Settings.GameSettings` — named after the module holding its type, which
/// lives in another file — and the flattened path resolved as the module's
/// qualification of a GameSettings field: "This expression was expected to
/// have type 'Menu' but here has type 'Settings.GameSettings'", five times,
/// rolled back. The type names declared in this file and the field's own
/// type cannot see that; the names in scope at the expression can. Read
/// from the completion list at the copy source, where the context is a
/// plain expression rather than a field list.
///
/// The completion list is the expensive part — it cost this rule 735ms
/// over a 19-file sweep, more than any other analyzer — and within one
/// module-level declaration nothing can change which modules and types
/// are in scope, so the answer is memoised per (name, declaration): Nu's
/// five sites in one `update` function are one lookup.
let private headIsEntityInScope
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (memo: System.Collections.Generic.Dictionary<string * pos, bool>)
    (path: SyntaxNode list)
    (outerBase: SynExpr)
    (head: string)
    =
    let declaration =
        path
        |> List.tryPick (fun node ->
            match node with
            | SyntaxNode.SynModule decl -> Some decl.Range.Start
            | _ -> None)
        |> Option.defaultValue outerBase.Range.Start

    match memo.TryGetValue((head, declaration)) with
    | true, known -> known
    | _ ->
        let collides =
            try
                let at = outerBase.Range.End
                let lineText = source.GetLineString(at.Line - 1)

                check.GetDeclarationListSymbols(
                    None,
                    at.Line,
                    lineText,
                    PartialLongName.Empty at.Column,
                    (fun () -> [])
                )
                |> List.exists (fun group ->
                    group
                    |> List.exists (fun symbolUse ->
                        match symbolUse.Symbol with
                        | :? FSharpEntity as entity -> entity.DisplayName = head
                        | _ -> false))
            with _ -> // a scope we cannot read is one we do not rewrite in; fsharpanalyzer: ignore-line FR0055
                true

        memo.[(head, declaration)] <- collides
        collides

/// Find flattenable nested copy-and-updates. Requires typed check results
/// for the name collision gate; the language version gate lives in the
/// registration.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // type names declared in this file: a path head naming one of them
    // would resolve as the type, not the field
    let fileTypeNames =
        index.Decls
        |> Array.collect (fun (_, decl) ->
            match decl with
            | SynModuleDecl.Types(typeDefns = defns) ->
                defns
                |> List.choose (fun (SynTypeDefn(typeInfo = SynComponentInfo(longId = ids))) ->
                    ids |> List.tryLast |> Option.map (fun i -> i.idText))
                |> Array.ofList
            | _ -> [||])
        |> Set.ofArray

    let scopeMemo = System.Collections.Generic.Dictionary<string * pos, bool>()

    [ for path, expr in index.Exprs do
          match expr with
          | SynExpr.Record(copyInfo = Some(outerBase, _); recordFields = fields) ->
              match identPath outerBase with
              | Some basePath ->
                  for field in fields do
                      match field with
                      // only fields whose value IS a nested copy-and-update
                      // are rewritten; sibling plain fields stay untouched
                      | SynExprRecordField(
                          fieldName = (SynLongIdent(id = fieldIds), _)
                          expr = Some(SynExpr.Record(copyInfo = Some _) as value)) when not fieldIds.IsEmpty ->
                          match flattenField basePath field with
                          // a leaf without a dot means the inner source did
                          // not match — a genuine cross-record copy, no gain
                          | Some leaves when
                              not leaves.IsEmpty
                              && leaves |> List.exists (fun leaf -> leaf.Path.Contains '.')
                              // collision gate: the path head must not name
                              // a type, module or namespace
                              && (let head = (List.head fieldIds).idText

                                  not (fileTypeNames.Contains head)
                                  && fieldTypeName check source (List.head fieldIds) <> Some head
                                  && not (headIsEntityInScope check source scopeMemo path outerBase head))
                              ->
                              let fieldStart = (List.head fieldIds).idRange.Start

                              let editRange = Range.mkRange value.Range.FileName fieldStart value.Range.End

                              // the original's line structure survives: a
                              // field that started a new line starts one
                              // here too, at the outer field's column, and
                              // fields that shared a line still do. Joining
                              // everything with `; ` made a 170-column line
                              // of suave's Stream.fs — correct, and rejected
                              // by fantomas --check.
                              let indent = System.String(' ', fieldStart.Column)

                              let replacement =
                                  leaves
                                  |> List.mapi (fun i leaf ->
                                      let text = $"{leaf.Path} = {textOfRange source leaf.Value.Range}"

                                      if i = 0 then
                                          text
                                      elif leaf.Line > leaves.[i - 1].Line then
                                          $"\n{indent}{text}"
                                      else
                                          "; " + text)
                                  |> String.concat ""

                              if not (spansDirective source editRange) then
                                  { Range = editRange
                                    OriginalText = textOfRange source editRange
                                    ReplacementText = replacement
                                    Path = leaves |> List.map (fun leaf -> leaf.Path) |> String.concat ", " }
                          | _ -> ()
                      | _ -> ()
              | None -> ()
          | _ -> () ]
    // outermost wins: an inner copy-update also matches as its own outer,
    // but its rewrite is subsumed by the enclosing suggestion
    |> fun all ->
        all
        |> List.filter (fun s ->
            not (
                all
                |> List.exists (fun outer ->
                    not (obj.ReferenceEquals(outer, s))
                    && Range.rangeContainsRange outer.Range s.Range)
            ))
