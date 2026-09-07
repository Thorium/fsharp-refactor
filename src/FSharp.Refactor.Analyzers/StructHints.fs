/// Three allocation hints for CONTAINED types, in the spirit of
/// https://www.bartoszsypytkowski.com/writing-high-performance-f-code/ :
///
/// 1. voption fields (FR0069): a private/internal record field typed
///    `int option` / `DateTime option` / `Guid option` heap-allocates a
///    Some box around a struct payload; `voption` (ValueOption) keeps the
///    value flat in the record.
///
/// 2. Small struct types (FR0070): a private/internal record whose fields
///    are all small structs (four fields at most) can carry [<Struct>],
///    removing one heap allocation per instance.
///
/// 3. Struct tuple fields (FR0093): a field typed `int * int` is a
///    System.Tuple — a heap object per value — while `struct (int * int)`
///    is a ValueTuple stored inline, in the same spirit as 1.
///
/// Both are deliberately gated to private/internal types — declared so, or
/// living inside a private/internal module. For a PUBLIC type the
/// migration is much bigger than the type itself: serialized shapes may
/// change, and the signature ripples into an unbounded amount of call-site
/// refactoring. Contained visibility keeps the blast radius in one file or
/// one assembly. See Visibility.isInScope: `--api-changes` opts into the
/// public case deliberately.
module FSharp.Refactor.StructHints

open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type VOptionFieldSuggestion =
    {
        Range: range
        FieldName: string
        /// The struct payload's type text, e.g. "int".
        ElementText: string
        TypeName: string
        /// The field's defining ident, for symbol resolution.
        FieldIdRange: range
        /// The `option`/`Option` type name itself — the type edit's target.
        OptionNameRange: range
        /// Strictly file-private (own modifier or a private enclosing
        /// module): every use lives in this file, so the migration can be
        /// a single-file fix.
        IsFilePrivate: bool
        /// Confined to the assembly (private or internal, directly or via
        /// the enclosing module) — the widest scope a cross-file migration
        /// may touch: a PUBLIC field's consumers can live in a sibling
        /// project no scan sees.
        IsConfined: bool
    }

type StructTypeSuggestion =
    {
        Range: range
        TypeName: string
        FieldCount: int
        /// Zero-width insert point and the attribute line to put there —
        /// present when the definition heads its decl (`type`, not `and`)
        /// and carries no other attributes to interfere with.
        Fix: (range * string) option
    }

type StructTupleFieldSuggestion =
    {
        Range: range
        FieldName: string
        /// The tuple's own source text, e.g. "int * int".
        TupleText: string
        TypeName: string
        /// The field's defining ident, for symbol resolution.
        FieldIdRange: range
        /// Strictly file-private (own modifier or a private enclosing
        /// module): every use lives in this file, so the migration can be
        /// a single-file fix.
        IsFilePrivate: bool
        /// Confined to the assembly — see VOptionFieldSuggestion.
        IsConfined: bool
    }

/// Well-known struct types by (last) name — the primitives plus the
/// common BCL value types the article calls out.
let private structNames =
    set
        [ "int"
          "int8"
          "int16"
          "int32"
          "int64"
          "uint"
          "uint8"
          "uint16"
          "uint32"
          "uint64"
          "byte"
          "sbyte"
          "float"
          "float32"
          "double"
          "single"
          "decimal"
          "bool"
          "char"
          "nativeint"
          "unativeint"
          "DateTime"
          "DateTimeOffset"
          "TimeSpan"
          "Guid" ]

let private lastIdentText (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idText
    | _ -> None

/// A type whose name is a known struct.
let private isKnownStruct (t: SynType) =
    lastIdentText t |> Option.exists structNames.Contains

/// `<struct> option`, in postfix or prefix form. Yields the payload type
/// and the option TYPE NAME's own range (the migration's type edit).
[<return: Struct>]
let private (|StructOption|_|) (t: SynType) =
    match t with
    | SynType.App(typeName = name; typeArgs = [ elem ]) when
        (lastIdentText name = Some "option" || lastIdentText name = Some "Option")
        && isKnownStruct elem
        ->
        ValueSome(elem, name.Range)
    | _ -> ValueNone

/// A reference tuple of a handful of known structs: `int * int`.
///
/// Capped at four elements: a struct tuple is copied by value, so past a
/// few small fields the copying costs more than the allocation it saves.
/// Already-struct tuples are left alone, as are tuples carrying a `/`
/// segment (units of measure), where the segments are not plain elements.
[<return: Struct>]
let private (|SmallStructTuple|_|) (t: SynType) =
    match t with
    | SynType.Tuple(isStruct = false; path = segments) when
        segments
        |> List.forall (function
            | SynTupleTypeSegment.Slash _ -> false
            | SynTupleTypeSegment.Type _
            | SynTupleTypeSegment.Star _ -> true)
        ->
        let elements =
            segments
            |> List.choose (function
                | SynTupleTypeSegment.Type element -> Some element
                | SynTupleTypeSegment.Star _
                | SynTupleTypeSegment.Slash _ -> None)

        if
            elements.Length >= 2
            && elements.Length <= 4
            && elements |> List.forall isKnownStruct
        then
            ValueSome elements
        else
            ValueNone
    | _ -> ValueNone

/// A field type that already lives flat: a known struct, or a voption of one.
let private isStructField (t: SynType) =
    isKnownStruct t
    || (match t with
        | SynType.App(typeName = name; typeArgs = [ elem ]) when
            (lastIdentText name = Some "voption" || lastIdentText name = Some "ValueOption")
            && isKnownStruct elem
            ->
            true
        | _ -> false)

/// Find all three hint kinds. Parse-only.
let find
    (allowApiChanges: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : VOptionFieldSuggestion list * StructTypeSuggestion list * StructTupleFieldSuggestion list =
    let index = AstIndex.ofTree parseTree
    let voptions = ResizeArray<VOptionFieldSuggestion>()
    let structs = ResizeArray<StructTypeSuggestion>()
    let structTuples = ResizeArray<StructTupleFieldSuggestion>()

    // quotations in this file: `<@ @>`, `<@@ @@>` and `query { }` blocks.
    // A struct local captured inside one cannot have a field read — that
    // takes its address, which a quotation may not do — so a record whose
    // fields are read in a quotation stays a class (Linq.Expression.
    // Optimizer's `query { ... fun sl -> sl.x = j.x ... }`)
    let quotationRanges = AstIndex.quotationRanges parseTree

    let fieldsReadInQuotation (fieldNames: Set<string>) =
        not quotationRanges.IsEmpty
        && index.Exprs
           |> Seq.exists (fun (_, e) ->
               quotationRanges |> List.exists (fun q -> Range.rangeContainsRange q e.Range)
               && (match e with
                   | SynExpr.DotGet(longDotId = SynLongIdent(id = ids))
                   | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                       ids.Length >= 2 && fieldNames.Contains (List.last ids).idText
                   | SynExpr.Record(recordFields = recordFields) ->
                       recordFields
                       |> List.exists (fun (SynExprRecordField(fieldName = (SynLongIdent(id = ids), _))) ->
                           not ids.IsEmpty && fieldNames.Contains (List.last ids).idText)
                   | _ -> false))

    for path, decl in index.Decls do
        match decl with
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeInfo = info; typeRepr = repr; trivia = defnTrivia) in defns do
                let (SynComponentInfo(attributes = attrs; longId = typeIds; accessibility = access)) =
                    info

                let typeName = typeIds |> List.map (fun i -> i.idText) |> String.concat "."

                match repr with
                | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Record(recordFields = fields)) when
                    Visibility.isInScopeNamedPath allowApiChanges path [ access ] typeIds
                    ->
                    // strictly file-private: its own modifier, or a private
                    // enclosing module — then every use is in this file and
                    // the voption migration can be a single-file fix
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

                    // FR0069: struct payloads boxed in option fields
                    // FR0093: struct payloads boxed in a reference tuple
                    for SynField(idOpt = idOpt; fieldType = fieldType) in fields do
                        match fieldType, idOpt with
                        | StructOption(elem, optionNameRange), Some fieldId ->
                            voptions.Add
                                { Range = fieldType.Range
                                  FieldName = fieldId.idText
                                  ElementText = textOfRange source elem.Range
                                  TypeName = typeName
                                  FieldIdRange = fieldId.idRange
                                  OptionNameRange = optionNameRange
                                  IsFilePrivate = isFilePrivate
                                  IsConfined = Visibility.isConfined path [ access ] }
                        | SmallStructTuple _, Some fieldId ->
                            structTuples.Add
                                { Range = fieldType.Range
                                  FieldName = fieldId.idText
                                  TupleText = textOfRange source fieldType.Range
                                  TypeName = typeName
                                  FieldIdRange = fieldId.idRange
                                  IsFilePrivate = isFilePrivate
                                  IsConfined = Visibility.isConfined path [ access ] }
                        | _ -> ()

                    // FR0070: a small all-struct record can be a struct itself
                    let alreadyStruct = hasAttributeNamed "Struct" attrs

                    let allStructFields =
                        fields
                        |> List.forall (fun (SynField(fieldType = t; isMutable = m)) -> not m && isStructField t)

                    if
                        not alreadyStruct
                        && not fields.IsEmpty
                        && fields.Length <= 4
                        && allStructFields
                        && not typeIds.IsEmpty
                    then
                        // the fix: `[<Struct>]` on its own line above the
                        // `type` keyword (below any /// doc by position).
                        // All fields are immutable small structs, so copies
                        // are semantically invisible; an `and`-position
                        // definition or existing attributes (CLIMutable
                        // would conflict outright) keep it advice
                        let fieldNames =
                            fields
                            |> List.choose (fun (SynField(idOpt = idOpt)) -> idOpt |> Option.map (fun i -> i.idText))
                            |> Set.ofList

                        let attributeFix =
                            match defnTrivia.LeadingKeyword with
                            | SynTypeDefnLeadingKeyword.Type kwRange when
                                attrs.IsEmpty
                                && not (fieldsReadInQuotation fieldNames)
                                && (source.GetLineString(kwRange.StartLine - 1))
                                    .Substring(0, kwRange.StartColumn)
                                    .Trim() = ""
                                ->
                                let at = Position.mkPos kwRange.StartLine 0
                                let indent = String.replicate kwRange.StartColumn " "

                                Some(Range.mkRange decl.Range.FileName at at, $"{indent}[<Struct>]\n")
                            | _ -> None

                        structs.Add
                            { Range = (List.last typeIds).idRange
                              TypeName = typeName
                              FieldCount = fields.Length
                              Fix = attributeFix }
                | _ -> ()
        | _ -> ()

    List.ofSeq voptions, List.ofSeq structs, List.ofSeq structTuples
