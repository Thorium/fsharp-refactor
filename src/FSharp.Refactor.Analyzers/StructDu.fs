/// Refactoring (performance): mark a small discriminated union with
/// [<Struct>], avoiding a heap allocation per value.
///
///     type Shape =                       [<Struct>]
///         | Circle of radius: float      type Shape =
///         | Square of side: float            | Circle of radius: float
///                                            | Square of side: float
///
/// A struct union is a different kind of value from a class union: it is
/// copied rather than referenced and can never be null. Consumers inside
/// the assembly get compiler errors if that matters to them; consumers
/// outside get silently different semantics. So — like its record sibling
/// FR0070 — this fires only on unions invisible outside the assembly,
/// unless the caller opted in with `--api-changes`.
///
/// Safety rules (struct DUs have real language constraints, so only clearly
/// safe unions are suggested):
///   - module-level, attribute-free type definition with 2–3 cases
///   - private/internal, or nested in a private/internal module, unless
///     API changes were allowed
///   - every case field's type is a whitelisted small immutable value type
///     (int, float, bool, char, byte, int64, decimal, Guid, DateTime, ...)
///     written as a plain identifier — no strings (reference type is fine in
///     a struct DU but signals a bigger payload), no generics, no options,
///     no recursion by construction
///   - when more than one case carries fields, all fields must be named
///     (unnamed fields collide on the compiled ItemN names in struct unions)
module FSharp.Refactor.StructDu

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The type name, for the message.
        TypeName: string
        /// Zero-width insertion point before the type declaration.
        InsertRange: range
        /// The attribute line plus re-indentation.
        InsertText: string
        /// The companion signature's half: the same attribute above the
        /// `type` it declares (see SignatureFile).
        SignatureEdits: SignatureFile.Edit list
    }

let private smallValueTypes =
    set
        [
            "int"
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
            "single"
            "double"
            "decimal"
            "bool"
            "char"
            "nativeint"
            "unativeint"
            "Guid"
            "DateTime"
            "DateTimeOffset"
            "TimeSpan"
        ]

let private isSmallValueType (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) -> smallValueTypes.Contains (List.last ids).idText
    | _ -> false

/// Find small module-level unions that can carry [<Struct>].
let find (allowApiChanges: bool) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    // the companion signature is carried along: its `type` gains the same
    // attribute in the same edit set, or — where it cannot be read — every
    // fix in the file is withheld
    let signature = SignatureFile.read parseTree.FileName

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(path, decl) =
                match decl with
                | SynModuleDecl.Types(
                    typeDefns = [ SynTypeDefn(
                                      typeInfo = SynComponentInfo(
                                          attributes = []; longId = [ typeName ]; accessibility = typeAccess)
                                      typeRepr = SynTypeDefnRepr.Simple(
                                          simpleRepr = SynTypeDefnSimpleRepr.Union(unionCases = cases); range = _)
                                      members = []) ]) when
                    cases.Length >= 2
                    && cases.Length <= 3
                    // only the TYPE's own visibility counts: a private
                    // representation still leaves a public class-vs-struct
                    // type visible to consumers
                    && Visibility.isInScopeWithSignatureEdits allowApiChanges path [ typeAccess ]
                    ->
                    let caseFields =
                        cases
                        |> List.map (fun (SynUnionCase(caseType = caseType)) ->
                            match caseType with
                            | SynUnionCaseKind.Fields fields -> Some fields
                            | SynUnionCaseKind.FullType _ -> None)

                    match List.fold (fun acc f -> Option.map2 (fun a b -> b :: a) acc f) (Some []) caseFields with
                    | None -> ()
                    | Some allFields ->
                        let fieldLists = List.rev allFields
                        let fields = List.concat fieldLists

                        let allSmall =
                            fields
                            |> List.forall (fun (SynField(fieldType = t; isMutable = m)) -> not m && isSmallValueType t)

                        let casesWithFields =
                            fieldLists |> List.filter (fun fs -> not fs.IsEmpty) |> List.length

                        let allNamed = fields |> List.forall (fun (SynField(idOpt = idOpt)) -> idOpt.IsSome)

                        let namingOk = casesWithFields <= 1 || allNamed

                        // FS3585: in a struct DU, same-named fields across
                        // cases must also agree on TYPE — `A of value: float`
                        // plus `B of value: int` refuses to compile once the
                        // attribute lands. Spelled-type comparison suffices:
                        // the small-value whitelist keeps types to plain names
                        let sameNameSameType =
                            casesWithFields <= 1
                            || fields
                               |> List.choose (fun (SynField(idOpt = idOpt; fieldType = t)) ->
                                   idOpt |> Option.map (fun id -> id.idText, textOfRange source t.Range))
                               |> List.groupBy fst
                               |> List.forall (fun (_, group) ->
                                   group |> List.map snd |> List.distinct |> List.length <= 1)

                        if not fields.IsEmpty && allSmall && namingOk && sameNameSameType then
                            // below any XML doc, so the attribute sits
                            // against the type it marks
                            let insertPos = attributeInsertPos source decl.Range
                            let indent = String(' ', insertPos.Column)

                            let declaredPrivately = Visibility.isPrivate path [ typeAccess ]

                            match SignatureFile.structEdits declaredPrivately signature typeName.idText with
                            | ValueSome signatureEdits ->
                                suggestions.Add
                                    {
                                        TypeName = typeName.idText
                                        InsertRange = Range.mkRange decl.Range.FileName insertPos insertPos
                                        InsertText = "[<Struct>]\n" + indent
                                        SignatureEdits = signatureEdits
                                    }
                            | ValueNone -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
