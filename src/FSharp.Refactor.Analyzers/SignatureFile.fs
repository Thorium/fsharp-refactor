/// The companion signature file, read and edited IN STEP with a rewrite
/// that changes a declaration's compiled shape.
///
/// A `.fsi` must agree with its `.fs` on everything it declares: the
/// attribute on a type or a value, a literal's value, a binding's name. A
/// rule that changes one of those on the implementation side alone leaves
/// "the names differ" or "the attributes differ", and the project stops
/// compiling — fcs-fable, which carries 176 signature files, found this for
/// FR0022, FR0069, FR0093 and FR0130 in one sweep. FR0022 answered by
/// editing the signature's union case alongside the implementation's, one
/// atomic edit set spanning both files; this module is that answer shared,
/// so FR0130 (`[<Literal>]`), FR0133 (a rename) and FR0016 (`[<Struct>]`)
/// carry their signature with them too.
///
/// The signature is parsed through the host-installed cross-file parser:
/// the CLI installs one, editors do not, and where it is missing a fix that
/// needs the signature is WITHHELD rather than offered half-done.
module FSharp.Refactor.SignatureFile

open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// One edit: the range to replace, the text there now, the text to put.
type Edit = range * string * string

type Reading =
    /// No companion signature; nothing to keep in step.
    | Absent
    /// A signature exists but cannot be read here — editors install no
    /// cross-file parser — so a fix that needs it cannot be completed.
    | Unreadable
    /// The signature's tree, with its own source for rendering edits.
    | Read of tree: ParsedInput * sigSource: ISourceText

/// Read the signature beside an implementation file, if there is one.
let read (implFile: string) =
    if not (hasSignatureFile implFile) then
        Absent
    else
        match ProjectSources.tryParse (System.IO.Path.ChangeExtension(implFile, ".fsi")) with
        | Some(tree, sigSource) -> Read(tree, sigSource)
        | None -> Unreadable

/// Every declaration of a signature, nested modules flattened.
let rec private flatten (decls: SynModuleSigDecl list) =
    decls
    |> List.collect (fun decl ->
        match decl with
        | SynModuleSigDecl.NestedModule(moduleDecls = inner) -> decl :: flatten inner
        | _ -> [ decl ])

let private declarations (tree: ParsedInput) =
    match tree with
    | ParsedInput.SigFile(ParsedSigFileInput(contents = modules)) ->
        modules
        |> List.collect (fun (SynModuleOrNamespaceSig(decls = decls)) -> flatten decls)
    | ParsedInput.ImplFile _ -> []

/// The `val` the signature declares under this name, if any. A name it
/// does not declare is hidden behind the signature — private to the
/// implementation — and needs no edit.
let private valNamed (tree: ParsedInput) (name: string) =
    declarations tree
    |> List.tryPick (fun decl ->
        match decl with
        | SynModuleSigDecl.Val(valSig = SynValSig(ident = SynIdent(ident = id)) as valSig) when id.idText = name ->
            Some valSig
        | _ -> None)

/// The type signature declared under this name, if any.
let private typeNamed (tree: ParsedInput) (name: string) =
    declarations tree
    |> List.tryPick (fun decl ->
        match decl with
        | SynModuleSigDecl.Types(types = types) ->
            types
            |> List.tryFind (fun (SynTypeDefnSig(typeInfo = SynComponentInfo(longId = ids))) ->
                not ids.IsEmpty && (List.last ids).idText = name)
        | _ -> None)

/// An attribute on its own line above a keyword that starts its line, at
/// the keyword's indentation — the same shape the implementation-side rules
/// emit. A keyword sharing its line with something else gets no edit: the
/// attribute would land in the middle of that line.
let private attributeAbove (sigSource: ISourceText) (keyword: range) (attribute: string) : Edit option =
    let ownLine =
        keyword.StartColumn = 0
        || (sigSource.GetLineString(keyword.StartLine - 1)).Substring(0, keyword.StartColumn).Trim() = ""

    if ownLine then
        let indent = String.replicate keyword.StartColumn " "
        let at = Position.mkPos keyword.StartLine 0
        Some(Range.mkRange keyword.FileName at at, "", $"{indent}{attribute}\n")
    else
        None

/// The signature's half of `[<Literal>]` on a module-level constant: the
/// attribute above the `val`, and the value the signature must then spell
/// out itself — `val x: int` becomes `[<Literal>] val x: int = 42`, and F#
/// checks that the two values agree.
///
/// ValueNone withholds the fix: the signature is unreadable, or declares
/// the value with attributes or a literal value of its own, which is not
/// the plain declaration this edit was written for.
///
/// A declaration that is PRIVATE never appears in a signature, so it needs
/// no edit and an unreadable signature is no reason to withhold it — the
/// editor channel, which installs no cross-file parser, keeps every
/// private fix this way.
let literalEdits (declaredPrivately: bool) (reading: Reading) (name: string) (valueText: string) : Edit list voption =
    match reading with
    | _ when declaredPrivately -> ValueSome []
    | Absent -> ValueSome []
    | Unreadable -> ValueNone
    | Read(tree, sigSource) ->
        match valNamed tree name with
        | None -> ValueSome []
        | Some(SynValSig(attributes = attributes; synType = synType; synExpr = literal; trivia = trivia)) ->
            if not attributes.IsEmpty || literal.IsSome then
                ValueNone
            else
                match trivia.LeadingKeyword with
                | SynLeadingKeyword.Val keyword ->
                    match attributeAbove sigSource keyword "[<Literal>]" with
                    | Some attribute ->
                        let after = Range.mkRange keyword.FileName synType.Range.End synType.Range.End
                        ValueSome [ attribute; (after, "", $" = {valueText}") ]
                    | None -> ValueNone
                | _ -> ValueNone

/// The signature's half of renaming a module-level binding: its `val`
/// takes the new spelling. The name must read in the signature exactly as
/// it does in the implementation; any other spelling is one this rewrite
/// does not understand.
let renameEdits (declaredPrivately: bool) (reading: Reading) (name: string) (replacement: string) : Edit list voption =
    match reading with
    | _ when declaredPrivately -> ValueSome []
    | Absent -> ValueSome []
    | Unreadable -> ValueNone
    | Read(tree, sigSource) ->
        match valNamed tree name with
        | None -> ValueSome []
        | Some(SynValSig(ident = SynIdent(ident = id))) ->
            let original = textOfRange sigSource id.idRange

            if original = name then
                ValueSome [ id.idRange, original, replacement ]
            else
                ValueNone

/// The signature's half of `[<Struct>]` on a type: the attribute above its
/// `type`. A type the signature declares with attributes of its own is
/// left alone — it may already be a struct, or carry something this edit
/// must not sit beside — and the fix is withheld.
let structEdits (declaredPrivately: bool) (reading: Reading) (typeName: string) : Edit list voption =
    match reading with
    | _ when declaredPrivately -> ValueSome []
    | Absent -> ValueSome []
    | Unreadable -> ValueNone
    | Read(tree, sigSource) ->
        match typeNamed tree typeName with
        | None -> ValueSome []
        | Some(SynTypeDefnSig(typeInfo = SynComponentInfo(attributes = attributes); trivia = trivia)) ->
            if not attributes.IsEmpty then
                ValueNone
            else
                match trivia.LeadingKeyword with
                | SynTypeDefnLeadingKeyword.Type keyword ->
                    match attributeAbove sigSource keyword "[<Struct>]" with
                    | Some attribute -> ValueSome [ attribute ]
                    | None -> ValueNone
                | _ -> ValueNone
