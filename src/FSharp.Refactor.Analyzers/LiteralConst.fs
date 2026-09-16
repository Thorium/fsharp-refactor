/// FR0130 (fix): a module-level constant binding gains
/// [<Literal>]:
///
///     let ConnectionName = "orders"      [<Literal>]
///                                    →   let ConnectionName = "orders"
///
/// A literal can be used in patterns and attribute arguments and is
/// const-folded at use sites. On by default: a sweep that leaves every
/// constant annotated is what its users came to expect, and a repository
/// that finds it churn turns it off in fsharprefactor.json. Contained (private/internal) bindings only
/// unless --api-changes: [<Literal>] compiles a public field to a CONST,
/// which is a binary-compatibility change.
module FSharp.Refactor.LiteralConst

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        Name: string
        /// Zero-width insert point (line start of the `let`) and the
        /// attribute line.
        Fix: range * string
        /// The companion signature's half: the attribute above its `val`
        /// and the literal value it must then spell out (see SignatureFile).
        SignatureEdits: SignatureFile.Edit list
    }

let private isConstant (e: SynExpr) =
    match e with
    | SynExpr.Const(c, _) ->
        match c with
        | SynConst.String(_, SynStringKind.Regular, _)
        | SynConst.String(_, SynStringKind.Verbatim, _)
        | SynConst.Int32 _
        | SynConst.Int64 _
        | SynConst.Byte _
        | SynConst.UInt32 _
        | SynConst.UInt64 _
        | SynConst.Char _
        | SynConst.Bool _
        | SynConst.Double _
        | SynConst.Single _ -> true
        | _ -> false
    | _ -> false

/// A simple value binder and its own access modifier — `let private X`
/// parks the modifier on the pattern, and an identifier can parse as
/// Named or a no-argument LongIdent.
let private valueBinder (p: SynPat) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id); accessibility = acc) -> ValueSome(id, acc)
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []; accessibility = acc) ->
        ValueSome(id, acc)
    | _ -> ValueNone

/// Names that appear as a bare identifier PATTERN anywhere in the tree.
/// `match s with | greeting -> ...` binds today; once `greeting` carries
/// [<Literal>] the same pattern MATCHES THE CONSTANT — it compiles, and
/// the behavior silently changes. Local `let greeting = ...` binders are
/// patterns too and would turn into partial matches (FS3190, an error,
/// for a lowercase literal). Either parse shape a lone identifier takes.
let private patternIdents (index: AstIndex.Index) =
    [
        for _, p in index.Pats do
            match p with
            | SynPat.Named(ident = SynIdent(ident = id))
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                id.idText, id.idRange
            | _ -> ()
    ]

/// The names ANOTHER file of the compilation binds as bare patterns — the
/// host's half of the cross-file veto (Analyzers.patternBoundInSibling):
/// `let lat = 13.067439` in TestData.fs and `let! lat = validLatR` in
/// Result.fs of the same project is FS3190 the moment `lat` is a literal.
let patternBoundNames (parseTree: ParsedInput) : Set<string> =
    patternIdents (AstIndex.ofTree parseTree) |> List.map fst |> Set.ofList

/// `find` with the cross-file question answered by the host: does any OTHER
/// source file of the compilation bind `name` as a bare pattern? Asked only
/// for a binding another file can see — a `private` one is invisible
/// outside its module, so its name cannot clash there. The host answers
/// "yes" for a sibling it cannot read (fail closed).
let findWith
    (boundAsPatternElsewhere: string -> bool)
    (allowApiChanges: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : Suggestion list =
    // the companion signature is carried along, not a reason to stand down:
    // its `val` gains the attribute and the literal value in the same edit
    // set, or — where it cannot be read — the fix is withheld
    let signature = SignatureFile.read parseTree.FileName

    match signature with
    | SignatureFile.Unreadable -> []
    | SignatureFile.Absent
    | SignatureFile.Read _ ->
        let index = AstIndex.ofTree parseTree

        // any same-named bare pattern in this file other than the
        // candidate's own binder vetoes the annotation
        let patternIdents = patternIdents index

        let vetoed (id: Ident) =
            patternIdents
            |> List.exists (fun (text, r) -> text = id.idText && not (Range.equals r id.idRange))

        [
            for path, decl in index.Decls do
                match decl with
                | SynModuleDecl.Let(isRecursive = false; bindings = [ binding ]) ->
                    match binding with
                    | SynBinding(
                        accessibility = access
                        attributes = []
                        isMutable = false
                        isInline = false
                        headPat = pat
                        expr = rhs
                        trivia = trivia) when isConstant rhs ->
                        match valueBinder pat with
                        | ValueSome(id, patAccess) when
                            Visibility.isInScopeWithSignatureEdits allowApiChanges path [ access; patAccess ]
                            && not (vetoed id)
                            ->
                            let kw = trivia.LeadingKeyword.Range

                            let ownLine =
                                kw.StartColumn = 0
                                || (source.GetLineString(kw.StartLine - 1)).Substring(0, kw.StartColumn).Trim() = ""

                            let declaredPrivately = Visibility.isPrivate path [ access; patAccess ]

                            // a binding another file can see is asked about
                            // there too: the same veto, project-wide
                            let clashesElsewhere = not declaredPrivately && boundAsPatternElsewhere id.idText

                            // a body split by `#if` is a constant only in the
                            // branch the parse tree shows: Paket's
                            // `runningOnMono` is `false` here and a `try` under
                            // ENABLE_MONO_SUPPORT, where the attribute would
                            // not compile
                            let splitBody = spansDirective source decl.Range

                            if ownLine && not clashesElsewhere && not splitBody then
                                let indent = String.replicate kw.StartColumn " "
                                let at = Position.mkPos kw.StartLine 0

                                match
                                    SignatureFile.literalEdits
                                        declaredPrivately
                                        signature
                                        id.idText
                                        (textOfRange source rhs.Range)
                                with
                                | ValueSome signatureEdits ->
                                    {
                                        Range = id.idRange
                                        Name = id.idText
                                        Fix = Range.mkRange decl.Range.FileName at at, $"{indent}[<Literal>]\n"
                                        SignatureEdits = signatureEdits
                                    }
                                | ValueNone -> ()
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]

/// `findWith` for a caller with no other files to ask — a lone script, or
/// a test over one source string. Only this file's patterns veto.
let find (allowApiChanges: bool) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    findWith (fun _ -> false) allowApiChanges parseTree source
