/// Refactoring: a mutable backing field with a trivial get/set member is an
/// auto-property.
///
///     type Person() =                        type Person() =
///         let mutable name = ""         →        member val Name = "" with get, set
///         member this.Name
///             with get () = name
///             and set v = name <- v
///
/// Safety rules:
///   - the get accessor returns exactly the backing field; the set accessor
///     assigns exactly its parameter to it — nothing else
///   - the backing field is referenced nowhere else in the type, so removing
///     it cannot break other members
///   - the initializer is a pure atom: `member val` initializes at its own
///     declaration position, so moving an effectful initializer could
///     reorder construction effects
///   - neither accessor carries an accessibility modifier (asymmetric
///     visibility cannot be expressed with `member val`)
///   - the pair is a plain `member`: `member val` declares a new slot, so
///     an `override`/`default` pair would hide (FS0864) or no longer
///     implement the abstract property
module FSharp.Refactor.AutoProperty

open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The property name, for the message.
        PropertyName: string
        /// The get/set member, where the hint anchors.
        Range: range
        /// Two edits: delete the backing-field line, replace the member
        /// ((range, original, replacement)).
        Edits: (range * string * string) list
    }

/// The head pattern of a property accessor binding: `this.Prop`, unmodified.
[<return: Struct>]
let private (|AccessorPat|_|) (p: SynPat) =
    match p with
    | SynPat.LongIdent(
        longDotId = SynLongIdent(id = [ _self; prop ]); accessibility = None; argPats = SynArgPats.Pats args) ->
        ValueSome(prop, args)
    | _ -> ValueNone

/// Find backing-field + trivial get/set pairs.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    for _, decl in index.Decls do
        match decl with
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeRepr = repr) as typeDefn in defns do
                match repr with
                | SynTypeDefnRepr.ObjectModel(members = members) ->
                    // mutable instance backing fields, keyed by name
                    let backingFields =
                        members
                        |> List.choose (fun m ->
                            match m with
                            | SynMemberDefn.LetBindings(
                                isStatic = false
                                bindings = [ SynBinding(
                                                 isMutable = true
                                                 headPat = SynPat.Named(ident = SynIdent(ident = var))
                                                 expr = init) ]) when isSingleLine m.Range && isPureAtom init ->
                                Some(var.idText, (m, init))
                            | _ -> None)
                        |> Map.ofList

                    for memberDefn in members do
                        match memberDefn with
                        | SynMemberDefn.GetSetMember(
                            memberDefnForGet = Some(SynBinding(
                                attributes = getAttrs
                                headPat = AccessorPat(getProp, _)
                                expr = getBody
                                trivia = getTrivia))
                            memberDefnForSet = Some(SynBinding(
                                attributes = setAttrs; headPat = AccessorPat(setProp, [ setArg ]); expr = setBody))) when
                            getProp.idText = setProp.idText
                            // a plain `member` only: `member val` declares a
                            // NEW slot, so over an abstract one an `override`
                            // or `default` pair becomes a hiding member
                            // (FS0864) or leaves the slot unimplemented
                            && (match getTrivia.LeadingKeyword with
                                | SynLeadingKeyword.Member _ -> true
                                | _ -> false)
                            // the rewrite replaces memberDefn.Range wholesale,
                            // and that range INCLUDES the attribute list — an
                            // [<Obsolete>] or [<JsonIgnore>] would silently
                            // vanish, and the result still compiles
                            && getAttrs |> List.forall (fun a -> a.Attributes.IsEmpty)
                            && setAttrs |> List.forall (fun a -> a.Attributes.IsEmpty)
                            ->
                            let backingName =
                                match stripParens getBody with
                                | SynExpr.Ident b -> Some b.idText
                                | _ -> None

                            let setsBacking =
                                match backingName, boundVar setArg, setBody with
                                | Some b,
                                  Some(Some param),
                                  SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), SynExpr.Ident rhs, _) ->
                                    target.idText = b && rhs.idText = param
                                | _ -> false

                            match
                                backingName
                                |> Option.bind (fun b -> backingFields.TryFind b |> Option.map (fun v -> b, v))
                            with
                            | Some(b, (letMember, init)) when setsBacking ->

                                // the backing field must appear nowhere else
                                let outsideAccessorAndLet (r: range) =
                                    Range.rangeContainsRange typeDefn.Range r
                                    && not (Range.rangeContainsRange memberDefn.Range r)
                                    && not (Range.rangeContainsRange letMember.Range r)

                                let usedElsewhere =
                                    index.Exprs
                                    |> Array.exists (fun (_, e) ->
                                        match e with
                                        | SynExpr.Ident id when id.idText = b -> outsideAccessorAndLet id.idRange
                                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when
                                            firstId.idText = b
                                            ->
                                            outsideAccessorAndLet firstId.idRange
                                        // assignments target the field without an
                                        // Ident expression node
                                        | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) when
                                            firstId.idText = b
                                            ->
                                            outsideAccessorAndLet e.Range
                                        | _ -> false)

                                // the deleted line must hold only the binding
                                let letLine = source.GetLineString(letMember.Range.StartLine - 1)

                                let lineIsOnlyBinding = letLine.Trim() = (textOfRange source letMember.Range).Trim()

                                if not usedElsewhere && lineIsOnlyBinding then
                                    let file = letMember.Range.FileName

                                    let deleteRange =
                                        Range.mkRange
                                            file
                                            (Position.mkPos letMember.Range.StartLine 0)
                                            (Position.mkPos (letMember.Range.StartLine + 1) 0)

                                    let replacement =
                                        sprintf
                                            "member val %s = %s with get, set"
                                            getProp.idText
                                            (textOfRange source init.Range)

                                    suggestions.Add
                                        {
                                            PropertyName = getProp.idText
                                            Range = memberDefn.Range
                                            Edits =
                                                [
                                                    deleteRange, textOfRange source deleteRange, ""
                                                    memberDefn.Range, textOfRange source memberDefn.Range, replacement
                                                ]
                                        }
                            | _ -> ()
                        | _ -> ()
                | _ -> ()
        | _ -> ()

    suggestions
    |> Seq.filter (fun s -> not (spansDirective source s.Range))
    |> List.ofSeq
