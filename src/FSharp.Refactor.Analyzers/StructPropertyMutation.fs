/// FR0161 (correctness): a mutating method called on a struct that a
/// PROPERTY hands out — the getter returns a copy, the method mutates the
/// copy, and the stored value never changes.
///
///     type Holder() =
///         member val Counter = Counter() with get, set
///     holder.Counter.Bump()        // bumps a copy; holder.Counter.N stays 0
///
/// F# refuses the other copies of this family at compile time — a method
/// that mutates a struct through an immutable `let`, a record field or a
/// `for` variable is FS0256/FS0257 — so this one shape is where the copy
/// is silent. C#'s analyzers know it as the "mutating method on a struct
/// copy" defect.
///
/// A mutating method is one this file can see assigning a field of its
/// own struct (`this.N <- ...` inside a `[<Struct>]` type's member), or a
/// BCL struct's known mutator: `MoveNext` on an enumerator struct,
/// `SpinLock.Enter/Exit/TryEnter`, `SpinWait.SpinOnce/Reset`. The typed
/// check settles that the receiver IS a property and its type a struct.
/// Note only: the repair — copy to a `let mutable`, mutate, store back, or
/// make the type a class — is a design choice.
module FSharp.Refactor.StructPropertyMutation

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The method call.
        Range: range
        /// `holder.Counter` as written.
        PropertyText: string
        /// `Bump`.
        Method: string
    }

/// BCL struct mutators, by declaring type's full name (or a suffix of it
/// for the many enumerator structs).
let private knownMutators =
    [
        "System.Threading.SpinLock", set [ "Enter"; "Exit"; "TryEnter" ]
        "System.Threading.SpinWait", set [ "SpinOnce"; "Reset" ]
    ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // this file's struct types and the members that assign their own
        // fields: (type name, member name)
        let fileMutators =
            let isStruct (attrs: SynAttributes) (repr: SynTypeDefnRepr) =
                attrs
                |> List.exists (fun l ->
                    l.Attributes
                    |> List.exists (fun a ->
                        match a.TypeName with
                        | SynLongIdent(id = ids) when not ids.IsEmpty ->
                            let n = (List.last ids).idText
                            n = "Struct" || n = "StructAttribute"
                        | _ -> false))
                || (match repr with
                    | SynTypeDefnRepr.ObjectModel(kind = SynTypeDefnKind.Struct) -> true
                    | _ -> false)

            let rec assignsSelf (self: string) (e: SynExpr) =
                match e with
                | SynExpr.LongIdentSet(SynLongIdent(id = first :: _ :: _), _, _) -> first.idText = self
                | SynExpr.Set(targetExpr = SynExpr.DotGet(expr = SynExpr.Ident id)) -> id.idText = self
                | SynExpr.Sequential(expr1 = a; expr2 = b) -> assignsSelf self a || assignsSelf self b
                | SynExpr.IfThenElse(thenExpr = t; elseExpr = el) ->
                    assignsSelf self t || (el |> Option.exists (assignsSelf self))
                | LetOrUseE lou -> assignsSelf self lou.Body
                | SynExpr.Paren(expr = inner) -> assignsSelf self inner
                | SynExpr.Match(clauses = cs) ->
                    cs |> List.exists (fun (SynMatchClause(resultExpr = r)) -> assignsSelf self r)
                | _ -> false

            [
                for _, d in index.Decls do
                    match d with
                    | SynModuleDecl.Types(typeDefns = defns) ->
                        for SynTypeDefn(
                            typeInfo = SynComponentInfo(attributes = attrs; longId = tid)
                            typeRepr = repr
                            members = extra) in defns do
                            if isStruct attrs repr && not tid.IsEmpty then
                                let typeName = (List.last tid).idText

                                let members =
                                    match repr with
                                    | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                                    | _ -> extra

                                for m in members do
                                    match m with
                                    | SynMemberDefn.Member(
                                        memberDefn = SynBinding(
                                            headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ self; name ]))
                                            expr = body)) when assignsSelf self.idText body ->
                                        yield typeName, name.idText
                                    | _ -> ()
                    | _ -> ()
            ]
            |> set

        let symbolAt (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv -> Some mfv
                | _ -> None
            | None -> None

        // the property's type, when the identifier is a property of a
        // struct type
        let structProperty (propId: Ident) =
            match symbolAt propId with
            | Some mfv when mfv.IsProperty || mfv.IsPropertyGetterMethod ->
                (try
                    let t = OptionModule.stripAbbreviations mfv.ReturnParameter.Type

                    if
                        t.HasTypeDefinition
                        && t.TypeDefinition.IsValueType
                        && not t.TypeDefinition.IsEnum
                    then
                        Some t.TypeDefinition
                    else
                        None
                 with _ -> // an unreadable type is no struct; fsharpanalyzer: ignore-line FR0055
                     None)
            | _ -> None

        let mutates (structType: FSharpEntity) (methodId: Ident) =
            let name = methodId.idText
            let typeName = structType.DisplayName
            let full = structType.TryFullName |> Option.defaultValue ""

            fileMutators.Contains(typeName, name)
            || (name = "MoveNext" && typeName.EndsWith "Enumerator")
            || (knownMutators
                |> List.exists (fun (owner, methods) -> full = owner && methods.Contains name))

        [
            for _, e in index.Exprs do
                // `recv.Prop.Method args`, dotted or through DotGet
                let call =
                    match e with
                    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) & f) when
                        ids.Length >= 3
                        ->
                        let propId = ids.[ids.Length - 2]
                        let propRange = Range.mkRange f.Range.FileName f.Range.Start propId.idRange.End
                        Some(propId, List.last ids, propRange)
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.DotGet(
                            expr = SynExpr.DotGet(longDotId = SynLongIdent(id = pids)) & prop
                            longDotId = SynLongIdent(id = [ m ]))) when not pids.IsEmpty ->
                        Some(List.last pids, m, prop.Range)
                    | _ -> None

                // the method's name first: a symbol lookup per dotted call
                // in the file is not free
                let candidateName (methodId: Ident) =
                    let n = methodId.idText

                    n = "MoveNext"
                    || (knownMutators |> List.exists (fun (_, ms) -> ms.Contains n))
                    || (fileMutators |> Set.exists (fun (_, m) -> m = n))

                match call with
                | Some(propId, methodId, propRange) when candidateName methodId ->
                    match structProperty propId with
                    | Some structType when mutates structType methodId ->
                        {
                            Range = e.Range
                            PropertyText = textOfRange source propRange
                            Method = methodId.idText
                        }
                    | _ -> ()
                | _ -> ()
        ]
