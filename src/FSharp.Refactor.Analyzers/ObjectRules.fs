/// Object-programming correctness rules (the classic inspections):
///
/// 1. A type overriding `Equals` without overriding `GetHashCode` breaks
///    every hash-based container (Dictionary, Set, groupBy, distinct).
///    Hint only — a correct hash needs knowledge of the equality semantics.
///
/// 2. Calling an abstract member from a constructor runs the override
///    before the derived class's construction has finished — its state is
///    not initialized yet. Hint only.
///
/// Both rules are syntactic and scoped to the members declared in the same
/// type definition, which keeps them shadowing-proof and single-file.
module FSharp.Refactor.ObjectRules

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type EqualsSuggestion =
    {
        /// The type name, for the message.
        TypeName: string
        /// Range of the Equals member's name, where the hint is anchored.
        Range: range
        OriginalText: string
    }

type CtorCallSuggestion =
    {
        /// The abstract member being called during construction.
        MemberName: string
        Range: range
        OriginalText: string
    }

/// FR0054 (CA1065): a raise inside a member callers never expect to throw.
type RaiseInSpecialSuggestion =
    {
        /// "Equals", "GetHashCode", "ToString", or "Dispose".
        MemberName: string
        Range: range
    }

/// The member name bound by a `member`/`override` definition, with its range.
let private memberName (SynBinding(headPat = headPat)) =
    match headPat with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
    | _ -> None

let private isOverride (SynBinding(valData = SynValData(memberFlags = flags))) =
    flags |> Option.exists (fun f -> f.IsOverrideOrExplicitImpl)

/// All member bindings of a type definition (object-model body plus
/// augmentation-style members). With `includeInterfaces`, the bindings
/// inside `interface X with ...` blocks too — where IDisposable.Dispose
/// and IEquatable.Equals actually live.
let private memberBindingsOf (includeInterfaces: bool) (SynTypeDefn(typeRepr = repr; members = extraMembers)) =
    let rec ofMembers members =
        members
        |> List.collect (fun m ->
            match m with
            | SynMemberDefn.Member(memberDefn = binding) -> [ binding ]
            | SynMemberDefn.Interface(members = Some inner) when includeInterfaces -> ofMembers inner
            | _ -> [])

    match repr with
    | SynTypeDefnRepr.ObjectModel(members = members) -> ofMembers members @ ofMembers extraMembers
    | _ -> ofMembers extraMembers

let private memberBindings typeDefn = memberBindingsOf false typeDefn

/// Abstract slots declared directly in the type.
let private abstractSlotNames (SynTypeDefn(typeRepr = repr)) =
    match repr with
    | SynTypeDefnRepr.ObjectModel(members = members) ->
        members
        |> List.choose (fun m ->
            match m with
            | SynMemberDefn.AbstractSlot(slotSig = SynValSig(ident = SynIdent(ident = ident))) -> Some ident.idText
            | _ -> None)
        |> Set.ofList
    | _ -> Set.empty

/// The implicit constructor's self identifier (`as this`), if any.
let private selfIdentifier (SynTypeDefn(typeRepr = repr)) =
    match repr with
    | SynTypeDefnRepr.ObjectModel(members = members) ->
        members
        |> List.tryPick (fun m ->
            match m with
            | SynMemberDefn.ImplicitCtor(selfIdentifier = Some self) -> Some self.idText
            | _ -> None)
    | _ -> None

/// Constructor-time expressions: instance let/do bindings in the class body.
let private ctorExprs (SynTypeDefn(typeRepr = repr)) =
    match repr with
    | SynTypeDefnRepr.ObjectModel(members = members) ->
        members
        |> List.collect (fun m ->
            match m with
            | SynMemberDefn.LetBindings(bindings = bindings; isStatic = false) ->
                bindings |> List.map (fun (SynBinding(expr = e)) -> e)
            | _ -> [])
    | _ -> []

/// Members that hash containers, debuggers, and finalization call
/// implicitly — an exception thrown there surfaces far from its cause.
let private specialMembers = set [ "Equals"; "GetHashCode"; "ToString"; "Dispose" ]

/// Raising functions from FSharp.Core.
let private raisingFunctions =
    set [ "raise"; "failwith"; "failwithf"; "invalidOp"; "invalidArg"; "nullArg" ]

/// Find Equals-without-GetHashCode, ctor-time abstract calls, and raises in
/// members that are never expected to throw.
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    : EqualsSuggestion list * CtorCallSuggestion list * RaiseInSpecialSuggestion list =
    let equalsSuggestions = ResizeArray<EqualsSuggestion>()
    let ctorSuggestions = ResizeArray<CtorCallSuggestion>()
    let raiseSuggestions = ResizeArray<RaiseInSpecialSuggestion>()
    let index = AstIndex.ofTree parseTree

    // raise-like applications, for range-containment checks — the direct
    // call, `raise <| X()`, and `X() |> raise`
    let raiseSites =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn) when raisingFunctions.Contains fn.idText ->
                Some(fn.idText, e.Range)
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = SingleIdent fn)) when
                op.idText = "op_PipeLeft" && raisingFunctions.Contains fn.idText
                ->
                Some(fn.idText, e.Range)
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op)
                argExpr = SingleIdent fn) when op.idText = "op_PipeRight" && raisingFunctions.Contains fn.idText ->
                Some(fn.idText, e.Range)
            | _ -> None)

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkSynModuleDecl(_path, decl) =
                match decl with
                | SynModuleDecl.Types(typeDefns = typeDefns) ->
                    for SynTypeDefn(typeInfo = SynComponentInfo(longId = typeIds)) as typeDefn in typeDefns do
                        let typeName = typeIds |> List.map (fun i -> i.idText) |> String.concat "."

                        // rule 1: Equals override without GetHashCode override
                        let overrides =
                            memberBindings typeDefn |> List.filter isOverride |> List.choose memberName

                        let equalsIdent = overrides |> List.tryFind (fun i -> i.idText = "Equals")

                        let hasGetHashCode = overrides |> List.exists (fun i -> i.idText = "GetHashCode")

                        match equalsIdent with
                        | Some ident when not hasGetHashCode ->
                            equalsSuggestions.Add
                                {
                                    TypeName = typeName
                                    Range = ident.idRange
                                    OriginalText = textOfRange source ident.idRange
                                }
                        | _ -> ()

                        // rule 3 (FR0054): raises inside members callers never
                        // expect to throw (excluding ones inside a try-with,
                        // which the member handles itself)
                        for binding in memberBindingsOf true typeDefn |> List.filter isOverride do
                            match memberName binding, binding with
                            | Some nameId, SynBinding(expr = body) when specialMembers.Contains nameId.idText ->
                                let handledRanges =
                                    index.Exprs
                                    |> Array.choose (fun (_, e) ->
                                        match e with
                                        | SynExpr.TryWith(tryExpr = t) when Range.rangeContainsRange body.Range e.Range ->
                                            Some t.Range
                                        | _ -> None)

                                for _, siteRange in
                                    raiseSites
                                    |> Array.filter (fun (_, r) ->
                                        Range.rangeContainsRange body.Range r
                                        && not (handledRanges |> Array.exists (fun h -> Range.rangeContainsRange h r))) do
                                    raiseSuggestions.Add
                                        {
                                            MemberName = nameId.idText
                                            Range = siteRange
                                        }
                            | _ -> ()

                        // rule 2: abstract members referenced during construction
                        let abstracts = abstractSlotNames typeDefn

                        match selfIdentifier typeDefn with
                        | Some self when not abstracts.IsEmpty ->
                            // every `self.<slot>` anywhere inside a ctor-time
                            // binding: the index already walked each shape
                            // (assignment right-hand sides, loops, try blocks),
                            // where a hand-rolled worklist used to stop short
                            let ctorRanges = ctorExprs typeDefn |> List.map (fun e -> e.Range)

                            let inCtor (r: range) =
                                ctorRanges |> List.exists (fun c -> Range.rangeContainsRange c r)

                            for _, e in index.Exprs do
                                let referenced =
                                    match e with
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = head :: name :: _)) when
                                        head.idText = self && abstracts.Contains name.idText && inCtor e.Range
                                        ->
                                        Some name
                                    | SynExpr.DotGet(expr = SynExpr.Ident head; longDotId = SynLongIdent(id = name :: _)) when
                                        head.idText = self && abstracts.Contains name.idText && inCtor e.Range
                                        ->
                                        Some name
                                    | _ -> None

                                match referenced with
                                | Some ident ->
                                    ctorSuggestions.Add
                                        {
                                            MemberName = ident.idText
                                            Range = ident.idRange
                                            OriginalText = textOfRange source ident.idRange
                                        }
                                | None -> ()
                        | _ -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq equalsSuggestions, List.ofSeq ctorSuggestions, List.ofSeq raiseSuggestions
