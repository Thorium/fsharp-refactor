/// FR0179 (correctness, note), twin of the C# rule: the result of an
/// update on an immutable collection handed to `ignore`.
///
///     index.Add(key, value) |> ignore      // index is unchanged
///     Map.add key value index |> ignore
///     seen.Add item |> ignore              // an F# Set
///
/// An F# `Map` or `Set`, and every System.Collections.Immutable
/// collection, answers an update with a NEW collection and leaves the
/// receiver as it was. Discarding the answer discards the update: the code
/// reads as a mutation and does nothing.
///
/// Typed rule: the call is fully applied, it is a member of the collection
/// type or a function of its module (`Map`, `Set`), and its result is one
/// of those collection types. A function of your own returning a Map is
/// not read - it may have been called for an effect. Neither is a call
/// that builds the collection from something else (`Set.ofSeq xs |> ignore`
/// forces a lazy sequence) or takes a function (`Map.filter f m |> ignore`
/// may be an iteration in disguise): only a call that takes the collection
/// and plain values is an update with nothing else to it.
///
/// Note-only: the repair is to keep the result, and where it goes is the
/// author's design - a rebinding, a `mutable`, a fold.
module FSharp.Refactor.DiscardedUpdate

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole discarding expression.
        Range: range
        /// The call as written, without its arguments: `index.Add`, `Map.add`.
        CallName: string
        /// "Map", "Set" or the immutable collection's name.
        Collection: string
    }

[<Literal>]
let private immutableNamespace = "System.Collections.Immutable."

/// "Map" / "Set" / "ImmutableList" for a persistent collection type.
let private collectionOf (fullName: string) =
    match fullName with
    | "Microsoft.FSharp.Collections.FSharpMap`2" -> ValueSome "Map"
    | "Microsoft.FSharp.Collections.FSharpSet`1" -> ValueSome "Set"
    | name when name.StartsWith immutableNamespace ->
        let short = name.Substring immutableNamespace.Length

        match short.IndexOf '`' with
        | -1 -> ValueSome short
        | tick -> ValueSome(short.Substring(0, tick))
    | _ -> ValueNone

let private owners =
    set
        [
            "Microsoft.FSharp.Collections.FSharpMap`2"
            "Microsoft.FSharp.Collections.MapModule"
            "Microsoft.FSharp.Collections.FSharpSet`1"
            "Microsoft.FSharp.Collections.SetModule"
        ]

/// `ignore x` / `x |> ignore` - the operand, parens stripped.
[<return: Struct>]
let private (|Ignored|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = IdentName "ignore"; argExpr = arg) -> ValueSome(stripParens arg)
    | PipeApp(arg, IdentName "ignore") -> ValueSome(stripParens arg)
    | _ -> ValueNone

/// The called path and how many arguments it took: `m.Add(k, v)` ->
/// (m.Add, 1); `Map.add k v m` -> (Map.add, 3); `m |> Map.add k v` ->
/// (Map.add, 3).
[<TailCall>]
let rec private calleeAndDepth (depth: int) (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner) -> calleeAndDepth depth inner
    | PipeApp(_, rhs) -> calleeAndDepth (depth + 1) rhs
    | SynExpr.App(isInfix = false; funcExpr = f) -> calleeAndDepth (depth + 1) f
    | SynExpr.TypeApp(expr = inner) -> calleeAndDepth depth inner
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
        ValueSome(List.last ids, e.Range, depth)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.last ids, e.Range, depth)
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let resolve (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value -> ValueSome value
                | _ -> ValueNone
            | None -> ValueNone

        // the collection the call answers with, when the callee is the
        // collection's own member or module function and takes every
        // argument it declares
        let updated (callee: Ident) (applied: int) =
            match resolve callee with
            | ValueSome value ->
                (try
                    let owner = value.DeclaringEntity |> Option.bind (fun e -> e.TryFullName)

                    let ownUpdate =
                        match owner with
                        | Some name -> owners.Contains name || name.StartsWith immutableNamespace
                        | None -> false

                    let groups = value.CurriedParameterGroups.Count

                    if ownUpdate && groups > 0 && groups <= applied then
                        let result = OptionModule.stripAbbreviations value.ReturnParameter.Type

                        let fullNameOf (t: FSharpType) =
                            let t = OptionModule.stripAbbreviations t

                            if t.HasTypeDefinition then
                                t.TypeDefinition.TryFullName
                            else
                                None

                        let parameters =
                            value.CurriedParameterGroups
                            |> Seq.concat
                            |> Seq.map (fun p -> p.Type)
                            |> List.ofSeq

                        // an UPDATE takes the collection it answers with: as
                        // the receiver, or as an argument of the module
                        // function. `Set.ofSeq xs` builds from something
                        // else, and discarding it is how a lazy sequence
                        // gets forced
                        let takesCollection =
                            (value.IsInstanceMember && not value.IsExtensionMember)
                            || (parameters |> List.exists (fun p -> fullNameOf p = fullNameOf result))

                        // a function argument may be called for its effect
                        // (`Map.filter` used as an iteration)
                        let takesFunction =
                            parameters
                            |> List.exists (fun p ->
                                let p = OptionModule.stripAbbreviations p

                                p.IsFunctionType || (p.HasTypeDefinition && p.TypeDefinition.IsDelegate))

                        if takesCollection && not takesFunction then
                            match fullNameOf result with
                            | Some name -> collectionOf name
                            | None -> ValueNone
                        else
                            ValueNone
                    else
                        ValueNone
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     ValueNone)
            | ValueNone -> ValueNone

        [
            for _, e in index.Exprs do
                match e with
                | Ignored(SynExpr.App _ as operand) ->
                    match calleeAndDepth 0 operand with
                    | ValueSome(callee, calleeRange, applied) when applied > 0 ->
                        match updated callee applied with
                        | ValueSome collection ->
                            {
                                Range = e.Range
                                CallName = textOfRange source calleeRange
                                Collection = collection
                            }
                        | ValueNone -> ()
                    | _ -> ()
                // let _ = index.Add(key, value): the same discard
                | LetOrUseE lou when not (lou.IsBang || lou.IsUse) ->
                    match lou.Bindings with
                    | [ SynBinding(headPat = SynPat.Wild _; expr = rhs) ] ->
                        match stripParens rhs with
                        | SynExpr.App _ as operand ->
                            match calleeAndDepth 0 operand with
                            | ValueSome(callee, calleeRange, applied) when applied > 0 ->
                                match updated callee applied with
                                | ValueSome collection ->
                                    {
                                        Range = rhs.Range
                                        CallName = textOfRange source calleeRange
                                        Collection = collection
                                    }
                                | ValueNone -> ()
                            | _ -> ()
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]
