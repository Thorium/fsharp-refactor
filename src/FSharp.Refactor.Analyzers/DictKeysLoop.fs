/// FR0170 (performance): a loop over a dictionary's keys that looks every
/// key up again.
///
///     for k in d.Keys do                 for KeyValue(k, v) in d do
///         use k d.[k]              →         use k v
///
/// `d.[k]` hashes the key and probes the table once per iteration for a
/// value the enumerator already had in hand: `KeyValue` reads the pair.
/// CSharp.Refactor's CR0032 (`foreach (var (k, v) in d)`).
///
/// Guards: `d` is a name or a dotted read typed `Dictionary<K,V>`,
/// `IDictionary<K,V>` or `IReadOnlyDictionary<K,V>` (never a concurrent
/// one: its `Keys` is a snapshot where its enumerator is live, and the
/// two disagree under a writer); the loop variable is a plain name; the
/// body reads `d.[k]` / `d[k]` at least once and never stores through the
/// indexer, and never rebinds `k` (a `d.[k]` under a `let k = ...` reads
/// another key), and no read sits under a lambda, `lazy`, computation
/// expression or object expression inside the body (it runs later, against
/// the dictionary as it is then, where `v` is a snapshot); `k` read as a
/// plain value is fine, `KeyValue(k, v)` binds it;
/// the value name is `value`, else `v`, else `v1`, unused in the enclosing
/// binding. Every read converts together with the header.
module FSharp.Refactor.DictKeysLoop

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The loop header's `k in d.Keys` span, for the message.
        Range: range
        KeyName: string
        ValueName: string
        /// The header edit and one per indexer read: (range, original, replacement).
        Edits: (range * string * string) list
    }

let private dictionaryTypes =
    set
        [
            "System.Collections.Generic.Dictionary`2"
            "System.Collections.Generic.IDictionary`2"
            "System.Collections.Generic.IReadOnlyDictionary`2"
            "System.Collections.Generic.SortedDictionary`2"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let symbolOf (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
            |> Option.map (fun u -> u.Symbol)

        // the dictionary's type, from the last identifier of its spelling
        let isDictionary (id: Ident) =
            match symbolOf id with
            | Some(:? FSharpMemberOrFunctionOrValue as mfv) ->
                (try
                    let t = OptionModule.stripAbbreviations mfv.FullType

                    t.HasTypeDefinition
                    && (t.TypeDefinition.TryFullName |> Option.exists dictionaryTypes.Contains)
                 with _ -> // an unreadable type is no dictionary of ours; fsharpanalyzer: ignore-line FR0055
                     false)
            | Some(:? FSharpField as f) ->
                (try
                    let t = OptionModule.stripAbbreviations f.FieldType

                    t.HasTypeDefinition
                    && (t.TypeDefinition.TryFullName |> Option.exists dictionaryTypes.Contains)
                 with _ -> // fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false

        // `d.Keys` where `d` is a name or a dotted read: the receiver's
        // identifiers and its text
        let keysOf (e: SynExpr) =
            match stripParens e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2 && (List.last ids).idText = "Keys"
                ->
                let receiver = ids |> List.take (ids.Length - 1)
                Some(receiver, identText receiver)
            | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ keys ])) when keys.idText = "Keys" ->
                match receiver with
                | SynExpr.Ident id -> Some([ id ], id.idText)
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(ids, identText ids)
                | _ -> None
            | _ -> None

        // `d.[k]` / `d[k]` with the same receiver text and the loop key
        let indexerRead (receiverText: string) (key: string) (e: SynExpr) =
            let keyIs (arg: SynExpr) =
                match stripParens arg with
                | SynExpr.Ident id -> id.idText = key
                | _ -> false

            match e with
            | SynExpr.DotIndexedGet(objectExpr = obj; indexArgs = arg) ->
                textOfRange source obj.Range = receiverText && keyIs arg
            // F# 6 `d[k]`: an application of the receiver to a list literal
            | SynExpr.App(
                isInfix = false; funcExpr = obj; argExpr = SynExpr.ArrayOrListComputed(isArray = false; expr = arg)) ->
                textOfRange source obj.Range = receiverText && keyIs arg
            | _ -> false

        [
            for path, e in index.Exprs do
                match e with
                | SynExpr.ForEach(
                    pat = SynPat.Named(ident = SynIdent(ident = key)); enumExpr = enumExpr; bodyExpr = body) ->
                    match keysOf enumExpr with
                    | Some(receiverIds, receiverText) when isDictionary (List.last receiverIds) ->
                        let readsWithPaths =
                            index.Exprs
                            |> Array.filter (fun (_, inner) ->
                                Range.rangeContainsRange body.Range inner.Range
                                && indexerRead receiverText key.idText inner)

                        let reads = readsWithPaths |> Array.map snd

                        // a read under a lambda, `lazy`, computation
                        // expression or object expression inside the body
                        // runs LATER, against the dictionary as it is then;
                        // the pair's value is what it held during the loop
                        let deferredRead =
                            readsWithPaths
                            |> Array.exists (fun (readPath, _) ->
                                readPath
                                |> List.exists (fun node ->
                                    match node with
                                    | SyntaxNode.SynExpr(SynExpr.Lambda _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.MatchLambda _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.Lazy _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.ObjExpr _ as deferring) ->
                                        Range.rangeContainsRange body.Range deferring.Range
                                    | _ -> false))

                        // a store through the indexer, or a key used anywhere
                        // but as the lookup, keeps the loop
                        let stores =
                            index.Exprs
                            |> Array.exists (fun (_, inner) ->
                                Range.rangeContainsRange body.Range inner.Range
                                && (match inner with
                                    | SynExpr.DotIndexedSet(objectExpr = obj) ->
                                        textOfRange source obj.Range = receiverText
                                    | SynExpr.Set(targetExpr = SynExpr.App(funcExpr = obj)) ->
                                        textOfRange source obj.Range = receiverText
                                    | _ -> false))

                        let enclosing =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) ->
                                    Some(textOfRange source b.RangeOfBindingWithRhs)
                                | _ -> None)
                            |> Option.defaultValue (source.GetSubTextString(0, source.Length))

                        let valueName =
                            [ "value"; "v"; "v1" ] |> List.tryFind (mentionsIdentifier enclosing >> not)

                        // a `let k = ...`, a lambda or a match arm rebinding
                        // the key inside the body: a `d.[k]` under it reads
                        // ANOTHER key, which the pair's value is not
                        let keyRebound =
                            (index.Pats
                             |> Array.exists (fun (_, p) ->
                                 Range.rangeContainsRange body.Range p.Range
                                 && List.contains key.idText (patBoundNames p)))
                            // a lambda's parameters are simple patterns the
                            // index does not list
                            || (index.Exprs
                                |> Array.exists (fun (_, inner) ->
                                    Range.rangeContainsRange body.Range inner.Range
                                    && (match inner with
                                        | SynExpr.Lambda(parsedData = Some(pats, _)) ->
                                            pats |> List.collect patBoundNames |> List.contains key.idText
                                        | _ -> false)))

                        match valueName with
                        | Some valueName when
                            reads.Length > 0
                            && not stores
                            && not keyRebound
                            && not deferredRead
                            && isSingleLine enumExpr.Range
                            ->
                            let headerRange =
                                Range.mkRange enumExpr.Range.FileName key.idRange.Start enumExpr.Range.End

                            {
                                Range = headerRange
                                KeyName = key.idText
                                ValueName = valueName
                                Edits =
                                    (headerRange,
                                     textOfRange source headerRange,
                                     $"KeyValue({key.idText}, {valueName}) in {receiverText}")
                                    :: [ for r in reads -> r.Range, textOfRange source r.Range, valueName ]
                            }
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]
