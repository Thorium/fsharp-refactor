/// FR0164 (correctness): a collection mutated inside a `for` loop over
/// itself — `InvalidOperationException: Collection was modified` at the
/// next MoveNext, and only on the runs where the branch is taken.
///
///     for x in items do                    for x in Array.ofSeq items do
///         if stale x then                      if stale x then
///             items.Remove x |> ignore             items.Remove x |> ignore
///
/// F# lists are immutable, so the shape is rarer than in C#, but a
/// `ResizeArray`, a `Dictionary` or a `HashSet` walked by `for` and edited
/// in the body throws the same. The fix walks a SNAPSHOT: `Array.ofSeq`
/// around the enumerated expression, so the body may add and remove
/// freely — every element present at the start is visited once, which is
/// what the loop meant. Typed-gated to System.Collections.Generic's
/// mutable types; the concurrent collections enumerate a snapshot or
/// tolerate edits by design and are left alone. `Remove`, `Clear` and an
/// overwrite through the indexer on a `Dictionary` or `HashSet` are
/// allowed mid-enumeration since .NET Core 3.0 (measured on this
/// runtime), so only their additions count — a sweep over a .NET
/// Framework target would see more; a `List<T>` throws on every edit,
/// an indexer store included.
module FSharp.Refactor.EnumerationMutation

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The enumerated expression, `items` or `items.Keys`.
        Range: range
        OriginalText: string
        /// `Array.ofSeq items`.
        ReplacementText: string
        /// The collection's name and the mutating call, for the message.
        Collection: string
        Mutation: string
    }

/// Every edit a List, Queue, Stack, LinkedList, SortedSet, SortedList or
/// SortedDictionary refuses mid-enumeration.
let private allEdits =
    set
        [
            "Add"
            "AddRange"
            "Insert"
            "InsertRange"
            "Remove"
            "RemoveAt"
            "RemoveAll"
            "RemoveRange"
            "RemoveFirst"
            "RemoveLast"
            "AddFirst"
            "AddLast"
            "Clear"
            "Enqueue"
            "Dequeue"
            "Push"
            "Pop"
            "Sort"
            "Reverse"
            "TryAdd"
            "set_Item"
        ]

/// What a Dictionary or HashSet still refuses: growth. An indexer store
/// over a key the loop is visiting is an overwrite, which they allow, so
/// `set_Item` is not counted for them.
let private additions = set [ "Add"; "TryAdd"; "UnionWith" ]

let private tolerantOfRemoval =
    set
        [
            "System.Collections.Generic.Dictionary`2"
            "System.Collections.Generic.HashSet`1"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the full name of an identifier's type, when it is a
        // System.Collections.Generic collection
        let genericCollection (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                (try
                    let t =
                        match symbolUse.Symbol with
                        | :? FSharpMemberOrFunctionOrValue as mfv -> Some mfv.FullType
                        | :? FSharpField as f -> Some f.FieldType
                        | _ -> None

                    // a concrete class only: an `IDictionary<_, _>` parameter
                    // may be a ConcurrentDictionary at run time, which
                    // tolerates every edit
                    t
                    |> Option.map OptionModule.stripAbbreviations
                    |> Option.bind (fun t ->
                        if t.HasTypeDefinition && not t.TypeDefinition.IsInterface then
                            t.TypeDefinition.TryFullName
                        else
                            None)
                    |> Option.filter (fun n -> n.StartsWith "System.Collections.Generic.")
                 with _ -> // an unreadable type is no collection of ours; fsharpanalyzer: ignore-line FR0055
                     None)
            | None -> None

        // the collection an enumerated expression walks: `items`, or
        // `items.Keys`/`items.Values` — the root identifier
        let enumerated (e: SynExpr) =
            match stripParens e with
            | SynExpr.Ident id -> Some id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ root; view ])) when
                view.idText = "Keys" || view.idText = "Values"
                ->
                Some root
            | _ -> None

        let symbolOf (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
            |> Option.map (fun u -> u.Symbol)

        // the receiver IS the enumerated collection — the same symbol, not
        // a namesake a `let` in the body shadows it with
        let sameCollection (collection: Ident) (recv: Ident) =
            recv.idText = collection.idText
            && (match symbolOf collection, symbolOf recv with
                | Some a, Some b -> a.IsEffectivelySameAs b
                | _ -> false)

        // the loop body's own statements: a lambda, an object expression or
        // a local function inside it runs later, or not at all, and a
        // mutation there is not a mutation under this enumeration
        let deferred (path: SyntaxNode list) (body: SynExpr) =
            // the nodes strictly inside the body: the loop, the function and
            // everything above are not the body's own
            let inside (node: SyntaxNode) =
                match node with
                | SyntaxNode.SynExpr e ->
                    Range.rangeContainsRange body.Range e.Range
                    && not (Range.equals body.Range e.Range)
                | SyntaxNode.SynBinding(SynBinding _ as b) ->
                    Range.rangeContainsRange body.Range b.RangeOfBindingWithRhs
                | _ -> false

            path
            |> List.filter inside
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.Lambda _)
                | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
                | SyntaxNode.SynExpr(SynExpr.ObjExpr _) -> true
                // a local function; a value binding (`let ok = xs.Remove x`)
                // runs where it stands
                | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)))) ->
                    true
                | _ -> false)

        // the statement right after the mutation leaves the loop for good —
        // `raise`, `failwith`, a computation's `return`/`return!` — so the
        // next MoveNext never runs: the mutate-and-leave idiom
        let leavesAfter (path: SyntaxNode list) (mutation: SynExpr) =
            let rec leaves (e: SynExpr) =
                match e with
                // `return`/`return!` leave; a `yield` resumes the loop
                | SynExpr.YieldOrReturn(flags = (isYield, _))
                | SynExpr.YieldOrReturnFrom(flags = (isYield, _)) -> not isYield
                | SynExpr.App(funcExpr = f) ->
                    (match f with
                     | SynExpr.Ident id
                     | SynExpr.App(funcExpr = SynExpr.Ident id) ->
                         (match id.idText with
                          | "raise"
                          | "failwith"
                          | "failwithf"
                          | "invalidOp"
                          | "invalidArg"
                          | "reraise" -> true
                          | _ -> false)
                     | _ -> false)
                | SynExpr.Sequential(expr1 = first) -> leaves first
                | _ -> false

            // the mutation, or the pipe it heads (`xs.Remove x |> ignore`),
            // as the first half of a sequence whose second half leaves
            // climbing the application the mutation heads (`|> ignore` is
            // two Apps up), then the sequence it is the first half of
            let rec headOf (nodes: SyntaxNode list) (r: range) =
                match nodes with
                | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f; argExpr = a) as app) :: rest when
                    Range.equals f.Range r || Range.equals a.Range r
                    ->
                    headOf rest app.Range
                | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = first; expr2 = next)) :: _ when
                    Range.equals first.Range r
                    ->
                    leaves next
                | _ -> false

            headOf path mutation.Range

        // `items.M args` / `items.[k] <- v` on the enumerated collection, in
        // the body's own statements
        let mutationIn (collection: Ident) (refused: Set<string>) (body: SynExpr) =
            index.Exprs
            |> Array.tryPick (fun (path, e) ->
                if not (Range.rangeContainsRange body.Range e.Range) || deferred path body then
                    None
                else
                    let mutation =
                        match e with
                        | SynExpr.App(
                            isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ recv; m ]))) when
                            refused.Contains m.idText && sameCollection collection recv
                            ->
                            Some m.idText
                        // `items.[k] <- v`, and the F# 6 `items[k] <- v`
                        | SynExpr.DotIndexedSet(objectExpr = SynExpr.Ident recv) when
                            refused.Contains "set_Item" && sameCollection collection recv
                            ->
                            Some "[k] <-"
                        | SynExpr.Set(
                            targetExpr = SynExpr.App(
                                funcExpr = SynExpr.Ident recv; argExpr = SynExpr.ArrayOrListComputed _)) when
                            refused.Contains "set_Item" && sameCollection collection recv
                            ->
                            Some "[k] <-"
                        | _ -> None

                    match mutation with
                    | Some _ when leavesAfter path e -> None
                    | found -> found)

        [
            for _, e in index.Exprs do
                match e with
                | SynExpr.ForEach(enumExpr = enumExpr; bodyExpr = body) ->
                    match enumerated enumExpr with
                    | Some collection ->
                        match genericCollection collection with
                        | Some typeName ->
                            let refused =
                                if tolerantOfRemoval.Contains typeName then
                                    additions
                                else
                                    allEdits

                            match mutationIn collection refused body with
                            | Some mutation ->
                                let text = textOfRange source enumExpr.Range

                                {
                                    Range = enumExpr.Range
                                    OriginalText = text
                                    ReplacementText = $"Array.ofSeq {text}"
                                    Collection = collection.idText
                                    Mutation = mutation
                                }
                            | None -> ()
                        | None -> ()
                    | None -> ()
                | _ -> ()
        ]
