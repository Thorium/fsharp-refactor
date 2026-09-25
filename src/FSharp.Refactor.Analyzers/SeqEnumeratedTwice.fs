/// FR0169 (correctness): a `seq<'T>` parameter or local enumerated twice on one path.
///
///     let report (xs: int seq) =
///         if Seq.isEmpty xs then "none"          // walk one
///         else $"{Seq.length xs} items"           // walk two
///
/// A `seq` is a promise to enumerate, not a collection: what arrives may
/// be a `seq { }` that reads a file, a database query, a `Seq.map` over a
/// call that does work — and every consumer runs it again from the start.
/// The second walk repeats the effects and the cost, and a generator that
/// cannot restart (a reader) answers nothing the second time. F#'s own
/// `Seq` module is careful about this everywhere (`Seq.cache` exists for
/// it); user code rarely is. CSharp.Refactor's CR0030, on `IEnumerable<T>`
/// parameters, is the twin.
///
/// The shape: a parameter (annotated or inferred) or a local `let` value
/// typed as `seq`/`IEnumerable` by the typechecker (a list or array is a
/// collection and walks for free; a local built by `Seq.cache`, `Seq.ofList`
/// or an upcast is cheap to walk again and is not one), used
/// at two SITES that both enumerate it — a `for` over it, a Seq module
/// consumer applied to it (`Seq.length xs`, `xs |> Seq.iter f`, a pipeline
/// from it ending in one), `List.ofSeq`/`Array.ofSeq`/`Set.ofSeq`/
/// `Map.ofSeq` of it — where neither site sits inside a lambda (deferred:
/// once, twice or never) and the two are not in different arms of one
/// `if`/`match`/`try` (one path runs one of them). The sites are matched
/// by symbol, so a `let xs = List.ofSeq xs` shadow is a different `xs`.
/// Note only: whether to materialise once or read in one pass is the
/// author's; the note names the second site.
module FSharp.Refactor.SeqEnumeratedTwice

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The first site.
        Range: range
        ParameterName: string
        /// The line of the second site, for the message.
        SecondLine: int
    }

/// The Seq module functions that run the sequence to answer.
let private seqConsumers =
    set
        [
            "length"
            "iter"
            "iteri"
            "sum"
            "sumBy"
            "average"
            "averageBy"
            "max"
            "min"
            "maxBy"
            "minBy"
            "exists"
            "forall"
            "isEmpty"
            "fold"
            "foldBack"
            "reduce"
            "contains"
            "find"
            "tryFind"
            "findIndex"
            "tryFindIndex"
            "pick"
            "tryPick"
            "head"
            "tryHead"
            "last"
            "tryLast"
            "exactlyOne"
            "tryExactlyOne"
            "item"
            "tryItem"
            "toList"
            "toArray"
        ]

/// `Module.func` at the head of an application chain.
[<TailCall>]
let rec private headModuleFunc (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) -> ValueSome(m.idText, f.idText)
    | SynExpr.App(isInfix = false; funcExpr = funcExpr) -> headModuleFunc funcExpr
    | SynExpr.TypeApp(expr = inner) -> headModuleFunc inner
    | _ -> ValueNone

/// A stage that enumerates what is piped into it.
let private consumes (stage: SynExpr) =
    match headModuleFunc stage with
    | ValueSome("Seq", f) -> seqConsumers.Contains f
    | ValueSome(("List" | "Array" | "Set" | "Map" | "HashSet"), "ofSeq")
    | ValueSome("String", "concat") -> true
    | _ -> false

/// The identifier a pipeline starts from: `xs` in `xs |> Seq.map f |>
/// Seq.length`.
[<TailCall>]
let rec private pipelineRoot (e: SynExpr) =
    match e with
    | PipeApp(inner, _) -> pipelineRoot inner
    | SynExpr.Paren(expr = inner) -> pipelineRoot inner
    | SynExpr.Ident id -> ValueSome id
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let symbolOf (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ])
            |> Option.map (fun u -> u.Symbol)

        // a parameter the typechecker reads as IEnumerable<T> itself
        let isSeqSymbol (symbol: FSharpSymbol) =
            match symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                (try
                    let t = OptionModule.stripAbbreviations value.FullType

                    t.HasTypeDefinition
                    && t.TypeDefinition.TryFullName = Some "System.Collections.Generic.IEnumerable`1"
                 with _ -> // an unreadable type is not a seq of ours; fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false

        // the body a local value scopes over: that of the first `let` (in
        // index order) with a binding whose head is exactly `head`. Every
        // head of the file by its position, collected once when a local asks
        let letBodies =
            lazy
                (let byPosition =
                    System.Collections.Generic.Dictionary<struct (int * int * int * int), ResizeArray<range * range>>()

                 for _, e in index.Exprs do
                     match e with
                     | LetOrUseE lou ->
                         for SynBinding(headPat = hp) in lou.Bindings do
                             let r = hp.Range
                             let key = struct (r.StartLine, r.StartColumn, r.EndLine, r.EndColumn)

                             match byPosition.TryGetValue key with
                             | true, l -> l.Add(r, lou.Body.Range)
                             | false, _ -> byPosition.[key] <- ResizeArray [ r, lou.Body.Range ]
                     | _ -> ()

                 byPosition)

        let scopeOf (head: range) =
            match
                letBodies.Value.TryGetValue(struct (head.StartLine, head.StartColumn, head.EndLine, head.EndColumn))
            with
            | true, found ->
                found
                |> Seq.tryPick (fun (hr, body) -> if Range.equals hr head then Some body else None)
            | false, _ -> None

        // the sources cheap to walk again: a cached or already materialised
        // sequence spelled as one, or a collection upcast to seq
        let cheapSource (rhs: SynExpr) =
            let cheapStage (stage: SynExpr) =
                match headModuleFunc stage with
                | ValueSome("Seq", ("cache" | "ofList" | "ofArray" | "empty" | "singleton"))
                | ValueSome(("List" | "Array"), "toSeq") -> true
                | _ -> false

            match stripParens rhs with
            | SynExpr.Upcast _ -> true
            // the pipeline's LAST stage decides: `… |> Seq.cache`
            | PipeApp(_, stage) -> cheapStage stage
            | other -> cheapStage other

        // the names typed as a seq, each with the range its walks can sit in:
        // a parameter (annotated or inferred) with its binding, a local `let`
        // value with the body it scopes over. A lambda's parameter is per
        // call and every site under it is deferred, so it yields nothing.
        let candidates =
            [
                for path, pat in index.Pats do
                    match pat with
                    | SynPat.Named(ident = SynIdent(ident = id)) ->
                        // the innermost binding, and whether the pattern is in
                        // its head (a parameter) or is the binding's own name
                        let binding =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding(headPat = hp; expr = rhs) as b) ->
                                    Some(b.RangeOfBindingWithRhs, hp, rhs)
                                | _ -> None)

                        match binding with
                        | Some(bindingRange, headPat, rhs) ->
                            let inHead = Range.rangeContainsRange headPat.Range pat.Range

                            let isParameter =
                                inHead
                                && (match headPat with
                                    | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> true
                                    | SynPat.LongIdent(argPats = SynArgPats.NamePatPairs _) -> true
                                    | _ -> false)

                            // the typed lookup last, and once: for a parameter or
                            // a local value only, never for a match or lambda binder
                            if isParameter || (inHead && not (cheapSource rhs)) then
                                match symbolOf id with
                                | Some symbol when isSeqSymbol symbol ->
                                    if isParameter then
                                        yield id, bindingRange, symbol
                                    else
                                        // a local value: its scope is the body of
                                        // the let that binds it
                                        match scopeOf headPat.Range with
                                        | Some scope -> yield id, scope, symbol
                                        | None -> ()
                                | _ -> ()
                        | None -> ()
                    | _ -> ()
            ]

        // the identifier a site enumerates, if it is exactly the parameter
        let refersTo (symbol: FSharpSymbol) (id: Ident) =
            match symbolOf id with
            | Some s -> s.IsEffectivelySameAs symbol
            | None -> false

        // a site under a lambda or a local function inside the binding runs
        // on its own schedule
        let deferred (bindingRange: range) (path: SyntaxNode list) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.Lambda _ as e)
                | SyntaxNode.SynExpr(SynExpr.MatchLambda _ as e)
                | SyntaxNode.SynExpr(SynExpr.ObjExpr _ as e) ->
                    Range.rangeContainsRange bindingRange e.Range
                    && not (Range.equals bindingRange e.Range)
                | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))) as b) ->
                    Range.rangeContainsRange bindingRange b.RangeOfBindingWithRhs
                    && not (Range.equals bindingRange b.RangeOfBindingWithRhs)
                | _ -> false)

        // two sites in different arms of one branching expression are on
        // different paths. Only a branch inside the scope can part them: one
        // enclosing the scope holds both sites in the same arm
        let exclusive (scope: range) (a: range) (b: range) =
            let within (r: range) (site: range) = Range.rangeContainsRange r site

            AstIndex.exprsWithin index scope
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some els) ->
                    (within t.Range a && within els.Range b)
                    || (within els.Range a && within t.Range b)
                | SynExpr.Match(clauses = clauses)
                | SynExpr.MatchLambda(matchClauses = clauses)
                | SynExpr.MatchBang(clauses = clauses)
                | SynExpr.TryWith(withCases = clauses) ->
                    let armOf (site: range) =
                        clauses |> List.tryFindIndex (fun c -> within c.Range site)

                    match armOf a, armOf b with
                    | Some x, Some y -> x <> y
                    | _ -> false
                | _ -> false)

        [
            for id, bindingRange, symbol in candidates do
                let sites =
                    [
                        for path, e in AstIndex.exprsWithin index bindingRange do
                            if not (deferred bindingRange path) then
                                match e with
                                | SynExpr.ForEach(enumExpr = enumExpr) ->
                                    match stripParens enumExpr with
                                    | SynExpr.Ident x when x.idText = id.idText && refersTo symbol x ->
                                        yield enumExpr.Range
                                    | _ -> ()
                                // `xs |> Seq.length`, `xs |> Seq.map f |> Seq.toList`
                                | PipeApp(_, stage) when consumes stage ->
                                    match pipelineRoot e with
                                    | ValueSome x when x.idText = id.idText && refersTo symbol x -> yield e.Range
                                    | _ -> ()
                                // `Seq.length xs`, `Seq.iter f xs`, `List.ofSeq xs`
                                | SynExpr.App(isInfix = false; argExpr = arg) when consumes e ->
                                    match stripParens arg with
                                    | SynExpr.Ident x when x.idText = id.idText && refersTo symbol x -> yield e.Range
                                    | _ -> ()
                                | _ -> ()
                    ]
                    // `xs |> Seq.toList |> Seq.length` walks once: a site inside
                    // another site is the same walk
                    |> fun found ->
                        found
                        |> List.filter (fun r ->
                            not (
                                found
                                |> List.exists (fun outer ->
                                    not (Range.equals outer r) && Range.rangeContainsRange outer r)
                            ))
                    |> List.sortBy (fun r -> r.StartLine, r.StartColumn)

                let pair =
                    [
                        for i in 0 .. sites.Length - 1 do
                            for j in i + 1 .. sites.Length - 1 do
                                if not (exclusive bindingRange sites.[i] sites.[j]) then
                                    yield sites.[i], sites.[j]
                    ]
                    |> List.tryHead

                match pair with
                | Some(first, second) ->
                    {
                        Range = first
                        ParameterName = id.idText
                        SecondLine = second.StartLine
                    }
                | None -> ()
        ]
