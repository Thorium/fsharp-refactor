/// Refactoring note (performance): iterating an IQueryable inside another
/// loop executes one database query per outer iteration — the N+1 pattern.
///
///     for customer in customers do
///         for order in db.Orders do        // ← a fresh DB round-trip
///             ...                          //   on every customer
///
/// The remedies are design work, so this is advice without a fix:
/// materialize the query once before the loop, push the correlation into a
/// join, or batch the keys.
///
/// Safety rules:
///   - the inner source must statically resolve (via typed check results) to
///     System.Linq.IQueryable — plain sequences and lists never fire
///   - an outer loop whose source involves `chunkBySize` is intentional
///     batching and suppresses the note
///   - the file must have no type errors
module FSharp.Refactor.QueryInLoop

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The inner `for ... in <queryable>` loop, where the hint anchors.
        Range: range
        /// The queryable source's text, for the message.
        SourceText: string
    }

let private isQueryableName (name: string) =
    name.StartsWith "System.Linq.IQueryable"

/// Is the type (after abbreviations) IQueryable or an implementation of it?
let private isQueryableType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.TryFullName |> Option.exists isQueryableName
            || t.TypeDefinition.AllInterfaces
               |> Seq.exists (fun i ->
                   i.HasTypeDefinition
                   && (i.TypeDefinition.TryFullName |> Option.exists isQueryableName)))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The identifier to resolve for a loop source: `q`, `db.Orders`, `x.A.B`.
[<return: Struct>]
let private (|SourcePathLastIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// Does the source symbol at `ident` have an IQueryable type?
let private resolvesToQueryable (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            isQueryableType (
                try
                    value.ReturnParameter.Type
                with _ ->
                    value.FullType
            )
        | _ -> false
    | None -> false

/// Find IQueryable iterations nested inside another loop. Requires typed
/// check results; emits nothing when the file has type errors.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // does the expression subtree call chunkBySize (intentional batching)?
        let mentionsChunking (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.Ident id when id.idText = "chunkBySize" -> Range.rangeContainsRange r id.idRange
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                    not ids.IsEmpty && (List.last ids).idText = "chunkBySize"
                    ->
                    Range.rangeContainsRange r e.Range
                | _ -> false)

        // ...and the same when the chunking was BOUND first, which is how it
        // is usually written:
        //     let chunkedLoanIds = Array.chunkBySize 200 loanIdsAll
        //     for loanIds in chunkedLoanIds do
        // The outer loop's enumeration expression is then a bare identifier
        // whose range holds no call at all (management-portal DomainShared.fs).
        // Matching by NAME can suppress a note through shadowing, which is the
        // safe direction for advice that has no fix.
        let chunkedNames =
            let named (SynBinding(headPat = pat; range = r) as binding) =
                let range =
                    try
                        binding.RangeOfBindingWithRhs
                    with _ -> // fsharpanalyzer: ignore-line FR0055
                        r

                match pat with
                | SynPat.Named(ident = SynIdent(ident = id)) when mentionsChunking range -> Some id.idText
                | _ -> None

            Set.union
                (index.Decls
                 |> Array.collect (fun (_, d) ->
                     match d with
                     | SynModuleDecl.Let(bindings = bs) -> bs |> List.choose named |> Array.ofList
                     | _ -> [||])
                 |> Set.ofArray)
                (index.Exprs
                 |> Array.collect (fun (_, e) ->
                     match e with
                     | LetOrUseE lou -> lou.Bindings |> List.choose named |> Array.ofList
                     | _ -> [||])
                 |> Set.ofArray)

        let enumeratesChunks (e: SynExpr) =
            mentionsChunking e.Range
            || (match e with
                | SynExpr.Ident id -> chunkedNames.Contains id.idText
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    chunkedNames.Contains (List.last ids).idText
                | _ -> false)

        [ for path, expr in index.Exprs do
              match expr with
              | SynExpr.ForEach(enumExpr = SourcePathLastIdent sourceId as enumExpr) ->
                  // an "outer loop" is also a collection-function callback:
                  // `customers |> List.iter (fun c -> for o in db.Orders ...)`
                  // runs the query once per customer just like a for-loop.
                  // Walking the path nearest-first, a Lambda followed by an
                  // App headed by List/Array/Seq is that shape; the App's own
                  // expression stands in for the enumerated source so a
                  // chunkBySize anywhere in the pipeline still suppresses.
                  // the chunkBySize of a piped chain sits to the LEFT of the
                  // List.iter application, outside its range — widen to the
                  // outermost enclosing App so the whole pipeline is scanned
                  let widen (e: SynExpr) =
                      path
                      |> List.fold
                          (fun (acc: SynExpr) node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.App _ as outer) when
                                  Range.rangeContainsRange outer.Range acc.Range
                                  ->
                                  outer
                              | _ -> acc)
                          e

                  let outerLoops =
                      let loops = ResizeArray<SynExpr option>()
                      let mutable sawLambda = false

                      for node in path do
                          match node with
                          | SyntaxNode.SynExpr(SynExpr.ForEach(enumExpr = outerEnum)) -> loops.Add(Some outerEnum)
                          | SyntaxNode.SynExpr(SynExpr.For _)
                          | SyntaxNode.SynExpr(SynExpr.While _) -> loops.Add None
                          | SyntaxNode.SynExpr(SynExpr.Lambda _) -> sawLambda <- true
                          | SyntaxNode.SynExpr(SynExpr.App(
                              funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = m :: _))) as app) when
                              sawLambda && (m.idText = "List" || m.idText = "Array" || m.idText = "Seq")
                              ->
                              loops.Add(Some(widen app))
                              sawLambda <- false
                          | _ -> ()

                      List.ofSeq loops

                  let intentionalBatching =
                      outerLoops
                      |> List.exists (fun enum ->
                          match enum with
                          | Some(outerEnum: SynExpr) -> enumeratesChunks outerEnum
                          | None -> false)

                  // inside `query { }` a nested `for` is a JOIN the provider
                  // translates into one statement — but only when the OUTER
                  // loop's source is itself IQueryable: an in-memory outer
                  // sequence runs the inner query once per element, in a
                  // query block or out of it
                  // the outer source is queryable when it is a queryable
                  // value, or a `query { }` of its own — SQLProvider's tests
                  // nest sub-queries three deep, all one statement
                  let outerIsQueryable (e: SynExpr) =
                      match stripParens e with
                      | SourcePathLastIdent outerId -> resolvesToQueryable check source outerId
                      | SynExpr.App(funcExpr = SynExpr.Ident q; argExpr = SynExpr.ComputationExpr _) ->
                          q.idText.EndsWith("query", System.StringComparison.OrdinalIgnoreCase)
                      | _ -> false

                  let translatedJoin =
                      insideQuotedCode path
                      && (path
                          |> List.tryPick (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.ForEach(enumExpr = outer)) -> Some outer
                              | _ -> None)
                          |> Option.exists outerIsQueryable)

                  // a query under a loop that pages with skip/take, or filters
                  // by the outer element's batch (`chunk.Contains order.Id`),
                  // runs one statement per batch on purpose — SQLProvider's
                  // pagination and batching tests, not N+1
                  let paginated =
                      let outerVariables =
                          path
                          |> List.collect (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.ForEach(pat = p)) -> patNames p
                              | _ -> [])
                          |> Set.ofList

                      let queryBody =
                          path
                          |> List.tryPick (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.ComputationExpr(expr = body)) -> Some body
                              | _ -> None)

                      match queryBody with
                      | Some body ->
                          index.Exprs
                          |> Array.exists (fun (_, e) ->
                              Range.rangeContainsRange body.Range e.Range
                              && (match e with
                                  | SynExpr.App(funcExpr = SynExpr.Ident op) ->
                                      op.idText = "skip" || op.idText = "take"
                                  | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ x; m ]))) ->
                                      m.idText = "Contains" && outerVariables.Contains x.idText
                                  | _ -> false))
                      | None -> false

                  if
                      not outerLoops.IsEmpty
                      && not intentionalBatching
                      && not translatedJoin
                      && not paginated
                      && resolvesToQueryable check source sourceId
                  then
                      { Range = expr.Range
                        SourceText = textOfRange source enumExpr.Range }
              | _ -> () ]
