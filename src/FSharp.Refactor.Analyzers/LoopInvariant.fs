/// Refactoring (performance): a binding inside a loop or collection lambda
/// whose value cannot change between iterations is re-evaluated every pass.
///
///     for x = 0 to 100 do          let c = a + 3
///         let c = a + 3       →    for x = 0 to 100 do
///         sink (x + c)                 sink (x + c)
///
/// Also `while`, `for ... in`, and lambdas handed to List/Array/Seq
/// operations.
///
/// Hoisting changes how many times the right-hand side runs (n iterations
/// become exactly one, and an empty loop still runs it once), so the
/// safety rules make that unobservable:
///   - the RHS is PURE: constants, identifiers, tuples, list/array
///     literals, and core arithmetic/comparison operators (typed-gated
///     against shadowed operators) — no calls, no property reads
///   - the RHS references no loop variable, no name bound earlier in the
///     loop body, and no name assigned anywhere inside the loop
///   - the binding is a plain single-line `let` of a simple name (no
///     mutable, no use, no functions)
///   - the bound name appears nowhere in the file outside the loop body:
///     the hoisted binding's wider scope can shadow or collide otherwise
///   - the insertion anchor (the statement carrying the loop) starts its
///     own line, and no edit crosses a compiler directive
module FSharp.Refactor.LoopInvariant

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The invariant binding, where the hint anchors.
        Range: range
        Name: string
        /// (range, original, replacement) edits: remove the inner let,
        /// insert it above the loop's statement.
        Edits: (range * string * string) list
    }

/// Module functions whose lambda argument runs per element.
let private collectionModules = set [ "List"; "Array"; "Seq" ]

/// Purity walk: succeeds only for expression shapes that always yield the
/// same value. Collects every identifier read and every operator ident —
/// the (expensive) typed core-operator resolution runs LATER, once the
/// cheap gates have already filtered most candidates out.
[<TailCall>]
let rec private pureIdentsLoop
    (acc: string list)
    (ops: Ident list)
    (pending: SynExpr list)
    : (string list * Ident list) voption =
    match pending with
    | [] -> ValueSome(acc, ops)
    | e :: rest ->
        match e with
        | SynExpr.Const _ -> pureIdentsLoop acc ops rest
        | SynExpr.Ident id -> pureIdentsLoop (id.idText :: acc) ops rest
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner) -> pureIdentsLoop acc ops (inner :: rest)
        | SynExpr.Tuple(exprs = exprs) -> pureIdentsLoop acc ops (exprs @ rest)
        | SynExpr.ArrayOrListComputed(expr = inner) -> pureIdentsLoop acc ops (inner :: rest)
        | SynExpr.ArrayOrList(exprs = exprs) -> pureIdentsLoop acc ops (exprs @ rest)
        // infix operator: App(App(op, lhs), rhs)
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
            op.idText.StartsWith "op_"
            ->
            pureIdentsLoop acc (op :: ops) (lhs :: rhs :: rest)
        // unary operator, e.g. -a
        | SynExpr.App(funcExpr = SingleIdent op; argExpr = arg) when op.idText.StartsWith "op_" ->
            pureIdentsLoop acc (op :: ops) (arg :: rest)
        | _ -> ValueNone

/// The insertion point: the nearest enclosing expression (the loop itself,
/// or e.g. the pipeline feeding a lambda) that starts its own line. Only
/// expression ancestors are considered, so the hoisted binding never
/// leaves the scope whose values it reads.
let private insertionAnchor (source: ISourceText) (path: SyntaxNode list) (loopExpr: SynExpr) =
    let startsItsLine (r: range) =
        let line = source.GetLineString(r.StartLine - 1)

        r.StartColumn <= line.Length && line.Substring(0, r.StartColumn).Trim() = ""

    let ancestors =
        path
        |> List.takeWhile (fun n ->
            match n with
            | SyntaxNode.SynExpr _ -> true
            | _ -> false)
        |> List.choose (fun n ->
            match n with
            | SyntaxNode.SynExpr e -> Some e
            | _ -> None)

    loopExpr :: ancestors
    |> List.tryFind (fun e -> startsItsLine e.Range)
    |> Option.map (fun e -> e.Range)

/// The leading `let` bindings of a loop body, with the continuation each
/// one wraps.
[<TailCall>]
let rec private leadingLets (acc: (SynBinding * SynExpr) list) (body: SynExpr) =
    match body with
    | LetOrUseE lou when not (lou.IsUse || lou.IsBang || lou.IsRecursive) ->
        match lou.Bindings with
        | [ binding ] -> leadingLets ((binding, lou.Body) :: acc) lou.Body
        | _ -> List.rev acc
    | _ -> List.rev acc

/// Find hoistable invariant bindings. Requires typed check results for the
/// operator-purity gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree
        let suggestions = ResizeArray<Suggestion>()

        // (loop node, loop-bound names, body) for every loop-like shape
        let candidates =
            [ for path, expr in index.Exprs do
                  match expr with
                  | SynExpr.For(ident = loopVar; doBody = body) -> path, expr, Set.singleton loopVar.idText, body
                  | SynExpr.ForEach(pat = pat; bodyExpr = body) -> path, expr, Set.ofList (patBoundNames pat), body
                  | SynExpr.While(doExpr = body) -> path, expr, Set.empty, body
                  // xs |> List.map (fun x -> ...) — the lambda's params are
                  // the per-element names
                  | SynExpr.App(
                      funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; _ ]))
                      argExpr = SynExpr.Paren(expr = SynExpr.Lambda(parsedData = Some(pats, _); body = body))) when
                      collectionModules.Contains m.idText
                      ->
                      path, expr, Set.ofList (pats |> List.collect patBoundNames), body
                  | _ -> () ]

        // one pass of every mention (read or assigned) keyed by name; the
        // per-candidate scans below become dictionary lookups
        let mentionIndex =
            System.Collections.Generic.Dictionary<string, ResizeArray<range>>()

        let assignIndex =
            System.Collections.Generic.Dictionary<string, ResizeArray<range>>()

        let addTo (d: System.Collections.Generic.Dictionary<string, ResizeArray<range>>) name r =
            match d.TryGetValue name with
            | true, existing -> existing.Add r
            | false, _ ->
                let fresh = ResizeArray()
                fresh.Add r
                d.[name] <- fresh

        for _, e in index.Exprs do
            match e with
            | SynExpr.Ident id -> addTo mentionIndex id.idText id.idRange
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) ->
                addTo mentionIndex firstId.idText firstId.idRange
            | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) ->
                addTo mentionIndex firstId.idText e.Range
                addTo assignIndex firstId.idText e.Range
            | SynExpr.Set(targetExpr = SynExpr.Ident id) -> addTo assignIndex id.idText e.Range
            | _ -> ()

        // is `name` assigned anywhere inside `r`?
        let assignedInside (r: range) (name: string) =
            match assignIndex.TryGetValue name with
            | true, ranges -> ranges |> Seq.exists (Range.rangeContainsRange r)
            | false, _ -> false

        // does this name appear (read or assigned) anywhere outside `r`?
        let usedOutside (r: range) (name: string) =
            match mentionIndex.TryGetValue name with
            | true, ranges -> ranges |> Seq.exists (Range.rangeContainsRange r >> not)
            | false, _ -> false

        for path, loopExpr, loopVars, body in candidates do
            match insertionAnchor source path loopExpr with
            | Some anchor ->
                let mutable boundEarlier = Set.empty

                for binding, continuation in leadingLets [] body do
                    match binding with
                    | SynBinding(
                        isMutable = false
                        isInline = false
                        headPat = SynPat.Named(ident = SynIdent(ident = name); accessibility = None)
                        expr = rhs) when
                        isSingleLine binding.RangeOfBindingWithRhs
                        && binding.RangeOfBindingWithRhs.EndLine < continuation.Range.StartLine
                        ->
                        let forbidden = loopVars + boundEarlier |> Set.add name.idText

                        match pureIdentsLoop [] [] [ rhs ] with
                        | ValueSome(reads, ops) when
                            // only an invariant that DOES WORK is worth
                            // hoisting: an operator expression (`a + 3`).
                            // A bare identifier, constant or literal
                            // copy costs nothing per iteration, and
                            // hoisting `let ny = sinPhi` out of Mibo's
                            // Primitive3D inner loop only separated it
                            // from the `nx`/`nz` it belongs with
                            not ops.IsEmpty
                            && reads
                               |> List.forall (fun rd ->
                                   not (forbidden.Contains rd || assignedInside loopExpr.Range rd))
                            // the hoisted binding's wider scope must collide
                            // with nothing: the name may live only in the loop
                            && not (usedOutside loopExpr.Range name.idText)
                            // a shadowed operator can have arbitrary
                            // semantics; the typed gate runs last
                            && ops |> List.forall (OptionModule.resolvesToCoreOperator check source)
                            ->
                            let letLine = binding.RangeOfBindingWithRhs.StartLine
                            // the binding range starts at the pattern; the
                            // `let` keyword lives before it on the same line
                            let bindingText = textOfRange source binding.RangeOfBindingWithRhs

                            let removeRange =
                                Range.mkRange
                                    binding.RangeOfBindingWithRhs.FileName
                                    (Position.mkPos letLine 0)
                                    (Position.mkPos (letLine + 1) 0)

                            let indent = System.String(' ', anchor.StartColumn)

                            // a binding lifted out of the loop keeps the `#if`
                            // it was written under; a directive has to open its
                            // own line, so that form is inserted at column 0 of
                            // the anchor's line, ahead of its indentation
                            let insert =
                                match conditionToKeep source letLine anchor.StartLine with
                                | Some condition ->
                                    Range.mkRange
                                        anchor.FileName
                                        (Position.mkPos anchor.StartLine 0)
                                        (Position.mkPos anchor.StartLine 0),
                                    "",
                                    $"#if {condition}\n{indent}let {bindingText}\n#endif\n"
                                | None ->
                                    Range.mkRange anchor.FileName anchor.Start anchor.Start,
                                    "",
                                    $"let {bindingText}\n{indent}"

                            let edits = [ insert; removeRange, textOfRange source removeRange, "" ]

                            if
                                not (edits |> List.exists (fun (r, _, _) -> spansDirective source r))
                                // the let must own its whole line, so the
                                // line delete removes exactly the binding
                                && (source.GetLineString(letLine - 1)).Trim() = $"let {bindingText}"
                            then
                                suggestions.Add
                                    { Range = binding.RangeOfBindingWithRhs
                                      Name = name.idText
                                      Edits = edits }
                        | _ -> ()
                    | _ -> ()

                    boundEarlier <-
                        boundEarlier
                        + Set.ofList (
                            match binding with
                            | SynBinding(headPat = p) -> patBoundNames p
                        )
            | None -> ()

        List.ofSeq suggestions
