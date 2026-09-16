/// Refactoring note (performance): a recursive function that re-enters
/// itself through a `seq { }` builds a nested enumerator per recursion
/// level.
///
///     let rec walk node = seq {
///         yield node.Value
///         for child in node.Children do
///             yield! walk child          // fresh enumerator chain per level
///     }
///
/// Every yielded element is then dragged through O(depth) MoveNext calls,
/// and each level allocates its own state machine — deep trees turn a
/// linear walk into a quadratic one. The remedy is one sequence with an
/// explicit stack:
///
///     let walk root = seq {
///         let stack = Stack [ root ]
///         while stack.Count > 0 do
///             let node = stack.Pop()
///             yield node.Value
///             for child in node.Children do stack.Push child
///     }
///
/// Advice only — the traversal order (and laziness granularity) is the
/// author's to preserve. Applies to `seq`, `taskSeq`, and `asyncSeq`
/// builders alike.
module FSharp.Refactor.RecursiveSeq

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The self-referencing call site inside the seq body.
        Range: range
        /// The recursive function's name, for the message.
        FunctionName: string
        /// The builder used ("seq"/"taskSeq"/"asyncSeq").
        Builder: string
    }

let private seqBuilders = set [ "seq"; "taskSeq"; "asyncSeq" ]

/// The single name bound by a recursive binding's head pattern.
let private boundName (SynBinding(headPat = p)) =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ f ])) -> Some f.idText
    | SynPat.Named(ident = SynIdent(ident = f)) -> Some f.idText
    | _ -> None

/// The ranges of the `yield!`s in tail position of a seq body: the last
/// step of the body, reached through sequencing, bindings, `if` and
/// `match` — the places the compiler turns a recursive `yield!` into a
/// jump rather than a nested enumerator.
let private tailYieldFroms (body: SynExpr) =
    // the function position of `yield! f a b`: only a DIRECT self-call is
    // redirected; `yield! Seq.collect walk xs` still nests an enumerator
    // per level inside collect
    let rec headOf (e: SynExpr) =
        match e with
        | SynExpr.App(isInfix = false; funcExpr = f) -> headOf f
        | SynExpr.Paren(expr = inner)
        | SynExpr.TypeApp(expr = inner) -> headOf inner
        | SynExpr.Ident id -> Some id.idRange
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idRange
        | _ -> None

    let rec loop (acc: range list) (pending: SynExpr list) =
        match pending with
        | [] -> acc
        | e :: rest ->
            match e with
            | SynExpr.YieldOrReturnFrom(flags = (true, _); expr = target) ->
                loop ((headOf target |> Option.toList) @ acc) rest
            | SynExpr.Sequential(expr2 = e2) -> loop acc (e2 :: rest)
            | LetOrUseE lou -> loop acc (lou.Body :: rest)
            | SynExpr.IfThenElse(thenExpr = t; elseExpr = els) -> loop acc (t :: (Option.toList els) @ rest)
            | SynExpr.Match(clauses = clauses)
            | SynExpr.MatchBang(clauses = clauses) ->
                loop acc ((clauses |> List.map (fun (SynMatchClause(resultExpr = r)) -> r)) @ rest)
            | SynExpr.Paren(expr = inner)
            | SynExpr.Typed(expr = inner) -> loop acc (inner :: rest)
            | _ -> loop acc rest

    loop [] [ body ]

/// Find recursive self-entries inside sequence builders.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree

    // seq-builder CE bodies FIRST: no seq { } means nothing to do, and
    // most files have none. Before this early-out, the member widening
    // made this rule the slowest in the whole sweep — every member's
    // binding was collected and probed against every expression.
    let seqBodies =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                seqBuilders.Contains builder
                ->
                Some(builder, body.Range, tailYieldFroms body)
            | _ -> None)

    if Array.isEmpty seqBodies then
        []
    else

        // every ident occurrence by name, one pass — the self-call probe was
        // O(bindings × expressions) as separate scans
        let identOccurrences =
            System.Collections.Generic.Dictionary<string, ResizeArray<range * bool>>()

        let addOccurrence (name: string) (r: range) (dotted: bool) =
            match identOccurrences.TryGetValue name with
            | true, existing -> existing.Add(r, dotted)
            | false, _ ->
                let fresh = ResizeArray()
                fresh.Add(r, dotted)
                identOccurrences.[name] <- fresh

        for _, e in index.Exprs do
            match e with
            | SynExpr.Ident id -> addOccurrence id.idText id.idRange false
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                let last = List.last ids
                addOccurrence last.idText last.idRange (ids.Length > 1)
            | _ -> ()

        // (function name, binding body range) for every recursive binding
        let recBindings =
            let fromBindings isRec bindings =
                if isRec then
                    bindings
                    |> List.choose (fun (SynBinding(expr = body) as binding) ->
                        boundName binding |> Option.map (fun name -> name, body.Range))
                else
                    []

            let fromDecls =
                index.Decls
                |> Array.toList
                |> List.collect (fun (_, decl) ->
                    match decl with
                    | SynModuleDecl.Let(isRecursive = isRec; bindings = bindings) -> fromBindings isRec bindings
                    | _ -> [])

            let fromExprs =
                index.Exprs
                |> Array.toList
                |> List.collect (fun (_, e) ->
                    match e with
                    | LetOrUseE lou when lou.IsRecursive && not lou.IsBang -> fromBindings true lou.Bindings
                    | _ -> [])

            // members are implicitly recursive — there is no `rec` keyword to
            // find — and OO-style tree APIs are precisely where recursive seqs
            // live: `member this.Descendants() = seq { for c in children do
            // yield! c.Descendants() }`. Their self-calls are dotted, so these
            // bindings match dotted call spellings too (third tuple element).
            let fromMembers =
                index.Decls
                |> Array.toList
                |> List.collect (fun (_, decl) ->
                    match decl with
                    | SynModuleDecl.Types(typeDefns = defns) ->
                        defns
                        |> List.collect (fun (SynTypeDefn(typeRepr = repr; members = extra)) ->
                            let ofMembers (members: SynMemberDefn list) =
                                members
                                |> List.collect (fun m ->
                                    match m with
                                    | SynMemberDefn.Member(
                                        memberDefn = SynBinding(
                                            headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids))
                                            expr = body)) when not ids.IsEmpty ->
                                        [ (List.last ids).idText, body.Range, true ]
                                    | _ -> [])

                            (match repr with
                             | SynTypeDefnRepr.ObjectModel(members = ms) -> ofMembers ms
                             | _ -> [])
                            @ ofMembers extra)
                    | _ -> [])

            ((fromDecls @ fromExprs) |> List.map (fun (n, r) -> n, r, false)) @ fromMembers

        [
            for name, bodyRange, allowDotted in recBindings do
                // seq bodies belonging to this binding — skip the probe entirely
                // when there are none, which is nearly every binding
                let ownSeqs =
                    seqBodies
                    |> Array.filter (fun (_, seqRange, _) -> Range.rangeContainsRange bodyRange seqRange)

                // only a self-call whose RESULT is enumerated nests an
                // enumerator: the target of a `yield!` (directly, or through
                // Seq.collect and friends) or the source of a `for ... in`.
                // `yield innerText' elem` calls itself for a plain value
                let enumerated =
                    index.Exprs
                    |> Array.choose (fun (_, e) ->
                        match e with
                        | SynExpr.YieldOrReturnFrom(expr = target) when
                            ownSeqs
                            |> Array.exists (fun (_, s, _) -> Range.rangeContainsRange s target.Range)
                            ->
                            Some target.Range
                        | SynExpr.ForEach(enumExpr = src) when
                            ownSeqs |> Array.exists (fun (_, s, _) -> Range.rangeContainsRange s src.Range)
                            ->
                            Some src.Range
                        | _ -> None)

                if not (Array.isEmpty ownSeqs) then
                    // a self-call inside a tail-position `yield!` is not a
                    // nested enumerator: the compiler turns it into a jump
                    // (`yield! readLines (n + 1)` as the body's last step is a
                    // loop), so only re-entries elsewhere — under a `for`, a
                    // `while`, a `try`, or before further yields — count
                    let inOwnSeq (r: range) =
                        ownSeqs
                        |> Array.tryPick (fun (builder, seqRange, tails) ->
                            if
                                Range.rangeContainsRange seqRange r
                                && enumerated |> Array.exists (fun en -> Range.rangeContainsRange en r)
                                && not (tails |> List.exists (fun t -> Range.equals t r))
                            then
                                Some(r, builder)
                            else
                                None)

                    // the first self-reference inside any of them, via the
                    // occurrence table. A member's re-entry is dotted
                    // (`c.Descendants`); matching the last ident by name accepts
                    // some imprecision, fair for an advice-only rule
                    let selfCall =
                        match identOccurrences.TryGetValue name with
                        | true, occurrences ->
                            occurrences
                            |> Seq.tryPick (fun (r, dotted) -> if not dotted || allowDotted then inOwnSeq r else None)
                        | false, _ -> None

                    match selfCall with
                    | Some(callRange, builder) ->
                        {
                            Range = callRange
                            FunctionName = name
                            Builder = builder
                        }
                    | None -> ()
        ]
