/// FR0118 (fix): a call omits the CancellationToken its target offers
/// while a token sits unused in scope — cancellation stops propagating
/// exactly one call too early.
///
///     let fetch (client: HttpClient) (ct: CancellationToken) = task {
///         let! s = client.GetStringAsync(url)          // ct exists...
///     }                                                // ...pass it:
///         let! s = client.GetStringAsync(url, ct)
///
/// Typed gates, all must hold:
///   - the resolved method has a same-name overload with EXACTLY one more
///     parameter, a trailing System.Threading.CancellationToken, and the
///     shared prefix of parameter types identical — or the method itself
///     carries a trailing OPTIONAL CancellationToken the call omits
///   - the enclosing binding has EXACTLY one parameter annotated as a
///     CancellationToken (two tokens make the choice a human call)
///   - the call uses .NET tupled shape (`M()`, `M(a)`, `M(a, b)`) — the
///     edit appends the token inside the parentheses
///
/// The loop note (findUnobservedLoops): a loop awaiting inside, under the
/// token's binding, that never mentions the token — nor a local built
/// with it (`let enumerator = source.GetAsyncEnumerator ct`) — cannot be
/// cancelled. Outside `async { }` only, which observes the token at every
/// bind by itself; quiet where the fix above already hands the token to a
/// call in the loop.
module FSharp.Refactor.CancellationOverload

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type TokenGap =
    /// The call omits the token an overload (or optional parameter) takes.
    | Omitted
    /// The call passes `CancellationToken.None` although a real token is
    /// in scope — cancellation is explicitly cut instead of propagated.
    | NonePassed

type Suggestion =
    {
        /// The edit: replace `()`, append `, token` before the `)`, or
        /// replace the `CancellationToken.None` argument.
        Range: range
        Original: string
        Replacement: string
        MethodName: string
        TokenName: string
        Kind: TokenGap
    }

let private isCancellationTokenType (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText = "CancellationToken"
    | _ -> false

/// The last identifier of a member-call function expression.
[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// `name = expr` in argument position is a NAMED argument: it may well BE
/// the token (`cancellationToken = ct`), and positional arity counting is
/// meaningless around it — appending `, token` after one is a syntax error.
let private isNamedArg (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = op; argExpr = SynExpr.Ident _)) ->
        (match op with
         | SynExpr.Ident i -> i.idText = "op_Equality"
         | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ i ])) -> i.idText = "op_Equality"
         | _ -> false)
    | _ -> false

let private typeFullName (t: FSharpType) =
    try
        match t.StripAbbreviations().TypeDefinition.TryFullName with
        | Some full -> full
        | None -> ""
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        ""

let private isCancellationToken (t: FSharpType) =
    typeFullName t = "System.Threading.CancellationToken"

/// Parameter types rendered for a pairwise prefix comparison.
let private parameterShapes (displayContext: FSharpDisplayContext) (mfv: FSharpMemberOrFunctionOrValue) =
    try
        match mfv.CurriedParameterGroups |> List.ofSeq with
        | [ group ] -> Some [ for p in group -> p.Type.Format displayContext ]
        | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// Task.Run and Task.Factory.StartNew take the token as a SCHEDULING
/// condition, not as an operation to interrupt: with an already-cancelled
/// token the delegate never runs at all, so the side effects in its body
/// silently never happen — suave's Tcp.fs binds the listening socket and
/// completes a cell inside one. An I/O method's token only cancels the
/// call it was passed to; these two change whether the work starts, and
/// that is the author's decision.
let private schedulesDelegate (mfv: FSharpMemberOrFunctionOrValue) =
    (mfv.DisplayName = "Run" || mfv.DisplayName = "StartNew")
    && (OptionModule.enclosingFullName mfv).StartsWith "System.Threading.Tasks.Task"

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let resolveMember (id: Ident) =
            let lineText = source.GetLineString(id.idRange.EndLine - 1)

            match check.GetSymbolUseAtLocation(id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv -> Some(symbolUse, mfv)
                | _ -> None
            | None -> None

        // every binding parameter annotated `: CancellationToken`, with the
        // binding it belongs to — the scope a call must sit inside
        let tokenParams =
            [
                for path, pat in index.Pats do
                    match pat with
                    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)); targetType = t) when
                        isCancellationTokenType t
                        ->
                        let binding =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                                | _ -> None)

                        match binding with
                        | Some bindingRange -> yield id.idText, bindingRange
                        | None -> ()
                    | _ -> ()
            ]

        // the `with` handlers and `finally` blocks of every try: a call
        // there is CLEANUP — `tx.RollbackAsync()` after a cancelled
        // `CommitAsync ct`. Handing it the same token makes the rollback
        // throw OperationCanceledException on the way out instead of
        // rolling back, so the transaction is left hanging. No token is
        // ever injected into one (the same exclusion FR0079 applies to its
        // bridge sites)
        let cleanupRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.TryFinally(finallyExpr = f) -> [| f.Range |]
                | SynExpr.TryWith(withCases = cases) ->
                    cases
                    |> List.map (fun (SynMatchClause(resultExpr = result)) -> result.Range)
                    |> Array.ofList
                | _ -> [||])

        let inCleanup (callRange: range) =
            cleanupRanges |> Array.exists (fun z -> Range.rangeContainsRange z callRange)

        // the single in-scope token for a call site, if there is exactly one
        let tokenFor (callRange: range) =
            let inScope =
                tokenParams
                |> List.filter (fun (_, bindingRange) -> Range.rangeContainsRange bindingRange callRange)

            match inScope |> List.map fst |> List.distinct with
            | [ name ] when not (inCleanup callRange) -> Some name
            | _ -> None

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = CallIdent methodId; argExpr = args) ->
                    // .NET tupled call shapes only — the edit appends inside
                    // the parentheses
                    let callArity =
                        match args with
                        | SynExpr.Const(SynConst.Unit, _) -> Some 0
                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) when not (es |> List.exists isNamedArg) ->
                            Some es.Length
                        | SynExpr.Paren(expr = SynExpr.Tuple _) -> None
                        | SynExpr.Paren(expr = inner) when not (isNamedArg inner) -> Some 1
                        | _ -> None

                    // the token may already BE one of the arguments —
                    // `CreateLinkedTokenSource(ct)` takes the token as its
                    // PAYLOAD, and a params/two-token sibling overload would
                    // happily compile `(ct, ct)`
                    let alreadyPassed token =
                        let isToken (a: SynExpr) =
                            match stripParens a with
                            | SynExpr.Ident i -> i.idText = token
                            | _ -> false

                        match args with
                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> es |> List.exists isToken
                        | SynExpr.Paren(expr = inner) -> isToken inner
                        | _ -> false

                    match callArity, tokenFor expr.Range with
                    | Some arity, Some token when not (alreadyPassed token) ->
                        match resolveMember methodId with
                        | Some(symbolUse, mfv) ->
                            match mfv with
                            | mfv when mfv.IsMember && not mfv.IsProperty && not (schedulesDelegate mfv) ->
                                let shapes = parameterShapes symbolUse.DisplayContext mfv

                                let tokenAccepted =
                                    match shapes with
                                    | Some ps when ps.Length = arity ->
                                        // is there a sibling overload with the
                                        // same prefix plus a trailing token?
                                        (try
                                            match mfv.DeclaringEntity with
                                            | Some entity ->
                                                entity.MembersFunctionsAndValues
                                                |> Seq.exists (fun m ->
                                                    m.DisplayName = mfv.DisplayName
                                                    && (match parameterShapes symbolUse.DisplayContext m with
                                                        | Some mps when mps.Length = arity + 1 ->
                                                            List.truncate arity mps = ps
                                                            && (m.CurriedParameterGroups
                                                                |> Seq.collect id
                                                                |> Seq.tryLast
                                                                |> Option.map (fun p -> isCancellationToken p.Type)
                                                                |> Option.defaultValue false)
                                                        | _ -> false))
                                            | None -> false
                                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                             false)
                                    | Some ps when ps.Length = arity + 1 ->
                                        // the method itself has a trailing
                                        // OPTIONAL token the call omits
                                        (try
                                            let last = mfv.CurriedParameterGroups |> Seq.collect id |> Seq.last
                                            last.IsOptionalArg && isCancellationToken last.Type
                                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                             false)
                                    | _ -> false

                                if tokenAccepted then
                                    match args with
                                    | SynExpr.Const(SynConst.Unit, unitRange) ->
                                        {
                                            Range = unitRange
                                            Original = "()"
                                            Replacement = $"({token})"
                                            MethodName = methodId.idText
                                            TokenName = token
                                            Kind = TokenGap.Omitted
                                        }
                                    | SynExpr.Paren(expr = inner) ->
                                        // a trailing lambda, match or if runs
                                        // to the closing parenthesis: `, ct`
                                        // appended bare joins its BODY as a
                                        // tuple — Paket's
                                        // `ContinueWith(fun (_: Task) -> (), ct)`
                                        // returned `unit * CancellationToken`
                                        // and the pass rolled back. Such an
                                        // argument is wrapped first
                                        let lastElement =
                                            match inner with
                                            | SynExpr.Tuple(exprs = es) -> List.last es
                                            | e -> e

                                        let openEnded =
                                            match lastElement with
                                            | SynExpr.Lambda _
                                            | SynExpr.MatchLambda _
                                            | SynExpr.Match _
                                            | SynExpr.IfThenElse _
                                            | SynExpr.TryWith _
                                            | SynExpr.TryFinally _
                                            | SynExpr.Sequential _
                                            | SynExpr.LetOrUse _ -> true
                                            | _ -> false

                                        if openEnded then
                                            {
                                                Range = lastElement.Range
                                                Original = textOfRange source lastElement.Range
                                                Replacement = $"({textOfRange source lastElement.Range}), {token}"
                                                MethodName = methodId.idText
                                                TokenName = token
                                                Kind = TokenGap.Omitted
                                            }
                                        else
                                            let at = Range.mkRange expr.Range.FileName inner.Range.End inner.Range.End

                                            {
                                                Range = at
                                                Original = ""
                                                Replacement = $", {token}"
                                                MethodName = methodId.idText
                                                TokenName = token
                                                Kind = TokenGap.Omitted
                                            }
                                    | _ -> ()
                            | _ -> ()
                        | None -> ()
                    | _ -> ()
                | _ -> ()

                // propagation: `CancellationToken.None` as an ARGUMENT while
                // the enclosing binding receives a real token — the chain is
                // cut one call too early on purpose-by-accident
                match expr with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when pathEndsWith "CancellationToken" "None" ids ->
                    match tokenFor expr.Range with
                    | Some token ->
                        // only as an argument: replacing a stored binding's
                        // RHS would rewrite intent this scan cannot see
                        let enclosingCall =
                            index.Exprs
                            |> Array.tryPick (fun (_, e) ->
                                match e with
                                | SynExpr.App(funcExpr = callee; argExpr = a) when
                                    Range.equals a.Range expr.Range
                                    || (match a with
                                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) ->
                                            es |> List.exists (fun x -> Range.equals x.Range expr.Range)
                                        | SynExpr.Paren(expr = inner) -> Range.equals inner.Range expr.Range
                                        | _ -> false)
                                    ->
                                    Some callee
                                | _ -> None)

                        let isArgument = enclosingCall.IsSome

                        // an explicit None on Task.Run / StartNew is the
                        // author choosing to always start the work
                        let schedulesWork =
                            match enclosingCall with
                            | Some(CallIdent calleeId) ->
                                resolveMember calleeId |> Option.exists (fun (_, mfv) -> schedulesDelegate mfv)
                            | _ -> false

                        let typedGate =
                            let noneId = List.last ids
                            let lineText = source.GetLineString(noneId.idRange.EndLine - 1)

                            match
                                check.GetSymbolUseAtLocation(
                                    noneId.idRange.EndLine,
                                    noneId.idRange.EndColumn,
                                    lineText,
                                    [ noneId.idText ]
                                )
                            with
                            | Some symbolUse ->
                                match symbolUse.Symbol with
                                | :? FSharpMemberOrFunctionOrValue as p ->
                                    (try
                                        p.DeclaringEntity
                                        |> Option.bind (fun e -> e.TryFullName)
                                        |> Option.map (fun n -> n.StartsWith "System.Threading.CancellationToken")
                                        |> Option.defaultValue false
                                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                         false)
                                | _ -> false
                            | None -> false

                        if isArgument && typedGate && not schedulesWork then
                            {
                                Range = expr.Range
                                Original = textOfRange source expr.Range
                                Replacement = token
                                MethodName = "CancellationToken.None"
                                TokenName = token
                                Kind = TokenGap.NonePassed
                            }
                    | None -> ()
                | _ -> ()
        ]

// ---- the loop that never observes the token ----

/// A loop awaiting inside, in a binding that receives a CancellationToken
/// and never reads it in the loop: no call in the body takes it, nothing
/// checks `IsCancellationRequested`, no local built with it is stepped,
/// so cancellation cannot stop the loop. Outside `async { }`, which
/// observes the token at every bind by itself; `task { }` does not.
type LoopSuggestion =
    {
        /// The whole loop.
        Range: range
        TokenName: string
        /// `token.ThrowIfCancellationRequested()` as the body's first
        /// statement (CR0170's fix), where the body starts on its own line
        /// below the loop header; a one-line body stays a note.
        Fix: (range * string * string) option
    }

let findUnobservedLoops
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : LoopSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let tokenParams =
            [
                for path, pat in index.Pats do
                    match pat with
                    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)); targetType = t) when
                        isCancellationTokenType t
                        ->
                        let binding =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                                | _ -> None)

                        match binding with
                        | Some bindingRange -> yield id.idText, bindingRange
                        | None -> ()
                    | _ -> ()
            ]

        // the one token in scope, as `find` reads it
        let tokenFor (r: range) =
            match
                tokenParams
                |> List.filter (fun (_, bindingRange) -> Range.rangeContainsRange bindingRange r)
                |> List.map fst
                |> List.distinct
            with
            | [ name ] -> Some name
            | _ -> None

        // the binding the token belongs to
        let scopeOf (token: string) (r: range) =
            tokenParams
            |> List.tryPick (fun (name, bindingRange) ->
                if name = token && Range.rangeContainsRange bindingRange r then
                    Some bindingRange
                else
                    None)

        // locals of that binding built WITH the token — `let enumerator =
        // source.GetAsyncEnumerator ct`, `let reader = open ct` (Fuuga): a
        // loop stepping one of them observes the token through it
        let carriers (token: string) (scope: range) =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | LetOrUseE lou when Range.rangeContainsRange scope e.Range ->
                    // a value, or a local function whose body reads the
                    // token (`let step () = task { do! Task.Delay(10, ct) }`)
                    lou.Bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = rhs)
                        | SynBinding(
                            headPat = SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))); expr = rhs)
                        | SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])); expr = rhs) when
                            System.Text.RegularExpressions.Regex.IsMatch(
                                textOfRange source rhs.Range,
                                identifierPattern token
                            )
                            ->
                            Some id.idText
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])

        let mentionsAny (names: string seq) (text: string) =
            names
            |> Seq.exists (fun n -> System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern n))

        // a loop that `find` already offers a token inside needs no second
        // message: the fix makes the loop observe it
        let offeredInside =
            find parseTree source check
            |> List.filter (fun s -> s.Kind = TokenGap.Omitted)
            |> List.map (fun s -> s.Range)

        let underAsync (path: SyntaxNode list) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr _)) ->
                    builder.idText.StartsWith "async"
                | _ -> false)

        // a loop in a `finally` is cleanup: nothing should throw there, a
        // cancellation check least of all (as CR0170 draws it)
        let underFinally (path: SyntaxNode list) (r: range) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.TryFinally(finallyExpr = f)) -> Range.rangeContainsRange f.Range r
                | _ -> false)

        let bindsInside (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (match e with
                    | LetOrUseE lou -> lou.IsBang
                    | SynExpr.DoBang _
                    | SynExpr.MatchBang _ -> true
                    | _ -> false))

        // the fix: a zero-width insert at the body's first statement, the
        // statement itself moving to the next line at its own indentation
        let checkAtTop (token: string) (loop: SynExpr) =
            let body =
                match loop with
                | SynExpr.While(doExpr = b)
                | SynExpr.ForEach(bodyExpr = b)
                | SynExpr.For(doBody = b) -> Some b
                | _ -> None

            match body with
            | Some b when
                b.Range.StartLine > loop.Range.StartLine
                // the body heads its line: nothing before it to move
                && (source.GetLineString(b.Range.StartLine - 1)).Substring(0, b.Range.StartColumn).Trim() = ""
                ->
                let at = Range.mkRange loop.Range.FileName b.Range.Start b.Range.Start
                let indent = String.replicate b.Range.StartColumn " "
                Some(at, "", token + ".ThrowIfCancellationRequested()\n" + indent)
            | _ -> None

        let unobserved =
            [
                for path, e in index.Exprs do
                    // an AWAITING loop: one that runs long enough for
                    // cancellation to matter, and whose binds are where a
                    // token would be observed. A synchronous `while` draining
                    // a buffer (`while reader.TryRead(&tok) do`) is bounded
                    // by what is already there
                    let loop =
                        match e with
                        | SynExpr.While _
                        | SynExpr.ForEach _
                        | SynExpr.For _ -> bindsInside e.Range
                        | _ -> false

                    if loop && not (underAsync path) && not (underFinally path e.Range) then
                        match tokenFor e.Range with
                        | Some token ->
                            let text = textOfRange source e.Range

                            let observed =
                                System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern token)
                                || (match scopeOf token e.Range with
                                    | Some scope -> mentionsAny (carriers token scope) text
                                    | None -> false)

                            if
                                not observed
                                && not (offeredInside |> List.exists (fun r -> Range.rangeContainsRange e.Range r))
                            then
                                {
                                    Range = e.Range
                                    TokenName = token
                                    Fix = checkAtTop token e
                                }
                        | None -> ()
            ]

        // the outermost loop carries the note; a check at its top covers
        // the loops nested in it
        unobserved
        |> List.filter (fun s ->
            not (
                unobserved
                |> List.exists (fun outer ->
                    not (Range.equals outer.Range s.Range)
                    && Range.rangeContainsRange outer.Range s.Range)
            ))
