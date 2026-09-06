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
            [ for path, pat in index.Pats do
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
                  | _ -> () ]

        // the single in-scope token for a call site, if there is exactly one
        let tokenFor (callRange: range) =
            let inScope =
                tokenParams
                |> List.filter (fun (_, bindingRange) -> Range.rangeContainsRange bindingRange callRange)

            match inScope |> List.map fst |> List.distinct with
            | [ name ] -> Some name
            | _ -> None

        [ for _, expr in index.Exprs do
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
                                      { Range = unitRange
                                        Original = "()"
                                        Replacement = $"({token})"
                                        MethodName = methodId.idText
                                        TokenName = token
                                        Kind = TokenGap.Omitted }
                                  | SynExpr.Paren(expr = inner) ->
                                      let at = Range.mkRange expr.Range.FileName inner.Range.End inner.Range.End

                                      { Range = at
                                        Original = ""
                                        Replacement = $", {token}"
                                        MethodName = methodId.idText
                                        TokenName = token
                                        Kind = TokenGap.Omitted }
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
                          { Range = expr.Range
                            Original = textOfRange source expr.Range
                            Replacement = token
                            MethodName = "CancellationToken.None"
                            TokenName = token
                            Kind = TokenGap.NonePassed }
                  | None -> ()
              | _ -> () ]
