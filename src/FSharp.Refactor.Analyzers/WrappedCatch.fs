/// FR0181 (correctness, note), twin of the C# rule: a handler for a
/// specific exception around a blocking wait, where the task's exception
/// never arrives as itself.
///
///     try
///         work.Wait()
///     with
///     | :? NotFoundException -> register ()      // not reached by the task's failure
///
/// `Task.Wait()`, `.Result`, `Task.WaitAll` and `Task.WaitAny` raise an
/// `AggregateException` that WRAPS what the task threw. A `:? T` handler
/// sees only what the `try` body throws directly, so the failure it was
/// written for passes it by - to a catch-all if there is one, out of the
/// function if not.
///
/// The shapes: a `try ... with` whose body blocks on a task (typed: the
/// member belongs to System.Threading.Tasks.Task), with a `:? T` clause
/// where T is neither `AggregateException` nor `exn`/`Exception`, and no
/// clause for `AggregateException`. A wait under a lambda does not run in
/// the body and is not read.
///
/// Note-only on a sweep. Whether the handler should look one level down
/// (`InnerException`) or at the root cause (`GetBaseException()`) is not
/// in the code, so the editor offers both as a second clause - for a
/// one-line clause that does not use its own exception value, the one
/// shape where the body can be repeated as written.
/// `GetAwaiter().GetResult()` unwraps and is not this shape; it is not
/// offered either - it only hides the block.
module FSharp.Refactor.WrappedCatch

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `:? T` pattern.
        Range: range
        /// T as written.
        TypeText: string
        /// The blocking member: "Wait", "Result", "WaitAll", "WaitAny".
        Wait: string
        /// A catch-all clause follows and receives the wrapped failure.
        HasCatchAll: bool
        /// The clause to add, reading `InnerException`: insertion point and text.
        InnerOffer: (range * string) option
        /// The same, reading `GetBaseException()`.
        BaseOffer: (range * string) option
    }

let private waits = set [ "Wait"; "Result"; "WaitAll"; "WaitAny" ]

let private general =
    set [ "System.Exception"; "System.AggregateException"; "System.SystemException" ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let onTask (ident: Ident) =
            match BlockingSites.declaringEntityName check source ident with
            | Some name -> name.StartsWith "System.Threading.Tasks.Task"
            | None -> false

        let typeFullName (ident: Ident) =
            try
                match BlockingSites.symbolAt check source ident with
                | Some(:? FSharpEntity as entity) -> entity.TryFullName
                | _ -> None
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                None

        // the blocking member the body calls directly, lambdas excluded
        let blockingIn (body: SynExpr) =
            AstIndex.exprsWithin index body.Range
            |> Array.tryPick (fun (path, e) ->
                let deferred =
                    path
                    |> List.exists (fun node ->
                        match node with
                        | SyntaxNode.SynExpr(SynExpr.Lambda _ | SynExpr.MatchLambda _ as lambda) ->
                            Range.rangeContainsRange body.Range lambda.Range
                        | _ -> false)

                if deferred then
                    None
                else
                    match e with
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                        let last = List.last ids

                        if waits.Contains last.idText && onTask last then
                            Some last.idText
                        else
                            None
                    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                        let last = List.last ids

                        if waits.Contains last.idText && onTask last then
                            Some last.idText
                        else
                            None
                    | _ -> None)

        // an F# exception declaration (`exception NotFound of string`) used
        // as a pattern - `| NotFound name ->` - or `Failure`, FSharp.Core's
        // pattern for a plain exception with a message: both test the
        // exception itself, like `:? T`
        let exceptionPattern (p: SynPat) =
            match p with
            | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                let last = List.last ids

                (try
                    match BlockingSites.symbolAt check source last with
                    | Some(:? FSharpEntity as entity) when entity.IsFSharpExceptionDeclaration -> ValueSome last
                    | Some(:? FSharpActivePatternCase as case) when
                        case.Name = "Failure"
                        && (case.Group.DeclaringEntity
                            |> Option.bind (fun e -> e.TryFullName)
                            |> Option.exists (fun n -> n.StartsWith "Microsoft.FSharp.Core"))
                        ->
                        ValueSome last
                    | _ -> ValueNone
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     ValueNone)
            | _ -> ValueNone

        // `:? T` / `:? T as e`: the type's last identifier and the binder
        let typeTest (p: SynPat) =
            match p with
            | SynPat.IsInst(pat = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
                ValueSome(List.last ids, ValueNone)
            | SynPat.As(
                lhsPat = SynPat.IsInst(pat = SynType.LongIdent(SynLongIdent(id = ids)))
                rhsPat = SynPat.Named(ident = SynIdent(ident = binder))) when not ids.IsEmpty ->
                ValueSome(List.last ids, ValueSome binder)
            | _ -> ValueNone

        let word (name: string) =
            System.Text.RegularExpressions.Regex(@"\b" + System.Text.RegularExpressions.Regex.Escape name + @"\b")

        [
            for _, e in index.Exprs do
                match e with
                | SynExpr.TryWith(tryExpr = body; withCases = clauses) when not (spansDirective source e.Range) ->
                    let clauseText =
                        clauses
                        |> List.map (fun (SynMatchClause(pat = p)) -> textOfRange source p.Range)
                        |> String.concat "\n"

                    if not (clauseText.Contains "AggregateException") then
                        match blockingIn body with
                        | Some wait ->
                            let hasCatchAll =
                                clauses
                                |> List.exists (fun (SynMatchClause(pat = p; whenExpr = guard)) ->
                                    guard.IsNone
                                    && (match p with
                                        | SynPat.Wild _
                                        | SynPat.Named _ -> true
                                        | _ -> false))

                            let wholeText = textOfRange source e.Range

                            let fresh =
                                if (word "aggregate").IsMatch wholeText then
                                    "aggregateEx"
                                else
                                    "aggregate"

                            for SynMatchClause(pat = p; whenExpr = guard; resultExpr = result; range = clauseRange) in
                                clauses do
                                match typeTest p with
                                | ValueSome(typeIdent, binder) ->
                                    match typeFullName typeIdent with
                                    | Some full when not (general.Contains full) ->
                                        let typeText =
                                            match p with
                                            | SynPat.IsInst(pat = t)
                                            | SynPat.As(lhsPat = SynPat.IsInst(pat = t)) -> textOfRange source t.Range
                                            | _ -> typeIdent.idText

                                        let bodyText = textOfRange source result.Range

                                        let binderUsed =
                                            match binder with
                                            | ValueSome b -> (word b.idText).IsMatch bodyText
                                            | ValueNone -> false

                                        // the clause starts its own line behind
                                        // a bar, and ends on that line
                                        let line = source.GetLineString(clauseRange.StartLine - 1)
                                        let lead = line.Substring(0, min p.Range.StartColumn line.Length)
                                        let barred = lead.Trim() = "|"

                                        let offer (inner: string) =
                                            if
                                                barred
                                                && guard.IsNone
                                                && not binderUsed
                                                && clauseRange.StartLine = result.Range.EndLine
                                            then
                                                let indent = lead.Substring(0, lead.IndexOf '|')

                                                let at =
                                                    Range.mkRange e.Range.FileName result.Range.End result.Range.End

                                                Some(
                                                    at,
                                                    $"\n{indent}| :? System.AggregateException as {fresh} when ({fresh}.{inner} :? {typeText}) -> {bodyText}"
                                                )
                                            else
                                                None

                                        {
                                            Range = p.Range
                                            TypeText = typeText
                                            Wait = wait
                                            HasCatchAll = hasCatchAll
                                            InnerOffer = offer "InnerException"
                                            BaseOffer = offer "GetBaseException()"
                                        }
                                    | _ -> ()
                                | ValueNone ->
                                    // the body binds the pattern's fields, so
                                    // it cannot be repeated under another
                                    // pattern: noted, nothing offered
                                    match exceptionPattern p with
                                    | ValueSome name ->
                                        {
                                            Range = p.Range
                                            TypeText = name.idText
                                            Wait = wait
                                            HasCatchAll = hasCatchAll
                                            InnerOffer = None
                                            BaseOffer = None
                                        }
                                    | ValueNone -> ()
                        | None -> ()
                | _ -> ()
        ]
