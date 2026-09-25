/// FR0120 (fix): a log call inside an exception handler that never
/// mentions the caught exception — the one fact the handler exists to
/// record.
///
///     with ex ->                          with ex ->
///         logger.LogError("sync failed {Id}", id)
///                          →   logger.LogError(ex, "sync failed {Id}", id)
///
/// The primary fix passes the exception itself (ILogger's
/// exception-first overload; the SINK decides rendering). The editor
/// also offers `ex.GetBaseException()` — the root cause of a wrapped or
/// aggregate exception.
///
/// ANY existing mention of the exception in the call's arguments counts
/// as handled — `ex.Message` included: logging only the message is a
/// legitimate GDPR/PII choice, and this rule must not escalate it to a
/// full stack trace.
///
/// Typed-gated to Microsoft.Extensions.Logging's extension methods, so
/// a user type with a `LogError` member never matches.
module FSharp.Refactor.CatchLogException

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Zero-width: at the first argument, where `ex, ` goes (MEL and
        /// Serilog), or after the event stage, where
        /// ` |> Message.addExn ex` goes (Logary).
        Range: range
        ExceptionName: string
        LogMethod: string
        /// "MEL", "Serilog" or "Logary" — which spelling the fix takes.
        Family: string
    }

/// Microsoft.Extensions.Logging (the Abstractions package keeps the same
/// namespace), Serilog's static `Log` and `ILogger`, and Logary's event
/// constructors — the levels where an exception is the point.
let private logMethods = set [ "LogError"; "LogCritical"; "LogWarning" ]
let private serilogMethods = set [ "Error"; "Fatal"; "Warning" ]
let private logaryEvents = set [ "eventError"; "eventFatal"; "eventWarn" ]

/// The name a handler clause binds its exception to.
[<TailCall>]
let rec private exceptionNameOf (p: SynPat) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id)) -> ValueSome id.idText
    | SynPat.As(rhsPat = SynPat.Named(ident = SynIdent(ident = id))) -> ValueSome id.idText
    | SynPat.Paren(pat = inner) -> exceptionNameOf inner
    | _ -> ValueNone

[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // handler clauses that bind an exception, with their body ranges
        let handlers =
            [
                for _, e in index.Exprs do
                    match e with
                    | SynExpr.TryWith(withCases = cases) ->
                        for SynMatchClause(pat = p; resultExpr = result) in cases do
                            match exceptionNameOf p with
                            | ValueSome name -> yield name, result.Range
                            | ValueNone -> ()
                    | _ -> ()
            ]

        // the innermost handler an expression sits in
        let handlerOf (r: range) =
            handlers
            |> List.filter (fun (_, body) -> Range.rangeContainsRange body r)
            |> List.sortBy (fun (_, body) -> body.EndLine - body.StartLine, body.EndColumn)
            |> List.tryHead

        // which library an identifier belongs to, by the typed check
        let familyOf (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.bind (fun n ->
                            if n.StartsWith "Microsoft.Extensions.Logging" then
                                Some "MEL"
                            elif n.StartsWith "Serilog" then
                                Some "Serilog"
                            elif n.StartsWith "Logary" then
                                Some "Logary"
                            else
                                None)
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         None)
                | _ -> None
            | None -> None

        // ---- Logary: an event pipeline in a handler with no addExn ----
        let rec stages (e: SynExpr) =
            match e with
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)
                argExpr = right) when op.idText = "op_PipeRight" -> stages left @ [ right ]
            | SynExpr.Paren(expr = inner) -> stages inner
            | other -> [ other ]

        let isOuterPipe (path: SyntaxNode list) (e: SynExpr) =
            (match e with
             | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) ->
                 op.idText = "op_PipeRight"
             | _ -> false)
            && not (
                path
                |> List.exists (fun node ->
                    match node with
                    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) ->
                        op.idText = "op_PipeRight"
                    | SyntaxNode.SynExpr(SynExpr.App(
                        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op))) ->
                        op.idText = "op_PipeRight"
                    | _ -> false)
            )

        let logary =
            [
                for path, expr in index.Exprs do
                    if isOuterPipe path expr then
                        let chain = stages expr

                        // the event stage: applied, or point-free after the template
                        let eventStage =
                            chain
                            |> List.indexed
                            |> List.tryPick (fun (i, stage) ->
                                match stage with
                                | SynExpr.App(
                                    isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                                    ids.Length >= 2 && logaryEvents.Contains (List.last ids).idText
                                    ->
                                    Some(List.last ids, stage.Range)
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                    i = 1 && ids.Length >= 2 && logaryEvents.Contains (List.last ids).idText
                                    ->
                                    Some(List.last ids, stage.Range)
                                | _ -> None)

                        match eventStage, handlerOf expr.Range with
                        | Some(eventId, stageRange), Some(exName, _) when
                            not (Regex.IsMatch(textOfRange source expr.Range, identifierPattern exName))
                            && familyOf eventId = Some "Logary"
                            ->
                            {
                                Range = Range.mkRange expr.Range.FileName stageRange.End stageRange.End
                                ExceptionName = exName
                                LogMethod = eventId.idText
                                Family = "Logary"
                            }
                        | _ -> ()
            ]

        logary
        @ [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = CallIdent logId; argExpr = SynExpr.Paren(expr = inner)) when
                    (logMethods.Contains logId.idText || serilogMethods.Contains logId.idText)
                    // the exception-first overload only pairs with a template
                    // in FIRST position — `LogError(eventId, "msg")` wants the
                    // exception SECOND, and inserting it first matches nothing
                    && (match inner with
                        | SynExpr.Const(SynConst.String _, _)
                        | SynExpr.InterpolatedString _ -> true
                        | SynExpr.Tuple(exprs = first :: _) ->
                            (match first with
                             | SynExpr.Const(SynConst.String _, _)
                             | SynExpr.InterpolatedString _ -> true
                             | _ -> false)
                        | _ -> false)
                    ->
                    // the innermost handler this call sits in
                    let handler =
                        handlers
                        |> List.filter (fun (_, body) -> Range.rangeContainsRange body expr.Range)
                        |> List.sortBy (fun (_, body) -> body.EndLine - body.StartLine, body.EndColumn)
                        |> List.tryHead

                    match handler with
                    | Some(exName, _) when
                        // any mention of the exception — ex, ex.Message,
                        // ex.ToString() — means the author already chose what
                        // to record
                        not (Regex.IsMatch(textOfRange source inner.Range, identifierPattern exName))
                        ->
                        // typed gate: the method must be the library's own,
                        // and named the way that library names the level
                        let family =
                            match familyOf logId with
                            | Some "MEL" when logMethods.Contains logId.idText -> Some "MEL"
                            | Some "Serilog" when serilogMethods.Contains logId.idText -> Some "Serilog"
                            | _ -> None

                        match family with
                        | Some family ->
                            {
                                Range = Range.mkRange expr.Range.FileName inner.Range.Start inner.Range.Start
                                ExceptionName = exName
                                LogMethod = logId.idText
                                Family = family
                            }
                        | None -> ()
                    | _ -> ()
                | _ -> ()
        ]
