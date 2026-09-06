/// Two exception-flow notes:
///
/// 1. Raise inside `finally` (FR0063, CA2219): a throw in a finally block
///    replaces whatever exception was already in flight — the original
///    failure vanishes. Raises the finally itself catches are fine.
///
/// 2. Reserved exceptions (FR0064, CA2201): OutOfMemoryException,
///    StackOverflowException, IndexOutOfRangeException,
///    NullReferenceException, AccessViolationException and
///    ExecutionEngineException belong to the runtime; raising them
///    manually misleads every catcher and debugger. InvalidOperation/
///    Argument exceptions say what actually happened.
module FSharp.Refactor.ExceptionRules

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type FinallySuggestion = { Range: range }

type ReservedSuggestion =
    {
        Range: range
        /// The reserved exception's type name.
        TypeName: string
    }

let private raisingFunctions =
    set [ "raise"; "failwith"; "failwithf"; "invalidOp"; "invalidArg"; "nullArg" ]

let private reservedExceptions =
    set
        [ "OutOfMemoryException"
          "StackOverflowException"
          "IndexOutOfRangeException"
          "NullReferenceException"
          "AccessViolationException"
          "ExecutionEngineException" ]

/// The constructed exception type's name in `raise (<Type>(...))`.
[<return: Struct>]
let private (|RaisedTypeName|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = arg) when fn.idText = "raise" ->
        match stripParens arg with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id) -> ValueSome id.idText
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
            not ids.IsEmpty
            ->
            ValueSome (List.last ids).idText
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
            ValueSome (List.last ids).idText
        | _ -> ValueNone
    | _ -> ValueNone

/// Find both exception-flow smells.
let find (parseTree: ParsedInput) (source: ISourceText) : FinallySuggestion list * ReservedSuggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree
    let finallies = ResizeArray<FinallySuggestion>()
    let reserved = ResizeArray<ReservedSuggestion>()

    // raise-like application ranges
    let raiseSites =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn) when raisingFunctions.Contains fn.idText ->
                Some e.Range
            | _ -> None)

    // FR0063: raises in finally blocks, minus ones a nested try-with handles
    for _, e in index.Exprs do
        match e with
        | SynExpr.TryFinally(finallyExpr = fin) ->
            let handled =
                index.Exprs
                |> Array.choose (fun (_, inner) ->
                    match inner with
                    | SynExpr.TryWith(tryExpr = t) when Range.rangeContainsRange fin.Range inner.Range -> Some t.Range
                    | _ -> None)

            for site in raiseSites do
                if
                    Range.rangeContainsRange fin.Range site
                    && not (handled |> Array.exists (fun h -> Range.rangeContainsRange h site))
                then
                    finallies.Add { Range = site }
        | _ -> ()

    // a match whose sibling arms raise three or more DISTINCT exception
    // types is a dispatch table — FCS's `SimulateException` fault injection
    // raises OutOfMemory, AccessViolation, IndexOutOfRange and a dozen
    // others one per arm, by request; the reserved ones are the point
    let dispatchTableArms =
        let clausesOf (e: SynExpr) =
            match e with
            | SynExpr.Match(clauses = cs)
            | SynExpr.MatchBang(clauses = cs)
            | SynExpr.MatchLambda(matchClauses = cs) -> cs
            | _ -> []

        index.Exprs
        |> Array.collect (fun (_, e) ->
            let arms =
                clausesOf e
                |> List.choose (fun (SynMatchClause(resultExpr = arm)) ->
                    match stripParens arm with
                    | RaisedTypeName name -> Some(arm.Range, name)
                    | _ -> None)

            if (arms |> List.map snd |> List.distinct |> List.length) >= 3 then
                arms |> List.map fst |> Array.ofList
            else
                [||])

    let inDispatchTable (r: range) =
        dispatchTableArms |> Array.exists (fun arm -> Range.rangeContainsRange arm r)

    // FR0064: reserved exception constructions
    for _, e in index.Exprs do
        match e with
        | RaisedTypeName name when reservedExceptions.Contains name && not (inDispatchTable e.Range) ->
            reserved.Add { Range = e.Range; TypeName = name }
        | _ -> ()

    List.ofSeq finallies, List.ofSeq reserved
