/// Refactoring (performance, CA1836): prefer IsEmpty over Count for
/// emptiness checks on the concurrent collections.
///
///     q.Count = 0     →  q.IsEmpty
///     q.Count > 0     →  not q.IsEmpty
///
/// ConcurrentQueue/Stack/Bag compute Count by walking their segments —
/// O(n) with a snapshot — while IsEmpty peeks at the head. The rewrite is
/// gated to those types (a List's Count is a field read and fine).
module FSharp.Refactor.CountIsEmpty

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

let private gatedEntities =
    [
        "System.Collections.Concurrent.ConcurrentQueue`"
        "System.Collections.Concurrent.ConcurrentStack`"
        "System.Collections.Concurrent.ConcurrentBag`"
    ]

let private resolvesToGatedCount (check: FSharpCheckFileResults) (source: ISourceText) (countId: Ident) =
    let r = countId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ countId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let enclosing = OptionModule.enclosingFullName value

            gatedEntities |> List.exists enclosing.StartsWith
        | _ -> false
    | None -> false

/// `recv.Count` where recv is a name or a dotted path — a ConcurrentQueue
/// naturally lives in a field, so `this.queue.Count` must count too.
[<return: Struct>]
let private (|CountAccess|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 && (List.last ids).idText = "Count" ->
        let recvIds = ids |> List.take (ids.Length - 1)
        ValueSome(identText recvIds, List.last ids)
    | _ -> ValueNone

/// Find emptiness checks through Count. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) ->
                    // (recv, negate the emptiness?) for each comparison shape
                    let interpretation =
                        match op.idText, stripParens lhs, stripParens rhs with
                        | "op_Equality", CountAccess(recv, countId), ZeroConst
                        | "op_Equality", ZeroConst, CountAccess(recv, countId) -> Some(recv, countId, false)
                        | "op_Inequality", CountAccess(recv, countId), ZeroConst
                        | "op_Inequality", ZeroConst, CountAccess(recv, countId)
                        | "op_GreaterThan", CountAccess(recv, countId), ZeroConst
                        | "op_LessThan", ZeroConst, CountAccess(recv, countId) -> Some(recv, countId, true)
                        | _ -> None

                    match interpretation with
                    | Some(recv, countId, negated) when
                        resolvesToGatedCount check source countId
                        && OptionModule.resolvesToCoreOperator check source op
                        ->
                        let test = $"{recv}.IsEmpty"

                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = if negated then $"not {test}" else test
                        }
                    | _ -> ()
                | _ -> ()
        ]
