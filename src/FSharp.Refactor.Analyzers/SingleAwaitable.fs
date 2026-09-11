/// Refactoring note (performance, CA1842/CA1843): combinators over a
/// SINGLE awaitable add allocation and scheduling indirection for nothing.
///
///     Task.WhenAll [| t |]       // await t directly
///     Task.WaitAll [| t |]       // t.Wait() — or better, await it
///     Async.Parallel [ comp ]    // nothing runs in parallel
///
/// Advice only: the direct form changes the result type (WhenAll returns
/// Task where the task itself is Task<'T>; Async.Parallel returns
/// Async<'T[]> where the computation is Async<'T>), so the author chooses
/// the landing shape.
///
/// `Task`/`Async` are typed-gated to the BCL/FSharp.Core entities, and
/// only literal one-element collections match — a variable that happens
/// to hold one task is invisible and out of scope.
module FSharp.Refactor.SingleAwaitable

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// e.g. "Task.WhenAll".
        CallName: string
        /// The editor's fix: the call replaced by its one element. The
        /// result type changes (Task<'T[]> to Task<'T>), so the author
        /// takes it, a sweep never does.
        Fix: (range * string * string) option
    }

let private gatedCalls =
    [ ("Task", "WhenAll"), "System.Threading.Tasks.Task"
      ("Task", "WaitAll"), "System.Threading.Tasks.Task"
      ("Async", "Parallel"), "Microsoft.FSharp.Control.FSharpAsync" ]
    |> Map.ofList

/// A literal collection with exactly one plain element.
[<return: Struct>]
let private (|SingleElementLiteral|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.ArrayOrList(_, [ _ ], _) -> ValueSome()
    | SynExpr.ArrayOrListComputed(expr = inner) ->
        match inner with
        | SynExpr.Sequential _
        | SynExpr.IndexRange _
        | SynExpr.For _
        | SynExpr.ForEach _
        | SynExpr.While _
        | SynExpr.YieldOrReturn _
        | SynExpr.YieldOrReturnFrom _
        | SynExpr.IfThenElse _
        | SynExpr.Match _ -> ValueNone
        | _ -> ValueSome()
    | _ -> ValueNone

let private resolvesToGatedEntity (check: FSharpCheckFileResults) (source: ISourceText) (entity: string) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> OptionModule.enclosingFullName value = entity
        | _ -> false
    | None -> false

/// Find single-awaitable combinator calls. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the one element of the literal, for the editor's fix
        let singleElement (arg: SynExpr) =
            match stripParens arg with
            | SynExpr.ArrayOrList(_, [ only ], _) -> Some only
            | SynExpr.ArrayOrListComputed(expr = inner) -> Some inner
            | _ -> None

        [ for _, expr in index.Exprs do
              match expr with
              | SynExpr.App(
                  isInfix = false
                  funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                  argExpr = SingleElementLiteral as arg) ->
                  match gatedCalls.TryFind(m.idText, f.idText) with
                  | Some entity when resolvesToGatedEntity check source entity f ->
                      { Range = expr.Range
                        CallName = $"{m.idText}.{f.idText}"
                        Fix =
                          singleElement arg
                          |> Option.map (fun only ->
                              // `Task.WaitAll [| t |]` is a blocking unit
                              // statement: its element alone would DROP the
                              // wait (a bare Task in statement position), so
                              // it keeps one — `t.Wait()`. The awaiting
                              // combinators unwrap to the element itself
                              let replacement =
                                  if f.idText = "WaitAll" then
                                      $"{atomicText source only}.Wait()"
                                  else
                                      textOfRange source only.Range

                              expr.Range, textOfRange source expr.Range, replacement) }
                  | _ -> ()
              | _ -> () ]
