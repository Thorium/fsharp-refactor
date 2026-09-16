/// Refactoring (performance, CA1853/CA1868): a membership guard before an
/// operation that already handles absence just doubles the lookup.
///
///     if d.ContainsKey k then d.Remove k |> ignore   →  d.Remove k |> ignore
///     if not (s.Contains x) then s.Add x |> ignore   →  s.Add x |> ignore
///     if s.Contains x then s.Remove x |> ignore      →  s.Remove x |> ignore
///
/// Dictionary.Remove returns false for a missing key; HashSet/SortedSet
/// Add and Remove return false when the element is already there / absent.
/// The guarded and unguarded forms have identical effects and the result
/// is discarded either way, so the fix is behavior-preserving.
///
/// Safety rules:
///   - the receiver is the same plain identifier in guard and action, and
///     the key is a pure atom with identical source text in both
///   - the `if` has no else branch and the action is the then-branch's
///     only statement
///   - the action method resolves (typed check results) to Dictionary,
///     HashSet, or SortedSet — semantics elsewhere are not assumed
module FSharp.Refactor.RedundantGuard

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
        /// "ContainsKey" or "Contains", for the message.
        GuardName: string
        /// "Remove" or "Add", for the message.
        ActionName: string
    }

/// Entities whose Remove/Add return false instead of throwing on a miss.
let private gatedEntities =
    [
        "System.Collections.Generic.Dictionary`", set [ "Remove" ]
        "System.Collections.Generic.HashSet`", set [ "Add"; "Remove" ]
        "System.Collections.Generic.SortedSet`", set [ "Add"; "Remove" ]
    ]

/// `<recvIdent>.<method> <atomKey>` (parens tolerated around the key).
[<return: Struct>]
let private (|InstanceCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ recv; method ])); argExpr = arg) ->
        let key = stripParens arg

        if isPureAtom key then
            ValueSome(recv, method, key)
        else
            ValueNone
    | _ -> ValueNone

/// The action call inside the then-branch: bare, `|> ignore`, or `ignore (...)`.
[<return: Struct>]
let private (|ActionCall|_|) (e: SynExpr) =
    match e with
    | InstanceCall(recv, method, key) -> ValueSome(recv, method, key)
    | PipeApp(InstanceCall(recv, method, key), IdentName "ignore") -> ValueSome(recv, method, key)
    | SynExpr.App(isInfix = false; funcExpr = IdentName "ignore"; argExpr = arg) ->
        match stripParens arg with
        | InstanceCall(recv, method, key) -> ValueSome(recv, method, key)
        | _ -> ValueNone
    | _ -> ValueNone

/// Does the action method resolve to a collection with miss-tolerant
/// semantics for that method?
let private resolvesToGated (check: FSharpCheckFileResults) (source: ISourceText) (methodId: Ident) =
    let r = methodId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ methodId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let enclosing = OptionModule.enclosingFullName value

            gatedEntities
            |> List.exists (fun (prefix, methods) -> enclosing.StartsWith prefix && methods.Contains methodId.idText)
        | _ -> false
    | None -> false

/// Find redundant membership guards. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.IfThenElse(
                    ifExpr = cond
                    thenExpr = ActionCall(actRecv, actMethod, actKey) as thenExpr
                    elseExpr = None
                    trivia = trivia) when not trivia.IsElif && isSingleLine expr.Range ->
                    // (guard method, negated?) that licenses each action
                    let guard =
                        match stripParens cond with
                        | InstanceCall(gRecv, gMethod, gKey) -> Some(gRecv, gMethod, gKey, false)
                        | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = inner) ->
                            match stripParens inner with
                            | InstanceCall(gRecv, gMethod, gKey) -> Some(gRecv, gMethod, gKey, true)
                            | _ -> None
                        | _ -> None

                    match guard with
                    | Some(gRecv, gMethod, gKey, negated) when
                        gRecv.idText = actRecv.idText
                        && textOfRange source gKey.Range = textOfRange source actKey.Range
                        && (match gMethod.idText, negated, actMethod.idText with
                            | "ContainsKey", false, "Remove"
                            | "Contains", false, "Remove"
                            | "Contains", true, "Add" -> true
                            | _ -> false)
                        && resolvesToGated check source actMethod
                        ->
                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = textOfRange source thenExpr.Range
                            GuardName = gMethod.idText
                            ActionName = actMethod.idText
                        }
                    | _ -> ()
                | _ -> ()
        ]
