/// FR0152: `ConcurrentDictionary.GetOrAdd` whose VALUE captures a failure -
/// a `Task`, `ValueTask` or `Lazy`. The failure is then cached, and every
/// later reader gets it.
///
///     let cache = ConcurrentDictionary&lt;_, Task&lt;_&gt;&gt;()
///     let entry = cache.GetOrAdd(arguments, addCache)
///
/// A faulted task and a faulted `Lazy` both REMEMBER the exception: the
/// entry stays in the dictionary, and every subsequent GetOrAdd returns the
/// same failed value rather than retrying. One transient failure - a
/// timeout, a cold dependency - becomes permanent for the process's
/// lifetime, and it looks like the dependency is still down long after it
/// recovered.
///
/// Deliberately narrow, gated on the VALUE TYPE. A factory that simply
/// THROWS is safe and is not reported: GetOrAdd propagates the exception
/// and stores nothing, so the next caller retries. Only a value that
/// captured the failure instead of raising it has this problem, which is
/// why an untyped `GetOrAdd` never fires.
///
/// Note-only. The remedy is to remove the entry when the value faults,
/// which is a change to how the cache is designed rather than a rewrite of
/// this expression.
module FSharp.Refactor.CachedFailure

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

type Suggestion =
    {
        /// The `GetOrAdd` call site.
        Range: range
        /// "Task", "ValueTask" or "Lazy" - what captured the failure.
        ValueKind: string
    }

let private strip (t: FSharpType) =
    let rec go (t: FSharpType) (fuel: int) =
        if fuel <= 0 then
            t
        elif t.HasTypeDefinition && t.TypeDefinition.IsFSharpAbbreviation then
            go t.TypeDefinition.AbbreviatedType (fuel - 1)
        else
            t

    go t 16

/// The value types that remember a failure instead of raising it.
let private capturedFailureKind (t: FSharpType) =
    try
        let t = strip t

        if not t.HasTypeDefinition then
            None
        else
            match t.TypeDefinition.TryFullName with
            | Some "System.Threading.Tasks.Task"
            | Some "System.Threading.Tasks.Task`1" -> Some "Task"
            | Some "System.Threading.Tasks.ValueTask"
            | Some "System.Threading.Tasks.ValueTask`1" -> Some "ValueTask"
            | Some "System.Lazy`1" -> Some "Lazy"
            | _ -> None
    with _ -> // an unreadable type is not one of ours; fsharpanalyzer: ignore-line FR0055
        None

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // GetOrAdd's RETURN type is the dictionary's value type, which is the
        // whole question here - no need to reconstruct the receiver's generics
        let valueKind (id: Ident) =
            try
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as m ->
                        let onConcurrentDictionary =
                            (OptionModule.enclosingFullName m)
                                .StartsWith "System.Collections.Concurrent.ConcurrentDictionary"

                        if onConcurrentDictionary then
                            capturedFailureKind m.ReturnParameter.Type
                        else
                            None
                    | _ -> None
                | None -> None
            with _ -> // fsharpanalyzer: ignore-line FR0055
                None

        [ for _, e in index.Exprs do
              match e with
              | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                  ids.Length >= 2 && (List.last ids).idText = "GetOrAdd"
                  ->
                  match valueKind (List.last ids) with
                  | Some kind ->
                      yield
                          { Range = (List.last ids).idRange
                            ValueKind = kind }
                  | None -> ()
              | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = ids))) when
                  not ids.IsEmpty && (List.last ids).idText = "GetOrAdd"
                  ->
                  match valueKind (List.last ids) with
                  | Some kind -> yield { Range = (List.last ids).idRange; ValueKind = kind }
                  | None -> ()
              | _ -> () ]
