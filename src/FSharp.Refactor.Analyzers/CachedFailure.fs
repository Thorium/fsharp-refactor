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
/// Quiet where the code removes entries from that dictionary: a `TryRemove` or
/// `Remove` on its name, directly or through a cast (`(cache :>
/// ICollection&lt;KeyValuePair&lt;_, _&gt;&gt;).Remove(pair)`), in the declaration that binds
/// the name (a binding, or a type's `let`), or in the file when none of them
/// binds it. Whether the removal runs on a fault is not read. Also quiet where
/// the scan cannot tell: the dictionary's bare name handed on (`evict cache
/// key`, `let view = cache`, `member _.Cache = cache`), a removal on something
/// with no name (`get().TryRemove k`), or a `GetOrAdd` on something with no name
/// and any removal in the file.
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

/// `cache` of `cache.TryRemove`, `this.cache.TryRemove`.
let private ownerSegment (ids: Ident list) =
    match List.rev ids with
    | _ :: owner :: _ -> Some owner.idText
    | _ -> None

/// The name a receiver expression reaches a dictionary by, through parens and
/// casts; `None` for anything else, a call or an index.
[<TailCall>]
let rec private receiverName (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner)
    | SynExpr.Upcast(expr = inner)
    | SynExpr.Downcast(expr = inner) -> receiverName inner
    | SynExpr.Ident pid -> Some pid.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idText
    | _ -> None

/// The owner of a `DotGet` member call: the segment before the member, or the
/// receiver expression's name.
let private dotGetOwner (target: SynExpr) (ids: Ident list) =
    ownerSegment ids |> Option.orElseWith (fun () -> receiverName target)

let private isRemoval (ids: Ident list) =
    match List.tryLast ids with
    | Some last -> last.idText = "TryRemove" || last.idText = "Remove"
    | None -> false

/// A removal, with the name of what it removes from where it has one.
[<return: Struct>]
let private (|Removal|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 && isRemoval ids ->
        ValueSome(ownerSegment ids)
    | SynExpr.DotGet(expr = target; longDotId = SynLongIdent(id = ids)) when isRemoval ids ->
        ValueSome(dotGetOwner target ids)
    | _ -> ValueNone

/// Is this bare mention of the dictionary something other than reading its
/// entries, so that what happens to it is out of the scan's sight?
let private handedOn (path: SyntaxNode list) (mention: range) =
    match path with
    // `cache[k]`, `cache.[k]`, `for kv in cache do`
    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f)) :: _ when Range.equals f.Range mention -> false
    | SyntaxNode.SynExpr(SynExpr.DotIndexedGet _ | SynExpr.DotIndexedSet _) :: _ -> false
    | SyntaxNode.SynExpr(SynExpr.ForEach(enumExpr = source)) :: _ when Range.equals source.Range mention -> false
    | _ -> true

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the nearest binding or type around the call that binds the name, or
        // the whole file: a module's `let`, or a name this scan cannot place
        let scopeOf (owner: string) (path: SyntaxNode list) =
            let binds (r: range) =
                AstIndex.patsWithin index r
                |> Array.exists (fun (_, p) ->
                    match p with
                    | SynPat.Named(ident = SynIdent(ident = pid)) -> pid.idText = owner
                    | _ -> false)

            let enclosing =
                path
                |> List.tryPick (fun node ->
                    match node with
                    | SyntaxNode.SynBinding b when binds b.RangeOfBindingWithRhs -> Some b.RangeOfBindingWithRhs
                    | SyntaxNode.SynTypeDefn t when binds t.Range -> Some t.Range
                    | _ -> None)

            match enclosing with
            | Some r -> AstIndex.exprsWithin index r
            | None -> index.Exprs

        // runs for a call already typed as a capturing GetOrAdd, which is rare
        let removesFromElsewhere (e: SynExpr) =
            let removal =
                match e with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) -> List.tryLast ids
                | _ -> None

            match removal with
            | Some name ->
                let lineText = source.GetLineString(name.idRange.EndLine - 1)

                match
                    OptionModule.symbolUseAt
                        check
                        (name.idRange.EndLine, name.idRange.EndColumn, lineText, [ name.idText ])
                with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as m ->
                        let owner = OptionModule.enclosingFullName m

                        owner = "System.String"
                        || owner.StartsWith "System.Collections.Generic.List"
                        || owner.StartsWith "Microsoft.FSharp.Collections"
                    | _ -> false
                | None -> false
            | None -> false

        let removedOrUnknown (owner: string option) (path: SyntaxNode list) =
            match owner with
            | None ->
                index.Exprs
                |> Array.exists (fun (_, e) ->
                    match e with
                    | Removal _ -> not (removesFromElsewhere e)
                    | _ -> false)
            | Some name ->
                scopeOf name path
                |> Array.exists (fun (mentionPath, e) ->
                    match e with
                    | Removal(Some target) -> target = name
                    | Removal None -> not (removesFromElsewhere e)
                    | SynExpr.Ident pid -> pid.idText = name && handedOn mentionPath pid.idRange
                    | _ -> false)

        // GetOrAdd's RETURN type is the dictionary's value type, which is the
        // whole question here - no need to reconstruct the receiver's generics
        let valueKind (id: Ident) =
            try
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as m ->
                        let onConcurrentDictionary =
                            (OptionModule.enclosingFullName m).StartsWith
                                "System.Collections.Concurrent.ConcurrentDictionary"

                        if onConcurrentDictionary then
                            capturedFailureKind m.ReturnParameter.Type
                        else
                            None
                    | _ -> None
                | None -> None
            with _ -> // fsharpanalyzer: ignore-line FR0055
                None

        [
            for path, e in index.Exprs do
                match e with
                | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                    ids.Length >= 2 && (List.last ids).idText = "GetOrAdd"
                    ->
                    match valueKind (List.last ids) with
                    | Some kind when not (removedOrUnknown (ownerSegment ids) path) ->
                        yield
                            {
                                Range = (List.last ids).idRange
                                ValueKind = kind
                            }
                    | _ -> ()
                | SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.DotGet(expr = target; longDotId = SynLongIdent(id = ids))) when
                    not ids.IsEmpty && (List.last ids).idText = "GetOrAdd"
                    ->
                    match valueKind (List.last ids) with
                    | Some kind when not (removedOrUnknown (dotGetOwner target ids) path) ->
                        yield
                            {
                                Range = (List.last ids).idRange
                                ValueKind = kind
                            }
                    | _ -> ()
                | _ -> ()
        ]
