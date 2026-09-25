/// Refactoring: mapping a collection and throwing the result away.
///
///     xs |> List.map f |> ignore      →  xs |> List.iter (f >> ignore)
///     xs |> Array.map f |> ignore     →  xs |> Array.iter (f >> ignore)
///     xs |> Seq.map f |> ignore       // note only: Seq.map is LAZY — this
///                                     // line runs NOTHING at all
///
/// For List/Array the rewrite is provably identical: iter applies f to the
/// same elements in the same order, and the results were discarded either
/// way — the only change is that no result list is allocated. For Seq the
/// original is a BUG (the FR0017 family): the pipeline builds a lazy
/// sequence and ignores it unevaluated, so no side effect ever runs —
/// making it run is a behavior change the author must confirm, hence a
/// note instead of a fix.
///
/// `map` and `ignore` are typed-gated against shadowing.
module FSharp.Refactor.MapIgnore

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        /// The collection module: "List", "Array", or "Seq".
        ModuleName: string
        /// None = the lazy-Seq advisory (no safe automatic rewrite).
        ReplacementText: string option
    }

let private mapModules =
    [
        "List", "Microsoft.FSharp.Collections.ListModule"
        "Array", "Microsoft.FSharp.Collections.ArrayModule"
        "Seq", "Microsoft.FSharp.Collections.SeqModule"
    ]
    |> Map.ofList

/// Does the `map` ident resolve to the FSharp.Core module function?
let private resolvesToCoreMap
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (moduleName: string)
    (mapId: Ident)
    =
    let r = mapId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ mapId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            mapModules.TryFind moduleName
            |> Option.exists (fun entity -> OptionModule.enclosingFullName value = entity)
        | _ -> false
    | None -> false

/// Find map-then-ignore pipelines. Requires typed check results for the
/// shadowing gates.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the ignored expression, whichever way ignore was spelled
        let (|IgnoredExpr|_|) (e: SynExpr) =
            match e with
            | PipeApp(inner, IdentName "ignore") -> Some(stripParens inner)
            | SynExpr.App(isInfix = false; funcExpr = IdentName "ignore"; argExpr = inner) -> Some(stripParens inner)
            | _ -> None

        // a map call in either spelling: `xs |> Module.map f` or
        // `Module.map f xs` — the direct Seq form is the one that runs
        // NOTHING when ignored, which is the very bug this rule exists for
        let (|MapCall|_|) (e: SynExpr) =
            match e with
            | PipeApp(sourceExpr,
                      SynExpr.App(
                          isInfix = false
                          funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; mapId ]))
                          argExpr = mapArg)) -> Some(sourceExpr, m, mapId, mapArg)
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; mapId ]))
                    argExpr = mapArg)
                argExpr = sourceExpr) -> Some(sourceExpr, m, mapId, mapArg)
            | _ -> None

        [
            for _, expr in index.Exprs do
                match expr with
                | IgnoredExpr(MapCall(sourceExpr, m, mapId, mapArg)) when
                    mapId.idText = "map"
                    && mapModules.ContainsKey m.idText
                    && isSingleLine expr.Range
                    && resolvesToCoreMap check source m.idText mapId
                    ->
                    // `ignore` itself must be FSharp.Core's, not a shadow
                    let ignoreIsCore =
                        AstIndex.exprsWithin index expr.Range
                        |> Array.exists (fun (_, e) ->
                            match e with
                            | SynExpr.Ident id when
                                id.idText = "ignore" && Range.rangeContainsRange expr.Range id.idRange
                                ->
                                OptionModule.resolvesToCoreOperator check source id
                            | _ -> false)

                    if ignoreIsCore then
                        let replacement =
                            if m.idText = "Seq" then
                                None
                            else
                                Some(
                                    $"{textOfRange source sourceExpr.Range} |> {m.idText}.iter ({argumentText source mapArg} >> ignore)"
                                )

                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ModuleName = m.idText
                            ReplacementText = replacement
                        }
                | _ -> ()
        ]
