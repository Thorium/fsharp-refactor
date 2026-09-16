/// Refactoring: fuse two consecutive `map` stages of the same collection
/// module into one pass.
///
///     xs |> Array.map fst |> Array.map f   →  xs |> Array.map (fst >> f)
///     xs |> List.map snd |> List.map f     →  xs |> List.map (snd >> f)
///     xs |> Seq.map id |> Seq.map f        →  xs |> Seq.map f
///
/// For Array and List the win is the intermediate collection that stops
/// existing; for Seq it is one lazy wrapper fewer. The fused form applies
/// both functions to an element before touching the next one, where the
/// eager two-pass form ran the first function over EVERY element first —
/// an observable reordering if both functions have side effects. The rule
/// therefore only fires when the first mapper is one of the provably pure,
/// provably total projections `fst`, `snd`, or `id`: interleaving those
/// between calls of an arbitrary second mapper cannot be observed.
///
/// Safety rules: both stages must head the SAME module's `map` (a
/// Seq-to-Array boundary is FR0004's business, not ours); the first mapper
/// is a bare `fst`/`snd`/`id` identifier, parenthesized or not; both
/// stages single-line so the fused text stays a line.
module FSharp.Refactor.MapFusion

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range spanning the first map stage through the second.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The module whose two passes fused: Array, List, or Seq.
        Module: string
    }

let private collectionModules = set [ "Array"; "List"; "Seq" ]

/// `Module.map arg` as a pipeline stage.
[<return: Struct>]
let private (|MapStage|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = arg) when
        f.idText = "map" && collectionModules.Contains m.idText
        ->
        ValueSome(m.idText, arg)
    | _ -> ValueNone

/// A bare `fst`/`snd`/`id`, with or without parentheses — pure and total,
/// so running it between calls of the next mapper changes nothing.
[<return: Struct>]
let private (|PureProjection|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Ident i when i.idText = "fst" || i.idText = "snd" || i.idText = "id" -> ValueSome i.idText
    | _ -> ValueNone

/// Find `|> M.map <pure> |> M.map g` runs.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | PipeApp(PipeApp(_, (MapStage(m1, PureProjection projection) as fStage)),
                          (MapStage(m2, gArg) as gStage)) when
                    m1 = m2 && isSingleLine fStage.Range && isSingleLine gStage.Range
                    ->
                    let replacement =
                        if projection = "id" then
                            // `id >> g` is `g`: the first pass only copied
                            textOfRange source gStage.Range
                        else
                            let gText =
                                match gArg with
                                | SynExpr.Paren(expr = inner) -> textOfRange source inner.Range
                                | _ -> textOfRange source gArg.Range

                            $"%s{m1}.map (%s{projection} >> %s{gText})"

                    let fullRange =
                        Range.mkRange fStage.Range.FileName fStage.Range.Start gStage.Range.End

                    suggestions.Add
                        {
                            Range = fullRange
                            OriginalText = textOfRange source fullRange
                            ReplacementText = replacement
                            Module = m1
                        }
                | _ -> ()
        }

    AstIndex.replay collector parseTree

    suggestions
    |> Seq.filter (fun s -> not (spansDirective source s.Range))
    |> List.ofSeq
