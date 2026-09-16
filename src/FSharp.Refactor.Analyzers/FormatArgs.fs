/// Refactoring note (correctness, CA2241): a String.Format placeholder
/// without a matching argument throws FormatException at runtime.
///
///     String.Format("{0} of {1}", x)     // {1} throws when formatting
///
/// The compiler cannot check composite format strings the way it checks
/// sprintf, so the mismatch survives until the line runs. Advice only —
/// whether the fix is another argument or a different placeholder is the
/// author's call (and sprintf/interpolation would make it a compile error).
///
/// Only literal single-format-argument calls are inspected; `{{` escapes
/// are handled, and the culture-first overload is left alone (its format
/// is the second argument).
module FSharp.Refactor.FormatArgs

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// The placeholder index with no argument.
        MissingIndex: int
        /// How many format arguments the call supplies.
        ArgCount: int
    }

let private placeholderRegex = Regex(@"\{(\d+)", RegexOptions.Compiled)

/// Find String.Format calls whose literal format references a missing
/// argument.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree

    [
        for _, expr in index.Exprs do
            match expr with
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                argExpr = SynExpr.Paren(
                    expr = SynExpr.Tuple(exprs = SynExpr.Const(SynConst.String(fmt, _, _), _) :: args))) when
                pathEndsWith "String" "Format" ids && not args.IsEmpty
                ->
                // `{{` is an escaped brace in composite formats
                let cleaned = fmt.Replace("{{", "").Replace("}}", "")

                let indexes =
                    placeholderRegex.Matches cleaned
                    |> Seq.map (fun m -> int m.Groups.[1].Value)
                    |> List.ofSeq

                match indexes with
                | [] -> ()
                | _ ->
                    let maxIndex = List.max indexes

                    if maxIndex >= args.Length then
                        {
                            Range = expr.Range
                            MissingIndex = maxIndex
                            ArgCount = args.Length
                        }
            | _ -> ()
    ]
