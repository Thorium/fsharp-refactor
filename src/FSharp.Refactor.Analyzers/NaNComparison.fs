/// Refactoring (correctness, CA2242): equality against NaN never holds.
///
///     x = nan            →  System.Double.IsNaN x     // was always false
///     x <> Double.NaN    →  not (System.Double.IsNaN x)   // was always true
///
/// IEEE 754 defines NaN as unequal to everything including itself, so the
/// original comparison is a latent bug; the fix expresses the test the
/// author meant. The rewrite deliberately changes behavior — from a
/// constant to the intended check.
///
/// Safety rules:
///   - one side is the `nan` operator (typed-gated to FSharp.Core) or a
///     `Double.NaN`/`Single.NaN` path; both-sides-NaN is left alone
///   - the operator is FSharp.Core's `=`/`<>`
module FSharp.Refactor.NaNComparison

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// A NaN constant: (module "Double"/"Single", core-gate ident when the bare
/// `nan` operator was used).
[<return: Struct>]
let private (|NaNValue|_|) (e: SynExpr) =
    match e with
    | SingleIdent id when id.idText = "nan" -> ValueSome("Double", Some id)
    | SingleIdent id when id.idText = "nanf" -> ValueSome("Single", Some id)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        ids.Length >= 2
        && (List.last ids).idText = "NaN"
        && (let owner = ids.[ids.Length - 2].idText
            owner = "Double" || owner = "Single")
        ->
        ValueSome(ids.[ids.Length - 2].idText, None)
    | _ -> ValueNone

/// Find NaN equality comparisons. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                    (op.idText = "op_Equality" || op.idText = "op_Inequality")
                    && isSingleLine expr.Range
                    ->
                    let sides =
                        match stripParens lhs, stripParens rhs with
                        | NaNValue(m, gate), other -> Some(m, gate, other)
                        | other, NaNValue(m, gate) -> Some(m, gate, other)
                        | _ -> None

                    match sides with
                    | Some(moduleName, gateIdent, other) ->
                        let otherIsNaN =
                            match stripParens other with
                            | NaNValue _ -> true
                            | _ -> false

                        let gated =
                            gateIdent |> Option.forall (OptionModule.resolvesToCoreOperator check source)

                        if not otherIsNaN && gated && OptionModule.resolvesToCoreOperator check source op then
                            let test = $"System.{moduleName}.IsNaN {atomicText source (stripParens other)}"

                            let replacement = if op.idText = "op_Equality" then test else $"not ({test})"

                            {
                                Range = expr.Range
                                OriginalText = textOfRange source expr.Range
                                ReplacementText = replacement
                            }
                    | None -> ()
                | _ -> ()
        ]
