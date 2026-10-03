/// FR0177 (correctness, note), twin of the C# rule: two comparisons of one
/// value that together are always true or always false.
///
///     status <> "required" || status <> "optional"    // always true
///     kind = Loan && kind = Invest                    // always false
///     created > limit && created < limit              // always false
///
/// The first two need two DIFFERENT constants - literals, `[<Literal>]`
/// values, enum fields, field-less union cases - against the same plain
/// operand (a name or a property chain). No value equals two different
/// constants at once, so `<>` joined by `||` holds for every value and
/// `=` joined by `&&` for none. The third needs the same
/// operand on both sides of a strict pair (`>` with `<` or `<=`, `>=` with
/// `<`): nothing lies strictly on both sides of one bound.
///
/// The two comparisons are operands of one `||` (or `&&`) chain, with
/// anything between them. The comparison operators must be FSharp.Core's.
///
/// Note-only on a sweep: which operator was meant is not in the code. A
/// chain of exactly the two comparisons gets the editor's offer of the
/// other operator - `&&` for the always-true pair, `||` for the
/// always-false one.
///
/// Cost: a file has thousands of comparisons and a typechecker lookup is a
/// fraction of a millisecond each, so a pair is matched on its text first
/// - same operand, the right operators, the other sides different (or the
/// same) as written - and only a pair that passes asks what its operators
/// and constants resolve to.
module FSharp.Refactor.ConstantComparison

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type Verdict =
    | AlwaysTrue
    | AlwaysFalse

type Suggestion =
    {
        /// From the first comparison to the second.
        Range: range
        First: string
        Second: string
        Verdict: Verdict
        /// The joining operator and its counterpart, when the chain is
        /// exactly the two comparisons.
        OperatorFix: (range * string * string) option
    }

/// One comparison as written: the operand on the left of `Op`, the other
/// side still unresolved. Nothing here has asked the typechecker.
type private Reading =
    {
        Operand: string
        Op: string
        OpIdent: Ident
        Other: SynExpr
        OtherText: string
        Expr: SynExpr
    }

[<return: Struct>]
let private (|Infix|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) ->
        ValueSome(op, lhs, rhs)
    | _ -> ValueNone

let private flipped =
    dict
        [
            "op_Equality", "op_Equality"
            "op_Inequality", "op_Inequality"
            "op_LessThan", "op_GreaterThan"
            "op_GreaterThan", "op_LessThan"
            "op_LessThanOrEqual", "op_GreaterThanOrEqual"
            "op_GreaterThanOrEqual", "op_LessThanOrEqual"
        ]

/// Pairs no value satisfies together against one bound.
let private contradictory =
    set
        [
            "op_GreaterThan", "op_LessThan"
            "op_LessThan", "op_GreaterThan"
            "op_GreaterThan", "op_LessThanOrEqual"
            "op_LessThanOrEqual", "op_GreaterThan"
            "op_GreaterThanOrEqual", "op_LessThan"
            "op_LessThan", "op_GreaterThanOrEqual"
            "op_Equality", "op_Inequality"
            "op_Inequality", "op_Equality"
        ]

let private squeeze (text: string) =
    text |> String.filter (fun c -> not (System.Char.IsWhiteSpace c))

/// A written literal as the value a `[<Literal>]` of it reports, so `One`
/// and `1` are one constant.
let private written (constant: SynConst) : obj voption =
    match constant with
    | SynConst.Bool v -> ValueSome(box v)
    | SynConst.SByte v -> ValueSome(box v)
    | SynConst.Byte v -> ValueSome(box v)
    | SynConst.Int16 v -> ValueSome(box v)
    | SynConst.UInt16 v -> ValueSome(box v)
    | SynConst.Int32 v -> ValueSome(box v)
    | SynConst.UInt32 v -> ValueSome(box v)
    | SynConst.Int64 v -> ValueSome(box v)
    | SynConst.UInt64 v -> ValueSome(box v)
    | SynConst.Single v -> ValueSome(box v)
    | SynConst.Double v -> ValueSome(box v)
    | SynConst.Decimal v -> ValueSome(box v)
    | SynConst.Char v -> ValueSome(box v)
    | SynConst.String(text = text) -> ValueSome(box text)
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // ---- the typechecker: asked only by `confirmed`, below ----

        let symbolOf (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ])
            |> Option.map (fun symbolUse -> symbolUse.Symbol)

        let isCoreOperator (op: Ident) =
            match symbolOf op with
            | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                (try
                    (OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp.Core.Operators"
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false

        // the VALUE of a constant: two spellings of one value are one
        // constant, and no contradiction
        let constantOf (e: SynExpr) =
            let named (ident: Ident) =
                try
                    match symbolOf ident with
                    | Some(:? FSharpUnionCase as case) when case.Fields.Count = 0 -> ValueSome("case " + case.FullName)
                    | Some(:? FSharpField as field) ->
                        match field.LiteralValue with
                        | Some value -> ValueSome $"value {value}"
                        | None -> ValueNone
                    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                        match value.LiteralValue with
                        | Some literal -> ValueSome $"value {literal}"
                        | None -> ValueNone
                    | _ -> ValueNone
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    ValueNone

            match stripParens e with
            | SynExpr.Const(constant, _) ->
                match written constant with
                | ValueSome value -> ValueSome $"value {value}"
                | ValueNone -> ValueNone
            | SynExpr.Ident ident -> named ident
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> named (List.last ids)
            | _ -> ValueNone

        // ---- syntax only ----

        // a name or a property chain
        let plain (e: SynExpr) =
            match stripParens e with
            | SynExpr.Ident _
            | SynExpr.LongIdent _ as operand -> ValueSome(squeeze (textOfRange source operand.Range))
            | _ -> ValueNone

        // a literal: the other side of a comparison whose operand is plain
        let literal (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const(constant, _) -> (written constant).IsSome
            | _ -> false

        // every reading of one comparison: the operand on the left, and for
        // two plain sides the mirror as well (either may be the constant)
        let readings (e: SynExpr) : Reading list =
            match stripParens e with
            | Infix(op, lhs, rhs) as comparison when flipped.ContainsKey op.idText ->
                let reading (operand: string) (opName: string) (other: SynExpr) =
                    {
                        Operand = operand
                        Op = opName
                        OpIdent = op
                        Other = other
                        OtherText = squeeze (textOfRange source (stripParens other).Range)
                        Expr = comparison
                    }

                match plain lhs, plain rhs with
                | ValueSome left, ValueSome right ->
                    [ reading left op.idText rhs; reading right flipped.[op.idText] lhs ]
                | ValueSome left, ValueNone when literal rhs -> [ reading left op.idText rhs ]
                | ValueNone, ValueSome right when literal lhs -> [ reading right flipped.[op.idText] lhs ]
                | _ -> []
            | _ -> []

        let rec operandsOf (opName: string) (e: SynExpr) : SynExpr list =
            match stripParens e with
            | Infix(op, lhs, rhs) when op.idText = opName -> operandsOf opName lhs @ operandsOf opName rhs
            | _ -> [ e ]

        // what two readings would be, were their operators the core ones
        // and their constants different: decided on the text alone. The
        // flag says whether the other sides must resolve to constants
        let candidate (joined: string) (a: Reading) (b: Reading) =
            if a.Operand <> b.Operand then
                ValueNone
            elif
                joined = "op_BooleanOr"
                && a.Op = "op_Inequality"
                && b.Op = "op_Inequality"
                && a.OtherText <> b.OtherText
            then
                ValueSome(Verdict.AlwaysTrue, true)
            elif
                joined = "op_BooleanAnd"
                && a.Op = "op_Equality"
                && b.Op = "op_Equality"
                && a.OtherText <> b.OtherText
            then
                ValueSome(Verdict.AlwaysFalse, true)
            elif
                joined = "op_BooleanAnd"
                && a.OtherText = b.OtherText
                && contradictory.Contains((a.Op, b.Op))
            then
                ValueSome(Verdict.AlwaysFalse, false)
            else
                ValueNone

        // the candidate, confirmed by the typechecker
        let confirmed (constants: bool) (a: Reading) (b: Reading) =
            isCoreOperator a.OpIdent
            && isCoreOperator b.OpIdent
            && (not constants
                || (match constantOf a.Other, constantOf b.Other with
                    | ValueSome x, ValueSome y -> x <> y
                    | _ -> false))

        let seen = System.Collections.Generic.HashSet<struct (range * range)>()

        // the links of a chain already read from its outermost node: the
        // index hands out the outer expression first, and reading every
        // sub-chain again would make a long chain cubic
        let covered = System.Collections.Generic.HashSet<range>()

        let rec cover (opName: string) (e: SynExpr) =
            match stripParens e with
            | Infix(op, lhs, rhs) as link when op.idText = opName ->
                covered.Add link.Range |> ignore
                cover opName lhs
                cover opName rhs
            | _ -> ()

        [
            for _, e in index.Exprs do
                match e with
                | Infix(joiner, lhs, rhs) when
                    (joiner.idText = "op_BooleanOr" || joiner.idText = "op_BooleanAnd")
                    && not (covered.Contains e.Range)
                    && not (spansDirective source e.Range)
                    ->
                    cover joiner.idText lhs
                    cover joiner.idText rhs
                    let operands = operandsOf joiner.idText e |> Array.ofList
                    let read = operands |> Array.map readings

                    for i in 0 .. operands.Length - 2 do
                        if not read.[i].IsEmpty then
                            for j in i + 1 .. operands.Length - 1 do
                                let verdict =
                                    List.allPairs read.[i] read.[j]
                                    |> List.tryPick (fun (a, b) ->
                                        match candidate joiner.idText a b with
                                        | ValueSome(v, constants) when confirmed constants a b ->
                                            Some(v, constants, a, b)
                                        | _ -> None)

                                match verdict with
                                | Some(verdict, swappable, a, b) when seen.Add(struct (a.Expr.Range, b.Expr.Range)) ->
                                    let joinerText = textOfRange source joiner.idRange

                                    {
                                        Range = Range.unionRanges a.Expr.Range b.Expr.Range
                                        First = textOfRange source a.Expr.Range
                                        Second = textOfRange source b.Expr.Range
                                        Verdict = verdict
                                        OperatorFix =
                                            if
                                                swappable
                                                && operands.Length = 2
                                                && (joinerText = "||" || joinerText = "&&")
                                            then
                                                Some(
                                                    joiner.idRange,
                                                    joinerText,
                                                    (if joinerText = "||" then "&&" else "||")
                                                )
                                            else
                                                None
                                    }
                                | _ -> ()
                | _ -> ()
        ]
