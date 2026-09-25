/// FR0159 (correctness): a floating-point conversion applied to an INTEGER
/// division — the quotient is truncated before it is widened, and the
/// fraction the conversion was there to keep is already gone.
///
///     float (sum / count)         →  float sum / float count
///     double (done / total)       →  double done / double total
///     decimal (hits / requests)   →  decimal hits / decimal requests
///
/// C# has the twin (`double avg = sum / count`) through an implicit
/// widening; F# has no implicit conversion, so the shape is the explicit
/// one, a conversion function whose argument is a division of integers. The
/// typed check settles the operands: the `/` is FSharp.Core's, instantiated
/// at an integer type (int, int64, the unsigned and small ones), so a
/// float or decimal division inside a conversion stays quiet, as does
/// anything the typechecker cannot read.
///
/// Truncation can be the intent — `float (ms / 1000)` for whole seconds —
/// and a LITERAL operand is where that reading is likelier, so a division
/// with a literal on either side is the editor's (a sweep passes it by unless
/// `{ "FR0159": { "all": true } }` asks for the notes);
/// two named operands (`sum / count`) is the average that lost its
/// fraction, and the sweep applies the fix.
module FSharp.Refactor.IntDivisionToFloat

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole conversion application, `float (a / b)`.
        Range: range
        OriginalText: string
        /// `float a / float b`.
        ReplacementText: string
        /// The conversion's name: float, double, decimal, float32, single.
        Conversion: string
        /// The truncation may well be meant: an operand is a literal (`ms /
        /// 1000`, `screenW / 2`), or the dividend is a product (`x * mw / tw`,
        /// a coordinate scaled by a ratio, a percentage) — so a sweep passes
        /// it by unless asked, and only the editor offers the rewrite.
        LikelyMeant: bool
    }

/// The conversions that widen an integer into a fractional type.
let private conversions = set [ "float"; "double"; "float32"; "single"; "decimal" ]

let private integerTypes =
    set
        [
            "System.Int32"
            "System.Int64"
            "System.Int16"
            "System.SByte"
            "System.Byte"
            "System.UInt16"
            "System.UInt32"
            "System.UInt64"
            "System.IntPtr"
            "System.UIntPtr"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // FSharp.Core's `/` instantiated at an integer type
        let integerDivision (op: Ident) =
            let r = op.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ op.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        (OptionModule.fullNameOf mfv).StartsWith "Microsoft.FSharp.Core.Operators"
                        && (match symbolUse.GenericArguments with
                            | [] -> false
                            | inst ->
                                inst
                                |> List.forall (fun (_, t) ->
                                    let t = OptionModule.stripAbbreviations t

                                    t.HasTypeDefinition
                                    && (t.TypeDefinition.TryFullName
                                        |> Option.map integerTypes.Contains
                                        |> Option.defaultValue false)))
                     with _ -> // an unreadable operator is not known to be integer; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false

        // the conversion function is FSharp.Core's own, not a shadowing one
        // (`float` and `decimal` live in Operators, `double` and `single` in
        // ExtraTopLevelOperators)
        let coreConversion (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        let full = OptionModule.fullNameOf mfv

                        full.StartsWith "Microsoft.FSharp.Core.Operators"
                        || full.StartsWith "Microsoft.FSharp.Core.ExtraTopLevelOperators"
                     with _ -> // fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false

        let isLiteral (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const _ -> true
            | _ -> false

        // `a * b / c`: a value scaled by a ratio, whole by intent as often
        // as not (FsLemming's minimap maps every coordinate this way)
        let isProduct (e: SynExpr) =
            match stripParens e with
            | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) ->
                op.idText = "op_Multiply"
            | _ -> false

        // an operand under its own conversion: atomic stays bare, anything
        // else keeps parentheses — a negative literal included, since
        // `float -2` is a subtraction
        let converted (conversion: string) (e: SynExpr) =
            let text = textOfRange source e.Range

            match e with
            | SynExpr.Const _ when text.StartsWith '-' -> $"{conversion} ({text})"
            | SynExpr.Ident _
            | SynExpr.LongIdent _
            | SynExpr.Const _ -> $"{conversion} {text}"
            | SynExpr.Paren _ -> $"{conversion} {text}"
            | _ -> $"{conversion} ({text})"

        // the rewrite turns one application into a division: as an operand
        // of a tighter operator (`float (a / b) ** 2.0`) or an argument it
        // needs its own parentheses to bind as the original did
        let needsParens (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.App _) :: _
            | SyntaxNode.SynExpr(SynExpr.DotGet _) :: _
            | SyntaxNode.SynExpr(SynExpr.DotIndexedGet _) :: _
            | SyntaxNode.SynExpr(SynExpr.Tuple _) :: _ -> true
            | _ -> false

        // the whole-number quotient is the point under a rounding function
        // — `floor (float (a / b))`, `Math.Truncate` — and after a division
        // by the literal 1, which divides nothing
        let roundings =
            set
                [
                    "floor"
                    "ceil"
                    "round"
                    "truncate"
                    "Floor"
                    "Ceiling"
                    "Round"
                    "Truncate"
                ]

        let underRounding (path: SyntaxNode list) =
            let rec argumentOf (nodes: SyntaxNode list) =
                match nodes with
                | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest -> argumentOf rest
                | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f)) :: _ ->
                    (match f with
                     | SynExpr.Ident id -> roundings.Contains id.idText
                     | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                         roundings.Contains (List.last ids).idText
                     | _ -> false)
                | _ -> false

            argumentOf path

        let isOne (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const(SynConst.Int32 1, _)
            | SynExpr.Const(SynConst.Int64 1L, _) -> true
            | _ -> false

        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SingleIdent conversion
                    argExpr = SynExpr.Paren(
                        expr = SynExpr.App(
                            funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs)
                            argExpr = rhs))) when
                    conversions.Contains conversion.idText
                    && op.idText = "op_Division"
                    && not (isOne rhs)
                    && not (underRounding path)
                    && integerDivision op
                    && coreConversion conversion
                    ->
                    let c = conversion.idText
                    let division = $"{converted c lhs} / {converted c rhs}"

                    {
                        Range = expr.Range
                        OriginalText = textOfRange source expr.Range
                        ReplacementText = if needsParens path then $"({division})" else division
                        Conversion = c
                        LikelyMeant = isLiteral lhs || isLiteral rhs || isProduct lhs
                    }
                | _ -> ()
        ]
