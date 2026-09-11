/// Diagnostic (correctness): arithmetic that wraps silently on overflow.
///
///     let due = balance + 2_000_000_000       // int + int wraps SILENTLY
///     let micros = seconds * 1_000_000        // int32 is gone past 2147 s
///     let next = System.Int32.MaxValue + n    // every n but zero
///
/// F# arithmetic is unchecked by default: an int overflow does not throw,
/// it wraps, and the corrupted value flows on — this very repository's
/// benchmark harness summed an array with `Array.sum` (wrapped, silently
/// wrong) and LINQ's checked `Sum` (threw) side by side before this rule
/// existed. Three shapes make overflow a plausibility, not a theory:
///   - a constant within a factor of two of the type's ceiling
///   - a multiplication by a million or more: the time-unit conversions
///     (seconds to microseconds, milliseconds to ticks) that leave int32
///     within seconds of wall-clock time
///   - `Int32.MaxValue + e` and `MinValue - e`, which overflow for every e
///     but zero (`MaxValue - e` is the sentinel arithmetic Random.fs does
///     on purpose and stays quiet)
///
/// The editor offers two fixes, in this order:
///   1. widen the WHOLE arithmetic expression: every operand cast to int64
///      first, every literal spelled with L, the arithmetic run wide, and
///      `Checked.int` narrowing the result back to its original type —
///      `(1000000 * 1000000 + 5) / 100000` becomes
///      `Checked.int ((1000000L * 1000000L + 5L) / 100000L)`. The value
///      keeps its meaning, which is what the author wanted; delete the
///      narrowing to keep it int64
///   2. `Checked.( * ) seconds 1_000_000` — still fails, just loudly: an
///      OverflowException instead of a wrong number
/// A sweep only notes: the wraparound may be intended, and saying so
/// beats implying it.
///
/// Guards: only decimal-spelled literals count — a hex constant
/// (0x7FFFFFFF) is a mask, not a magnitude; unsigned literals are skipped
/// (wraparound arithmetic on those is routinely deliberate); and a file
/// that already opens Checked operators has made its choice.
module FSharp.Refactor.CheckedArithmetic

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type OverflowKind =
    /// A literal within a factor of two of the ceiling.
    | NearLimit
    /// A multiplication by a million or more: a unit conversion.
    | ScaleFactor
    /// `Int32.MaxValue + e` / `MinValue - e`.
    | LimitConstant

type Suggestion =
    {
        Range: range
        Kind: OverflowKind
        /// The constant's source text, for the message.
        ConstantText: string
        /// The editor's first offer: the expression widened to int64,
        /// (range, original, replacement). None when an operand is not a
        /// plain expression the rewrite can wrap.
        WidenFix: (range * string * string) option
        /// The editor's second offer: the same operation through
        /// `Checked.( op )`, throwing instead of wrapping.
        CheckedFix: (range * string * string) option
    }

/// int32 within a factor of two of the ceiling; int64 within a factor of
/// sixteen (ten-digit int64s are common as ids, eighteen-digit ones are
/// magnitudes).
let private nearLimit (c: SynConst) =
    match c with
    | SynConst.Int32 n -> n >= 1_073_741_824 || n <= -1_073_741_824
    | SynConst.Int64 n -> n >= 576_460_752_303_423_488L || n <= -576_460_752_303_423_488L
    | _ -> false

/// A multiplier of a million or more: int32 overflows once the other
/// operand passes 2147 — seconds, milliseconds, pixels, rows.
let private scaleFactor (c: SynConst) =
    match c with
    | SynConst.Int32 n -> n >= 1_000_000 || n <= -1_000_000
    | _ -> false

let private overflowOps = set [ "op_Addition"; "op_Multiply"; "op_Subtraction" ]

let private symbolOf (op: string) =
    match op with
    | "op_Addition" -> "+"
    | "op_Multiply" -> "*"
    | "op_Division" -> "/"
    | "op_Modulus" -> "%"
    | _ -> "-"

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // a file that already chose checked operators needs no reminder
    let opensChecked =
        index.Decls
        |> Array.exists (fun (_, decl) ->
            match decl with
            | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                ids |> List.exists (fun id -> id.idText = "Checked")
            | _ -> false)

    if opensChecked then
        []
    else
        // decimal spellings only: hex is a mask, not a magnitude
        let decimalLiteral (e: SynExpr) (qualifies: SynConst -> bool) =
            match stripParens e with
            | SynExpr.Const(constant = c) as constant when qualifies c ->
                let text = textOfRange source constant.Range

                if text.StartsWith "0x" || text.StartsWith "0X" then
                    ValueNone
                else
                    ValueSome text
            | _ -> ValueNone

        // `Int32.MaxValue + e` / `* e` and `Int32.MinValue - e` overflow for
        // every e but zero; the other directions (`MaxValue - e`) are the
        // sentinel arithmetic Random.fs and friends do on purpose
        let limitConstant (op: string) (side: SynExpr) (isLeft: bool) =
            match stripParens side with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) as e when ids.Length >= 2 ->
                let typeName = ids.[ids.Length - 2].idText
                let member' = (List.last ids).idText

                let integral =
                    typeName = "Int32"
                    || typeName = "Int64"
                    || typeName = "Int16"
                    || typeName = "SByte"

                let overflows =
                    (member' = "MaxValue" && (op = "op_Addition" || op = "op_Multiply"))
                    || (member' = "MinValue" && op = "op_Subtraction" && isLeft)

                if integral && overflows then
                    ValueSome(textOfRange source e.Range)
                else
                    ValueNone
            | _ -> ValueNone

        // an operand as a function argument: atomic stays bare, anything
        // else gets parentheses
        let asArgument (e: SynExpr) =
            let text = textOfRange source e.Range

            match e with
            | SynExpr.Ident _
            | SynExpr.LongIdent _
            | SynExpr.Const _
            | SynExpr.Paren _ -> text
            | _ -> $"({text})"

        [ for path, expr in index.Exprs do
              match expr with
              | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                  overflowOps.Contains op.idText
                  ->
                  let literalSide qualifies =
                      match decimalLiteral lhs qualifies, decimalLiteral rhs qualifies with
                      | ValueSome text, _ -> ValueSome(text, true)
                      | _, ValueSome text -> ValueSome(text, false)
                      | _ -> ValueNone

                  let found =
                      match literalSide nearLimit with
                      | ValueSome(text, literalOnLeft) -> ValueSome(OverflowKind.NearLimit, text, Some literalOnLeft)
                      | ValueNone ->
                          match
                              (if op.idText = "op_Multiply" then
                                   literalSide scaleFactor
                               else
                                   ValueNone)
                          with
                          | ValueSome(text, literalOnLeft) ->
                              ValueSome(OverflowKind.ScaleFactor, text, Some literalOnLeft)
                          | ValueNone ->
                              match limitConstant op.idText lhs true, limitConstant op.idText rhs false with
                              | ValueSome text, _
                              | _, ValueSome text -> ValueSome(OverflowKind.LimitConstant, text, None)
                              | _ -> ValueNone

                  match found with
                  | ValueSome(kind, text, literalOnLeft) ->
                      let original = textOfRange source expr.Range
                      let symbol = symbolOf op.idText

                      // the widening rewrites the WHOLE arithmetic expression
                      // this operation sits in — every int operand cast to
                      // int64 first, every int32 literal spelled with L, the
                      // arithmetic run wide, and Checked.int narrowing the
                      // result back to the original type at the end:
                      //     (1000000 * 1000000 + 5) / 100000
                      //  →  Checked.int ((1000000L * 1000000L + 5L) / 100000L)
                      let arithmetic =
                          set [ "op_Addition"; "op_Subtraction"; "op_Multiply"; "op_Division"; "op_Modulus" ]

                      let isArithmetic (e: SynExpr) =
                          match e with
                          | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent o)) ->
                              arithmetic.Contains o.idText
                          | SynExpr.App(isInfix = true; funcExpr = SingleIdent o) -> arithmetic.Contains o.idText
                          | _ -> false

                      // climbed from the operation outward, innermost parent
                      // first: an enclosing arithmetic application, or a
                      // paren whose OWN parent is one. A paren that is a
                      // function argument (`int64 (seconds * 1_000_000)`), a
                      // method argument (`Math.Max(seconds * 1_000_000, 0)`)
                      // or a comparison operand is where the arithmetic ends
                      // — widening past it fed `int64` a tuple, or narrowed
                      // back a value the author had just widened. Yields the
                      // outermost node and the path above it
                      let rec climb (acc: SynExpr) (above: SyntaxNode list) =
                          match above with
                          | SyntaxNode.SynExpr(SynExpr.Paren _ as p) :: (SyntaxNode.SynExpr parent :: _ as rest) when
                              isArithmetic parent && Range.rangeContainsRange p.Range acc.Range
                              ->
                              climb p rest
                          | SyntaxNode.SynExpr a :: rest when
                              isArithmetic a && Range.rangeContainsRange a.Range acc.Range
                              ->
                              climb a rest
                          | _ -> acc, above

                      let outermost, above = climb expr path

                      // the widened expression must be a WHOLE value — the
                      // right-hand side of a binding, a `return`, an
                      // assignment — so that `Checked.int (...)` replaces
                      // exactly what the original computed. An operand of a
                      // comparison, a call argument, a branch of an `if`:
                      // there the narrowing has no place of its own, and the
                      // widening is withheld (the Checked offer still stands)
                      let wholeValue =
                          let rec unwrap (nodes: SyntaxNode list) =
                              match nodes with
                              | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest
                              | SyntaxNode.SynExpr(SynExpr.Typed _) :: rest -> unwrap rest
                              | _ -> nodes

                          let holds (value: SynExpr) =
                              Range.rangeContainsRange value.Range outermost.Range

                          match unwrap above with
                          | SyntaxNode.SynBinding(SynBinding(expr = body)) :: _ -> holds body
                          | SyntaxNode.SynExpr(SynExpr.YieldOrReturn(expr = value)) :: _ -> holds value
                          | SyntaxNode.SynExpr(SynExpr.Set(rhsExpr = value)) :: _ -> holds value
                          | SyntaxNode.SynExpr(SynExpr.LongIdentSet(expr = value)) :: _ -> holds value
                          | SyntaxNode.SynExpr(SynExpr.DotSet(rhsExpr = value)) :: _ -> holds value
                          | SyntaxNode.SynExpr(SynExpr.DotIndexedSet(valueExpr = value)) :: _ -> holds value
                          | _ -> false

                      let rec wide (e: SynExpr) : string option =
                          match e with
                          | SynExpr.Paren(expr = inner) -> wide inner |> Option.map (fun t -> $"({t})")
                          | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent o; argExpr = l); argExpr = r) when
                              arithmetic.Contains o.idText
                              ->
                              let symbol = symbolOf o.idText

                              match wide l, wide r with
                              | Some a, Some b -> Some $"{a} {symbol} {b}"
                              | _ -> None
                          | SynExpr.Const(SynConst.Int32 _, _) ->
                              let t = textOfRange source e.Range

                              if t.StartsWith "0x" || t.StartsWith "0X" then
                                  None
                              else
                                  Some(t + "L")
                          | SynExpr.Const(SynConst.Int64 _, _) -> Some(textOfRange source e.Range)
                          | SynExpr.Const _ -> None
                          | other -> Some $"int64 {asArgument other}"

                      let widen =
                          match literalOnLeft with
                          // an int32 literal only: an int64 expression has
                          // nowhere wider to go, and narrowing it back to int
                          // would be the wrong type
                          | Some _ when wholeValue && not (text.EndsWith 'L' || text.EndsWith 'l') ->
                              // the chain must widen as a whole: a float or
                              // decimal operand anywhere means it is not int
                              // arithmetic. A prefix call with parentheses:
                              // `|> Checked.int` shares its precedence with
                              // `<`, `=` and `::`, and would have taken a
                              // comparison to its left along
                              wide outermost
                              |> Option.map (fun t ->
                                  outermost.Range, textOfRange source outermost.Range, $"Checked.int ({t})")
                          | _ -> None

                      let checkedFix =
                          match literalOnLeft with
                          | Some _ ->
                              let spelled = if symbol = "*" then "( * )" else $"({symbol})"
                              Some(expr.Range, original, $"Checked.{spelled} {asArgument lhs} {asArgument rhs}")
                          | None -> None

                      { Range = expr.Range
                        Kind = kind
                        ConstantText = text
                        WidenFix = widen
                        CheckedFix = checkedFix }
                  | ValueNone -> ()
              | _ -> () ]
