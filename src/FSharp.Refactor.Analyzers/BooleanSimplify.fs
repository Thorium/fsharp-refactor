/// Two boolean simplifications:
///
/// 1. Identity elements (FR0108, fix): `x && true`, `true && x`,
///    `x || false`, `false || x` — the literal contributes nothing, the
///    expression IS the other operand. `x && false` and `true || x` are
///    deliberately left alone: their VALUE is constant but `x`'s
///    evaluation (and its effects) still happens or is skipped, so the
///    honest rewrite would need to reason about purity for no gain.
///
/// 2. Idempotent duplicates (FR0109, fix): `a || a` → `a`, `a && a` → `a`
///    — only when the operands are textually identical AND visibly
///    effect-free: short-circuiting means `a || a` evaluates `a` twice on
///    the false path, so a side-effecting `a` collapsed to one evaluation
///    would change behavior. The message also nudges toward the likelier
///    truth: a duplicated operand is usually a copy-paste that meant to
///    name something else.
///
/// Both run inside `query { }` and quotations deliberately: removing a
/// node leaves a strictly simpler tree of shapes the translator already
/// accepted — nothing new to fail on.
module FSharp.Refactor.BooleanSimplify

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Kind =
    /// `x && true` and friends: drop the literal.
    | Identity
    /// `a || a`: drop the duplicate.
    | Duplicate

type Suggestion =
    {
        Range: range
        Kind: Kind
        OriginalText: string
        ReplacementText: string
    }

let private isBoolOp (op: Ident) =
    op.idText = "op_BooleanAnd" || op.idText = "op_BooleanOr"

[<return: Struct>]
let private (|BoolConst|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const(SynConst.Bool b, _) -> ValueSome b
    | _ -> ValueNone

/// The head of an application chain: `a > b` leads to `op_GreaterThan`,
/// `f x y` to `f`.
[<TailCall>]
let rec private appHead (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = f) -> appHead f
    | SynExpr.Paren(expr = inner) -> appHead inner
    | other -> other

/// Known-pure prelude functions a comparison operand may apply.
let private pureCallees = set [ "not"; "isNull" ]

/// May the operand be evaluated FEWER times than written? Collapsing
/// `a || a` drops the second evaluation on the false path, so beyond the
/// statement-shaped constructs FR0107's scan rejects, any actual CALL
/// disqualifies too — `tryConnect() || tryConnect()` is the deliberate
/// retry idiom, and `f x || f x` may lean on f's effects. Operators
/// (`op_*`) and a tiny pure allowlist are the only applications left:
/// property chains, indexing and comparisons pass, calls do not.
let private duplicateSafe (index: AstIndex.Index) (r: range) =
    AstIndex.exprsWithin index r
    |> Array.forall (fun (_, e) ->
        not (Range.rangeContainsRange r e.Range)
        || (match e with
            | SynExpr.Set _
            | SynExpr.LongIdentSet _
            | SynExpr.DotSet _
            | SynExpr.DotIndexedSet _
            | SynExpr.NamedIndexedPropertySet _
            | SynExpr.DotNamedIndexedPropertySet _
            | SynExpr.Sequential _
            | SynExpr.Do _
            | SynExpr.DoBang _
            | SynExpr.While _
            | SynExpr.For _
            | SynExpr.ForEach _
            | SynExpr.TryWith _
            | SynExpr.TryFinally _
            | SynExpr.LetOrUse _
            | SynExpr.New _ -> false
            | SynExpr.App _ as app ->
                (match appHead app with
                 | SingleIdent id -> id.idText.StartsWith "op_" || pureCallees.Contains id.idText
                 | _ -> false)
            | _ -> true))

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // a context that pins the expression to bool by itself: the literal is
    // then redundant wherever the other operand came from
    let pinsBool (path: SyntaxNode list) =
        match path with
        | SyntaxNode.SynExpr(SynExpr.IfThenElse _) :: _
        | SyntaxNode.SynExpr(SynExpr.While _) :: _
        | SyntaxNode.SynExpr(SynExpr.Assert _) :: _
        | SyntaxNode.SynMatchClause _ :: _ -> true
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent parentOp))) :: _ ->
            isBoolOp parentOp
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SingleIdent parentOp)) :: _ ->
            isBoolOp parentOp || parentOp.idText = "not"
        | _ -> false

    // a CALL as the kept operand may owe its bool type to the literal
    // beside it: FSharpPlus's `let _111 = parse "true" && true`, where
    // `parse` is an SRTP function whose return type the `&& true` pins -
    // dropped, the binding no longer typechecks. Outside a bool-pinning
    // context such an operand keeps its literal
    let anchoredByLiteral (path: SyntaxNode list) (kept: SynExpr) =
        (match appHead (stripParens kept) with
         | SingleIdent id -> not (id.idText.StartsWith "op_" || pureCallees.Contains id.idText)
         | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
             not (ids.IsEmpty || (List.last ids).idText.StartsWith "op_")
         | _ -> false)
        && (match stripParens kept with
            | SynExpr.App _ -> true
            | _ -> false)
        && not (pinsBool path)

    [
        for path, expr in index.Exprs do
            match expr with
            | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                isBoolOp op && isSingleLine expr.Range && not (spansDirective source expr.Range)
                ->
                let isAnd = op.idText = "op_BooleanAnd"

                let keep (kept: SynExpr) kind =
                    {
                        Range = expr.Range
                        Kind = kind
                        OriginalText = textOfRange source expr.Range
                        ReplacementText = separated source expr.Range (textOfRange source kept.Range)
                    }

                match lhs, rhs with
                // the literal operand contributes nothing - unless the other
                // operand is a call that owes it its type
                | BoolConst true, kept when isAnd && anchoredByLiteral path kept -> ()
                | kept, BoolConst true when isAnd && anchoredByLiteral path kept -> ()
                | BoolConst false, kept when not isAnd && anchoredByLiteral path kept -> ()
                | kept, BoolConst false when not isAnd && anchoredByLiteral path kept -> ()
                | BoolConst true, _ when isAnd -> keep rhs Identity
                | _, BoolConst true when isAnd -> keep lhs Identity
                | BoolConst false, _ when not isAnd -> keep rhs Identity
                | _, BoolConst false when not isAnd -> keep lhs Identity
                // `a || a` / `a && a` — identical, effect-free operands only
                | _ ->
                    if
                        textOfRange source lhs.Range = textOfRange source rhs.Range
                        && duplicateSafe index lhs.Range
                    then
                        keep lhs Duplicate
            | _ -> ()
    ]
