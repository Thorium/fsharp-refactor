/// FR0129 (fix): a when-guard that only equality-tests the clause's own
/// binder against a literal IS the literal pattern:
///
///     | x when x = "A" -> 1            | "A" -> 1
///     | x when x = "B" -> 2      →     | "B" -> 2
///     | x -> 3                         | x -> 3
///
/// Per clause, gated on:
///   - the pattern is a bare binder, the guard EXACTLY `binder = literal`
///     (either side), the literal a constant the pattern language can
///     spell (string/char/int/bool/float...)
///   - the clause body never mentions the binder — after the rewrite it
///     no longer exists
/// Works on match, match! and `function` alike.
module FSharp.Refactor.MatchGuards

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// `x when x = "A"` — replaced by the literal's own text.
        Range: range
        LiteralText: string
        BinderName: string
    }

let private opName (e: SynExpr) =
    match e with
    | SynExpr.Ident op -> Some op.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])) -> Some op.idText
    | _ -> None

/// A constant a PATTERN can spell verbatim.
let private isPatternConst (e: SynExpr) =
    match e with
    | SynExpr.Const(c, _) ->
        match c with
        | SynConst.Unit
        | SynConst.Measure _
        | SynConst.UserNum _
        | SynConst.SourceIdentifier _
        // legal in expressions but NOT in the pattern language
        | SynConst.Decimal _
        | SynConst.IntPtr _
        | SynConst.UIntPtr _ -> false
        | _ -> true
    | _ -> false

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [
        for _, e in index.Exprs do
            let clauses =
                match e with
                | SynExpr.Match(clauses = cs)
                | SynExpr.MatchBang(clauses = cs)
                | SynExpr.MatchLambda(matchClauses = cs) -> cs
                | _ -> []

            for SynMatchClause(pat = p; whenExpr = w; resultExpr = body) in clauses do
                match p, w with
                | SynPat.Named(ident = SynIdent(ident = binder)), Some guard ->
                    // the guard must be EXACTLY `binder = literal`
                    let literal =
                        match stripParens guard with
                        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = opE; argExpr = lhs); argExpr = rhs) when
                            opName opE = Some "op_Equality"
                            ->
                            match stripParens lhs, stripParens rhs with
                            | SynExpr.Ident l, lit when l.idText = binder.idText && isPatternConst lit -> Some lit
                            | lit, SynExpr.Ident r when r.idText = binder.idText && isPatternConst lit -> Some lit
                            | _ -> None
                        | _ -> None

                    match literal with
                    | Some lit when
                        // the binder must not survive into the body — after
                        // the rewrite it no longer exists
                        not (Regex.IsMatch(textOfRange source body.Range, identifierPattern binder.idText))
                        ->
                        {
                            Range = Range.mkRange p.Range.FileName p.Range.Start guard.Range.End
                            LiteralText = textOfRange source lit.Range
                            BinderName = binder.idText
                        }
                    | _ -> ()
                | _ -> ()
    ]
