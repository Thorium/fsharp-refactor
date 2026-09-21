/// FR0166 (performance): a prefix or suffix of a string, cut out only to
/// be compared with a literal, is a StartsWith/EndsWith that cuts nothing.
///
///     s.Substring(0, 6) = "ORDER-"     →  s.StartsWith("ORDER-", StringComparison.Ordinal)
///     s[..5] = "ORDER-"                →  s.StartsWith("ORDER-", StringComparison.Ordinal)
///     s.Substring(s.Length - 3) = "abc" →  s.EndsWith("abc", StringComparison.Ordinal)
///     s[s.Length - 3 ..] <> "abc"      →  not (s.EndsWith("abc", StringComparison.Ordinal))
///
/// Measured in benchmarks/PerfClaims: 4.5 → 1.9 ns and 40 → 0 B per
/// comparison. F#'s `=` on strings is ordinal, so `StringComparison.Ordinal`
/// is the same comparison spelled out, and a culture-sensitive
/// `StartsWith(string)` is exactly what the rewrite must NOT emit.
///
/// The literal's length must equal the cut's: `s.Substring(0, 3) = "ab"`
/// is a comparison that can never hold, a bug this rule does not touch.
///
/// The SLICE forms are exact under FSharp.Core 5 and later: an F# slice
/// clamps to the string (FS-1077), so a short `s` gives a shorter slice
/// that is not equal, just as StartsWith answers false. A SUBSTRING throws
/// ArgumentOutOfRangeException on a short `s` where StartsWith answers
/// false — and so does a slice under FSharp.Core 4 — so those forms are
/// exact only under a length guard in the same condition — `s.Length >= 6
/// && s.Substring(0, 6) = …`, or inside `if s.Length >= 6 then`, with no
/// lambda, `let` or match arm rebinding the receiver between — and the fix
/// is applied by a sweep only then (`Exact`); without the guard the editor
/// still offers it, for a human who knows the string is long enough, and
/// the CLI notes.
///
/// Guards: the receiver is a name or a dotted path (no call evaluated
/// twice), proven a string; the `Length` of the suffix forms is the SAME
/// receiver's; the literal is a plain string constant (an interpolated or
/// computed right-hand side has no length to check); the compilation is a
/// modern framework (OptionModule.stringIsModern), as the string rules
/// all require; no quotation.
module FSharp.Refactor.PrefixCompare

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole comparison expression the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// "StartsWith" or "EndsWith", for the message.
        Method: string
        /// The rewrite is exact on every input (a slice, or a Substring
        /// under a length guard): a sweep may apply it. Otherwise a short
        /// string would throw before and answer false after, and only the
        /// editor offers the edit.
        Exact: bool
    }

/// `a op b` with the operator's one-segment name: infix operators parse
/// their name as a LongIdent of one ident, not an Ident.
[<return: Struct>]
let private (|Infix|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(isInfix = true; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])); argExpr = l)
        argExpr = r) -> ValueSome(op.idText, l, r)
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SynExpr.Ident op; argExpr = l); argExpr = r) ->
        ValueSome(op.idText, l, r)
    | _ -> ValueNone

[<return: Struct>]
let private (|IntLiteral|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const(SynConst.Int32 n, _) -> ValueSome n
    | _ -> ValueNone

/// A receiver: a name or a dotted path, as its identifiers.
[<return: Struct>]
let private (|Receiver|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Ident id -> ValueSome [ id ]
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = (_ :: _ as ids))) -> ValueSome ids
    | _ -> ValueNone

let private sameIdents (a: Ident list) (b: Ident list) =
    a.Length = b.Length && List.forall2 (fun (x: Ident) (y: Ident) -> x.idText = y.idText) a b

/// `recv.Length - n`: the start of a suffix of length `n`.
[<return: Struct>]
let private (|LengthMinus|_|) (receiver: Ident list) (e: SynExpr) =
    match stripParens e with
    | Infix("op_Subtraction", SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)), IntLiteral n) when
        not ids.IsEmpty
        && (List.last ids).idText = "Length"
        && sameIdents (List.take (ids.Length - 1) ids) receiver
        ->
        ValueSome n
    | _ -> ValueNone

/// What the probe side cuts: a prefix or suffix of `length` characters of
/// `receiver`, by Substring (throws on a short string) or by slice (clamps).
type private Cut =
    {
        Receiver: Ident list
        /// The identifier the receiver's string type is proven through:
        /// the `Substring` itself, or the receiver's last name.
        Proof: Ident
        Method: string
        Length: int
        Slice: bool
    }

let private cutOf (e: SynExpr) =
    match stripParens e with
    // s.Substring(0, n)
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2 && (List.last ids).idText = "Substring"
        ->
        let receiver = List.take (ids.Length - 1) ids
        let proof = List.last ids

        match stripParens arg with
        | SynExpr.Tuple(exprs = [ IntLiteral 0; IntLiteral n ]) when n > 0 ->
            ValueSome
                {
                    Receiver = receiver
                    Proof = proof
                    Method = "StartsWith"
                    Length = n
                    Slice = false
                }
        // s.Substring(s.Length - n)
        | LengthMinus receiver n when n > 0 ->
            ValueSome
                {
                    Receiver = receiver
                    Proof = proof
                    Method = "EndsWith"
                    Length = n
                    Slice = false
                }
        | _ -> ValueNone
    // s[..n], s[0..n], s[s.Length - n ..] — and the dotted spellings
    | SynExpr.App(isInfix = false; funcExpr = Receiver receiver; argExpr = SynExpr.ArrayOrListComputed(expr = range))
    | SynExpr.DotIndexedGet(objectExpr = Receiver receiver; indexArgs = range) ->
        let proof = List.last receiver

        match range with
        | SynExpr.IndexRange(expr1 = None; expr2 = Some(IntLiteral n))
        | SynExpr.IndexRange(expr1 = Some(IntLiteral 0); expr2 = Some(IntLiteral n)) when n >= 0 ->
            ValueSome
                {
                    Receiver = receiver
                    Proof = proof
                    Method = "StartsWith"
                    Length = n + 1
                    Slice = true
                }
        | SynExpr.IndexRange(expr1 = Some(LengthMinus receiver n); expr2 = None) when n > 0 ->
            ValueSome
                {
                    Receiver = receiver
                    Proof = proof
                    Method = "EndsWith"
                    Length = n
                    Slice = true
                }
        | _ -> ValueNone
    | _ -> ValueNone

/// Is the comparison guarded by `recv.Length >= n` (or an equivalent) in
/// the same `&&` chain, or in the condition of an enclosing `if` whose
/// then-branch holds it? Then a Substring cannot throw and the rewrite is
/// exact.
let private lengthGuarded (path: SyntaxNode list) (own: range) (receiver: Ident list) (n: int) =
    let isLength (e: SynExpr) =
        match stripParens e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
            not ids.IsEmpty
            && (List.last ids).idText = "Length"
            && sameIdents (List.take (ids.Length - 1) ids) receiver
        | _ -> false

    let rec guards (e: SynExpr) =
        match stripParens e with
        | Infix("op_BooleanAnd", l, r) -> guards l || guards r
        | Infix("op_GreaterThanOrEqual", len, IntLiteral k) when isLength len -> k >= n
        | Infix("op_GreaterThan", len, IntLiteral k) when isLength len -> k >= n - 1
        | Infix("op_Equality", len, IntLiteral k) when isLength len -> k >= n
        | Infix("op_LessThanOrEqual", IntLiteral k, len) when isLength len -> k >= n
        | Infix("op_LessThan", IntLiteral k, len) when isLength len -> k >= n - 1
        | _ -> false

    // a condition that FAILS on a long-enough string: the else branch of
    // `if recv.Length < n then … else <ours>` is guarded too
    let rec failsWhenLong (e: SynExpr) =
        match stripParens e with
        | Infix("op_BooleanOr", l, r) -> failsWhenLong l || failsWhenLong r
        | Infix("op_LessThan", len, IntLiteral k) when isLength len -> k <= n
        | Infix("op_LessThanOrEqual", len, IntLiteral k) when isLength len -> k <= n - 1
        | Infix("op_GreaterThan", IntLiteral k, len) when isLength len -> k <= n
        | Infix("op_GreaterThanOrEqual", IntLiteral k, len) when isLength len -> k <= n - 1
        | _ -> false

    // a node that binds names: below it the receiver may be ANOTHER value
    // of the same name (`if s.Length >= 6 then xs |> List.map (fun s ->
    // s.Substring(0, 6) = …)`), and the guard above says nothing about it
    let root = (List.head receiver).idText

    let rec patBinds (p: SynPat) =
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = root
        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) -> id.idText = root
        | SynPat.Typed(pat = inner)
        | SynPat.Attrib(pat = inner)
        | SynPat.Paren(inner, _) -> patBinds inner
        | SynPat.Tuple(elementPats = ps)
        | SynPat.ArrayOrList(elementPats = ps)
        | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> ps |> List.exists patBinds
        | SynPat.As(lhsPat = l; rhsPat = r)
        | SynPat.Or(lhsPat = l; rhsPat = r) -> patBinds l || patBinds r
        | SynPat.Record(fieldPats = fs) -> fs |> List.exists (fun (NamePatPairField(pat = p)) -> patBinds p)
        | _ -> false

    let binds (node: SyntaxNode) =
        match node with
        // a `let` between the `if` and the comparison rebinds the receiver
        // only when one of its bindings names it
        | SyntaxNode.SynExpr(LetOrUseE lou) ->
            lou.Bindings |> List.exists (fun (SynBinding(headPat = p)) -> patBinds p)
        | SyntaxNode.SynExpr(SynExpr.Lambda _)
        | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
        | SyntaxNode.SynExpr(SynExpr.ForEach _)
        | SyntaxNode.SynExpr(SynExpr.For _)
        | SyntaxNode.SynExpr(SynExpr.ObjExpr _)
        | SyntaxNode.SynMatchClause _
        | SyntaxNode.SynBinding _
        | SyntaxNode.SynMemberDefn _ -> true
        | _ -> false

    // the `&&` chain: every operand to the LEFT of ours is evaluated first.
    // The path is nearest-first; a left operand sits under the inner
    // infix App, which is stepped over
    let rec chainGuards (path: SyntaxNode list) (inner: range) =
        match path with
        | SyntaxNode.SynExpr(SynExpr.Paren _ as p) :: rest -> chainGuards rest p.Range
        | SyntaxNode.SynExpr(Infix("op_BooleanAnd", l, r) as whole) :: rest ->
            (Range.rangeContainsRange r.Range inner && guards l) || chainGuards rest whole.Range
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true)) :: rest -> chainGuards rest inner
        | _ -> false

    // an `if` on the path, with no binder between it and the comparison
    let rec ifGuards (path: SyntaxNode list) =
        match path with
        | [] -> false
        | node :: _ when binds node -> false
        | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenE; elseExpr = elseE)) :: rest ->
            (Range.rangeContainsRange thenE.Range own && guards cond)
            || (match elseE with
                | Some e -> Range.rangeContainsRange e.Range own && failsWhenLong cond
                | None -> false)
            || ifGuards rest
        | _ :: rest -> ifGuards rest

    chainGuards path own || ifGuards path

/// `tolerantSlicing`: the project's FSharp.Core clamps an out-of-range slice
/// (5.0 and later, FS-1077); under an older one a slice THROWS like a
/// Substring and needs the same length guard to be exact.
let find
    (tolerantSlicing: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the receiver is a string, on a modern framework: through the
        // Substring (String's own) or through the receiver's type
        let provenString (cut: Cut) =
            let entity =
                match OptionModule.symbolOfIdent check source cut.Proof with
                | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                    if cut.Slice then
                        OptionModule.stringEntityOf value
                    else
                        (try
                            value.ApparentEnclosingEntity
                            |> Option.filter (fun e -> e.TryFullName = Some "System.String")
                         with OptionModule.FcsSymbolFailure ->
                             None)
                // a record field's receiver (`d.Name[..2]`) is an FSharpField
                | Some(:? FSharpField as field) when cut.Slice -> OptionModule.stringEntityOfType field.FieldType
                | _ -> None

            match entity with
            | Some e -> OptionModule.stringIsModern e
            | None -> false

        let prefix = if opensSystemNamespace source then "" else "System."

        [
            for path, expr in index.Exprs do
                match expr with
                | Infix(("op_Equality" | "op_Inequality") as op, l, r) when
                    isSingleLine expr.Range && not (insideQuotedCode path)
                    ->
                    let literalAndCut =
                        match stripParens l, stripParens r with
                        | SynExpr.Const(SynConst.String(text, _, _), _) as lit, probe
                        | probe, (SynExpr.Const(SynConst.String(text, _, _), _) as lit) ->
                            match cutOf probe with
                            | ValueSome cut when cut.Length = text.Length -> Some(lit, cut)
                            | _ -> None
                        | _ -> None

                    match literalAndCut with
                    | Some(lit, cut) when provenString cut ->
                        let call =
                            $"{identText cut.Receiver}.{cut.Method}({textOfRange source lit.Range}, {prefix}StringComparison.Ordinal)"

                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = if op = "op_Equality" then call else $"not ({call})"
                            Method = cut.Method
                            Exact =
                                (cut.Slice && tolerantSlicing)
                                || lengthGuarded path expr.Range cut.Receiver cut.Length
                        }
                    | _ -> ()
                | _ -> ()
        ]
