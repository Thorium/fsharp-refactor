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
/// && s.Substring(0, 6) = …`, inside `if s.Length >= 6 then`, or in the
/// else branch of a condition whose failure proves it (`if s.Length < 6
/// then … else`; `< 3` proves too little), with no
/// lambda, `let` or match arm rebinding the receiver between, and the
/// receiver an immutable value read through immutable fields (a `let
/// mutable` may be reassigned between the guard and the cut, a getter may
/// answer another string) — and the fix
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
        funcExpr = SynExpr.App(
            isInfix = true; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])); argExpr = l)
        argExpr = r) -> ValueSome(op.idText, l, r)
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SynExpr.Ident op; argExpr = l); argExpr = r) ->
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
    a.Length = b.Length
    && List.forall2 (fun (x: Ident) (y: Ident) -> x.idText = y.idText) a b

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
/// exact. Answers the guard's range, so the caller can look at what runs
/// between the guard and the cut.
let private lengthGuarded (path: SyntaxNode list) (own: range) (receiver: Ident list) (n: int) : range option =
    let isLength (e: SynExpr) =
        match stripParens e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
            not ids.IsEmpty
            && (List.last ids).idText = "Length"
            && sameIdents (List.take (ids.Length - 1) ids) receiver
        | _ -> false

    // the comparison that proves the length, so the caller knows where the
    // proof ends and what runs after it
    let rec guards (e: SynExpr) : range option =
        let proven (holds: bool) = if holds then Some e.Range else None

        match stripParens e with
        | Infix("op_BooleanAnd", l, r) ->
            match guards l with
            | Some g -> Some g
            | None -> guards r
        | Infix("op_GreaterThanOrEqual", len, IntLiteral k) when isLength len -> proven (k >= n)
        | Infix("op_GreaterThan", len, IntLiteral k) when isLength len -> proven (k >= n - 1)
        | Infix("op_Equality", len, IntLiteral k) when isLength len -> proven (k >= n)
        | Infix("op_LessThanOrEqual", IntLiteral k, len) when isLength len -> proven (k >= n)
        | Infix("op_LessThan", IntLiteral k, len) when isLength len -> proven (k >= n - 1)
        | _ -> None

    // a condition that FAILS on a long-enough string: the else branch of
    // `if recv.Length < n then … else <ours>` is guarded too. The else
    // branch knows only the NEGATION: `Length < k` failed proves Length >= k,
    // exact only for k >= n (`if s.Length < 3 then … else s.Substring(0, 6)`
    // still throws on "ORDER", where StartsWith returns false); `Length <=
    // k` failed proves Length >= k + 1
    let rec failsWhenLong (e: SynExpr) : range option =
        let proven (holds: bool) = if holds then Some e.Range else None

        match stripParens e with
        | Infix("op_BooleanOr", l, r) ->
            match failsWhenLong l with
            | Some g -> Some g
            | None -> failsWhenLong r
        | Infix("op_LessThan", len, IntLiteral k) when isLength len -> proven (k >= n)
        | Infix("op_LessThanOrEqual", len, IntLiteral k) when isLength len -> proven (k >= n - 1)
        | Infix("op_GreaterThan", IntLiteral k, len) when isLength len -> proven (k >= n)
        | Infix("op_GreaterThanOrEqual", IntLiteral k, len) when isLength len -> proven (k >= n - 1)
        | _ -> None

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
        | SyntaxNode.SynExpr(LetOrUseE lou) -> lou.Bindings |> List.exists (fun (SynBinding(headPat = p)) -> patBinds p)
        // a loop between the `if` and the cut runs the cut again after a
        // write later in its body, with the guard evaluated once
        | SyntaxNode.SynExpr(SynExpr.Lambda _)
        | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
        | SyntaxNode.SynExpr(SynExpr.ForEach _)
        | SyntaxNode.SynExpr(SynExpr.For _)
        | SyntaxNode.SynExpr(SynExpr.While _)
        | SyntaxNode.SynExpr(SynExpr.WhileBang _)
        | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed _)
        | SyntaxNode.SynExpr(SynExpr.ComputationExpr _)
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
            match
                (if Range.rangeContainsRange r.Range inner then
                     guards l
                 else
                     None)
            with
            | Some g -> Some g
            | None -> chainGuards rest whole.Range
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true)) :: rest -> chainGuards rest inner
        | _ -> None

    // an `if` on the path, with no binder between it and the comparison
    let rec ifGuards (path: SyntaxNode list) =
        match path with
        | [] -> None
        | node :: _ when binds node -> None
        | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenE; elseExpr = elseE)) :: rest ->
            let found =
                if Range.rangeContainsRange thenE.Range own then
                    guards cond
                else
                    match elseE with
                    | Some e when Range.rangeContainsRange e.Range own -> failsWhenLong cond
                    | _ -> None

            // the window opens where the proof ends: the rest of the
            // condition runs after it, and may write the receiver
            match found with
            | Some g -> Some g
            | None -> ifGuards rest
        | _ :: rest -> ifGuards rest

    match chainGuards path own with
    | Some g -> Some g
    | None -> ifGuards path

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

        // the body of this file a symbol names, to read what a call between
        // the guard and the cut visibly does
        let bodiesDeclaredAt (symbol: FSharpSymbol) =
            OptionModule.bodiesBoundAt index parseTree.FileName symbol |> List.map fst

        // `member val X = ... with get` properties of this file, by name and
        // declaring line: a field set once, at construction
        let getOnlyAutoProperties =
            lazy
                (index.Decls
                 |> Array.collect (fun (_, decl) ->
                     match decl with
                     | SynModuleDecl.Types(typeDefns = types) ->
                         [|
                             for SynTypeDefn(typeRepr = repr; members = members) in types do
                                 let inner =
                                     match repr with
                                     | SynTypeDefnRepr.ObjectModel(members = inner) -> inner
                                     | _ -> []

                                 for m in members @ inner do
                                     match m with
                                     | SynMemberDefn.AutoProperty(ident = id; propKind = SynMemberKind.PropertyGet) ->
                                         id.idText, id.idRange.StartLine
                                     | _ -> ()
                         |]
                     | _ -> [||])
                 |> Set.ofArray)

        // the guard read the receiver's Length; the cut reads the receiver
        // again. An immutable value (never a byref, whose target may be
        // written), through immutable fields, get-only `member val`s and the
        // BCL's instance getters, is the same string both times. A `let
        // mutable` is too unless it is written between the guard and the cut:
        // a local one only by a `<-` or a `&` in that stretch (a closure
        // cannot capture it), so `while not (isNull line) do if line.Length
        // >= 6 then ... line.Substring(0, 6)` stays exact; a module or class
        // one by any call in the stretch as well. A computed getter may
        // answer another string each call
        let receiverFixed (path: SyntaxNode list) (receiver: Ident list) (guard: range) (cut: range) =
            let resolve (ids: Ident list) =
                let last = List.last ids
                let r = last.idRange

                OptionModule.symbolUseAt
                    check
                    (r.EndLine, r.EndColumn, source.GetLineString(r.EndLine - 1), ids |> List.map (fun i -> i.idText))
                |> Option.map (fun u -> u.Symbol)

            // the mutable itself: `s` of `M.s` and of `this.s`, whatever path
            // the receiver reaches it by - matched as a symbol, so another
            // `line` of another scope is another value
            let mutableSymbol =
                [ 1 .. receiver.Length ]
                |> List.tryPick (fun n ->
                    match resolve (List.take n receiver) with
                    | Some(:? FSharpMemberOrFunctionOrValue as v) when v.IsMutable -> Some(v :> FSharpSymbol)
                    | _ -> None)

            let root =
                match mutableSymbol with
                | Some v -> v.DisplayName
                | None -> (List.head receiver).idText

            let declaredAt (symbol: FSharpSymbol) =
                try
                    symbol.DeclarationLocation
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    None

            let rootDeclared = mutableSymbol |> Option.bind declaredAt

            // the ident names the receiver's own mutable
            let isRoot (id: Ident) =
                id.idText = root
                && (match rootDeclared with
                    | Some declared ->
                        (match resolve [ id ] with
                         | Some symbol -> declaredAt symbol = Some declared
                         | None -> true)
                    | None -> true)

            let anyRoot (ids: Ident list) = ids |> List.exists isRoot

            // what runs after the guard and before the cut
            let between = Range.mkRange guard.FileName guard.End cut.Start

            let betweenExprs =
                lazy
                    (AstIndex.exprsWithin index between
                     |> Array.filter (fun (_, e) -> Range.rangeContainsRange between e.Range))

            // a byref to the receiver, taken anywhere, writes through
            let byrefStore (id: Ident) =
                match resolve [ id ] with
                | Some(:? FSharpMemberOrFunctionOrValue as v) -> OptionModule.isByRefLike v.FullType
                | _ -> false

            let writtenBetween () =
                betweenExprs.Value
                |> Array.exists (fun (_, e) ->
                    match e with
                    | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = [ id ])) -> isRoot id || byrefStore id
                    | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)) -> anyRoot ids
                    | SynExpr.DotSet(targetExpr = SynExpr.Ident id) -> isRoot id
                    | SynExpr.DotSet(longDotId = SynLongIdent(id = ids)) -> anyRoot ids
                    | SynExpr.Set(targetExpr = target) ->
                        (match stripParens target with
                         | SynExpr.Ident id -> isRoot id || byrefStore id
                         | _ -> false)
                    | SynExpr.AddressOf(expr = SynExpr.Ident id) -> isRoot id
                    | _ -> false)

            // declared inside the binding the cut sits in: a local, which
            // only this code can write; a class or module `let mutable` is
            // any call's to write
            let declaredHere (v: FSharpMemberOrFunctionOrValue) =
                try
                    let declared = v.DeclarationLocation

                    path
                    |> List.exists (fun node ->
                        match node with
                        | SyntaxNode.SynBinding(SynBinding _ as b) ->
                            Range.rangeContainsRange b.RangeOfBindingWithRhs declared
                        | _ -> false)
                with _ -> // no declaration to place: not a local; fsharpanalyzer: ignore-line FR0055
                    false

            // a call between the guard and the cut resets a module or class
            // mutable only when its body, defined in this file, visibly
            // assigns the receiver - itself or through the calls it makes,
            // three deep (`Reset() = Clear()`), a `&` to it included; a call
            // defined elsewhere, an interface call, a constructor is taken as
            // harmless - the fix by default
            let calleeAssignsBetween () =
                let assigns (body: SynExpr) =
                    AstIndex.exprsWithin index body.Range
                    |> Array.exists (fun (_, x) ->
                        Range.rangeContainsRange body.Range x.Range
                        && (match x with
                            | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids))
                            | SynExpr.DotSet(longDotId = SynLongIdent(id = ids)) -> anyRoot ids
                            | SynExpr.Set(targetExpr = target) ->
                                (match stripParens target with
                                 | SynExpr.Ident id -> isRoot id
                                 | _ -> false)
                            | SynExpr.AddressOf(expr = SynExpr.Ident id) -> isRoot id
                            | SynExpr.AddressOf(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
                                anyRoot ids
                            | _ -> false))

                // every function of this file named in a range may run
                // there: applied, piped (`"" |> setS`), composed, handed to
                // `List.iter`
                let mentioned (r: range) =
                    AstIndex.exprsWithin index r
                    |> Array.choose (fun (_, x) ->
                        if Range.rangeContainsRange r x.Range then
                            match x with
                            | SynExpr.Ident id -> Some [ id ]
                            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some ids
                            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                Some [ List.last ids ]
                            | _ -> None
                        else
                            None)

                let visited = System.Collections.Generic.HashSet<string>()

                let rec assignsThrough (depth: int) (ids: Ident list) =
                    match resolve ids with
                    | Some symbol ->
                        bodiesDeclaredAt symbol
                        |> List.exists (fun body ->
                            visited.Add $"{body.Range.StartLine}:{body.Range.StartColumn}"
                            && (assigns body
                                || (depth > 0 && (mentioned body.Range |> Array.exists (assignsThrough (depth - 1))))))
                    | None -> false

                mentioned between |> Array.exists (assignsThrough 2)

            [ 1 .. receiver.Length ]
            |> List.forall (fun n ->
                try
                    match resolve (List.take n receiver) with
                    // a module or namespace on the way: `Config.Name`
                    | Some(:? FSharpEntity as e) -> e.IsFSharpModule || e.IsNamespace
                    | Some(:? FSharpMemberOrFunctionOrValue as v) when
                        n > 1 && (v.IsProperty || v.IsPropertyGetterMethod) && v.IsInstanceMember
                        ->
                        (OptionModule.enclosingFullName v).StartsWith "System."
                        || (not v.HasSetterMethod
                            && getOnlyAutoProperties.Value.Contains((v.DisplayName, v.DeclarationLocation.StartLine)))
                    | Some(:? FSharpMemberOrFunctionOrValue as v) ->
                        not v.IsMember
                        && not (OptionModule.isByRefLike v.FullType)
                        && (not v.IsMutable
                            || (not (writtenBetween ()) && (declaredHere v || not (calleeAssignsBetween ()))))
                    | Some(:? FSharpField as f) when n > 1 -> not f.IsMutable
                    | _ -> false
                with _ -> // an unreadable symbol proves nothing; fsharpanalyzer: ignore-line FR0055
                    false)

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
                                || (match lengthGuarded path expr.Range cut.Receiver cut.Length with
                                    | Some guard -> receiverFixed path cut.Receiver guard expr.Range
                                    | None -> false)
                        }
                    | _ -> ()
                | _ -> ()
        ]
