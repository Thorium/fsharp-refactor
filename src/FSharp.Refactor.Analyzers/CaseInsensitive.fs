/// Refactoring note (performance, CA1862): comparing via ToLower/ToUpper
/// allocates a lowered copy of the string just to throw it away.
///
///     a.ToLower() = b.ToLower()        // two allocations per comparison
///     s.ToLower().StartsWith "abc"     // one allocation per call
///
/// The allocation-free spellings are `String.Equals(a, b, comparison)` and
/// the `StringComparison` overloads of Contains/StartsWith/EndsWith/
/// IndexOf — the form the .NET string best-practices guide names outright
/// (learn.microsoft.com/dotnet/standard/base-types/best-practices-strings:
/// state the comparison explicitly, prefer OrdinalIgnoreCase for
/// non-linguistic matching, do not lower-case to compare). Both the
/// equality and the method-call shapes get a FIX when the other operand is
/// a pure-ASCII literal whose case agrees with the lowering direction;
/// everything else stays advice, because lower-then-compare,
/// OrdinalIgnoreCase and CultureIgnoreCase can differ on edge cases
/// (Turkish dotless i, ß) and there the comparison type is the author's
/// deliberate choice.
///
/// The lowering method is typed-gated to System.String; the Contains
/// rewrite additionally requires the StringComparison overload to exist in
/// the compilation's references (netstandard2.1+).
module FSharp.Refactor.CaseInsensitive

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type CaseKind =
    /// `a.ToLower() = ...` — suggest String.Equals with a comparison.
    | Equality
    /// `s.ToLower().Contains ...` — suggest the comparison overload.
    | MethodCall of methodName: string

type Suggestion =
    {
        Range: range
        Kind: CaseKind
        /// The lowering method used, for the message.
        LoweringName: string
        /// A ready replacement, when the rewrite is provably safe: the
        /// other operand is a pure-ASCII string literal. Measured across
        /// ALL of Unicode, `x.ToLowerInvariant() = "ascii"` and
        /// String.Equals(x, "ascii", OrdinalIgnoreCase) diverge for
        /// exactly ONE input character (U+212A KELVIN SIGN, literals
        /// containing k) and the upper direction for one more (U+017F
        /// LONG S, literals containing s) — compatibility characters
        /// that do not occur in the config values and role strings this
        /// pattern compares. Non-ASCII literals and non-literal
        /// comparisons stay advice.
        Replacement: string option
        /// The culture-aware alternative (InvariantCultureIgnoreCase), for
        /// editors that offer both spellings side by side. The CLI applies
        /// only the primary: ordinal is the right comparison for the config
        /// values and role strings this pattern compares, and a bulk tool
        /// should not guess at linguistics.
        CultureReplacement: string option
    }

let private loweringMethods =
    set [ "ToLower"; "ToUpper"; "ToLowerInvariant"; "ToUpperInvariant" ]

let private comparisonMethods =
    set [ "Contains"; "StartsWith"; "EndsWith"; "IndexOf"; "LastIndexOf" ]

/// `<receiver>.ToLower()` and friends — the lowering method identifier.
[<return: Struct>]
let private (|LoweredCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = UnitConst) when
        ids.Length >= 2 && loweringMethods.Contains (List.last ids).idText
        ->
        ValueSome(List.last ids)
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = [ m ])); argExpr = UnitConst) when
        loweringMethods.Contains m.idText
        ->
        ValueSome m
    | _ -> ValueNone

/// Does the lowering method resolve to System.String?
let private resolvesToStringMethod (check: FSharpCheckFileResults) (source: ISourceText) (methodId: Ident) =
    let r = methodId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ methodId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let enclosing = OptionModule.enclosingFullName value

            enclosing = "System.String"
        | _ -> false
    | None -> false

/// Find allocating case-insensitive comparisons. Requires typed check
/// results for the string gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the receiver's source text, for the String.Equals rewrite
        let receiverTextOf (loweredCall: SynExpr) =
            match loweredCall with
            | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when ids.Length >= 2 ->
                // the receiver's own SOURCE text, not its idText: idText
                // strips the backticks off a ``quoted name``, and the
                // rebuilt receiver would not compile
                let first = List.head ids
                let lastOfReceiver = ids.[ids.Length - 2]

                Some(
                    textOfRange
                        source
                        (Range.mkRange first.idRange.FileName first.idRange.Start lastOfReceiver.idRange.End)
                )
            | SynExpr.App(funcExpr = SynExpr.DotGet(expr = receiver)) -> Some(textOfRange source receiver.Range)
            | _ -> None

        let isAsciiLiteral (e: SynExpr) =
            match e with
            | SynExpr.Const(SynConst.String(text = text), _) -> text |> Seq.forall (fun c -> int c < 128)
            | _ -> false

        // `x.ToLower().StartsWith "FILE:"` can never match — the receiver
        // was just lowered. Rewriting it to OrdinalIgnoreCase would make it
        // start matching, which is a silent behavior change even if it is
        // probably the intended one; mismatched-case literals stay advice.
        let literalAgreesWithLowering (loweringName: string) (e: SynExpr) =
            match e with
            | SynExpr.Const(SynConst.String(text = text), _) ->
                if loweringName.StartsWith "ToLower" then
                    text |> Seq.forall (System.Char.IsAsciiLetterUpper >> not)
                else
                    text |> Seq.forall (System.Char.IsAsciiLetterLower >> not)
            | _ -> false

        // Contains(string, StringComparison) is netstandard2.1+, so on
        // net48/netstandard2.0 that rewrite would not compile; the other
        // comparison methods have carried their StringComparison overload
        // since .NET 2.0. Fail CLOSED, like FR0038's char gate: no visible
        // overload, no fix.
        let hasComparisonOverload (methodId: Ident) =
            let r = methodId.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ methodId.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value ->
                    match value.DeclaringEntity with
                    | Some entity ->
                        (try
                            entity.MembersFunctionsAndValues
                            |> Seq.exists (fun m ->
                                m.LogicalName = methodId.idText
                                && m.CurriedParameterGroups
                                   |> Seq.exists (fun group ->
                                       group.Count = 2
                                       && group.[1].Type.HasTypeDefinition
                                       && group.[1].Type.TypeDefinition.TryFullName = Some "System.StringComparison"))
                         with OptionModule.FcsSymbolFailure ->
                             false)
                    | None -> false
                | _ -> false
            | None -> false

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                    op.idText = "op_Equality" || op.idText = "op_Inequality"
                    ->
                    let lowered =
                        match stripParens lhs, stripParens rhs with
                        | (LoweredCall m as call), other
                        | other, (LoweredCall m as call) -> Some(m, call, other)
                        | _ -> None

                    match lowered with
                    | Some(m, call, other) when resolvesToStringMethod check source m ->
                        let replacementWith (comparison: string) =
                            // same case-agreement gate as the method-call
                            // shape: `x.ToLower() = "ABC"` is always false,
                            // and making it start matching is a behavior
                            // change only a human signs
                            if
                                isAsciiLiteral other
                                && literalAgreesWithLowering m.idText (stripParens other)
                                && isSingleLine expr.Range
                            then
                                receiverTextOf call
                                |> Option.map (fun receiver ->
                                    let literal = textOfRange source other.Range

                                    // without `open System` in the file the
                                    // short spelling would not compile — the
                                    // qualified one always does
                                    let prefix = if opensSystemNamespace source then "" else "System."

                                    let equals =
                                        $"{prefix}String.Equals({receiver}, {literal}, {prefix}StringComparison.{comparison})"

                                    if op.idText = "op_Inequality" then
                                        $"not ({equals})"
                                    else
                                        equals)
                            else
                                None

                        {
                            Range = expr.Range
                            Kind = CaseKind.Equality
                            LoweringName = m.idText
                            Replacement = replacementWith "OrdinalIgnoreCase"
                            CultureReplacement = replacementWith "InvariantCultureIgnoreCase"
                        }
                    | _ -> ()
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.DotGet(
                        expr = (LoweredCall lowering as loweredExpr); longDotId = SynLongIdent(id = [ methodId ]))
                    argExpr = arg) when comparisonMethods.Contains methodId.idText ->
                    if resolvesToStringMethod check source lowering then
                        let literalArg =
                            match stripParens arg with
                            | SynExpr.Const(SynConst.String _, _) as lit -> Some lit
                            | _ -> None

                        let replacementWith (comparison: string) =
                            match literalArg with
                            | Some lit when
                                isAsciiLiteral lit
                                && literalAgreesWithLowering lowering.idText lit
                                && isSingleLine expr.Range
                                && (methodId.idText <> "Contains" || hasComparisonOverload methodId)
                                ->
                                receiverTextOf loweredExpr
                                |> Option.map (fun receiver ->
                                    let literal = textOfRange source lit.Range
                                    let prefix = if opensSystemNamespace source then "" else "System."

                                    $"{receiver}.{methodId.idText}({literal}, {prefix}StringComparison.{comparison})")
                            | _ -> None

                        {
                            Range = expr.Range
                            Kind = CaseKind.MethodCall methodId.idText
                            LoweringName = lowering.idText
                            Replacement = replacementWith "OrdinalIgnoreCase"
                            CultureReplacement = replacementWith "InvariantCultureIgnoreCase"
                        }
                | _ -> ()
        ]
