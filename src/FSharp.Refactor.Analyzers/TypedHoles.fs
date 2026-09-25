/// Refactoring: in an interpolated string that already uses typed holes,
/// type the remaining plain holes too.
///
///     $"%s{name} is {age}"   →  $"%s{name} is %d{age}"
///
/// A typed hole pins the fill's type at compile time — change `age` to a
/// record and `%d{age}` stops compiling where `{age}` silently switches
/// to ToString output.
///
/// Deliberately narrow:
///   - only strings that ALREADY contain a %-specifier hole are touched:
///     those are on the printf formatting path anyway, so adding
///     specifiers costs nothing. A specifier-free string interpolation
///     lowers to String.Concat on F# 8+ — adding `%s` there would move it
///     to the slower path, so it is left alone.
///   - only specifiers whose output provably equals ToString: `%s` for
///     strings, `%d` for integer types, `%c` for chars. `%b` lowercases
///     booleans and `%f` pads floats — those fills stay untyped.
///   - the fill must be an identifier or dotted path that resolves via
///     the typed check results.
module FSharp.Refactor.TypedHoles

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Zero-width insertion point just before the fill's `{`.
        Range: range
        /// "%s", "%d", or "%c".
        Specifier: string
        /// The fill's text, for the message.
        FillText: string
    }

/// Trailing text that means the NEXT fill already has a specifier.
let private hasUnescapedSpecifier (text: string) = endsWithFormatSpecifier text

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
        ]

/// The provably ToString-identical specifier for the fill's type.
let private specifierFor (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        let fillType =
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value -> Some(resultTypeOf value)
            | :? FSharpField as field -> Some field.FieldType
            | _ -> None

        fillType
        |> Option.bind (fun t ->
            try
                let t = OptionModule.stripAbbreviations t

                if not t.HasTypeDefinition then
                    None
                else
                    match t.TypeDefinition.TryFullName with
                    | Some "System.String" -> Some "%s"
                    | Some "System.Char" -> Some "%c"
                    | Some name when integerTypes.Contains name -> Some "%d"
                    | _ -> None
            with OptionModule.FcsSymbolFailure ->
                None)
    | None -> None

/// Find untyped fills in already-typed interpolated strings. Requires
/// typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.InterpolatedString(contents = parts; range = stringRange) ->
                    // `$$"""…"""` (F# 8): as many `$` as open the string, so
                    // many braces open a hole and so many `%` start a
                    // specifier — a lone `{` or `%` is text there. The parser
                    // hands the String parts back with `%%s` already folded
                    // to `%s`, so past one `$` the raw text decides; and a
                    // part's range ends after ALL the braces opening its hole
                    let dollars =
                        let lineText = source.GetLineString(stringRange.StartLine - 1)

                        let rec advanceN n =
                            if
                                stringRange.StartColumn + n < lineText.Length
                                && lineText.[stringRange.StartColumn + n] = '$'
                            then
                                advanceN (n + 1)
                            else
                                n

                        let n = advanceN 0

                        max 1 n

                    let opensHole (leadRange: range) =
                        let raw = textOfRange source leadRange

                        raw.Length >= dollars
                        && raw.Substring(raw.Length - dollars) = String.replicate dollars "{"
                        && (raw.Length = dollars || raw.[raw.Length - dollars - 1] <> '{')

                    // the lexer folds a `$$` part's value into printf
                    // convention (`%%s` → `%s`, a literal `%` stays `%%`), so
                    // the same parity-aware check reads every dollar count;
                    // the raw text would misread `%%%s{{x}}` (literal percent
                    // and then a specifier) as untyped
                    let typedLead (lead: string) (_: range) = hasUnescapedSpecifier lead

                    // pair every fill with the literal text preceding it
                    let fillsWithLeadText =
                        parts
                        |> List.pairwise
                        |> List.choose (fun pair ->
                            match pair with
                            | SynInterpolatedStringPart.String(value = lead; range = leadRange),
                              SynInterpolatedStringPart.FillExpr(fillExpr = fill; qualifiers = None) when
                                opensHole leadRange
                                ->
                                Some(lead, leadRange, fill)
                            | _ -> None)

                    let anyTyped =
                        fillsWithLeadText
                        |> List.exists (fun (lead, leadRange, _) -> typedLead lead leadRange)

                    if anyTyped then
                        for lead, leadRange, fill in fillsWithLeadText do
                            if not (typedLead lead leadRange) then
                                let fillIdent =
                                    match stripParens fill with
                                    | SynExpr.Ident id -> Some id
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                        Some(List.last ids)
                                    | _ -> None

                                match fillIdent |> Option.bind (specifierFor check source) with
                                | Some specifier when leadRange.EndColumn >= dollars ->
                                    // the String part's range includes the
                                    // trailing `{` (`{{` under `$$`); insert
                                    // just before it, with as many `%` as
                                    // the string has `$`
                                    let insertAt = Position.mkPos leadRange.EndLine (leadRange.EndColumn - dollars)

                                    {
                                        Range = Range.mkRange leadRange.FileName insertAt insertAt
                                        Specifier = String.replicate (dollars - 1) "%" + specifier
                                        FillText = textOfRange source fill.Range
                                    }
                                | _ -> ()
                | _ -> ()
        ]
