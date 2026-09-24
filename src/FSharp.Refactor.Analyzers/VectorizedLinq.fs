/// Refactoring note (performance): on .NET 8+ System.Linq's Sum, Average,
/// Min, Max, and Contains are SIMD-vectorized over primitive arrays, while
/// F#'s Array.sum family and Array.contains are scalar loops — for large
/// int[]/int64[] the LINQ call is several times faster (Contains measured
/// ~5x at 1000 ints, ~6x at 100k).
///
///     values |> Array.sum         →  values.Sum()        // open System.Linq
///     values |> Array.contains v  →  values.Contains v
///
/// The aggregations are advice, not a fix, because the semantics are not
/// identical:
///   - LINQ Sum is overflow-CHECKED (throws OverflowException) where
///     Array.sum wraps silently — usually an improvement, but a change
///   - Min/Max/Average throw InvalidOperationException on an empty array
///   - on floats, F# min/max and LINQ Min/Max disagree about NaN, so the
///     note is gated to int/int64 element types where the win is clean
///
/// `Array.contains v arr` is exact on those types and a sweep applies it
/// as `System.Linq.Enumerable.Contains(arr, v)` (`Enumerable.Contains`
/// under `open System.Linq`): int equality agrees with
/// EqualityComparer.Default, and a null array throws ArgumentNullException
/// on both sides. Guards: FSharp.Core's Array module (typed), single line,
/// and where the direct form read the probed value BEFORE a dotted array
/// path (a getter), a value with no effect (a constant, a name). The
/// piped form reads the array first on both sides. `Seq.contains` over an
/// array stays a note here - FR0139 fixes it.
///
/// The array value must be a plain identifier whose type resolves (typed
/// check results) to a vectorizable primitive array.
module FSharp.Refactor.VectorizedLinq

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// "Array" or "Seq" — the module used at the call site.
        ModuleName: string
        /// "sum", "average", "min", "max" — for the message.
        FunctionName: string
        /// The array value's name, for the message.
        ArrayName: string
        /// The exact LINQ spelling the sweep applies over `Range` - an
        /// `Array.contains` only; None for a note.
        ReplacementText: string option
    }

let private vectorizedFunctions = set [ "sum"; "average"; "min"; "max" ]

/// `Seq.sum` over an array is the same scalar loop as `Array.sum`; both
/// modules are matched, and the typed gate below requires the VALUE to be
/// an array (a Seq.sum over a list never fires).
let private aggregationModules = set [ "Array"; "Seq" ]

/// Element types whose LINQ aggregations are vectorized with clean
/// semantics (floats excluded: NaN handling differs between the worlds).
let private vectorizedElements = set [ "System.Int32"; "System.Int64" ]

/// The aggregated array: a bare name or a dotted path (this.samples,
/// state.Buffer). Resolution happens on the LAST ident — the field or
/// property that actually carries the array type.
[<return: Struct>]
let private (|ArrPath|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome(id, id.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.last ids, identText ids)
    | _ -> ValueNone

/// `<m>.<fn> arr` / `arr |> <m>.<fn>` for an aggregation function.
[<return: Struct>]
let private (|ArrayAggregation|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
        argExpr = ArrPath(arr, text)) when aggregationModules.Contains m.idText && vectorizedFunctions.Contains f.idText ->
        ValueSome(m.idText, f, arr, text, None)
    | PipeApp(ArrPath(arr, text), SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))) when
        aggregationModules.Contains m.idText && vectorizedFunctions.Contains f.idText
        ->
        ValueSome(m.idText, f, arr, text, None)
    // `Array.contains v arr` / `arr |> Array.contains v` — two-argument
    // shape; Enumerable.Contains rides the same vectorized span path as
    // the aggregations (measured ~5x at 1000 ints, ~6x at 100k). The
    // probed value comes back too, for the fix
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(
            isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = needle)
        argExpr = ArrPath(arr, text)) when aggregationModules.Contains m.idText && f.idText = "contains" ->
        ValueSome(m.idText, f, arr, text, Some needle)
    | PipeApp(ArrPath(arr, text),
              SynExpr.App(
                  isInfix = false
                  funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                  argExpr = needle)) when aggregationModules.Contains m.idText && f.idText = "contains" ->
        ValueSome(m.idText, f, arr, text, Some needle)
    | _ -> ValueNone

/// Does the identifier resolve to an int[]/int64[]?
let private resolvesToVectorizableArray (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    let vectorizable (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t

            t.HasTypeDefinition
            && t.TypeDefinition.IsArrayType
            && t.GenericArguments.Count = 1
            && (OptionModule.stripAbbreviations t.GenericArguments.[0]).TypeDefinition.TryFullName
               |> Option.exists vectorizedElements.Contains
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> vectorizable value.FullType
        // a record field: `state.Buffer |> Array.sum` resolves Buffer to
        // FSharpField, not a member-or-value
        | :? FSharpField as field -> vectorizable field.FieldType
        | _ -> false
    | None -> false

/// Find scalar Array aggregations with a vectorized LINQ equivalent.
/// Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // spelled so it resolves whether or not System.Linq is open, as
        // FR0139 spells its Contains
        let enumerable =
            if opensNamespace source "System.Linq" then
                "Enumerable"
            else
                "System.Linq.Enumerable"

        let coreArrayFunction (f: Ident) =
            match OptionModule.symbolOfIdent check source f with
            | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                OptionModule.enclosingFullName value = "Microsoft.FSharp.Collections.ArrayModule"
            | _ -> false

        // a needle whose evaluation has no effect: the direct form read it
        // before the array, `Enumerable.Contains(arr, v)` reads it after
        let rec inert (e: SynExpr) =
            match e with
            | SynExpr.Const _
            | SynExpr.Ident _ -> true
            | SynExpr.Paren(expr = inner) -> inert inner
            | _ -> false

        [
            for path, expr in index.Exprs do
                match expr with
                | ArrayAggregation(m, fn, arr, arrText, needle) when
                    not (insideQuotedCode path) && resolvesToVectorizableArray check source arr
                    ->
                    let piped =
                        match expr with
                        | PipeApp _ -> true
                        | _ -> false

                    // `Array.contains` only: `Seq.contains` over an array is
                    // FR0139's fix. The aggregations stay notes - LINQ Sum
                    // throws on overflow where Array.sum wraps, Min/Max/Average
                    // throw InvalidOperationException on an empty array
                    let replacement =
                        match needle with
                        | Some needle when
                            m = "Array"
                            && isSingleLine expr.Range
                            && coreArrayFunction fn
                            && (piped || not (arrText.Contains '.') || inert needle)
                            ->
                            Some $"{enumerable}.Contains({arrText}, {textOfRange source needle.Range})"
                        | _ -> None

                    {
                        Range = expr.Range
                        ModuleName = m
                        FunctionName = fn.idText
                        ArrayName = arrText
                        ReplacementText = replacement
                    }
                | _ -> ()
        ]
