/// FR0139 (fix, performance): a `Seq.` function applied to something the
/// typed tree proves is an ARRAY goes through IEnumerable — an enumerator
/// allocation and an interface call per element — where the `Array.`
/// function reads the block directly.
///
///     arr |> Seq.length            →  arr |> Array.length
///     Seq.exists p arr             →  Array.exists p arr
///
/// ARRAYS ONLY, deliberately. A `Seq.` call on a list or on a lazy source
/// can be the author's point: seq is lazy, and on an IQueryable the Seq
/// functions are what the provider translates — rewriting either changes
/// meaning or defeats the intent. An array is already materialised and
/// contiguous, so there is no laziness to preserve and the concrete
/// module is strictly cheaper.
///
/// Only functions whose RESULT TYPE is unchanged are rewritten: `Seq.map`
/// and friends return `seq<'b>` where `Array.map` returns `'b[]`, which
/// would change the expression's type and ripple into its consumer.
///
/// `item` is deliberately absent: `Array.item` throws
/// IndexOutOfRangeException where `Seq.item` throws ArgumentException —
/// the same reason FR0004 refuses to move it.
///
/// The NUMERIC AGGREGATES — sum, sumBy, average, averageBy, min, max,
/// minBy, maxBy — are absent too, and on purpose: FR0041 points the other
/// way there, because .NET vectorises the LINQ aggregates over
/// span-backed sources. Rewriting them here would have this rule arguing
/// with that one over the same line of code.
module FSharp.Refactor.SeqOnArray

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `Seq` segment itself — the whole fix is its replacement.
        Range: range
        FunctionName: string
        CollectionText: string
        /// `contains` over a VECTORISABLE element type has two better
        /// answers rather than one, so it carries the whole call's range
        /// and a ready LINQ spelling. That spelling is the DEFAULT the CLI
        /// applies — it is 5.4x where the Array module is 1.27x, and this
        /// is a performance rule — with `Array.contains` offered beside it
        /// in an editor for anyone who wants the idiomatic step instead.
        LinqSpelling: (range * string) option
    }

/// Seq functions that return a scalar, an option or unit — never a
/// collection, so swapping the module cannot change the expression type —
/// AND that measure faster on .NET 10, the runtime this targets:
///
///     head 17.2 -> 2.7ns   last 25.4 -> 5.8ns   find 707 -> 237ns
///     forall 572 -> 237ns  fold 567 -> 239ns    tryFind 577 -> 238ns
///     isEmpty 4.9 -> 3.3ns length 3.6 -> 2.2ns
///
/// `iter`/`iteri` are absent: measured 236.6 against 235.4ns, a wash, and
/// a performance rule has no business rewriting code for half a percent.
/// `contains` is absent for a sharper reason — see below.
let private sameResultShape =
    set
        [
            "length"
            "isEmpty"
            "exists"
            "forall"
            "find"
            "tryFind"
            "findIndex"
            "tryFindIndex"
            "findBack"
            "tryFindBack"
            "pick"
            "tryPick"
            "head"
            "tryHead"
            "last"
            "tryLast"
            "exactlyOne"
            "tryExactlyOne"
            "fold"
            "reduce"
        ]

/// An identifier or dotted path — the only collection shapes typed here.
[<return: Struct>]
let private (|Path|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident i -> ValueSome(i, i.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        ValueSome(List.last ids, identText ids) // the LAST segment carries the type: `s.Buffer` is the field
    | _ -> ValueNone

/// The head of a (possibly curried) application: `Seq.exists p` leads to
/// the `Seq`/`exists` identifier pair.
[<TailCall>]
let rec private seqHead (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when m.idText = "Seq" -> ValueSome(m, f)
    | SynExpr.App(isInfix = false; funcExpr = inner) -> seqHead inner
    | _ -> ValueNone

/// `contains` has TWO better answers on these element types, not one, so
/// it is handled apart from the list above. Measured on .NET 10 over 1000
/// ints: Seq.contains 587ns, Array.contains 464ns, and the vectorised
/// Enumerable.Contains 109ns. The LINQ spelling is the default the CLI
/// applies — 5.4x against the Array module's 1.27x, and this rule exists
/// to make code faster; an editor offers the idiomatic Array step beside
/// it for anyone who would rather keep the F# module.
///
/// The set is deliberately these two types only. Their F# structural
/// equality and EqualityComparer.Default agree, so the LINQ spelling is
/// not merely faster but equivalent — which is not true in general.
let private vectorisableElements = set [ "System.Int32"; "System.Int64" ]

/// On a REFERENCE array `contains` gets no rule at all: Seq.contains
/// measures 938ns against Array.contains at 1024ns, so the "obvious"
/// conversion is a small LOSS. (On .NET 8 it was a win — which is exactly
/// why the benchmarks target the runtime the customer actually runs.)
///
/// Is this `Seq.f` the REAL FSharp.Core Seq module? A file may define its
/// own `Seq`, and swapping that to `Array` would name a function nobody
/// wrote. Every comparable rule here is typed-gated; so is this one.
let private resolvesToSeqModule (check: FSharpCheckFileResults) (source: ISourceText) (f: Ident) =
    let r = f.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ f.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            OptionModule.enclosingFullName value = "Microsoft.FSharp.Collections.SeqModule"
        | _ -> false
    | None -> false

/// The array's element type name, or None when the path is not an array.
let private arrayElementOf (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    let elementOf (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t

            if
                t.HasTypeDefinition
                && t.TypeDefinition.IsArrayType
                && t.GenericArguments.Count = 1
            then
                // "" for an element with no full name (a generic parameter):
                // still an array, just never a vectorisable one
                Some(
                    (OptionModule.stripAbbreviations t.GenericArguments.[0]).TypeDefinition.TryFullName
                    |> Option.defaultValue ""
                )
            else
                None
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            None

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> elementOf value.FullType
        // `state.Buffer |> Seq.length` resolves Buffer to a field
        | :? FSharpField as field -> elementOf field.FieldType
        | _ -> None
    | None -> None

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for _, expr in index.Exprs do
                let candidate =
                    match expr with
                    // arr |> Seq.length   /   arr |> Seq.exists p
                    | PipeApp(Path(root, text), rhs) ->
                        match seqHead rhs with
                        | ValueSome(m, f) -> Some(m, f, root, text)
                        | ValueNone -> None
                    // Seq.length arr   /   Seq.exists p arr
                    | SynExpr.App(isInfix = false; funcExpr = fn; argExpr = Path(root, text)) ->
                        match seqHead fn with
                        | ValueSome(m, f) -> Some(m, f, root, text)
                        | ValueNone -> None
                    | _ -> None

                match candidate with
                | Some(m, f, root, text) when resolvesToSeqModule check source f ->
                    match arrayElementOf check source root with
                    | None -> ()
                    | Some element ->
                        if sameResultShape.Contains f.idText then
                            {
                                Range = m.idRange
                                FunctionName = f.idText
                                CollectionText = text
                                LinqSpelling = None
                            }
                        elif f.idText = "contains" && vectorisableElements.Contains element then
                            // the second, faster answer, spelled so it
                            // resolves whether or not System.Linq is open
                            let prefix =
                                if opensNamespace source "System.Linq" then
                                    "Enumerable"
                                else
                                    "System.Linq.Enumerable"

                            let needle =
                                match expr with
                                | PipeApp(_, rhs) ->
                                    match rhs with
                                    | SynExpr.App(argExpr = arg) -> textOfRange source arg.Range
                                    | _ -> ""
                                | SynExpr.App(funcExpr = SynExpr.App(argExpr = arg)) -> textOfRange source arg.Range
                                | _ -> ""

                            if needle <> "" then
                                {
                                    Range = m.idRange
                                    FunctionName = f.idText
                                    CollectionText = text
                                    LinqSpelling = Some(expr.Range, $"{prefix}.Contains({text}, {needle})")
                                }
                | _ -> ()
        ]
