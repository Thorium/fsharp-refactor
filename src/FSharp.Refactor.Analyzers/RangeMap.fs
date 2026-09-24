/// Refactoring (performance): a range built only to be mapped over is
/// `init`, which builds the result and nothing else.
///
///     [| 0 .. dimension - 1 |] |> Array.map f   =>   Array.init dimension f
///
/// The range literal materialises a second array, the same length as the
/// result and of the same element width, purely to have something to walk:
/// at 2^30 elements that is four gigabytes of ints thrown away. Measured
/// at a million elements (.NET 10): 7.0 ms and 8,000,099 B become 3.3 ms
/// and 4,000,044 B - twice as fast on exactly half the allocation, the
/// half being the range itself.
///
/// `Array.init` applies the function for 0, 1, ... n-1 in that order, the
/// same order `Array.map` walks the range in, so a side effect in the
/// function happens as often and in the sequence it did before.
///
/// THE ONE DIFFERENCE is a NEGATIVE count: `[| 0 .. n - 1 |]` with
/// `n = -1` is the empty range, so the map yields `[||]`; `Array.init -1`
/// raises ArgumentException. A count PROVEN non-negative - a literal, or a
/// `Length`/`Count`/`length` the typed tree says is the FRAMEWORK's (a
/// property somebody wrote can answer anything) - is written as is;
/// any other is written `max 0 n`, which hands a negative count the empty
/// result the range gave. Exact for every count either way, so a sweep
/// applies it too: a 2^n array of ints is not worth keeping over a count
/// nobody expects to be negative.
///
/// The count becomes an argument, so one that is not a single atom keeps
/// its parentheses: `[| 0 .. n * 2 - 1 |]` has to produce
/// `Array.init (n * 2) f`, since `Array.init n * 2 f` parses as
/// `(Array.init n) * (2 f)`.
///
/// Declined: a range that does not start at 0 (`[| 1 .. n |] |> map f`
/// would need the function shifted), a stepped range, a mapper spanning
/// lines that is no lambda with its body on a line of its own, or whose
/// later lines are not indented past the column the range starts at (its
/// text moves as written, lines and columns kept, so `Array.init n (fun i
/// ->` over a body indented under it is fine, one hanging left of it is
/// not, and neither is `(fun i -> match i with` over arms aligned to the
/// `match`, which the rewrite moves), and a compiler directive inside
/// the expression - the rewrite drops the range's own text, and a
/// directive written there would go with it. A comment inside is held the
/// same way, by the analyzer's comment guard.
module FSharp.Refactor.RangeMap

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole `range |> X.map f` expression.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// True when the count is provably non-negative, so a sweep may
        /// apply it; otherwise the editor offers it alone.
        CountProven: bool
    }

/// The `init` counterpart of a `map`, and the container the range must be
/// written as for the two to typecheck together. `Seq.map` takes either.
let private initOf (moduleName: string) =
    match moduleName with
    | "Array" -> ValueSome("Array.init", Some true)
    | "List" -> ValueSome("List.init", Some false)
    | "Seq" -> ValueSome("Seq.init", None)
    | _ -> ValueNone

/// Is this identifier the FRAMEWORK's, rather than something of the same
/// name in this project? The whole point of the proof is that the count
/// cannot be negative, and only the framework's `Length`/`Count`/`length`
/// promise that - a property somebody wrote can answer anything, and
/// trusting its NAME would defeat the guard it is here to provide.
let private framework (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match OptionModule.symbolOfIdent check source ident with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            let owner = OptionModule.enclosingFullName value

            owner.StartsWith "System." || owner.StartsWith "Microsoft.FSharp."
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// A count this rule can prove is not negative: a framework length or
/// count read, or a non-negative literal. Anything else is the author's to
/// vouch for, and gets the editor's offer rather than a sweep's edit.
let private provablyNonNegative (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) =
    let isLengthName (name: string) = name = "Length" || name = "Count"

    match stripParens e with
    | SynExpr.Const(SynConst.Int32 n, _) -> n >= 0
    // xs.Length / xs.Count
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty && isLengthName (List.last ids).idText ->
        framework check source (List.last ids)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 && isLengthName (List.last ids).idText ->
        framework check source (List.last ids)
    // Array.length xs, List.length xs, Seq.length xs, String.length s
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; f ])); argExpr = _) when
        f.idText = "length"
        ->
        framework check source f
    | _ -> false

/// The count becomes an ARGUMENT of `init`, so anything that is not a
/// single atom has to keep its own parentheses: `[| 0 .. n * 2 - 1 |]`
/// would otherwise produce `Array.init n * 2 f`, which parses as
/// `(Array.init n) * (2 f)` and does not compile. A literal, a name and a
/// dotted path stand alone; everything else is wrapped.
let private asArgument (source: ISourceText) (e: SynExpr) =
    let text = textOfRange source e.Range

    match e with
    | SynExpr.Const _
    | SynExpr.Ident _
    | SynExpr.LongIdent _
    | SynExpr.DotGet _
    | SynExpr.Paren _ -> text
    | _ -> $"({text})"

/// `0 .. <upper>` written as a range literal, yielding the COUNT the
/// `init` needs: `0 .. c - 1` counts `c`, `0 .. <literal k>` counts
/// `k + 1`, and any other upper bound `n` counts `(n + 1)`.
[<return: Struct>]
let private (|ZeroRangeCount|_|) (check: FSharpCheckFileResults, source: ISourceText) (e: SynExpr) =
    let countOf (upper: SynExpr) =
        match stripParens upper with
        // c - 1
        | SynExpr.App(
            funcExpr = SynExpr.App(funcExpr = SingleIdent minus; argExpr = countExpr)
            argExpr = SynExpr.Const(SynConst.Int32 1, _)) when minus.idText = "op_Subtraction" ->
            ValueSome(asArgument source countExpr, provablyNonNegative check source countExpr)
        // a literal upper bound folds: 0 .. 9 is ten elements
        | SynExpr.Const(SynConst.Int32 k, _) when k >= -1 -> ValueSome(string (k + 1), true)
        // any other upper bound `n` counts `n + 1` (the `0` fixes it as an
        // int, the type `init` takes); a provably non-negative `n` proves
        // the count, anything else is clamped by the caller
        | other -> ValueSome($"({asArgument source other} + 1)", provablyNonNegative check source other)

    match e with
    | SynExpr.IndexRange(expr1 = Some ZeroConst; expr2 = Some upper) -> countOf upper
    | _ -> ValueNone

/// An array or list literal holding exactly one range expression. A
/// stepped range parses with its own shape and never matches here.
[<return: Struct>]
let private (|RangeLiteral|_|) (check: FSharpCheckFileResults, source: ISourceText) (e: SynExpr) =
    match stripParens e with
    | SynExpr.ArrayOrListComputed(isArray = isArray; expr = inner) ->
        match (|ZeroRangeCount|_|) (check, source) inner with
        | ValueSome(count, proven) -> ValueSome(isArray, count, proven)
        | ValueNone -> ValueNone
    | _ -> ValueNone

/// `Array.map` / `List.map` / `Seq.map` as written: the module ident, the
/// `map` ident (for the typed gate) and the function being mapped.
[<return: Struct>]
let private (|MapCall|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = mapper) when
        f.idText = "map"
        ->
        ValueSome(m, f, mapper)
    | _ -> ValueNone

/// Does this `Array`/`List`/`Seq` `.map` resolve to FSharp.Core's? A
/// module of the project's own named `Array` would otherwise be rewritten
/// into a function it does not have.
let private coreMap (check: FSharpCheckFileResults) (source: ISourceText) (moduleIdent: Ident) (mapIdent: Ident) =
    match OptionModule.symbolOfIdent check source mapIdent with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            (OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp.Collections."
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ ->
        ignore moduleIdent
        false

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let suggestions = ResizeArray<Suggestion>()

        // a multi-line mapper (`(fun i ->` and a body under it) moves with its
        // lines where they are: `Array.init n (fun i ->` then starts at the
        // column the range did, and every later line must be indented past it.
        // Only a lambda whose body starts on a line of its own: a token after
        // the arrow moves with the first line, and what later lines aligned to
        // it would turn offside (`match`'s arms) or bind anew (a second
        // statement indented past a first one moved left is its argument)
        let carriesOver (startColumn: int) (mapper: SynExpr) =
            let range = mapper.Range

            let bodyOnItsOwnLine =
                match stripParens mapper with
                | SynExpr.Lambda(parsedData = Some(_, body)) -> body.Range.StartLine > range.StartLine
                | _ -> false

            isSingleLine range
            || bodyOnItsOwnLine
               && [ range.StartLine + 1 .. range.EndLine ]
                  |> List.forall (fun l ->
                      let line = source.GetLineString(l - 1)
                      let trimmed = line.TrimStart()
                      let indent = line.Length - trimmed.Length

                      trimmed = ""
                      || indent > startColumn
                      || (indent = startColumn && trimmed.StartsWith ")"))

        let consider (whole: SynExpr) (rangeExpr: SynExpr) (mapExpr: SynExpr) =
            match (|RangeLiteral|_|) (check, source) rangeExpr, mapExpr with
            | ValueSome(isArray, count, proven), MapCall(moduleIdent, mapIdent, mapper) ->
                match initOf moduleIdent.idText with
                | ValueSome(initName, wantsArray) when
                    wantsArray |> Option.forall (fun a -> a = isArray)
                    // the mapper's text is spliced as written, its later lines
                    // keeping their columns: they must stay right of where
                    // `Array.init` will start (a closing `)` may sit on it)
                    && carriesOver whole.Range.StartColumn mapper
                    // the replacement drops the range's own text, so a
                    // directive inside what it replaces would go with it
                    && not (spansDirective source whole.Range)
                    && coreMap check source moduleIdent mapIdent
                    ->
                    // an unproven count is clamped: `max 0 n` makes a negative
                    // count the empty result the range gave, so the rewrite is
                    // exact for every count and a sweep applies it too
                    let countText = if proven then count else $"(max 0 {count})"

                    suggestions.Add
                        {
                            Range = whole.Range
                            OriginalText = textOfRange source whole.Range
                            ReplacementText = $"{initName} {countText} {textOfRange source mapper.Range}"
                            CountProven = proven
                        }
                | _ -> ()
            | _ -> ()

        let collector =
            { new SyntaxCollectorBase() with
                override _.WalkExpr(_path, expr) =
                    match expr with
                    // range |> Array.map f
                    | PipeApp(lhs, rhs) -> consider expr lhs rhs
                    // Array.map f range
                    | SynExpr.App(isInfix = false; funcExpr = (MapCall _ as mapExpr); argExpr = arg) ->
                        consider expr arg mapExpr
                    | _ -> ()
            }

        AstIndex.replay collector parseTree
        List.ofSeq suggestions
