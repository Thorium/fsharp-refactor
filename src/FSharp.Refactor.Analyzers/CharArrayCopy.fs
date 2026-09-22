/// FR0167 (performance): `ToCharArray()` copies the whole string into an
/// array the consumer then only reads once — a string already IS a
/// sequence of its characters.
///
///     for c in s.ToCharArray() do …        →  for c in s do …
///     Array.exists Char.IsDigit (s.ToCharArray())  →  String.exists Char.IsDigit s
///     s.ToCharArray() |> Array.iter f      →  s |> String.iter f
///
/// Measured in benchmarks/PerfClaims on a runtime-built string: the `for`
/// 13.4 → 9.4 ns and 72 → 0 B per pass, `Array.exists` 9.2 → 4.3 ns and
/// 72 → 0 B. (On a string the JIT knows as a frozen constant .NET 10
/// stack-allocates the copy and the two sides measure at parity; a string
/// that arrives as a parameter pays the copy.) F# compiles `for c in s`
/// over a string to an indexed loop, and the String module's iter, iteri,
/// exists and forall walk the string by index too — the same code, minus
/// the copy.
///
/// Only those four Array functions: `Array.map`/`filter` change the result
/// type under `String.*` (a string, not an array), and `Seq.*` over the
/// string was measured 2.3x SLOWER than over the array (the string's
/// CharEnumerator against the array's), so that copy stays.
///
/// Guards: the call is the argument-free `ToCharArray()` (the two-argument
/// form slices), directly the loop's source or the Array function's only
/// array argument (bound to a name it may be read twice or mutated —
/// left alone); `ToCharArray` resolves to System.String's and the Array
/// function to FSharp.Core's Array module; the compilation is a modern
/// framework (OptionModule.stringIsModern), as the string rules all
/// require; single line; no quotation. The `for` is exact on every input —
/// both sides throw on a null string — and a sweep applies it; the String
/// module treats a null string as EMPTY (`String.exists f null` is false,
/// `String.iter f null` does nothing) where `null.ToCharArray()` threw, so
/// those rewrites are the editor's offer and a note in a sweep.
module FSharp.Refactor.CharArrayCopy

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The expression the fix replaces: the loop source, or the whole
        /// Array call / pipeline.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// "for", or the String function the Array one becomes.
        Consumer: string
        /// The rewrite is the same on every input: the `for` (both sides throw
        /// on a null string) — a sweep applies it. The String functions treat
        /// a null string as empty where the copy threw, so only the editor
        /// offers those; the CLI notes.
        Exact: bool
    }

/// The Array functions whose String twin returns the same type.
let private arrayToString = set [ "iter"; "iteri"; "exists"; "forall" ]

/// `recv.ToCharArray()`: the `ToCharArray` ident and the receiver's text.
[<return: Struct>]
let private (|ToCharArrayCall|_|) (source: ISourceText) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
        match f with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
            ids.Length >= 2 && (List.last ids).idText = "ToCharArray"
            ->
            let receiver = List.take (ids.Length - 1) ids
            let r = Range.unionRanges receiver.Head.idRange (List.last receiver).idRange
            ValueSome(List.last ids, textOfRange source r)
        | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ m ])) when m.idText = "ToCharArray" ->
            ValueSome(m, textOfRange source receiver.Range)
        | _ -> ValueNone
    | _ -> ValueNone

/// `Array.f`: the `Array` ident and the function's name.
[<return: Struct>]
let private (|ArrayFunction|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when
        m.idText = "Array" && arrayToString.Contains f.idText
        ->
        ValueSome(f)
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // System.String's ToCharArray, on a modern framework
        let stringCopy (toCharArray: Ident) =
            match OptionModule.symbolOfIdent check source toCharArray with
            | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                (try
                    match value.ApparentEnclosingEntity with
                    | Some e -> OptionModule.stringIsModern e
                    | None -> false
                 with OptionModule.FcsSymbolFailure ->
                     false)
            | _ -> false

        let coreArrayFunction (f: Ident) =
            match OptionModule.symbolOfIdent check source f with
            | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                OptionModule.enclosingFullName value = "Microsoft.FSharp.Collections.ArrayModule"
            | _ -> false

        // a receiver that needs no parentheses as a function argument
        let atom (text: string) =
            System.Text.RegularExpressions.Regex.IsMatch(text, @"^[\w.']+$")

        let argument (text: string) = if atom text then text else $"({text})"

        [
            for path, expr in index.Exprs do
                if not (insideQuotedCode path) then
                    match expr with
                    // for c in s.ToCharArray() do
                    | SynExpr.ForEach(enumExpr = ToCharArrayCall source (m, receiver) as enumExpr) when
                        isSingleLine enumExpr.Range && stringCopy m
                        ->
                        {
                            Range = enumExpr.Range
                            OriginalText = textOfRange source enumExpr.Range
                            ReplacementText = receiver
                            Consumer = "for"
                            Exact = true
                        }
                    // Array.exists f (s.ToCharArray())
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.App(isInfix = false; funcExpr = ArrayFunction f; argExpr = fn)
                        argExpr = ToCharArrayCall source (m, receiver)) when
                        isSingleLine expr.Range && stringCopy m && coreArrayFunction f
                        ->
                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = $"String.{f.idText} {textOfRange source fn.Range} {argument receiver}"
                            Consumer = $"String.{f.idText}"
                            Exact = false
                        }
                    // s.ToCharArray() |> Array.exists f
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.App(
                            isInfix = true
                            funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ]))
                            argExpr = ToCharArrayCall source (m, receiver))
                        argExpr = SynExpr.App(isInfix = false; funcExpr = ArrayFunction f; argExpr = fn)) when
                        op.idText = "op_PipeRight"
                        && isSingleLine expr.Range
                        && stringCopy m
                        && coreArrayFunction f
                        ->
                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = $"{receiver} |> String.{f.idText} {textOfRange source fn.Range}"
                            Consumer = $"String.{f.idText}"
                            Exact = false
                        }
                    | _ -> ()
        ]
