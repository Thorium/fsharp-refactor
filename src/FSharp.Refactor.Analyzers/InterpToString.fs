/// Refactoring: drop a redundant `.ToString()` inside an interpolated string.
///
///     $"{x.ToString()} items"   →   $"{x} items"
///
/// String interpolation formats the value the same way, so the call only
/// adds noise (and boxes early). Calls with arguments — `x.ToString("d")` —
/// carry format/culture information and are never touched.
module FSharp.Refactor.InterpToString

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole fill expression `x.ToString()`.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// `<receiver>.ToString()` — returns the receiver's text, or None for any
/// other shape (including ToString with arguments).
let private toStringReceiver (source: ISourceText) (e: SynExpr) : string option =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
        match funcExpr with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
            ids.Length >= 2 && (List.last ids).idText = "ToString"
            ->
            let front = ids.[.. ids.Length - 2]

            let receiverRange =
                Range.mkRange e.Range.FileName (List.head front).idRange.Start (List.last front).idRange.End

            Some(textOfRange source receiverRange)
        | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ name ])) when name.idText = "ToString" ->
            Some(textOfRange source receiver.Range)
        | _ -> None
    | _ -> None

/// Find `.ToString()` calls used as interpolation fills. Fills under a
/// typed hole (`%s{x.ToString()}`) are left alone: the specifier pins the
/// fill's type, so dropping the conversion would not typecheck.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.InterpolatedString(contents = parts) ->
                    let mutable precededBySpecifier = false

                    for part in parts do
                        match part with
                        | SynInterpolatedStringPart.String(value = lead) ->
                            precededBySpecifier <- endsWithFormatSpecifier lead
                        | SynInterpolatedStringPart.FillExpr(fillExpr = fill) ->
                            if not precededBySpecifier && isSingleLine fill.Range then
                                match toStringReceiver source fill with
                                | Some receiverText ->
                                    suggestions.Add
                                        {
                                            Range = fill.Range
                                            OriginalText = textOfRange source fill.Range
                                            ReplacementText = receiverText
                                        }
                                | None -> ()

                            precededBySpecifier <- false
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
