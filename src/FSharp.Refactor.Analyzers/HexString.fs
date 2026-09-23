/// Refactoring (performance, CA1872): hex encoding through BitConverter
/// allocates the dashed string only to strip it again.
///
///     BitConverter.ToString(bytes).Replace("-", "")
///         →  System.Convert.ToHexString bytes
///
/// Convert.ToHexString produces the identical uppercase hex directly (one
/// allocation instead of three). Only the exact dash-stripping shape over
/// a single-argument ToString is rewritten; the offset/length overloads
/// and other Replace arguments are left alone.
module FSharp.Refactor.HexString

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// `BitConverter.ToString(<single arg>)`, optionally System-qualified.
[<return: Struct>]
let private (|BitConverterToString|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2
        && (List.last ids).idText = "ToString"
        && ids.[ids.Length - 2].idText = "BitConverter"
        ->
        match stripParens arg with
        | SynExpr.Tuple _ -> ValueNone // offset/length overloads
        | single -> ValueSome single
    | _ -> ValueNone

[<return: Struct>]
let private (|StringConst|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.String(text, _, _), _) -> ValueSome text
    | _ -> ValueNone

/// Does this compilation's reference set include Convert.ToHexString?
/// (.NET 5+ — absent on netstandard2.0/net48, where the fix would not
/// compile.)
let private toHexStringAvailable (check: FSharpCheckFileResults) =
    check.ProjectContext.GetReferencedAssemblies()
    |> Seq.exists (fun assembly ->
        try
            match assembly.Contents.FindEntityByPath [ "System"; "Convert" ] with
            | Some entity ->
                entity.MembersFunctionsAndValues
                |> Seq.exists (fun m -> m.LogicalName = "ToHexString")
            | None -> false
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false)

/// Does a member access continue off the END of the replaced range?
/// `BitConverter.ToString(h).Replace("-", "").Substring(0, 16)` replaces
/// only as far as the `Replace`, so the space-applied form would leave
/// `Convert.ToHexString h.Substring(0, 16)` — handing the substring OF
/// THE BYTES to ToHexString instead of taking it from the hex. Found live
/// on prismatic, where it cost a whole rollback pass. An indexer or slice
/// (`.Replace("-", "")[..7]`, `.[0]`) continues the same way:
/// `ToHexString hash[..7]` hex-encodes the first eight BYTES. Parenthesise
/// there, and only there.
let private continuesIntoMemberAccess (source: ISourceText) (r: range) =
    let line = source.GetLineString(r.EndLine - 1)

    r.EndColumn < line.Length
    && (line.[r.EndColumn] = '.' || line.[r.EndColumn] = '[')

/// Find dash-stripped BitConverter hex chains. Requires typed check results
/// for the target-framework gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let candidates =
        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.DotGet(
                        expr = BitConverterToString bytes; longDotId = SynLongIdent(id = [ replaceId ]))
                    argExpr = arg) when replaceId.idText = "Replace" && isSingleLine expr.Range ->
                    match stripParens arg with
                    | SynExpr.Tuple(exprs = [ StringConst "-"; StringConst "" ]) ->
                        {
                            Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText =
                                (let prefix = if opensSystemNamespace source then "" else "System."
                                 let call = $"{prefix}Convert.ToHexString {argumentText source bytes}"

                                 if continuesIntoMemberAccess source expr.Range then
                                     $"({call})"
                                 else
                                     call)
                        }
                    | _ -> ()
                | _ -> ()
        ]

    // gate only when there is something to gate: the assembly scan is the
    // expensive part
    match candidates with
    | [] -> []
    | found -> if toHexStringAvailable check then found else []
