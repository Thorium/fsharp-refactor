/// FR0171 (performance): an ASCII literal encoded to bytes at run time is a
/// byte string literal.
///
///     Encoding.UTF8.GetBytes "GET / HTTP/1.1"    →  "GET / HTTP/1.1"B
///     Encoding.ASCII.GetBytes("OK")               →  "OK"B
///
/// `GetBytes` runs the encoder over the string on every call and
/// allocates the result; `"..."B` is the bytes as compiled data, copied
/// into a fresh array by `InitializeArray` — no encoder, no transcoding
/// pass, and the same `byte[]` type. CSharp.Refactor's CR0148 (`"..."u8`).
///
/// Guards: the receiver is `Encoding.UTF8`, `Encoding.ASCII`, `Encoding.Latin1`
/// or `Encoding.Default` spelled with any prefix of `System.Text`, or a
/// static `UTF8Encoding`/`ASCIIEncoding` instance is not asked; the
/// argument is one regular or verbatim string literal (no interpolation,
/// no triple quotes) whose every character is ASCII — a non-ASCII
/// character differs between the encodings, and `"…"B` refuses it (FS1140);
/// no quotation. Typed where check results exist (the `GetBytes` must be
/// System.Text.Encoding's); parse-only, the receiver spelling is the proof:
/// a user type named `Encoding` with a `UTF8` member of its own is a
/// stretch the rule accepts.
module FSharp.Refactor.ByteStringLiteral

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole `Encoding.X.GetBytes arg` application.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// `UTF8`, `ASCII`, ... for the message.
        EncodingName: string
    }

let private encodings = set [ "UTF8"; "ASCII"; "Latin1"; "Default" ]

/// `[System.][Text.]Encoding.<enc>.GetBytes`.
let private getBytesOf (ids: Ident list) =
    match List.rev ids with
    | m :: enc :: encoding :: prefix when
        m.idText = "GetBytes"
        && encodings.Contains enc.idText
        && encoding.idText = "Encoding"
        && (match prefix |> List.rev |> List.map (fun i -> i.idText) with
            | []
            | [ "Text" ]
            | [ "System"; "Text" ] -> true
            | _ -> false)
        ->
        ValueSome enc.idText
    | _ -> ValueNone

/// A plain ASCII string literal: regular or verbatim, every char below 128.
let private asciiLiteral (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const(SynConst.String(text, (SynStringKind.Regular | SynStringKind.Verbatim), _), _) when
        text |> Seq.forall (fun c -> int c < 128)
        ->
        true
    | _ -> false

/// With check results the `GetBytes` must be System.Text.Encoding's own (a
/// user `Encoding` type with a `UTF8` member is not rewritten); without them
/// the receiver spelling is the proof.
let findWith (check: FSharpCheckFileResults option) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let isEncodings (getBytes: Ident) =
        match check with
        | None -> true
        | Some check ->
            match OptionModule.symbolOfIdent check source getBytes with
            | Some(:? FSharpMemberOrFunctionOrValue as mfv) ->
                (try
                    mfv.DeclaringEntity
                    |> Option.bind (fun e -> e.TryFullName)
                    |> Option.exists (fun n -> n = "System.Text.Encoding" || n.StartsWith "System.Text.")
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false

    [
        for _, e in index.Exprs do
            match e with
            | SynExpr.App(
                isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                isSingleLine e.Range
                ->
                match getBytesOf ids with
                | ValueSome enc when asciiLiteral arg && isEncodings (List.last ids) ->
                    let literal = stripParens arg

                    {
                        Range = e.Range
                        OriginalText = textOfRange source e.Range
                        ReplacementText = textOfRange source literal.Range + "B"
                        EncodingName = enc
                    }
                | _ -> ()
            | _ -> ()
    ]

/// `findWith` without check results: the parse-only entry.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list = findWith None parseTree source
