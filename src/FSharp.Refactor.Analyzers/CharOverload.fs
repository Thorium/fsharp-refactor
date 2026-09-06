/// Refactoring (performance, CA1834/CA1847/CA1865-1867 family): a
/// single-character string passed where a char overload exists.
///
///     s.Contains "x"                            →  s.Contains 'x'
///     sb.Append "x"                             →  sb.Append 'x'
///     s.StartsWith("x", StringComparison.Ordinal)  →  s.StartsWith 'x'
///
/// The char overloads skip the string-comparison setup entirely.
///
/// The culture nuance decides fix vs advice: `Contains(string)` and
/// `StringBuilder.Append` are already ordinal, and an explicit
/// `StringComparison.Ordinal` argument matches the char overload's
/// behavior — those get fixes. Bare `StartsWith`/`EndsWith`/`IndexOf`
/// with a string are CULTURE-sensitive while the char overloads are
/// ordinal, so those only get an advisory note asking the author to
/// verify ordinal semantics are acceptable.
///
/// Method resolution is typed-gated to System.String / StringBuilder, so
/// a Contains on a collection never matches.
module FSharp.Refactor.CharOverload

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        /// None = advisory only (culture-sensitive overload).
        ReplacementText: string option
        /// For a bare culture-sensitive call: the editor's offer of the
        /// ordinal char overload — (literal range, original, char literal).
        /// The CLI never applies it; ordinal-versus-culture is intent.
        OrdinalOffer: (range * string * string) option
        /// Where the project's NARROWEST target has no char overload —
        /// `Contains(char)` arrived in netstandard2.1 — the portable
        /// rewrite instead: `s.Contains "x"` → `s.IndexOf 'x' >= 0`.
        /// `IndexOf(char)` exists on every framework and is ordinal, as
        /// `Contains(string)` already is, so the two forms agree. Offered
        /// for `Contains` alone: the culture-sensitive methods would
        /// change meaning, which is the author's call, not a portability
        /// fix. Editor-offered, like OrdinalOffer.
        PortableOffer: (range * string * string) option
        MethodName: string
    }

/// string methods with char overloads that are ordinal either way
let private ordinalSafeMethods = set [ "Contains" ]

/// string methods whose string overload is culture-sensitive
let private cultureSensitiveMethods =
    set [ "StartsWith"; "EndsWith"; "IndexOf"; "LastIndexOf" ]

let private enclosingEntities =
    [ "System.String", ordinalSafeMethods + cultureSensitiveMethods
      "System.Text.StringBuilder", set [ "Append" ] ]

/// Render a char literal for the single character of a string constant.
let private charLiteral (c: char) =
    let escaped =
        match c with
        | '\\' -> "\\\\"
        | '\'' -> "\\'"
        | '\n' -> "\\n"
        | '\r' -> "\\r"
        | '\t' -> "\\t"
        | other ->
            if System.Char.IsControl other then
                sprintf "\\u%04x" (int other)
            else
                string other

    $"'{escaped}'"

/// A single-character regular string constant.
[<return: Struct>]
let private (|SingleCharString|_|) (e: SynExpr) =
    match e with
    // all three kinds: `@"\"` is THE spelling of a backslash in path code,
    // and the AST's text is already decoded either way (the FR0015 lesson)
    | SynExpr.Const(SynConst.String(text,
                                    (SynStringKind.Regular | SynStringKind.Verbatim | SynStringKind.TripleQuote),
                                    _),
                    _) when text.Length = 1 -> ValueSome(text.[0], e.Range)
    | _ -> ValueNone

/// `StringComparison.Ordinal` as an argument expression.
[<return: Struct>]
let private (|OrdinalComparison|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        ids.Length >= 2
        && (List.last ids).idText = "Ordinal"
        && ids.[ids.Length - 2].idText = "StringComparison"
        ->
        ValueSome()
    | _ -> ValueNone

/// Does this method have an overload whose first parameter is char? On
/// netstandard2.0/net48 e.g. String.Contains(char) does not exist and the
/// rewrite would not compile. Fails OPEN: when the member list yields no
/// overloads at all the scan is blind, and no-information must not
/// suppress — only a visible overload set without a char variant does.
/// Is the type char, possibly through the F# `char` abbreviation?
[<TailCall>]
let rec private isCharType (t: FSharpType) =
    t.HasTypeDefinition
    && (t.TypeDefinition.TryFullName = Some "System.Char"
        || (t.TypeDefinition.IsFSharpAbbreviation
            && isCharType t.TypeDefinition.AbbreviatedType))

let private hasCharOverload (entity: FSharpEntity) (methodName: string) =
    let takesChar (m: FSharpMemberOrFunctionOrValue) =
        try
            m.CurriedParameterGroups
            |> Seq.exists (fun group -> group.Count >= 1 && isCharType group.[0].Type)
        with OptionModule.FcsSymbolFailure ->
            false

    let overloads =
        try
            entity.MembersFunctionsAndValues
            |> Seq.filter (fun m ->
                try
                    m.LogicalName = methodName
                with OptionModule.FcsSymbolFailure ->
                    false)
            |> Seq.toList
        with OptionModule.FcsSymbolFailure ->
            []

    // fail CLOSED: a blind member list is no proof the char overload
    // exists, and this rule's fixes were exactly the ones a
    // multi-framework build check had to put back on SQLProvider. Same
    // policy as FR0106's span-overload gate — no proof, no fix.
    overloads |> List.exists takesChar

/// Does the method identifier resolve to one of the gated BCL types, with a
/// char overload available in this compilation's references?
let private resolvesToGatedMethod (check: FSharpCheckFileResults) (source: ISourceText) (methodId: Ident) =
    let r = methodId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ methodId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let enclosingEntity =
                try
                    value.ApparentEnclosingEntity
                with OptionModule.FcsSymbolFailure ->
                    None

            let enclosing =
                enclosingEntity
                |> Option.bind (fun e -> e.TryFullName)
                |> Option.defaultValue ""

            enclosingEntities
            |> List.exists (fun (entity, methods) -> enclosing = entity && methods.Contains methodId.idText)
            && (enclosingEntity |> Option.exists (fun e -> hasCharOverload e methodId.idText))
        | _ -> false
    | None -> false

/// Find single-character string arguments to char-overloaded methods.
/// Requires typed check results for the receiver gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for path, expr in index.Exprs do
              match expr with
              // inside query { } / <@ @> the STRING overload is the shape
              // a LINQ translator recognizes (Contains -> SQL LIKE); the
              // char overload is a tree it has never seen
              | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = arg) when not (insideQuotedCode path) ->
                  let methodId =
                      match funcExpr with
                      | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                          Some(List.last ids)
                      | SynExpr.DotGet(longDotId = SynLongIdent(id = [ id ])) -> Some id
                      | _ -> None

                  match methodId with
                  | Some methodId when
                      (ordinalSafeMethods.Contains methodId.idText
                       || cultureSensitiveMethods.Contains methodId.idText
                       || methodId.idText = "Append")
                      && resolvesToGatedMethod check source methodId
                      ->
                      let cultureSensitive = cultureSensitiveMethods.Contains methodId.idText

                      match stripParens arg with
                      | SingleCharString(c, literalRange) ->
                          // bare culture-sensitive calls get advice only —
                          // plus an editor offer of the ordinal char
                          // overload, the author's call to take; ordinal-safe
                          // ones get the literal replaced
                          let range, replacement =
                              if cultureSensitive then
                                  expr.Range, None
                              else
                                  literalRange, Some(charLiteral c)

                          // the receiver, for the portable IndexOf form
                          let receiverText =
                              match funcExpr with
                              | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                  let prefix = ids |> List.take (ids.Length - 1)

                                  Some(
                                      textOfRange
                                          source
                                          (Range.mkRange
                                              expr.Range.FileName
                                              (List.head prefix).idRange.Start
                                              (List.last prefix).idRange.End)
                                  )
                              | SynExpr.DotGet(expr = recv) -> Some(textOfRange source recv.Range)
                              | _ -> None

                          { Range = range
                            OriginalText = textOfRange source range
                            ReplacementText = replacement
                            OrdinalOffer =
                              if cultureSensitive then
                                  Some(literalRange, textOfRange source literalRange, charLiteral c)
                              else
                                  None
                            PortableOffer =
                              if methodId.idText = "Contains" && isSingleLine expr.Range then
                                  receiverText
                                  |> Option.map (fun r ->
                                      expr.Range, textOfRange source expr.Range, $"{r}.IndexOf {charLiteral c} >= 0")
                              else
                                  None
                            MethodName = methodId.idText }
                      | SynExpr.Tuple(exprs = [ SingleCharString(c, _); OrdinalComparison ]) when cultureSensitive ->
                          // explicit Ordinal matches the char overload: fix
                          // by replacing the whole argument list
                          { Range = arg.Range
                            OriginalText = textOfRange source arg.Range
                            ReplacementText = Some $"({charLiteral c})"
                            OrdinalOffer = None
                            PortableOffer = None
                            MethodName = methodId.idText }
                      | _ -> ()
                  | _ -> ()
              | _ -> () ]
