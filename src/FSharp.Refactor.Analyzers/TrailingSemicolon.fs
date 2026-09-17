/// Refactoring: a `;` that ends a line says nothing in light syntax.
///
///     let x = 1;              →  let x = 1
///     printfn "starting";     →  printfn "starting"
///
/// In light (offside) syntax — the default, and what almost all F# is
/// written in — a newline already separates expressions, so a `;` before one
/// is left over from another language.
///
/// It is NOT left over in three places, and none of them are touched:
///
///   - inside a list, array, record or anonymous record. There `;` is the
///     element separator doing its job, whether or not a newline follows:
///     `[ 1;` on its own line is separating 1 from what comes next.
///
///   - inside an attribute group. `[<Foo;` continues into the next
///     attribute, exactly as inside a list.
///
///   - anywhere in a file that turns light syntax off with `#light "off"`,
///     where `;` is significant and removing one changes the parse.
///
/// `;;` is left alone too. It terminates an interaction in F# Interactive,
/// which is a different thing from separating two expressions.
module FSharp.Refactor.TrailingSemicolon

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Compiler.Tokenization
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the semicolon and the blank space before it.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// Ranges where `;` separates rather than terminates.
/// Read straight off the index rather than through `AstIndex.replay`, which
/// drives WalkExpr and WalkSynModuleDecl only — a WalkPat override there is
/// never called, so list PATTERNS went unprotected and their separators were
/// stripped:
///
///     | MethodCall(None, name, [ SourceWithQueryData source;
///                                OptionalQuote q ]) -> ...
let private separatorRanges (parseTree: ParsedInput) =
    let index = AstIndex.ofTree parseTree

    let ranges: range list =
        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.ArrayOrList _
                | SynExpr.ArrayOrListComputed _
                | SynExpr.Record _
                | SynExpr.AnonRecd _
                // A computation expression too, though its `;` sequences rather than
                // separates. Inside one it also holds the LAYOUT together:
                //
                //     seq { yield 1;
                //         yield 2;
                //       yield 3 }
                //
                // parses, and the same lines without the semicolons do not (FS0010).
                // Cleaning a `;` that reads as redundant is not worth breaking that.
                | SynExpr.ComputationExpr _ -> expr.Range
                | _ -> ()

            for _, pat in index.Pats do
                match pat with
                | SynPat.ArrayOrList _
                | SynPat.Record _ -> pat.Range
                | _ -> ()

            // a record TYPE's field list separates with `;` exactly as a record
            // expression does
            for _, decl in index.Decls do
                match decl with
                | SynModuleDecl.Types(typeDefns = defns) ->
                    for SynTypeDefn(typeRepr = repr) in defns do
                        match repr with
                        | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Record(range = r)) -> r
                        | _ -> ()
                | _ -> ()
        ]

    ranges

/// How many times does `needle` occur in `text`? Counting a two-character
/// literal is a plain scan; a regex would parse its pattern on every line,
/// which is what our own FR0015 says about doing this in a loop.
let private countOccurrences (needle: string) (text: string) =
    let mutable count = 0
    let mutable index = text.IndexOf(needle, StringComparison.Ordinal)

    while index >= 0 do
        count <- count + 1
        index <- text.IndexOf(needle, index + needle.Length, StringComparison.Ordinal)

    count

/// Does this line's last content end in `;`, ignoring blanks and a trailing
/// `//` comment? Deliberately crude — a `;` closing a string, or one inside a
/// comment, matches here too. This only decides whether the file is worth
/// lexing at all; the tokenizer settles what each one really is.
let private endsWithSemicolon (line: string) =
    /// The last non-blank character at or before `from`, or -1.
    let lastNonBlankAt (from: int) =
        let rec retreatI i =
            if i >= 0 && Char.IsWhiteSpace line.[i] then
                retreatI (i - 1)
            else
                i

        let i = retreatI from

        i

    let last = lastNonBlankAt (line.Length - 1)

    if last >= 0 && line.[last] = ';' then
        true
    else
        // `let x = 1; // note` ends in a comment, with the semicolon before it
        let comment = line.IndexOf("//", StringComparison.Ordinal)

        if comment <= 0 then
            false
        else
            let beforeComment = lastNonBlankAt (comment - 1)
            beforeComment >= 0 && line.[beforeComment] = ';'

/// One pass over the raw text, answering both questions that can rule the
/// whole file out before any lexing happens: does it turn light syntax off,
/// and does any line end in a semicolon at all?
///
/// Lexing is what makes a `;` inside a string or comment safe to ignore, and
/// it is by far the most expensive thing this rule does — a second full
/// lexical pass. Most F# files have no line-ending semicolon whatsoever, and
/// those pay only the scan below.
let private worthLexing (source: ISourceText) =
    let mutable verbose = false
    let mutable candidate = false
    let mutable line = 0
    let lineCount = source.GetLineCount()

    while not verbose && line < lineCount do
        let text = source.GetLineString line

        if text.Contains "#light" && (text.Contains "\"off\"" || text.Contains "off") then
            verbose <- true
        elif not candidate && endsWithSemicolon text then
            candidate <- true

        line <- line + 1

    not verbose && candidate

/// The last token on a line that is neither blank nor a comment, with the
/// column the run of blank space before it starts at.
let private lastMeaningfulToken (tokenizer: FSharpSourceTokenizer) (line: string) (state: FSharpTokenizerLexState) =
    let lineTokenizer = tokenizer.CreateLineTokenizer line
    let mutable current = state
    let mutable finished = false
    let mutable last = None
    let mutable blankStartedAt = 0

    while not finished do
        let token, next = lineTokenizer.ScanToken current
        current <- next

        match token with
        | None -> finished <- true
        | Some info ->
            let isBlank = info.TokenName = "WHITESPACE"
            let isComment = info.ColorClass = FSharpTokenColorKind.Comment

            if not (isBlank || isComment) then
                last <- Some(info, blankStartedAt)
                blankStartedAt <- info.RightColumn + 1
            elif isBlank && blankStartedAt <> info.LeftColumn then
                blankStartedAt <- info.LeftColumn

    last, current

/// Find semicolons that end a line for no reason.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    if not (worthLexing source) then
        []
    else

        let protectedRanges = separatorRanges parseTree
        let fileName = parseTree.FileName

        // conditional defines do not matter here: an inactive `#if` branch is
        // tokenized as inactive code, and we only act on real semicolon tokens
        let tokenizer = FSharpSourceTokenizer([], Some fileName, None, None)
        let mutable state = FSharpTokenizerLexState.Initial
        // attribute groups span lines: `[<Foo;` then `Bar>]`
        let mutable attributeDepth = 0

        let suggestions: Suggestion list =
            [
                for lineIndex in 0 .. source.GetLineCount() - 1 do
                    let lineText = source.GetLineString lineIndex
                    let lineNumber = lineIndex + 1

                    // depth entering this line decides whether its own `;` is inside a
                    // group; count the line's brackets afterwards for the next line
                    let depthEnteringLine = attributeDepth

                    let opened = countOccurrences "[<" lineText
                    let closed = countOccurrences ">]" lineText

                    attributeDepth <- max 0 (attributeDepth + opened - closed)

                    let last, nextState = lastMeaningfulToken tokenizer lineText state
                    state <- nextState

                    match last with
                    | Some(info, blankStartedAt) when info.TokenName = "SEMICOLON" ->
                        let semicolonStart = Position.mkPos lineNumber info.LeftColumn
                        let semicolonEnd = Position.mkPos lineNumber (info.RightColumn + 1)

                        let insideSeparatorList =
                            protectedRanges
                            |> List.exists (fun r -> Range.rangeContainsPos r semicolonStart)

                        // an attribute group open on this line, or still open from an
                        // earlier one, makes the `;` a separator
                        let insideAttribute = depthEnteringLine > 0 || opened > closed

                        if not (insideSeparatorList || insideAttribute) then
                            let span =
                                Range.mkRange fileName (Position.mkPos lineNumber blankStartedAt) semicolonEnd

                            {
                                Range = span
                                OriginalText = textOfRange source span
                                ReplacementText = ""
                            }
                    | _ -> ()
            ]

        suggestions
