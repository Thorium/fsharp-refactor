/// Refactoring (paste repair): F# forbids TAB characters as whitespace
/// (FS1161), so code pasted from tab-indented sources does not even parse.
/// The fix expands every leading TAB to four spaces, line by line, which
/// usually restores the intended offside structure in one step.
///
/// Works from the SOURCE TEXT alone — the file may not parse, which is
/// the point (like FR0077, this rule repairs broken code).
///
/// Safety rules:
///   - only LEADING whitespace is touched; a tab after code could be
///     inside a string literal
///   - a file containing triple-quoted (""") or verbatim (@") strings is
///     skipped entirely: their literals span lines, so even a leading tab
///     can be string CONTENT there
///   - a line that OPENS inside a block comment `(* ... *)` (the literate
///     `(** ... *)` included) or inside a plain string literal is left
///     alone: a tab there is prose or content, not indentation, and the
///     compiler never sees it as FS1161. Fantomas's
///     docs/end-users/GettingStarted.fsx keeps a tab-indented
///     `dotnet new tool-manifest` shell transcript inside `(** ... *)`.
module FSharp.Refactor.TabIndentation

open FSharp.Compiler.Text

type Suggestion =
    {
        /// The first offending line's leading whitespace (message anchor).
        Range: range
        /// One edit per tab-indented line: (range, original, replacement).
        Edits: (range * string * string) list
    }

/// Expand tabs in a leading-whitespace segment: each tab becomes four
/// spaces, existing spaces pass through.
let private expand (leading: string) = leading.Replace("\t", "    ")

/// Lexical state at a character boundary — enough of F#'s lexer to know
/// whether the start of a line is code.
[<RequireQualifiedAccess>]
type private Lex =
    | Code
    | LineComment
    /// Block comments nest: `(* (* *) *)` is one comment.
    | BlockComment of depth: int
    | String

/// For every line, does its FIRST column sit inside a block comment or a
/// string literal? Scans the whole text once; `(*)` is the multiplication
/// operator, not a comment opener, and a `//` line comment hides any
/// quote to its right.
let private lineOpensInsideCommentOrString (source: ISourceText) : bool[] =
    let lineCount = source.GetLineCount()
    let inside = Array.zeroCreate<bool> lineCount
    let mutable state = Lex.Code

    for i in 0 .. lineCount - 1 do
        inside.[i] <-
            (match state with
             | Lex.BlockComment _
             | Lex.String -> true
             | Lex.Code
             | Lex.LineComment -> false)

        let line = source.GetLineString i
        let n = line.Length

        // a line comment ends with its line
        if state = Lex.LineComment then
            state <- Lex.Code

        let mutable j = 0

        while j < n do
            let c = line.[j]
            let next = if j + 1 < n then line.[j + 1] else '\000'

            match state with
            | Lex.Code ->
                if c = '(' && next = '*' && not (j + 2 < n && line.[j + 2] = ')') then
                    state <- Lex.BlockComment 1
                    j <- j + 2
                elif c = '/' && next = '/' then
                    state <- Lex.LineComment
                    j <- n
                elif c = '"' then
                    state <- Lex.String
                    j <- j + 1
                elif c = '\'' then
                    // a char literal (`'"'`, `'\n'`) must not open a string;
                    // a type variable `'a` is one apostrophe and moves on
                    if next = '\\' then
                        let close = line.IndexOf('\'', j + 2)
                        j <- if close > 0 && close - j <= 6 then close + 1 else j + 1
                    elif j + 2 < n && line.[j + 2] = '\'' then
                        j <- j + 3
                    else
                        j <- j + 1
                else
                    j <- j + 1
            | Lex.LineComment -> j <- n
            | Lex.BlockComment depth ->
                if c = '(' && next = '*' then
                    state <- Lex.BlockComment(depth + 1)
                    j <- j + 2
                elif c = '*' && next = ')' then
                    state <- (if depth = 1 then Lex.Code else Lex.BlockComment(depth - 1))
                    j <- j + 2
                else
                    j <- j + 1
            | Lex.String ->
                if c = '\\' then
                    j <- j + 2
                elif c = '"' then
                    state <- Lex.Code
                    j <- j + 1
                else
                    j <- j + 1

    inside

let find (fileName: string) (source: ISourceText) : Suggestion list =
    let lineCount = source.GetLineCount()

    // multiline string literals could own a leading tab as content
    let mutable hasMultilineStrings = false

    for i in 0 .. lineCount - 1 do
        let line = source.GetLineString i

        if line.Contains "\"\"\"" || line.Contains "@\"" then
            hasMultilineStrings <- true

    if hasMultilineStrings then
        []
    else
        let insideCommentOrString = lineOpensInsideCommentOrString source

        let edits =
            [ for i in 0 .. lineCount - 1 do
                  let line = source.GetLineString i
                  let leadingLen = line.Length - line.TrimStart().Length
                  let leading = line.Substring(0, leadingLen)

                  if leading.Contains '\t' && not insideCommentOrString.[i] then
                      let range =
                          Range.mkRange fileName (Position.mkPos (i + 1) 0) (Position.mkPos (i + 1) leadingLen)

                      range, leading, expand leading ]

        match edits with
        | [] -> []
        | (firstRange, _, _) :: _ -> [ { Range = firstRange; Edits = edits } ]
