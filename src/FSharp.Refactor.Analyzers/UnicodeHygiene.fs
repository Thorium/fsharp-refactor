/// FR0125: invisible and bidirectional Unicode in source.
///
/// Three families, none of which survives honest code review because
/// none of them can be SEEN:
///
///   - bidi controls (U+202A-202E, U+2066-2069): Trojan Source
///     (CVE-2021-42574) — code that reads one way and compiles another
///   - Unicode tag block (U+E0001, U+E0020-E007F): invisible characters
///     that survive into LLM prompts — the prompt-injection smuggling
///     channel SonarQube's agentic rules flag
///   - zero-width/invisible spaces (U+200B, U+2060-2064, mid-file
///     U+FEFF): identifiers and literals that differ while looking
///     identical
///
/// ZWJ/ZWNJ (U+200D/U+200C) are deliberately NOT flagged: emoji
/// sequences and Persian/Arabic text use them legitimately.
///
/// Inside a REGULAR string literal the fix rewrites the character as
/// its \uXXXX escape — same string, now visible. Everywhere else
/// (comments, identifiers, verbatim/triple-quoted strings where escapes
/// do not exist) it stays a note: whether the character belongs is
/// exactly the question.
module FSharp.Refactor.UnicodeHygiene

open System.Text
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

type Suggestion =
    {
        Range: range
        /// U+XXXX display form.
        CodePoint: string
        FamilyName: string
        /// Present when the character sits in a regular string literal:
        /// the escape spelling.
        Fix: (range * string * string) option
    }

let private bidi =
    set [ 0x202A; 0x202B; 0x202C; 0x202D; 0x202E; 0x2066; 0x2067; 0x2068; 0x2069 ]

let private invisible = set [ 0x200B; 0x2060; 0x2061; 0x2062; 0x2063; 0x2064 ]

let private familyOf (cp: int) (line: int) (col: int) =
    if bidi.Contains cp then
        ValueSome "bidirectional control (Trojan Source)"
    elif invisible.Contains cp then
        ValueSome "zero-width/invisible"
    elif cp = 0xFEFF && (line > 1 || col > 0) then
        ValueSome "mid-file byte-order mark"
    elif cp = 0xE0001 || (cp >= 0xE0020 && cp <= 0xE007F) then
        ValueSome "Unicode tag block (invisible smuggling)"
    else
        ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // regular string literals, where \uXXXX escapes exist
    let regularLiterals =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.Const(SynConst.String(_, SynStringKind.Regular, _), r) -> Some r
            | _ -> None)

    let inRegularLiteral (r: range) =
        regularLiterals |> Array.exists (fun lit -> Range.rangeContainsRange lit r)

    [
        for lineIx in 0 .. source.GetLineCount() - 1 do
            let line = source.GetLineString lineIx
            let mutable col = 0

            for rune in line.EnumerateRunes() do
                let width = rune.Utf16SequenceLength

                match familyOf rune.Value (lineIx + 1) col with
                | ValueSome family ->
                    let r =
                        Range.mkRange
                            parseTree.FileName
                            (Position.mkPos (lineIx + 1) col)
                            (Position.mkPos (lineIx + 1) (col + width))

                    let display =
                        if rune.Value <= 0xFFFF then
                            $"U+%04X{rune.Value}"
                        else
                            $"U+%06X{rune.Value}"

                    let escape =
                        if rune.Value <= 0xFFFF then
                            $"\\u%04X{rune.Value}"
                        else
                            $"\\U%08X{rune.Value}"

                    {
                        Range = r
                        CodePoint = display
                        FamilyName = family
                        Fix =
                            if inRegularLiteral r then
                                Some(r, line.Substring(col, width), escape)
                            else
                                None
                    }
                | ValueNone -> ()

                col <- col + width
    ]
