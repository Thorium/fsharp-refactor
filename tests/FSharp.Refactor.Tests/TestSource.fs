/// Test sources written as indented triple-quoted blocks, so a snippet
/// reads as code beside the test instead of one long escaped line:
///
///     let source =
///         fsharp """
///             module M
///             let f x = x + 1
///             """
///
/// The line break after the opening quotes goes, the closing quotes'
/// indentation is cut from every line - the analyzer still sees the snippet
/// at column 0 - and CRLF (a CRLF test file embeds it) becomes LF. The
/// value is exactly the text between the quotes as written, dedented: a
/// blank line inside stays, and a trailing newline is a blank line before
/// the closing quotes. A line indented less than the closing quotes is a
/// mistake in the test, reported rather than guessed at.
///
/// Auto-opened from the root namespace, so every test file sees it; the
/// property tests link this file too.
[<AutoOpen>]
module TestSource

let private dedent (helper: string) (block: string) : string =
    let lines = block.Replace("\r\n", "\n").Split '\n'

    if lines.Length < 2 || lines.[0] <> "" || lines.[lines.Length - 1].Trim() <> "" then
        invalidArg
            "block"
            $"{helper}: write the snippet on the lines between the quotes, the closing quotes on a line of their own"

    let indent = lines.[lines.Length - 1].Length

    lines.[1 .. lines.Length - 2]
    |> Array.map (fun line ->
        if line.Length >= indent && line.Substring(0, indent).Trim() = "" then
            line.Substring indent
        elif line.Trim() = "" then
            ""
        else
            invalidArg "block" $"{helper}: a line is indented less than the closing quotes: {line}")
    |> String.concat "\n"

/// An F# snippet written as an indented `"""` block (see the module).
let fsharp (block: string) : string = dedent "fsharp" block
