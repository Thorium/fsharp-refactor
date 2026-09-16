/// FR0135 (fix): a multi-line `(* ... *)` block comment in an .fsx script
/// that clearly carries MARKDOWN — a ``` code fence, or a `###` heading —
/// is almost certainly meant as a literate cell; one star turns it into
/// one:
///
///     (*                          (**
///     ### Setup                   ### Setup
///     ```fsharp          →        ```fsharp
///     let x = 1                   let x = 1
///     ```                         ```
///     *)                          *)
///
/// FSharp.Formatting renders `(** ... *)` as a markdown cell and treats
/// `(* ... *)` as an ignored comment — the markdown is silently dropped
/// from the generated docs. The compiler sees no difference, so the edit
/// is inert outside literate tooling. Scripts only (.fsx); existing
/// `(**` cells and `(*** command ***)` cells are left alone.
module FSharp.Refactor.LiterateComment

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// What marked it as markdown, for the message.
        Evidence: string
        /// Zero-width insert of `*` after the opening `(*`.
        Fix: range * string
    }

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    if not (parseTree.FileName.EndsWith(".fsx", System.StringComparison.OrdinalIgnoreCase)) then
        []
    else
        commentsWithText parseTree source
        |> List.choose (fun (r, text) ->
            if
                r.StartLine < r.EndLine
                && text.StartsWith "(*"
                && not (text.StartsWith "(**")
                // a comment must OPEN its line to be a cell
                && (r.StartColumn = 0
                    || (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = "")
            then
                let lines = text.Split '\n' |> Array.map (fun l -> l.Trim())

                let evidence =
                    if lines |> Array.exists (fun l -> l.StartsWith "```") then
                        Some "a ``` code fence"
                    elif lines |> Array.exists (fun l -> l.StartsWith "###") then
                        Some "a ### heading"
                    else
                        None

                evidence
                |> Option.map (fun ev ->
                    let at = Position.mkPos r.StartLine (r.StartColumn + 2)

                    {
                        Range = r
                        Evidence = ev
                        Fix = Range.mkRange r.FileName at at, "*"
                    })
            else
                None)
