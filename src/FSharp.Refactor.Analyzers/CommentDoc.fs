/// FR0132 (fix): a PUBLIC declaration with no XML doc but a trailing
/// same-line comment gets that comment promoted to the doc position:
///
///     let interestRate r n = r * n   // monthly, non-compounding
///                        →
///     /// monthly, non-compounding
///     let interestRate r n = r * n
///
/// Same for type definitions and union cases. The comment's text is worth
/// the same either way — but only the `///` position reaches tooltips,
/// generated docs and editor hovers. Public declarations only: that is
/// where the doc surfaces; a private helper's trailing note is fine where
/// it sits.
///
/// The insert spells the moved comment as `/` + the original text, so the
/// replacement provably CONTAINS the deleted comment — the comment-loss
/// guards then pass by construction.
module FSharp.Refactor.CommentDoc

open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        What: string
        /// Delete the trailing comment; insert it as `///` above.
        Edits: (range * string * string) list
    }

/// Comments that are instructions, not documentation — and comments a
/// doc position cannot carry verbatim: `<` and `&` are XML syntax, and
/// promoting `// true when a < b` unescaped draws FS3390 on every build.
/// (Escaping would break the contains-the-original comment-loss proof.)
///
/// Beyond instructions, a trailing note must READ as a summary before it
/// becomes one. suave's `// ^ Index is out of range`, `// -- node no.`
/// and `// unused` were promoted verbatim: a Haskell-style marker, a
/// single word, or a note too short to document anything is a margin
/// annotation, and a doc line made of it is worse than none.
let private excluded (text: string) =
    let body = (text.TrimStart '/').Trim()

    body = ""
    || body.StartsWith "fsharpanalyzer"
    || body.StartsWith "TODO"
    || body.StartsWith "FIXME"
    || body.StartsWith "HACK"
    || body.Contains '<'
    || body.Contains '&'
    // a punctuation marker opens an annotation, not a sentence
    || "^-|*!".Contains body.[0]
    // a single word (`unused`, `todo`) or fewer than 12 characters
    || not (body.Contains ' ')
    || body.Length < 12

/// A test file's public declarations are fixtures, not an API: the
/// trailing note on `let emojiParty = "\U0001F389" // 🎉 PARTY POPPER`
/// labels the fixture and documents nothing. The shared answer
/// (AstIndex.isTestFile): a test framework's `open`, a test attribute,
/// or an Expecto test builder.
let private isTestFile = AstIndex.isTestFile

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // plain line comments only — /// doc comments live in PreXmlDoc, and
    // (* *) blocks read as prose mid-line, not as a note about the decl
    let comments =
        if isTestFile index source then
            []
        else
            commentsWithText parseTree source
            |> List.filter (fun (_, t) -> t.StartsWith "//" && not (t.StartsWith "///") && not (excluded t))

    // the promotion for one declaration header, if its line qualifies —
    // a union case's anchor sits after its `|`, which may open the line
    let promote (what: string) (anchor: range) (headerEndLine: int) =
        let headerLine = source.GetLineString(anchor.StartLine - 1)
        let beforeAnchor = headerLine.Substring(0, anchor.StartColumn).Trim()

        if beforeAnchor = "" || beforeAnchor = "|" then
            comments
            |> List.tryPick (fun (cr, ctext) ->
                let lineText = source.GetLineString(cr.StartLine - 1)

                if
                    cr.StartLine = headerEndLine
                    && cr.StartLine >= anchor.StartLine
                    // the comment must END its line — anything after it is
                    // not a trailing note
                    && lineText.Substring(cr.EndColumn).Trim() = ""
                    // and real code must precede it on the line
                    && lineText.Substring(0, cr.StartColumn).Trim() <> ""
                then
                    let codeEnd = (lineText.Substring(0, cr.StartColumn)).TrimEnd().Length

                    let indent =
                        String.replicate (headerLine.Length - headerLine.TrimStart().Length) " "

                    let deleteRange =
                        Range.mkRange
                            anchor.FileName
                            (Position.mkPos cr.StartLine codeEnd)
                            (Position.mkPos cr.StartLine cr.EndColumn)

                    let insertAt =
                        Range.mkRange
                            anchor.FileName
                            (Position.mkPos anchor.StartLine 0)
                            (Position.mkPos anchor.StartLine 0)

                    Some
                        { Range = cr
                          What = what
                          Edits =
                            [ deleteRange, textOfRange source deleteRange, ""
                              insertAt, "", $"{indent}/{ctext}\n" ] }
                else
                    None)
        else
            None

    let valueAccess (p: SynPat) =
        match p with
        | SynPat.Named(accessibility = acc)
        | SynPat.LongIdent(accessibility = acc) -> acc
        | _ -> None

    [ if not comments.IsEmpty then
          for path, decl in index.Decls do
              match decl with
              // attributes = []: the insert lands at the keyword line, and a
              // /// between an attribute line and its declaration draws the
              // FS3520 misplaced-doc warning
              | SynModuleDecl.Let(
                  bindings = [ SynBinding(
                                   xmlDoc = xd; attributes = []; accessibility = acc; headPat = pat; trivia = btrivia) ]) when
                  xd.IsEmpty && not (Visibility.isConfined path [ acc; valueAccess pat ])
                  ->
                  // the comment sits at the end of the HEADER line — the
                  // line the `let` keyword starts
                  match promote "binding" btrivia.LeadingKeyword.Range btrivia.LeadingKeyword.Range.StartLine with
                  | Some s -> s
                  | None -> ()
              | SynModuleDecl.Types(typeDefns = defns) ->
                  for SynTypeDefn(typeInfo = info; typeRepr = repr; trivia = ttrivia) in defns do
                      let (SynComponentInfo(xmlDoc = xd; attributes = tattrs; accessibility = acc)) = info

                      match ttrivia.LeadingKeyword with
                      | SynTypeDefnLeadingKeyword.Type kwRange when
                          xd.IsEmpty && tattrs.IsEmpty && not (Visibility.isConfined path [ acc ])
                          ->
                          match promote "type" kwRange kwRange.StartLine with
                          | Some s -> s
                          | None -> ()
                      | _ -> ()

                      // union cases carry their own doc position
                      match repr with
                      | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Union(unionCases = cases)) when
                          not (Visibility.isConfined path [ acc ])
                          ->
                          for SynUnionCase(xmlDoc = cxd; attributes = cattrs) as case in cases do
                              if cxd.IsEmpty && cattrs.IsEmpty then
                                  match promote "union case" case.Range case.Range.EndLine with
                                  | Some s -> s
                                  | None -> ()
                      | _ -> ()
              | _ -> () ]
