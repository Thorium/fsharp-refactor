/// Refactoring note (documentation): XML doc comments that document some
/// parameters but not all of them — the classic drift after a parameter
/// was added or renamed.
///
///     /// <summary>Scales a value.</summary>
///     /// <param name="value">The value.</param>
///     let scale (value: int) (factor: int) = ...   // factor undocumented
///
/// The compiler already warns (FS3390) about `<param>` tags naming a
/// NONEXISTENT parameter; the gap is the missing direction, so this note
/// fires when a binding has at least one `<param>` tag and a real
/// parameter has none. Fully undocumented functions are left alone —
/// whether to document at all is a style decision; drifting half-truths
/// are not.
module FSharp.Refactor.XmlDocParams

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Compiler.Xml
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// The undocumented parameter names, in order.
        MissingParams: string list
        /// The binding's name, for the message.
        BindingName: string
        /// The editor's offer: where to insert, and the `<param>` lines to
        /// insert there — one empty tag per missing parameter, after the
        /// comment's last `<param>` line, in its indentation. Empty tags
        /// are a scaffold for the author, so the CLI never writes them.
        Insertion: (range * string) option
    }

let private paramTagRegex =
    Regex("<param\\s+name\\s*=\\s*\"([^\"]*)\"", RegexOptions.Compiled)

/// The documented parameter names in a doc comment.
let private documentedParams (xmlDoc: PreXmlDoc) =
    // ToXmlDoc parses the comment; malformed XML comes back as failure
    let lines =
        try
            xmlDoc.ToXmlDoc(false, None).UnprocessedLines
        with
        | :? System.Xml.XmlException
        | OptionModule.FcsSymbolFailure -> [||]

    lines
    |> Array.collect (fun line ->
        paramTagRegex.Matches line
        |> Seq.map (fun m -> m.Groups.[1].Value)
        |> Seq.toArray)
    |> Set.ofArray

/// The binding's parameter names in declaration order (tuple elements
/// flattened; wildcards skipped).
let private parameterNames (headPat: SynPat) =
    match headPat with
    | SynPat.LongIdent(argPats = SynArgPats.Pats args) -> args |> List.collect patBoundNames
    | _ -> []

/// The insertion for the missing tags: the end of the comment's last
/// `<param>` line, and the new lines spelled with that line's prefix
/// (indentation and `///`).
let private insertionFor (source: ISourceText) (xmlDoc: PreXmlDoc) (missing: string list) =
    try
        let r = xmlDoc.ToXmlDoc(false, None).Range

        let lastParamLine =
            [ r.StartLine - 1 .. r.EndLine - 1 ]
            |> List.filter (fun l -> l >= 0 && l < source.GetLineCount())
            |> List.tryFindBack (fun l -> source.GetLineString(l).Contains "<param")

        lastParamLine
        |> Option.bind (fun l ->
            let text = source.GetLineString l
            let slashes = text.IndexOf "///"

            if slashes < 0 then
                None
            else
                let prefix = text.Substring(0, slashes + 3) + " "
                let at = Position.mkPos (l + 1) text.Length

                let lines =
                    missing
                    |> List.map (fun p -> $"\n{prefix}<param name=\"{p}\"></param>")
                    |> String.concat ""

                Some(Range.mkRange r.FileName at at, lines))
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

let private checkBinding
    (source: ISourceText)
    (suggestions: ResizeArray<Suggestion>)
    (SynBinding(headPat = headPat; xmlDoc = xmlDoc))
    =
    let documented = documentedParams xmlDoc

    if not documented.IsEmpty then
        let actual = parameterNames headPat

        let missing = actual |> List.filter (documented.Contains >> not)

        let name =
            match headPat with
            | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText
            | _ -> "?"

        if not (missing.IsEmpty || actual.IsEmpty) then
            suggestions.Add
                {
                    Range = headPat.Range
                    MissingParams = missing
                    BindingName = name
                    Insertion = insertionFor source xmlDoc missing
                }

/// Find bindings whose doc comments document only some parameters.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()
    let checkBinding = checkBinding source

    for _, decl in index.Decls do
        match decl with
        | SynModuleDecl.Let(bindings = bindings) -> bindings |> List.iter (checkBinding suggestions)
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeRepr = repr; members = extra) in defns do
                let members =
                    match repr with
                    | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                    | _ -> extra

                for m in members do
                    match m with
                    // a [<CustomOperation>] doc comment documents the DSL
                    // keyword, not the F# signature's parameters
                    | SynMemberDefn.Member(memberDefn = (SynBinding(attributes = attrs) as binding)) when
                        not (hasAttributeNamed "CustomOperation" attrs)
                        ->
                        checkBinding suggestions binding
                    | _ -> ()
        | _ -> ()

    List.ofSeq suggestions
