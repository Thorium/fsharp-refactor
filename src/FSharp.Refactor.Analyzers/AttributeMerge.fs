/// Refactoring (style): consecutive attribute brackets merge into one.
///
///     [<Attr1>] [<Attr2>]        →  [<Attr1; Attr2>]
///     [<Attr1>]
///     [<Attr2>]                  →  [<Attr1; Attr2>]
///     let f () = ...                let f () = ...
///
/// Safety rules:
///   - only whitespace sits between the bracket groups (a comment would
///     be swallowed by the merge, so it suppresses the fix)
///   - no attribute carries a target (`[<assembly: ...>]` groups keep
///     their own brackets)
///
/// Covers attributes on let bindings, type definitions, union cases,
/// fields, and members.
module FSharp.Refactor.AttributeMerge

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// How many attributes may share one bracket. Four is about where a merged
/// line stops being a list you scan and starts being one you parse — but
/// that is a house-style call, not a correctness one, so a repository can
/// say otherwise:
///
///     { "FR0060": { "maxAttributes": 6, "wrapColumn": 120 } }
[<Literal>]
let DefaultMaxAttributes = 4

/// And where the line stops fitting, whatever the count. Overridden by the
/// `wrapColumn` knob above.
[<Literal>]
let DefaultWrapColumn = 110

/// Merge candidate from one declaration's attribute lists.
let private suggestionFor
    (maxMerged: int)
    (wrapColumn: int)
    (source: ISourceText)
    (attributeLists: SynAttributeList list)
    =
    if attributeLists.Length < 2 then
        None
    elif
        attributeLists
        |> List.exists (fun l -> l.Attributes |> List.exists (fun a -> a.Target.IsSome))
    then
        None
    else
        // only whitespace may separate the bracket groups
        let gapsClean =
            attributeLists
            |> List.pairwise
            |> List.forall (fun (a, b) ->
                let gap = Range.mkRange a.Range.FileName a.Range.End b.Range.Start

                (textOfRange source gap).Trim() = "")

        if not gapsClean then
            None
        else
            let first = List.head attributeLists
            let last = List.last attributeLists

            let span = Range.mkRange first.Range.FileName first.Range.Start last.Range.End

            let attributes = attributeLists |> List.collect (fun l -> l.Attributes)

            let merged =
                attributes
                |> List.map (fun a -> textOfRange source a.Range)
                |> String.concat "; "

            let replacement = $"[<{merged}>]"

            // one merged line stops helping somewhere. Past a handful the
            // list is no longer scannable, and past the wrap column it no
            // longer fits; either way the separate brackets read better, so
            // the rule stands down rather than inventing a wrapped layout
            if
                attributes.Length > maxMerged
                || first.Range.StartColumn + replacement.Length > wrapColumn
            then
                None
            else
                Some
                    {
                        Range = span
                        OriginalText = textOfRange source span
                        ReplacementText = replacement
                    }

/// Find declarations wearing more than one attribute bracket group.
let find (maxMerged: int) (wrapColumn: int) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    let ofBinding (SynBinding(attributes = attrs)) =
        suggestionFor maxMerged wrapColumn source attrs |> Option.iter suggestions.Add

    for _, decl in index.Decls do
        match decl with
        | SynModuleDecl.Let(bindings = bindings) -> bindings |> List.iter ofBinding
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeInfo = SynComponentInfo(attributes = typeAttrs); typeRepr = repr; members = extra) in
                defns do
                suggestionFor maxMerged wrapColumn source typeAttrs
                |> Option.iter suggestions.Add

                let members =
                    match repr with
                    | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                    | _ -> extra

                for m in members do
                    match m with
                    | SynMemberDefn.Member(memberDefn = binding) -> ofBinding binding
                    | SynMemberDefn.LetBindings(bindings = bindings) -> bindings |> List.iter ofBinding
                    | _ -> ()

                match repr with
                | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Union(unionCases = cases)) ->
                    for SynUnionCase(attributes = caseAttrs) in cases do
                        suggestionFor maxMerged wrapColumn source caseAttrs
                        |> Option.iter suggestions.Add
                | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Record(recordFields = fields)) ->
                    for SynField(attributes = fieldAttrs) in fields do
                        suggestionFor maxMerged wrapColumn source fieldAttrs
                        |> Option.iter suggestions.Add
                | _ -> ()
        | _ -> ()

    suggestions
    |> Seq.filter (fun s -> not (spansDirective source s.Range))
    |> List.ofSeq
