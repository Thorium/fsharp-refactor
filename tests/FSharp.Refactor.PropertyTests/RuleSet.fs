/// The parse-only rules under test: the same set CorpusValidation runs over
/// real repositories, run here over generated programs instead. A fix a
/// rule offers on a parse tree alone must keep the file parseable, and no
/// rule may throw on any tree the parser recovers into.
module FSharp.Refactor.PropertyTests.RuleSet

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor

type Edit =
    {
        Code: string
        Range: range
        Replacement: string
    }

let private edit (code: string) (range: range) (replacement: string) =
    {
        Code = code
        Range = range
        Replacement = replacement
    }

/// Every single-edit suggestion of every parse-only fix rule.
let singleEdits (tree: ParsedInput) (source: ISourceText) : Edit list =
    [
        for s in RedundantParens.find tree source -> edit "FR0013" s.Range s.ReplacementText
        for s in MethodCallParens.find tree source -> edit "FR0094" s.Range s.ReplacementText
        for s in LambdaBuiltin.find tree source -> edit "FR0095" s.Range s.ReplacementText
        for s in PatternParens.find tree source -> edit "FR0096" s.Range s.ReplacementText
        for s in TypeSyntax.findRedundantParens tree source -> edit "FR0097" s.Range s.ReplacementText
        for s in TypeSyntax.findAbbreviations tree source -> edit "FR0098" s.Range s.ReplacementText
        for s in TrailingSemicolon.find tree source -> edit "FR0099" s.Range s.ReplacementText
        for s in MatchToIf.find tree source -> edit "FR0001" s.Range s.ReplacementText
        for s in RaiseFailwith.find tree source -> edit "FR0024" s.Range s.ReplacementText
        for s in AttributeMerge.find AttributeMerge.DefaultMaxAttributes AttributeMerge.DefaultWrapColumn tree source ->
            edit "FR0060" s.Range s.ReplacementText
        for s in HintEngine.find [] tree source None -> edit "FR0011" s.Range s.ReplacementText
        for s in Simplification.find tree source None -> edit "FR0010" s.Range s.ReplacementText
        for s in ConversionMove.find tree source -> edit "FR0004" s.Range s.ReplacementText
        for s in StructDu.find (Visibility.apiChangesAllowed ()) tree source -> edit "FR0016" s.InsertRange s.InsertText
        for s in RedundantSyntax.find None tree source -> edit $"FR008x/{s.Kind}" s.Range s.ReplacementText
        for s in TypeTestChain.find tree source -> edit "FR0103" s.Range s.ReplacementText
        for s in BooleanSimplify.find tree source -> edit $"FR0108/{s.Kind}" s.Range s.ReplacementText
    ]

/// The rules whose edits apply as a set.
let multiEditSets (tree: ParsedInput) (source: ISourceText) : (string * Edit list) list =
    [
        for s in MatchBangRule.find tree source -> "FR0073", [ for r, _, t in s.Edits -> edit "FR0073" r t ]
        for s in MatchBangRule.findWhileBang tree source -> "FR0078", [ for r, _, t in s.Edits -> edit "FR0078" r t ]
        for s in IndexedLoop.find tree source -> "FR0101", [ for r, _, t in s.Edits -> edit "FR0101" r t ]
    ]

/// The note-only rules: nothing to patch, but they must run.
let notes (tree: ParsedInput) (source: ISourceText) : (string * range) list =
    let voptions, structs, structTuples =
        StructHints.find (Visibility.apiChangesAllowed ()) tree source

    [
        for s in voptions -> "FR0069", s.Range
        for s in structs -> "FR0070", s.Range
        for s in structTuples -> "FR0093", s.Range
        for s in PathSeparator.find tree source -> "FR0081", s.Range
        for s in DuFieldNames.find (Visibility.apiChangesAllowed ()) tree source -> "FR0022", s.Range
    ]

/// Apply one set of edits bottom-up, so earlier ranges stay valid.
let applyEdits (source: string) (edits: Edit list) : string =
    edits
    |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
    |> List.fold (fun acc e -> Tests.Parsing.applyEdit acc e.Range e.Replacement) source

/// The codes the generated programs are meant to reach.
let targetedCodes =
    [
        "FR0001"
        "FR0004"
        "FR0010"
        "FR0011"
        "FR0013"
        "FR0024"
        "FR0060"
        "FR0073"
        "FR0094"
        "FR0095"
        "FR0096"
        "FR0097"
        "FR0098"
        "FR0099"
        "FR0101"
        "FR0103"
        "FR0108/Identity"
        "FR0108/Duplicate"
        "FR008x/AttributeSuffix"
        "FR008x/AttributeParens"
        "FR008x/Backticks"
        "FR008x/HoleFreeInterpolation"
    ]
