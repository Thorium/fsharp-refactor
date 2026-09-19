/// The properties CorpusValidation checks over real repositories, over
/// generated programs instead: a rule never throws, and a parse-only fix
/// never leaves the file unparseable. Where the corpus run needs a
/// checkout and an environment variable, these run on every `dotnet test`.
module FSharp.Refactor.PropertyTests.RobustnessTests

open Xunit
open FsCheck.Xunit
open FsCheck
open FsCheck.FSharp
open FSharp.Refactor.Tests.Parsing
open FSharp.Refactor.PropertyTests

/// Every single edit and every edit set, each applied alone to `source`,
/// must leave it parseable.
let private checkEdits (source: string) =
    let tree, sourceText = parse source

    for e in RuleSet.singleEdits tree sourceText do
        let patched = applyEdit source e.Range e.Replacement

        if not (parsesCleanly patched) then
            failwithf
                "%s at %s -> %s breaks the parse:\n--- before\n%s\n--- after\n%s"
                e.Code
                (Interpreter.rangeText e.Range)
                e.Replacement
                source
                patched

    for code, edits in RuleSet.multiEditSets tree sourceText do
        let patched = RuleSet.applyEdits source edits

        if not (parsesCleanly patched) then
            failwithf "%s (%d edits) breaks the parse:\n--- before\n%s\n--- after\n%s" code edits.Length source patched

    RuleSet.notes tree sourceText |> ignore

[<Property(MaxTest = 200, EndSize = 40)>]
let ``a generated program parses, and every parse-only fix keeps it parseable`` () =
    Prop.forAll Programs.arbitrary (Programs.program >> checkEdits)

[<Property(MaxTest = 500, EndSize = 40)>]
let ``no rule throws on a damaged program, and fixes on a still-parseable one keep it parseable`` () =
    Prop.forAll (Arb.zip (Programs.arbitrary, Arb.fromGen Mutation.genMutations)) (fun (shapes, mutations) ->
        let damaged = Mutation.applyAll (Programs.program shapes) mutations
        let tree, hadErrors, sourceText = tryParseNamed "Test.fs" damaged

        try
            if hadErrors then
                // a partial tree: the rules must survive it, nothing more
                RuleSet.singleEdits tree sourceText |> ignore
                RuleSet.multiEditSets tree sourceText |> ignore
                RuleSet.notes tree sourceText |> ignore
            else
                checkEdits damaged
        with ex when hadErrors ->
            printfn "a rule threw on a recovered tree: %s\n--- source\n%s" (string ex) damaged
            reraise ())

/// The generators exist to reach the rules: if a shape stops firing its
/// rule (a rule tightened, a shape drifted), this says which.
[<Fact>]
let ``every targeted rule fires somewhere in a sample of programs`` () =
    let fired = System.Collections.Generic.HashSet<string>()

    for shapes in Gen.sampleWithSize 40 300 Programs.genProgram do
        let source = Programs.program shapes
        let tree, sourceText = parse source

        for e in RuleSet.singleEdits tree sourceText do
            fired.Add e.Code |> ignore

        for code, _ in RuleSet.multiEditSets tree sourceText do
            fired.Add code |> ignore

    let missing = RuleSet.targetedCodes |> List.filter (fired.Contains >> not)
    Assert.True(missing.IsEmpty, $"rules the generated programs never reached: %A{missing}")
