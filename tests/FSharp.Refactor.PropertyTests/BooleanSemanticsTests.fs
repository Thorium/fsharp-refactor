/// The boolean rewrites preserve meaning. A generated term is printed as a
/// function of three integers; the rules are applied one edit at a time
/// until none is left; after every edit the program must still parse and
/// must still compute what the original term computes, at every point of
/// the environment grid. And the process must stop: a rewrite that undoes
/// another would loop here.
module FSharp.Refactor.PropertyTests.BooleanSemanticsTests

open FsCheck.Xunit
open FsCheck
open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.BoolExpr

/// The rules that rewrite a boolean term: identities and duplicates, the
/// hint engine's negation and De Morgan rules, the `if c then true else
/// false` collapse, and the parentheses cleanup.
let private edits (source: string) : RuleSet.Edit list =
    let tree, sourceText = parse source

    [
        for s in BooleanSimplify.find tree sourceText ->
            {
                Code = $"FR0108/{s.Kind}"
                Range = s.Range
                Replacement = s.ReplacementText
            }
        for s in HintEngine.find [] tree sourceText None ->
            {
                Code = $"FR0012 {s.Rule}"
                Range = s.Range
                Replacement = s.ReplacementText
            }
        for s in Simplification.find tree sourceText None ->
            {
                Code = "FR0010"
                Range = s.Range
                Replacement = s.ReplacementText
            }
        for s in RedundantParens.find tree sourceText ->
            {
                Code = "FR0013"
                Range = s.Range
                Replacement = s.ReplacementText
            }
    ]

/// The program's function evaluated over the whole grid.
let private truthTable (source: string) : bool list =
    let tree, _ = parse source
    envs |> List.map (Interpreter.run tree)

/// Apply the first edit (by position), re-parse, compare; repeat to a
/// fixed point. Returns how many edits it took.
let private rewriteToFixedPoint (term: BoolExpr) : int =
    let expected = envs |> List.map (fun env -> eval env term)
    let bound = 4 * sizeOf term + 8

    let rec loop (source: string) (steps: int) (trail: string list) =
        match edits source |> List.sortBy (fun e -> e.Range.StartLine, e.Range.StartColumn) with
        | [] -> steps
        | first :: _ ->
            if steps >= bound then
                failwithf
                    "no fixed point after %d edits (term size %d); the trail:\n%s"
                    steps
                    (sizeOf term)
                    (String.concat "\n---\n" (List.rev trail))

            let patched = applyEdit source first.Range first.Replacement

            if not (parsesCleanly patched) then
                failwithf
                    "%s at %s -> %s breaks the parse:\n--- before\n%s\n--- after\n%s"
                    first.Code
                    (Interpreter.rangeText first.Range)
                    first.Replacement
                    source
                    patched

            let actual = truthTable patched

            if actual <> expected then
                let differing =
                    List.zip3 envs expected actual
                    |> List.filter (fun (_, e, a) -> e <> a)
                    |> List.map (fun (env, e, a) -> $"x0={env.[0]} x1={env.[1]} x2={env.[2]}: expected {e}, got {a}")

                failwithf
                    "%s at %s -> %s changes the value:\n--- before\n%s\n--- after\n%s\n--- at\n%s"
                    first.Code
                    (Interpreter.rangeText first.Range)
                    first.Replacement
                    source
                    patched
                    (String.concat "\n" differing)

            loop patched (steps + 1) ($"{first.Code}: {first.Replacement}" :: trail)

    loop (program term) 0 []

[<Property(MaxTest = 1000, EndSize = 60)>]
let ``the boolean rewrites keep the function's truth table and reach a fixed point`` () =
    Prop.forAll BoolExpr.arbitrary (fun term ->
        let steps = rewriteToFixedPoint term

        // the distribution says whether the generator still reaches the
        // rules: a run where nothing ever fires proves nothing
        Prop.classify (steps = 0) "no rewrite" (Prop.classify (steps >= 3) "3+ rewrites" true))

[<Property(MaxTest = 200, EndSize = 60)>]
let ``the printed term computes what the term computes`` () =
    // the oracle and the interpreter agree BEFORE any rule runs: a
    // disagreement here is a test bug, not a rule bug
    Prop.forAll BoolExpr.arbitrary (fun term ->
        let expected = envs |> List.map (fun env -> eval env term)
        let actual = truthTable (program term)
        expected = actual)
