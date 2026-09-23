/// A fix keeps the program's BEHAVIOUR, not only its syntax.
///
/// The other properties ask whether a rewritten program still parses and
/// still typechecks. Both are necessary and neither is the promise a fix
/// rule makes: `let buf = [| a + 1 |]` hoisted out of its loop parses,
/// typechecks, and writes into one shared buffer where the original
/// allocated a fresh one per iteration. This property runs the program
/// before and after each fix and compares what it did — the general
/// oracle the boolean truth-table check is a special case of, and the one
/// that does not need a rule to be written for it.
///
/// A generated program traces its work through `sink`; two programs are
/// equivalent when their traces agree. Each fix is applied ALONE, so a
/// failure names the rule.
module FSharp.Refactor.PropertyTests.ExecutionTests

open Xunit
open FsCheck
open FsCheck.FSharp
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private families = Families.All.all

/// Each program's fixes are run, and an evaluation is the expensive part
/// (measured: 163 ms against 49 ms for the typecheck), so they are
/// capped — by RULE first and then in total.
///
/// Taking the first few outright would run one common rule over and over
/// and never reach the rare one: FR0007 fires five times as often as
/// FR0071 here, and it was FR0071 that was wrong. Capping after grouping
/// fixes that, but the cap still falls where the families are listed, so
/// the last families in `Families.All` would never be reached on a
/// program with many fixes; the list is rotated by the program's own tape
/// first, which spreads the cap over all of them and stays reproducible
/// from the seed.
[<Literal>]
let private maxPerRule = 2

[<Literal>]
let private maxFixesPerProgram = 8

/// A run-wide budget, because the fixes are wildly unevenly distributed:
/// over 1200 generated programs FR0007 and FR0131 accounted for 84% of
/// them, and every one of FR0131's 618 was the SAME rewrite — `[<TailCall>]`
/// on the same fixture function. Re-running an identical edit cannot find
/// anything, and a common rule crowding out a rare one is how FR0071's
/// hole survived. So: an edit whose text has already been checked is
/// skipped, and past the first few a rule is sampled rather than run
/// every time. Both are run-wide and evolve the same way on a replay, so
/// a failing seed still reproduces.
let private alreadyChecked = System.Collections.Generic.HashSet<string>()

let private timesRun = System.Collections.Generic.Dictionary<string, int>()

let private worthRunning (code: string) (edits: Edit list) =
    let key =
        code
        + " | "
        + (edits
           |> List.map (fun e -> $"{Interpreter.rangeText e.Range}=>{e.Replacement}")
           |> String.concat " ;; ")

    if not (alreadyChecked.Add key) then
        false
    else
        let n =
            match timesRun.TryGetValue code with
            | true, v -> v
            | _ -> 0

        timesRun.[code] <- n + 1
        n < 6 || n % 6 = 0

/// The few rules whose fix is MEANT to change what the program does, and
/// which this property would otherwise report as defects. FR0067 pins a
/// parse to the invariant culture, so a machine in another culture reads
/// the date differently on purpose; FR0121 moves a local clock reading to
/// UTC; FR0049 turns a blocking call into an awaited one. A rule belongs
/// here only when the change in behaviour IS the fix — never to quiet a
/// failure.
let private intentionallyChangesBehaviour = set [ "FR0049"; "FR0067"; "FR0121" ]

/// Rotate by an amount the program itself determines.
let private rotate (choices: int list) (xs: 'a list) =
    match xs with
    | []
    | [ _ ] -> xs
    | _ ->
        let sum = choices |> List.sumBy (fun c -> c % 97)
        let offset = ((sum % xs.Length) + xs.Length) % xs.Length
        List.skip offset xs @ List.take offset xs

/// Is every edit inside the generated body? The log, `sink` and `trace`
/// are the measuring apparatus — a rule marking `trace` private would
/// break the run without saying anything about the rule.
let private insideBody (p: Effects.Program) (edits: Edit list) =
    edits
    |> List.forall (fun e -> e.Range.StartLine >= p.BodyStart && e.Range.EndLine <= p.BodyEnd)

let private describe (code: string) (edits: Edit list) =
    let texts =
        edits
        |> List.map (fun e -> $"{Interpreter.rangeText e.Range} -> {e.Replacement}")

    $"{code}: " + String.concat " | " texts

/// How many programs a run draws. This is the slowest property in the
/// suite by an order of magnitude — a program costs a typecheck (49 ms)
/// and an evaluation for itself plus one per fix (163 ms each), so a run
/// is roughly 0.8 s a program — and it is the one property whose value
/// comes from VOLUME rather than from any single case. So the count is a
/// knob: small enough by default that running the suite locally stays
/// cheap, and set high in CI, where the wall clock is not a person's.
///
/// `[<Property(MaxTest = …)>]` takes a compile-time constant, which is why
/// this is a Fact driving FsCheck itself.
let private runs =
    match System.Environment.GetEnvironmentVariable "FSREF_EXECUTION_RUNS" with
    | null
    | "" -> 25
    | value ->
        match System.Int32.TryParse value with
        | true, n when n > 0 -> n
        | _ -> 25

// StartSize is high because a tiny program exercises nothing: the ramp
// from 1 that the other properties use would spend its first tests on
// programs of one statement.
[<Fact>]
let ``a fix keeps what the program does`` () =
    // QuickThrowOnFailure, not Quick: `Quick` PRINTS a falsified property
    // and returns, which would leave this test passing while the property
    // was false
    let configuration =
        Config.QuickThrowOnFailure.WithMaxTest(runs).WithStartSize(15).WithEndSize(32).WithQuietOnSuccess true

    Check.One(
        configuration,
        Prop.forAll Effects.arbitrary (fun choices ->
            let generated = Effects.program choices
            let source = generated.Source
            let checked' = Typed.check source

            if not checked'.Errors.IsEmpty then
                failwithf
                    "the generated program does not typecheck — the generator is wrong, not a rule:\n%s\n--- errors\n%s"
                    source
                    (String.concat "\n" checked'.Errors)

            let sets =
                [
                    for f in families do
                        for code, edits in f.Edits checked' do
                            if insideBody generated edits then
                                code, edits

                    // the parse-only fix rules, which want no typed results and
                    // so are not wired into any family: redundant parentheses,
                    // the hint engine, the boolean simplifications, the syntax
                    // cleanups. Generated code is full of what they rewrite.
                    let asEdit (e: RuleSet.Edit) =
                        {
                            Code = e.Code
                            Range = e.Range
                            Replacement = e.Replacement
                        }

                    for e in RuleSet.singleEdits checked'.Tree checked'.Source do
                        let edits = [ asEdit e ]

                        if insideBody generated edits then
                            e.Code, edits

                    for code, es in RuleSet.multiEditSets checked'.Tree checked'.Source do
                        let edits = es |> List.map asEdit

                        if insideBody generated edits then
                            code, edits
                ]
                |> List.groupBy fst
                |> rotate choices
                |> List.collect (snd >> List.truncate maxPerRule)
                |> List.filter (fun (code, edits) ->
                    not (intentionallyChangesBehaviour.Contains code) && worthRunning code edits)
                |> List.truncate maxFixesPerProgram

            if sets.IsEmpty then
                Prop.classify true "no fix" true
            else
                let before =
                    match Execution.trace source with
                    | Ok t -> t
                    | Error e -> failwithf "the generated program does not run:\n%s\n--- %s" source e

                for code, edits in sets do
                    let patched = applyEdits source edits

                    match Execution.trace patched with
                    | Error e ->
                        failwithf
                            "%s leaves a program that does not run:\n--- before\n%s\n--- after\n%s\n--- %s"
                            (describe code edits)
                            source
                            patched
                            e
                    | Ok after when after <> before ->
                        failwithf
                            "%s CHANGES WHAT THE PROGRAM DOES:\n  before: %s\n  after:  %s\n--- before\n%s\n--- after\n%s"
                            (describe code edits)
                            before
                            after
                            source
                            patched
                    | Ok _ -> ()

                Prop.classify (sets.Length >= 3) "3+ fixes" true)
    )
