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

open FsCheck
open FsCheck.FSharp
open FsCheck.Xunit
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private families = Families.All.all

/// At most this many fixes per program are run: a program with a dozen
/// fixes costs a dozen evaluations, and the tail of the list is rarely a
/// different rule from the head.
let private maxFixesPerProgram = 4

/// Is every edit inside the generated body? The log, `sink` and `trace`
/// are the measuring apparatus — a rule marking `trace` private would
/// break the run without saying anything about the rule.
let private insideBody (p: Effects.Program) (edits: Edit list) =
    edits
    |> List.forall (fun e -> e.Range.StartLine >= p.BodyStart && e.Range.EndLine <= p.BodyEnd)

let private describe (code: string, edits: Edit list) =
    let texts =
        edits
        |> List.map (fun e -> $"{Interpreter.rangeText e.Range} -> {e.Replacement}")

    $"{code}: " + String.concat " | " texts

[<Property(MaxTest = 50, EndSize = 30)>]
let ``a fix keeps what the program does`` () =
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
            ]
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
                        (describe (code, edits))
                        source
                        patched
                        e
                | Ok after when after <> before ->
                    failwithf
                        "%s CHANGES WHAT THE PROGRAM DOES:\n  before: %s\n  after:  %s\n--- before\n%s\n--- after\n%s"
                        (describe (code, edits))
                        before
                        after
                        source
                        patched
                | Ok _ -> ()

            Prop.classify (sets.Length >= 3) "3+ fixes" true)
