/// Fixes compose: applying the parse-only rules' edits one at a time to a
/// generated program terminates, with the program parseable at every step.
/// A rule whose fix re-creates another rule's trigger (or its own) would
/// cycle here — the sweep's idempotency, checked in the small.
module FSharp.Refactor.PropertyTests.FixTests

open FsCheck.Xunit
open FsCheck
open FsCheck.FSharp
open FSharp.Refactor.Tests.Parsing
open FSharp.Refactor.PropertyTests

/// One edit — the first single edit by position, else the first edit set.
let private nextEdits (source: string) : (string * RuleSet.Edit list) option =
    let tree, sourceText = parse source

    match
        RuleSet.singleEdits tree sourceText
        |> List.sortBy (fun e -> e.Range.StartLine, e.Range.StartColumn)
    with
    | first :: _ -> Some(first.Code, [ first ])
    | [] ->
        match RuleSet.multiEditSets tree sourceText with
        | (code, edits) :: _ -> Some(code, edits)
        | [] -> None

[<Property(MaxTest = 150, EndSize = 40)>]
let ``applying fixes one at a time reaches a fixed point, parseable throughout`` () =
    Prop.forAll Programs.arbitrary (fun shapes ->
        let original = Programs.program shapes
        // every declaration fires a handful of rules at most; a term's
        // rewrites are bounded by its size
        let bound = 12 * shapes.Length + 8

        let rec loop (source: string) (steps: int) (trail: string list) =
            match nextEdits source with
            | None -> steps
            | Some(code, edits) ->
                if steps >= bound then
                    failwithf
                        "no fixed point after %d edits; the trail:\n%s\n--- original\n%s\n--- current\n%s"
                        steps
                        (String.concat "\n" (List.rev trail))
                        original
                        source

                let patched = RuleSet.applyEdits source edits

                if not (parsesCleanly patched) then
                    failwithf "%s breaks the parse:\n--- before\n%s\n--- after\n%s" code source patched

                let replacements = edits |> List.map _.Replacement |> String.concat " | "
                loop patched (steps + 1) ($"{code}: {replacements}" :: trail)

        let steps = loop original 0 []
        Prop.classify (steps = 0) "no rewrite" (Prop.classify (steps >= 5) "5+ rewrites" true))
