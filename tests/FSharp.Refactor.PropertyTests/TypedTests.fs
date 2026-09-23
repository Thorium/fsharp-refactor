/// The properties every rule family promises, over generated programs
/// that typecheck: a generator emits only programs the compiler accepts
/// (a rule's answer on a broken program means nothing); each fix, applied
/// alone, keeps the program parseable; all the fixes that do not overlap,
/// applied together, keep it typechecking; and no rule throws on a program
/// damaged mid-keystroke. The coverage test holds every shape to the rule
/// it was written for.
module FSharp.Refactor.PropertyTests.TypedTests

open System.Collections.Generic
open Xunit
open FsCheck
open FsCheck.FSharp
open FsCheck.Xunit
open FSharp.Compiler.Text
open FSharp.Refactor.Tests.Parsing
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private families = Families.All.all

/// Every fix of every family: the family, the code and the edit set.
let private fixes (c: Typed.Checked) : (string * string * Edit list) list =
    [
        for f in families do
            for code, edits in f.Edits c -> f.Name, code, edits
    ]

let private notes (c: Typed.Checked) : (string * string * range) list =
    [
        for f in families do
            for code, r in f.Notes c -> f.Name, code, r
    ]

let private startOf (edits: Edit list) =
    edits |> List.map (fun e -> e.Range.StartLine, e.Range.StartColumn) |> List.min

let private endOf (edits: Edit list) =
    edits |> List.map (fun e -> e.Range.EndLine, e.Range.EndColumn) |> List.max

/// Two edit sets touch the same text, or meet at one point: two
/// insertions at the same position are alternatives (`private ` and
/// `internal ` before one name), not a pair to apply together, and an
/// edit ending where another begins is close enough to count.
let private overlap (a: Edit list) (b: Edit list) =
    a
    |> List.exists (fun x ->
        b
        |> List.exists (fun y ->
            let xs, xe =
                (x.Range.StartLine, x.Range.StartColumn), (x.Range.EndLine, x.Range.EndColumn)

            let ys, ye =
                (y.Range.StartLine, y.Range.StartColumn), (y.Range.EndLine, y.Range.EndColumn)

            xs <= ye && ys <= xe))

/// The fixes in position order, each kept only when it overlaps none kept
/// before it: the largest set the properties can apply in one go.
let private disjoint (sets: (string * string * Edit list) list) =
    sets
    |> List.sortBy (fun (_, _, edits) -> startOf edits, endOf edits)
    |> List.fold
        (fun kept (family, code, edits) ->
            if kept |> List.exists (fun (_, _, k) -> overlap k edits) then
                kept
            else
                kept @ [ family, code, edits ])
        []

let private describe (family: string, code: string, edits: Edit list) =
    let texts =
        edits
        |> List.map (fun e -> $"{Interpreter.rangeText e.Range} -> {e.Replacement}")

    $"{code} ({family}): " + String.concat " | " texts

[<Property(MaxTest = 60, EndSize = 32)>]
let ``a generated program typechecks, each fix alone keeps it parseable, and the disjoint fixes together keep it typechecking``
    ()
    =
    Prop.forAll (arbitrary families) (fun shapes ->
        let source = program shapes
        let checked' = Typed.check source

        if not checked'.Errors.IsEmpty then
            failwithf
                "the generated program does not typecheck — a shape is wrong, not a rule:\n%s\n--- errors\n%s"
                source
                (String.concat "\n" checked'.Errors)

        let sets = fixes checked'

        for family, code, edits in sets do
            let patched = applyEdits source edits

            if not (parsesCleanly patched) then
                failwithf
                    "%s breaks the parse:\n--- before\n%s\n--- after\n%s"
                    (describe (family, code, edits))
                    source
                    patched

        notes checked' |> ignore

        let chosen = disjoint sets

        if not chosen.IsEmpty then
            let combined =
                applyEdits source (chosen |> List.collect (fun (_, _, edits) -> edits))

            let after = Typed.check combined

            if not after.Errors.IsEmpty then
                // which fix did it: each chosen set alone, then the rest is interaction
                let culprits =
                    chosen
                    |> List.filter (fun (_, _, edits) -> not (Typed.check (applyEdits source edits)).Errors.IsEmpty)

                let blame =
                    match culprits with
                    | [] -> "every fix typechecks alone; together they do not"
                    | some ->
                        "alone, these already fail:\n"
                        + (some |> List.map describe |> String.concat "\n")

                failwithf
                    "the fixes leave a program that does not typecheck.\n%s\n--- applied\n%s\n--- before\n%s\n--- after\n%s\n--- errors\n%s"
                    blame
                    (chosen |> List.map describe |> String.concat "\n")
                    source
                    combined
                    (String.concat "\n" after.Errors)

        Prop.classify sets.IsEmpty "no fix" (Prop.classify (sets.Length >= 5) "5+ fixes" true))

[<Property(MaxTest = 60, EndSize = 32)>]
let ``no rule throws on a damaged program`` () =
    Prop.forAll (Arb.zip (arbitrary families, Arb.fromGen Mutation.genMutations)) (fun (shapes, mutations) ->
        let damaged = Mutation.applyAll (program shapes) mutations
        let checked' = Typed.check damaged

        try
            fixes checked' |> ignore
            notes checked' |> ignore
        with ex ->
            printfn "a rule threw on a damaged program: %s\n--- source\n%s" (string ex) damaged
            reraise ())

/// The shapes exist to reach the rules: each shape, alone in a program of
/// its own, must be found by its family under every code it names — alone,
/// so a sibling shape with the same code cannot stand in for one that has
/// stopped firing. When a rule tightens or a shape drifts, this says which.
[<Fact>]
let ``every shape reaches the rule it was written for`` () =
    let missing = List<string>()

    for family in families do
        for gen in family.Shapes do
            let shape = Gen.sampleWithSize 20 1 gen |> Array.head
            let source = program [ shape ]
            let checked' = Typed.check source

            if not checked'.Errors.IsEmpty then
                failwithf
                    "%s/%s: the shape does not typecheck:\n%s\n--- errors\n%s"
                    family.Name
                    shape.Name
                    source
                    (String.concat "\n" checked'.Errors)

            let fired = HashSet<string>()

            for code, _ in family.Edits checked' do
                fired.Add code |> ignore

            for code, _ in family.Notes checked' do
                fired.Add code |> ignore

            let expected, quiet = expectations shape

            for code in expected do
                if not (fired.Contains code) then
                    missing.Add $"{family.Name}/{shape.Name}: {code}"

            // a shape written to stay quiet under a rule (`!FR0162`) is the
            // rule's false-positive guard
            for code in quiet do
                if fired.Contains code then
                    missing.Add $"{family.Name}/{shape.Name}: {code} fired on a shape written to stay quiet"

    Assert.True(missing.Count = 0, "shapes that never reached their rule:\n" + String.concat "\n" missing)

/// The rules no generated program can reach, each with its reason. A rule
/// leaves this list by getting a shape; one joins it only with a reason
/// the harness cannot answer.
let private unreachable =
    [
        "FR0077", "fixes a compile error (FS0366, missing interface members): fires only on a program with type errors"
        "FR0145", "fixes a compile error (FS0764, unassigned record fields): fires only on a program with type errors"
        "FR0143", "reads a script's #load chain against an fsproj on disk; a generated program owns no directory"
        "FR0090",
        "the api pass's tupled-to-curried migration rewrites call sites across a project; the tool runs it, not a rule"
        "FR0091", "the api pass's data-last reorder rewrites call sites across a project; the tool runs it, not a rule"
        "FR0080", "a leading tab in code is FS1161: fires only on a program the compiler rejects"
    ]

/// The parse-only suite's codes as the catalog spells them: a kind suffix
/// (`FR0108/Identity`) drops, and the redundant-syntax kinds map to their
/// rule codes.
let private parseOnlyCodes =
    RuleSet.targetedCodes
    |> List.map (fun code ->
        match code with
        | "FR008x/AttributeSuffix" -> "FR0082"
        | "FR008x/AttributeParens" -> "FR0083"
        | "FR008x/Backticks" -> "FR0084"
        | "FR008x/HoleFreeInterpolation" -> "FR0086"
        // the duplicate-operand kind is its own rule
        | "FR0108/Duplicate" -> "FR0109"
        | c when c.Contains '/' -> c.Substring(0, c.IndexOf '/')
        | c -> c)

/// Every rule of the catalog has a generated shape, in this suite or the
/// parse-only one, or a reason above. When a rule is added without a
/// shape, this says so.
[<Fact>]
let ``every catalogued rule has a generated shape or a stated reason`` () =
    let shaped =
        [
            yield! parseOnlyCodes

            for family in families do
                for gen in family.Shapes do
                    yield! fst (expectations (Gen.sampleWithSize 20 1 gen |> Array.head))
        ]
        |> Set.ofList

    let excused = unreachable |> List.map fst |> Set.ofList

    let unshaped =
        FSharp.Refactor.RuleCatalog.known
        |> Set.filter (fun code -> not (shaped.Contains code || excused.Contains code))

    let excusedButShaped = Set.intersect shaped excused

    Assert.True(unshaped.IsEmpty, "catalogued rules without a generated shape: " + String.concat ", " unshaped)

    Assert.True(
        excusedButShaped.IsEmpty,
        "rules listed as unreachable that a shape reaches: "
        + String.concat ", " excusedButShaped
    )
