/// The option, result and pattern-matching rules: FR0002 OptionModule,
/// FR0009 ResultModule, FR0025 OptionOfObj, FR0034 OptionMatch, FR0059
/// StructOption, FR0003 Composition, FR0072 ExpandWildcard, FR0087 /
/// FR0088 / FR0089 PatternCleanups, FR0129 MatchGuards, FR0117
/// MatchArmMerge, FR0110 MissingCases, FR0100 UnimplementedBranch and
/// FR0040 RedundantGuard. A shape that needs a union or a private helper
/// prints one nested module holding the type and the function, so it is
/// still one declaration and shrinks as one.
module FSharp.Refactor.PropertyTests.Families.Matching

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

/// The comment phrases FR0100 accepts as an admission that the branch is
/// unfinished, in both comment syntaxes.
let private genStubComment: FsCheck.Gen<string> =
    Gen.elements
        [
            "// Not supported yet"
            "// not implemented yet"
            "(* unimplemented *)"
            "// TODO: implement this"
            "// unsupported for now"
        ]

let private shapes =
    [
        // FR0002: Some-wrapped body with None is Option.map
        withFree "OptionMap" [ "FR0002" ] genSmall (fun n i ->
            $"let f{i} (x: int option) = match x with | Some v -> Some (v + {n}) | None -> None")
        // FR0002: the bound variable with a literal default is Option.defaultValue
        withFree "OptionDefault" [ "FR0002" ] genSmall (fun n i ->
            $"let f{i} (x: int option) =\n    match x with\n    | Some v -> v\n    | None -> {n}")
        // FR0002: a non-atomic default keeps its laziness with Option.defaultWith
        withFree "OptionDefaultWith" [ "FR0002" ] genSmall (fun n i ->
            $"let f{i} (x: int option) (d: int) = match x with | Some v -> v | None -> d + {n}")
        // FR0002: a transformed body with a default is map then defaultValue
        withFree "OptionMapDefault" [ "FR0002" ] genSmall (fun n i ->
            $"let f{i} (x: int option) = match x with | Some v -> v * {n} | None -> 0")
        // FR0002: true/false arms are IsSome, reversed IsNone
        withFree "OptionIsSome" [ "FR0002" ] (Gen.elements [ "true", "false"; "false", "true" ]) (fun (a, b) i ->
            $"let f{i} (x: int option) = match x with | Some _ -> {a} | None -> {b}")
        // FR0002: a unit None arm is Option.iter
        fixed' "OptionIter" [ "FR0002" ] (fun i ->
            $"let f{i} (g: int -> unit) (x: int option) = match x with | Some v -> g v | None -> ()")
        // FR0002: the ValueOption twin
        withFree "ValueOptionDefault" [ "FR0002" ] genSmall (fun n i ->
            $"let f{i} (x: int voption) = match x with | ValueSome v -> v | ValueNone -> {n}")
        // FR0009: Ok-wrapped body with the error passed through is Result.map
        withFree "ResultMap" [ "FR0009" ] genSmall (fun n i ->
            $"let f{i} (r: Result<int, string>) = match r with | Ok v -> Ok (v + {n}) | Error e -> Error e")
        // FR0009: the bound value with a literal default is Result.defaultValue
        withFree "ResultDefault" [ "FR0009" ] genSmall (fun n i ->
            $"let f{i} (r: Result<int, string>) =\n    match r with\n    | Ok v -> v\n    | Error _ -> {n}")
        // FR0009: true/false arms are Result.isOk, reversed isError
        withFree "ResultIsOk" [ "FR0009" ] (Gen.elements [ "true", "false"; "false", "true" ]) (fun (a, b) i ->
            $"let f{i} (r: Result<int, string>) = match r with | Ok _ -> {a} | Error _ -> {b}")
        // FR0009: a unit Error arm is Result.iter
        fixed' "ResultIter" [ "FR0009" ] (fun i ->
            $"let f{i} (g: int -> unit) (r: Result<int, string>) = match r with | Ok v -> g v | Error _ -> ()")
        // FR0009: a rewrapped error is Result.mapError
        withFree "ResultMapError" [ "FR0009" ] genWord (fun w i ->
            $"let f{i} (r: Result<int, string>) = match r with | Ok v -> Ok v | Error e -> Error (e + \"{w}\")")
        // FR0025: the four spellings of a null test that wraps the value
        withFree
            "NullTestWrap"
            [ "FR0025" ]
            (Gen.elements
                [
                    "if isNull s then None else Some s"
                    "if not (isNull s) then Some s else None"
                    "if s = null then None else Some s"
                    "if s <> null then Some s else None"
                    "match s with\n    | null -> None\n    | v -> Some v"
                ])
            (fun body i -> $"let f{i} (s: string) =\n    {body}")
        // FR0025: the ValueOption twin
        fixed' "NullTestWrapValue" [ "FR0025" ] (fun i ->
            $"let f{i} (s: string) = if isNull s then ValueNone else ValueSome s")
        // FR0034: IsSome then .Value is a match
        withFree "IsSomeThenValue" [ "FR0034" ] genSmall (fun n i ->
            $"let f{i} (x: int option) = if x.IsSome then x.Value + {n} else {n}")
        // FR0034: the multi-line form, IsNone first
        withFree "IsNoneThenValueBlock" [ "FR0034" ] genSmall (fun n i ->
            $"let f{i} (x: int option) =\n    if x.IsNone then\n        {n}\n    else\n        x.Value * 2")
        // FR0034: a unit then-branch with no else
        fixed' "IsSomeThenPrint" [ "FR0034" ] (fun i ->
            $"let f{i} (x: int option) = if x.IsSome then printfn \"%%d\" x.Value")
        // FR0034: IsSome && .Value test is Option.exists, IsNone || is Option.forall
        withFree
            "IsSomeAndValue"
            [ "FR0034" ]
            (Gen.zip (Gen.elements [ "IsSome &&"; "IsNone ||" ]) genSmall)
            (fun (op, n) i -> $"let f{i} (x: int option) = x.{op} x.Value > {n}")
        // FR0059: a private option-returning helper whose only use is a match
        withFree "PrivateOptionHelper" [ "FR0059" ] (Gen.zip (Gen.choose (1, 9)) genWord) (fun (k, w) i ->
            $"module M{i} =\n    let private tryHalf{i} (n: int) = if n %% 2 = 0 then Some(n / {k}) else None\n\n    let f{i} (n: int) =\n        match tryHalf{i} n with\n        | Some h -> string h\n        | None -> \"{w}\"")
        // FR0003: a lambda that only pipes its argument through functions
        withFree "PipeLambda" [ "FR0003" ] (Gen.elements [ "x |> g |> h"; "h (g x)" ]) (fun body i ->
            $"let f{i} (g: int -> int) (h: int -> string) (xs: int list) = xs |> List.map (fun x -> {body})")
        // FR0003: an operator section as the last stage
        withFree "PipeLambdaSection" [ "FR0003" ] genSmall (fun n i ->
            $"let f{i} (g: int -> int) (xs: int list) = xs |> List.map (fun x -> x |> g |> (+) {n})")
        // FR0072: a wildcard hiding two cases of a three-case union
        withFree "WildcardHidesTwo" [ "FR0072" ] genSmall (fun n i ->
            $"module M{i} =\n    type T{i} =\n        | A{i}\n        | B{i}\n        | C{i}\n\n    let f{i} (t: T{i}) =\n        match t with\n        | A{i} -> {n}\n        | _ -> {n} + 1")
        // FR0072: a wildcard hiding one case that carries a field
        withFree "WildcardHidesField" [ "FR0072" ] genSmall (fun n i ->
            $"module M{i} =\n    type T{i} =\n        | A{i}\n        | B{i} of int\n\n    let f{i} (t: T{i}) =\n        match t with\n        | A{i} -> {n}\n        | _ -> {n} + 1")
        // FR0072: a RequireQualifiedAccess union keeps its qualifier in the fix
        withFree "WildcardQualified" [ "FR0072" ] genSmall (fun n i ->
            $"module M{i} =\n    [<RequireQualifiedAccess>]\n    type T{i} =\n        | Fast{i}\n        | Careful{i}\n        | Dry{i}\n\n    let f{i} (m: T{i}) =\n        match m with\n        | T{i}.Fast{i} -> {n}\n        | T{i}.Careful{i} -> {n} + 1\n        | _ -> {n} + 2")
        // FR0072: a wildcard standing in for None
        withFree "WildcardIsNone" [ "FR0072" ] genSmall (fun n i ->
            $"let f{i} (x: int option) =\n    match x with\n    | Some v -> v + 1\n    | _ -> {n}")
        // FR0087: cons of the empty list is a one-element list pattern
        withFree "ConsOfEmpty" [ "FR0087" ] genSmall (fun n i ->
            $"let f{i} (xs: int list) =\n    match xs with\n    | x :: [] -> x + {n}\n    | _ -> 0")
        // FR0088: every field of the case is a wildcard
        withFree "AllWildFields" [ "FR0088" ] genSmall (fun n i ->
            $"module M{i} =\n    type T{i} =\n        | Pair{i} of int * int\n        | One{i}\n\n    let f{i} (t: T{i}) =\n        match t with\n        | Pair{i}(_, _) -> {n}\n        | One{i} -> {n} + 1")
        // FR0089: a comma inside an unannotated list literal builds one tuple
        withFree "TupleInList" [ "FR0089" ] (Gen.zip genSmall genSmall) (fun (a, b) i -> $"let v{i} = [ {a}, {b} ]")
        // FR0129: a guard that only equality-tests the binder against a string
        withFree "GuardIsStringLiteral" [ "FR0129" ] (Gen.zip genWord genSmall) (fun (w, n) i ->
            $"let f{i} (a: string) =\n    match a with\n    | x when x = \"{w}\" -> {n}\n    | _ -> {n} + 1")
        // FR0129: the same against an int, literal on the left
        withFree "GuardIsIntLiteral" [ "FR0129" ] genSmall (fun n i ->
            $"let f{i} (a: int) =\n    match a with\n    | x when {n} = x -> \"{n}\"\n    | _ -> \"other\"")
        // FR0117: adjacent arms with the same body fold into an or-pattern
        withFree "AdjacentSameArms" [ "FR0117" ] (Gen.zip genSmall (Gen.choose (2, 4))) (fun (n, count) i ->
            let arms =
                [ for k in 0 .. count - 1 -> $"    | {n + 100 * k} -> true" ]
                |> String.concat "\n"

            $"let f{i} (a: int) =\n    match a with\n{arms}\n    | _ -> false")
        // FR0117: union cases with literal payloads merge too
        withFree "AdjacentPayloadArms" [ "FR0117" ] genSmall (fun n i ->
            $"let f{i} (o: int option) =\n    match o with\n    | Some {n} -> true\n    | Some {n + 1} -> true\n    | Some _ -> false\n    | None -> false")
        // FR0110: a match with no arm for one case and no wildcard
        withFree "MissingOneCase" [ "FR0110" ] genSmall (fun n i ->
            $"module M{i} =\n    type T{i} =\n        | R{i}\n        | G{i}\n        | B{i}\n\n    let f{i} (c: T{i}) =\n        match c with\n        | R{i} -> {n}\n        | G{i} -> {n} + 1")
        // FR0110: the missing case carries a field, and two are missing
        withFree "MissingTwoCases" [ "FR0110" ] genSmall (fun n i ->
            $"module M{i} =\n    type T{i} =\n        | Dot{i}\n        | Circle{i} of int\n        | Square{i} of int\n\n    let f{i} (s: T{i}) =\n        match s with\n        | Dot{i} -> {n}")
        // FR0100: a branch that says it is unfinished and returns None
        withFree "UnfinishedNone" [ "FR0100" ] genStubComment (fun comment i ->
            $"module M{i} =\n    type T{i} =\n        | Ga{i} of int\n        | Se{i} of int\n        | Jo{i}\n\n    let f{i} (m: T{i}) =\n        match m with\n        | Ga{i} c -> Some c\n        | Se{i} c -> Some (c + 1)\n        | Jo{i} ->\n            {comment}\n            None")
        // FR0100: an empty string stand-in
        withFree "UnfinishedEmptyString" [ "FR0100" ] genStubComment (fun comment i ->
            $"module M{i} =\n    type T{i} =\n        | A{i}\n        | B{i}\n        | C{i}\n\n    let f{i} (m: T{i}) =\n        match m with\n        | A{i} -> string 1\n        | B{i} -> string 2\n        | C{i} ->\n            {comment}\n            \"\"")
        // FR0040: a membership guard before a miss-tolerant Remove/Add
        withFree
            "GuardBeforeRemove"
            [ "FR0040" ]
            (Gen.elements
                [
                    "(d: Dictionary<int, string>) (k: int) = if d.ContainsKey k then d.Remove k |> ignore"
                    "(s: HashSet<int>) (x: int) = if not (s.Contains x) then s.Add x |> ignore"
                    "(s: HashSet<int>) (x: int) = if s.Contains x then s.Remove x |> ignore"
                ])
            (fun rest i -> $"let f{i} {rest}")
    ]

let family: Family =
    {
        Name = "Matching"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in OptionModule.find c.Tree c.Source c.Check ->
                        "FR0002", [ edit "FR0002" s.Range s.ReplacementText ]
                    // the script runs on FSharp.Core 10, so the Core 9 targets need no filtering
                    for s in ResultModule.find c.Tree c.Source c.Check ->
                        "FR0009", [ edit "FR0009" s.Range s.ReplacementText ]
                    for s in OptionOfObj.find c.Tree c.Source c.Check ->
                        "FR0025", [ edit "FR0025" s.Range s.ReplacementText ]
                    for s in OptionMatch.find c.Tree c.Source c.Check ->
                        "FR0034", [ edit "FR0034" s.Range s.ReplacementText ]
                    for s in StructOption.find c.Tree c.Source c.Check ->
                        "FR0059", [ for r, _, t in s.Edits -> edit "FR0059" r t ]
                    for s in Composition.find c.Tree c.Source c.Check ->
                        "FR0003", [ edit "FR0003" s.Range s.ReplacementText ]
                    for s in ExpandWildcard.find c.Tree c.Source c.Check ->
                        "FR0072", [ edit "FR0072" s.Range s.ReplacementText ]
                    let conses, wilds, tuples = PatternCleanups.find c.Tree c.Source c.Check
                    for s in conses -> "FR0087", [ edit "FR0087" s.Range s.ReplacementText ]
                    for s in wilds -> "FR0088", [ edit "FR0088" s.Range s.ReplacementText ]
                    // the CLI reports FR0089 without a fix; the editor's fix is taken here so it is exercised
                    for s in tuples do
                        let r, _, t = s.Fix
                        yield "FR0089", [ edit "FR0089" r t ]

                    for s in MatchGuards.find c.Tree c.Source -> "FR0129", [ edit "FR0129" s.Range s.LiteralText ]

                    for s in MissingCases.findMergeableArms c.Tree c.Source ->
                        "FR0117", [ edit "FR0117" s.ReplaceRange s.NewText ]

                    for s in MissingCases.find c.Tree c.Source c.Check ->
                        "FR0110", [ edit "FR0110" s.Range s.InsertText ]

                    for s in UnimplementedBranch.find c.Tree c.Source ->
                        "FR0100", [ edit "FR0100" s.Range s.ReplacementText ]

                    for s in RedundantGuard.find c.Tree c.Source c.Check ->
                        "FR0040", [ edit "FR0040" s.Range s.ReplacementText ]
                ]
        Notes = fun _ -> []
    }
