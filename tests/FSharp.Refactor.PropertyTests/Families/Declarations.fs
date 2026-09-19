/// The declaration-level rules the parse-only suite runs without a shape
/// of their own: FR0016 StructDu, FR0022 DuFieldNames, FR0069 / FR0070 /
/// FR0093 StructHints, FR0078 WhileBang, FR0081 PathSeparator. The struct
/// hints are notes here, as the CLI reports them without a project to
/// migrate across.
module FSharp.Refactor.PropertyTests.Families.Declarations

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private shapes =
    [
        // FR0016: a private union of struct payloads
        withFree "PrivateUnionOfStructs" [ "FR0016" ] (Gen.elements [ "float"; "int"; "int64"; "decimal" ]) (fun t i ->
            $"type private Shape{i} =\n    | Circle{i} of radius: {t}\n    | Square{i} of side: {t}")
        // FR0022: the names a match site gives the case's fields
        withFree "MatchSiteNames" [ "FR0022" ] (Gen.zip genWord genWord) (fun (a, b) i ->
            $"type private Order{i} =\n    | Line{i} of int * decimal\n    | Total{i} of decimal\n\nlet private f{i} (o: Order{i}) =\n    match o with\n    | Line{i}({a}, {b}) -> decimal {a} * {b}\n    | Total{i} t -> t")
        // FR0069: a struct option field in a private record
        withFree "StructOptionField" [ "FR0069" ] (Gen.elements [ "Guid"; "int"; "DateTime" ]) (fun t i ->
            $"type private Row{i} = {{ Id: {t} option; Name: string }}")
        // FR0070: a small all-struct private record
        withFree "SmallStructRecord" [ "FR0070" ] (Gen.elements [ "float"; "int" ]) (fun t i ->
            $"type private Point{i} = {{ X: {t}; Y: {t} }}")
        // FR0093: a reference tuple of structs in a private record field
        withFree "TupleField" [ "FR0093" ] (Gen.elements [ "int * int"; "float * float * float * float" ]) (fun t i ->
            $"type private Span{i} = {{ Bounds: {t} }}")
        // FR0078: the three-part mutable-condition loop
        fixed' "MutableConditionLoop" [ "FR0078" ] (fun i ->
            $"let private run{i} (check: unit -> Async<bool>) (step: unit -> Async<unit>) =\n    async {{\n        let! first = check ()\n        let mutable go = first\n        while go do\n            do! step ()\n            let! next = check ()\n            go <- next\n    }}")
        // FR0081: a path joined with a hard-coded separator
        withFree
            "SeparatorJoin"
            [ "FR0081" ]
            (Gen.elements
                [
                    "rootDir + \"/\" + fileName"
                    "\"./data/\" + fileName + \".json\""
                    "rootDir + \"\\\\\" + fileName"
                ])
            (fun e i -> $"let f{i} (rootDir: string) (fileName: string) = {e}")
    ]

let family: Family =
    {
        Name = "Declarations"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in StructDu.find (Visibility.apiChangesAllowed ()) c.Tree c.Source ->
                        "FR0016", [ edit "FR0016" s.InsertRange s.InsertText ]
                    for s in DuFieldNames.find (Visibility.apiChangesAllowed ()) c.Tree c.Source ->
                        "FR0022", [ for r, _, t in s.Edits -> edit "FR0022" r t ]
                    for s in MatchBangRule.findWhileBang c.Tree c.Source ->
                        "FR0078", [ for r, _, t in s.Edits -> edit "FR0078" r t ]
                ]
        Notes =
            fun c ->
                let voptions, structs, structTuples =
                    StructHints.find (Visibility.apiChangesAllowed ()) c.Tree c.Source

                [
                    for s in voptions -> "FR0069", s.Range
                    for s in structs -> "FR0070", s.Range
                    for s in structTuples -> "FR0093", s.Range
                    for s in PathSeparator.find c.Tree c.Source -> "FR0081", s.Range
                ]
    }
