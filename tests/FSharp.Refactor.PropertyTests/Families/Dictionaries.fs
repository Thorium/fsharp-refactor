/// FR0014 DictTryGet, FR0018 DictTryAdd, FR0154 DictGetOrAdd: the
/// dictionary lookup idioms.
module FSharp.Refactor.PropertyTests.Families.Dictionaries

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private shapes =
    [
        // FR0014: `if d.ContainsKey k then d.[k] else fallback`
        withFree "ContainsThenIndex" [ "FR0014" ] genSmall (fun n i ->
            $"let f{i} (d: Dictionary<string, int>) (k: string) = if d.ContainsKey k then d.[k] else {n}")
        // FR0014: the multi-line form
        withFree "ContainsThenIndexBlock" [ "FR0014" ] genSmall (fun n i ->
            $"let f{i} (d: Dictionary<string, int>) (k: string) =\n    if d.ContainsKey k then\n        d.[k] + {n}\n    else\n        0")
        // FR0018: `if not (d.ContainsKey k) then d.[k] <- v`
        fixed' "CheckThenAdd" [ "FR0018" ] (fun i ->
            $"let f{i} (d: Dictionary<string, int>) (k: string) (v: int) = if not (d.ContainsKey k) then d.[k] <- v")
        // FR0154: TryGetValue, then compute and store
        fixed' "TryGetThenStore" [ "FR0154" ] (fun i ->
            $"let f{i} (xs: System.Collections.Concurrent.ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =\n    match xs.TryGetValue key with\n    | true, x -> x\n    | false, _ ->\n        let res = compute ()\n        xs.[key] <- res\n        res")
    ]

let family: Family =
    {
        Name = "Dictionaries"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in DictTryGet.find c.Tree c.Source c.Check ->
                        "FR0014", [ edit "FR0014" s.Range s.ReplacementText ]
                    for s in DictTryGet.findTryAdd c.Tree c.Source c.Check ->
                        "FR0018", [ edit "FR0018" s.Range s.ReplacementText ]
                    for s in DictTryGet.findGetOrAdd c.Tree c.Source c.Check ->
                        "FR0154", [ edit "FR0154" s.Range s.ReplacementText ]
                ]
        Notes = fun _ -> []
    }
