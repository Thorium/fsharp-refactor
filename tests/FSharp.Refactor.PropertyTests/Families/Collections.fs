/// The collection and construction rules: FR0137 MapFusion, FR0102
/// ListIndexing, FR0139 SeqOnArray, FR0052 CountIsEmpty, FR0030 AddRange,
/// FR0041 VectorizedLinq, FR0076 MapIgnore, FR0074 NestedRecordUpdate,
/// FR0145 RecordFields, FR0140 ObjectInitializer, FR0085 RedundantNew,
/// FR0036 TypeChecks, FR0027 ClosureCapture, FR0007 MutableRemoval,
/// FR0164 EnumerationMutation.
///
/// FR0145 has no shape: it fixes a compile error (a record expression that
/// leaves fields unassigned, FS0764) and runs only on a file with type
/// errors, which the generated programs must not have. Its `find` still
/// runs in `Edits`/`Notes`, so the damaged-program property exercises it.
module FSharp.Refactor.PropertyTests.Families.Collections

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private shapes =
    [
        // FR0137: two map passes whose first mapper is fst or snd
        withFree
            "MapFusionProjection"
            [ "FR0137" ]
            (Gen.zip (Gen.elements [ "Array", "[]"; "List", "list"; "Seq", "seq" ]) (Gen.elements [ "fst"; "snd" ]))
            (fun ((m, suffix), proj) i ->
                let elem = if proj = "fst" then "(int * string)" else "(string * int)"
                $"let f{i} (g: int -> int) (xs: {elem} {suffix}) = xs |> {m}.map {proj} |> {m}.map g")
        // FR0137: a leading map id
        withFree "MapFusionId" [ "FR0137" ] (Gen.elements [ "Array"; "List"; "Seq" ]) (fun m i ->
            $"let f{i} (g: int -> int) (xs: int {m.ToLowerInvariant()}) = xs |> {m}.map id |> {m}.map g")
        // FR0137: the pipeline laid out across lines
        fixed' "MapFusionMultiLine" [ "FR0137" ] (fun i ->
            $"let f{i} (g: int -> int) (xs: (int * string) list) =\n    xs\n    |> List.map fst\n    |> List.map g")
        // FR0102: indexing a list per iteration
        withFree "ListIndexLoop" [ "FR0102" ] genSmall (fun n i ->
            $"let f{i} (names: int list) (count: int) =\n    let mutable total = {n}\n    for i in 0 .. count - 1 do\n        total <- total + names.[i]\n    total")
        // FR0102: List.item inside a collection callback
        fixed' "ListItemCallback" [ "FR0102" ] (fun i ->
            $"let f{i} (names: string list) (idxs: int list) = idxs |> List.map (fun i -> (List.item i names).Length)")
        // FR0102: the list's length read per iteration
        withFree "ListLengthLoop" [ "FR0102" ] genSmall (fun n i ->
            $"let f{i} (points: int list) (count: int) =\n    let mutable total = 0\n    for i in 0 .. count - 1 do\n        total <- total + count / (points.Length + {n + 1})\n    total")
        // FR0139: a scalar-returning Seq function piped from an array
        withFree
            "SeqOnArrayPiped"
            [ "FR0139" ]
            (Gen.elements [ "length"; "isEmpty"; "tryHead"; "tryLast"; "tryExactlyOne" ])
            (fun fn i -> $"let f{i} (xs: int[]) = xs |> Seq.{fn}")
        // FR0139: a curried predicate call, direct and piped
        withFree
            "SeqOnArrayPredicate"
            [ "FR0139" ]
            (Gen.zip (Gen.elements [ "exists"; "forall"; "tryFind"; "tryFindIndex" ]) genSmall)
            (fun (fn, n) i -> $"let f{i} (xs: int[]) = xs |> Seq.{fn} (fun x -> x > {n})")
        withFree "SeqOnArrayDirect" [ "FR0139" ] (Gen.elements [ "exists"; "forall" ]) (fun fn i ->
            $"let f{i} (xs: string[]) = Seq.{fn} (fun x -> x <> \"\") xs")
        // FR0139: a record field typed as an array
        withFree "SeqOnArrayField" [ "FR0139" ] (Gen.elements [ "isEmpty"; "length"; "tryHead" ]) (fun fn i ->
            $"type S{i} = {{ Buffer{i}: int[] }}\nlet f{i} (s: S{i}) = s.Buffer{i} |> Seq.{fn}")
        // FR0139: contains on an int array takes the LINQ spelling
        withFree "SeqContainsInt" [ "FR0139" ] (Gen.elements [ "int"; "int64" ]) (fun t i ->
            $"let f{i} (xs: {t}[]) (v: {t}) = xs |> Seq.contains v")
        // FR0052: an emptiness check through Count on a concurrent collection
        withFree
            "ConcurrentCountZero"
            [ "FR0052" ]
            (Gen.zip
                (Gen.elements [ "ConcurrentQueue"; "ConcurrentStack"; "ConcurrentBag" ])
                (Gen.elements [ "q.Count = 0"; "0 = q.Count"; "q.Count > 0"; "q.Count <> 0"; "0 < q.Count" ]))
            (fun (t, test) i -> $"let f{i} (q: System.Collections.Concurrent.{t}<int>) = {test}")
        // FR0030: a loop that only adds its element to a ResizeArray
        withFree "AddLoop" [ "FR0030" ] (Gen.elements [ "xs"; "List.rev xs"; "List.sort xs" ]) (fun src i ->
            $"let f{i} (acc: ResizeArray<int>) (xs: int list) =\n    for x in {src} do\n        acc.Add x")
        // FR0030: a range source becomes an array literal
        withFree "AddLoopRange" [ "FR0030" ] genSmall (fun n i ->
            $"let f{i} (acc: ResizeArray<int>) (a: int) (b: int) =\n    for x in a + {n} .. b do\n        acc.Add x")
        // FR0041: a scalar aggregation over a primitive array
        withFree
            "ArrayAggregate"
            [ "FR0041" ]
            (Gen.zip3
                (Gen.elements [ "Array"; "Seq" ])
                (Gen.elements [ "sum"; "max"; "min" ])
                (Gen.elements [ "int"; "int64" ]))
            (fun (m, fn, t) i -> $"let f{i} (values: {t}[]) = values |> {m}.{fn}")
        withFree "ArrayAggregateDirect" [ "FR0041" ] (Gen.elements [ "sum"; "max"; "min" ]) (fun fn i ->
            $"let f{i} (values: int[]) = Array.{fn} values")
        // FR0041: the aggregated array behind a record field
        fixed' "ArrayAggregateField" [ "FR0041" ] (fun i ->
            $"type State{i} = {{ Samples{i}: int[] }}\nlet f{i} (state: State{i}) = state.Samples{i} |> Array.sum")
        // FR0041: contains on a primitive array
        withFree "ArrayContains" [ "FR0041" ] genSmall (fun n i ->
            $"let f{i} (values: int[]) = values |> Array.contains {n}")
        // FR0076: a List/Array map whose result is thrown away
        withFree "MapIgnoreStrict" [ "FR0076" ] (Gen.elements [ "List", "list"; "Array", "[]" ]) (fun (m, suffix) i ->
            $"let f{i} (g: int -> int) (xs: int {suffix}) = xs |> {m}.map g |> ignore")
        // FR0076: the lazy Seq.map ignored, which runs nothing
        fixed' "MapIgnoreLazy" [ "FR0076" ] (fun i ->
            $"let f{i} (g: int -> int) (xs: seq<int>) = xs |> Seq.map g |> ignore")
        // FR0074: a nested copy-and-update
        withFree "NestedUpdate" [ "FR0074" ] genSmall (fun n i ->
            $"type I{i} = {{ Y{i}: int; Z{i}: int }}\ntype O{i} = {{ X{i}: I{i}; N{i}: int }}\nlet f{i} (r: O{i}) (v: int) = {{ r with X{i} = {{ r.X{i} with Y{i} = v + {n} }} }}")
        // FR0074: two inner fields, and two levels
        fixed' "NestedUpdateTwoFields" [ "FR0074" ] (fun i ->
            $"type I{i} = {{ Y{i}: int; Z{i}: int }}\ntype O{i} = {{ X{i}: I{i}; N{i}: int }}\nlet f{i} (r: O{i}) (v: int) = {{ r with X{i} = {{ r.X{i} with Y{i} = v; Z{i} = v + 1 }} }}")
        fixed' "NestedUpdateDeep" [ "FR0074" ] (fun i ->
            $"type L3{i} = {{ V{i}: int }}\ntype L2{i} = {{ Inner{i}: L3{i} }}\ntype L1{i} = {{ Mid{i}: L2{i} }}\nlet f{i} (r: L1{i}) (v: int) = {{ r with Mid{i} = {{ r.Mid{i} with Inner{i} = {{ r.Mid{i}.Inner{i} with V{i} = v }} }} }}")
        // FR0140: property sets right after the construction
        withFree "ObjectInit" [ "FR0140" ] (Gen.zip genSmall genWord) (fun (n, w) i ->
            $"type C{i}() =\n    member val Id = 0 with get, set\n    member val Name = \"\" with get, set\nlet f{i} () =\n    let h = C{i}()\n    h.Id <- {n}\n    h.Name <- \"{w}\"\n    h")
        // FR0140: the new keyword and existing constructor arguments
        withFree "ObjectInitNewWithArgs" [ "FR0140" ] genSmall (fun n i ->
            $"type P{i}(name: string) =\n    member val Name = name with get, set\n    member val Age = 0 with get, set\nlet f{i} (s: string) =\n    let p = new P{i}(s)\n    p.Age <- {n}\n    p")
        // FR0085: new on a construction nothing disposes
        withFree
            "RedundantNew"
            [ "FR0085" ]
            (Gen.zip
                (Gen.elements [ "StringBuilder"; "ResizeArray<int>"; "Random"; "System.Text.StringBuilder" ])
                genSmall)
            (fun (t, n) i -> $"let v{i} = new {t}({n})")
        // FR0036: the type's name compared to a string
        withFree "TypeNameCompare" [ "FR0036" ] (Gen.zip (Gen.elements [ "Name"; "FullName" ]) genWord) (fun (p, w) i ->
            $"let f{i} (x: obj) = x.GetType().{p} = \"{w}\"")
        // FR0036: exact-type equality with typeof
        withFree "TypeofEquality" [ "FR0036" ] (Gen.elements [ "string"; "int"; "Exception" ]) (fun t i ->
            $"let f{i} (x: obj) = x.GetType() = typeof<{t}>")
        // FR0027: a this-capturing handler hung on a process-wide publisher
        withFree
            "ProcessWideHandler"
            [ "FR0027" ]
            (Gen.elements
                [
                    "System.AppDomain.CurrentDomain.ProcessExit |> Event.add (fun _ -> this.Bump())"
                    "System.AppDomain.CurrentDomain.UnhandledException.Add(fun _ -> this.Bump())"
                ])
            (fun hook i ->
                $"type H{i}() =\n    let mutable exits = 0\n    member this.Hook() = {hook}\n    member this.Bump() = exits <- exits + 1")
        // FR0027: a publisher handed in, captured through an instance field
        fixed' "ExternalHandler" [ "FR0027" ] (fun i ->
            $"type S{i}() =\n    let fired = Event<int>()\n    member _.Fired = fired.Publish\ntype U{i}(src: S{i}) =\n    let mutable total = 0\n    member _.Hook() = src.Fired.Add(fun n -> total <- total + n)\n    member _.Total = total")
        // FR0007: a local mutable that is never assigned
        withFree "UnusedMutableInt" [ "FR0007" ] genSmall (fun n i ->
            $"let f{i} () =\n    let mutable x = {n}\n    x + 1")
        fixed' "UnusedMutableString" [ "FR0007" ] (fun i ->
            $"let f{i} (s: string) =\n    let mutable name = s\n    name.Length")
        fixed' "UnusedMutableGuid" [ "FR0007" ] (fun i ->
            $"let f{i} () =\n    let mutable g = Guid.NewGuid()\n    g.ToString()")
        // FR0164: a ResizeArray pruned inside a for loop over itself
        withFree "PrunedWhileEnumerated" [ "FR0164" ] genSmall (fun n i ->
            $"let f{i} (items: List<int>) =\n    for x in items do\n        if x < {n} then\n            items.Remove x |> ignore")
        // FR0164 must stay quiet: the mutation is deferred into a lambda, or
        // the loop is left right after it (CR0171's mutate-and-leave idiom)
        withFree
            "DeferredOrLeavingMutation"
            [ "!FR0164" ]
            (Gen.zip genSmall (Gen.elements [ true; false ]))
            (fun (n, deferred) i ->
                if deferred then
                    $"let f{i} (items: List<int>) (later: List<unit -> unit>) =\n    for x in items do\n        if x < {n} then\n            later.Add(fun () -> items.Remove x |> ignore)"
                else
                    $"let f{i} (items: List<int>) =\n    for x in items do\n        if x < {n} then\n            items.Remove x |> ignore\n            failwith \"negative\"")
        // FR0164: a dictionary grown while its keys are walked
        withFree "GrownWhileEnumerated" [ "FR0164" ] genSmall (fun n i ->
            $"let f{i} (d: Dictionary<int, int>) =\n    for k in d.Keys do\n        d.Add(k + {n + 100}, k)")
        // FR0164: an indexer store into the list being walked, both spellings
        withFree "StoredWhileEnumerated" [ "FR0164" ] (Gen.elements [ "xs.[0]"; "xs[0]" ]) (fun slot i ->
            $"let f{i} (xs: ResizeArray<int>) =\n    for x in xs do\n        {slot} <- x")
        // FR0164 must stay quiet: an interface-typed collection may be a
        // concurrent one at run time, and a dictionary tolerates removal
        withFree "EditedThroughInterface" [ "!FR0164" ] genSmall (fun n i ->
            $"let f{i} (items: IList<int>) (d: Dictionary<int, int>) =\n    for x in items do\n        if x < {n} then items.Remove x |> ignore\n    for KeyValue(k, v) in d do\n        if v < {n} then d.Remove k |> ignore")
        // FR0169: a seq parameter walked twice on one path
        withFree "SeqWalkedTwice" [ "FR0169" ] genSmall (fun n i ->
            $"let f{i} (xs: int seq) =\n    if Seq.isEmpty xs then {n} else Seq.length xs + Seq.sum xs")
        // FR0169 must stay quiet: the two walks sit in different arms
        withFree "SeqWalkedOnce" [ "!FR0169" ] genSmall (fun n i ->
            $"let f{i} (xs: int seq) (flag: bool) =\n    if flag then Seq.length xs else Seq.sum xs + {n}")
        // FR0170: a loop over a dictionary's keys that looks each one up again
        withFree "KeysLoopLookup" [ "FR0170" ] genSmall (fun n i ->
            $"let f{i} (d: Dictionary<string, int>) =\n    let mutable total = {n}\n    for k in d.Keys do\n        total <- total + d.[k] + k.Length\n    total")
        // FR0170 must stay quiet: a store through the indexer
        withFree "KeysLoopStore" [ "!FR0170" ] genSmall (fun n i ->
            $"let f{i} (d: Dictionary<string, int>) =\n    for k in d.Keys do\n        d.[k] <- d.[k] + {n}")
        // FR0173: a range allocated only to be mapped over
        withFree "RangeMapped" [ "FR0173" ] genSmall (fun n i ->
            $"let f{i} (count: int) = [| 0 .. count - 1 |] |> Array.map (fun x -> x + {n})")
        // FR0173 must stay quiet: a range that does not start at 0, and a
        // map over a collection that is not a range
        withFree "RangeMapKept" [ "!FR0173" ] genSmall (fun n i ->
            $"let f{i} (count: int) (xs: int[]) =\n    Array.append ([| 1 .. count |] |> Array.map (fun x -> x + {n})) (xs |> Array.map (fun x -> x - {n}))")
        // FR0174: a query copied before a trivial filter and projection (the
        // generated module opens no System.Linq, so the shape's own module does)
        withFree "QueryCopiedChain" [ "FR0174" ] genSmall (fun n i ->
            $"module Q{i} =\n    open System.Linq\n    type Row{i} = {{ Id{i}: int; State{i}: int }}\n    let f{i} (q: IQueryable<Row{i}>) = q.ToList().Where(fun r -> r.Id{i} > {n} || r.State{i} = 0).Select(fun r -> r.State{i})")
        // FR0174 must stay quiet: a call inside the filter, a list that is no
        // query, and a pipeline - the F# modules' copy is the author's visible
        // choice, taken only under the default-off `pipelines` knob
        withFree "QueryCopyKept" [ "!FR0174" ] genSmall (fun n i ->
            $"module Q{i} =\n    open System.Linq\n    type Row{i} = {{ Id{i}: int; Name{i}: string }}\n    let f{i} (q: IQueryable<Row{i}>) (xs: ResizeArray<Row{i}>) =\n        q.ToList().Where(fun r -> r.Name{i}.Contains \"{n}\"), xs.ToList().Where(fun r -> r.Id{i} > {n}), (q |> Seq.toList |> List.filter (fun r -> r.Id{i} <> {n}))")
    ]

let family: Family =
    {
        Name = "Collections"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in MapFusion.find c.Tree c.Source -> "FR0137", [ edit "FR0137" s.Range s.ReplacementText ]
                    // the filter shape takes RemoveAll, as the analyzer prefers it
                    for s in EnumerationMutation.find c.Tree c.Source c.Check ->
                        match s.Filter with
                        | Some(r, _, replacement) -> "FR0164", [ edit "FR0164" r replacement ]
                        | None -> "FR0164", [ edit "FR0164" s.Range s.ReplacementText ]
                    for s in DictKeysLoop.find c.Tree c.Source c.Check ->
                        "FR0170", [ for r, _, t in s.Edits -> edit "FR0170" r t ]
                    for s in RangeMap.find c.Tree c.Source c.Check ->
                        "FR0173", [ edit "FR0173" s.Range s.ReplacementText ]
                    // the sweep applies the exact translations, pipelines left
                    // to their default (off)
                    for s in QueryCopy.find false c.Tree c.Source c.Check do
                        if s.Fidelity = QueryCopy.Exact then
                            yield "FR0174", [ edit "FR0174" s.Range s.ReplacementText ]
                    for s in SeqOnArray.find c.Tree c.Source c.Check ->
                        match s.LinqSpelling with
                        | None -> "FR0139", [ edit "FR0139" s.Range "Array" ]
                        | Some(callRange, linqText) -> "FR0139", [ edit "FR0139" callRange linqText ]
                    // Array.contains is swept to Enumerable.Contains; the
                    // aggregations are notes
                    for s in VectorizedLinq.find c.Tree c.Source c.Check do
                        match s.ReplacementText with
                        | Some replacement -> yield "FR0041", [ edit "FR0041" s.Range replacement ]
                        | None -> ()
                    for s in CountIsEmpty.find c.Tree c.Source c.Check ->
                        "FR0052", [ edit "FR0052" s.Range s.ReplacementText ]
                    for s in AddRange.find c.Tree c.Source c.Check ->
                        "FR0030", [ edit "FR0030" s.Range s.ReplacementText ]
                    for s in MapIgnore.find c.Tree c.Source c.Check do
                        match s.ReplacementText with
                        | Some replacement -> yield "FR0076", [ edit "FR0076" s.Range replacement ]
                        | None -> ()
                    for s in NestedRecordUpdate.find c.Tree c.Source c.Check ->
                        "FR0074", [ edit "FR0074" s.Range s.ReplacementText ]
                    // the CLI applies only the all-obvious insertion; a
                    // placeholder is the editor's offer
                    for s in RecordFields.find c.Tree c.Source c.Check do
                        if s.AllObvious then
                            yield "FR0145", [ edit "FR0145" s.Range s.InsertText ]
                    for s in ObjectInitializer.find c.Tree c.Source c.Check ->
                        "FR0140", [ edit "FR0140" s.Range s.ReplacementText ]
                    for s in RedundantNew.find c.Tree c.Source c.Check -> "FR0085", [ edit "FR0085" s.Range "" ]
                    for s in MutableRemoval.find c.Tree c.Source c.Check -> "FR0007", [ edit "FR0007" s.Range "" ]
                ]
        Notes =
            fun c ->
                [
                    for s in ListIndexing.find c.Tree c.Source c.Check -> "FR0102", s.Range
                    for s in VectorizedLinq.find c.Tree c.Source c.Check do
                        if s.ReplacementText.IsNone then
                            yield "FR0041", s.Range
                    for s in MapIgnore.find c.Tree c.Source c.Check do
                        if s.ReplacementText.IsNone then
                            yield "FR0076", s.Range
                    for s in RecordFields.find c.Tree c.Source c.Check do
                        if not s.AllObvious then
                            yield "FR0145", s.Range
                    for s in TypeChecks.find c.Tree c.Source -> "FR0036", s.Range
                    for s in ClosureCapture.find c.Tree c.Source c.Check -> "FR0027", s.Range
                    for s in SeqEnumeratedTwice.find c.Tree c.Source c.Check -> "FR0169", s.Range
                ]
    }
