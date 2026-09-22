/// The loop and recursion rules: FR0035 ContainsInLoop and FR0037
/// ConstructionInLoop (LoopPerf), FR0050 MutableFold, FR0051
/// QuadraticAppend and FR0107 FlagLoop (Accumulation), FR0156
/// AccumulatorLoop, FR0158 IndexScan, FR0071 LoopInvariant, FR0028
/// QueryInLoop, FR0141 GenerativeLoop, FR0104 RecursiveAppend, FR0058
/// RecursiveSeq, FR0131 RecTailCall and FR0116 RecGroup.
///
/// Every rule of the family fires from a single script. A probed
/// collection that FR0035 can FIX must be a module-level binding, so that
/// shape is a nested module holding the binding and its probing function.
module FSharp.Refactor.PropertyTests.Families.Loops

open FsCheck
open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private lines (xs: string list) = String.concat "\n" xs

/// A list literal of two to four random words, for a startup collection.
let private genWords: Gen<string> =
    Gen.choose (2, 4)
    |> Gen.bind (fun n -> List.replicate n genWord |> Gen.sequenceToList)
    |> Gen.map (fun ws -> ws |> List.map (fun w -> $"\"{w}\"") |> String.concat "; ")

let private shapes =
    [
        // FR0035: `M.contains x ys` on a loop-invariant collection inside a for loop
        withFree
            "ContainsInLoop"
            [ "FR0035" ]
            (Gen.elements [ "List", "int list"; "Array", "int[]"; "Seq", "int seq" ])
            (fun (m, ty) i ->
                lines
                    [
                        $"let f{i} (xs: int list) (ys: {ty}) ="
                        "    for x in xs do"
                        $"        if {m}.contains x ys then ignore x"
                    ])
        // FR0035: the piped probe inside a collection-function callback
        fixed' "ContainsInCallback" [ "FR0035" ] (fun i ->
            $"let f{i} (xs: int list) (ys: int list) = xs |> List.filter (fun x -> ys |> List.contains x)")
        // FR0035 with its fix: a startup-built module binding probed in a loop;
        // private converts in place to a Set, a public one with another use
        // gains the HashSet companion
        withFree "StartupListProbe" [ "FR0035" ] (Gen.zip genWords (Gen.elements [ true; false ])) (fun (ws, priv) i ->
            let header = if priv then $"module private M{i} =" else $"module M{i} ="

            lines
                [
                    header
                    $"    let allowed{i} = [ {ws} ]"
                    if not priv then
                        $"    let count{i} = List.length allowed{i}"
                    $"    let f{i} (xs: string list) ="
                    "        for x in xs do"
                    $"            if List.contains x allowed{i} then ignore x"
                ])
        // FR0037: an expensive-by-design type constructed on every iteration
        withFree
            "ConstructionInLoop"
            [ "FR0037" ]
            (Gen.elements
                [
                    "let d = System.Collections.Concurrent.ConcurrentDictionary<int, int>()", "d.TryAdd(x, x) |> ignore"
                    "let o = System.Text.Json.JsonSerializerOptions()", "ignore (o.WriteIndented, x)"
                    "let c = new System.Net.Http.HttpClient()", "ignore (c.Timeout, x)"
                    // a non-literal pattern: FR0015 declines the hoist, so the note stands
                    "let r = Regex(string x)", "r.IsMatch \"a\" |> ignore"
                ])
            (fun (construct, use') i ->
                lines
                    [
                        $"let f{i} (xs: int list) ="
                        "    for x in xs do"
                        $"        {construct}"
                        $"        {use'}"
                    ])
        // FR0050: a floating accumulator summed in a loop becomes List.sum / sumBy
        withFree
            "FloatSum"
            [ "FR0050" ]
            (Gen.zip (Gen.elements [ "float list"; "float[]"; "float seq" ]) (Gen.elements [ "x"; "x * x"; "x + 1.0" ]))
            (fun (ty, term) i ->
                lines
                    [
                        $"let f{i} (xs: {ty}) ="
                        $"    let mutable total{i} = 0.0"
                        "    for x in xs do"
                        $"        total{i} <- total{i} + {term}"
                        $"    total{i} * 2.0"
                    ])
        // FR0050: a general combine becomes a fold
        withFree "MaxFold" [ "FR0050" ] genSmall (fun n i ->
            lines
                [
                    $"let f{i} (xs: int list) ="
                    $"    let mutable best{i} = {n}"
                    "    for x in xs do"
                    $"        best{i} <- max best{i} (x - 7)"
                    $"    best{i}"
                ])
        // FR0051: appending one element to the accumulator per iteration
        withFree
            "QuadraticAppend"
            [ "FR0051" ]
            (Gen.zip
                genSmall
                (Gen.elements
                    [
                        "int list", "[]", "acc @ [ x ]"
                        "int list", "[]", "List.append acc [ x ]"
                        "int[]", "[||]", "Array.append acc [| x |]"
                    ]))
            (fun (n, (ty, empty, append)) i ->
                let append = append.Replace("acc", $"acc{i}")

                lines
                    [
                        $"let f{i} (xs: int list) ="
                        $"    let mutable acc{i}: {ty} = {empty}"
                        "    for x in xs do"
                        $"        if x > {n} then acc{i} <- {append}"
                        $"    acc{i}"
                    ])
        // FR0051: a string built with + inside a while loop, the Str kind of the note
        fixed' "QuadraticString" [ "FR0051" ] (fun i ->
            lines
                [
                    $"let f{i} (next: unit -> string option) ="
                    $"    let mutable acc{i} = \"\""
                    $"    let mutable go{i} = true"
                    $"    while go{i} do"
                    "        match next () with"
                    $"        | Some s -> acc{i} <- acc{i} + s"
                    $"        | None -> go{i} <- false"
                    $"    acc{i}"
                ])
        // FR0107: a boolean flag raised in a loop is exists; lowered, forall
        withFree
            "FlagLoop"
            [ "FR0107" ]
            (Gen.zip
                genSmall
                (Gen.elements
                    [
                        "int list", "false", ">", "true"
                        "int[]", "false", ">", "true"
                        "int list", "true", "<", "false"
                    ]))
            (fun (n, (ty, init, cmp, set)) i ->
                lines
                    [
                        $"let f{i} (xs: {ty}) ="
                        $"    let mutable found{i} = {init}"
                        "    for x in xs do"
                        $"        if x {cmp} {n} then found{i} <- {set}"
                        $"    found{i}"
                    ])
        // FR0156: a ResizeArray filled Add by Add and drained as a list
        withFree
            "AccumulatorFill"
            [ "FR0156" ]
            (Gen.zip genSmall (Gen.elements [ "List.ofSeq acc"; "Seq.toList acc"; "acc |> List.ofSeq" ]))
            (fun (n, drain) i ->
                let drain = drain.Replace("acc", $"acc{i}")

                lines
                    [
                        $"let f{i} (xs: int list) ="
                        $"    let acc{i} = ResizeArray<int>()"
                        ""
                        "    for x in xs do"
                        $"        if x > {n} then"
                        $"            acc{i}.Add(x * 2)"
                        ""
                        $"    {drain}"
                    ])
        // FR0156: a mutable list appended one element per iteration, or consed
        // and reversed, and only read after - the list expression; FR0050
        // leaves the combine alone (a fold would keep the copy)
        withFree
            "MutableListFill"
            [ "FR0156"; "!FR0050" ]
            (Gen.zip
                genSmall
                (Gen.elements
                    [
                        "acc <- acc @ [ x * 2 ]", "acc"
                        "acc <- List.append acc [ x * 2 ]", "List.sum acc"
                        "acc <- x * 2 :: acc", "List.rev acc"
                    ]))
            (fun (n, (feed, drain)) i ->
                let feed = feed.Replace("acc", $"acc{i}")
                let drain = drain.Replace("acc", $"acc{i}")

                lines
                    [
                        $"let f{i} (xs: int list) ="
                        $"    let mutable acc{i} = []"
                        ""
                        "    for x in xs do"
                        $"        if x > {n} then"
                        $"            {feed}"
                        ""
                        $"    {drain}"
                    ])
        // FR0156 must stay quiet: a consed list read without the reverse
        // is backwards, and a list assigned after its loops is still
        // being built (FR0051's note either way)
        withFree
            "MutableListKept"
            [ "!FR0156" ]
            (Gen.zip genSmall (Gen.elements [ "acc <- x :: acc", "acc"; "acc <- acc @ [ x ]", "acc <- []\n    acc" ]))
            (fun (n, (feed, drain)) i ->
                let feed = feed.Replace("acc", $"acc{i}")
                let drain = drain.Replace("acc", $"acc{i}")

                lines
                    [
                        $"let f{i} (xs: int list) ="
                        $"    let mutable acc{i} = []"
                        "    for x in xs do"
                        $"        if x > {n} then {feed}"
                        $"    {drain}"
                    ])
        // FR0158: a while loop stepping a mutable index while a condition holds
        withFree
            "IndexScan"
            [ "FR0158" ]
            (Gen.elements
                [
                    "0", "IDX < lines.Length && lines.[IDX].Trim() = \"\"", "+"
                    "lines.Length - 1", "IDX >= 0 && lines.[IDX] = \"\"", "-"
                ])
            (fun (init, cond, step) i ->
                let cond = cond.Replace("IDX", $"line{i}")

                lines
                    [
                        $"let f{i} (lines: string[]) ="
                        $"    let mutable line{i} = {init}"
                        ""
                        $"    while {cond} do"
                        $"        line{i} <- line{i} {step} 1"
                        ""
                        $"    line{i}"
                    ])
        // FR0071: a pure binding that depends on nothing in the loop, hoisted above it
        withFree
            "LoopInvariant"
            [ "FR0071" ]
            (Gen.zip genSmall (Gen.elements [ "for x in xs do"; "for x = 0 to 10 do" ]))
            (fun (n, loop) i ->
                lines
                    [
                        $"let f{i} (a: int) (xs: int list) ="
                        $"    {loop}"
                        $"        let c{i} = a + {n}"
                        $"        ignore (x + c{i})"
                    ])
        // FR0071: the same inside a collection-function lambda
        withFree "LoopInvariantLambda" [ "FR0071" ] genSmall (fun n i ->
            lines
                [
                    $"let f{i} (a: int) (xs: int list) ="
                    "    xs"
                    "    |> List.map (fun x ->"
                    $"        let c{i} = a + {n}"
                    $"        x + c{i})"
                ])
        // FR0028: an IQueryable enumerated inside another loop, one query per outer element
        withFree
            "QueryInLoop"
            [ "FR0028" ]
            (Gen.elements [ "for x in xs do"; "xs |> List.iter (fun x ->" ])
            (fun outer i ->
                let close = if outer.EndsWith "->" then ")" else ""

                lines
                    [
                        $"let f{i} (q: System.Linq.IQueryable<int>) (xs: int list) ="
                        $"    {outer}"
                        "        for p in q do"
                        $"            ignore (x + p){close}"
                    ])
        // FR0141: a while loop that carries state by mutation and leaves through a flag
        withFree "GenerativeLoop" [ "FR0141" ] genSmall (fun n i ->
            lines
                [
                    $"let f{i} (model: int) (limit: int) ="
                    $"    let generated{i} = ResizeArray<int>()"
                    $"    let mutable cache{i} = 0"
                    $"    let mutable stopped{i} = false"
                    $"    while not stopped{i} && generated{i}.Count < limit do"
                    $"        let next = model + cache{i}"
                    $"        cache{i} <- next"
                    $"        if next = {n} then stopped{i} <- true"
                    $"        else generated{i}.Add next"
                    $"    generated{i}"
                ])
        // FR0104: a singleton appended to the accumulator on every recursive call
        withFree
            "RecursiveAppend"
            [ "FR0104" ]
            (Gen.elements [ "acc @ [ x ]"; "List.append acc [ x ]" ])
            (fun append i ->
                lines
                    [
                        $"let rec collect{i} (keep: int -> bool) (acc: int list) (xs: int list) ="
                        "    match xs with"
                        "    | [] -> acc"
                        $"    | x :: rest when keep x -> collect{i} keep ({append}) rest"
                        $"    | _ :: rest -> collect{i} keep acc rest"
                    ])
        // FR0058: a recursive function re-entering itself through seq { }
        withFree "RecursiveSeq" [ "FR0058" ] genSmall (fun stop i ->
            lines
                [
                    $"let rec countDown{i} (n: int) = seq {{"
                    "    yield n"
                    $"    if n > {stop} then yield! countDown{i} (n - 1)"
                    "    yield -1"
                    $"}}"
                ])
        // FR0058: a member is implicitly recursive; the tree walk through seq { }
        fixed' "RecursiveSeqMember" [ "FR0058" ] (fun i ->
            lines
                [
                    $"type Node{i}(children: Node{i} list) ="
                    $"    member this.Descendants() : seq<int> = seq {{"
                    "        yield 1"
                    "        for c in children do"
                    "            yield! c.Descendants()"
                    $"    }}"
                ])
        // FR0131: every self-call in tail position gains [<TailCall>]
        withFree "RecTailCall" [ "FR0131" ] (Gen.elements [ true; false ]) (fun matchLambda i ->
            if matchLambda then
                lines
                    [
                        $"let rec sum{i} (acc: int) ="
                        "    function"
                        "    | [] -> acc"
                        $"    | h :: t -> sum{i} (acc + h) t"
                    ]
            else
                lines
                    [
                        $"let rec sum{i} (acc: int) (xs: int list) ="
                        "    match xs with"
                        "    | [] -> acc"
                        $"    | h :: t -> sum{i} (acc + h) t"
                    ])
        // FR0116: a member referencing no sibling leaves the let rec group
        withFree "RecGroupExtract" [ "FR0116" ] genSmall (fun n i ->
            lines
                [
                    $"let rec f{i} (x: int) : int = if x = 0 then 0 else h{i} (x - 1) + x"
                    $"and g{i} (y: int) = y + {n}"
                    $"and h{i} (z: int) : int = if z = 0 then 0 else f{i} (z - 1) - z"
                ])
        // FR0116: the head references nobody, so the keywords swap in place
        withFree "RecGroupRecrown" [ "FR0116" ] genSmall (fun n i ->
            lines
                [
                    $"let rec helper{i} (y: int) = y + {n}"
                    $"and g{i} (x: int) : int = if x = 0 then helper{i} x else h{i} (x - 1)"
                    $"and h{i} (z: int) : int = if z = 0 then 0 else g{i} (z - 1)"
                ])
    ]

let family: Family =
    {
        Name = "Loops"
        Shapes = shapes
        Edits =
            fun c ->
                // a script has no later file, and the scope gate is the opt-in alone
                let contains, _ =
                    LoopPerf.findWith (fun _ -> false) (Visibility.apiChangesAllowed ()) (Some c.Check) c.Tree c.Source

                let folds, _ = Accumulation.find c.Tree c.Source c.Check

                [
                    for s in contains |> List.filter (fun s -> not s.Fix.IsEmpty) ->
                        "FR0035", [ for r, _, replacement in s.Fix -> edit "FR0035" r replacement ]
                    for s in folds -> "FR0050", [ edit "FR0050" s.Range s.ReplacementText ]
                    for s in Accumulation.findFlagLoops c.Tree c.Source c.Check ->
                        "FR0107", [ edit "FR0107" s.Range s.ReplacementText ]
                    for s in AccumulatorLoop.findWith false false c.Tree c.Source c.Check ->
                        "FR0156", [ for e in s.Edits -> edit "FR0156" e.Range e.Replacement ]
                    for s in IndexScan.find c.Tree c.Source c.Check ->
                        "FR0158", [ edit "FR0158" s.Range s.ReplacementText ]
                    for s in LoopInvariant.find c.Tree c.Source c.Check ->
                        "FR0071", [ for r, _, replacement in s.Edits -> edit "FR0071" r replacement ]
                    for s in RecTailCall.find c.Tree c.Source c.Check ->
                        "FR0131", [ edit "FR0131" (fst s.Fix) (snd s.Fix) ]
                    for s in RecGroup.find (Some c.Check) c.Tree c.Source ->
                        "FR0116",
                        edit "FR0116" s.InsertRange s.InsertText
                        :: [ for r in s.Removes -> edit "FR0116" r "" ]
                    for s in RecGroup.findHeadRecrowns (Some c.Check) c.Tree c.Source ->
                        "FR0116", [ edit "FR0116" s.LetRecRange "let"; edit "FR0116" s.AndRange "let rec" ]
                ]
        Notes =
            fun c ->
                let contains, constructions =
                    LoopPerf.findWith (fun _ -> false) (Visibility.apiChangesAllowed ()) (Some c.Check) c.Tree c.Source

                // a Regex construction FR0015 hoists gets its fix there, not this note
                let hoistedByRegexUsage =
                    if constructions |> List.exists (fun s -> s.TypeName = "Regex") then
                        RegexUsage.hoistedConstructions true c.Tree c.Source
                    else
                        []

                let noted =
                    constructions
                    |> List.filter (fun s ->
                        not (hoistedByRegexUsage |> List.exists (FSharp.Compiler.Text.Range.equals s.Range)))

                let _, quadratics = Accumulation.find c.Tree c.Source c.Check

                [
                    for s in contains |> List.filter (fun s -> s.Fix.IsEmpty) -> "FR0035", s.Range
                    for s in noted -> "FR0037", s.Range
                    for s in quadratics -> "FR0051", s.Range
                    for s in QueryInLoop.find c.Tree c.Source c.Check -> "FR0028", s.Range
                    for s in GenerativeLoop.find c.Tree c.Source -> "FR0141", s.Range
                    for s in RecursiveAppend.find c.Tree c.Source -> "FR0104", s.Range
                    for s in RecursiveSeq.find c.Tree c.Source -> "FR0058", s.Range
                ]
    }
