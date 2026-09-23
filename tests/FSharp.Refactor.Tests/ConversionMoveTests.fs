module FSharp.Refactor.Tests.ConversionMoveTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, check = parseAndCheck source
    ConversionMove.findWith (Some check) tree sourceText

/// Expect one suggestion; verify the fully patched source text and that it
/// still parses.
let private assertPatched (source: string) (expectedPatched: string) =
    match findIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``a length-preserving operation does not move into Seq`` () =
    // measured: `Seq.map g |> Seq.toList` runs 35% SLOWER than
    // `Seq.toList |> List.map g` (46k -> 62k ns/op at n=1000) for 12% less
    // allocation. The intermediate list does disappear, but Seq.toList then
    // builds the result through an enumerator with a virtual call per
    // element where List.map walked cons cells in a tight loop, and with a
    // map there is no smaller output to pay for the indirection
    assertNoSuggestion "module Test\nlet f g xs = xs |> Seq.toList |> List.map g"

[<Fact>]
let ``a size-reducing operation still moves into Seq`` () =
    // filter's output is smaller than its input, and that saving covers the
    // enumerator cost: -4% time, -13% allocation
    assertPatched
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.toList |> List.filter g"
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.filter g |> Seq.toList"

[<Fact>]
let ``ofSeq spelling is preserved when moved`` () =
    assertPatched
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> List.ofSeq |> List.filter g"
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.filter g |> List.ofSeq"

[<Fact>]
let ``seq-to-array does not move a map into Seq either`` () =
    // the destination module makes no difference to this: what costs is
    // running the map through Seq's enumerator. Measured, the rewrite is
    // ~6% slower for 2% less allocation
    assertNoSuggestion "module Test\nlet f g xs = xs |> Seq.toArray |> Array.map g"

[<Fact>]
let ``an operation is not moved out of Array into List`` () =
    // Array.choose runs over a contiguous block; List.choose would allocate
    // a cons cell per surviving element and then be walked to build the
    // array anyway, so the move is a pessimisation
    assertNoSuggestion "module Test\nlet f g xs = xs |> List.toArray |> Array.choose g"

[<Fact>]
let ``the Array-of-list spelling is blocked the same way`` () =
    assertNoSuggestion "module Test\nlet f g xs = xs |> Array.ofList |> Array.map g"

[<Fact>]
let ``an Array operation still moves into Seq where laziness removes the array`` () =
    // the seq is enumerated once either way; filtering first means the
    // unfiltered n-element array is never built at all
    assertPatched
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.toArray |> Array.filter g"
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.filter g |> Seq.toArray"

[<Fact>]
let ``a consuming operation still drops a list-to-array conversion`` () =
    // here the conversion disappears entirely, which is a win either way
    assertPatched
        "module Test\nlet f xs = xs |> List.toArray |> Array.length"
        "module Test\nlet f xs = xs |> List.length"

[<Fact>]
let ``array-to-list conversion moves past map`` () =
    assertPatched
        "module Test\nlet f g xs = xs |> Array.toList |> List.map g"
        "module Test\nlet f g xs = xs |> Array.map g |> Array.toList"

[<Fact>]
let ``conversion before length is dropped`` () =
    assertPatched "module Test\nlet f xs = xs |> Seq.toList |> List.length" "module Test\nlet f xs = xs |> Seq.length"

[<Fact>]
let ``conversion before iter is dropped`` () =
    assertPatched
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.toList |> List.iter g"
        "module Test\nlet f g (xs: ResizeArray<int>) = xs |> Seq.iter g"

[<Fact>]
let ``mid-pipeline segment is rewritten in place`` () =
    assertPatched
        "module Test\nlet f h k xs = xs |> h |> Seq.toList |> List.filter (fun v -> v > 1) |> k"
        "module Test\nlet f h k xs = xs |> h |> Seq.filter (fun v -> v > 1) |> Seq.toList |> k"

[<Fact>]
let ``multi-line pipeline is rewritten and collapses two stages`` () =
    assertPatched
        "module Test\nlet f g (xs: ResizeArray<int>) =\n    xs\n    |> Seq.toList\n    |> List.filter g"
        "module Test\nlet f g (xs: ResizeArray<int>) =\n    xs\n    |> Seq.filter g\n    |> Seq.toList"

[<Fact>]
let ``lambda argument text is preserved verbatim`` () =
    assertPatched
        "module Test\nlet f xs = xs |> Seq.toList |> List.filter (fun v -> v > 1)"
        "module Test\nlet f xs = xs |> Seq.filter (fun v -> v > 1) |> Seq.toList"

[<Fact>]
let ``operation from a different module is not rewritten`` () =
    assertNoSuggestion "module Test\nlet f g xs = xs |> Seq.toList |> Array.map g"

[<Fact>]
let ``non-whitelisted operation is not rewritten`` () =
    // List.skip and Seq.skip throw different exception types on short input
    assertNoSuggestion "module Test\nlet f xs = xs |> Seq.toList |> List.skip 1"

[<Fact>]
let ``groupBy is not rewritten`` () =
    // Seq.groupBy yields seq-valued groups: the element type would change
    assertNoSuggestion "module Test\nlet f (g: int -> int) xs = xs |> Seq.toList |> List.groupBy g"

[<Fact>]
let ``sortBy does not move into Seq`` () =
    // a sort cannot avoid materialising, so moving it into Seq removes no
    // intermediate at all — it only adds the enumerator on the way out.
    // Into Array the sort family is refused separately, for stability
    assertNoSuggestion "module Test\nlet f (g: int -> int) xs = xs |> Seq.toList |> List.sortBy g"

[<Fact>]
let ``rev conversion moves`` () =
    assertPatched
        "module Test\nlet f xs = xs |> Array.toList |> List.rev"
        "module Test\nlet f xs = xs |> Array.rev |> Array.toList"

[<Fact>]
let ``conversion before exists is dropped`` () =
    assertPatched
        "module Test\nlet f (p: int -> bool) (xs: ResizeArray<int>) = xs |> Seq.toList |> List.exists p"
        "module Test\nlet f (p: int -> bool) (xs: ResizeArray<int>) = xs |> Seq.exists p"

[<Fact>]
let ``a short-circuiting consumer keeps the conversion over a source whose enumeration runs user code`` () =
    // `Seq.toList |> List.exists` read every element; `Seq.exists` stops at
    // the first hit and skips the `printfn` for the rest (CR0020 asks the
    // same of its source before Any/First/Contains)
    let typed (source: string) =
        let tree, sourceText, check = parseAndCheck source
        ConversionMove.findWith (Some check) tree sourceText

    assertNoSuggestion
        "module Test\nlet f (xs: int list) =\n    seq { for x in xs do printfn \"%d\" x; yield x } |> Seq.toList |> List.exists (fun x -> x > 2)"

    assertNoSuggestion
        "module Test\nlet log (x: int) = printfn \"%d\" x; x\nlet f (xs: int list) = xs |> Seq.map log |> Seq.toList |> List.exists (fun x -> x > 2)"

    // parse-only, a user function returning a sequence cannot be cleared
    assertNoSuggestion "module Test\nlet f (read: unit -> int seq) = read () |> Seq.toList |> List.tryHead"

    // the same shapes under a consumer that reads everything are still fixed
    assertPatched
        "module Test\nlet log (x: int) = printfn \"%d\" x; x\nlet f (xs: int list) = xs |> Seq.map log |> Seq.toList |> List.length"
        "module Test\nlet log (x: int) = printfn \"%d\" x; x\nlet f (xs: int list) = xs |> Seq.map log |> Seq.length"

    // a name, a literal, an eager stage: pure by shape
    assertPatched
        "module Test\nlet f (xs: int[]) = xs |> Array.map ((+) 1) |> Seq.toList |> List.tryHead"
        "module Test\nlet f (xs: int[]) = xs |> Array.map ((+) 1) |> Seq.tryHead"

    // typed: a lazy stage over FSharp.Core's own functions is cleared
    match
        typed "module Test\nlet f (xs: int list) = xs |> Seq.map ((+) 1) |> Seq.toList |> List.exists (fun x -> x > 2)"
    with
    | [ s ] -> Assert.Contains("Seq.exists", s.ReplacementText)
    | other -> failwithf "Expected the typed proof to clear the source, got %A" other

    // typed: a user callback in the lazy stage is not
    Assert.Empty(
        typed
            "module Test\nlet log (x: int) = printfn \"%d\" x; x\nlet f (xs: int list) = xs |> Seq.map log |> Seq.toList |> List.exists (fun x -> x > 2)"
    )

[<Fact>]
let ``conversion before isEmpty is dropped`` () =
    assertPatched "module Test\nlet f xs = xs |> Seq.toList |> List.isEmpty" "module Test\nlet f xs = xs |> Seq.isEmpty"

[<Fact>]
let ``conversion before fold is dropped`` () =
    assertPatched
        "module Test\nlet f xs = xs |> Seq.toList |> List.fold (+) 0"
        "module Test\nlet f xs = xs |> Seq.fold (+) 0"

[<Fact>]
let ``conversion toward seq is never moved`` () =
    // rewriting would turn eager code lazy
    assertNoSuggestion "module Test\nlet f g xs = xs |> Seq.ofList |> Seq.map g"

[<Fact>]
let ``pipeline without conversion is not rewritten`` () =
    assertNoSuggestion "module Test\nlet f g xs = xs |> List.map g |> List.filter g"

[<Fact>]
let ``collect is not moved across a List-Array boundary`` () =
    // review regression: List.collect needs a list-returning mapper
    assertNoSuggestion "module Test\nlet f (g: int -> int[]) xs = xs |> List.toArray |> Array.collect g"

[<Fact>]
let ``collect moves for Seq-sourced conversions`` () =
    assertPatched
        "module Test\nlet f (g: int -> int list) (xs: ResizeArray<int>) = xs |> Seq.toList |> List.collect g"
        "module Test\nlet f (g: int -> int list) (xs: ResizeArray<int>) = xs |> Seq.collect g |> Seq.toList"

[<Fact>]
let ``sort family is not moved across an Array boundary`` () =
    // review regression: Array sorts are unstable, Seq/List sorts are stable
    assertNoSuggestion "module Test\nlet f (g: int -> int) xs = xs |> Seq.toArray |> Array.sortBy g"

[<Fact>]
let ``item is not treated as consuming`` () =
    // review regression: Array.item and List.item throw different exception types
    assertNoSuggestion "module Test\nlet f xs = xs |> Seq.toList |> List.item 1"

[<Fact>]
let ``a mutating operation keeps its eager conversion`` () =
    // SQLProvider's shape, and 19 of its tests: the sequence is built FROM
    // the dictionary the body assigns into, so Seq.toList is what keeps
    // enumeration and mutation apart. Dropping it throws "Collection was
    // modified" at run time - and it compiles, so no build check sees it
    assertNoSuggestion
        "module Test\nopen System.Collections.Generic\nlet f (d: Dictionary<int,int>) (items: seq<int * int>) =\n    items |> Seq.toList |> List.iter (fun (k, v) -> d.[k] <- v)"

[<Fact>]
let ``a non-mutating operation still moves`` () =
    // the guard must not cost the ordinary case
    assertPatched
        "module Test\nlet f (xs: ResizeArray<int>) = xs |> Seq.toList |> List.iter (printfn \"%d\")"
        "module Test\nlet f (xs: ResizeArray<int>) = xs |> Seq.iter (printfn \"%d\")"

[<Fact>]
let ``a module-level collection is never enumerated lazily under a callback`` () =
    // `register` may write into the very collection the sequence reads —
    // nothing in this file can tell — and the eager copy is what kept
    // that safe. A collection owned by the function cannot be reached
    // by a function it did not receive it from, so only a wider-scoped
    // source is gated out
    assertNoSuggestion
        "module Test\nopen System.Collections.Generic\nlet registry = Dictionary<int, int>()\nlet register k = registry.[k] <- 1\nlet f () = registry.Keys |> Seq.toList |> List.iter register"

[<Fact>]
let ``a module-level collection under a callback-free operation still moves`` () =
    // List.length takes no function: nothing can write during the walk
    assertPatched
        "module Test\nlet registry = ResizeArray<int>()\nlet f () = registry |> Seq.toList |> List.length"
        "module Test\nlet registry = ResizeArray<int>()\nlet f () = registry |> Seq.length"

[<Fact>]
let ``a local collection written by a local closure keeps its conversion`` () =
    // the write is not in the operation but in a closure the function
    // itself defines: the whole function body is what gets read for `<-`
    assertNoSuggestion
        "module Test\nopen System.Collections.Generic\nlet f () =\n    let d = Dictionary<int, int>()\n    let register k = d.[k] <- 1\n    d.Keys |> Seq.toList |> List.iter register"

[<Fact>]
let ``a local collection under a pure callback moves`` () =
    assertPatched
        "module Test\nlet f () =\n    let xs = ResizeArray<int>()\n    xs |> Seq.toList |> List.iter (printfn \"%d\")"
        "module Test\nlet f () =\n    let xs = ResizeArray<int>()\n    xs |> Seq.iter (printfn \"%d\")"

[<Fact>]
let ``a list literal source is already materialised`` () =
    // the source being in hand changes nothing about the map's cost through
    // Seq; a size-reducing operation is what earns the move
    assertPatched
        "module Test\nlet f g = [ 1; 2; 3 ] |> Seq.toArray |> Array.filter g"
        "module Test\nlet f g = [ 1; 2; 3 ] |> Seq.filter g |> Seq.toArray"

[<Fact>]
let ``writes BEFORE the pipeline do not stop a pure callback moving`` () =
    // FsRocket's checkTrooperHits: the array is assigned into in a loop,
    // then filtered with a lambda that reads only. Only what runs during
    // the walk matters, and reading the whole function for `<-` refused
    // this — the ordinary imperative shape
    assertPatched
        "module Test\ntype E = { Dead: bool }\nlet f (input: E[]) =\n    let es = Array.copy input\n    for i in 0 .. es.Length - 1 do\n        if es[i].Dead then\n            es[i] <- { Dead = true }\n    es |> Array.toList |> List.filter (fun e -> not e.Dead)"
        "module Test\ntype E = { Dead: bool }\nlet f (input: E[]) =\n    let es = Array.copy input\n    for i in 0 .. es.Length - 1 do\n        if es[i].Dead then\n            es[i] <- { Dead = true }\n    es |> Array.filter (fun e -> not e.Dead) |> Array.toList"

[<Fact>]
let ``a callback handed the collection itself keeps the conversion`` () =
    // `List.iter (register es)` gives an outside function the very
    // collection being walked
    assertNoSuggestion
        "module Test\nlet register (xs: ResizeArray<int>) (x: int) = xs.Add x\nlet f () =\n    let es = ResizeArray<int>()\n    es |> Seq.toList |> List.iter (register es)"

// ---- a source that is already the target kind (fsharplint) ----

[<Fact>]
let ``an array-returning method feeding toArray is already an array`` () =
    // fsharplint: `identifier.idText.Split('|') |> Seq.toArray |> Array.filter ..`
    // became a lazy Seq.filter over an input that was an array all along
    assertNoSuggestion
        "module Test\nlet f (s: string) = s.Split('|') |> Seq.toArray |> Array.filter (fun p -> p <> \"\")"

[<Fact>]
let ``an array literal feeding toArray is already an array`` () =
    assertNoSuggestion "module Test\nlet f g = [| 1; 2; 3 |] |> Seq.toArray |> Array.map g"

[<Fact>]
let ``the target module's own output feeding the conversion is already materialised`` () =
    assertNoSuggestion
        "module Test\nlet f g (xs: int[]) = xs |> Array.map g |> Seq.toArray |> Array.filter (fun x -> x > 0)"

[<Fact>]
let ``a list literal feeding toList is already a list`` () =
    assertNoSuggestion "module Test\nlet f g = [ 1; 2; 3 ] |> Seq.toList |> List.map g"

[<Fact>]
let ``a consuming operation over an array-returning method keeps the array`` () =
    // dropping the copy would leave `Seq.length` walking what
    // `Array.length` reads in O(1)
    assertNoSuggestion "module Test\nlet f (s: string) = s.Split(',') |> Seq.toArray |> Array.length"

[<Fact>]
let ``a plain identifier source still moves past the operation`` () =
    assertPatched
        "module Test\nlet f (xs: seq<int>) = xs |> Seq.toArray |> Array.filter (fun x -> x > 0)"
        "module Test\nlet f (xs: seq<int>) = xs |> Seq.filter (fun x -> x > 0) |> Seq.toArray"

[<Fact>]
let ``a lazy source keeps its conversion under a callback with effects`` () =
    // `File.ReadLines` is lazy: `Seq.toList` read the whole file before the
    // first append; `Seq.iter` would interleave the appends with the read
    // (the file still open), and a filter/choose stage the same
    let typed (source: string) =
        let tree, sourceText, check = parseAndCheck source
        ConversionMove.findWith (Some check) tree sourceText

    Assert.Empty(
        typed
            "module Test\nopen System.IO\nlet f (path: string) =\n    let lines = File.ReadLines path\n    lines |> Seq.toList |> List.iter (fun l -> File.AppendAllText(path, l))"
    )

    Assert.Empty(
        typed
            "module Test\nopen System.IO\nlet f (path: string) =\n    let lines = File.ReadLines path\n    lines |> Seq.toArray |> Array.filter (fun l -> File.Exists l)"
    )

    // parse-only, nothing proves the source materialised or the callback pure
    assertNoSuggestion
        "module Test\nlet f (path: string) =\n    let lines = System.IO.File.ReadLines path\n    lines |> Seq.toList |> List.iter (fun l -> System.IO.File.AppendAllText(path, l))"

    // a pure callback over the lazy source still moves
    match
        typed
            "module Test\nopen System.IO\nlet f (path: string) =\n    let lines = File.ReadLines path\n    lines |> Seq.toArray |> Array.filter (fun l -> l.Length > 2)"
    with
    | [ s ] -> Assert.Contains("Seq.filter", s.ReplacementText)
    | other -> failwithf "Expected a pure callback to move, got %A" other

    // a materialised source (typed) keeps the move under an effectful callback
    match
        typed
            "module Test\nopen System.IO\nlet f (path: string) (lines: ResizeArray<string>) =\n    lines |> Seq.toList |> List.iter (fun l -> File.AppendAllText(path, l))"
    with
    | [ s ] -> Assert.Contains("Seq.iter", s.ReplacementText)
    | other -> failwithf "Expected a materialised source to move, got %A" other
