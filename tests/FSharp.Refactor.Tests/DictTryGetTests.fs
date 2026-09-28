module FSharp.Refactor.Tests.DictTryGetTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DictTryGet.find tree sourceText checkResults

let private assertSingleSuggestion (source: string) (expectedReplacement: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``single-line contains-then-index becomes TryGetValue`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then d.[k] else 0
            """)
        "match d.TryGetValue k with | true, value -> value | false, _ -> 0"

[<Fact>]
let ``multi-line if becomes a three-line match`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k =
                if d.ContainsKey k then
                    d.[k] + 1
                else
                    0
            """)
        (fsharp
            """
            match d.TryGetValue k with
                | true, value -> value + 1
                | false, _ -> 0
            """)

[<Fact>]
let ``indexer inside a larger then-branch is substituted`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then string d.[k] else "?"
            """)
        "match d.TryGetValue k with | true, value -> string value | false, _ -> \"?\""

[<Fact>]
let ``fsharp6 indexing syntax is substituted`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then d[k] else 0
            """)
        "match d.TryGetValue k with | true, value -> value | false, _ -> 0"

[<Fact>]
let ``dotted container path works`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            type S = { Cache: Dictionary<string, int> }
            let f (s: S) k = if s.Cache.ContainsKey k then s.Cache.[k] else 0
            """)
        "match s.Cache.TryGetValue k with | true, value -> value | false, _ -> 0"

[<Fact>]
let ``concurrent dictionary is flagged as concurrent`` () =
    let source =
        fsharp
            """
            open System.Collections.Concurrent
            let f (d: ConcurrentDictionary<string, int>) k = if d.ContainsKey k then d.[k] else 0
            """

    match findIn source with
    | [ s ] -> Assert.True s.Concurrent
    | other -> failwithf "Expected exactly one concurrent suggestion, got %A" other

[<Fact>]
let ``fsharp Map gets the TryFind option idiom`` () =
    assertSingleSuggestion
        "let f (m: Map<string, int>) k = if m.ContainsKey k then m.[k] else 0"
        "match m.TryFind k with | Some value -> value | None -> 0"

[<Fact>]
let ``then-branch without the indexer is not rewritten`` () =
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then 1 else 0
            """
    )

[<Fact>]
let ``effectful key is not rewritten`` () =
    // the key expression was evaluated twice; collapsing to once could change behavior
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) (mk: unit -> string) = if d.ContainsKey (mk ()) then d.[mk ()] else 0
            """
    )

[<Fact>]
let ``branch already using the name value is not rewritten`` () =
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k (value: int) = if d.ContainsKey k then d.[k] + value else 0
            """
    )

[<Fact>]
let ``indexer with a different key is not substituted`` () =
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k j = if d.ContainsKey k then d.[j] else 0
            """
    )
// ---- harder cases: intermediate statements, false positives, forbidden substitutions ----

[<Fact>]
let ``multi-statement then-branch is left alone`` () =
    // intermediate commands between the lookup and the use: conservative skip
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k =
                if d.ContainsKey k then
                    let v = d.[k]
                    v * 2
                else
                    0
            """
    )

[<Fact>]
let ``compound condition is not rewritten`` () =
    // `d.ContainsKey k && other` cannot become a bare TryGetValue match
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k (go: bool) = if d.ContainsKey k && go then d.[k] else 0
            """
    )

[<Fact>]
let ``then-branch that mutates the dictionary first is not rewritten`` () =
    // sequential branch: substituting would change what the indexer sees
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then (d.Remove k |> ignore; d.[k]) else 0
            """
    )

[<Fact>]
let ``indexer text inside a string literal is not substituted`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = if d.ContainsKey k then sprintf "d.[k]=%d" d.[k] else "?"
            """)
        "match d.TryGetValue k with | true, value -> sprintf \"d.[k]=%d\" value | false, _ -> \"?\""

[<Fact>]
let ``shadowed container inside a lambda is not substituted`` () =
    // the lambda re-binds d; its d.[k] belongs to the shadow, so no rewrite
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) (d2: Dictionary<string, int>) k = if d.ContainsKey k then (fun (d: Dictionary<string, int>) -> d.[k]) d2 else 0
            """
    )

[<Fact>]
let ``similarly named container is not confused`` () =
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) (dd: Dictionary<string, int>) k = if d.ContainsKey k then dd.[k] else 0
            """
    )

// ---- FR0018 TryAdd ----

let private tryAddIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DictTryGet.findTryAdd tree sourceText checkResults

let private assertTryAdd (source: string) (expectedReplacement: string) =
    match tryAddIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one TryAdd suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``check-then-add on Dictionary becomes TryAdd`` () =
    assertTryAdd
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d.[k] <- v
            """)
        "d.TryAdd(k, v) |> ignore"

[<Fact>]
let ``check-then-add on ConcurrentDictionary is flagged as a race`` () =
    let source =
        fsharp
            """
            open System.Collections.Concurrent
            let f (d: ConcurrentDictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d.[k] <- v
            """

    match tryAddIn source with
    | [ s ] ->
        Assert.True s.Concurrent
        Assert.Equal("d.TryAdd(k, v) |> ignore", s.ReplacementText)
    | other -> failwithf "Expected exactly one concurrent TryAdd suggestion, got %A" other

[<Fact>]
let ``check-then-add stays where the framework has no Dictionary TryAdd`` () =
    // net48 / netstandard2.0: Dictionary<'K,'V>.TryAdd does not exist. The
    // legacy reference set is the machine's mscorlib: only a Windows script
    // compilation resolves it; elsewhere the fixture cannot typecheck
    if System.OperatingSystem.IsWindows() then
        let tree, sourceText, checkResults =
            parseAndCheckLegacyFramework (
                fsharp
                    """
                    open System.Collections.Generic
                    let f (d: Dictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d.[k] <- v
                    """
            )

        Assert.Empty(DictTryGet.findTryAdd tree sourceText checkResults)

[<Fact>]
let ``fsharp6 index-set syntax is recognized`` () =
    assertTryAdd
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d[k] <- v
            """)
        "d.TryAdd(k, v) |> ignore"

[<Fact>]
let ``update without the not-guard is an overwrite and stays`` () =
    Assert.Empty(
        tryAddIn (
            fsharp
                """
                open System.Collections.Generic
                let f (d: Dictionary<string, int>) k (v: int) = if d.ContainsKey k then d.[k] <- v
                """
        )
    )

[<Fact>]
let ``effectful value is not moved into TryAdd`` () =
    // TryAdd evaluates the value always; the original evaluated it only when absent
    Assert.Empty(
        tryAddIn (
            fsharp
                """
                open System.Collections.Generic
                let f (d: Dictionary<string, int>) k (mk: unit -> int) = if not (d.ContainsKey k) then d.[k] <- mk ()
                """
        )
    )

[<Fact>]
let ``check-then-add with an else branch stays`` () =
    Assert.Empty(
        tryAddIn (
            fsharp
                """
                open System.Collections.Generic
                let f (d: Dictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d.[k] <- v else d.[k] <- v + 1
                """
        )
    )

[<Fact>]
let ``mismatched key is not rewritten as TryAdd`` () =
    Assert.Empty(
        tryAddIn (
            fsharp
                """
                open System.Collections.Generic
                let f (d: Dictionary<string, int>) k j (v: int) = if not (d.ContainsKey k) then d.[j] <- v
                """
        )
    )

[<Fact>]
let ``sorted dictionary lacks TryAdd and stays`` () =
    Assert.Empty(
        tryAddIn (
            fsharp
                """
                open System.Collections.Generic
                let f (d: SortedDictionary<string, int>) k (v: int) = if not (d.ContainsKey k) then d.[k] <- v
                """
        )
    )

// ---- match-on-ContainsKey form ----

[<Fact>]
let ``match on ContainsKey with interpolated indexer becomes TryGetValue`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) x = match d.ContainsKey x with | true -> $"hello {d[x]}" | false -> "not"
            """)
        "match d.TryGetValue x with | true, value -> $\"hello {value}\" | false, _ -> \"not\""

[<Fact>]
let ``match on ContainsKey with wildcard miss clause works`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = match d.ContainsKey k with | true -> d.[k] | _ -> 0
            """)
        "match d.TryGetValue k with | true, value -> value | false, _ -> 0"

[<Fact>]
let ``match with false clause first swaps the branches`` () =
    assertSingleSuggestion
        (fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k = match d.ContainsKey k with | false -> 0 | true -> d.[k]
            """)
        "match d.TryGetValue k with | true, value -> value | false, _ -> 0"

[<Fact>]
let ``match form on Map uses TryFind`` () =
    assertSingleSuggestion
        "let f (m: Map<string, int>) k = match m.ContainsKey k with | true -> m.[k] | false -> 0"
        "match m.TryFind k with | Some value -> value | None -> 0"

[<Fact>]
let ``match with a when-guard is not rewritten`` () =
    assertNoSuggestion (
        fsharp
            """
            open System.Collections.Generic
            let f (d: Dictionary<string, int>) k (go: bool) = match d.ContainsKey k with | true when go -> d.[k] | _ -> 0
            """
    )

[<Fact>]
let ``an elif chain peels one TryGetValue level per pass`` () =
    // the outer if rewrites alone; the elif comes along VERBATIM as the
    // fallthrough arm with its elif spelled back to if, which the next
    // fix-then-reanalyze pass rewrites in turn
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let f (mapped: Dictionary<string, obj>) =
                if mapped.ContainsKey "FragmentId" then
                    Some(mapped.["FragmentId"].ToString())
                elif mapped.ContainsKey "Id" then
                    Some(mapped.["Id"].ToString())
                else None
            """

    match findIn source with
    | [ s ] ->
        Assert.Contains("""match mapped.TryGetValue "FragmentId" with""", s.ReplacementText)
        Assert.Contains("| true, value -> Some(value.ToString())", s.ReplacementText)
        Assert.Contains("if mapped.ContainsKey \"Id\"", s.ReplacementText)
        Assert.DoesNotContain("elif", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched

        // second pass over the patched text peels the next level
        match findIn patched with
        | [ s2 ] ->
            Assert.Contains("""match mapped.TryGetValue "Id" with""", s2.ReplacementText)
            let patched2 = applyEdit patched s2.Range s2.ReplacementText
            assertTypechecks "Second pass" patched2
        | other -> failwithf "Expected the second level on pass two, got %A" other
    | other -> failwithf "Expected exactly one chain suggestion, got %A" other

// ---- FR0154 GetOrAdd ----

let private findGetOrAddIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DictTryGet.findGetOrAdd tree sourceText checkResults

let private assertGetOrAdd (source: string) (expectedReplacement: string) =
    match findGetOrAddIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one GetOrAdd suggestion, got %d: %A" (List.length other) other

let private assertNoGetOrAdd (source: string) = Assert.Empty(findGetOrAddIn source)

/// A ConcurrentDictionary<string, int> lookup with the given arms under
/// `match xs.TryGetValue key with`.
let private concurrentLookup (arms: string) =
    fsharp
        """
        open System.Collections.Concurrent
        let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
            match xs.TryGetValue key with

        """
    + arms

[<Fact>]
let ``TryGetValue then indexer store becomes GetOrAdd`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``fsharp6 index-set store becomes GetOrAdd`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs[key] <- res
                        res
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``TryAdd store becomes GetOrAdd`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.TryAdd(key, res) |> ignore
                        res
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``AddOrUpdate store returning the value becomes GetOrAdd`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.AddOrUpdate(key, res, fun _ _ -> res) |> ignore
                        res
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``a wildcard miss arm is accepted`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``the explicit miss arm may come first`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                    | true, x -> x
                """
        ))
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``a leading wildcard arm is not a miss arm`` () =
    // `_` first takes the hit case too; the compiler warns and the value is
    // always recomputed - not this rule's shape
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                    | true, x -> x
                """
        )
    )

[<Fact>]
let ``several lets move into the lambda body`` () =
    assertGetOrAdd
        (concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let a = compute ()
                        let res = a + 1
                        xs.[key] <- res
                        res
                """
        ))
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                        let a = compute ()
                        let res = a + 1
                        res)
            """)

[<Fact>]
let ``a match starting mid-line indents the body under the lambda`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
                let v = match xs.TryGetValue key with
                        | true, x -> x
                        | false, _ ->
                            let a = compute ()
                            let res = a + 1
                            xs.[key] <- res
                            res
                v + 1
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                                let a = compute ()
                                let res = a + 1
                                res)
            """)

[<Fact>]
let ``a comment after the last body line stays outside the replaced range`` () =
    // the arm ends at `res`; the comment follows the match's range and is
    // still there after the paren
    let source =
        concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let a = compute ()
                        let res = a + 1
                        xs.[key] <- res
                        res // computed once
                """
        )

    assertGetOrAdd
        source
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                        let a = compute ()
                        let res = a + 1
                        res)
            """)

    match findGetOrAddIn source with
    | [ s ] -> Assert.EndsWith("res) // computed once", applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a tuple key is parenthesised as the GetOrAdd argument`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string * int, int>) (a: string) (b: int) (compute: unit -> int) =
                match xs.TryGetValue((a, b)) with
                | true, x -> x
                | false, _ ->
                    let res = compute ()
                    xs.[(a, b)] <- res
                    res
            """)
        "xs.GetOrAdd((a, b), fun _ -> compute ())"

[<Fact>]
let ``a plain Dictionary has no GetOrAdd`` () =
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Generic
            let f (xs: Dictionary<string, int>) (key: string) (compute: unit -> int) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = compute ()
                    xs.[key] <- res
                    res
            """
    )

[<Fact>]
let ``a Task-valued cache gets the Lazy note and no fix`` () =
    // two concurrent misses start two tasks; GetOrAdd alone does not change
    // that, a Lazy value does - a design change, so the message alone
    match
        findGetOrAddIn (
            fsharp
                """
                open System.Collections.Concurrent
                open System.Threading.Tasks
                let f (xs: ConcurrentDictionary<string, Task<int>>) (key: string) (compute: unit -> Task<int>) =
                    match xs.TryGetValue key with
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        )
    with
    | [ s ] ->
        Assert.True s.Deferred
        Assert.Equal("xs.GetOrAdd(key, fun _ ->", s.Head)
        Assert.Equal(Some "compute ()", s.Factory)
        Assert.Equal(4, s.Range.StartLine)
    | other -> failwithf "Expected one deferred suggestion, got %A" other

[<Fact>]
let ``an Async-valued cache gets the Lazy note too`` () =
    match
        findGetOrAddIn (
            fsharp
                """
                open System.Collections.Concurrent
                let f (xs: ConcurrentDictionary<string, Async<int>>) (key: string) (compute: unit -> Async<int>) =
                    match xs.TryGetValue key with
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        )
    with
    | [ s ] -> Assert.True s.Deferred
    | other -> failwithf "Expected one deferred suggestion, got %A" other

[<Fact>]
let ``a Lazy-valued cache stays as it is`` () =
    // FR0152's subject once it sits behind GetOrAdd
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, Lazy<int>>) (key: string) (compute: unit -> int) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = lazy (compute ())
                    xs.[key] <- res
                    res
            """
    )

[<Fact>]
let ``a factory that calls something carries the Lazy hint`` () =
    match
        findGetOrAddIn (
            concurrentLookup (
                fsharp
                    """
                        | true, x -> x
                        | false, _ ->
                            let res = compute ()
                            xs.[key] <- res
                            res
                    """
            )
        )
    with
    | [ s ] ->
        Assert.False s.Deferred
        Assert.Equal(Some "compute ()", s.Factory)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a pure factory carries no Lazy hint`` () =
    match
        findGetOrAddIn (
            fsharp
                """
                open System.Collections.Concurrent
                let f (xs: ConcurrentDictionary<int, int>) (key: int) =
                    match xs.TryGetValue key with
                    | true, x -> x
                    | false, _ ->
                        let res = key * 2 + 1
                        xs.[key] <- res
                        res
                """
        )
    with
    | [ s ] ->
        Assert.False s.Deferred
        Assert.Equal(None, s.Factory)
        Assert.Equal("xs.GetOrAdd(key, fun _ -> key * 2 + 1)", s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a body of several lets carries no factory`` () =
    match
        findGetOrAddIn (
            concurrentLookup (
                fsharp
                    """
                        | true, x -> x
                        | false, _ ->
                            let a = compute ()
                            let res = a + 1
                            xs.[key] <- res
                            res
                    """
            )
        )
    with
    | [ s ] -> Assert.Equal(None, s.Factory)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a store under another key stays`` () =
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key + "!"] <- res
                        res
                """
        )
    )

[<Fact>]
let ``a store of another value stays`` () =
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res + 1
                        res
                """
        )
    )

[<Fact>]
let ``a hit arm that transforms the value stays`` () =
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | true, x -> x + 1
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        )
    )

[<Fact>]
let ``a statement after the store stays`` () =
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let res = compute ()
                        xs.[key] <- res
                        printfn "stored"
                        res
                """
        )
    )

[<Fact>]
let ``an arm reading a mutable local is not made a closure`` () =
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) =
                let mutable calls = 0
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = calls + 1
                    xs.[key] <- res
                    res
            """
    )

[<Fact>]
let ``an effectful key is not evaluated once in GetOrAdd`` () =
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (next: unit -> string) (compute: unit -> int) =
                match xs.TryGetValue(next ()) with
                | true, x -> x
                | false, _ ->
                    let res = compute ()
                    xs.[next ()] <- res
                    res
            """
    )

// ---- FR0154: layouts and closure limits ----

[<Fact>]
let ``a match in argument position keeps its body under the lambda`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
                string (match xs.TryGetValue key with
                        | true, x -> x
                        | false, _ ->
                            let a = compute ()
                            let res = a + 1
                            xs.[key] <- res
                            res)
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                                let a = compute ()
                                let res = a + 1
                                res)
            """)

[<Fact>]
let ``a match in an if branch is rewritten`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) (fresh: bool) =
                if fresh then
                    match xs.TryGetValue key with
                    | true, x -> x
                    | false, _ ->
                        let a = compute ()
                        let res = a + 1
                        xs.[key] <- res
                        res
                else
                    0
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                            let a = compute ()
                            let res = a + 1
                            res)
            """)

[<Fact>]
let ``a match inside a task is rewritten`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
                task {
                    let v =
                        match xs.TryGetValue key with
                        | true, x -> x
                        | false, _ ->
                            let res = compute ()
                            xs.[key] <- res
                            res

                    return v + 1
                }
            """)
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``a two-space body is shifted under the lambda`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
              match xs.TryGetValue key with
              | true, x -> x
              | false, _ ->
                let a = compute ()
                let res = a + 1
                xs.[key] <- res
                res
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                    let a = compute ()
                    let res = a + 1
                    res)
            """)

[<Fact>]
let ``a nested match in the body moves with its arms`` () =
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res =
                        match compute () with
                        | 0 -> 1
                        | n -> n
                    xs.[key] <- res
                    res
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                        let res =
                            match compute () with
                            | 0 -> 1
                            | n -> n
                        res)
            """)

[<Fact>]
let ``an arm reading a Span parameter is not made a closure`` () =
    // a byref-like value declared outside the arm cannot be captured
    assertNoGetOrAdd (
        fsharp
            """
            open System
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) (chars: ReadOnlySpan<char>) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = chars.Length
                    xs.[key] <- res
                    res
            """
    )

[<Fact>]
let ``a Span declared inside the arm moves with it`` () =
    // declared inside, it is a local of the lambda, which is fine
    assertGetOrAdd
        (fsharp
            """
            open System
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let span = key.AsSpan()
                    let res = span.Length
                    xs.[key] <- res
                    res
            """)
        (fsharp
            """
            xs.GetOrAdd(key, fun _ ->
                        let span = key.AsSpan()
                        let res = span.Length
                        res)
            """)

[<Fact>]
let ``an arm taking an address is not made a closure`` () =
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (key: string) =
                let mutable n = 1
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = System.Threading.Interlocked.Increment(&n)
                    xs.[key] <- res
                    res
            """
    )

[<Fact>]
let ``an obj-valued cache resolves to the factory overload`` () =
    // a lambda coerces to obj at a method call as well, and F# still
    // prefers the delegate conversion
    assertGetOrAdd
        (fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, obj>) (key: string) (compute: unit -> obj) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let res = compute ()
                    xs.[key] <- res
                    res
            """)
        "xs.GetOrAdd(key, fun _ -> compute ())"

[<Fact>]
let ``a key rebound inside the arm is another key`` () =
    // the store is matched by text; `key` there is the shadow
    assertNoGetOrAdd (
        concurrentLookup (
            fsharp
                """
                    | true, x -> x
                    | false, _ ->
                        let key = key + "!"
                        let res = compute ()
                        xs.[key] <- res
                        res
                """
        )
    )

[<Fact>]
let ``a container rebound inside the arm is another container`` () =
    assertNoGetOrAdd (
        fsharp
            """
            open System.Collections.Concurrent
            let f (xs: ConcurrentDictionary<string, int>) (other: ConcurrentDictionary<string, int>) (key: string) (compute: unit -> int) =
                match xs.TryGetValue key with
                | true, x -> x
                | false, _ ->
                    let xs = other
                    let res = compute ()
                    xs.[key] <- res
                    res
            """
    )
