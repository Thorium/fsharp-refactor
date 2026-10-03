/// FR0177 ConstantComparison, FR0178 EmptyOptionValue, FR0179 DiscardedUpdate.
module FSharp.Refactor.Tests.LogicRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0177 ConstantComparison ----

let private comparisonsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ConstantComparison.find tree sourceText checkResults

[<Fact>]
let ``FR0177: two different constants against one operand are always true or always false`` () =
    let source =
        fsharp
            """
            module M
            type Kind =
                | Loan
                | Invest
                | Other of int
            [<Literal>]
            let Required = "required"
            let a (status: string) = status <> "required" || status <> "optional"
            let b (kind: Kind) = kind = Loan && kind = Invest
            let c (status: string) (n: int) = status <> Required || n > 3 || "optional" <> status
            let d (order: {| Code: int |}) = order.Code = 1 && order.Code = 2
            """

    match comparisonsIn source with
    | [ a; b; c; d ] ->
        Assert.Equal(ConstantComparison.Verdict.AlwaysTrue, a.Verdict)
        Assert.Equal(("status <> \"required\"", "status <> \"optional\""), (a.First, a.Second))

        match a.OperatorFix with
        | Some(r, original, replacement) ->
            Assert.Equal(("||", "&&"), (original, replacement))
            let patched = applyEdit source r replacement
            Assert.Contains("status <> \"required\" && status <> \"optional\"", patched)
            assertTypechecks "Patched source" patched
        | None -> failwith "Expected the operator offer on a two-operand chain"

        Assert.Equal(ConstantComparison.Verdict.AlwaysFalse, b.Verdict)
        Assert.Equal(Some("&&", "||"), b.OperatorFix |> Option.map (fun (_, o, r) -> o, r))
        // a longer chain: swapping one operator would regroup it
        Assert.Equal(ConstantComparison.Verdict.AlwaysTrue, c.Verdict)
        Assert.True c.OperatorFix.IsNone
        Assert.Equal(ConstantComparison.Verdict.AlwaysFalse, d.Verdict)
    | other -> failwithf "Expected four findings, got %A" other

[<Fact>]
let ``FR0177: one bound on both strict sides is always false`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (created: DateTime) (limit: DateTime) = created > limit && created < limit
            let b (x: int) (e: int) (flag: bool) = x >= e && flag && e > x
            let c (x: int) = x = 3 && x <> 3
            """

    match comparisonsIn source with
    | [ a; b; c ] as all ->
        Assert.All(
            all,
            (fun s ->
                Assert.Equal(ConstantComparison.Verdict.AlwaysFalse, s.Verdict)
                Assert.True s.OperatorFix.IsNone)
        )

        Assert.Equal(("created > limit", "created < limit"), (a.First, a.Second))
        Assert.Equal(("x >= e", "e > x"), (b.First, b.Second))
        Assert.Equal(("x = 3", "x <> 3"), (c.First, c.Second))
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0177: sound chains, equal constants, calls and other operands stay quiet`` () =
    let source =
        fsharp
            """
            module M
            [<Literal>]
            let One = 1
            [<Literal>]
            let Uno = 1
            let next () = 1
            let a (status: string) = status <> "required" && status <> "optional"
            let b (status: string) = status = "required" || status = "optional"
            let c (x: int) (lo: int) (hi: int) = x > lo && x < hi
            let d (x: int) (e: int) = x >= e && x <= e
            let e (x: int) = x <> One || x <> Uno
            let f (x: int) (y: int) = x <> 1 || y <> 2
            let g () = next () <> 1 || next () <> 2
            let h (x: int) (other: int) = x <> other || x <> 2
            let i (x: int) (e: int) = x > e || x < e
            """

    Assert.Empty(comparisonsIn source)

// ---- FR0178 EmptyOptionValue ----

let private emptyReadsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    EmptyOptionValue.find tree sourceText checkResults

[<Fact>]
let ``FR0178: Value read in the branch where the option is empty is noted`` () =
    let source =
        fsharp
            """
            module M
            type Payment = { ItemRef: System.Guid voption; Note: string option }
            let a (payment: Payment) =
                if payment.ItemRef.IsSome then
                    async { return None }
                else
                    let itemRef = payment.ItemRef.Value
                    async { return Some itemRef }
            let b (x: int option) = if x.IsNone then x.Value + 1 else 0
            let c (x: int option) = if not x.IsSome then string x.Value else ""
            let d (x: int option) = if x = None then x.Value else 0
            let e (x: int option) = if Option.isSome x then 0 else x.Value
            let f (payment: Payment) = if payment.Note <> None then 0 else payment.Note.Value.Length
            """

    match emptyReadsIn source with
    | [ a; b; c; d; e; f ] ->
        Assert.Equal(("payment.ItemRef", "payment.ItemRef.IsSome"), (a.Receiver, a.Test))
        Assert.Equal("x", b.Receiver)
        Assert.Equal("not x.IsSome", c.Test)
        Assert.Equal("x = None", d.Test)
        Assert.Equal("Option.isSome x", e.Test)
        Assert.Equal("payment.Note", f.Receiver)
    | other -> failwithf "Expected six findings, got %A" other

[<Fact>]
let ``FR0178: the right way round, a refill, a second test, a lambda and another type stay quiet`` () =
    let source =
        fsharp
            """
            module M
            type Holder() =
                member val Slot: int option = None with get, set
            type Box() =
                member _.IsSome = false
                member _.Value = 1
            let a (x: int option) = if x.IsSome then x.Value else 0
            let b (x: int option) = if x.IsNone then 0 else x.Value
            let c (h: Holder) =
                if h.Slot.IsNone then
                    h.Slot <- Some 1
                    h.Slot.Value
                else
                    0
            let d (h: Holder) (load: unit -> unit) =
                if h.Slot.IsNone then
                    load ()
                    if h.Slot.IsSome then h.Slot.Value else 0
                else
                    1
            let d2 (h: Holder) (load: unit -> unit) =
                if h.Slot.IsNone then
                    load ()
                    h.Slot.Value
                else
                    1
            let e (x: int option) = if x.IsNone then (fun () -> x.Value) else (fun () -> 0)
            let f (b: Box) = if b.IsSome then 0 else b.Value
            let g (x: int option) (y: int option) = if x.IsNone then y.Value else 0
            let h (x: int option) (y: int option) = if x.IsNone && y.IsSome then y.Value else 0
            """

    Assert.Empty(emptyReadsIn source)

// ---- FR0179 DiscardedUpdate ----

let private discardedUpdatesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DiscardedUpdate.find tree sourceText checkResults

[<Fact>]
let ``FR0179: an update of a Map, a Set or an immutable collection handed to ignore is noted`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Immutable
            let a (index: Map<string, int>) = index.Add("k", 1) |> ignore
            let b (index: Map<string, int>) = Map.add "k" 1 index |> ignore
            let c (seen: Set<int>) = ignore (seen.Add 1)
            let d (seen: Set<int>) = seen |> Set.remove 1 |> ignore
            let e (items: ImmutableList<int>) = items.Add 1 |> ignore
            """

    match discardedUpdatesIn source with
    | [ a; b; c; d; e ] ->
        Assert.Equal(("index.Add", "Map"), (a.CallName, a.Collection))
        Assert.Equal(("Map.add", "Map"), (b.CallName, b.Collection))
        Assert.Equal(("seen.Add", "Set"), (c.CallName, c.Collection))
        Assert.Equal(("Set.remove", "Set"), (d.CallName, d.Collection))
        Assert.Equal(("items.Add", "ImmutableList"), (e.CallName, e.Collection))
    | other -> failwithf "Expected five findings, got %A" other

[<Fact>]
let ``FR0179: a mutable collection, a kept result, a partial application and a user function stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            let build (n: int) : Map<string, int> = Map.empty
            let a (seen: HashSet<int>) = seen.Add 1 |> ignore
            let b (index: Map<string, int>) = index.Add("k", 1)
            let c (index: Map<string, int>) = Map.add "k" 1 |> ignore
            let d () = build 3 |> ignore
            let e (index: Map<string, int>) = index.ContainsKey "k" |> ignore
            let f (items: List<int>) = items.Remove 1 |> ignore
            """

    Assert.Empty(discardedUpdatesIn source)

// ---- found by attacking the rules ----

[<Fact>]
let ``FR0177: a named literal and the same value written out are one constant`` () =
    let source =
        fsharp
            """
            module M
            [<Literal>]
            let One = 1
            [<Literal>]
            let Name = "a"
            let a (x: int) = x <> One || x <> 1
            let b (x: string) = x <> Name || x <> "a"
            let c (x: int) = x = One && x = 1
            let d (x: int) = x <> 1 || x <> 01
            let e (x: float) = x <> 1.0 || x <> 1.00
            """

    Assert.Empty(comparisonsIn source)

[<Fact>]
let ``FR0177: a named literal against a different value is still always true`` () =
    let source =
        fsharp
            """
            module M
            [<Literal>]
            let One = 1
            let a (x: int) = x <> One || x <> 2
            let b (x: int) = x <> 1 || x <> -1
            """

    match comparisonsIn source with
    | [ a; b ] ->
        Assert.Equal(ConstantComparison.Verdict.AlwaysTrue, a.Verdict)
        Assert.Equal(ConstantComparison.Verdict.AlwaysTrue, b.Verdict)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0178: a mutable local a call may have filled stays quiet, an immutable one does not`` () =
    let source =
        fsharp
            """
            module M
            let a () =
                let mutable cache: int option = None
                let fill () = cache <- Some 1
                if cache.IsNone then
                    fill ()
                    cache.Value
                else
                    0
            let b (x: int option) (log: string -> unit) =
                if x.IsNone then
                    log "empty"
                    x.Value
                else
                    0
            """

    match emptyReadsIn source with
    | [ b ] -> Assert.Equal("x", b.Receiver)
    | other -> failwithf "Expected only the immutable parameter's read, got %A" other

[<Fact>]
let ``FR0179: building from something else, or taking a function, is not an update`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Immutable
            let lazySeq = seq { yield 1 }
            let a () = lazySeq |> Set.ofSeq |> ignore
            let b () = Map.ofList [ 1, 2 ] |> ignore
            let c (xs: int seq) = xs.ToImmutableList() |> ignore
            let d (m: Map<int, int>) = m |> Map.filter (fun k _ -> k > 0) |> ignore
            let e (m: Map<int, int>) = Map.map (fun _ v -> v + 1) m |> ignore
            """

    Assert.Empty(discardedUpdatesIn source)

[<Fact>]
let ``FR0179: a chained update and a set operation are still updates`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Immutable
            let a (xs: ImmutableList<int>) = xs.Add(1).Add(2) |> ignore
            let b (s: Set<int>) (t: Set<int>) = Set.union s t |> ignore
            let c (m: Map<int, int>) = m.Remove 1 |> ignore
            """

    match discardedUpdatesIn source with
    | [ _; _; _ ] -> ()
    | other -> failwithf "Expected three findings, got %A" other
