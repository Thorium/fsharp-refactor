/// FR0174: a query copied before Where/Select runs them in the query.
module FSharp.Refactor.Tests.QueryCopyTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// Enough declarations for the cases to typecheck on their own.
let private header =
    "open System\nopen System.Linq\n"
    + "type State = Open = 0 | Closed = 1\n"
    + "[<CLIMutable>]\ntype Order = { Id: int; State: State; Active: bool; Total: decimal; Name: string; Parent: Nullable<int> }\n"
    + "type Row() =\n    member val Id = 0 with get, set\n    member this.Twice = this.Id * 2\n"
    + "let orders: IQueryable<Order> = Array.empty<Order>.AsQueryable()\n"
    + "let rows: IQueryable<Row> = Array.empty<Row>.AsQueryable()\n"
    + "let limit = 3\n"

/// `pipelines`: the knob that takes the `|> Seq.toList |> List.filter` shape.
let private foundWith (pipelines: bool) (body: string) =
    let tree, source, check = parseAndCheck (header + body)
    QueryCopy.find pipelines tree source check

let private found = foundWith false

let private assertRewritesWith (pipelines: bool) (body: string) (expected: string) (fidelity: QueryCopy.Fidelity) =
    match foundWith pipelines body with
    | [ s ] ->
        let patched = applyEdit (header + body) s.Range s.ReplacementText
        Assert.Equal(fidelity, s.Fidelity)
        Assert.True s.Fixable
        Assert.Contains(expected, patched)
        // the standing rule: the produced text must be right on its own,
        // never rescued by a compile check afterwards
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

let private assertRewrites = assertRewritesWith false

[<Fact>]
let ``a copy before trivial Where and Select moves after them`` () =
    assertRewrites
        "let r = orders.ToList().Where(fun o -> o.Id > 0 || o.State = State.Open).Select(fun o -> o.Id)"
        "let r = orders.Where(fun o -> o.Id > 0 || o.State = State.Open).Select(fun o -> o.Id).ToList()"
        QueryCopy.Exact

[<Fact>]
let ``a copy of the same kind after the stages is the one kept`` () =
    assertRewrites
        "let r = orders.ToArray().Where(fun o -> o.Active && not (o.Id = limit)).ToArray()"
        "let r = orders.Where(fun o -> o.Active && not (o.Id = limit)).ToArray()"
        QueryCopy.Exact

[<Fact>]
let ``a member val column of this file is a column`` () =
    assertRewrites
        "let r = rows.ToList().Where(fun x -> x.Id > limit)"
        "let r = rows.Where(fun x -> x.Id > limit).ToList()"
        QueryCopy.Exact

[<Fact>]
let ``under the pipelines knob the pipeline copy moves after filter and map`` () =
    assertRewritesWith
        true
        "let r = orders |> Seq.toList |> List.filter (fun o -> o.Id > 0) |> List.map (fun o -> o.Id)"
        "let r = orders.Where(fun o -> o.Id > 0).Select(fun o -> o.Id) |> Seq.toList"
        QueryCopy.Exact

[<Fact>]
let ``a pipeline across lines keeps the copy on its own line`` () =
    assertRewritesWith
        true
        "let r =\n    orders\n    |> Array.ofSeq\n    |> Array.filter (fun o -> o.Name <> null)"
        "let r =\n    orders.Where(fun o -> o.Name <> null)\n    |> Array.ofSeq"
        QueryCopy.Exact

[<Fact>]
let ``only the translatable stages move; the rest stays after the copy`` () =
    assertRewrites
        "let r = orders.ToList().Where(fun o -> o.Id > 0).Select(fun o -> o.Id * 2)"
        "let r = orders.Where(fun o -> o.Id > 0).ToList().Select(fun o -> o.Id * 2)"
        QueryCopy.Exact

[<Fact>]
let ``the chain is type-stable only where a List binds as the IEnumerable did`` () =
    let stable body =
        match found body with
        | [ s ] -> s.TypeStable
        | other -> failwithf "Expected exactly one suggestion, got %A" other

    // walked as a sequence, continued by an Enumerable call, or ending in the same copy
    Assert.True(stable "let r = [ for o in orders.ToList().Where(fun o -> o.Id > 0) -> o.Id ]")
    Assert.True(stable "let r = orders.ToList().Where(fun o -> o.Id > 0) |> Seq.length")
    Assert.True(stable "let r = Seq.length (orders.ToList().Where(fun o -> o.Id > 0))")
    Assert.True(stable "let r = orders.ToList().Where(fun o -> o.Id > 0).Select(fun o -> o.Id * 2)")
    Assert.True(stable "let r = orders.ToList().Where(fun o -> o.Id > 0).ToList()")
    Assert.True(stable "let r = orders.AsEnumerable().Where(fun o -> o.Id > 0)")
    // a let carries the new type on; Reverse would bind to List<T>.Reverse
    Assert.False(stable "let r = orders.ToList().Where(fun o -> o.Id > 0)")
    Assert.False(stable "let r = orders.ToList().Where(fun o -> o.Id > 0).Reverse()")

[<Fact>]
let ``a navigation column is no value: null without Include in memory, a join in the query`` () =
    let header =
        header.Replace("Parent: Nullable<int> }", "Parent: Nullable<int>; Previous: Order }")

    let tree, source, check =
        parseAndCheck (header + "let r = orders.ToList().Where(fun o -> o.Previous = null)")

    Assert.Empty(QueryCopy.find false tree source check)

    let tree, source, check =
        parseAndCheck (header + "let r = orders.ToList().Select(fun o -> o.Previous)")

    Assert.Empty(QueryCopy.find false tree source check)

[<Fact>]
let ``a string, decimal or nullable comparison is Near`` () =
    assertRewrites
        "let r = orders.ToList().Where(fun o -> o.Name = \"a\")"
        "orders.Where(fun o -> o.Name = \"a\").ToList()"
        QueryCopy.Near

    assertRewrites
        "let r = orders.ToList().Where(fun o -> o.Total > 0.005m)"
        "orders.Where(fun o -> o.Total > 0.005m).ToList()"
        QueryCopy.Near

[<Fact>]
let ``a stage a provider might not translate stays in memory`` () =
    // a computed property, a call, arithmetic, a list that is no query,
    // a tuple projection, a filter reading a mutable
    Assert.Empty(found "let r = rows.ToList().Where(fun x -> x.Twice > 0)")
    Assert.Empty(found "let r = orders.ToList().Where(fun o -> o.Name.StartsWith \"a\")")
    Assert.Empty(found "let r = orders.ToList().Where(fun o -> o.Id % 2 = 0)")
    Assert.Empty(found "let r (xs: ResizeArray<Order>) = xs.ToList().Where(fun o -> o.Id > 0)")
    Assert.Empty(found "let r = orders.ToList().Select(fun o -> (o.Id, o.Name))")
    Assert.Empty(found "let mutable floor = 0\nlet r = orders.ToList().Where(fun o -> o.Id > floor)")
    Assert.Empty(foundWith true "let r = orders |> Seq.toList |> List.filter (fun o -> o.Id > 0 && o.Name.Length > 2)")

[<Fact>]
let ``without open System.Linq the knob's pipeline is a note`` () =
    let header =
        header.Replace("open System.Linq\n", "").Replace(": IQueryable<", ": System.Linq.IQueryable<")

    let body = "let r = orders |> Seq.toList |> List.filter (fun o -> o.Id > 0)"

    let tree, source, check =
        parseAndCheck (
            header
                .Replace("Array.empty<Order>.AsQueryable()", "System.Linq.Queryable.AsQueryable(Array.empty<Order>)")
                .Replace("Array.empty<Row>.AsQueryable()", "System.Linq.Queryable.AsQueryable(Array.empty<Row>)")
            + body
        )

    Assert.True(
        typechecksCleanly (source.GetSubTextString(0, source.Length)),
        source.GetSubTextString(0, source.Length)
    )

    match QueryCopy.find true tree source check with
    | [ s ] -> Assert.False s.Fixable
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``by default a pipeline is the author's visible choice, and query { } always is`` () =
    // the C#-style LINQ chain hides where the rows come into memory; a
    // pipeline shows it, and the knob is off
    Assert.Empty(found "let r = orders |> Seq.toList |> List.filter (fun o -> o.Id > 0) |> List.map (fun o -> o.Id)")
    Assert.Empty(found "let r = orders |> Array.ofSeq |> Array.filter (fun o -> o.Id > 0)")

    Assert.Empty(
        foundWith true "let r = query { for o in orders do select o } |> Seq.toList |> List.filter (fun o -> o.Id > 0)"
    )
