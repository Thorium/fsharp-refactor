module FSharp.Refactor.Tests.QueryInLoopTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private queriesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    QueryInLoop.find tree sourceText checkResults

[<Fact>]
let ``queryable iterated inside a loop is noted`` () =
    let suggestions =
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.People = [ 1; 2 ].AsQueryable()
                let f (db: Db) (xs: int list) =
                    for x in xs do
                        for p in db.People do
                            printfn "%d %d" x p
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("db.People", s.SourceText)
    | other -> failwithf "Expected exactly one N+1 note, got %A" other

[<Fact>]
let ``local queryable value is also noted`` () =
    let suggestions =
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f (xs: int list) =
                    for x in xs do
                        for p in q do
                            printfn "%d %d" x p
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("q", s.SourceText)
    | other -> failwithf "Expected exactly one local-queryable note, got %A" other

[<Fact>]
let ``in-memory inner sequence is fine`` () =
    Assert.Empty(
        queriesIn (
            fsharp
                """
                let ys = [ 1; 2 ]
                let f (xs: int list) =
                    for x in xs do
                        for y in ys do
                            printfn "%d %d" x y
                """
        )
    )

[<Fact>]
let ``single un-nested queryable loop is fine`` () =
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f () =
                    for p in q do
                        printfn "%d" p
                """
        )
    )

[<Fact>]
let ``chunkBySize batching suppresses the note`` () =
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f (xs: int list) =
                    for chunk in xs |> List.chunkBySize 100 do
                        for p in q do
                            printfn "%d %d" (List.sum chunk) p
                """
        )
    )

[<Fact>]
let ``chunkBySize bound to a let before the loop suppresses the note`` () =
    // the usual way to write it; the guard reads the binding, since the
    // loop header's enumeration expression is a bare identifier holding no
    // call at all. Chunking IS the accepted
    // mitigation for N+1; flagging it reports the cure as the disease
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f (xs: int list) =
                    let chunked = xs |> List.chunkBySize 100
                    for chunk in chunked do
                        for p in q do
                            printfn "%d %d" (List.sum chunk) p
                """
        )
    )

    // without chunking anywhere, the note stands
    Assert.NotEmpty(
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f (xs: int list) =
                    let plain = xs
                    for x in plain do
                        for p in q do
                            printfn "%d %d" x p
                """
        )
    )

[<Fact>]
let ``while loop around a queryable is also noted`` () =
    let suggestions =
        queriesIn (
            fsharp
                """
                open System.Linq
                let q = [ 1; 2 ].AsQueryable()
                let f () =
                    let mutable go = true
                    while go do
                        for p in q do
                            printfn "%d" p
                        go <- false
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("q", s.SourceText)
    | other -> failwithf "Expected exactly one while-nested note, got %A" other

[<Fact>]
let ``a collection-callback outer loop counts as a loop`` () =
    // customers |> List.iter (fun c -> for o in db.Orders do ...) runs the
    // query once per element exactly like a for-loop
    let suggestions =
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.Orders = [ 1; 2 ].AsQueryable()
                let f (db: Db) (xs: int list) =
                    xs |> List.iter (fun x ->
                        for o in db.Orders do
                            printfn "%d %d" x o)
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("db.Orders", s.SourceText)
    | other -> failwithf "Expected exactly one callback N+1 note, got %A" other

[<Fact>]
let ``chunkBySize in the callback pipeline still suppresses`` () =
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.Orders = [ 1; 2 ].AsQueryable()
                let f (db: Db) (xs: int list) =
                    xs |> List.chunkBySize 50 |> List.iter (fun batch ->
                        for o in db.Orders do
                            printfn "%d %d" batch.Length o)
                """
        )
    )

[<Fact>]
let ``FR0028: a nested for inside a query expression is a join, not an N+1`` () =
    // `for order in customer.Orders do`
    // under `query { }` becomes one SQL statement
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.People = [ 1; 2 ].AsQueryable()
                    member _.Orders = [ 3; 4 ].AsQueryable()
                let f (db: Db) =
                    query {
                        for p in db.People do
                            for o in db.Orders do
                                where (o > p)
                                select (p, o)
                    }
                """
        )
    )

[<Fact>]
let ``FR0028: an in-memory outer loop over a queryable inside a query expression is still an N+1`` () =
    // only a queryable OUTER source makes the nested for a translated join;
    // a list outside the provider's reach runs the inner query per element
    let suggestions =
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.Orders = [ 3; 4 ].AsQueryable()
                let f (db: Db) (ids: int list) =
                    query {
                        for i in ids do
                            for o in db.Orders do
                                where (o > i)
                                select (i, o)
                    }
                """
        )

    match suggestions with
    | [ s ] -> Assert.Equal("db.Orders", s.SourceText)
    | other -> failwithf "Expected exactly one N+1 note, got %A" other

[<Fact>]
let ``FR0028: a nested for over a sub-query inside a query expression is one statement`` () =
    Assert.Empty(
        queriesIn (
            fsharp
                """
                open System.Linq
                type Db() =
                    member _.People = [ 1; 2 ].AsQueryable()
                    member _.Orders = [ 3; 4 ].AsQueryable()
                let f (db: Db) =
                    query {
                        for p in (query { for x in db.People do select x }) do
                            for o in db.Orders do
                                where (o > p)
                                select (p, o)
                    }
                """
        )
    )

[<Fact>]
let ``a paging or batched query under a loop is one statement per batch, not N+1`` () =
    // pagination and batching: skip/take driven by the
    // loop, or a where on the outer element's batch
    let scaffold =
        fsharp
            """
            module Test
            open System.Linq
            type Order = { OrderId: int }
            let orders : IQueryable<Order> = ([] : Order list).AsQueryable()

            """

    let paging =
        scaffold
        + fsharp
            """
            let pages () =
                let mutable page = 0
                while page < 3 do
                    let batch = query { for o in orders do
                                        skip (page * 10)
                                        take 10
                                        select o.OrderId }
                    page <- page + 1
            """

    Assert.Empty(queriesIn paging)

    let batched =
        scaffold
        + fsharp
            """
            let batches (ids: int[]) =
                for chunk in Array.chunkBySize 5 ids do
                    let hits = query { for o in orders do
                                       where (chunk.Contains o.OrderId)
                                       select o.OrderId }
                    ignore hits
            """

    Assert.Empty(queriesIn batched)
