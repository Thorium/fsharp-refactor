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
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.People = [ 1; 2 ].AsQueryable()\nlet f (db: Db) (xs: int list) =\n    for x in xs do\n        for p in db.People do\n            printfn \"%d %d\" x p"

    match suggestions with
    | [ s ] -> Assert.Equal("db.People", s.SourceText)
    | other -> failwithf "Expected exactly one N+1 note, got %A" other

[<Fact>]
let ``local queryable value is also noted`` () =
    let suggestions =
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f (xs: int list) =\n    for x in xs do\n        for p in q do\n            printfn \"%d %d\" x p"

    match suggestions with
    | [ s ] -> Assert.Equal("q", s.SourceText)
    | other -> failwithf "Expected exactly one local-queryable note, got %A" other

[<Fact>]
let ``in-memory inner sequence is fine`` () =
    Assert.Empty(
        queriesIn
            "let ys = [ 1; 2 ]\nlet f (xs: int list) =\n    for x in xs do\n        for y in ys do\n            printfn \"%d %d\" x y"
    )

[<Fact>]
let ``single un-nested queryable loop is fine`` () =
    Assert.Empty(
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f () =\n    for p in q do\n        printfn \"%d\" p"
    )

[<Fact>]
let ``chunkBySize batching suppresses the note`` () =
    Assert.Empty(
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f (xs: int list) =\n    for chunk in xs |> List.chunkBySize 100 do\n        for p in q do\n            printfn \"%d %d\" (List.sum chunk) p"
    )

[<Fact>]
let ``chunkBySize bound to a let before the loop suppresses the note`` () =
    // management-portal DomainShared.fs writes it this way, and the guard
    // scanned only the loop header - where the enumeration expression is a
    // bare identifier holding no call at all. Chunking IS the accepted
    // mitigation for N+1; flagging it reports the cure as the disease
    Assert.Empty(
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f (xs: int list) =\n    let chunked = xs |> List.chunkBySize 100\n    for chunk in chunked do\n        for p in q do\n            printfn \"%d %d\" (List.sum chunk) p"
    )

    // without chunking anywhere, the note stands
    Assert.NotEmpty(
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f (xs: int list) =\n    let plain = xs\n    for x in plain do\n        for p in q do\n            printfn \"%d %d\" x p"
    )

[<Fact>]
let ``while loop around a queryable is also noted`` () =
    let suggestions =
        queriesIn
            "open System.Linq\nlet q = [ 1; 2 ].AsQueryable()\nlet f () =\n    let mutable go = true\n    while go do\n        for p in q do\n            printfn \"%d\" p\n        go <- false"

    match suggestions with
    | [ s ] -> Assert.Equal("q", s.SourceText)
    | other -> failwithf "Expected exactly one while-nested note, got %A" other

[<Fact>]
let ``a collection-callback outer loop counts as a loop`` () =
    // customers |> List.iter (fun c -> for o in db.Orders do ...) runs the
    // query once per element exactly like a for-loop
    let suggestions =
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.Orders = [ 1; 2 ].AsQueryable()\nlet f (db: Db) (xs: int list) =\n    xs |> List.iter (fun x ->\n        for o in db.Orders do\n            printfn \"%d %d\" x o)"

    match suggestions with
    | [ s ] -> Assert.Equal("db.Orders", s.SourceText)
    | other -> failwithf "Expected exactly one callback N+1 note, got %A" other

[<Fact>]
let ``chunkBySize in the callback pipeline still suppresses`` () =
    Assert.Empty(
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.Orders = [ 1; 2 ].AsQueryable()\nlet f (db: Db) (xs: int list) =\n    xs |> List.chunkBySize 50 |> List.iter (fun batch ->\n        for o in db.Orders do\n            printfn \"%d %d\" batch.Length o)"
    )

[<Fact>]
let ``FR0028: a nested for inside a query expression is a join, not an N+1`` () =
    // SQLProvider's navigation tests: `for order in customer.Orders do`
    // under `query { }` becomes one SQL statement
    Assert.Empty(
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.People = [ 1; 2 ].AsQueryable()\n    member _.Orders = [ 3; 4 ].AsQueryable()\nlet f (db: Db) =\n    query {\n        for p in db.People do\n            for o in db.Orders do\n                where (o > p)\n                select (p, o)\n    }"
    )

[<Fact>]
let ``FR0028: an in-memory outer loop over a queryable inside a query expression is still an N+1`` () =
    // only a queryable OUTER source makes the nested for a translated join;
    // a list outside the provider's reach runs the inner query per element
    let suggestions =
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.Orders = [ 3; 4 ].AsQueryable()\nlet f (db: Db) (ids: int list) =\n    query {\n        for i in ids do\n            for o in db.Orders do\n                where (o > i)\n                select (i, o)\n    }"

    match suggestions with
    | [ s ] -> Assert.Equal("db.Orders", s.SourceText)
    | other -> failwithf "Expected exactly one N+1 note, got %A" other

[<Fact>]
let ``FR0028: a nested for over a sub-query inside a query expression is one statement`` () =
    Assert.Empty(
        queriesIn
            "open System.Linq\ntype Db() =\n    member _.People = [ 1; 2 ].AsQueryable()\n    member _.Orders = [ 3; 4 ].AsQueryable()\nlet f (db: Db) =\n    query {\n        for p in (query { for x in db.People do select x }) do\n            for o in db.Orders do\n                where (o > p)\n                select (p, o)\n    }"
    )

[<Fact>]
let ``a paging or batched query under a loop is one statement per batch, not N+1`` () =
    // SQLProvider's pagination and batching tests: skip/take driven by the
    // loop, or a where on the outer element's batch
    let scaffold =
        "module Test\nopen System.Linq\ntype Order = { OrderId: int }\nlet orders : IQueryable<Order> = ([] : Order list).AsQueryable()\n"

    let paging =
        scaffold
        + "let pages () =\n    let mutable page = 0\n    while page < 3 do\n        let batch = query { for o in orders do\n                            skip (page * 10)\n                            take 10\n                            select o.OrderId }\n        page <- page + 1"

    Assert.Empty(queriesIn paging)

    let batched =
        scaffold
        + "let batches (ids: int[]) =\n    for chunk in Array.chunkBySize 5 ids do\n        let hits = query { for o in orders do\n                           where (chunk.Contains o.OrderId)\n                           select o.OrderId }\n        ignore hits"

    Assert.Empty(queriesIn batched)
