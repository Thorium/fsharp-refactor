module FSharp.Refactor.Tests.LoopPerfTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0035 / FR0037 LoopPerf ----

let private loopPerfIn (source: string) =
    let tree, sourceText = parse source
    LoopPerf.find false tree sourceText

[<Fact>]
let ``contains inside a for loop is noted`` () =
    let contains, _ =
        loopPerfIn
            "module Test\nlet f (xs: int list) (ys: int list) =\n    for x in xs do\n        if List.contains x ys then printfn \"%d\" x"

    match contains with
    | [ s ] ->
        Assert.Equal("ys", s.CollectionName)
        Assert.Equal("List", s.ModuleName)
    | other -> failwithf "Expected exactly one contains note, got %A" other

[<Fact>]
let ``piped contains inside a filter callback is noted`` () =
    let contains, _ =
        loopPerfIn
            "module Test\nlet f (xs: int list) (ys: int list) = xs |> List.filter (fun x -> ys |> List.contains x)"

    match contains with
    | [ s ] -> Assert.Equal("ys", s.CollectionName)
    | other -> failwithf "Expected exactly one callback contains note, got %A" other

[<Fact>]
let ``contains outside any loop is fine`` () =
    let contains, _ =
        loopPerfIn "module Test\nlet f (x: int) (ys: int list) = List.contains x ys"

    Assert.Empty contains

[<Fact>]
let ``probing the loop variable itself is fine`` () =
    // scanning each inner collection once is not a repeated probe
    let contains, _ =
        loopPerfIn
            "module Test\nlet f (xss: int list list) =\n    for xs in xss do\n        if List.contains 1 xs then printfn \"hit\""

    Assert.Empty contains

[<Fact>]
let ``ConcurrentDictionary built in a loop is noted`` () =
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Collections.Concurrent\nlet f (xs: int list) =\n    for x in xs do\n        let d = ConcurrentDictionary<int, int>()\n        d.TryAdd(x, x) |> ignore"

    match constructions with
    | [ s ] -> Assert.Equal("ConcurrentDictionary", s.TypeName)
    | other -> failwithf "Expected exactly one construction note, got %A" other

[<Fact>]
let ``JsonSerializerOptions built in a loop is noted`` () =
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Text.Json\nlet f (xs: string list) =\n    for x in xs do\n        let opts = JsonSerializerOptions()\n        ignore (JsonSerializer.Deserialize<int>(x, opts))"

    match constructions with
    | [ s ] -> Assert.Equal("JsonSerializerOptions", s.TypeName)
    | other -> failwithf "Expected exactly one options-construction note, got %A" other

[<Fact>]
let ``SearchValues Create in a loop is noted`` () =
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Buffers\nlet f (xs: string list) =\n    for x in xs do\n        let sv = SearchValues.Create \"aeiou\"\n        ignore (x.AsSpan().IndexOfAny sv)"

    match constructions with
    | [ s ] -> Assert.Equal("SearchValues", s.TypeName)
    | other -> failwithf "Expected exactly one SearchValues note, got %A" other

[<Fact>]
let ``ConcurrentDictionary outside a loop is fine`` () =
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Collections.Concurrent\nlet d = ConcurrentDictionary<int, int>()\nlet f (x: int) = d.TryAdd(x, x) |> ignore"

    Assert.Empty constructions

// ---- FR0036 TypeChecks ----

let private typeChecksIn (source: string) =
    let tree, sourceText = parse source
    TypeChecks.find tree sourceText

[<Fact>]
let ``type name string comparison is noted`` () =
    let suggestions =
        typeChecksIn "module Test\nlet f (x: obj) = x.GetType().Name = \"Customer\""

    match suggestions with
    | [ s ] -> Assert.Equal(TypeChecks.TypeCheckKind.NameComparison "Name", s.Kind)
    | other -> failwithf "Expected exactly one name-comparison note, got %A" other

[<Fact>]
let ``full name comparison is noted either way round`` () =
    let suggestions =
        typeChecksIn "module Test\nlet f (x: obj) = \"N.Customer\" = x.GetType().FullName"

    match suggestions with
    | [ s ] -> Assert.Equal(TypeChecks.TypeCheckKind.NameComparison "FullName", s.Kind)
    | other -> failwithf "Expected exactly one full-name note, got %A" other

[<Fact>]
let ``GetType equality with typeof is noted`` () =
    let suggestions =
        typeChecksIn "module Test\nlet f (x: obj) = x.GetType() = typeof<string>"

    match suggestions with
    | [ s ] -> Assert.Equal(TypeChecks.TypeCheckKind.TypeofEquality("x", "string"), s.Kind)
    | other -> failwithf "Expected exactly one typeof-equality note, got %A" other

[<Fact>]
let ``FR0036: an exact-type guard refining a type test is intent`` () =
    // FCS FileSystem.fs: `| :? IOException as err when retryLocked &&
    // err.GetType() = typeof<IOException>` retries only on a PLAIN
    // IOException — the `:?` the note would offer is the test being refined
    Assert.Empty(
        typeChecksIn
            "module Test\nopen System.IO\nlet f (retryLocked: bool) (work: unit -> int) =\n    try\n        work ()\n    with\n    | :? IOException as err when retryLocked && err.GetType() = typeof<IOException> -> -1"
    )

[<Fact>]
let ``FR0036: a guard against another type, or the comparison in the body, is still noted`` () =
    // the guard only refines the test when it names the tested type
    let otherType =
        typeChecksIn
            "module Test\nopen System.IO\nlet f (work: unit -> int) =\n    try\n        work ()\n    with\n    | :? IOException as err when err.GetType() = typeof<FileNotFoundException> -> -1"

    let inBody =
        typeChecksIn
            "module Test\nopen System.IO\nlet f (work: unit -> int) =\n    try\n        work ()\n    with\n    | :? IOException as err -> if err.GetType() = typeof<IOException> then -1 else -2"

    // fsi.fs: `.GetType().Name = \"OperationCanceledException\"` in a guard
    // has a typed spelling and stays flagged
    let byName =
        typeChecksIn
            "module Test\nopen System.Reflection\nlet f (work: unit -> int) =\n    try\n        work ()\n    with\n    | :? TargetInvocationException as e when e.InnerException.GetType().Name = \"OperationCanceledException\" -> -1"

    Assert.Single otherType |> ignore
    Assert.Single inBody |> ignore

    match byName with
    | [ s ] -> Assert.Equal(TypeChecks.TypeCheckKind.NameComparison "Name", s.Kind)
    | other -> failwithf "Expected one name-comparison note, got %A" other

[<Fact>]
let ``comparing two GetType calls is fine`` () =
    Assert.Empty(typeChecksIn "module Test\nlet f (x: obj) (y: obj) = x.GetType() = y.GetType()")

[<Fact>]
let ``typeof against typeof is fine`` () =
    Assert.Empty(typeChecksIn "module Test\nlet f () = typeof<string> = typeof<obj>")

[<Fact>]
let ``Regex built in a loop is noted`` () =
    // Constructing one parses and compiles the pattern — the whole cost.
    // FR0015 covers static Regex CALLS in a loop; a Regex bound to a value
    // inside one fell between the two rules.
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Text.RegularExpressions\nlet f (xs: string list) =\n    for x in xs do\n        let r = Regex \"a+\"\n        r.IsMatch x |> ignore"

    match constructions with
    | [ s ] -> Assert.Equal("Regex", s.TypeName)
    | other -> failwithf "Expected exactly one Regex construction note, got %A" other

[<Fact>]
let ``Regex built outside a loop is fine`` () =
    let _, constructions =
        loopPerfIn
            "module Test\nopen System.Text.RegularExpressions\nlet r = Regex \"a+\"\nlet f (x: string) = r.IsMatch x"

    Assert.Empty constructions

[<Fact>]
let ``a field-held collection probed in a loop is noted`` () =
    // collections routinely live in a config record — `config.Excluded`
    // is loop-invariant exactly when its root is
    let contains, _ =
        loopPerfIn
            "module Test\ntype Config = { Excluded: int list }\nlet f (config: Config) (xs: int list) =\n    for x in xs do\n        if List.contains x config.Excluded then printfn \"%d\" x"

    match contains with
    | [ s ] -> Assert.Equal("config.Excluded", s.CollectionName)
    | other -> failwithf "Expected exactly one contains note, got %A" other
