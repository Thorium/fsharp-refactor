module FSharp.Refactor.Tests.LambdaBuiltinTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findIn (source: string) =
    let tree, sourceText = parse source
    LambdaBuiltin.find tree sourceText

let private assertReplacement (source: string) (expected: string) =
    match findIn source with
    | [ s ] -> Assert.Equal(expected, s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``fun x -> x is id`` () =
    assertReplacement "module Test\nlet m = List.map (fun x -> x) []" "id"

[<Fact>]
let ``fun (a, b) -> a is fst`` () =
    assertReplacement "module Test\nlet m = List.map (fun (a, b) -> a) []" "fst"

[<Fact>]
let ``fun (a, b) -> b is snd`` () =
    assertReplacement "module Test\nlet m = List.map (fun (a, b) -> b) []" "snd"

[<Fact>]
let ``a curried lambda is not fst`` () =
    // `fun x y -> x` takes its arguments one at a time; `fst` takes a tuple
    assertNoSuggestion "module Test\nlet m = List.map (fun x y -> x) []"

[<Fact>]
let ``an annotated parameter keeps the lambda`` () =
    assertNoSuggestion "module Test\nlet m = List.map (fun (a: int, b) -> a) []"

[<Fact>]
let ``a lambda returning something else is untouched`` () =
    assertNoSuggestion "module Test\nlet m = List.map (fun x -> x + 1) []"

[<Fact>]
let ``a three-element tuple is neither fst nor snd`` () =
    assertNoSuggestion "module Test\nlet m = List.map (fun (a, b, c) -> a) []"

[<Fact>]
let ``a method argument keeps its lambda`` () =
    // the lambda-to-delegate conversion is doing work a function value may not
    assertNoSuggestion (
        fsharp
            """
            module Test
            let m (xs: System.Collections.Generic.List<int>) = xs.ConvertAll(fun x -> x)
            """
    )

[<Fact>]
let ``a file that rebinds id does not get id`` () =
    // a module may redefine all three: `let id bhvr = returnB bhvr`.
    // Rewriting `fun x -> x` to `id` there calls the module's own function,
    // not FSharp.Core's, and breaks the build
    assertNoSuggestion (
        fsharp
            """
            module Test
            let id (x: int) = x + 1
            let m = List.map (fun x -> x) []
            """
    )

[<Fact>]
let ``a file that rebinds fst still gets snd`` () =
    // the guard is per NAME, not per file: shadowing one builtin says
    // nothing about the others
    assertReplacement
        (fsharp
            """
            module Test
            let fst (x: int) = x
            let m = List.map (fun (a, b) -> b) []
            """)
        "snd"

[<Fact>]
let ``a local id in another function does not cost this one its fix`` () =
    // `let id = 42` somewhere in the file is the common shadowing; it only
    // reaches the scope it sits in
    assertReplacement
        (fsharp
            """
            module Test
            let g () =
                let id = 42
                id + 1

            let m = List.map (fun x -> x) []
            """)
        "id"

[<Fact>]
let ``a local id earlier in the same function shadows`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let g () =
                let id = 42
                List.map (fun x -> x) [ id ]
            """
    )

[<Fact>]
let ``a module-level id declared AFTER the lambda does not shadow it`` () =
    // F# scope runs downward: the rebinding is not visible above itself
    assertReplacement
        (fsharp
            """
            module Test
            let m = List.map (fun x -> x) []
            let id (x: int) = x + 1
            """)
        "id"

[<Fact>]
let ``a parameter named fst shadows`` () =
    assertNoSuggestion "module Test\nlet g fst = List.map (fun (a, b) -> a) [ fst ]"

[<Fact>]
let ``a match-bound snd shadows`` () =
    assertNoSuggestion (
        fsharp
            """
            module Test
            let g o =
                match o with
                | Some snd -> List.map (fun (a, b) -> b) [ snd ]
                | None -> []
            """
    )

// ---- the lambda's parentheses go with it ----

[<Fact>]
let ``a parenthesised lambda argument drops its parentheses with the lambda`` () =
    // `Array.init this.Count (fun v -> v)` becomes `Array.init this.Count id`, not `(id)`
    let source = "module Test\nlet m (n: int) = Array.init n (fun v -> v)"

    match findIn source with
    | [ s ] ->
        Assert.Equal("(fun v -> v)", s.OriginalText)
        Assert.Equal("module Test\nlet m (n: int) = Array.init n id", applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a parenthesised lambda inside a tuple drops its parentheses too`` () =
    // `ListReduceNode(list, (fun v -> v), reduction)` must not keep `(id)`
    let source =
        fsharp
            """
            module Test
            let m (f: int list * (int -> int) * int -> int) (xs: int list) = f (xs, (fun v -> v), 1)
            """

    match findIn source with
    | [ s ] -> Assert.Contains("f (xs, id, 1)", applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a lambda glued to its callee keeps its parentheses`` () =
    // `List.map(fun x -> x)` would fuse into `List.mapid`
    let source = "module Test\nlet m = List.map(fun x -> x) []"

    match findIn source with
    | [ s ] ->
        Assert.Equal("fun x -> x", s.OriginalText)
        Assert.Contains("List.map(id) []", applyEdit source s.Range s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other
