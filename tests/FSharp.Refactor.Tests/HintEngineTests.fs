module FSharp.Refactor.Tests.HintEngineTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private findWith (extraRules: string list) (source: string) =
    let tree, sourceText, check = parseAndCheck source
    HintEngine.find extraRules tree sourceText (Some check)

let private findIn (source: string) = findWith [] source

let private assertSingleSuggestion (source: string) (expectedReplacement: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

let private assertNoSuggestion (source: string) = Assert.Empty(findIn source)

[<Fact>]
let ``negated equality flips the operator`` () =
    assertSingleSuggestion "module Test\nlet f a b = not (a = b)" "a <> b"

[<Fact>]
let ``negated less-than flips to greater-or-equal`` () =
    assertSingleSuggestion "module Test\nlet f (a: int) b = not (a < b)" "a >= b"

[<Fact>]
let ``metavariables bind complex expressions with parens as needed`` () =
    assertSingleSuggestion "module Test\nlet f (g: int -> int) x b = not (g x = b)" "(g x) <> b"

[<Fact>]
let ``bool comparison with true is dropped`` () =
    assertSingleSuggestion "module Test\nlet f (x: bool) = x = true" "x"

[<Fact>]
let ``bool comparison with false negates`` () =
    assertSingleSuggestion "module Test\nlet f (x: bool) = false = x" "not x"

[<Fact>]
let ``comparing an obj value with a bool literal is not a redundant comparison`` () =
    // from the corpus (SQLProvider OfflineTools): `o = true` type-checks for
    // o : obj — the literal subsumes to obj — so bare `o` would be FS0001
    assertNoSuggestion "module Test\nlet f (o: obj) = if (isNull o) || o = true then 1 else 2"

[<Fact>]
let ``a bool literal comparison without typed proof stays put`` () =
    // parse-only callers (no check results) cannot prove the operand is bool
    let tree, sourceText = parse "module Test\nlet f (x: bool) = x = true"
    Assert.Empty(HintEngine.find [] tree sourceText None)

[<Fact>]
let ``a bool-returning method call loses its literal comparison`` () =
    // non-atomic substitutions are parenthesized by the engine
    assertSingleSuggestion "module Test\nlet f (s: string) = s.Contains \"x\" = true" "(s.Contains \"x\")"

[<Fact>]
let ``null comparison becomes isNull`` () =
    assertSingleSuggestion "module Test\nlet f (s: string) = s = null" "isNull s"

[<Fact>]
let ``null inequality becomes not isNull`` () =
    assertSingleSuggestion "module Test\nlet f (s: string) = s <> null" "not (isNull s)"

[<Fact>]
let ``map-map fusion composes the mappers`` () =
    assertSingleSuggestion "module Test\nlet f g h xs = List.map g (List.map h xs)" "List.map (h >> g) xs"

[<Fact>]
let ``concat of map becomes collect`` () =
    assertSingleSuggestion
        "module Test\nlet f (g: int -> int list) xs = List.concat (List.map g xs)"
        "List.collect g xs"

[<Fact>]
let ``isEmpty of filter becomes not exists`` () =
    assertSingleSuggestion
        "module Test\nlet f (p: int -> bool) xs = Seq.isEmpty (Seq.filter p xs)"
        "not (Seq.exists p xs)"

[<Fact>]
let ``not isEmpty of filter becomes exists`` () =
    assertSingleSuggestion
        "module Test\nlet f (p: int -> bool) xs = not (List.isEmpty (List.filter p xs))"
        "List.exists p xs"

[<Fact>]
let ``fold plus zero stays a fold: sum adds checked`` () =
    // Mibo's Tests.fs: `Array.fold (+) 0` wraps on overflow, `Array.sum`
    // throws OverflowException — not the same program
    assertNoSuggestion "module Test\nlet f (xs: int list) = List.fold (+) 0 xs"

[<Fact>]
let ``sum of map becomes sumBy`` () =
    assertSingleSuggestion "module Test\nlet f (g: int -> int) xs = List.sum (List.map g xs)" "List.sumBy g xs"

[<Fact>]
let ``map id disappears`` () =
    assertSingleSuggestion "module Test\nlet f (xs: int list) = List.map id xs" "xs"

[<Fact>]
let ``head of sort becomes min`` () =
    assertSingleSuggestion "module Test\nlet f (xs: int list) = List.head (List.sort xs)" "List.min xs"

[<Fact>]
let ``a float comparison flip is NaN-unsound and stays put`` () =
    // not (nan > limit) is true; nan <= limit is false — the branch flips
    assertNoSuggestion "module Test\nlet f (x: float) (limit: float) = not (x > limit)"

[<Fact>]
let ``a float compare collapse is NaN-unsound and stays put`` () =
    // compare nan nan = 0 is true; nan = nan is false
    assertNoSuggestion "module Test\nlet f (a: float) (b: float) = compare a b = 0"

[<Fact>]
let ``head of sort on floats stays put`` () =
    // sort places NaN first; min folds through it order-dependently
    assertNoSuggestion "module Test\nlet f (xs: float list) = List.head (List.sort xs)"

[<Fact>]
let ``an equality negation on floats is NaN-sound and still fires`` () =
    // not (nan = x) and nan <> x agree — only ORDERING flips are gated
    assertSingleSuggestion "module Test\nlet f (a: float) (b: float) = not (a = b)" "a <> b"

[<Fact>]
let ``compare equals zero becomes equality`` () =
    assertSingleSuggestion "module Test\nlet f (a: int) b = compare a b = 0" "a = b"

[<Fact>]
let ``double rev disappears`` () =
    assertSingleSuggestion "module Test\nlet f (xs: int list) = List.rev (List.rev xs)" "xs"

[<Fact>]
let ``id composition simplifies`` () =
    assertSingleSuggestion "module Test\nlet f (g: int -> int) = id >> g" "g"

[<Fact>]
let ``repeated metavariable must bind identical text`` () =
    // rev(rev) with different arguments must not match the double-rev rule
    assertNoSuggestion "module Test\nlet f (xs: int list) ys = List.rev (List.append (List.rev ys) xs)"

[<Fact>]
let ``replacement in operand position is parenthesized`` () =
    let src = "module Test\nlet f (b: bool) (n: int) = string (not (not b))"
    // inner not(not b) matches; parent is a Paren so no extra parens needed
    match findIn src with
    | [ s ] -> Assert.Equal("b", s.ReplacementText)
    | other -> failwithf "Expected one operand-position suggestion, got %A" other

[<Fact>]
let ``extra rules from configuration are applied`` () =
    let suggestions =
        findWith
            [ "Option.isSome x |> not ===> Option.isNone x" ]
            "module Test\nlet f (x: int option) = Option.isSome x |> not"

    match suggestions with
    | [ s ] -> Assert.Equal("Option.isNone x", s.ReplacementText)
    | other -> failwithf "Expected one extra-rule suggestion, got %A" other

[<Fact>]
let ``invalid extra rules are skipped silently`` () =
    Assert.Empty(findWith [ "not valid ==> nope"; "also (((" ] "module Test\nlet f (x: int) = x")

[<Fact>]
let ``rule dropping an effectful binding does not fire`` () =
    // `true && g ()` -> `g ()` is fine (kept); but a rule that DROPS a
    // non-atom must not fire: craft one via extra rules
    Assert.Empty(findWith [ "ignore x ===> ()" ] "module Test\nlet f (g: unit -> int) = ignore (g ())")

[<Fact>]
let ``rule dropping a pure atom fires`` () =
    let suggestions =
        findWith [ "ignore x ===> ()" ] "module Test\nlet f (n: int) = ignore n"

    match suggestions with
    | [ s ] -> Assert.Equal("()", s.ReplacementText)
    | other -> failwithf "Expected one pure-atom suggestion, got %A" other

[<Fact>]
let ``multi-line expressions are not matched`` () =
    assertNoSuggestion "module Test\nlet f a b =\n    not (\n        a = b\n    )"

[<Fact>]
let ``named arguments are never rewritten`` () =
    // found by running the engine on our own code: `Foo(Flag = true)` parses
    // as an equality expression but is a named argument
    assertNoSuggestion "module Test\nlet f () = System.Text.Json.JsonDocumentOptions(AllowTrailingCommas = true)"

[<Fact>]
let ``named argument in a multi-argument call is never rewritten`` () =
    assertNoSuggestion
        "module Test\nlet f () = System.Text.Json.JsonDocumentOptions(CommentHandling = System.Text.Json.JsonCommentHandling.Skip, AllowTrailingCommas = true)"

[<Fact>]
let ``named argument on a new construction is never rewritten`` () =
    // the argument list of `new T(...)` hangs off SynExpr.New, not App:
    // Fuuga's `new Timers.Timer(period, AutoReset = true)` lost its
    // AutoReset until the guard learned that ancestor
    assertNoSuggestion
        "module Test
let f (period: float) = new System.Timers.Timer(period, AutoReset = true)"

// ---- harder cases ----

[<Fact>]
let ``record field assignment is not a comparison`` () =
    // `{ r with Flag = true }` must not become `{ r with Flag }`
    assertNoSuggestion "module Test\ntype R = { Flag: bool; N: int }\nlet f (r: R) = { r with Flag = true }"

[<Fact>]
let ``quoted code is never rewritten`` () =
    // rewriting inside <@ ... @> changes the reified AST
    assertNoSuggestion "module Test\nlet q (x: bool) = <@ x = true @>"

[<Fact>]
let ``metavariables inside array literals substitute correctly`` () =
    // regression: Sequential chains inside [| ... |] were not traversed
    assertSingleSuggestion
        "module Test\nlet f (p: int[]) (q: int[]) (r: int[]) = Array.append p (Array.append q r)"
        "Array.concat [| p; q; r |]"

[<Fact>]
let ``match nested inside surrounding calls still rewrites precisely`` () =
    // fusion target sits inside a larger expression with intermediate steps
    assertSingleSuggestion
        "module Test\nlet f (g: int -> int) xs = Set.ofList (List.map string (List.map g xs))"
        "List.map (g >> string) xs"

[<Fact>]
let ``pipelined form of an application rule is normalized and matched`` () =
    // `lhs |> rhs` unifies with application-shaped rules as `rhs lhs`
    assertSingleSuggestion
        "module Test\nlet f (g: int -> int) xs = xs |> List.map g |> List.map string"
        "xs |> List.map (g >> string)"

[<Fact>]
let ``pipe normalization also simplifies inner pipeline stages`` () =
    // the inner `xs |> List.map id` matches `List.map id x ===> x`
    assertSingleSuggestion "module Test\nlet f (xs: string list) = xs |> List.map id |> List.length" "xs"

[<Fact>]
let ``De Morgan combines negated conjuncts`` () =
    assertSingleSuggestion "module Test\nlet f (a: bool) b = not a && not b" "not (a || b)"

[<Fact>]
let ``De Morgan combines negated disjuncts`` () =
    assertSingleSuggestion "module Test\nlet f (a: bool) b = not a || not b" "not (a && b)"

[<Fact>]
let ``an attribute argument is not an expression to simplify`` () =
    // from Fuuga: [<DllImport(..., SetLastError = true)>] — the property
    // resolves to a bool FIELD, so the typed gate alone waves it through;
    // attribute arguments are constant territory and no hint may fire there
    assertNoSuggestion
        "module Test\n[<System.AttributeUsage(System.AttributeTargets.All, AllowMultiple = true)>]\ntype MyAttr() =\n    inherit System.Attribute()"

[<Fact>]
let ``an OVERLOADED method group is never moved by a hint`` () =
    // prismatic: `Array.head (Array.sortByDescending File.GetLastWriteTime x)`
    // collapses to maxBy, but the collapsed form checks the projection
    // before the element type is known and no overload can be picked
    Assert.Empty(
        findIn
            "module Test\nopen System.IO\nlet f (logFiles: string[]) =\n    logFiles |> Array.sortByDescending File.GetLastWriteTime |> Array.head"
    )

[<Fact>]
let ``a single-overload projection still collapses`` () =
    // the guard must cost nothing where there is no ambiguity to fear.
    // (Path.GetFileName is NOT such a case — string and ReadOnlySpan
    // overloads both exist, and the collapsed form really does not
    // compile; the guard standing down there is the point.)
    match
        findIn "module Test\nlet f (paths: string[]) =\n    paths |> Array.sortByDescending String.length |> Array.head"
    with
    | [ s ] -> Assert.Equal("paths |> Array.maxBy String.length", s.ReplacementText)
    | other -> failwithf "Expected the maxBy collapse, got %A" other

[<Fact>]
let ``a pipelined collect rewrite keeps the pipeline so the lambda sees its type`` () =
    // rendered as `Seq.collect (fun x -> x.Items) xs` the lambda is checked
    // before `xs`, and `x.Items` meets an indeterminate type — Fable's
    // UnionTests, Nu's WorldModuleEntity and PethostBackup's Util all rolled
    // back on exactly this; `xs |> Seq.collect (fun x -> x.Items)` types
    // `xs` first
    assertSingleSuggestion
        "module Test\ntype Box = { Items: int list }\nlet f (xs: Box list) = xs |> Seq.map (fun x -> x.Items) |> Seq.concat"
        "xs |> Seq.collect (fun x -> x.Items)"

[<Fact>]
let ``De Morgan leaves function applications bare beside the operator`` () =
    // sweep find: `not ((List.isEmpty instMembers) && (List.isEmpty statMembers))`
    // — an application is atomic enough beside `||`, the brackets only
    // made the rewrite harder to read than the code it replaced
    assertSingleSuggestion
        "module Test\nlet f (instMembers: int list) (statMembers: int list) =\n    not (List.isEmpty instMembers) && not (List.isEmpty statMembers)"
        "not (List.isEmpty instMembers || List.isEmpty statMembers)"

[<Fact>]
let ``De Morgan leaves method calls bare beside the operator`` () =
    assertSingleSuggestion
        "module Test\nlet f (json: System.Collections.Generic.Dictionary<string, int>) =\n    not (json.ContainsKey \"Case\") && not (json.ContainsKey \"Fields\")"
        "not (json.ContainsKey \"Case\" || json.ContainsKey \"Fields\")"

[<Fact>]
let ``De Morgan leaves a tupled call and a name bare beside the operator`` () =
    assertSingleSuggestion
        "module Test\nlet f (isOpItem: string * int list -> bool) (isFSharpList: string -> bool) nm items =\n    not (isOpItem (nm, items)) || not (isFSharpList nm)"
        "not (isOpItem (nm, items) && isFSharpList nm)"

[<Fact>]
let ``De Morgan leaves a pipeline operand bare`` () =
    // `|>` binds tighter than `||`
    assertSingleSuggestion
        "module Test\nlet f (xs: int list) (b: bool) = not (xs |> List.isEmpty) && not b"
        "not (xs |> List.isEmpty || b)"

[<Fact>]
let ``De Morgan keeps parentheses around an operand of equal precedence`` () =
    assertSingleSuggestion "module Test\nlet f (a: bool) b c = not (a || b) && not c" "not ((a || b) || c)"

[<Fact>]
let ``De Morgan keeps parentheses around a lower-precedence operand`` () =
    assertSingleSuggestion "module Test\nlet f (a: bool) b c = not (a || b) || not c" "not ((a || b) && c)"

[<Fact>]
let ``De Morgan leaves a tighter-binding operand bare`` () =
    // `&&` under `||` needs no brackets
    assertSingleSuggestion "module Test\nlet f (a: bool) b c = not (a && b) && not c" "not (a && b || c)"

[<Fact>]
let ``De Morgan keeps parentheses around an if operand`` () =
    assertSingleSuggestion
        "module Test\nlet f (a: bool) b c = not (if a then b else c) && not c"
        "not ((if a then b else c) || c)"

let private assertTypedRewrite (source: string) (expected: string) =
    match findIn source with
    | [ s ] ->
        Assert.Equal(expected, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``De Morgan keeps pipelines bare: |> binds tighter than ||`` () =
    assertTypedRewrite
        "module Test\nlet f (xs: int list) (ys: int list) = not (xs |> List.isEmpty) && not (ys |> List.isEmpty)"
        "not (xs |> List.isEmpty || ys |> List.isEmpty)"

[<Fact>]
let ``De Morgan keeps type tests bare`` () =
    assertTypedRewrite
        "module Test\nlet f (x: obj) (y: obj) = not (x :? string) && not (y :? string)"
        "not (x :? string || y :? string)"

[<Fact>]
let ``De Morgan keeps comparisons and applications bare`` () =
    assertTypedRewrite
        "module Test\nlet f (g: int -> int) (h: int -> bool) (x: int) = not (g x = 1) && not (h x)"
        "not (g x = 1 || h x)"

[<Fact>]
let ``De Morgan brackets an or under an or`` () =
    // equal precedence keeps the grouping visible; the result still compiles
    assertTypedRewrite "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (a || b) && not c" "not ((a || b) || c)"

[<Fact>]
let ``De Morgan brackets an or under an and`` () =
    assertTypedRewrite "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (a || b) || not c" "not ((a || b) && c)"

[<Fact>]
let ``De Morgan brackets a lambda application and an if`` () =
    assertTypedRewrite
        "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (if a then b else c) && not ((fun z -> z) b)"
        "not ((if a then b else c) || (fun z -> z) b)"
