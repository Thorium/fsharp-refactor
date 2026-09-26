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
let ``map-map fusion composes two provably pure mappers`` () =
    // FSharp.Core functions, union cases and lambdas over them: calling
    // either has no effect, so interleaving the calls changes nothing
    assertSingleSuggestion
        "module Test\nlet f (xs: (int * string) list) = List.map string (List.map fst xs)"
        "List.map (fst >> string) xs"

    assertSingleSuggestion
        "module Test\nlet f (xs: int[]) = Array.map (fun x -> x + 1) (Array.map abs xs)"
        "Array.map (abs >> (fun x -> x + 1)) xs"

    assertSingleSuggestion
        "module Test\ntype K = A of int\nlet f (xs: int seq) = Seq.map A (Seq.map (fun (x: int) -> x * 2) xs)"
        "Seq.map ((fun (x: int) -> x * 2) >> A) xs"

[<Fact>]
let ``map-map fusion stands down unless both mappers are provably effect-free`` () =
    // `List.map g (List.map h xs)` runs every h before the first g; the
    // fused `List.map (h >> g) xs` interleaves them, so a mapper that may
    // have an effect - an opaque user function, a lambda that prints,
    // assigns or sequences statements, a .NET method - keeps the two sweeps
    assertNoSuggestion "module Test\nlet f g h xs = List.map g (List.map h xs)"

    assertNoSuggestion
        "module Test\nlet f (g: int -> int) (xs: int list) = Array.map string (Array.map g (Array.ofList xs))"

    assertNoSuggestion
        "module Test\nlet f (xs: int list) = xs |> List.map (fun x -> printfn \"a\"; x) |> List.map (fun x -> printfn \"b\"; x)"

    assertNoSuggestion
        "module Test\nlet mutable n = 0\nlet f (xs: int list) = List.map string (List.map (fun x -> n <- n + 1; x) xs)"

    assertNoSuggestion
        "module Test\nlet f (xs: string list) = Seq.map string (Seq.map (fun (s: string) -> System.Console.WriteLine s; s.Length) xs)"

    assertNoSuggestion
        "module Test\nlet f (xs: string list) = List.map string (List.map (fun (s: string) -> System.IO.File.ReadAllText s) xs)"

[<Fact>]
let ``map-map fusion stands down when a composed lambda looks a bare parameter up`` () =
    // `fst >> (fun s -> s.Length)` is checked before the list it maps, so
    // `s` has no type at the lookup (FS0072) where `List.map (fun s ->
    // s.Length)` alone inferred it; an annotated parameter composes fine
    assertNoSuggestion
        "module Test\nlet f (pairs: (string * int) list) = List.map (fun s -> s.Length) (List.map fst pairs)"

    assertSingleSuggestion
        "module Test\nlet f (pairs: (string * int) list) = List.map (fun (s: string) -> s.Length) (List.map fst pairs)"
        "List.map (fst >> (fun (s: string) -> s.Length)) pairs"

[<Fact>]
let ``map-map fusion stands down on a throwing or active-pattern mapper`` () =
    // a mapper that raises by design: fused, the second sweep's throw can
    // fire before the first sweep has finished
    assertNoSuggestion
        "module Test\nlet f (strs: string list) = List.map (fun (x: int) -> if x < 0 then failwith \"neg\" else x) (List.map int strs)"

    // an active pattern runs its own body, which no expression of the
    // lambda names
    assertNoSuggestion
        "module Test\nlet (|Logged|) (x: int) = printfn \"%d\" x; x\nlet f (xs: int list) = List.map (fun x -> match x with Logged v -> v + 1) (List.map (fun x -> match x with Logged v -> v * 2) xs)"

    // a reference-cell write and an in-place array sort are effects
    assertNoSuggestion
        "module Test\nlet last = ref 0\nlet f (xs: int list) = List.map string (List.map (fun x -> last := x; x) xs)"

    assertNoSuggestion
        "module Test\nlet f (xs: int[] list) = List.map Array.length (List.map (fun (a: int[]) -> Array.sortInPlace a; a) xs)"

[<Fact>]
let ``map-map fusion needs the typed tree`` () =
    // without a clean typed check no mapper is provably pure
    let source =
        "module Test\nlet f (xs: (int * string) list) = List.map string (List.map fst xs)"

    let tree, sourceText, _ = parseAndCheck source
    Assert.Empty(HintEngine.find [] tree sourceText None)

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
        "module Test\nlet f (p: int -> bool) xs = not (Seq.isEmpty (Seq.filter p xs))"
        "Seq.exists p xs"

[<Fact>]
let ``FR0060: an eager filter probed once keeps running the predicate on every element`` () =
    // List/Array.filter runs `p` on every element, exists/tryFind stop at
    // the first match: a printfn or an exception in `p` sees the difference.
    // A lazy Seq.filter stops at the first match too. The eager forms fire
    // only on a total predicate: comparisons over reads, nothing to throw
    for m in [ "List"; "Array" ] do
        assertNoSuggestion $"module Test\nlet f (p: int -> bool) xs = {m}.isEmpty ({m}.filter p xs)"
        assertNoSuggestion $"module Test\nlet f (p: int -> bool) xs = not ({m}.isEmpty ({m}.filter p xs))"
        assertNoSuggestion $"module Test\nlet f (p: int -> bool) xs = {m}.tryHead ({m}.filter p xs)"

        assertNoSuggestion
            $"module Test\nlet f (xs: string {m.ToLower()}) = {m}.isEmpty ({m}.filter (fun s -> int s > 10) xs)"

        assertNoSuggestion
            $"module Test\nlet f (xs: int {m.ToLower()}) = {m}.isEmpty ({m}.filter (fun x -> 10 / x > 1) xs)"

        assertNoSuggestion
            $"module Test\nlet f (xs: int {m.ToLower()}) = {m}.tryHead ({m}.filter (fun x -> printfn \"%%d\" x; x > 0) xs)"

        assertSingleSuggestion
            $"module Test\nlet f (xs: int {m.ToLower()}) = {m}.isEmpty ({m}.filter (fun x -> x > 0 && x <> 5) xs)"
            $"not ({m}.exists (fun x -> x > 0 && x <> 5) xs)"

    // `Array.item 0` of an empty array throws IndexOutOfRangeException,
    // `Array.head` an ArgumentException
    assertNoSuggestion "module Test\nlet f (xs: int[]) = Array.item 0 xs"

[<Fact>]
let ``FR0060: a dotted read in an eager filter's predicate is total only when typed-proven plain`` () =
    // `o.Value` on None, `l.Head` on [] and `s.Length` on null are getters
    // that throw: the eager filter raised on an element after the first
    // match, which exists never reaches. A record field is a plain read
    for m in [ "List"; "Array" ] do
        let t = m.ToLower()

        assertNoSuggestion
            $"module Test\nlet f (xs: int option {t}) = {m}.isEmpty ({m}.filter (fun o -> o.Value > 0) xs)"

        assertNoSuggestion $"module Test\nlet f (xs: int list {t}) = {m}.isEmpty ({m}.filter (fun l -> l.Head > 0) xs)"

        assertNoSuggestion $"module Test\nlet f (xs: string {t}) = {m}.isEmpty ({m}.filter (fun s -> s.Length > 0) xs)"

        assertSingleSuggestion
            $"module Test\ntype R = {{ Age: int }}\nlet f (xs: R {t}) = {m}.isEmpty ({m}.filter (fun r -> r.Age > 0) xs)"
            $"not ({m}.exists (fun r -> r.Age > 0) xs)"

    // a BCL constant, a struct's getter and a static field are plain reads
    assertSingleSuggestion
        "module Test\nlet f (xs: int list) = List.isEmpty (List.filter (fun x -> x < System.Int32.MaxValue) xs)"
        "not (List.exists (fun x -> x < System.Int32.MaxValue) xs)"

    assertSingleSuggestion
        "module Test\nlet f (xs: System.DateTime list) = List.isEmpty (List.filter (fun (d: System.DateTime) -> d.Year > 2000) xs)"
        "not (List.exists (fun (d: System.DateTime) -> d.Year > 2000) xs)"

    assertSingleSuggestion
        "module Test\nlet f (xs: string list) = List.isEmpty (List.filter (fun s -> s <> System.String.Empty) xs)"
        "not (List.exists (fun s -> s <> System.String.Empty) xs)"

    // getters that read on every value of their type
    for predicate, typeText in
        [
            "(fun (kv: System.Collections.Generic.KeyValuePair<string, int>) -> kv.Value > 0)",
            "System.Collections.Generic.KeyValuePair<string, int>"
            "(fun (x: int option) -> x.IsSome)", "int option"
            "(fun (x: int list) -> x.IsEmpty)", "int list"
            "(fun (x: System.Nullable<int>) -> x.HasValue)", "System.Nullable<int>"
        ] do
        assertSingleSuggestion
            $"module Test\nlet f (xs: {typeText} list) = List.isEmpty (List.filter {predicate} xs)"
            $"not (List.exists {predicate} xs)"

    // a struct whose getters throw on a default value, or call user code
    assertNoSuggestion
        "module Test\nlet f (xs: System.GCMemoryInfo list) = List.isEmpty (List.filter (fun (g: System.GCMemoryInfo) -> g.HeapSizeBytes > 0L) xs)"

    assertNoSuggestion
        "module Test\nlet f (xs: System.Memory<int> list) = List.isEmpty (List.filter (fun (m: System.Memory<int>) -> m.Span.IsEmpty) xs)"

    // but not a Nullable's Value, a struct getter that throws
    assertNoSuggestion
        "module Test\nlet f (xs: System.Nullable<int> list) = List.isEmpty (List.filter (fun (n: System.Nullable<int>) -> n.Value > 0) xs)"

    // the premise: the filter throws where exists stops first
    let xs = [ Some 1; None ]

    Assert.Throws<System.NullReferenceException>(fun () ->
        List.filter (fun (o: int option) -> o.Value > 0) xs |> ignore)
    |> ignore

    Assert.True(List.exists (fun (o: int option) -> o.Value > 0) xs)

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
let ``a custom operation spelled like a core function is not that function`` () =
    // FsCDK's `lifecycleRule { id "rule" }`: `id` is the builder's custom
    // operation, and `id x ===> x` erased it (12 sites rolled back)
    assertNoSuggestion
        "module Test\ntype RuleBuilder() =\n    member _.Yield(_: unit) = \"\"\n    [<CustomOperation(\"id\")>]\n    member _.Id(_: string, value: string) = value\nlet rule = RuleBuilder()\nlet r = rule { id \"test-rule\" }"

[<Fact>]
let ``the core function of the same name still simplifies`` () =
    assertSingleSuggestion "module Test\nlet f (x: int) = id x" "x"

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
let ``a repository's own rule may name the repository's own function`` () =
    // the FSharp.Core check is for the built-in rules; a repository's rule
    // names its own functions and is its author's to aim
    let suggestions =
        findWith
            [ "Helpers.twice (Helpers.twice x) ===> x * 4" ]
            "module Test\nmodule Helpers =\n    let twice (x: int) = x * 2\nlet f (x: int) = Helpers.twice (Helpers.twice x)"

    match suggestions with
    | [ s ] -> Assert.Equal("x * 4", s.ReplacementText)
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

[<Fact>]
let ``a null named argument is never rewritten, a null test beside an operator is`` () =
    // the guard treats a parent APPLICATION as a call, but not an OPERATOR
    // application: `MyType(Prop = null)`, `m.Method(Prop = null)` and
    // `new MyType(Prop = null)` keep their named arguments, while
    // `x = null || y` and `f (x = null)`'s sibling `not (x = null)`... are
    // the hint's business
    let stub =
        "module Test\n"
        + "[<AllowNullLiteral>]\n"
        + "type MyType() =\n"
        + "    member val Prop: string = null with get, set\n"
        + "    member val Other: string = null with get, set\n"
        + "    member this.With(v: int) = this\n"

    assertNoSuggestion (stub + "let a () = MyType(Prop = null)")
    assertNoSuggestion (stub + "let b () = MyType(Prop = null, Other = null)")
    assertNoSuggestion (stub + "let c () = new MyType(Prop = null)")
    assertNoSuggestion (stub + "let d () = MyType().With(1, Prop = null)")

    // the same equality as an operand of `||` is a null test
    let src =
        stub + "let e (t: MyType) (flag: bool) = if t.Prop = null || flag then 1 else 0"

    match findIn src with
    | [ s ] ->
        Assert.Equal("isNull t.Prop", s.ReplacementText)
        Assert.Contains("if isNull t.Prop || flag then", applyEdit src s.Range s.ReplacementText)
    | other -> failwithf "Expected one suggestion, got %A" other

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
        "module Test\nlet f (xs: int list) = Set.ofList (List.map string (List.map abs xs))"
        "List.map (abs >> string) xs"

[<Fact>]
let ``pipelined form of an application rule is normalized and matched`` () =
    // `lhs |> rhs` unifies with application-shaped rules as `rhs lhs`
    assertSingleSuggestion
        "module Test\nlet f (xs: int list) = xs |> List.map abs |> List.map string"
        "xs |> List.map (abs >> string)"

[<Fact>]
let ``pipe normalization also simplifies inner pipeline stages`` () =
    // the inner `xs |> List.map id` matches `List.map id x ===> x`
    assertSingleSuggestion "module Test\nlet f (xs: string list) = xs |> List.map id |> List.length" "xs"

[<Fact>]
let ``De Morgan combines negated conjuncts`` () =
    assertSingleSuggestion "module Test\nlet f (a: bool) b = not a && not b" "not (a || b)"

[<Fact>]
let ``De Morgan folds a third conjunct without re-bracketing the pair`` () =
    // the second step used to bracket the first's result: `not ((a || b) || c)`
    assertSingleSuggestion "module Test\nlet f (a: bool) (b: bool) c = not (a || b) && not c" "not (a || b || c)"

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
let ``De Morgan keeps parentheses around an equal-precedence operand on the right`` () =
    // on the left the grammar's own grouping makes them redundant (see
    // `folds a third conjunct`); on the right they keep it visible
    assertSingleSuggestion "module Test\nlet f (a: bool) b c = not a && not (b || c)" "not (a || (b || c))"

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
let ``De Morgan leaves a left or under an or bare`` () =
    // `(a || b) || c` is what `a || b || c` parses to; the result still compiles
    assertTypedRewrite "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (a || b) && not c" "not (a || b || c)"

[<Fact>]
let ``De Morgan brackets an or under an and`` () =
    assertTypedRewrite "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (a || b) || not c" "not ((a || b) && c)"

[<Fact>]
let ``De Morgan brackets a lambda application and an if`` () =
    assertTypedRewrite
        "module Test\nlet f (a: bool) (b: bool) (c: bool) = not (if a then b else c) && not ((fun z -> z) b)"
        "not ((if a then b else c) || (fun z -> z) b)"

[<Fact>]
let ``a replacement touching the next token gets one space, and no more`` () =
    // `)with` is legal; `a = b` in its place would read `bwith`
    assertSingleSuggestion
        "module Test\nlet f (a: int) (b: int) =\n    match not (a <> b)with\n    | true -> 1\n    | false -> 2"
        "a = b "
    // already separated: nothing added
    assertSingleSuggestion
        "module Test\nlet f (a: int) (b: int) =\n    match not (a <> b) with\n    | true -> 1\n    | false -> 2"
        "a = b"
