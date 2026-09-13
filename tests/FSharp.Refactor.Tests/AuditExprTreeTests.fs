/// Real-repo sweep findings A1, A2, A5: shape-changing rules inside an
/// argument the compiler quotes into a LINQ expression tree (SqlHydra),
/// FR0012's `isNull` landing on a file's own `isNull` (Earcut), and the
/// comparison flip on a unit-of-measure float (svg_path).
module FSharp.Refactor.Tests.AuditExprTreeTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- A1: SqlHydra-shaped builder whose custom operations take
// `[<ProjectionParameter>] Expression<Func<'T, bool>>` ----

let private builderStub =
    """module Test
open System
open System.Linq
open System.Linq.Expressions

type QuerySource<'T>() =
    member _.Items: 'T list = []

type SelectBuilder() =
    member _.For(state: QuerySource<'T>, f: 'T -> QuerySource<'T>) = state
    member _.Yield(_: 'T) = QuerySource<'T>()
    member _.Zero() = QuerySource<'T>()

    [<CustomOperation("where", MaintainsVariableSpace = true)>]
    member _.Where(state: QuerySource<'T>, [<ProjectionParameter>] whereExpression: Expression<Func<'T, bool>>) =
        ignore whereExpression
        state

    [<CustomOperation("having", MaintainsVariableSpace = true)>]
    member _.Having(state: QuerySource<'T>, [<ProjectionParameter>] havingExpression: Expression<Func<'T, bool>>) =
        ignore havingExpression
        state

let select = SelectBuilder()
let table<'T> = QuerySource<'T>()
let maxBy (x: 'T) = x

type Address = { City: string; AddressLine2: string option }
type NullableEntity = { Line2: string; QuestionAnswered: Nullable<bool> }
"""

let private simplifications (source: string) =
    let tree, sourceText, check = parseAndCheck source
    Simplification.find tree sourceText (Some check)

let private hints (source: string) =
    let tree, sourceText, check = parseAndCheck source
    HintEngine.find [] tree sourceText (Some check)

let private optionMatches (source: string) =
    let tree, sourceText, check = parseAndCheck source
    OptionMatch.find tree sourceText check

[<Fact>]
let ``the builder stub itself typechecks`` () =
    Assert.True(
        typechecksCleanly (
            builderStub
            + "let q = select { for a in table<Address> do where (a.AddressLine2 <> None) }"
        )
    )

[<Fact>]
let ``FR0010 leaves a None comparison inside a where projection alone`` () =
    // SqlHydra Npgsql/QueryUnitTests.fs(113,19): `where (a.addressline2 <> None)`
    // became `where (a.addressline2 |> Option.isSome)` and the visitor threw
    let src =
        builderStub
        + "let q = select { for a in table<Address> do where (a.AddressLine2 <> None) }"

    Assert.Empty(simplifications src)

[<Fact>]
let ``FR0010 leaves a None comparison inside a having projection alone`` () =
    // SqlHydra Npgsql/QueryUnitTests.fs(1976,20): `having (maxBy a.addressline2 = None)`
    let src =
        builderStub
        + "let q = select { for a in table<Address> do having (maxBy a.AddressLine2 = None) }"

    Assert.Empty(simplifications src)

[<Fact>]
let ``FR0010 leaves a None comparison in a where laid out over lines alone`` () =
    let src =
        builderStub
        + "let q =\n    select {\n        for a in table<Address> do\n        where (a.AddressLine2 <> None)\n    }"

    Assert.Empty(simplifications src)

[<Fact>]
let ``FR0010 still rewrites the same comparison in a plain conditional`` () =
    let src =
        builderStub + "let f (a: Address) = if a.AddressLine2 <> None then 1 else 0"

    match simplifications src with
    | [ s ] ->
        Assert.Equal("a.AddressLine2.IsSome", s.ReplacementText)
        Assert.True(typechecksCleanly (applyEdit src s.Range s.ReplacementText))
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0010 still rewrites the same comparison inside query`` () =
    // F# quotations and `query { }` stay rewritable: the owner's decision
    let src =
        builderStub
        + "let f (xs: Address list) = query { for a in xs do where (a.AddressLine2 <> None); select a }"

    match simplifications src with
    // the query variable's type is not settled at the comparison, so the
    // module spelling keeps inference going — as it did before
    | [ s ] -> Assert.Equal("a.AddressLine2 |> Option.isSome", s.ReplacementText)
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0010 still rewrites the same comparison inside a quotation`` () =
    let src = builderStub + "let f (a: Address) = <@ a.AddressLine2 <> None @>"

    match simplifications src with
    | [ s ] -> Assert.Equal("a.AddressLine2.IsSome", s.ReplacementText)
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0010 parse-only cannot see the callee and keeps its old behaviour`` () =
    // the gate needs the typed callee; without check results an emptiness
    // rewrite inside `where` is what it always was
    let src =
        builderStub
        + "let q = select { for a in table<Address> do where (a.City |> Seq.length > 0) }"

    let tree, sourceText = parse src
    Assert.NotEmpty(Simplification.find tree sourceText None)

[<Fact>]
let ``FR0010 leaves an emptiness rewrite inside a where projection alone when typed`` () =
    let src =
        builderStub
        + "let q = select { for a in table<Address> do where (a.City |> Seq.length > 0) }"

    Assert.Empty(simplifications src)

[<Fact>]
let ``FR0012 leaves a null comparison inside a where projection alone`` () =
    // SqlHydra SqlServer/QueryNullableUnitTests.fs(62,19): `where (a.AddressLine2 <> null)`
    let src =
        builderStub
        + "let q = select { for a in table<NullableEntity> do where (a.Line2 <> null) }"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 leaves a De Morgan shape inside a where projection alone`` () =
    // SqlHydra SqlServer/QueryNullableUnitTests.fs(51,19)
    let src =
        builderStub
        + "let q = select { for o in table<NullableEntity> do where (not o.QuestionAnswered.Value || not o.QuestionAnswered.HasValue) }"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 still rewrites the null comparison in a plain conditional`` () =
    let src =
        builderStub + "let f (a: NullableEntity) = if a.Line2 <> null then 1 else 0"

    match hints src with
    | [ s ] ->
        Assert.Equal("not (isNull a.Line2)", s.ReplacementText)
        Assert.True(typechecksCleanly (applyEdit src s.Range s.ReplacementText))
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0012 still rewrites the De Morgan shape inside query`` () =
    let src =
        builderStub
        + "let f (xs: NullableEntity list) = query { for o in xs do where (not o.QuestionAnswered.Value || not o.QuestionAnswered.HasValue); select o }"

    match hints src with
    | [ s ] -> Assert.Equal("not (o.QuestionAnswered.Value && o.QuestionAnswered.HasValue)", s.ReplacementText)
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0012 leaves a lambda handed to a Queryable method alone`` () =
    // the plain-method path: System.Linq.Queryable.Where takes an
    // Expression<Func<'T, bool>>, so the lambda is auto-quoted
    let src =
        builderStub
        + "let f (xs: NullableEntity list) = xs.AsQueryable().Where(fun a -> a.Line2 <> null)"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 still rewrites a lambda handed to an Enumerable method`` () =
    // Enumerable.Where takes a Func: ordinary code
    let src =
        builderStub
        + "let f (xs: NullableEntity list) = xs.Where(fun a -> a.Line2 <> null)"

    match hints src with
    | [ s ] -> Assert.Equal("not (isNull a.Line2)", s.ReplacementText)
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0034 leaves an IsSome-and-Value chain inside a where projection alone`` () =
    // SqlHydra SqlServer/QueryUnitTests.fs(41,17):
    // `where (cityFilter.IsSome && a.City = cityFilter.Value)` became
    // `Option.exists`, an NMethodCall the visitor rejects
    let src =
        builderStub
        + "let q (cityFilter: string option) = select { for a in table<Address> do where (cityFilter.IsSome && a.City = cityFilter.Value) }"

    Assert.Empty(optionMatches src)

[<Fact>]
let ``FR0034 still rewrites the IsSome-and-Value chain outside`` () =
    let src =
        builderStub
        + "let g (cityFilter: string option) (a: Address) = cityFilter.IsSome && a.City = cityFilter.Value"

    match optionMatches src with
    | [ s ] ->
        Assert.Equal("cityFilter |> Option.exists (fun v -> a.City = v)", s.ReplacementText)
        Assert.True(typechecksCleanly (applyEdit src s.Range s.ReplacementText))
    | other -> failwithf "expected one suggestion, got %A" other

// ---- A2: a file's own `isNull` shadows FSharp.Core's ----

[<Fact>]
let ``FR0012 withholds isNull when the file defines its own isNull`` () =
    // Earcut.fs:59 `let inline internal isNull (node: Node)` — the rewrite
    // `isNull holes` resolved to it and did not compile
    let src =
        "module Test\n"
        + "type Node(i: int) =\n    member _.I = i\n"
        + "let inline isNull (node: Node) : bool = obj.ReferenceEquals(node, Unchecked.defaultof<Node>)\n"
        + "let f (holes: System.Collections.Generic.IList<int>) = if holes = null then 0 else holes.Count"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 withholds isNull when a local binding shadows it`` () =
    let src =
        "module Test\n"
        + "let f (holes: System.Collections.Generic.IList<int>) =\n"
        + "    let isNull (xs: System.Collections.Generic.IList<int>) = xs.Count = 0\n"
        + "    if holes = null then 0 else holes.Count"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 withholds isNull when an opened module of the project defines it`` () =
    // typed path: the shadowing definition lives in an earlier file and is
    // brought in by `open`; the rewrite would even compile — to a
    // different function
    let helpers = "module Helpers\nlet isNull (s: string) = s = \"\"\n"

    let src =
        "module Test\nopen Helpers\nlet f (s: string) = if s = null then 0 else s.Length\n"

    let tree, sourceText, check = parseAndCheckSecond helpers src
    Assert.Empty(HintEngine.find [] tree sourceText (Some check))

[<Fact>]
let ``FR0012 withholds a List function when a List module of the file redefines it`` () =
    let src =
        "module Test\n"
        + "module List =\n    let collect (f: 'a -> 'b list) (xs: 'a list) : 'b list = []\n"
        + "let f (g: int -> int list) (xs: int list) = List.concat (List.map g xs)"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 still emits isNull when only unrelated names are defined`` () =
    let src =
        "module Test\n"
        + "let isNullOrEmpty (s: string) = System.String.IsNullOrEmpty s\n"
        + "let f (s: string) = if s = null then 0 else s.Length"

    match hints src with
    | [ s ] ->
        Assert.Equal("isNull s", s.ReplacementText)
        Assert.True(typechecksCleanly (applyEdit src s.Range s.ReplacementText))
    | other -> failwithf "expected one suggestion, got %A" other

// ---- A5: a unit-of-measure float is a float with NaN ----

[<Literal>]
let private measure = "module Test\n[<Measure>] type length\n"

[<Fact>]
let ``FR0012 keeps the negated ordering on an annotated measure float`` () =
    // svg_path Transform.fs:49 `if not (tolerance >= 0.0<length>)` is the
    // NaN-rejecting guard; `tolerance < 0.0<length>` lets NaN through
    let src =
        measure
        + "let f (tolerance: float<length>) = if not (tolerance >= 0.0<length>) then 1 else 2"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 keeps the negated ordering on an inferred measure float`` () =
    // the parameter is unannotated in svg_path; its type is inferred from
    // the literal it is compared with
    let src =
        measure + "let f tolerance = if not (tolerance >= 0.0<length>) then 1 else 2"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 keeps the negated ordering on a measure float32`` () =
    let src =
        measure
        + "let f (t: float32<length>) = if not (t >= 0.0f<length>) then 1 else 2"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 keeps the negated ordering on a measure float compared with a name`` () =
    let src =
        measure + "let f (t: float<length>) (limit: float<length>) = not (t > limit)"

    Assert.Empty(hints src)

[<Fact>]
let ``FR0012 keeps the negated ordering without typed results`` () =
    let tree, sourceText = parse "module Test\nlet f a b = not (a >= b)"
    Assert.Empty(HintEngine.find [] tree sourceText None)

[<Fact>]
let ``FR0012 still flips a negated equality on a measure float`` () =
    // `not (nan = x)` and `nan <> x` agree: equality is NaN-sound
    let src = measure + "let f (a: float<length>) (b: float<length>) = not (a = b)"

    match hints src with
    | [ s ] -> Assert.Equal("a <> b", s.ReplacementText)
    | other -> failwithf "expected one suggestion, got %A" other

[<Fact>]
let ``FR0012 still flips a negated ordering on an int`` () =
    let src = "module Test\nlet f (n: int) = if not (n >= 0) then 1 else 2"

    match hints src with
    | [ s ] ->
        Assert.Equal("n < 0", s.ReplacementText)
        Assert.True(typechecksCleanly (applyEdit src s.Range s.ReplacementText))
    | other -> failwithf "expected one suggestion, got %A" other
