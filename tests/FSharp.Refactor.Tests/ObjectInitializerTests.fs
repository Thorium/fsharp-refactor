module FSharp.Refactor.Tests.ObjectInitializerTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0140 ObjectInitializer ----

let private objInitIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ObjectInitializer.find tree sourceText checkResults

[<Literal>]
let private klass =
    "module Test\ntype Henkilo() =\n    member val Id = 0L with get, set\n    member val Etunimi = \"\" with get, set\n    member this.Shout () = 1\n"

[<Fact>]
let ``property sets after a construction fold into it`` () =
    let source =
        klass
        + "let f () =\n    let h = Henkilo()\n    h.Id <- 1L\n    h.Etunimi <- \"x\"\n    h"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal(2, s.Count)
        Assert.Equal("Henkilo(Id = 1L, Etunimi = \"x\")", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``the new keyword is preserved`` () =
    let source = klass + "let f () =\n    let h = new Henkilo()\n    h.Id <- 1L\n    h"

    match objInitIn source with
    | [ s ] -> Assert.Equal("new Henkilo(Id = 1L)", s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``existing constructor arguments are kept and the properties appended`` () =
    let source =
        "module Test\ntype P(name: string) =\n    member val Name = name with get, set\n    member val Age = 0 with get, set\nlet f () =\n    let p = P(\"bob\")\n    p.Age <- 42\n    p"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("P(\"bob\", Age = 42)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``an unrelated statement in between stops the fold`` () =
    // moving the sets across it would change evaluation order; the author
    // lifts the line themselves if they want the rewrite
    let source =
        klass
        + "let f () =\n    let h = Henkilo()\n    printfn \"between\"\n    h.Id <- 1L\n    h"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a value that reads the object cannot move into its construction`` () =
    let source =
        klass + "let f () =\n    let h = Henkilo()\n    h.Id <- h.Id + 1L\n    h"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a repeated property is left alone`` () =
    // two writes would collapse into one
    let source =
        klass
        + "let f () =\n    let h = Henkilo()\n    h.Id <- 1L\n    h.Id <- 2L\n    h"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a record is not an object initializer`` () =
    let source =
        "module Test\ntype R = { mutable A: int }\nlet f () =\n    let r = { A = 0 }\n    r.A <- 1\n    r"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``only the leading run folds in`` () =
    let source =
        klass
        + "let f () =\n    let h = Henkilo()\n    h.Id <- 1L\n    printfn \"tail\"\n    h.Etunimi <- \"x\"\n    h"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal(1, s.Count)
        Assert.Equal("Henkilo(Id = 1L)", s.ReplacementText)
    | other -> failwithf "Expected one suggestion covering only the leading set, got %A" other

[<Fact>]
let ``a long construction is laid out across lines and still compiles`` () =
    // seven properties on one line made a 380-character line on the sample
    // this rule was written for
    let wide =
        "module Test\ntype W() =\n    member val Alpha = \"\" with get, set\n    member val Beta = \"\" with get, set\n    member val Gamma = \"\" with get, set\n"

    let source =
        wide
        + "let f (someRatherLongInputName: string) =\n    let w = W()\n    w.Alpha <- someRatherLongInputName + \"aaaaaaaaaaaaaaaa\"\n    w.Beta <- someRatherLongInputName + \"bbbbbbbbbbbbbbbb\"\n    w.Gamma <- someRatherLongInputName + \"cccccccccccccccc\"\n    w"

    match objInitIn source with
    | [ s ] ->
        Assert.Contains("\n", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")

        for line in patched.Split '\n' do
            Assert.True(line.TrimEnd().Length <= 110, $"line too long: %s{line}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``new plus existing constructor arguments`` () =
    let source =
        "module Test\ntype P(name: string) =\n    member val Name = name with get, set\n    member val Age = 0 with get, set\nlet f () =\n    let p = new P(\"bob\")\n    p.Age <- 42\n    p"

    match objInitIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``several constructor arguments keep their order`` () =
    let source =
        "module Test\ntype P(a: string, b: int) =\n    member val A = a with get, set\n    member val B = b with get, set\n    member val Age = 0 with get, set\nlet f () =\n    let p = P(\"x\", 1)\n    p.Age <- 42\n    p"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("P(\"x\", 1, Age = 42)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``empty parens written with a space still splice correctly`` () =
    // `T( )` does not end with "()" — the naive branch would emit `T( , Age = 42)`
    let source =
        "module Test\ntype P() =\n    member val Age = 0 with get, set\nlet f () =\n    let p = P( )\n    p.Age <- 42\n    p"

    match objInitIn source with
    | [] -> () // standing down is acceptable
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a generic type's construction splices correctly`` () =
    let source =
        "module Test\nopen System.Collections.Generic\nlet f () =\n    let d = Dictionary<string, int>()\n    d.Capacity <- 16\n    d"

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a constructor parameter feeding the property still folds`` () =
    // type X(y) with settable Y: the ctor sets 5, the named property
    // overwrites to 4 — same as the sequential form, verified
    let source =
        "module Test\ntype X(y: int) =\n    member val Y = y with get, set\nlet f () =\n    let x = X(5)\n    x.Y <- 4\n    x"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("X(5, Y = 4)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a property sharing a constructor parameter's NAME stands down`` () =
    // `B(5, Size = 4)` binds Size to the ctor parameter and fails FS0500
    let source =
        "module Test\ntype B(Size: int) =\n    member val Size = Size with get, set\nlet f () =\n    let b = B(5)\n    b.Size <- 4\n    b"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``assignments with nothing after them must not orphan the binding`` () =
    // `let h = Henkilo()` + sets and NO trailing expression: folding them
    // away would leave a let with no body, which does not compile
    let source =
        "module Test\ntype H() =\n    member val Id = 0L with get, set\nlet f () =\n    let h = H()\n    h.Id <- 1L"

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a static factory method is not a construction`` () =
    // `Factory.Create(Id = 1L)` binds Id as a NAMED ARGUMENT to the method,
    // not as a property set — a different call entirely
    let source =
        "module Test\ntype H() =\n    member val Id = 0L with get, set\ntype Factory =\n    static member Create () = H()\nlet f () =\n    let h = Factory.Create()\n    h.Id <- 1L\n    h"

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a factory whose parameter shares the property name must not silently rebind`` () =
    // the dangerous shape: Create has an `Id` parameter, so `Create(Id = 1L)`
    // COMPILES but calls something else entirely
    let source =
        "module Test\ntype H() =\n    member val Id = 0L with get, set\ntype Factory =\n    static member Create (?Id: int64) = H()\nlet f () =\n    let h = Factory.Create()\n    h.Id <- 1L\n    h"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a cast value is parenthesised`` () =
    // SQLProvider: `Connection = con :?> SqlConnection` parses as
    // `(Connection = con) :?> SqlConnection` — an equality against an
    // undefined `Connection`. The cast binds looser than the named `=`.
    let source =
        "module Test\ntype Conn() = class end\ntype Cmd() =\n    member val Connection : Conn = Conn() with get, set\nlet f (con: obj) =\n    let cmd = Cmd()\n    cmd.Connection <- con :?> Conn\n    cmd"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Cmd(Connection = (con :?> Conn))", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a type-annotated constructor argument stands down`` () =
    // after `m: Henkilo` the parser is reading a TYPE, and the comma that
    // would introduce `Id = 1L` ends it: `Wrap(m: Henkilo, Id = 1L)` is
    // "Unexpected symbol ',' in expression" (Fuuga's McpToolRouting)
    let source =
        klass
        + "type Wrap(h: Henkilo) =\n    member val Id = 0L with get, set\nlet f (m: Henkilo) =\n    let w = Wrap(m: Henkilo)\n    w.Id <- 1L\n    w"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a plain constructor argument still folds`` () =
    let source =
        klass
        + "type Wrap(h: Henkilo) =\n    member val Id = 0L with get, set\nlet f (m: Henkilo) =\n    let w = Wrap(m)\n    w.Id <- 1L\n    w"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Wrap(m, Id = 1L)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected the plain argument to fold, got %A" other

[<Fact>]
let ``a construction without parentheses stands down`` () =
    // `ProcessStartInfo "dotnet"` has no argument list to splice named
    // properties into: the splice gave `ProcessStartInfo "dotnet"(Arguments = ...)`
    // and "This value is not a function and cannot be applied" (Fable's
    // MSBuildCrackerResolver)
    let source =
        "module Test\ntype Wrap(name: string) =\n    member val Id = 0L with get, set\nlet f () =\n    let w = Wrap \"x\"\n    w.Id <- 1L\n    w"

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a call past 100 columns takes the fantomas layout under the let`` () =
    // the compiler's ShadowPass.fs: properties hanging under the open
    // paren with a dangling `)` failed fantomas --check, and `null` had
    // gained parentheses the original never had
    let source =
        "module Test\ntype ProcessStartInformation() =\n    member val FileName = \"\" with get, set\n    member val Arguments = \"\" with get, set\n    member val WorkingDirectory: string = null with get, set\n    member val RedirectStandardOutput = false with get, set\nlet f (arguments: string) =\n    let psi = ProcessStartInformation()\n    psi.FileName <- \"dotnet\"\n    psi.Arguments <- arguments\n    psi.WorkingDirectory <- null\n    psi.RedirectStandardOutput <- true\n    psi"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal(
            "\n        ProcessStartInformation(\n            FileName = \"dotnet\",\n            Arguments = arguments,\n            WorkingDirectory = null,\n            RedirectStandardOutput = true\n        )",
            s.ReplacementText
        )

        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Contains("    let psi =\n        ProcessStartInformation(\n", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a short call with a null and a negative literal stays on one line, unparenthesised`` () =
    let source =
        "module Test\ntype Cfg() =\n    member val Name: string = null with get, set\n    member val Depth = 0 with get, set\nlet f () =\n    let c = Cfg()\n    c.Name <- null\n    c.Depth <- -1\n    c"

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Cfg(Name = null, Depth = -1)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other
