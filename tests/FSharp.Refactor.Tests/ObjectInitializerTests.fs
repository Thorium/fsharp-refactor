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
        + fsharp
            """
            let f () =
                let h = Henkilo()
                h.Id <- 1L
                h.Etunimi <- "x"
                h
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal(2, s.Count)
        Assert.Equal("""Henkilo(Id = 1L, Etunimi = "x")""", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``the new keyword is preserved`` () =
    let source =
        klass
        + fsharp
            """
            let f () =
                let h = new Henkilo()
                h.Id <- 1L
                h
            """

    match objInitIn source with
    | [ s ] -> Assert.Equal("new Henkilo(Id = 1L)", s.ReplacementText)
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``existing constructor arguments are kept and the properties appended`` () =
    let source =
        fsharp
            """
            module Test
            type P(name: string) =
                member val Name = name with get, set
                member val Age = 0 with get, set
            let f () =
                let p = P("bob")
                p.Age <- 42
                p
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("""P("bob", Age = 42)""", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``an unrelated statement in between stops the fold`` () =
    // moving the sets across it would change evaluation order; the author
    // lifts the line themselves if they want the rewrite
    let source =
        klass
        + fsharp
            """
            let f () =
                let h = Henkilo()
                printfn "between"
                h.Id <- 1L
                h
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a value that reads the object cannot move into its construction`` () =
    let source =
        klass
        + fsharp
            """
            let f () =
                let h = Henkilo()
                h.Id <- h.Id + 1L
                h
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a repeated property is left alone`` () =
    // two writes would collapse into one
    let source =
        klass
        + fsharp
            """
            let f () =
                let h = Henkilo()
                h.Id <- 1L
                h.Id <- 2L
                h
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a record is not an object initializer`` () =
    let source =
        fsharp
            """
            module Test
            type R = { mutable A: int }
            let f () =
                let r = { A = 0 }
                r.A <- 1
                r
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``only the leading run folds in`` () =
    let source =
        klass
        + fsharp
            """
            let f () =
                let h = Henkilo()
                h.Id <- 1L
                printfn "tail"
                h.Etunimi <- "x"
                h
            """

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
        fsharp
            """
            module Test
            type W() =
                member val Alpha = "" with get, set
                member val Beta = "" with get, set
                member val Gamma = "" with get, set

            """

    let source =
        wide
        + fsharp
            """
            let f (someRatherLongInputName: string) =
                let w = W()
                w.Alpha <- someRatherLongInputName + "aaaaaaaaaaaaaaaa"
                w.Beta <- someRatherLongInputName + "bbbbbbbbbbbbbbbb"
                w.Gamma <- someRatherLongInputName + "cccccccccccccccc"
                w
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Contains("\n", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched

        for line in patched.Split '\n' do
            Assert.True(line.TrimEnd().Length <= 110, $"line too long: %s{line}")
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``new plus existing constructor arguments`` () =
    let source =
        fsharp
            """
            module Test
            type P(name: string) =
                member val Name = name with get, set
                member val Age = 0 with get, set
            let f () =
                let p = new P("bob")
                p.Age <- 42
                p
            """

    match objInitIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``several constructor arguments keep their order`` () =
    let source =
        fsharp
            """
            module Test
            type P(a: string, b: int) =
                member val A = a with get, set
                member val B = b with get, set
                member val Age = 0 with get, set
            let f () =
                let p = P("x", 1)
                p.Age <- 42
                p
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("""P("x", 1, Age = 42)""", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``empty parens written with a space still splice correctly`` () =
    // `T( )` does not end with "()" — the naive branch would emit `T( , Age = 42)`
    let source =
        fsharp
            """
            module Test
            type P() =
                member val Age = 0 with get, set
            let f () =
                let p = P( )
                p.Age <- 42
                p
            """

    match objInitIn source with
    | [] -> () // standing down is acceptable
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a generic type's construction splices correctly`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let f () =
                let d = List<string>()
                d.Capacity <- 16
                d
            """

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a constructor parameter feeding the property still folds`` () =
    // type X(y) with settable Y: the ctor sets 5, the named property
    // overwrites to 4 — same as the sequential form, verified
    let source =
        fsharp
            """
            module Test
            type X(y: int) =
                member val Y = y with get, set
            let f () =
                let x = X(5)
                x.Y <- 4
                x
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("X(5, Y = 4)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a property sharing a constructor parameter's NAME stands down`` () =
    // `B(5, Size = 4)` binds Size to the ctor parameter and fails FS0500
    let source =
        fsharp
            """
            module Test
            type B(Size: int) =
                member val Size = Size with get, set
            let f () =
                let b = B(5)
                b.Size <- 4
                b
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``assignments with nothing after them must not orphan the binding`` () =
    // `let h = Henkilo()` + sets and NO trailing expression: folding them
    // away would leave a let with no body, which does not compile
    let source =
        fsharp
            """
            module Test
            type H() =
                member val Id = 0L with get, set
            let f () =
                let h = H()
                h.Id <- 1L
            """

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a static factory method is not a construction`` () =
    // `Factory.Create(Id = 1L)` binds Id as a NAMED ARGUMENT to the method,
    // not as a property set — a different call entirely
    let source =
        fsharp
            """
            module Test
            type H() =
                member val Id = 0L with get, set
            type Factory =
                static member Create () = H()
            let f () =
                let h = Factory.Create()
                h.Id <- 1L
                h
            """

    match objInitIn source with
    | [] -> ()
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected at most one suggestion, got %A" other

[<Fact>]
let ``a factory whose parameter shares the property name must not silently rebind`` () =
    // the dangerous shape: Create has an `Id` parameter, so `Create(Id = 1L)`
    // COMPILES but calls something else entirely
    let source =
        fsharp
            """
            module Test
            type H() =
                member val Id = 0L with get, set
            type Factory =
                static member Create (?Id: int64) = H()
            let f () =
                let h = Factory.Create()
                h.Id <- 1L
                h
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a cast value is parenthesised`` () =
    // SQLProvider: `Connection = con :?> SqlConnection` parses as
    // `(Connection = con) :?> SqlConnection` — an equality against an
    // undefined `Connection`. The cast binds looser than the named `=`.
    let source =
        fsharp
            """
            module Test
            type Conn() = class end
            type Cmd() =
                member val Connection : Conn = Conn() with get, set
            let f (con: obj) =
                let cmd = Cmd()
                cmd.Connection <- con :?> Conn
                cmd
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Cmd(Connection = (con :?> Conn))", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a type-annotated constructor argument stands down`` () =
    // after `m: Henkilo` the parser is reading a TYPE, and the comma that
    // would introduce `Id = 1L` ends it: `Wrap(m: Henkilo, Id = 1L)` is
    // "Unexpected symbol ',' in expression" (Fuuga's McpToolRouting)
    let source =
        klass
        + fsharp
            """
            type Wrap(h: Henkilo) =
                member val Id = 0L with get, set
            let f (m: Henkilo) =
                let w = Wrap(m: Henkilo)
                w.Id <- 1L
                w
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a plain constructor argument still folds`` () =
    let source =
        klass
        + fsharp
            """
            type Wrap(h: Henkilo) =
                member val Id = 0L with get, set
            let f (m: Henkilo) =
                let w = Wrap(m)
                w.Id <- 1L
                w
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Wrap(m, Id = 1L)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected the plain argument to fold, got %A" other

[<Fact>]
let ``a construction without parentheses stands down`` () =
    // `ProcessStartInfo "dotnet"` has no argument list to splice named
    // properties into: the splice gave `ProcessStartInfo "dotnet"(Arguments = ...)`
    // and "This value is not a function and cannot be applied" (Fable's
    // MSBuildCrackerResolver)
    let source =
        fsharp
            """
            module Test
            type Wrap(name: string) =
                member val Id = 0L with get, set
            let f () =
                let w = Wrap "x"
                w.Id <- 1L
                w
            """

    Assert.Empty(objInitIn source)

[<Fact>]
let ``a call past 100 columns takes the fantomas layout under the let`` () =
    // the compiler's ShadowPass.fs: properties hanging under the open
    // paren with a dangling `)` failed fantomas --check, and `null` had
    // gained parentheses the original never had
    let source =
        fsharp
            """
            module Test
            type ProcessStartInformation() =
                member val FileName = "" with get, set
                member val Arguments = "" with get, set
                member val WorkingDirectory: string = null with get, set
                member val RedirectStandardOutput = false with get, set
            let f (arguments: string) =
                let psi = ProcessStartInformation()
                psi.FileName <- "dotnet"
                psi.Arguments <- arguments
                psi.WorkingDirectory <- null
                psi.RedirectStandardOutput <- true
                psi
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal(
            fsharp
                """

                        ProcessStartInformation(
                            FileName = "dotnet",
                            Arguments = arguments,
                            WorkingDirectory = null,
                            RedirectStandardOutput = true
                        )
                """,
            s.ReplacementText
        )

        let patched = applyEdit source s.Range s.ReplacementText

        Assert.Contains(
            fsharp
                """
                    let psi =
                        ProcessStartInformation(

                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other

[<Fact>]
let ``a short call with a null and a negative literal stays on one line, unparenthesised`` () =
    let source =
        fsharp
            """
            module Test
            type Cfg() =
                member val Name: string = null with get, set
                member val Depth = 0 with get, set
            let f () =
                let c = Cfg()
                c.Name <- null
                c.Depth <- -1
                c
            """

    match objInitIn source with
    | [ s ] ->
        Assert.Equal("Cfg(Name = null, Depth = -1)", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one suggestion, got %A" other
