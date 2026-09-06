module FSharp.Refactor.Tests.ObjectDesignTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open FSharp.Compiler.Syntax

// ---- FR0031 StringConcat ----

let private concatIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    StringConcat.find tree sourceText checkResults

let private assertConcat (source: string) (expectedReplacement: string) =
    match concatIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one concat suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``literal and identifier chain becomes interpolation`` () =
    assertConcat "let f (name: string) = \"Hello \" + name + \"!\"" "$\"Hello {name}!\""

[<Fact>]
let ``dotted string property is a hole`` () =
    assertConcat
        "type P = { Label: string }\nlet f (prefix: string) (p: P) = prefix + \": \" + p.Label"
        "$\"{prefix}: {p.Label}\""

[<Fact>]
let ``braces or percent in a literal leave the chain alone`` () =
    // $"{{100%%}} {name}" reads worse than the concatenation it replaces
    Assert.Empty(concatIn "let f (name: string) = \"{100%} \" + name")

[<Fact>]
let ``non-string operand chain is left alone`` () =
    Assert.Empty(concatIn "let f (n: int) = n + 1")

[<Fact>]
let ``method-call operand is left alone`` () =
    Assert.Empty(concatIn "let f (name: string) = \"Hello \" + name.Trim()")

[<Fact>]
let ``all-literal chain is left alone`` () =
    Assert.Empty(concatIn "let f () = \"a\" + \"b\"")

[<Fact>]
let ``literal-free chain is left alone`` () =
    Assert.Empty(concatIn "let f (a: string) (b: string) = a + b")

// ---- FR0032 / FR0033 ObjectDesign ----

let private designIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    // --api-changes on: the public test types keep their FR0033 notes
    ObjectDesign.find true tree sourceText checkResults

/// The editor's view: no API changes, so FR0033 only reaches confined members.
let private designConfinedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ObjectDesign.find false tree sourceText checkResults

[<Fact>]
let ``new-constructed disposable field without IDisposable is noted`` () =
    let disposables, _, _ =
        designIn "type Holder() =\n    let stream = new System.IO.MemoryStream()\n    member _.Size = stream.Length"

    match disposables with
    | [ s ] ->
        Assert.Equal("Holder", s.TypeName)
        Assert.Equal("stream", s.FieldName)
    | other -> failwithf "Expected exactly one disposable-field note, got %A" other

[<Fact>]
let ``implementing IDisposable silences the field note`` () =
    let disposables, _, _ =
        designIn
            "type Holder() =\n    let stream = new System.IO.MemoryStream()\n    member _.Size = stream.Length\n\n    interface System.IDisposable with\n        member _.Dispose() = stream.Dispose()"

    Assert.Empty disposables

[<Fact>]
let ``injected disposable is not owned`` () =
    let disposables, _, _ =
        designIn "type Holder(stream: System.IO.MemoryStream) =\n    let s = stream\n    member _.Size = s.Length"

    Assert.Empty disposables

[<Fact>]
let ``member without instance state can be static`` () =
    let _, statics, _ =
        designIn
            "type Calc(seed: int) =\n    let offset = seed * 2\n    member _.Twice(x: int) = x * 2\n    member _.WithOffset(x: int) = x + offset"

    match statics with
    | [ s ] -> Assert.Equal("Twice", s.MemberName)
    | other -> failwithf "Expected exactly one static-member note, got %A" other

[<Fact>]
let ``member using the self identifier stays instance`` () =
    let _, statics, _ =
        designIn "type Calc() =\n    member this.Twice(x: int) = this.Base + x\n    member _.Base = 2"

    Assert.Empty statics

[<Fact>]
let ``member using a constructor parameter stays instance`` () =
    let _, statics, _ =
        designIn "type Calc(seed: int) =\n    member _.Offset(x: int) = x + seed"

    Assert.Empty statics

[<Fact>]
let ``override members are never suggested static`` () =
    let _, statics, _ = designIn "type Desc() =\n    override _.ToString() = \"desc\""

    Assert.Empty statics

[<Fact>]
let ``member parameter shadowing a field still counts as static`` () =
    let _, statics, _ =
        designIn
            "type Calc() =\n    let offset = 2\n    member _.Apply(offset: int) = offset + 1\n    member _.Off = offset"

    match statics with
    | [ s ] -> Assert.Equal("Apply", s.MemberName)
    | other -> failwithf "Expected exactly one shadowed-param note, got %A" other

[<Fact>]
let ``computation expression builder members stay instance`` () =
    // F# calls builder members on the builder value; static would break the CE
    let _, statics, _ =
        designIn
            "type MaybeBuilder() =\n    member _.Bind(m: int option, f: int -> int option) = Option.bind f m\n    member _.Return(x: int) = Some x\nlet maybe = MaybeBuilder()"

    Assert.Empty statics

[<Fact>]
let ``custom operation members stay instance`` () =
    let _, statics, _ =
        designIn
            "type Cfg() =\n    member _.Yield(_: unit) = 0\n    [<CustomOperation \"width\">]\n    member _.Width(state: int, w: int) = state + w"

    Assert.Empty statics

[<Fact>]
let ``members of a subclass stay instance`` () =
    // frameworks (SignalR hubs, controllers) dispatch subclass members on
    // instances by name; static would break the contract
    let _, statics, _ =
        designIn
            "type Base() =\n    member _.Tag = 1\ntype Hub() =\n    inherit Base()\n    member _.Send(msg: string) = msg.Length"

    Assert.Empty statics

[<Fact>]
let ``two-term concat is left alone`` () =
    // path + ".bak" reads fine; interpolation only pays off from three parts
    Assert.Empty(concatIn "let f (path: string) = path + \".bak\"")

[<Fact>]
let ``copy-and-update of constructor state counts as instance use`` () =
    // regression: `{ state with ... }` only mentions `state` in the record
    // copy source, which the AST walker does not visit as its own node
    let _, statics, _ =
        designIn "type St = { P: int }\ntype B(state: St) =\n    member _.WithP(p: int) = B({ state with P = p })"

    Assert.Empty statics

[<Fact>]
let ``a verbatim prefix chain becomes a verbatim interpolation`` () =
    // path chains are exactly where @-strings appear; the result is $@"..."
    assertConcat "let f (name: string) = @\"C:\out\\\" + name + \".txt\"" "$@\"C:\out\{name}.txt\""

[<Fact>]
let ``three or more holes keep the concat chain`` () =
    // measured: the F# compiler turns SMALL interpolations into
    // String.Concat, but a 3-hole one takes the String.Format path —
    // 4.9x slower and 2.3x the allocation of the + chain it would
    // replace, which is already a single String.Concat call
    Assert.Empty(concatIn "let f (a: string) (b: string) (c: string) = \"[\" + a + \",\" + b + \",\" + c + \"]\"")

[<Fact>]
let ``two holes still become an interpolation`` () =
    assertConcat "let f (a: string) (b: string) = \"x\" + a + \"-\" + b" "$\"x{a}-{b}\""

[<Fact>]
let ``an attributed member is framework territory and stays instance`` () =
    // [<Fact>] tests, [<Benchmark>] methods (BenchmarkDotNet REQUIRES
    // instance), controller actions: reflective dispatch owns the shape
    let _, statics, _ =
        designIn
            "module Test\nopen Xunit\ntype Suite() =\n    [<Fact>]\n    member _.``adds up`` () = Assert.True(1 + 1 = 2)"

    Assert.Empty statics

[<Fact>]
let ``the concat alternative of a plus chain also typechecks`` () =
    let source = "module Test\nlet f (a: string) (b: string) = \"x\" + a + \"-\" + b"

    match concatIn source with
    | [ s ] ->
        Assert.Equal(Some "System.String.Concat(\"x\", a, \"-\", b)", s.ConcatAlternative)
        let patched = applyEdit source s.Range s.ConcatAlternative.Value
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``the concat alternative uses the short spelling under open System`` () =
    let source =
        "module Test\nopen System\nlet f (a: string) (b: string) = \"x\" + a + \"-\" + b"

    match concatIn source with
    | [ s ] -> Assert.Equal(Some "String.Concat(\"x\", a, \"-\", b)", s.ConcatAlternative)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0032: the editor fix appends a plain IDisposable disposing every created field`` () =
    let source =
        "module Test\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let reader = new StreamReader(stream)\n    member _.Read() = reader.ReadLine()"

    let disposables, _, _ = designIn source

    match disposables with
    | [ first; second ] ->
        Assert.Equal("stream", first.FieldName)
        Assert.True(first.Fix.IsSome, "the first field carries the type's fix")
        Assert.True(second.Fix.IsNone, "the second field carries none")
        let r, _, replacement = first.Fix.Value
        let patched = applyEdit source r replacement
        Assert.Contains("interface System.IDisposable with", patched)
        Assert.Contains("stream.Dispose()", patched)
        Assert.Contains("reader.Dispose()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected two leaked-field findings, got %A" other

[<Fact>]
let ``FR0047: the editor fix disposes the missed field first in Dispose`` () =
    let source =
        "module Test\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let reader = new StreamReader(stream)\n    interface System.IDisposable with\n        member _.Dispose() =\n            reader.Dispose()"

    let _, _, undisposed = designIn source

    match undisposed with
    | [ s ] ->
        Assert.Equal("stream", s.FieldName)
        let r, _, replacement = s.Fix.Value
        let patched = applyEdit source r replacement
        Assert.Contains("stream.Dispose()\n            reader.Dispose()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one undisposed-field finding, got %A" other

[<Fact>]
let ``FR0032: a type inheriting a disposable base is noted without the interface fix`` () =
    let source =
        "module Test\nopen System.IO\ntype Holder(path: string) =\n    inherit MemoryStream()\n    let reader = new StreamReader(path)\n    member _.Read() = reader.ReadLine()"

    let disposables, _, _ = designIn source

    match disposables with
    | [ s ] ->
        Assert.True(s.Fix.IsNone, "a disposable base makes the added interface a duplicate")
        Assert.Equal(Some "MemoryStream", s.DisposableBase)
    | other -> failwithf "Expected one leaked-field finding, got %A" other

[<Fact>]
let ``FR0032: a disposable built with the object itself is the framework's to dispose`` () =
    // MonoGame: `new GraphicsDeviceManager(this)` registers with the Game,
    // which disposes it; Kasino drew a note for exactly that
    let source =
        "module Test\ntype Manager(owner: obj) =\n    interface System.IDisposable with\n        member _.Dispose() = ()\ntype Game() as this =\n    let manager = new Manager(this)\n    member _.Manager = manager\ntype Plain() =\n    let manager = new Manager(null)\n    member _.Manager = manager"

    let tree, sourceText, checkResults = parseAndCheck source
    let disposables, _, _ = ObjectDesign.find true tree sourceText checkResults

    match disposables with
    | [ s ] -> Assert.Equal("Plain", s.TypeName)
    | other -> failwithf "Expected only the plain type's note, got %A" other

[<Fact>]
let ``FR0031: an unannotated parameter typed only by the chain keeps its + chain`` () =
    // the F# compiler's `qualifiedMangledNameOfTyconRef tcref nm`: a plain
    // hole lets `nm` generalise (FS0034 against its signature file), and a
    // `%s` hole would leave the String.Concat fast path — the chain stays
    let signature = "module Test\nval qualifiedName: string -> string -> string"

    let implementation =
        "module Test\nlet qualifiedName (tcref: string) nm = tcref + \"-\" + nm + \"!\""

    let tree, sourceText, check, baseline, _ =
        parseAndCheckSigned signature implementation

    Assert.Empty baseline

    match StringConcat.find tree sourceText check with
    | [] -> ()
    | other -> failwithf "Expected one concat suggestion, got %A" other

// ---- FR0032 / FR0047: Dispose paths one hop away, inherited IDisposable, no-op disposables ----

[<Fact>]
let ``FR0047: an interface Dispose delegating to the type's own Dispose member is followed`` () =
    // the F# compiler's NativeDllResolveHandlerCoreClr: `member _.Dispose()`
    // disposes the field, `interface IDisposable` calls `this.Dispose()`
    let _, _, undisposed =
        designIn
            "module Test\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    member _.Dispose() = stream.Dispose()\n    interface System.IDisposable with\n        member this.Dispose() = this.Dispose()"

    Assert.Empty undisposed

[<Fact>]
let ``FR0047: an interface Dispose delegating to a let-bound function is followed`` () =
    // TcImports: `let dispose () = ... (disposal :> IDisposable).Dispose()`
    // and `interface IDisposable with member _.Dispose() = dispose ()`
    let _, _, undisposed =
        designIn
            "module Test\nopen System\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let dispose () = (stream :> IDisposable).Dispose()\n    interface IDisposable with\n        member _.Dispose() = dispose ()"

    Assert.Empty undisposed

[<Fact>]
let ``FR0047: a delegate that disposes nothing still leaves the field noted`` () =
    let _, _, undisposed =
        designIn
            "module Test\nopen System.IO\ntype Holder(path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    member _.Dispose() = ()\n    interface System.IDisposable with\n        member this.Dispose() = this.Dispose()"

    Assert.Single undisposed |> ignore

[<Fact>]
let ``FR0032: an interface that inherits IDisposable makes the type disposable`` () =
    // fantomas's LSPFantomasService implements FantomasService, which
    // inherits IDisposable: the type IS disposable, so FR0032 stays quiet.
    // Its Dispose only cancels the cts, though, which FR0047 now says
    // (the real service leaks the handle exactly this way)
    let disposables, _, undisposed =
        designIn
            "module Test\nopen System\nopen System.Threading\ntype Service =\n    interface\n        inherit IDisposable\n        abstract Run: unit -> unit\n    end\ntype Impl() =\n    let cts = new CancellationTokenSource()\n    interface Service with\n        member _.Dispose() = cts.Cancel()\n        member _.Run() = ()"

    Assert.Empty disposables

    match undisposed with
    | [ s ] ->
        Assert.Equal("cts", s.FieldName)
        Assert.True s.MentionedOnly
    | other -> failwithf "Expected the cancel-without-dispose note, got %A" other

[<Fact>]
let ``FR0032: a StringReader field owns nothing`` () =
    // fsharp.formatting's FsiSession: `let inStream = new StringReader("")`
    let disposables, _, _ =
        designIn
            "module Test\nopen System.IO\ntype Session() =\n    let inStream = new StringReader(\"\")\n    member _.Read() = inStream.ReadLine()"

    Assert.Empty disposables
// ---- FR0033 audit guards ----

[<Fact>]
let ``FR0033: an instance let bound by a tuple pattern is instance state`` () =
    // FCS GraphChecking: `let sigToImpl, implToSig = buildBiDirectionalMaps
    // goodPairs`, read by the members — every binder of the pattern counts
    let _, statics, _ =
        designIn
            "module Test\ntype Pairs(pairs: (int * int) list) =\n    let sigToImpl, implToSig = List.unzip pairs\n    member _.Impl(i: int) = List.item i implToSig\n    member _.Sig(i: int) = List.item i sigToImpl\n    member _.Twice(x: int) = x * 2"

    match statics with
    | [ s ] -> Assert.Equal("Twice", s.MemberName)
    | other -> failwithf "Expected only the Twice note, got %A" other

[<Fact>]
let ``FR0033: a constructor parameter applied in a record copy source counts`` () =
    // FCS Symbols: `FSharpDisplayContext(fun g -> { denv g with ... })` —
    // the copy source is an application of the ctor parameter, not a name
    let _, statics, _ =
        designIn
            "module Test\ntype Env = { Short: bool }\ntype Ctx(denv: int -> Env) =\n    member _.WithShort(shortNames: bool) = Ctx(fun g -> { denv g with Short = shortNames })"

    Assert.Empty statics

[<Fact>]
let ``FR0033: an instance let function called from a match! scrutinee counts`` () =
    // FCS TransparentCompiler: `match! ComputeItemKeyStore(...) with` inside
    // an async member body reads the instance let function
    let _, statics, _ =
        designIn
            "module Test\ntype Store(cache: System.Collections.Generic.Dictionary<string, int>) =\n    let Compute (name: string) =\n        async { return (if cache.ContainsKey name then Some cache.[name] else None) }\n    member _.Find(name: string) =\n        async {\n            match! Compute name with\n            | None -> return 0\n            | Some v -> return v\n        }"

    Assert.Empty statics

[<Fact>]
let ``the index carries a match! scrutinee exactly once`` () =
    // the SDK walker skips it; the supplement lifts it — and must not
    // double it, or every rule counting expressions would count twice
    let tree, _ =
        parse
            "module Test\nlet f (g: int -> Async<int option>) =\n    async {\n        match! g 1 with\n        | None -> return 0\n        | Some v -> return v\n    }"

    let index = AstIndex.ofTree tree

    let scrutinees =
        index.Exprs
        |> Array.filter (fun (_, e) ->
            match e with
            | SynExpr.App(funcExpr = SynExpr.Ident g) -> g.idText = "g"
            | _ -> false)

    Assert.Equal(1, scrutinees.Length)

[<Fact>]
let ``FR0033: a public member is an API change and waits for --api-changes`` () =
    let source = "module Test\ntype Calc() =\n    member _.Twice(x: int) = x * 2"
    let _, confined, _ = designConfinedIn source
    Assert.Empty confined

    let _, widened, _ = designIn source

    match widened with
    | [ s ] -> Assert.Equal("Twice", s.MemberName)
    | other -> failwithf "Expected the Twice note under --api-changes, got %A" other

[<Fact>]
let ``FR0033: a private type or member is confined and noted without opt-in`` () =
    let _, byType, _ =
        designConfinedIn "module Test\ntype private Calc() =\n    member _.Twice(x: int) = x * 2"

    let _, byMember, _ =
        designConfinedIn "module Test\ntype Calc() =\n    member internal _.Twice(x: int) = x * 2"

    match byType, byMember with
    | [ a ], [ b ] ->
        Assert.Equal("Twice", a.MemberName)
        Assert.Equal("Twice", b.MemberName)
    | other -> failwithf "Expected one note each, got %A" other

[<Fact>]
let ``FR0033: a member a sibling signature declares stays instance`` () =
    // FCS prim-parsing: `IParseState.RaiseError` is spelled out in the
    // .fsi; the signature owns the shape, so only a private member could
    // change
    let signature =
        "module Test\ntype Calc =\n    new: unit -> Calc\n    member Twice: x: int -> int"

    let implementation =
        "module Test\ntype Calc() =\n    member _.Twice(x: int) = x * 2"

    let tree, sourceText, check, baseline, _ =
        parseAndCheckSigned signature implementation

    Assert.Empty baseline
    let _, statics, _ = ObjectDesign.find true tree sourceText check
    Assert.Empty statics

[<Fact>]
let ``FR0033: protocol stubs and inline templates are not computations`` () =
    // fsharp.formatting's fake fsi event loop: `Run() = ()`; FCS's
    // `_DebugKeyStoreNoop`: `member inline _.WriteRange(_m) = ()`
    let _, statics, _ =
        designIn
            "module Test\ntype Loop() =\n    member _.Run() = ()\n    member _.Default() = Unchecked.defaultof<int>\n    member inline _.Write(x: int) = x + 1\n    member _.Invoke(f: unit -> int) = f ()"

    match statics with
    | [ s ] -> Assert.Equal("Invoke", s.MemberName)
    | other -> failwithf "Expected only the Invoke note, got %A" other

[<Fact>]
let ``FR0033: a type whose instances are boxed to obj is consumed by reflection`` () =
    // fsharp.formatting's `CreateNoOpFsiObject() = box (NoOpFsiObject())`
    // hands the instance to reflection, where a static member is invisible
    let _, statics, _ =
        designIn
            "module Test\ntype Fake() =\n    member _.Invoke(f: unit -> int) = f ()\ntype Plain() =\n    member _.Call(f: unit -> int) = f ()\nlet handoff = box (Fake())"

    match statics with
    | [ s ] -> Assert.Equal("Call", s.MemberName)
    | other -> failwithf "Expected only Plain's note, got %A" other

// ---- FR0148 DisposeWithoutInterface ----

let private disposeWithoutInterfaceIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ObjectDesign.disposeWithoutInterface tree sourceText checkResults

[<Fact>]
let ``FR0148: a public Dispose on a type without IDisposable is noted`` () =
    match
        disposeWithoutInterfaceIn
            "module Test\nopen System.IO\ntype Session(inner: MemoryStream) =\n    member _.Dispose() = inner.Dispose()"
    with
    | [ s ] -> Assert.Equal("Session", s.TypeName)
    | other -> failwithf "Expected one note, got %A" other

[<Fact>]
let ``FR0148: a type implementing IDisposable, or inheriting one, is fine`` () =
    Assert.Empty(
        disposeWithoutInterfaceIn
            "module Test\nopen System\nopen System.IO\ntype Session(inner: MemoryStream) =\n    member _.Dispose() = inner.Dispose()\n    interface IDisposable with\n        member this.Dispose() = this.Dispose()"
    )

    Assert.Empty(
        disposeWithoutInterfaceIn
            "module Test\nopen System.IO\ntype Session() =\n    inherit MemoryStream()\n    member _.Dispose() = ()"
    )

[<Fact>]
let ``FR0148: a private Dispose is the type's own business`` () =
    Assert.Empty(
        disposeWithoutInterfaceIn
            "module Test\nopen System.IO\ntype Session(inner: MemoryStream) =\n    member private _.Dispose() = inner.Dispose()"
    )
