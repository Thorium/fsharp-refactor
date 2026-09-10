module FSharp.Refactor.Tests.ModernizationTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing
open FSharp.Compiler.Syntax

let private applyAll (source: string) (edits: (FSharp.Compiler.Text.range * string * string) list) =
    edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

// ---- FR0073 MatchBang ----

let private matchBangsIn (source: string) =
    let tree, sourceText = parse source
    MatchBangRule.find tree sourceText

let private assertMatchBang (source: string) (expectedPatched: string) =
    match matchBangsIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one match! note, got %A" other

[<Fact>]
let ``let!-then-match collapses to match!`` () =
    assertMatchBang
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        let! x = fetch ()\n        match x with\n        | Some v -> return v\n        | None -> return 0\n    }"
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        match! fetch () with\n        | Some v -> return v\n        | None -> return 0\n    }"

[<Fact>]
let ``a binder used in a clause body must stay`` () =
    Assert.Empty(
        matchBangsIn
            "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        let! x = fetch ()\n        match x with\n        | Some _ -> return x\n        | None -> return None\n    }"
    )

[<Fact>]
let ``a use! binding manages a resource and stays`` () =
    Assert.Empty(
        matchBangsIn
            "module Test\nopen System\nlet acquire () = async { return { new IDisposable with member _.Dispose() = () } }\nlet run () =\n    async {\n        use! d = acquire ()\n        match d with\n        | _ -> return 1\n    }"
    )

// ---- FR0078 WhileBang ----

let private whileBangsIn (source: string) =
    let tree, sourceText = parse source
    MatchBangRule.findWhileBang tree sourceText

[<Fact>]
let ``the three-part mutable-condition loop collapses to while!`` () =
    match
        whileBangsIn
            "module Test\nlet check () = async { return false }\nlet step () = async { return () }\nlet run () =\n    async {\n        let! first = check ()\n        let mutable go = first\n        while go do\n            do! step ()\n            let! next = check ()\n            go <- next\n    }"
    with
    | [ s ] ->
        let patched =
            applyAll
                "module Test\nlet check () = async { return false }\nlet step () = async { return () }\nlet run () =\n    async {\n        let! first = check ()\n        let mutable go = first\n        while go do\n            do! step ()\n            let! next = check ()\n            go <- next\n    }"
                s.Edits

        Assert.Equal(
            "module Test\nlet check () = async { return false }\nlet step () = async { return () }\nlet run () =\n    async {\n        while! check () do\n            do! step ()\n    }",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one while! note, got %A" other

[<Fact>]
let ``a stale-bool while without the rebind is not while!`` () =
    // while! re-evaluates each iteration; this shape does not
    Assert.Empty(
        whileBangsIn
            "module Test\nlet check () = async { return false }\nlet run () =\n    async {\n        let! first = check ()\n        let mutable go = first\n        while go do\n            printfn \"tick\"\n    }"
    )

[<Fact>]
let ``different condition computations stay apart`` () =
    Assert.Empty(
        whileBangsIn
            "module Test\nlet check () = async { return false }\nlet other () = async { return false }\nlet run () =\n    async {\n        let! first = check ()\n        let mutable go = first\n        while go do\n            printfn \"tick\"\n            let! next = other ()\n            go <- next\n    }"
    )

// ---- FR0074 NestedRecordUpdate ----

let private nestedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    NestedRecordUpdate.find tree sourceText checkResults

let private assertFlattened (source: string) (expectedReplacement: string) =
    match nestedIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one flatten note, got %A" other

[<Fact>]
let ``a nested copy-and-update flattens to a path`` () =
    assertFlattened
        "module Test\ntype Inner = { Y: int; Z: int }\ntype Outer = { X: Inner; N: int }\nlet f (r: Outer) (v: int) = { r with X = { r.X with Y = v } }"
        "X.Y = v"

[<Fact>]
let ``multiple inner fields flatten side by side`` () =
    assertFlattened
        "module Test\ntype Inner = { Y: int; Z: int }\ntype Outer = { X: Inner; N: int }\nlet f (r: Outer) (v: int) = { r with X = { r.X with Y = v; Z = v + 1 } }"
        "X.Y = v; X.Z = v + 1"

[<Fact>]
let ``two levels flatten to a deep path`` () =
    assertFlattened
        "module Test\ntype L3 = { V: int }\ntype L2 = { Inner: L3 }\ntype L1 = { Mid: L2 }\nlet f (r: L1) (v: int) = { r with Mid = { r.Mid with Inner = { r.Mid.Inner with V = v } } }"
        "Mid.Inner.V = v"

[<Fact>]
let ``a field named after a type keeps the nested form`` () =
    // `{ r with B.A.V = v }` would resolve B as the TYPE and fail to
    // compile — the field-named-after-its-type pattern stays nested
    Assert.Empty(
        nestedIn
            "module Test\ntype A = { V: int }\ntype B = { A: A }\ntype C = { B: B }\nlet f (r: C) (v: int) = { r with B = { r.B with A = { r.B.A with V = v } } }"
    )

[<Fact>]
let ``a cross-record inner copy stays`` () =
    // the inner source is a DIFFERENT record, not r.X — nothing to flatten
    Assert.Empty(
        nestedIn
            "module Test\ntype Inner = { Y: int; Z: int }\ntype Outer = { X: Inner; N: int }\nlet f (r: Outer) (q: Inner) (v: int) = { r with X = { q with Y = v } }"
    )

[<Fact>]
let ``a field named after the module holding its type keeps the nested form`` () =
    // Nu's Kasino: `Settings: Settings.GameSettings` — the field shares its
    // name with the MODULE its type lives in. `{ menu with Settings.X = v }`
    // resolves Settings as the module and the record as GameSettings: "This
    // expression was expected to have type 'Menu' but here has type
    // 'Settings.GameSettings'", rolled back five times over
    Assert.Empty(
        nestedIn
            "module Test
module Settings =
    type GameSettings = { RandomCardBacks: bool }
type Menu = { Settings: Settings.GameSettings; N: int }
let f (menu: Menu) = { menu with Settings = { menu.Settings with RandomCardBacks = true } }"
    )

// ---- FR0075 UseBinding ----

let private useBindingsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.find tree sourceText checkResults

[<Fact>]
let ``a contained local disposable becomes a use binding`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    b + 1"
    with
    | [ s ] ->
        Assert.Equal(Some("let", "use"), s.Fix)

        let patched =
            applyEdit
                "module Test\nopen System.IO\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    b + 1"
                s.Range
                "use"

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a disposable passed on bare gets advice only`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet handOff (sink: FileStream -> unit) (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    sink stream"
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.Function("sink", false)), s.Destination)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``a disposable piped to a function names the function`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet handOff (sink: FileStream -> unit) (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    stream |> sink"
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.Function("sink", false)), s.Destination)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``a disposable returned to the caller is the caller's to dispose`` () =
    // `use` here would dispose the stream before the caller ever saw it,
    // and the caller is the one that should write `use`: the factory
    // pattern is not a leak, so nothing is said
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet openStream (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    stream"
    )

[<Fact>]
let ``a disposable handed to a returned wrapper is adopted`` () =
    // StreamReader takes ownership and outlives this scope
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet openReader (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    new StreamReader(stream)"
    )

[<Fact>]
let ``a handler chained into an HttpClient is adopted, named arguments and all`` () =
    // HttpClient disposes its handler; the chain is the ClearBank/Carmel
    // pattern that used to draw two notes per client
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.Net.Http\nlet make (url: string) =\n    let handler = new HttpClientHandler(UseCookies = false)\n    new HttpClient(handler, true, BaseAddress = System.Uri url)"
    )

[<Fact>]
let ``a disposable compared but never passed still becomes a use binding`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = if stream = null then 0 else stream.ReadByte()
    b"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a manually disposed local is managed already`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    stream.Dispose()\n    b"
    )

[<Fact>]
let ``a non-disposable local is fine`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nlet f () =\n    let sb = new System.Text.StringBuilder()\n    sb.Append('x') |> ignore\n    sb.Length"
    )

// ---- FR0076 MapIgnore ----

let private mapIgnoresIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MapIgnore.find tree sourceText checkResults

[<Fact>]
let ``List map piped to ignore becomes iter`` () =
    match mapIgnoresIn "module Test\nlet f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore" with
    | [ s ] ->
        Assert.Equal(Some "xs |> List.iter (g >> ignore)", s.ReplacementText)

        let patched =
            applyEdit
                "module Test\nlet f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore"
                s.Range
                s.ReplacementText.Value

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one map-ignore fix, got %A" other

[<Fact>]
let ``Seq map piped to ignore is the lazy bug and gets advice`` () =
    match mapIgnoresIn "module Test\nlet f (g: int -> int) (xs: seq<int>) = xs |> Seq.map g |> ignore" with
    | [ s ] ->
        Assert.Equal("Seq", s.ModuleName)
        Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one lazy advisory, got %A" other

[<Fact>]
let ``a used map result is fine`` () =
    Assert.Empty(mapIgnoresIn "module Test\nlet f (g: int -> int) (xs: int list) = xs |> List.map g |> List.sum")

[<Fact>]
let ``a shadowed map is left alone`` () =
    Assert.Empty(
        mapIgnoresIn
            "module Test\nmodule List =\n    let map (f: int -> int) (xs: int list) = xs\nlet f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore"
    )

[<Fact>]
let ``a condition computation reading the mutable binder stays`` () =
    // `let! next = step go` — deleting `go` would strand the computation
    Assert.Empty(
        whileBangsIn
            "module Test\nlet step (b: bool) = async { return not b }\nlet run () =\n    async {\n        let! first = step true\n        let mutable go = first\n        while go do\n            printfn \"tick\"\n            let! next = step go\n            go <- next\n    }"
    )

// ---- FR0079 SingleAwaitable ----

let private singlesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SingleAwaitable.find tree sourceText checkResults

[<Fact>]
let ``WhenAll over a single-task literal is noted`` () =
    match singlesIn "module Test\nopen System.Threading.Tasks\nlet f (t: Task<int>) = Task.WhenAll [| t |]" with
    | [ s ] -> Assert.Equal("Task.WhenAll", s.CallName)
    | other -> failwithf "Expected exactly one WhenAll note, got %A" other

[<Fact>]
let ``Parallel over a single computation is noted`` () =
    match singlesIn "module Test\nlet f (c: Async<int>) = Async.Parallel [ c ]" with
    | [ s ] -> Assert.Equal("Async.Parallel", s.CallName)
    | other -> failwithf "Expected exactly one Parallel note, got %A" other

[<Fact>]
let ``two tasks genuinely combine`` () =
    Assert.Empty(
        singlesIn
            "module Test\nopen System.Threading.Tasks\nlet f (a: Task<int>) (b: Task<int>) = Task.WhenAll [| a; b |]"
    )

[<Fact>]
let ``a comprehension may yield any number`` () =
    Assert.Empty(singlesIn "module Test\nlet f (cs: Async<int> list) = Async.Parallel [ for c in cs -> c ]")

// ---- FR0077 ImplementMissing ----

let private missingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ImplementMissing.find tree sourceText checkResults

[<Fact>]
let ``missing interface members get NotImplementedException stubs`` () =
    let source =
        "module Test\ntype IThing =\n    abstract member Go: unit -> int\n    abstract member Stop: string -> unit\n    abstract member Name: string\n\nlet t =\n    { new IThing with\n        member _.Go() = 1 }"

    match missingIn source with
    | [ s ] ->
        Assert.Equal<string list>([ "Stop"; "Name" ] |> List.sort, s.MissingNames |> List.sort)
        let patched = applyEdit source s.Range s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one implement-missing fix, got %A" other

[<Fact>]
let ``an inherited interface stubs in its own section`` () =
    let source =
        "module Test\nopen System\ntype IRes =\n    inherit IDisposable\n    abstract member Load: unit -> int\n\nlet r =\n    { new IRes with\n        member _.Load() = 1 }"

    match missingIn source with
    | [ s ] ->
        Assert.Contains("Dispose", s.MissingNames)
        Assert.Contains("interface IDisposable with", s.InsertText)
        let patched = applyEdit source s.Range s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one inherited-stub fix, got %A" other

[<Fact>]
let ``members implemented in the main block satisfy inherited interfaces`` () =
    // from the corpus (SQLProvider Stubs): the IDbConnection stub implements
    // Dispose in the main block, which satisfies IDisposable — an extra
    // `interface IDisposable with` stub would double-implement it (FS0767).
    // The unrelated error keeps the file in FR0077's runs-on-broken-code path.
    Assert.Empty(
        missingIn
            "module Test\nopen System\ntype IRes2 =\n    inherit IDisposable\n    abstract member Load: unit -> int\n\nlet broken: int = \"s\"\n\nlet r =\n    { new IRes2 with\n        member _.Load() = 1\n        member _.Dispose() = () }"
    )

[<Fact>]
let ``a file that already type-checks is left alone`` () =
    // a clean file has nothing missing, whatever the name-matching
    // heuristics conclude — FR0077 exists to fix FS0366, not working code
    Assert.Empty(
        missingIn
            "module Test\nopen System\ntype IRes3 =\n    inherit IDisposable\n    abstract member Load: unit -> int\n\nlet r =\n    { new IRes3 with\n        member _.Load() = 1\n        member _.Dispose() = () }"
    )

[<Fact>]
let ``a complete object expression is quiet`` () =
    Assert.Empty(
        missingIn
            "module Test\ntype IThing2 =\n    abstract member Go: unit -> int\n\nlet t =\n    { new IThing2 with\n        member _.Go() = 1 }"
    )

[<Fact>]
let ``a property with getter and setter stubs both`` () =
    let source =
        "module Test\ntype IHolder =\n    abstract member Value: int with get, set\n    abstract member Touch: unit -> unit\n\nlet h =\n    { new IHolder with\n        member _.Touch() = () }"

    match missingIn source with
    | [ s ] ->
        Assert.Contains("with get () =", s.InsertText)
        Assert.Contains("and set _v =", s.InsertText)
        let patched = applyEdit source s.Range s.InsertText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one get-set stub fix, got %A" other

// ---- FR0080 TabIndentation ----

let private tabsIn (source: string) =
    let sourceText = FSharp.Compiler.Text.SourceText.ofString source
    TabIndentation.find "Test.fs" sourceText

[<Fact>]
let ``leading tabs expand to spaces line by line`` () =
    let source = "module Test\nlet f x =\n\tlet y = x + 1\n\ty + 1"

    match tabsIn source with
    | [ s ] ->
        Assert.Equal(2, s.Edits.Length)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Equal("module Test\nlet f x =\n    let y = x + 1\n    y + 1", patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one tab note, got %A" other

[<Fact>]
let ``a tab after code is not indentation`` () =
    Assert.Empty(tabsIn "module Test\nlet s = \"a\tb\"")

[<Fact>]
let ``multiline string literals make tabs ambiguous`` () =
    // the leading tab could be CONTENT of the triple-quoted literal
    Assert.Empty(tabsIn "module Test\nlet s = \"\"\"line\n\tstill the string\"\"\"\nlet f x =\n\tx + 1")

// ---- FR0081 PathSeparator ----

let private pathsIn (source: string) =
    let tree, sourceText = parse source
    PathSeparator.find tree sourceText

[<Fact>]
let ``a backslash-joined path is noted`` () =
    match pathsIn "module Test\nlet f (dir: string) (file: string) = dir + \"\\\\\" + file" with
    | [ s ] -> Assert.Equal("\\", s.Separator)
    | other -> failwithf "Expected exactly one path note, got %A" other

[<Fact>]
let ``a slash-joined path is noted`` () =
    match pathsIn "module Test\nlet f (root: string) (name: string) = root + \"/\" + name + \".txt\"" with
    | [ s ] -> Assert.Equal("/", s.Separator)
    | other -> failwithf "Expected exactly one slash note, got %A" other

[<Fact>]
let ``a url join is not a file path`` () =
    Assert.Empty(pathsIn "module Test\nlet f (baseUrl: string) (route: string) = baseUrl + \"/\" + route")

[<Fact>]
let ``a scheme literal is not a file path`` () =
    Assert.Empty(pathsIn "module Test\nlet f (host: string) = \"https://\" + host + \"/api\"")

[<Fact>]
let ``plain text concatenation is not a path`` () =
    Assert.Empty(pathsIn "module Test\nlet f (a: string) (b: string) = a + \", \" + b")

[<Fact>]
let ``a name bound one hop away to a url makes the join a url`` () =
    // every FAKE build script of a certain vintage: `gitHome + "/" +
    // gitName + ".git"` with `gitHome = "https://github.com/" + gitOwner`
    // fifty lines up (FsXaml, Chessie, FSharp.CloudAgent, ComposableQuery)
    Assert.Empty(
        pathsIn
            "module Test\nlet gitOwner = \"fsprojects\"\nlet gitHome = \"https://github.com/\" + gitOwner\nlet gitName = \"FsXaml\"\nlet clone () = gitHome + \"/\" + gitName + \".git\""
    )

    // a local binding is read the same way
    Assert.Empty(
        pathsIn
            "module Test\nlet clone (owner: string) (name: string) =\n    let home = \"https://github.com/\" + owner\n    home + \"/\" + name + \".git\""
    )

    // ... and a directory bound one hop away still joins a path
    match pathsIn "module Test\nlet root = \"C:\\\\builds\"\nlet f (name: string) = root + \"/\" + name + \".txt\"" with
    | [ _ ] -> ()
    | other -> failwithf "Expected one path note, got %A" other

[<Fact>]
let ``a join compared or searched for is a key, not a path to build`` () =
    // fsharplint's docs generator: `"content/" + n.file = page`
    Assert.Empty(pathsIn "module Test\nlet f (file: string) (page: string) = \"content/\" + file = page")
    Assert.Empty(pathsIn "module Test\nlet f (dir: string) (file: string) (page: string) = page <> dir + \"/\" + file")

    Assert.Empty(
        pathsIn
            "module Test\nlet f (keys: System.Collections.Generic.HashSet<string>) (dir: string) (file: string) = keys.Contains(dir + \"/\" + file)"
    )

[<Fact>]
let ``a call operand is path evidence only through the file system API it invokes`` () =
    // the compiler's TypedTree: `getNameOfScopeRef scoref + "/" +
    // textOfPath (List.map fst path)` builds a mangled compilation path;
    // "path" in a function's name is not a directory
    Assert.Empty(
        pathsIn
            "module Test\nlet textOfPath (xs: string list) = String.concat \".\" xs\nlet nameOf (x: int) = string x\nlet mangled (x: int) (path: (string * int) list) = nameOf x + \"/\" + textOfPath (List.map fst path)"
    )

    // a call INTO the file system is evidence
    match pathsIn "module Test\nlet f (name: string) = System.IO.Path.GetTempPath() + \"/\" + name" with
    | [ _ ] -> ()
    | other -> failwithf "Expected one path note, got %A" other

// ---- FR0082-FR0086 RedundantSyntax ----

let private syntaxIn (source: string) =
    let tree, sourceText = parse source
    RedundantSyntax.find None tree sourceText

let private assertSyntaxFix (kind: RedundantSyntax.Kind) (source: string) (expectedPatched: string) =
    match syntaxIn source |> List.filter (fun s -> s.Kind = kind) with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(parsesCleanly patched, $"Patched source does not parse:\n%s{patched}")
    | other -> failwithf "Expected exactly one %A fix, got %A" kind other

[<Fact>]
let ``the Attribute suffix is trimmed`` () =
    assertSyntaxFix
        RedundantSyntax.Kind.AttributeSuffix
        "module Test\n[<System.SerializableAttribute>]\ntype T = { X: int }"
        "module Test\n[<System.Serializable>]\ntype T = { X: int }"

[<Fact>]
let ``an attribute named exactly Attribute keeps its name`` () =
    Assert.Empty(
        syntaxIn "module Test\n[<System.Serializable>]\ntype T = { X: int }"
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.AttributeSuffix)
    )

[<Fact>]
let ``empty attribute parens go away`` () =
    assertSyntaxFix
        RedundantSyntax.Kind.AttributeParens
        "module Test\n[<System.Serializable()>]\ntype T = { X: int }"
        "module Test\n[<System.Serializable>]\ntype T = { X: int }"

[<Fact>]
let ``redundant backticks strip at use and binder sites`` () =
    match
        syntaxIn "module Test\nlet ``plain`` = 1\nlet f () = ``plain`` + 1"
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    with
    | [ _; _ ] -> ()
    | other -> failwithf "Expected two backtick fixes, got %A" other

[<Fact>]
let ``necessary backticks stay`` () =
    Assert.Empty(
        syntaxIn "module Test\nlet ``two words`` = 1\nlet ``type`` = 2\nlet f () = ``two words`` + ``type``"
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    )

[<Fact>]
let ``a hole-free interpolated string flattens`` () =
    assertSyntaxFix
        RedundantSyntax.Kind.HoleFreeInterpolation
        "module Test\nlet s = $\"just text\""
        "module Test\nlet s = \"just text\""

[<Fact>]
let ``escaped braces keep the interpolation`` () =
    Assert.Empty(
        syntaxIn "module Test\nlet s = $\"a {{ b }}\""
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

// ---- FR0085 RedundantNew ----

let private newsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RedundantNew.find tree sourceText checkResults

[<Fact>]
let ``new on a non-disposable construction is noted`` () =
    match newsIn "module Test\nlet sb = new System.Text.StringBuilder()" with
    | [ s ] ->
        Assert.Equal("StringBuilder", s.TypeName)

        let patched =
            applyEdit "module Test\nlet sb = new System.Text.StringBuilder()" s.Range ""

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one redundant-new fix, got %A" other

[<Fact>]
let ``new on a disposable stays`` () =
    Assert.Empty(
        newsIn
            "module Test\nopen System.IO\nlet f (p: string) =\n    use s = new FileStream(p, FileMode.Open)\n    s.ReadByte()"
    )

// ---- FR0087-FR0089 PatternCleanups ----

let private cleanupsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    PatternCleanups.find tree sourceText checkResults

[<Fact>]
let ``cons of empty is a one-element list pattern`` () =
    let conses, _, _ =
        cleanupsIn "module Test\nlet f (xs: int list) =\n    match xs with\n    | x :: [] -> x\n    | _ -> 0"

    match conses with
    | [ s ] -> Assert.Equal("[ x ]", s.ReplacementText)
    | other -> failwithf "Expected exactly one cons fix, got %A" other

[<Fact>]
let ``all-wildcard case fields collapse`` () =
    let _, wilds, _ =
        cleanupsIn
            "module Test\ntype T =\n    | Pair of int * int\n    | One\nlet f (t: T) =\n    match t with\n    | Pair(_, _) -> 1\n    | One -> 0"

    match wilds with
    | [ s ] ->
        Assert.Equal("Pair", s.CaseName)
        Assert.Equal(" _", s.ReplacementText)
    | other -> failwithf "Expected exactly one wild-fields fix, got %A" other

[<Fact>]
let ``a partially bound case keeps its fields`` () =
    let _, wilds, _ =
        cleanupsIn
            "module Test\ntype T =\n    | Pair of int * int\n    | One\nlet f (t: T) =\n    match t with\n    | Pair(a, _) -> a\n    | One -> 0"

    Assert.Empty wilds

[<Fact>]
let ``a tuple filling an unannotated list literal is noted`` () =
    let _, _, tuples = cleanupsIn "module Test\nlet xs = [ 1, 2 ]"

    match tuples with
    | [ s ] -> Assert.Equal(2, s.Elements)
    | other -> failwithf "Expected exactly one tuple-in-list note, got %A" other

[<Fact>]
let ``FR0089: an annotation spelling the tuple out says the tuple is meant`` () =
    // Mibo: `let expectedInitial: Map<int, int> = Map.ofList [ 2, 25 ]` and
    // plain `(int * int) list` annotations — the slot asks for tuples
    let _, _, byBinding = cleanupsIn "module Test\nlet xs: (int * int) list = [ 1, 2 ]"
    let _, _, byExpr = cleanupsIn "module Test\nlet xs = ([ 1, 2 ] : (int * int) list)"
    Assert.Empty byBinding
    Assert.Empty byExpr

[<Fact>]
let ``FR0089: a one-entry map is the tuple list Map.ofList asks for`` () =
    // Mibo: `Map.ofList [ k, v ]`, `[ 1, 1 ] |> Map.ofSeq`, `dict [ 1, 1 ]`,
    // `Assert.Equal<Map<int, int>>(Map.ofList [ 0, 0 ], m)`
    let _, _, tuples =
        cleanupsIn
            "module Test\nlet a = Map.ofList [ 3, 6 ]\nlet b = [ 1, 1 ] |> Map.ofSeq\nlet c = dict [ 1, 1 ]\nlet d = Map.ofList [ 0, Map.ofList [ 1, 3 ] ]\nlet chunksOf (ranges: (int * int) list) = ranges.Length\nlet e = chunksOf [ 0, 2 ]\nlet f (k: int) (pairs: (int * int) list) = k + pairs.Length\nlet g = f 1 [ 2, 3 ]\nlet h = [ 4, 5 ] |> f 1"

    Assert.Empty tuples

[<Fact>]
let ``FR0089: a tupled method argument asks its own parameter`` () =
    let _, _, tuples =
        cleanupsIn
            "module Test\ntype T =\n    static member Take(n: int, pairs: (int * int) list) = n + pairs.Length\n    static member Loose(n: int, xs: 'a list) = n + xs.Length\nlet a = T.Take(1, [ 2, 3 ])\nlet b = T.Loose(1, [ 2, 3 ])"

    match tuples with
    | [ s ] -> Assert.Equal(6, s.Range.StartLine)
    | other -> failwithf "Expected only the generic-parameter note, got %A" other

[<Fact>]
let ``a semicolon list is fine`` () =
    let _, _, tuples = cleanupsIn "module Test\nlet xs = [ 1; 2 ]"
    Assert.Empty tuples

[<Fact>]
let ``prose around slashes is not a path`` () =
    Assert.Empty(pathsIn "module Test\nlet f (a: string) (b: string) = a + \" / \" + b")

[<Fact>]
let ``source-directory concatenation is a path`` () =
    match pathsIn "module Test\nlet data = __SOURCE_DIRECTORY__ + \"/data\" + \"/set.json\"" with
    | [ s ] -> Assert.Equal("/", s.Separator)
    | other -> failwithf "Expected exactly one source-dir note, got %A" other

[<Fact>]
let ``a Literal binding cannot call Path Combine`` () =
    Assert.Empty(pathsIn "module Test\n[<Literal>]\nlet DataDir = __SOURCE_DIRECTORY__ + \"/data\" + \"/set.json\"")

[<Fact>]
let ``an attribute argument cannot call Path Combine`` () =
    Assert.Empty(
        pathsIn "module Test\nopen System\n[<Obsolete(__SOURCE_DIRECTORY__ + \"/moved\" + \"/here.fs\")>]\nlet f () = 1"
    )

[<Fact>]
let ``an expression tuple list is deliberate`` () =
    let _, _, tuples =
        cleanupsIn "module Test\nlet edits (r: int) (t: string) = [ r, t, \"code\" ]"

    Assert.Empty tuples

// ---- release-review regressions ----

[<Fact>]
let ``escaped percents keep the interpolation`` () =
    // `%%` is an escaped percent in interpolated strings, a literal
    // double-percent in plain ones
    Assert.Empty(
        syntaxIn "module Test\nlet s = $\"100%%\""
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

[<Fact>]
let ``an underscore binder keeps its backticks`` () =
    // bare _ is the wildcard, not a binder
    Assert.Empty(
        syntaxIn "module Test\nlet ``_`` = 1\nlet f () = ``_`` + 1"
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    )

[<Fact>]
let ``a same-file type under the short name blocks the suffix trim`` () =
    // [<My>] would resolve to type My, not MyAttribute
    Assert.Empty(
        syntaxIn
            "module Test\ntype My() = class end\ntype MyAttribute() =\n    inherit System.Attribute()\n\n[<MyAttribute>]\nlet f () = 1"
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.AttributeSuffix)
    )

[<Fact>]
let ``spaced names and backticks inside strings are untouched`` () =
    // detection is AST-ident-based: string CONTENT is invisible, and a
    // multi-word name is not a plain identifier
    Assert.Empty(
        syntaxIn "module Test\nlet ``yes fsharp supports long variables like this`` = \" `` \""
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    )

// ---- FR0092 FailwithContext ----

let private failwithContextIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    FailwithContext.find tree sourceText checkResults

let private assertFailwithContext (source: string) (expectedPatched: string) =
    match failwithContextIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.Equal(expectedPatched, patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one failwith-context hint, got %A" other

[<Fact>]
let ``static failwith message gains the enclosing arguments`` () =
    assertFailwithContext
        "module Test\nlet mymethod (x: int) =\n    failwith \"Error\""
        "module Test\nlet mymethod (x: int) =\n    failwith $\"Error, calling mymethod with x: {x}\""

[<Fact>]
let ``every parameter is reported in order`` () =
    assertFailwithContext
        "module Test\nlet locate (name: string) (index: int) =\n    failwith \"Not found\""
        "module Test\nlet locate (name: string) (index: int) =\n    failwith $\"Not found, calling locate with name: {name}, index: {index}\""

[<Fact>]
let ``the innermost enclosing function wins`` () =
    assertFailwithContext
        "module Test\nlet outer (a: int) =\n    let inner (b: int) =\n        failwith \"Bad\"\n    inner a"
        "module Test\nlet outer (a: int) =\n    let inner (b: int) =\n        failwith $\"Bad, calling inner with b: {b}\"\n    inner a"

[<Fact>]
let ``an already interpolated message is left to its author`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod x =\n    failwith $\"Error {x}\"")

[<Fact>]
let ``a message already naming a parameter is left alone`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod (count: int) =\n    failwith \"count must be positive\"")

[<Fact>]
let ``a parameterless function has nothing to report`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod () =\n    failwith \"Error\"")

[<Fact>]
let ``a top-level failwith outside any function is left alone`` () =
    Assert.Empty(failwithContextIn "module Test\nlet value = failwith \"Error\"")

[<Fact>]
let ``braces would need escaping so the message is left alone`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod (x: int) =\n    failwith \"Bad {shape}\"")

[<Fact>]
let ``a percent sign would change meaning when interpolated`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod (x: int) =\n    failwith \"Over 100% used\"")

[<Fact>]
let ``a shadowed failwith is not ours to rewrite`` () =
    Assert.Empty(
        failwithContextIn "module Test\nlet failwith (s: string) = ()\nlet mymethod (x: int) =\n    failwith \"Error\""
    )

[<Fact>]
let ``wildcard parameters carry nothing to report`` () =
    Assert.Empty(failwithContextIn "module Test\nlet mymethod _ =\n    failwith \"Error\"")

[<Fact>]
let ``a parameter whose type prints nothing useful is not quoted`` () =
    // a byte array prints "System.Byte[]", a generic 'a whatever it is
    // bound to, a stream its type name (ilread's sigptr readers, Suave's
    // acceptor): with no parameter worth quoting there is no note
    Assert.Empty(failwithContextIn "module Test\nlet decode (bytes: byte[]) =\n    failwith \"Error\"")
    Assert.Empty(failwithContextIn "module Test\nlet decode x =\n    failwith \"Error\"")

    Assert.Empty(
        failwithContextIn "module Test\nlet decode (s: System.IO.Stream) (f: int -> int) =\n    failwith \"Error\""
    )

    // ... and a mixed list quotes only the printing ones
    assertFailwithContext
        "module Test\nlet decode (bytes: byte[]) (offset: int) =\n    failwith \"Error\""
        "module Test\nlet decode (bytes: byte[]) (offset: int) =\n    failwith $\"Error, calling decode with offset: {offset}\""

[<Fact>]
let ``a fieldless union, an enum, an option and a small record print usefully`` () =
    assertFailwithContext
        "module Test\ntype Mode =\n    | Fast\n    | Slow\ntype Point = { X: int; Y: int }\nlet run (mode: Mode) (at: Point option) =\n    failwith \"Error\""
        "module Test\ntype Mode =\n    | Fast\n    | Slow\ntype Point = { X: int; Y: int }\nlet run (mode: Mode) (at: Point option) =\n    failwith $\"Error, calling run with mode: {mode}, at: {at}\""

    // a union WITH fields prints its payload's type names
    Assert.Empty(
        failwithContextIn
            "module Test\ntype Shape =\n    | Circle of System.IO.Stream\n    | Square of byte[]\nlet run (shape: Shape) =\n    failwith \"Error\""
    )

[<Fact>]
let ``an invariant message explains itself without arguments`` () =
    // "unreachable - linear let" (the compiler), "varargs NYI" (ilread),
    // "not possible" (fantomas), "invalid case." (Suave): the branch was
    // never meant to run, and no argument says why it did
    for message in
        [ "unreachable - linear let"
          "varargs NYI"
          "not possible"
          "impossible"
          "invalid case."
          "Suave.Web.split: invalid case"
          "not implemented"
          "internal error; should not have successfully decrypted data"
          "invalid state" ] do
        Assert.Empty(failwithContextIn $"module Test\nlet run (n: int) =\n    failwith \"{message}\"")

[<Fact>]
let ``a message that is the function's own name is fslex's fallthrough`` () =
    Assert.Empty(failwithContextIn "module Test\nlet rule (n: int) =\n    failwith \"rule\"")

[<Fact>]
let ``secrets in scope are not for the log`` () =
    // Suave's Authentication.parseData throws on freshly decrypted session
    // data; interpolating the blob would log it. The function, a
    // parameter, or an enclosing module or type can carry the smell
    Assert.Empty(failwithContextIn "module Test\nlet decryptSession (blob: string) =\n    failwith \"Error\"")
    Assert.Empty(failwithContextIn "module Test\nlet parse (token: string) =\n    failwith \"Error\"")
    Assert.Empty(failwithContextIn "module Test\nlet parse (apiKey: string) =\n    failwith \"Error\"")

    Assert.Empty(
        failwithContextIn
            "namespace Test\nmodule Authentication =\n    let parseData (blob: string) =\n        failwith \"Error\""
    )

    Assert.Empty(
        failwithContextIn
            "module Test\ntype CredentialStore() =\n    member _.Parse(blob: string) =\n        let inner (line: string) = failwith \"Error\"\n        inner blob"
    )

    // an author and a tokenizer are not secrets
    assertFailwithContext
        "namespace Test\nmodule Tokenizer =\n    let author (name: string) =\n        failwith \"Error\""
        "namespace Test\nmodule Tokenizer =\n    let author (name: string) =\n        failwith $\"Error, calling author with name: {name}\""

[<Fact>]
let ``a test file's failwith is an assertion the runner already describes`` () =
    Assert.Empty(
        failwithContextIn
            "module Test\nopen Xunit\nlet expectOk (name: string) =\n    failwith \"HSTS missing\"\n[<Fact>]\nlet ``a test`` () = expectOk \"x\""
    )

[<Fact>]
let ``a message thrown twice is not a message read back`` () =
    // Hpack's `failwith "Index overrun."` twice in one function: two throws
    // sharing a text are not one reading the other, both get the note
    let twoThrows =
        failwithContextIn
            "module Test\nlet entry (idx: int) =\n    if idx <= 0 then failwith \"Index overrun.\"\n    elif idx < 10 then idx\n    else failwith \"Index overrun.\""

    Assert.Equal(2, twoThrows.Length)

    // ... while the same text spelled anywhere ELSE is somebody reading it
    Assert.Empty(
        failwithContextIn
            "module Test\nlet expected = \"Index overrun.\"\nlet entry (idx: int) =\n    if idx <= 0 then failwith \"Index overrun.\"\n    else idx"
    )

[<Fact>]
let ``a parameter is mentioned as a word, not as letters`` () =
    // ParsePynb's `x` is not mentioned by "no text property"; fsi's `ty`
    // is not mentioned by "open generic type"
    assertFailwithContext
        "module Test\nlet read (x: string) =\n    failwith \"no text property\""
        "module Test\nlet read (x: string) =\n    failwith $\"no text property, calling read with x: {x}\""

[<Fact>]
let ``a tuple parameter is left out, the named ones stay`` () =
    // Suave's `writeResource name (conn: Connection, _)`: the tuple carries
    // no name to quote, and used to disqualify the whole function
    assertFailwithContext
        "module Test\nlet write (name: string) (conn: int, _) =\n    failwith \"error\""
        "module Test\nlet write (name: string) (conn: int, _) =\n    failwith $\"error, calling write with name: {name}\""

[<Fact>]
let ``a function's wildcard arm is named so its argument can be quoted`` () =
    // Suave's `toOpcode = function ... | _ -> failwith "Invalid opcode."`:
    // the one argument has no name, so the arm that throws gets one
    let source =
        "module Test\ntype Opcode =\n    | Text\n    | Binary\nlet toOpcode = function\n    | 0uy -> Text\n    | 1uy -> Binary\n    | _ -> failwith \"Invalid opcode.\""

    match failwithContextIn source with
    | [ s ] ->
        let edits =
            (s.Range, s.OriginalText, s.ReplacementText) :: Option.toList s.PatternEdit

        let patched = applyAll source edits

        Assert.Equal(
            "module Test\ntype Opcode =\n    | Text\n    | Binary\nlet toOpcode = function\n    | 0uy -> Text\n    | 1uy -> Binary\n    | value -> failwith $\"Invalid opcode., calling toOpcode with value: {value}\"",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one function-arm hint, got %A" other

    // a `function` over a type that prints nothing stays quiet, and so does
    // a throw under a NESTED match, whose wildcard is not the argument
    Assert.Empty(
        failwithContextIn
            "module Test\nlet decode = function\n    | Some(bytes: byte[]) -> bytes.Length\n    | None -> failwith \"Error\""
    )

    Assert.Empty(
        failwithContextIn
            "module Test\nlet decode = function\n    | (n: int) when n > 0 ->\n        match n % 2 with\n        | 0 -> n\n        | _ -> failwith \"Error\"\n    | _ -> 0"
    )

[<Fact>]
let ``a File factory result leaks like a bare constructor`` () =
    // File.OpenRead is THE way to open a file; ownership transfers to the
    // caller exactly as with `new FileStream(...)`
    let suggestions =
        useBindingsIn
            "let f (path: string) =\n    let stream = System.IO.File.OpenRead path\n    let n = stream.ReadByte()\n    n"

    match suggestions with
    | [ s ] ->
        Assert.Equal("stream", s.Name)
        Assert.True s.Fix.IsSome
    | other -> failwithf "Expected exactly one use-binding suggestion, got %A" other

[<Fact>]
let ``ignore applied directly still finds the map`` () =
    let suggestions =
        mapIgnoresIn "let f (xs: int list) = ignore (xs |> List.map string)"

    match suggestions with
    | [ s ] -> Assert.Equal(Some "xs |> List.iter (string >> ignore)", s.ReplacementText)
    | other -> failwithf "Expected exactly one map-ignore suggestion, got %A" other

[<Fact>]
let ``the direct Seq map spelling is the lazy nothing-runs bug too`` () =
    let suggestions = mapIgnoresIn "let f (xs: seq<int>) = Seq.map string xs |> ignore"

    match suggestions with
    | [ s ] -> Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one seq map-ignore note, got %A" other

[<Fact>]
let ``modern indexer syntax is not a single-tuple list`` () =
    // `grid[0, 1, 2]` is INDEXING. Since F# 6 it parses as an atomic
    // application of a bracket literal — the same shape as `[ 0, 1, 2 ]` —
    // and TorchSharp code is nothing but this (6 false notes in Fuuga)
    let _, _, tuples =
        cleanupsIn
            "module Test\nlet grid = Array3D.zeroCreate<int> 3 3 3\nlet read = grid[0, 1, 2]\nlet write () = grid[0, 1, 2] <- 5"

    Assert.Empty tuples

[<Fact>]
let ``the legacy dot-bracket indexer is not a single-tuple list either`` () =
    let _, _, tuples =
        cleanupsIn "module Test\nlet grid = Array3D.zeroCreate<int> 3 3 3\nlet read = grid.[0, 1, 2]"

    Assert.Empty tuples

[<Fact>]
let ``a genuine single-tuple list still fires`` () =
    // the paste trap the rule exists for: `,` where `;` was meant
    let _, _, tuples = cleanupsIn "module Test\nlet trap = [ 1, 2 ]"

    match tuples with
    | [ s ] -> Assert.Equal(2, s.Elements)
    | other -> failwithf "Expected exactly one single-tuple note, got %A" other

[<Fact>]
let ``a spaced list ARGUMENT is still a literal, not an index`` () =
    // `f [ 1, 2 ]` with a space is a real argument (NonAtomic) — the trap
    // is just as real there, so the index gate must not swallow it; the
    // parameter is generic, so the slot asks for no tuple either
    let _, _, tuples =
        cleanupsIn "module Test\nlet f (xs: 'a list) = xs.Length\nlet n = f [ 1, 2 ]"

    match tuples with
    | [ s ] -> Assert.Equal(2, s.Elements)
    | other -> failwithf "Expected exactly one single-tuple note, got %A" other

[<Fact>]
let ``new stays where a union case would capture the construction`` () =
    // in expression position a UNION CASE wins over a type name, so `new` is
    // the only thing forcing the constructor path. Nu's OpenGL.Texture
    // declares a LazyTexture class beside a Texture.LazyTexture case:
    // dropping `new` made a six-argument construction into a one-argument
    // case application, and the tuple was checked against the case payload
    let source =
        "module Test\ntype Thing(a: int, b: int) =\n    member _.Sum = a + b\n\ntype Wrapper =\n    | Thing of Thing\n\nlet shadowed = new Thing(1, 2)"

    Assert.Empty(newsIn source)

[<Fact>]
let ``new is still dropped where nothing shadows the type`` () =
    // the guard must not cost the ordinary case
    match newsIn "module Test\nlet sb = new System.Text.StringBuilder()" with
    | [ s ] -> Assert.Equal("StringBuilder", s.TypeName)
    | other -> failwithf "Expected the plain construction, got %A" other

[<Fact>]
let ``new is dropped where one assembly holds the name at both arities`` () =
    // .NET overloads type names by arity, and a namespace is one fragment per
    // assembly. Within ONE fragment F# picks by arity, so the bare `Resp()`
    // compiles, as `TaskCompletionSource()` and `Lazy<int>(...)` do. The hazard
    // is a name SPLIT across fragments: Microsoft.Extensions.AI.Abstractions
    // holds `ChatResponse`, Microsoft.Extensions.AI holds `ChatResponse<'T>`,
    // and Fuuga's Eval failed with "takes 2 argument(s) but is here given 0".
    // A single compilation cannot stage that; the guard counts fragments, so
    // this fixture must NOT be declined
    let source =
        "namespace Test

type Resp() =
    member _.X = 1

type Resp<'a>(a: 'a, b: int) =
    member _.A = a

module M =
    let r = new Resp()"

    match newsIn source with
    | [ s ] ->
        let patched = applyEdit source s.Range ""

        Assert.True(
            typechecksCleanly patched,
            $"Patched source does not typecheck:
%s{patched}"
        )
    | other -> failwithf "Expected the one-fragment construction to qualify, got %A" other

// ---- FR0086 and an expected FormattableString ----

let private holeFreeIn (source: string) =
    syntaxIn source
    |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)

[<Fact>]
let ``a hole-free interpolation annotated as FormattableString keeps its dollar`` () =
    // the `$` is what makes the conversion to FormattableString available; a
    // plain string never converts (Fable's StringTests)
    Assert.Empty(holeFreeIn "module Test\nlet s3: System.FormattableString = $\"I have no holes\"")

[<Fact>]
let ``a hole-free interpolation passed to a method keeps its dollar`` () =
    // only the typed tree could say whether the parameter is a
    // FormattableString; a syntactic rule declines rather than guess
    Assert.Empty(holeFreeIn "module Test\nlet s = System.FormattableString.Invariant($\"no holes\")")

[<Fact>]
let ``a hole-free interpolation bound plainly still loses its dollar`` () =
    match holeFreeIn "module Test\nlet s = $\"no holes\"" with
    | [ s ] -> Assert.Equal("\"no holes\"", s.ReplacementText)
    | other -> failwithf "Expected the plain case to keep its fix, got %A" other

[<Fact>]
let ``a hole-free interpolation passed to an F# function keeps its dollar`` () =
    // Ionide's `Log.setMessageI $"..."` takes a FormattableString and its
    // spelling does not say so (FsAutoComplete's AdaptiveServerState)
    Assert.Empty(
        holeFreeIn
            "module Test\nlet setMessageI (m: System.FormattableString) = m.Format\nlet s = setMessageI $\"Enter loading projects\""
    )

[<Fact>]
let ``FR0092 leaves a message the file reads back elsewhere`` () =
    // the test below asserts on the exact text (Fuuga): amending it breaks
    // the assertion
    Assert.Empty(
        failwithContextIn
            "module Test\nlet gen (prompt: string) =\n    failwith \"model inference failed\"\nlet check () =\n    try gen \"q\" with e -> e.Message = \"model inference failed\""
    )

[<Fact>]
let ``FR0086 strips the dollar from a printfn argument when the typed tree shows no FormattableString`` () =
    let source = "module Test\nlet f () =\n    printfn $\"Status: Processing\""
    let tree, sourceText, checkResults = parseAndCheck source

    let holeFree =
        RedundantSyntax.find (Some checkResults) tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)

    match holeFree with
    | [ s ] -> Assert.Equal("\"Status: Processing\"", s.ReplacementText)
    | other -> failwithf "Expected one hole-free interpolation, got %A" other

[<Fact>]
let ``FR0086 keeps the dollar for a callee taking a FormattableString`` () =
    let source =
        "module Test\nlet log (m: System.FormattableString) = m.Format\nlet f () =\n    log $\"Status: Processing\""

    let tree, sourceText, checkResults = parseAndCheck source

    Assert.Empty(
        RedundantSyntax.find (Some checkResults) tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

[<Fact>]
let ``FR0086 keeps the dollar in an argument without the typed tree`` () =
    let source = "module Test\nlet f () =\n    printfn $\"Status: Processing\""
    let tree, sourceText = parse source

    Assert.Empty(
        RedundantSyntax.find None tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

[<Fact>]
let ``FR0077 also offers stubs returning the empty value of each member's type`` () =
    let source =
        "module Test\ntype IThing =\n    abstract member Go: unit -> int\n    abstract member Stop: string -> unit\n    abstract member Tags: string list\n    abstract member Name: string\n\nlet t =\n    { new IThing with\n        member _.Go() = 1 }"

    match missingIn source with
    | [ s ] ->
        Assert.Contains("member _.Stop(arg0) = ()", s.EmptyInsertText)
        Assert.Contains("member _.Tags = []", s.EmptyInsertText)
        Assert.Contains("member _.Name = \"\"", s.EmptyInsertText)
        Assert.DoesNotContain("NotImplementedException", s.EmptyInsertText)
        let patched = applyEdit source s.Range s.EmptyInsertText
        Assert.True(typechecksCleanly patched, $"Empty-value stubs do not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one implement-missing fix, got %A" other

[<Fact>]
let ``FR0081: a dot-segment prefix is relative-path notation, not a join`` () =
    // Fable's `"./" + path` — Path.Combine cannot spell a `./` prefix
    Assert.Empty(pathsIn "module Test\nlet relative (path: string) = \"./\" + path")

[<Fact>]
let ``FR0081: appending parent segments is not a join either`` () =
    Assert.Empty(pathsIn "module Test\nlet up (prefix: string) = prefix + \"../\"")

[<Fact>]
let ``FR0081: a document pointer joined in a JSON module is not a filesystem path`` () =
    // FSharp.Data's JsonRuntime: `doc.Path() + "/" + name` is a JSON pointer
    Assert.Empty(pathsIn "module JsonRuntime\nlet pointer (jsonPath: string) (name: string) = jsonPath + \"/\" + name")

[<Fact>]
let ``FR0079: the editor fix is the one element itself`` () =
    match singlesIn "module Test\nopen System.Threading.Tasks\nlet run (t: Task<int>) = Task.WhenAll [| t |]" with
    | [ s ] ->
        match s.Fix with
        | Some(_, original, replacement) ->
            Assert.Equal("Task.WhenAll [| t |]", original)
            Assert.Equal("t", replacement)
        | None -> failwith "Expected the unwrap offer"
    | other -> failwithf "Expected one single-awaitable finding, got %A" other

[<Fact>]
let ``FR0089: the editor fix separates the elements with semicolons`` () =
    let _, _, tuples =
        cleanupsIn "module Test\nlet xs = [ 1, 2, 3 ]\nlet ys = [| 1.5, 2.5 |]"

    match tuples with
    | [ a; b ] ->
        let _, _, ra = a.Fix
        let _, _, rb = b.Fix
        Assert.Equal("[ 1; 2; 3 ]", ra)
        Assert.Equal("[| 1.5; 2.5 |]", rb)
    | other -> failwithf "Expected two tuple-in-list findings, got %A" other

// ---- FR0147 QualifiedNames ----

// the tight thresholds, so the shapes stay small; the defaults are 6 and 4
let private qualifiedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    QualifiedNames.find 3 2 tree sourceText checkResults

[<Fact>]
let ``FR0147: a namespace spelled three times becomes an open after the existing opens`` () =
    let source =
        "module Test\nopen System\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.Threading.Tasks", s.Namespace)
        Assert.Equal(3, s.Uses)
        let patched = applyAll source s.Edits

        Assert.Equal(
            "module Test\nopen System\nopen System.Threading.Tasks\nlet a = Task.FromResult 1\nlet b = Task.Delay 10\nlet c (t: Task<int>) = t.Result",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: only the namespace part goes, a type stays qualified by its name`` () =
    let source =
        "module Test\nlet a (p: string) = System.IO.File.Exists p\nlet b (p: string) = System.IO.File.ReadAllText p\nlet c (p: string) = System.IO.Path.GetFileName p"

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        let patched = applyAll source s.Edits
        Assert.Contains("open System.IO\nlet a (p: string) = File.Exists p", patched)
        Assert.Contains("Path.GetFileName p", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: two uses of a shallow namespace are not worth an open`` () =
    Assert.Empty(
        qualifiedIn
            "module Test\nlet a (p: string) = System.IO.File.Exists p\nlet b (p: string) = System.IO.File.ReadAllText p"
    )

[<Fact>]
let ``FR0147: a namespace the file already opens only gets its uses shortened`` () =
    let source =
        "module Test\nopen System.IO\nlet a (p: string) = System.IO.File.Exists p"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits
        Assert.Equal("module Test\nopen System.IO\nlet a (p: string) = File.Exists p", patched)
    | other -> failwithf "Expected one shortening, got %A" other

[<Fact>]
let ``FR0147: a namespace whose open would clash with a name the file defines is noted, not fixed`` () =
    // the file's own `File` is why the author qualified System.IO.File
    let source =
        "module Test\ntype File = { Name: string }\nlet a (p: string) = System.IO.File.Exists p\nlet b (p: string) = System.IO.File.ReadAllText p\nlet c (p: string) = System.IO.Path.GetFileName p"

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        Assert.Empty s.Edits
        Assert.Equal(Some "this file defines 'File' itself", s.Reason)
    | other -> failwithf "Expected one clash note, got %A" other

[<Fact>]
let ``FR0147: a clash note names the clashing identifier and where it comes from`` () =
    // "would clash with a name this file already uses" left the reader to
    // find the name; the note says which and whence
    let fromAnotherOpen =
        "module Test\nopen System.Timers\nlet a (t: System.Threading.Timer) = t.Dispose()\nlet b (t: System.Threading.Timer) = t.Dispose()\nlet c (t: System.Threading.Timer) = t.Dispose()"

    match qualifiedIn fromAnotherOpen with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Equal(Some "'Timer' (open System.Timers) already comes from another open of this file", s.Reason)
    | other -> failwithf "Expected one clash note, got %A" other

    // the compiler's CheckExpressions: `FSComp.SR.x` 384 times, and `SR`
    // already in scope from `Internal.Utilities` — the note names SR and
    // the open that brings it
    let lib =
        "namespace Internal.Utilities\nmodule SR =\n    let a () = 1\nnamespace FSComp\nmodule SR =\n    let b () = 2"

    let user =
        "module Test\nopen Internal.Utilities\nlet x () = FSComp.SR.b () + FSComp.SR.b () + FSComp.SR.b () + SR.a ()"

    let tree, sourceText, checkResults = parseAndCheckSecond lib user

    match QualifiedNames.find 3 2 tree sourceText checkResults with
    | [ s ] ->
        Assert.Equal("FSComp", s.Namespace)
        Assert.Empty s.Edits

        match s.Reason with
        | Some reason ->
            Assert.Contains("'SR'", reason)
            Assert.Contains("Internal.Utilities", reason)
        | None -> failwith "Expected the clash reason"
    | other -> failwithf "Expected one clash note, got %A" other

    // an offered open carries no reason
    match
        qualifiedIn
            "module Test\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.FromResult 2\nlet c = System.Threading.Tasks.Task.FromResult 3"
    with
    | [ s ] ->
        Assert.NotEmpty s.Edits
        Assert.Equal(None, s.Reason)
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``FR0147: the default thresholds are six uses, or four for a deep namespace`` () =
    let tree, sourceText, checkResults =
        parseAndCheck
            "module Test\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.FromResult 2\nlet c = System.Threading.Tasks.Task.FromResult 3\nlet d (p: string) = System.IO.File.Exists p\nlet e (p: string) = System.IO.File.Exists p\nlet f (p: string) = System.IO.File.Exists p\nlet g (p: string) = System.IO.File.Exists p\nlet h (p: string) = System.IO.File.Exists p"

    // three deep uses and five shallow ones: neither reaches the default
    Assert.Empty(QualifiedNames.find 6 4 tree sourceText checkResults)

    let tree2, sourceText2, checkResults2 =
        parseAndCheck
            "module Test\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.FromResult 2\nlet c = System.Threading.Tasks.Task.FromResult 3\nlet d = System.Threading.Tasks.Task.FromResult 4"

    match QualifiedNames.find 6 4 tree2 sourceText2 checkResults2 with
    | [ s ] -> Assert.Equal(4, s.Uses)
    | other -> failwithf "Expected the deep namespace at four uses, got %A" other

[<Fact>]
let ``FR0147: the open lands beside the opens of the same family`` () =
    let source =
        "module Test\nopen System\nopen System.IO\nopen Microsoft.FSharp.Collections\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.StartsWith(
            "module Test\nopen System\nopen System.IO\nopen System.Threading.Tasks\nopen Microsoft.FSharp.Collections\n",
            patched
        )
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: namespaces come deepest first, and their opens end up shallow to deep`` () =
    let source =
        "module Test\nlet a (s: string) = System.String.IsNullOrEmpty s\nlet b (s: string) = System.String.IsNullOrEmpty s\nlet c (s: string) = System.String.IsNullOrEmpty s\nlet d = System.Collections.Generic.List<int>()\nlet e = System.Collections.Generic.Dictionary<int, int>()"

    match qualifiedIn source with
    | [ deep; shallow ] ->
        Assert.Equal("System.Collections.Generic", deep.Namespace)
        Assert.Equal("System", shallow.Namespace)
        // each use belongs to exactly one namespace: no removal overlaps
        let removals = (deep.Edits @ shallow.Edits) |> List.filter (fun (_, _, r) -> r = "")
        Assert.Equal(5, removals.Length)
        // applied deep first (the order emitted), the shallow open lands above
        let patched = applyAll source (deep.Edits @ shallow.Edits)

        Assert.StartsWith(
            "module Test\nopen System\nopen System.Collections.Generic\nlet a (s: string) = String.IsNullOrEmpty s",
            patched
        )

        Assert.Contains("let d = List<int>()", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected the deep namespace first and the shallow one second, got %A" other

[<Fact>]
let ``FR0147: an open the file already has is never inserted again`` () =
    let source =
        "module Test\nopen System.Collections.Generic\nlet d = System.Collections.Generic.List<int>()\nlet e = System.Collections.Generic.Dictionary<int, int>()"

    match qualifiedIn source with
    | [ s ] ->
        Assert.Empty(s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open"))
        let patched = applyAll source s.Edits

        Assert.Equal(
            "module Test\nopen System.Collections.Generic\nlet d = List<int>()\nlet e = Dictionary<int, int>()",
            patched
        )
    | other -> failwithf "Expected one shortening, got %A" other

[<Fact>]
let ``FR0147: an existing open System.Collections gets Generic after it and System before it`` () =
    let source =
        "module Test\nopen System.Collections\nlet a (s: string) = System.String.IsNullOrEmpty s\nlet b (s: string) = System.String.IsNullOrEmpty s\nlet c (s: string) = System.String.IsNullOrEmpty s\nlet d = System.Collections.Generic.List<int>()\nlet e = System.Collections.Generic.Dictionary<int, int>()"

    match qualifiedIn source with
    | [ deep; shallow ] ->
        let deepOpen =
            deep.Edits
            |> List.pick (fun (r, _, t) -> if t.StartsWith "open" then Some r else None)

        let shallowOpen =
            shallow.Edits
            |> List.pick (fun (r, _, t) -> if t.StartsWith "open" then Some r else None)
        // line 2 is `open System.Collections`: Generic goes below it, System above it
        Assert.Equal(3, deepOpen.StartLine)
        Assert.Equal(2, shallowOpen.StartLine)
    | other -> failwithf "Expected the deep and the shallow namespace, got %A" other

// ---- FR0075: a same-file callee is read one hop ----

[<Fact>]
let ``a disposable handed to a same-file function that disposes it is adopted`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private consume (s: Stream) =\n    use s = s\n    s.ReadByte()\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    consume stream"
    )

[<Fact>]
let ``a disposable handed to a same-file function that keeps it names the leak`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet private consume (s: Stream) = s.ReadByte()\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    consume stream"
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.Function("consume", true)), s.Destination)
        Assert.Contains("in this file, which does not dispose it", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``a disposable in a tuple element is followed to the matching parameter`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private consume (name: string, s: Stream) =\n    s.Dispose()\n    name\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    consume (\"x\", stream)"
    )

[<Fact>]
let ``a leak in the entry point says so`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\n[<EntryPoint>]\nlet main (argv: string[]) =\n    let stream = new FileStream(argv.[0], FileMode.Open)\n    printfn \"%d\" (stream.ReadByte())\n    0"
    with
    | [ s ] ->
        Assert.Equal(Some("let", "use"), s.Fix)
        Assert.Equal(Some UseBinding.ScopeContext.EntryPoint, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leaked handle in the entry point is an ordinary leak`` () =
    // the OS reclaims the handle at exit; there is no unflushed work
    match
        useBindingsIn
            "module Test\n[<EntryPoint>]\nlet main (argv: string[]) =\n    let cts = new System.Threading.CancellationTokenSource()\n    printfn \"%b\" cts.IsCancellationRequested\n    0"
    with
    | [ s ] -> Assert.Equal(None, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leak in an action method is a per-request leak`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\ntype HttpGetAttribute() =\n    inherit System.Attribute()\ntype Api() =\n    [<HttpGet>]\n    member _.Get(path: string) =\n        let stream = new FileStream(path, FileMode.Open)\n        stream.ReadByte()"
    with
    | [ s ] -> Assert.Equal(Some UseBinding.ScopeContext.RequestHandler, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leak in a controller member is a per-request leak`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\ntype ControllerBase() =\n    class\n    end\ntype Api() =\n    inherit ControllerBase()\n    member _.Get(path: string) =\n        let stream = new FileStream(path, FileMode.Open)\n        stream.ReadByte()"
    with
    | [ s ] -> Assert.Equal(Some UseBinding.ScopeContext.RequestHandler, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``FR0147: a file without a module line gets the open before its first declaration`` () =
    // the implicit module of a last file or a script has no header line to
    // go under; the "header" range is the first declaration's own line
    let source =
        "let a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            "open System.Threading.Tasks\nlet a = Task.FromResult 1\nlet b = Task.Delay 10\nlet c (t: Task<int>) = t.Result",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: an expression head naming a type from elsewhere is a clash, a module of that name is not`` () =
    // `Queue.Synchronized` is System.Collections.Queue; opening
    // System.Collections.Generic would re-bind `Queue` to the generic one
    let clashing =
        "module Test\nopen System.Collections\nlet q () = Queue.Synchronized(Queue())\nlet a = System.Collections.Generic.List<int>()\nlet b = System.Collections.Generic.List<int>()\nlet c = System.Collections.Generic.List<int>()"

    match qualifiedIn clashing with
    | [ s ] ->
        Assert.Equal("System.Collections.Generic", s.Namespace)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one clash note, got %A" other

    // `List.map` is the F# List module, which coexists with the generic List
    let coexisting =
        "module Test\nlet xs = List.map id [ 1 ]\nlet a = System.Collections.Generic.List<int>()\nlet b = System.Collections.Generic.List<int>()\nlet c = System.Collections.Generic.List<int>()"

    match qualifiedIn coexisting with
    | [ s ] -> Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``a disposable handed to one of two same-named functions is not followed`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nmodule A =\n    let consume (s: Stream) =\n        use s = s\n        s.ReadByte()\nmodule B =\n    let consume (s: Stream) = s.ReadByte()\nopen B\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    consume stream"
    with
    | [ s ] -> Assert.Equal(Some(UseBinding.Destination.Function("consume", false)), s.Destination)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``FR0147: a short name another open already brings is a clash, even for a namespace that is open`` () =
    // System.Timers has a Timer too: the author qualified System.Threading's
    // on purpose (prismatic's FSharp.Data.HttpMethod beside System.Net.Http's)
    let freshOpen =
        "module Test\nopen System.Timers\nlet a (t: System.Threading.Timer) = t.Dispose()\nlet b (t: System.Threading.Timer) = t.Dispose()\nlet c (t: System.Threading.Timer) = t.Dispose()"

    match qualifiedIn freshOpen with
    | [ s ] ->
        Assert.Equal("System.Threading", s.Namespace)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one clash note, got %A" other

    // already open, still qualified: nothing to say at all
    let alreadyOpen =
        "module Test\nopen System.Threading\nopen System.Timers\nlet a (t: System.Threading.Timer) = t.Dispose()\nlet b (t: System.Threading.Timer) = t.Dispose()\nlet c (t: System.Threading.Timer) = t.Dispose()"

    Assert.Empty(qualifiedIn alreadyOpen)

let private qualifiedInSecond (lib: string) (user: string) =
    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    QualifiedNames.find 3 2 tree sourceText checkResults

[<Fact>]
let ``FR0147: a module named like its namespace is not the namespace`` () =
    // toro: `namespace rec Toro` holds a `module Toro`; `Toro.noGrad` names
    // the module, and under `open Toro` a bare `noGrad` reaches nothing
    let lib =
        "namespace Toro\nmodule Toro =\n    let noGrad (f: unit -> 'a) : 'a = f ()"

    let user =
        "module Example\nopen Toro\nlet a = Toro.noGrad (fun () -> 1)\nlet b = Toro.noGrad (fun () -> 2)\nlet c = Toro.noGrad (fun () -> 3)"

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: a same-project module of the introduced name is a clash`` () =
    // FsAutoComplete: Utils.Utils.Expect beside Expecto.Expect — the
    // qualified Expecto.Expect was the author's way of reaching the other
    let lib =
        "namespace Lib\nmodule Expect =\n    let equal (a: int) (b: int) = ()\nnamespace Utils\nmodule Utils =\n    module Expect =\n        let equal (a: int) (b: int) (msg: string) = ()"

    let user =
        "module Tests\nopen Lib\nopen Utils.Utils\nlet a = Expect.equal 1 1 \"m\"\nlet b = Lib.Expect.equal 1 1\nlet c = Lib.Expect.equal 2 2\nlet d = Lib.Expect.equal 3 3"

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: a same-project namespace still gets its open`` () =
    let lib = "namespace Lib.Deep\ntype Thing() =\n    static member Make() = Thing()"

    let user =
        "module Example\nlet a = Lib.Deep.Thing.Make()\nlet b = Lib.Deep.Thing.Make()\nlet c = Lib.Deep.Thing.Make()"

    match qualifiedInSecond lib user with
    | [ s ] ->
        Assert.Equal("Lib.Deep", s.Namespace)
        Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``FR0147: the open goes under the module line, not under the doc comment above it`` () =
    // Logari: a doc comment precedes `module Logari`, and the module's range
    // starts at the comment
    let source =
        "/// Doc line one\n/// Doc line two\nmodule Test\nlet a = System.Threading.Tasks.Task.FromResult 1\nlet b = System.Threading.Tasks.Task.Delay 10\nlet c (t: System.Threading.Tasks.Task<int>) = t.Result"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            "/// Doc line one\n/// Doc line two\nmodule Test\nopen System.Threading.Tasks\nlet a = Task.FromResult 1\nlet b = Task.Delay 10\nlet c (t: Task<int>) = t.Result",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: an open further down the file covers nothing above it`` () =
    // Fuuga's Eval.fs opens System.Text.RegularExpressions at line 1811; the
    // uses above it are not "already open", and the new open cannot land
    // beside that one either
    let source =
        "module Test\nlet a = System.Text.RegularExpressions.Regex(\"x\")\nlet b = System.Text.RegularExpressions.Regex(\"y\")\nlet c = System.Text.RegularExpressions.Regex(\"z\")\nopen System.Text.RegularExpressions\nlet d = Regex(\"w\")"

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            "module Test\nopen System.Text.RegularExpressions\nlet a = Regex(\"x\")\nlet b = Regex(\"y\")\nlet c = Regex(\"z\")\nopen System.Text.RegularExpressions\nlet d = Regex(\"w\")",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: each top-level namespace block gets its own open`` () =
    // an open in `namespace A` covers nothing in the `namespace B` below it
    let block (ns: string) (name: string) =
        $"namespace {ns}\nmodule {name} =\n    let a = System.Threading.Tasks.Task.FromResult 1\n    let b = System.Threading.Tasks.Task.Delay 10\n    let c (t: System.Threading.Tasks.Task<int>) = t.Result"

    let source = block "A" "M" + "\n" + block "B" "N"

    match qualifiedIn source with
    | [ first; second ] ->
        let edits = first.Edits @ second.Edits
        let patched = applyAll source edits

        let shortened (ns: string) (name: string) =
            $"namespace {ns}\nopen System.Threading.Tasks\nmodule {name} =\n    let a = Task.FromResult 1\n    let b = Task.Delay 10\n    let c (t: Task<int>) = t.Result"

        Assert.Equal(shortened "A" "M" + "\n" + shortened "B" "N", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one finding per block, got %A" other

[<Fact>]
let ``FR0147: a namespace shadowed by a module of its name is never opened`` () =
    // Nu: `[<RequireQualifiedAccess>] module OpenGL` in namespace Nu beside
    // `namespace Nu.OpenGL` — `open Nu.OpenGL` resolves to the module and
    // is refused, so the qualified spelling stays
    let lib =
        "namespace Nu\n[<RequireQualifiedAccess>]\nmodule OpenGL =\n    let version = 1\nnamespace Nu.OpenGL\ntype Thing() =\n    static member Make() = Thing()"

    let user =
        "module Example\nlet a = Nu.OpenGL.Thing.Make()\nlet b = Nu.OpenGL.Thing.Make()\nlet c = Nu.OpenGL.Thing.Make()"

    // `open Nu` with `OpenGL.Thing` is fine (the module name still
    // qualifies the access); `open Nu.OpenGL` is what the compiler refuses
    for s in qualifiedInSecond lib user do
        for _, _, text in s.Edits do
            Assert.DoesNotContain("open Nu.OpenGL", text)

[<Fact>]
let ``FR0147: an active pattern another open brings shadows the constructor of that name`` () =
    // FsAutoComplete: `(|Ident|_|)` from an opened module over
    // FSharp.Compiler.Syntax.Ident — the shortened `Ident(...)` applies the
    // pattern ("This value is not a function")
    let lib =
        "namespace Lib.Syntax\ntype Ident(text: string) =\n    member _.Text = text\nnamespace Lib.Helpers\nmodule Patterns =\n    let (|Ident|_|) (s: string) = if s = \"\" then None else Some s"

    let user =
        "module Example\nopen Lib.Syntax\nopen Lib.Helpers.Patterns\nlet a = Lib.Syntax.Ident(\"a\")\nlet b = Lib.Syntax.Ident(\"b\")\nlet c = Lib.Syntax.Ident(\"c\")"

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: an open inside a nested module does not count for the file`` () =
    // Fuuga's ConfigTests: nested test modules with their own opens; a
    // qualified System.IO in a later nested module still needs the open
    let source =
        "module Test\nmodule First =\n    open System.Text\n    let a = StringBuilder()\nmodule Second =\n    let p = System.IO.Path.Combine(\"a\", \"b\")\n    let q = System.IO.File.Exists p\n    let r = System.IO.File.Exists \"c\""

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        let patched = applyAll source s.Edits

        Assert.Equal(
            "module Test\nopen System.IO\nmodule First =\n    open System.Text\n    let a = StringBuilder()\nmodule Second =\n    let p = Path.Combine(\"a\", \"b\")\n    let q = File.Exists p\n    let r = File.Exists \"c\"",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one qualified-names fix, got %A" other

// ---- FR0085: a function spelled like the type keeps the `new` ----

[<Fact>]
let ``FR0085: a same-named function brought by open keeps new`` () =
    // `type Parse` in one module, `let Parse (_: 'a)` in a second, both opened:
    // `new Parse()` builds the class and `Parse()` calls the function. Measured
    // on a running probe - the tag went from "ctor" to "function" - and it
    // compiles either way, so nothing downstream would have caught it
    let clashing =
        "module Test\nmodule A =\n    type Parse(tag: string) =\n        new() = Parse \"ctor\"\n        member _.Tag = tag\nmodule B =\n    let Parse (_: 'a) = A.Parse \"function\"\nmodule C =\n    open A\n    open B\n    let make () = new Parse()"

    let tree, sourceText, checkResults = parseAndCheck clashing
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // the same file without B opened: nothing captures the name, `new` goes
    let clean =
        "module Test\nmodule A =\n    type Parse(tag: string) =\n        new() = Parse \"ctor\"\n        member _.Tag = tag\nmodule C =\n    open A\n    let make () = new Parse()"

    let tree, sourceText, checkResults = parseAndCheck clean
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: a same-named function declared beside the type keeps new`` () =
    // the same-file guard cannot see a function in ANOTHER file. Where its
    // signature disagrees the bare form is a type error and the build check
    // puts it back; where it is GENERIC it typechecks and quietly calls the
    // function instead of the constructor, which nothing downstream catches
    let generic =
        "module Test\ntype Widget(a: int, b: int) =\n    member _.Sum = a + b\nlet Widget (_: 'a) = Widget(0, 0)\nlet make () = new Widget(1, 2)"

    let tree, sourceText, checkResults = parseAndCheck generic
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // no sibling of that name: the `new` still goes
    let plain =
        "module Test\ntype Widget(a: int, b: int) =\n    member _.Sum = a + b\nlet make () = new Widget(1, 2)"

    let tree, sourceText, checkResults = parseAndCheck plain
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: new string keeps its new - the bare name is the conversion function`` () =
    // management-portal's id generator. `string (chars, i, n)` is FSharp.Core's
    // `string` applied to a TUPLE - it yields "(System.Char[], 1, 3)", typechecks
    // as string either way, and every generated id became that literal
    let lowercase =
        "module Test\nlet take (output: char[]) (index: int) = new string (output, index + 1, 12 - index)"

    let tree, sourceText, checkResults = parseAndCheck lowercase
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // the TYPE spelling names no function, so it still drops
    let uppercase =
        "module Test\nlet take (output: char[]) (index: int) = new System.String (output, index + 1, 12 - index)"

    let tree, sourceText, checkResults = parseAndCheck uppercase
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: a function bound with the type's name keeps new`` () =
    // TypeProviders SDK: `let SharedRow(elems) = new SharedRow(elems, hash)`;
    // without `new` the bare name is the function, called with the wrong arguments
    let shadowed =
        "module Test\ntype SharedRow(elems: int[], hash: int) =\n    member _.Hash = hash\nlet SharedRow(elems: int[]) = new SharedRow(elems, elems.Length)\nlet make (xs: int[]) = new SharedRow(xs, 1)"

    let tree, sourceText, checkResults = parseAndCheck shadowed
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    let plain =
        "module Test\ntype SharedRow(elems: int[], hash: int) =\n    member _.Hash = hash\nlet make (xs: int[]) = new SharedRow(xs, 1)"

    let tree, sourceText, checkResults = parseAndCheck plain
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``a disposable handed to a disposable owner's property or Add is adopted`` () =
    // prismatic: HttpRequestMessage disposes its Content, MultipartContent
    // its parts — the most frequent FR0075 notes there were these
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.Net.Http\nlet send (client: HttpClient) (body: string) =\n    use request = new HttpRequestMessage(HttpMethod.Post, \"http://x\")\n    let content = new StringContent(body)\n    request.Content <- content\n    client.Send request"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.Net.Http\nlet build (body: string) =\n    use multipart = new MultipartFormDataContent()\n    let part = new StringContent(body)\n    multipart.Add(part, \"body\")\n    multipart.Headers.ContentLength"
    )

[<Fact>]
let ``FR0147: a union case an F#-compiled assembly's namespace brings is a clash`` () =
    // FsAutoComplete: `type SymbolKind = | Ident | ...` in namespace
    // FsAutoComplete (FsAutoComplete.Core.dll) beside FCS's Ident class —
    // an F# assembly nests its types under namespace entities, which a
    // top-level scan never saw. FSharp.Core is such an assembly: its
    // Microsoft.FSharp.Control brings `Async`
    let lib = "namespace Lib.Ctl\ntype Async(x: int) =\n    member _.X = x"

    let user =
        "module Example\nopen Microsoft.FSharp.Control\nlet a = Lib.Ctl.Async(1).X\nlet b = Lib.Ctl.Async(2).X\nlet c = Lib.Ctl.Async(3).X"

    match qualifiedInSecond lib user with
    | [ s ] -> Assert.Empty s.Edits
    | [] -> ()
    | other -> failwithf "Expected a clash note or silence, got %A" other

// ---- FR0140: a greedy last constructor argument gets its parentheses ----

[<Fact>]
let ``FR0140: a lambda argument is parenthesised before the named properties`` () =
    // TypeProviders SDK: `TypeProviderConfig(fun _ -> false)` — appended
    // properties would land inside the lambda as a tuple
    let source =
        "module Test\ntype Cfg(f: int -> bool) =\n    member val Hosted = false with get, set\n    member val Name = \"\" with get, set\nlet make () =\n    let cfg = Cfg(fun _ -> false)\n    cfg.Hosted <- true\n    cfg.Name <- \"x\"\n    cfg"

    let tree, sourceText, checkResults = parseAndCheck source

    match ObjectInitializer.find tree sourceText checkResults with
    | [ s ] ->
        Assert.Equal("Cfg((fun _ -> false), Hosted = true, Name = \"x\")", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected one construction rewrite, got %A" other

[<Fact>]
let ``FR0147: a shortening that lands on an FSharp.Core name is withheld`` () =
    // the F# compiler's zmap.fs: `Tagged.Map<_, _>.FromList` under an
    // `open Internal.Utilities.Collections.Tagged` — shortened to
    // `Map<_, _>` it reaches FSharp.Core's Map, which has no FromList
    // (`Tagged.Map<_, _>` is an ABBREVIATION of the three-parameter type; a
    // real type of the name would shadow FSharp.Core's and shorten fine)
    let lib =
        "namespace Tagged\ntype Map<'K, 'V, 'Tag> =\n    { Items: ('K * 'V) list }\n    static member FromList(tag: 'Tag, xs: ('K * 'V) list) : Map<'K, 'V, 'Tag> =\n        ignore tag\n        { Items = xs }\ntype Map<'K, 'V> = Map<'K, 'V, int>"

    let user =
        "module Example\nopen Tagged\nlet a = Tagged.Map<int, int>.FromList(0, [ 1, 2 ])\nlet b = Tagged.Map<int, int>.FromList(0, [])\nlet c = Tagged.Map<int, int>.FromList(0, [ 3, 4 ])"

    // the shapes must typecheck, or the rule's error gate would make the
    // assertion vacuous
    let _, _, checkResults = parseAndCheckSecond lib user

    Assert.Empty(
        checkResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
    )

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: a child namespace of an opened namespace is a name in scope`` () =
    // the F# compiler's DiagnosticsLogger.fs: `FSharp.Compiler.Diagnostics.Metrics.Meter`
    // (a module value) shortened to `Metrics.Meter` under `open System.Diagnostics`
    // reached System.Diagnostics.Metrics.Meter, the type
    let lib =
        "namespace Diag.Metrics\ntype Meter(name: string) =\n    member _.Name = name\nnamespace Own\nmodule Metrics =\n    let Meter = \"m\""

    let user =
        "module Example\nopen Own\nopen Diag\nlet a = Own.Metrics.Meter\nlet b = Own.Metrics.Meter + \"x\"\nlet c = Own.Metrics.Meter + \"y\""

    let _, _, checkResults = parseAndCheckSecond lib user

    Assert.Empty(
        checkResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
    )

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0088: a nullary case drops its wildcard altogether, a case with data keeps one`` () =
    // fsharplint's SynMemberKind matches: `Constructor(_)` is accepted for a
    // case that takes no data, `Constructor _` is not
    let _, wilds, _ =
        cleanupsIn
            "type K =\n    | Ctor\n    | Mem of int\nlet f k =\n    match k with\n    | Ctor(_) -> 0\n    | Mem(_) -> 1"

    match wilds |> List.sortBy (fun s -> s.Range.StartLine) with
    | [ ctor; mem ] ->
        Assert.Equal("", ctor.ReplacementText)
        Assert.Equal(" _", mem.ReplacementText)
    | other -> failwithf "Expected two wildcard cleanups, got %A" other

[<Fact>]
let ``FR0147: an open that would capture a bare union-case construction is withheld`` () =
    // fsharplint's TestHintParser: `Byte('x'B)` is its own Constant case
    // until `open System` makes it the System.Byte constructor
    let lib = "namespace Lint\ntype Constant =\n    | Byte of byte\n    | Str of string"

    let user =
        "module Example\nopen Lint\nlet a = Byte(1uy)\nlet x = System.Math.Abs 1\nlet y = System.Math.Max(1, 2)\nlet z = System.Math.Min(1, 2)"

    let _, _, checkResults = parseAndCheckSecond lib user

    Assert.Empty(
        checkResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
    )

    for s in qualifiedInSecond lib user do
        Assert.Empty s.Edits

[<Fact>]
let ``FR0075: a disposable a local function's task uses after the scope is advice, not a use`` () =
    // suave's ConnectionHealthChecker: the CancellationTokenSource lived on
    // in a returned task's loop, and `use` disposed it before the loop ran
    let source =
        "module Test\nopen System.Threading\nopen System.Threading.Tasks\nlet start () =\n    let cts = new CancellationTokenSource()\n    let loop () = task { do! Task.Delay(1, cts.Token) }\n    loop ()"

    match useBindingsIn source with
    | [ s ] -> Assert.Equal(None, s.Fix)
    | other -> failwithf "Expected one advisory finding, got %A" other

[<Fact>]
let ``FR0075: a disposable used only inside its own scope's task still gets use`` () =
    let source =
        "module Test\nopen System.Threading\nopen System.Threading.Tasks\nlet run () =\n    task {\n        let cts = new CancellationTokenSource()\n        do! Task.Delay(1, cts.Token)\n        return 1\n    }"

    match useBindingsIn source with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a stream wrapper over a caller's stream is not the scope's to dispose`` () =
    // the F# compiler's ilnativeres.fs: `use resWriter = new BinaryWriter(resStream)`
    // closed the caller's stream at the end of an append
    Assert.Empty(
        useBindingsIn
            "module Test\nlet append (resStream: System.IO.Stream) (data: byte[]) =\n    let w = new System.IO.BinaryWriter(resStream)\n    w.Write data"
    )

[<Fact>]
let ``FR0075: a reader over a path still gets use`` () =
    match
        useBindingsIn
            "module Test\nlet read (path: string) =\n    let r = new System.IO.StreamReader(path)\n    let s = r.ReadToEnd()\n    s.Length"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other


// ---- FR0080 TabIndentation: block comments and strings (fantomas GettingStarted.fsx) ----

[<Fact>]
let ``FR0080 a tab inside a literate block comment is prose, not indentation`` () =
    // fantomas's docs/docs/end-users/GettingStarted.fsx keeps a tab-indented
    // shell transcript inside `(** ... *)`; the compiler never sees FS1161 there
    let source =
        "(**\n# Getting started\n\tdotnet new tool-manifest\n\tdotnet tool install fantomas\n*)\nlet f x =\n\tx + 1"

    match tabsIn source with
    | [ s ] ->
        match s.Edits with
        | [ (r, _, replacement) ] ->
            Assert.Equal(7, r.StartLine)
            Assert.Equal("    ", replacement)
        | other -> failwithf "Expected the one code line only, got %A" other
    | other -> failwithf "Expected exactly one tab note, got %A" other

[<Fact>]
let ``FR0080 a file whose only tabs sit in a block comment is left alone`` () =
    Assert.Empty(tabsIn "module Test\n(*\n\ttabbed prose\n\t(* nested *)\n\tstill prose\n*)\nlet x = 1")

[<Fact>]
let ``FR0080 a tab inside a plain string spanning lines is content`` () =
    let source = "module Test\nlet s = \"first\n\tsecond\"\nlet f x =\n\tx + 1"

    match tabsIn source with
    | [ s ] ->
        match s.Edits with
        | [ (r, _, _) ] -> Assert.Equal(5, r.StartLine)
        | other -> failwithf "Expected the one code line only, got %A" other
    | other -> failwithf "Expected exactly one tab note, got %A" other

[<Fact>]
let ``FR0080 a quote inside a line comment does not open a string`` () =
    let source = "module Test\n// it's a \"note\nlet f x =\n\tx + 1"

    match tabsIn source with
    | [ s ] -> Assert.Equal(1, s.Edits.Length)
    | other -> failwithf "Expected exactly one tab note, got %A" other

[<Fact>]
let ``FR0080 tabs after the block comment closes are still indentation`` () =
    let source = "(* header *)\nlet f x =\n\tlet y = x + 1\n\ty"

    match tabsIn source with
    | [ s ] -> Assert.Equal(2, s.Edits.Length)
    | other -> failwithf "Expected exactly one tab note, got %A" other


// ---- FR0073 MatchBang: blank lines around the removed let! ----

[<Fact>]
let ``a blank line between the let! and its match goes with the binding`` () =
    // fantomas EndToEndTests: `backgroundTask {` opened with an empty line
    // where the `let!` had been
    assertMatchBang
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        let! x = fetch ()\n\n        match x with\n        | Some v -> return v\n        | None -> return 0\n    }"
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        match! fetch () with\n        | Some v -> return v\n        | None -> return 0\n    }"

[<Fact>]
let ``a let! between two blank lines leaves a single one`` () =
    // fsharplint TestApi.fs: two consecutive blank lines above the match!
    assertMatchBang
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        let y = 1\n\n        let! x = fetch ()\n\n        match x with\n        | Some v -> return v + y\n        | None -> return y\n    }"
        "module Test\nlet fetch () = async { return Some 1 }\nlet run () =\n    async {\n        let y = 1\n\n        match! fetch () with\n        | Some v -> return v + y\n        | None -> return y\n    }"


[<Fact>]
let ``FR0074: a multi-line inner record keeps one field per line`` () =
    // suave's Stream.fs: the flattened fields were joined into one
    // 170-column line; each field that started a line still does, at the
    // outer field's column
    assertFlattened
        "module Test\ntype Inner = { Y: int; Z: int }\ntype Outer = { X: Inner; N: int }\nlet f (r: Outer) (v: int) =\n    { r with\n        X =\n            { r.X with\n                Y = v\n                Z = v + 1 }\n        N = 2 }"
        "X.Y = v\n        X.Z = v + 1"

[<Fact>]
let ``FR0074: fields aligned after the copy source stay aligned`` () =
    assertFlattened
        "module Test\ntype Inner = { Y: int; Z: int }\ntype Outer = { X: Inner; N: int }\nlet f (r: Outer) (v: int) =\n    { r with X = { r.X with Y = v\n                            Z = v + 1 } }"
        "X.Y = v\n             X.Z = v + 1"

[<Fact>]
let ``FR0147: uses under one #if get their open under the same condition`` () =
    // the F# compiler's TypedTreeOps.ExprOps.fs: a namespace needed only
    // under a condition must not become a dependency of every build
    let source =
        "module Test\nopen System\n#if !FOO\nlet a = System.Text.Encoding.UTF8\nlet b = System.Text.Encoding.ASCII\nlet c = System.Text.Encoding.Unicode\n#endif"

    match qualifiedIn source with
    | [ s ] ->
        let opens = s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open")

        match opens with
        | [ (r, _, text) ] ->
            Assert.Equal("open System.Text\n", text)
            Assert.Equal(4, r.StartLine)
        | other -> failwithf "Expected one open inside the #if, got %A" other
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: an open under #if is no anchor for unconditional uses`` () =
    let source =
        "module Test\nopen System\n#if !FOO\nopen System.Collections.Generic\n#endif\nlet a = System.Text.Encoding.UTF8\nlet b = System.Text.Encoding.ASCII\nlet c = System.Text.Encoding.Unicode"

    match qualifiedIn source with
    | [ s ] ->
        match s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open") with
        | [ (r, _, _) ] -> Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected the open right after `open System`, got %A" other
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: an assignment target is a spelling too`` () =
    // fsharp.formatting's `System.Diagnostics.Trace.AutoFlush <- true` kept
    // its prefix while the reads beside it lost theirs
    let source =
        "module Test\nopen System.Diagnostics\nlet f () =\n    System.Diagnostics.Trace.AutoFlush <- true\n    System.Diagnostics.Trace.AutoFlush <- false\n    System.Diagnostics.Trace.Flush()"

    match qualifiedIn source with
    | [ s ] -> Assert.Equal(3, s.Edits |> List.filter (fun (_, _, r) -> r = "") |> List.length)
    | other -> failwithf "Expected one suggestion with three shortenings, got %A" other

[<Fact>]
let ``FR0147: a name an enclosing namespace provides is not introduced`` () =
    // the F# compiler: every file under FSharp.Compiler sees its SR module;
    // `open FSComp` to spell `SR.x` made SR mean two modules
    let lib =
        "namespace Outer\nmodule SR =\n    let x = 1\nnamespace Lib2\nmodule SR =\n    let y = 2"

    let user =
        "namespace Outer.Inner\nmodule M =\n    let a = Lib2.SR.y\n    let b = Lib2.SR.y + 1\n    let c = Lib2.SR.y + 2"

    for s in qualifiedInSecond lib user do
        Assert.Empty s.Edits

// ---- FR0075: ownership transfers through containers, stores, closes and no-op disposables ----

[<Fact>]
let ``FR0075: a disposable returned inside a tuple is the caller's`` () =
    // suave's Proxy.fs test upstream returns `(port, cts)` after a loop
    // closure captured the cts; ilwritepdb returns its MemoryStream in a
    // 5-tuple after handing it to WriteContentTo
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private fill (s: Stream) = s.WriteByte 1uy\nlet make (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    fill stream\n    (stream.Length, stream)"
    )

[<Fact>]
let ``FR0075: a disposable returned through upcasts inside a tuple is the caller's`` () =
    // Mibo's ASet.mapUse: `(node :> IDisposable, node :> aset<'B>)`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System\nopen System.IO\nlet make (path: string) : IDisposable * Stream =\n    let stream = new FileStream(path, FileMode.Open)\n    (stream :> IDisposable, stream :> Stream)"
    )

[<Fact>]
let ``FR0075: a disposable stored into a returned record is the caller's`` () =
    // Mibo's Primitive3D.upload: the VertexBuffer goes into a PrimitiveMesh
    // record whose Dispose disposes it
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Mesh = { Data: FileStream; Count: int }\nlet load (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    stream.ReadByte() |> ignore\n    { Data = stream; Count = 1 }"
    )

[<Fact>]
let ``FR0075: a disposable returned from a computation expression in a tuple is the caller's`` () =
    // the F# compiler's CompilerImports: `return tcGlobals, frameworkTcImports`
    // 140 lines after `new TcImports(...)`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private register (s: Stream) = ()\nlet load (path: string) =\n    async {\n        let stream = new FileStream(path, FileMode.Open)\n        register stream\n        return 1, stream\n    }"
    )

[<Fact>]
let ``FR0075: a disposable rebound under its own name through an upcast and returned is the caller's`` () =
    // ilread.fs: `let ilModuleReader = ilModuleReader :> ILModuleReader`
    // before caching and returning it
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private stash (s: Stream) = ()\nlet load (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let stream = stream :> Stream\n    stash stream\n    stream"
    )

[<Fact>]
let ``FR0075: a disposable handed on and then returned is the caller's`` () =
    // Activity.fs: `ActivitySource.AddActivityListener(l); l` — the return
    // decides the owner whatever else the scope did with the value
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private register (s: Stream) = ()\nlet load (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    register stream\n    stream"
    )

[<Fact>]
let ``FR0075: a disposable returned from a match arm after a copy is the caller's`` () =
    // FsXaml's Utilities: `resStream.CopyTo ms; ms.Position <- 0L; ms`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet load (path: string) =\n    use src = File.OpenRead path\n    match src with\n    | null -> failwith \"missing\"\n    | _ ->\n        let ms = new MemoryStream()\n        src.CopyTo ms\n        ms.Position <- 0L\n        ms"
    )

[<Fact>]
let ``FR0075: a disposable returned inside a union case is the caller's`` () =
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet tryOpen (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    stream.ReadByte() |> ignore\n    Some stream"
    )

[<Fact>]
let ``FR0075: a disposable stored into a field of the enclosing type belongs to the type`` () =
    // Mibo's ForwardPipeline/Renderer2D: `billboardEffect <- ValueSome e`,
    // Runtime.fs: `audioServiceOpt <- ValueSome audio` — FR0032/FR0047 judge
    // the type's Dispose; this scope is not the owner
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Holder() =\n    let mutable effect: FileStream voption = ValueNone\n    member _.Load(path: string) =\n        let e = new FileStream(path, FileMode.Open)\n        effect <- ValueSome e\n    member _.Loaded = effect.IsSome"
    )

[<Fact>]
let ``FR0075: a disposable stored into a property belongs to the holder`` () =
    // Mibo's ShadowPass: `res.Raster <- sr` on a resources object
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Res() =\n    member val Raster: FileStream = null with get, set\nlet ensure (res: Res) (path: string) =\n    if isNull res.Raster then\n        let sr = new FileStream(path, FileMode.Open)\n        res.Raster <- sr"
    )

[<Fact>]
let ``FR0075: a disposable stored into a collection belongs to the collection's holder`` () =
    // suave's Tcp.fs fills a socket array (`listenSockets.[i] <- s`) it stops
    // one by one later; Mibo's RenderTargetPool adds to an `inUse` list
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet openAll (paths: string[]) =\n    let streams = Array.zeroCreate<FileStream> paths.Length\n    for i in 0 .. paths.Length - 1 do\n        let s = new FileStream(paths.[i], FileMode.Open)\n        streams.[i] <- s\n        s.ReadByte() |> ignore\n    streams"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Pool() =\n    let inUse = ResizeArray<FileStream>()\n    member _.Acquire(path: string) =\n        let s = new FileStream(path, FileMode.Open)\n        inUse.Add s\n        s.ReadByte()"
    )

[<Fact>]
let ``FR0075: a disposable stored into a module-level ref cell belongs to the module`` () =
    // suave's RateLimit: `cleanupTimer := Some timer`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private current: FileStream option ref = ref None\nlet start (path: string) =\n    match current.Value with\n    | Some _ -> ()\n    | None ->\n        let s = new FileStream(path, FileMode.Open)\n        current := Some s"
    )

[<Fact>]
let ``FR0075: a part added to a use-bound multipart content is adopted`` () =
    // suave's Bug256 regression test: `formdata.Add(upload, "file", "pix.gif")`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nopen System.Net.Http\nlet post (path: string) =\n    use fs = File.OpenRead path\n    use formdata = new MultipartFormDataContent()\n    let upload = new StreamContent(fs)\n    upload.Headers.ContentType <- Headers.MediaTypeHeaderValue(\"image/gif\")\n    formdata.Add(upload, \"file\", \"pix.gif\")\n    formdata.Headers.ContentLength"
    )

[<Fact>]
let ``FR0075: disposing through an IDisposable upcast is disposal`` () =
    // fantomas's DaemonTests: `(daemon :> IDisposable).Dispose()`
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System\nopen System.IO\nlet run (path: string) =\n    let stream = new FileStream(path, FileMode.Open)\n    let b = stream.ReadByte()\n    (stream :> IDisposable).Dispose()\n    b"
    )

[<Fact>]
let ``FR0075: closing a stream or writer is disposal`` () =
    // ilwrite.fs: `ms.Close()` before `ms.ToArray()`, `stream.Close()` after
    // a closure reopened it
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet copy (src: Stream) =\n    let ms = new MemoryStream()\n    src.CopyTo ms\n    ms.Close()\n    ms.ToArray()"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet write (path: string) =\n    let w = new StreamWriter(path)\n    w.Write \"x\"\n    w.Close()"
    )

[<Fact>]
let ``FR0075: Close on a type where it is not Dispose is no disposal`` () =
    match
        useBindingsIn
            "module Test\ntype Conn() =\n    member _.Close() = ()\n    interface System.IDisposable with\n        member _.Dispose() = ()\nlet run () =\n    let c = new Conn()\n    c.Close()"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a MemoryStream over a caller's buffer, a StringReader or a StringWriter own no resource`` () =
    // suave's Hpack/Huffman codecs, fsharp.formatting's Transformations:
    // Dispose on these is a no-op, there is nothing to leak
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private dec (s: Stream) = s.ReadByte()\nlet decode (buf: byte[]) =\n    let wbuf = new MemoryStream(buf)\n    dec wbuf |> ignore\n    Array.sub buf 0 (int wbuf.Position)"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private enc (s: Stream) = s.WriteByte 1uy\nlet encode (raw: byte[]) =\n    let tmp = Array.zeroCreate<byte> (raw.Length * 4 + 8)\n    let tmpBuf = new MemoryStream(tmp, 0, tmp.Length, true, true)\n    enc tmpBuf\n    tmp"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet private emit (w: TextWriter) = w.Write \"x\"\nlet render () =\n    let sb = System.Text.StringBuilder()\n    let writer = new StringWriter(sb)\n    emit writer\n    let reader = new StringReader(\"\")\n    reader.ReadLine() |> ignore\n    sb.ToString()"
    )

[<Fact>]
let ``FR0075: a MemoryStream over its own buffer still gets use`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet make () =\n    let ms = new MemoryStream(1024)\n    ms.WriteByte 1uy\n    let n = ms.Length\n    n"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a stream wrapper over a member's stream parameter is not the scope's to dispose`` () =
    // ilnativeres.fs: `static member ReadResFile(stream: Stream)` wraps it in
    // a BinaryReader, AppendVersionToResourceStream(resStream, ...) in a
    // BinaryWriter; ilwrite.fs wraps writeBinaryAux's tupled `stream`
    // parameter inside a tuple-bound nested let
    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\ntype Res() =\n    static member Read(stream: Stream) =\n        let reader = new BinaryReader(stream, System.Text.Encoding.Unicode)\n        reader.ReadUInt32()\n    static member Append(resStream: Stream, isDll: bool) =\n        let w = new BinaryWriter(resStream, System.Text.Encoding.Unicode)\n        w.Write isDll"
    )

    Assert.Empty(
        useBindingsIn
            "module Test\nopen System.IO\nlet writeBinaryAux (stream: Stream, options: int) =\n    let a, b =\n        let os = new BinaryWriter(stream, System.Text.Encoding.UTF8)\n        os.Write options\n        1, 2\n    a + b"
    )

[<Fact>]
let ``FR0075: a hash algorithm from its Create factory is locally constructed`` () =
    // the F# compiler's Hashing.fs and suave's WebSocket.sha1: `MD5.Create()`
    // and `SHA1.Create()` never disposed
    match
        useBindingsIn
            "module Test\nopen System.Security.Cryptography\nlet hash (bytes: byte[]) =\n    let sha = SHA1.Create()\n    let h = sha.ComputeHash bytes\n    h"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a construction hidden behind an upcast is still a construction`` () =
    // YaafFSharpScripting: `new StringWriter(sb) :> TextWriter` (a no-op
    // disposable, but the shape hides every construction)
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet read (path: string) =\n    let stream = new FileStream(path, FileMode.Open) :> Stream\n    let b = stream.ReadByte()\n    b"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a plain-valued member call as the scope's result is read before use disposes it`` () =
    // Hashing.fs: `md5.ComputeHash bytes` is the result — a byte[], computed
    // before the scope exits; only a task, sequence or object still tied to
    // the disposable outlives it
    match
        useBindingsIn
            "module Test\nopen System.Security.Cryptography\nlet hash (bytes: byte[]) =\n    let md5 = MD5.Create()\n    md5.ComputeHash bytes"
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

    match
        useBindingsIn
            "module Test\nopen System.Net.Http\nlet fetch (url: string) =\n    let client = new HttpClient()\n    client.GetStringAsync url"
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some UseBinding.Destination.ReadInResult, s.Destination)
        Assert.Contains("the scope's result reads it", UseBinding.describeEscape s)
    | other -> failwithf "Expected one advisory, got %A" other

[<Fact>]
let ``FR0075: a disposable stored into a local mutable is named as such`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet pick (path: string) =\n    let mutable best: FileStream option = None\n    let s = new FileStream(path, FileMode.Open)\n    best <- Some s\n    best.IsSome"
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.StoredLocally "best"), s.Destination)
        Assert.Contains("stored in the local 'best'", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``FR0075: a disposable captured by a closure says so`` () =
    match
        useBindingsIn
            "module Test\nopen System.IO\nlet defer (run: (unit -> int) -> unit) (path: string) =\n    let s = new FileStream(path, FileMode.Open)\n    run (fun () -> s.ReadByte())"
    with
    | [ s ] ->
        Assert.Equal(Some UseBinding.Destination.Captured, s.Destination)
        Assert.Contains("a closure", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory, got %A" other

// ---- FR0150 EscapingUse ----

let private escapingUsesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    UseBinding.findEscapingUse tree sourceText checkResults

[<Fact>]
let ``FR0150: a use captured by a returned task is flagged and moved inside`` () =
    // suave's ConnectionHealthChecker: the token source is disposed when
    // the starter returns, and the loop reads .Token on every interval
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    use cts = new CancellationTokenSource()\n\n    task {\n        do! Task.Delay(1000, cts.Token)\n        return 1\n    }"

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("cts", s.Name)
        Assert.Equal("task", s.Builder)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("    task {\n        use cts = new CancellationTokenSource()\n        do! Task.Delay", patched)
        Assert.DoesNotContain("    use cts = new CancellationTokenSource()\n\n    task", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: the computation reached through a binding is seen too`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    use cts = new CancellationTokenSource()\n\n    let loop =\n        task {\n            do! Task.Delay(1000, cts.Token)\n            return 1\n        }\n\n    loop"

    match escapingUsesIn source with
    | [ s ] -> Assert.Equal("cts", s.Name)
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: a use the computation never reads is fine`` () =
    Assert.Empty(
        escapingUsesIn
            "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    use cts = new CancellationTokenSource()\n    ignore cts\n\n    task {\n        do! Task.Delay 1000\n        return 1\n    }"
    )

[<Fact>]
let ``FR0150: a use consumed inside the scope is fine`` () =
    // nothing escapes: the task is awaited before the scope returns
    Assert.Empty(
        escapingUsesIn
            "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    task {\n        use cts = new CancellationTokenSource()\n        do! Task.Delay(1000, cts.Token)\n        return 1\n    }"
    )

[<Fact>]
let ``FR0150: a statement between the use and the computation that reads it holds the fix back`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    use cts = new CancellationTokenSource()\n    let token = cts.Token\n\n    task {\n        do! Task.Delay(1000, cts.Token)\n        return 1\n    }"

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("cts", s.Name)
        Assert.Empty s.Edits
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: unrelated statements between the use and the computation stay outside it`` () =
    // the binding moves in; the greeting it does not touch stays where it was
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet start (name: string) =\n    use cts = new CancellationTokenSource()\n    let greeting = \"hello \" + name\n    printfn \"%s\" greeting\n\n    task {\n        do! Task.Delay(1000, cts.Token)\n        return greeting.Length\n    }"

    match escapingUsesIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("    let greeting = \"hello \" + name\n    printfn \"%s\" greeting", patched)
        Assert.Contains("    task {\n        use cts = new CancellationTokenSource()\n        do! Task.Delay", patched)
        Assert.DoesNotContain("    use cts = new CancellationTokenSource()\n    let greeting", patched)
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: the fix through a binding keeps the statements before it in place`` () =
    let source =
        "open System.Threading\nopen System.Threading.Tasks\nlet start (n: int) =\n    use cts = new CancellationTokenSource()\n    let doubled = n * 2\n    let label = string doubled\n\n    let loop =\n        task {\n            do! Task.Delay(doubled, cts.Token)\n            return label\n        }\n\n    loop"

    match escapingUsesIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains("    let doubled = n * 2\n    let label = string doubled", patched)

        Assert.Contains(
            "        task {\n            use cts = new CancellationTokenSource()\n            do! Task.Delay",
            patched
        )

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: an async computation is the same shape`` () =
    let source =
        "open System.Threading\nlet start () =\n    use cts = new CancellationTokenSource()\n\n    async {\n        do! Async.Sleep 1000\n        return cts.Token.IsCancellationRequested\n    }"

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("async", s.Builder)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: a computation the scope consumes itself is not escaping`` () =
    // the task is drained before the scope returns: the use is correct
    Assert.Empty(
        escapingUsesIn
            "open System.Threading\nopen System.Threading.Tasks\nlet start () =\n    use cts = new CancellationTokenSource()\n\n    let t =\n        task {\n            do! Task.Delay(1000, cts.Token)\n            return 1\n        }\n\n    t.Result"
    )
