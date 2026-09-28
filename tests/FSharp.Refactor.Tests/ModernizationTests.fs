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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one match! note, got %A" other

[<Fact>]
let ``let!-then-match collapses to match!`` () =
    assertMatchBang
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    let! x = fetch ()
                    match x with
                    | Some v -> return v
                    | None -> return 0
                }
            """)
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    match! fetch () with
                    | Some v -> return v
                    | None -> return 0
                }
            """)

[<Fact>]
let ``a binder used in a clause body must stay`` () =
    Assert.Empty(
        matchBangsIn (
            fsharp
                """
                module Test
                let fetch () = async { return Some 1 }
                let run () =
                    async {
                        let! x = fetch ()
                        match x with
                        | Some _ -> return x
                        | None -> return None
                    }
                """
        )
    )

[<Fact>]
let ``a use! binding manages a resource and stays`` () =
    Assert.Empty(
        matchBangsIn (
            fsharp
                """
                module Test
                open System
                let acquire () = async { return { new IDisposable with member _.Dispose() = () } }
                let run () =
                    async {
                        use! d = acquire ()
                        match d with
                        | _ -> return 1
                    }
                """
        )
    )

// ---- FR0078 WhileBang ----

let private whileBangsIn (source: string) =
    let tree, sourceText = parse source
    MatchBangRule.findWhileBang tree sourceText

[<Fact>]
let ``the three-part mutable-condition loop collapses to while!`` () =
    match
        whileBangsIn (
            fsharp
                """
                module Test
                let check () = async { return false }
                let step () = async { return () }
                let run () =
                    async {
                        let! first = check ()
                        let mutable go = first
                        while go do
                            do! step ()
                            let! next = check ()
                            go <- next
                    }
                """
        )
    with
    | [ s ] ->
        let patched =
            applyAll
                (fsharp
                    """
                    module Test
                    let check () = async { return false }
                    let step () = async { return () }
                    let run () =
                        async {
                            let! first = check ()
                            let mutable go = first
                            while go do
                                do! step ()
                                let! next = check ()
                                go <- next
                        }
                    """)
                s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                let check () = async { return false }
                let step () = async { return () }
                let run () =
                    async {
                        while! check () do
                            do! step ()
                    }
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one while! note, got %A" other

[<Fact>]
let ``a stale-bool while without the rebind is not while!`` () =
    // while! re-evaluates each iteration; this shape does not
    Assert.Empty(
        whileBangsIn (
            fsharp
                """
                module Test
                let check () = async { return false }
                let run () =
                    async {
                        let! first = check ()
                        let mutable go = first
                        while go do
                            printfn "tick"
                    }
                """
        )
    )

[<Fact>]
let ``different condition computations stay apart`` () =
    Assert.Empty(
        whileBangsIn (
            fsharp
                """
                module Test
                let check () = async { return false }
                let other () = async { return false }
                let run () =
                    async {
                        let! first = check ()
                        let mutable go = first
                        while go do
                            printfn "tick"
                            let! next = other ()
                            go <- next
                    }
                """
        )
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one flatten note, got %A" other

[<Fact>]
let ``a nested copy-and-update flattens to a path`` () =
    assertFlattened
        (fsharp
            """
            module Test
            type Inner = { Y: int; Z: int }
            type Outer = { X: Inner; N: int }
            let f (r: Outer) (v: int) = { r with X = { r.X with Y = v } }
            """)
        "X.Y = v"

[<Fact>]
let ``multiple inner fields flatten side by side`` () =
    assertFlattened
        (fsharp
            """
            module Test
            type Inner = { Y: int; Z: int }
            type Outer = { X: Inner; N: int }
            let f (r: Outer) (v: int) = { r with X = { r.X with Y = v; Z = v + 1 } }
            """)
        "X.Y = v; X.Z = v + 1"

[<Fact>]
let ``two levels flatten to a deep path`` () =
    assertFlattened
        (fsharp
            """
            module Test
            type L3 = { V: int }
            type L2 = { Inner: L3 }
            type L1 = { Mid: L2 }
            let f (r: L1) (v: int) = { r with Mid = { r.Mid with Inner = { r.Mid.Inner with V = v } } }
            """)
        "Mid.Inner.V = v"

[<Fact>]
let ``a field named after a type keeps the nested form`` () =
    // `{ r with B.A.V = v }` would resolve B as the TYPE and fail to
    // compile — the field-named-after-its-type pattern stays nested
    Assert.Empty(
        nestedIn (
            fsharp
                """
                module Test
                type A = { V: int }
                type B = { A: A }
                type C = { B: B }
                let f (r: C) (v: int) = { r with B = { r.B with A = { r.B.A with V = v } } }
                """
        )
    )

[<Fact>]
let ``a cross-record inner copy stays`` () =
    // the inner source is a DIFFERENT record, not r.X — nothing to flatten
    Assert.Empty(
        nestedIn (
            fsharp
                """
                module Test
                type Inner = { Y: int; Z: int }
                type Outer = { X: Inner; N: int }
                let f (r: Outer) (q: Inner) (v: int) = { r with X = { q with Y = v } }
                """
        )
    )

[<Fact>]
let ``a field named after the module holding its type keeps the nested form`` () =
    // `Settings: Settings.GameSettings` — the field shares its name with
    // the MODULE its type lives in. `{ menu with Settings.X = v }`
    // resolves Settings as the module and the record as GameSettings: "This
    // expression was expected to have type 'Menu' but here has type
    // 'Settings.GameSettings'"
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
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    let b = stream.ReadByte()
                    b + 1
                """
        )
    with
    | [ s ] ->
        Assert.Equal(Some("let", "use"), s.Fix)

        let patched =
            applyEdit
                (fsharp
                    """
                    module Test
                    open System.IO
                    let read (path: string) =
                        let stream = new FileStream(path, FileMode.Open)
                        let b = stream.ReadByte()
                        b + 1
                    """)
                s.Range
                "use"

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a disposable passed on bare gets advice only`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let handOff (sink: FileStream -> unit) (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    sink stream
                """
        )
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.Function("sink", false)), s.Destination)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``a disposable piped to a function names the function`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let handOff (sink: FileStream -> unit) (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    stream |> sink
                """
        )
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
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let openStream (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    stream
                """
        )
    )

[<Fact>]
let ``a disposable handed to a returned wrapper is adopted`` () =
    // StreamReader takes ownership and outlives this scope
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let openReader (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    new StreamReader(stream)
                """
        )
    )

[<Fact>]
let ``a handler chained into an HttpClient is adopted, named arguments and all`` () =
    // HttpClient disposes its handler: the chain is one owner, not two
    // notes per client
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                let make (url: string) =
                    let handler = new HttpClientHandler(UseCookies = false)
                    new HttpClient(handler, true, BaseAddress = System.Uri url)
                """
        )
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
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    let b = stream.ReadByte()
                    stream.Dispose()
                    b
                """
        )
    )

[<Fact>]
let ``a non-disposable local is fine`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                let f () =
                    let sb = new System.Text.StringBuilder()
                    sb.Append('x') |> ignore
                    sb.Length
                """
        )
    )

// ---- FR0076 MapIgnore ----

let private mapIgnoresIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    MapIgnore.find tree sourceText checkResults

[<Fact>]
let ``List map piped to ignore becomes iter`` () =
    match
        mapIgnoresIn (
            fsharp
                """
                module Test
                let f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore
                """
        )
    with
    | [ s ] ->
        Assert.Equal(Some "xs |> List.iter (g >> ignore)", s.ReplacementText)

        let patched =
            applyEdit
                (fsharp
                    """
                    module Test
                    let f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore
                    """)
                s.Range
                s.ReplacementText.Value

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one map-ignore fix, got %A" other

[<Fact>]
let ``Seq map piped to ignore is the lazy bug and gets advice`` () =
    match
        mapIgnoresIn (
            fsharp
                """
                module Test
                let f (g: int -> int) (xs: seq<int>) = xs |> Seq.map g |> ignore
                """
        )
    with
    | [ s ] ->
        Assert.Equal("Seq", s.ModuleName)
        Assert.Equal(None, s.ReplacementText)
    | other -> failwithf "Expected exactly one lazy advisory, got %A" other

[<Fact>]
let ``a used map result is fine`` () =
    Assert.Empty(
        mapIgnoresIn (
            fsharp
                """
                module Test
                let f (g: int -> int) (xs: int list) = xs |> List.map g |> List.sum
                """
        )
    )

[<Fact>]
let ``a shadowed map is left alone`` () =
    Assert.Empty(
        mapIgnoresIn (
            fsharp
                """
                module Test
                module List =
                    let map (f: int -> int) (xs: int list) = xs
                let f (g: int -> int) (xs: int list) = xs |> List.map g |> ignore
                """
        )
    )

[<Fact>]
let ``a condition computation reading the mutable binder stays`` () =
    // `let! next = step go` — deleting `go` would strand the computation
    Assert.Empty(
        whileBangsIn (
            fsharp
                """
                module Test
                let step (b: bool) = async { return not b }
                let run () =
                    async {
                        let! first = step true
                        let mutable go = first
                        while go do
                            printfn "tick"
                            let! next = step go
                            go <- next
                    }
                """
        )
    )

// ---- FR0079 SingleAwaitable ----

let private singlesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SingleAwaitable.find tree sourceText checkResults

[<Fact>]
let ``WhenAll over a single-task literal is noted`` () =
    match
        singlesIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (t: Task<int>) = Task.WhenAll [| t |]
                """
        )
    with
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
        singlesIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let f (a: Task<int>) (b: Task<int>) = Task.WhenAll [| a; b |]
                """
        )
    )

[<Fact>]
let ``a comprehension may yield any number`` () =
    Assert.Empty(
        singlesIn (
            fsharp
                """
                module Test
                let f (cs: Async<int> list) = Async.Parallel [ for c in cs -> c ]
                """
        )
    )

// ---- FR0077 ImplementMissing ----

// FR0077 fixes FS0366 itself, so its inputs carry that error on purpose
let private missingIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheckAllowingErrors source
    ImplementMissing.find tree sourceText checkResults

[<Fact>]
let ``missing interface members get NotImplementedException stubs`` () =
    let source =
        fsharp
            """
            module Test
            type IThing =
                abstract member Go: unit -> int
                abstract member Stop: string -> unit
                abstract member Name: string

            let t =
                { new IThing with
                    member _.Go() = 1 }
            """

    match missingIn source with
    | [ s ] ->
        Assert.Equal<string list>([ "Stop"; "Name" ] |> List.sort, s.MissingNames |> List.sort)
        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one implement-missing fix, got %A" other

[<Fact>]
let ``an inherited interface stubs in its own section`` () =
    let source =
        fsharp
            """
            module Test
            open System
            type IRes =
                inherit IDisposable
                abstract member Load: unit -> int

            let r =
                { new IRes with
                    member _.Load() = 1 }
            """

    match missingIn source with
    | [ s ] ->
        Assert.Contains("Dispose", s.MissingNames)
        Assert.Contains("interface IDisposable with", s.InsertText)
        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one inherited-stub fix, got %A" other

[<Fact>]
let ``members implemented in the main block satisfy inherited interfaces`` () =
    // an IDbConnection stub implementing Dispose in the main block
    // satisfies IDisposable — an extra `interface IDisposable with` stub would double-implement it (FS0767).
    // The unrelated error keeps the file in FR0077's runs-on-broken-code path.
    Assert.Empty(
        missingIn (
            fsharp
                """
                module Test
                open System
                type IRes2 =
                    inherit IDisposable
                    abstract member Load: unit -> int

                let broken: int = "s"

                let r =
                    { new IRes2 with
                        member _.Load() = 1
                        member _.Dispose() = () }
                """
        )
    )

[<Fact>]
let ``a file that already type-checks is left alone`` () =
    // a clean file has nothing missing, whatever the name-matching
    // heuristics conclude — FR0077 exists to fix FS0366, not working code
    Assert.Empty(
        missingIn (
            fsharp
                """
                module Test
                open System
                type IRes3 =
                    inherit IDisposable
                    abstract member Load: unit -> int

                let r =
                    { new IRes3 with
                        member _.Load() = 1
                        member _.Dispose() = () }
                """
        )
    )

[<Fact>]
let ``a complete object expression is quiet`` () =
    Assert.Empty(
        missingIn (
            fsharp
                """
                module Test
                type IThing2 =
                    abstract member Go: unit -> int

                let t =
                    { new IThing2 with
                        member _.Go() = 1 }
                """
        )
    )

[<Fact>]
let ``a property with getter and setter stubs both`` () =
    let source =
        fsharp
            """
            module Test
            type IHolder =
                abstract member Value: int with get, set
                abstract member Touch: unit -> unit

            let h =
                { new IHolder with
                    member _.Touch() = () }
            """

    match missingIn source with
    | [ s ] ->
        Assert.Contains("with get () =", s.InsertText)
        Assert.Contains("and set _v =", s.InsertText)
        let patched = applyEdit source s.Range s.InsertText
        assertTypechecks "Patched source" patched
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

        Assert.Equal(
            fsharp
                """
                module Test
                let f x =
                    let y = x + 1
                    y + 1
                """,
            patched
        )

        assertParses "Patched source" patched
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
    match
        pathsIn (
            fsharp
                """
                module Test
                let f (dir: string) (file: string) = dir + "\\" + file
                """
        )
    with
    | [ s ] -> Assert.Equal("\\", s.Separator)
    | other -> failwithf "Expected exactly one path note, got %A" other

[<Fact>]
let ``a slash-joined path is noted`` () =
    match
        pathsIn (
            fsharp
                """
                module Test
                let f (root: string) (name: string) = root + "/" + name + ".txt"
                """
        )
    with
    | [ s ] -> Assert.Equal("/", s.Separator)
    | other -> failwithf "Expected exactly one slash note, got %A" other

[<Fact>]
let ``a url join is not a file path`` () =
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let f (baseUrl: string) (route: string) = baseUrl + "/" + route
                """
        )
    )

[<Fact>]
let ``a scheme literal is not a file path`` () =
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let f (host: string) = "https://" + host + "/api"
                """
        )
    )

[<Fact>]
let ``plain text concatenation is not a path`` () =
    Assert.Empty(pathsIn "module Test\nlet f (a: string) (b: string) = a + \", \" + b")

[<Fact>]
let ``a name bound one hop away to a url makes the join a url`` () =
    // the classic FAKE build script shape: `gitHome + "/" + gitName +
    // ".git"` with `gitHome = "https://github.com/" + gitOwner` further up
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let gitOwner = "fsprojects"
                let gitHome = "https://github.com/" + gitOwner
                let gitName = "FsXaml"
                let clone () = gitHome + "/" + gitName + ".git"
                """
        )
    )

    // a local binding is read the same way
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let clone (owner: string) (name: string) =
                    let home = "https://github.com/" + owner
                    home + "/" + name + ".git"
                """
        )
    )

    // ... and a directory bound one hop away still joins a path
    match
        pathsIn (
            fsharp
                """
                module Test
                let root = "C:\\builds"
                let f (name: string) = root + "/" + name + ".txt"
                """
        )
    with
    | [ _ ] -> ()
    | other -> failwithf "Expected one path note, got %A" other

[<Fact>]
let ``a join compared or searched for is a key, not a path to build`` () =
    // `"content/" + n.file = page`
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let f (file: string) (page: string) = "content/" + file = page
                """
        )
    )

    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let f (dir: string) (file: string) (page: string) = page <> dir + "/" + file
                """
        )
    )

    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let f (keys: System.Collections.Generic.HashSet<string>) (dir: string) (file: string) = keys.Contains(dir + "/" + file)
                """
        )
    )

[<Fact>]
let ``a call operand is path evidence only through the file system API it invokes`` () =
    // `getNameOfScopeRef scoref + "/" +
    // textOfPath (List.map fst path)` builds a mangled compilation path;
    // "path" in a function's name is not a directory
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                let textOfPath (xs: string list) = String.concat "." xs
                let nameOf (x: int) = string x
                let mangled (x: int) (path: (string * int) list) = nameOf x + "/" + textOfPath (List.map fst path)
                """
        )
    )

    // a call INTO the file system is evidence
    match
        pathsIn (
            fsharp
                """
                module Test
                let f (name: string) = System.IO.Path.GetTempPath() + "/" + name
                """
        )
    with
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
        assertParses "Patched source" patched
    | other -> failwithf "Expected exactly one %A fix, got %A" kind other

[<Fact>]
let ``the Attribute suffix is trimmed`` () =
    assertSyntaxFix
        RedundantSyntax.Kind.AttributeSuffix
        (fsharp
            """
            module Test
            [<System.SerializableAttribute>]
            type T = { X: int }
            """)
        (fsharp
            """
            module Test
            [<System.Serializable>]
            type T = { X: int }
            """)

[<Fact>]
let ``an attribute named exactly Attribute keeps its name`` () =
    Assert.Empty(
        syntaxIn (
            fsharp
                """
                module Test
                [<System.Serializable>]
                type T = { X: int }
                """
        )
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.AttributeSuffix)
    )

[<Fact>]
let ``empty attribute parens go away`` () =
    assertSyntaxFix
        RedundantSyntax.Kind.AttributeParens
        (fsharp
            """
            module Test
            [<System.Serializable()>]
            type T = { X: int }
            """)
        (fsharp
            """
            module Test
            [<System.Serializable>]
            type T = { X: int }
            """)

[<Fact>]
let ``an attribute with real arguments or none written keeps its spelling`` () =
    // the parser hands a bare [<Serializable>] a unit argument too, spanning
    // the name: only a written "()" is empty parens, and an argument the
    // attribute needs is never touched
    Assert.Empty(
        syntaxIn (
            fsharp
                """
                module Test
                [<System.Serializable; System.Obsolete("use V2")>]
                type T = { X: int }
                [<System.Obsolete("use V3", false)>]
                let f () = 1
                """
        )
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.AttributeParens)
    )

[<Fact>]
let ``redundant backticks strip at use and binder sites`` () =
    match
        syntaxIn (
            fsharp
                """
                module Test
                let ``plain`` = 1
                let f () = ``plain`` + 1
                """
        )
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    with
    | [ _; _ ] -> ()
    | other -> failwithf "Expected two backtick fixes, got %A" other

[<Fact>]
let ``necessary backticks stay`` () =
    Assert.Empty(
        syntaxIn (
            fsharp
                """
                module Test
                let ``two words`` = 1
                let ``type`` = 2
                let f () = ``two words`` + ``type``
                """
        )
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

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one redundant-new fix, got %A" other

[<Fact>]
let ``new on a disposable stays`` () =
    Assert.Empty(
        newsIn (
            fsharp
                """
                module Test
                open System.IO
                let f (p: string) =
                    use s = new FileStream(p, FileMode.Open)
                    s.ReadByte()
                """
        )
    )

// ---- FR0087-FR0089 PatternCleanups ----

let private cleanupsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    PatternCleanups.find tree sourceText checkResults

[<Fact>]
let ``cons of empty is a one-element list pattern`` () =
    let conses, _, _ =
        cleanupsIn (
            fsharp
                """
                module Test
                let f (xs: int list) =
                    match xs with
                    | x :: [] -> x
                    | _ -> 0
                """
        )

    match conses with
    | [ s ] -> Assert.Equal("[ x ]", s.ReplacementText)
    | other -> failwithf "Expected exactly one cons fix, got %A" other

[<Fact>]
let ``a cons pattern laid out over several lines keeps its layout`` () =
    // wrapping `{ Id = id` in "[ " would shift it right of the `Name` line
    // aligned under it: the one-line rewrite is not a layout-safe edit
    let source =
        fsharp
            """
            module Test
            type Row = { Id: int; Name: string }
            let only (rows: Row list) =
                match rows with
                | { Id = id
                    Name = name } :: [] -> Some(id, name)
                | _ -> None
            """

    assertTypechecks "Test input" source
    let conses, _, _ = cleanupsIn source
    Assert.Empty conses

[<Fact>]
let ``all-wildcard case fields collapse`` () =
    let _, wilds, _ =
        cleanupsIn (
            fsharp
                """
                module Test
                type T =
                    | Pair of int * int
                    | One
                let f (t: T) =
                    match t with
                    | Pair(_, _) -> 1
                    | One -> 0
                """
        )

    match wilds with
    | [ s ] ->
        Assert.Equal("Pair", s.CaseName)
        Assert.Equal(" _", s.ReplacementText)
    | other -> failwithf "Expected exactly one wild-fields fix, got %A" other

[<Fact>]
let ``a partially bound case keeps its fields`` () =
    let _, wilds, _ =
        cleanupsIn (
            fsharp
                """
                module Test
                type T =
                    | Pair of int * int
                    | One
                let f (t: T) =
                    match t with
                    | Pair(a, _) -> a
                    | One -> 0
                """
        )

    Assert.Empty wilds

[<Fact>]
let ``a tuple filling an unannotated list literal is noted`` () =
    let _, _, tuples = cleanupsIn "module Test\nlet xs = [ 1, 2 ]"

    match tuples with
    | [ s ] -> Assert.Equal(2, s.Elements)
    | other -> failwithf "Expected exactly one tuple-in-list note, got %A" other

[<Fact>]
let ``FR0089: an annotation spelling the tuple out says the tuple is meant`` () =
    // `let expectedInitial: Map<int, int> = Map.ofList [ 2, 25 ]` and
    // plain `(int * int) list` annotations — the slot asks for tuples
    let _, _, byBinding = cleanupsIn "module Test\nlet xs: (int * int) list = [ 1, 2 ]"
    let _, _, byExpr = cleanupsIn "module Test\nlet xs = ([ 1, 2 ] : (int * int) list)"
    Assert.Empty byBinding
    Assert.Empty byExpr

[<Fact>]
let ``FR0089: a one-entry map is the tuple list Map.ofList asks for`` () =
    // `Map.ofList [ k, v ]`, `[ 1, 1 ] |> Map.ofSeq`, `dict [ 1, 1 ]`,
    // `Assert.Equal<Map<int, int>>(Map.ofList [ 0, 0 ], m)`
    let _, _, tuples =
        cleanupsIn (
            fsharp
                """
                module Test
                let a = Map.ofList [ 3, 6 ]
                let b = [ 1, 1 ] |> Map.ofSeq
                let c = dict [ 1, 1 ]
                let d = Map.ofList [ 0, Map.ofList [ 1, 3 ] ]
                let chunksOf (ranges: (int * int) list) = ranges.Length
                let e = chunksOf [ 0, 2 ]
                let f (k: int) (pairs: (int * int) list) = k + pairs.Length
                let g = f 1 [ 2, 3 ]
                let h = [ 4, 5 ] |> f 1
                """
        )

    Assert.Empty tuples

[<Fact>]
let ``FR0089: a tupled method argument asks its own parameter`` () =
    let _, _, tuples =
        cleanupsIn (
            fsharp
                """
                module Test
                type T =
                    static member Take(n: int, pairs: (int * int) list) = n + pairs.Length
                    static member Loose(n: int, xs: 'a list) = n + xs.Length
                let a = T.Take(1, [ 2, 3 ])
                let b = T.Loose(1, [ 2, 3 ])
                """
        )

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
    match
        pathsIn (
            fsharp
                """
                module Test
                let data = __SOURCE_DIRECTORY__ + "/data" + "/set.json"
                """
        )
    with
    | [ s ] -> Assert.Equal("/", s.Separator)
    | other -> failwithf "Expected exactly one source-dir note, got %A" other

[<Fact>]
let ``a Literal binding cannot call Path Combine`` () =
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                [<Literal>]
                let DataDir = __SOURCE_DIRECTORY__ + "/data" + "/set.json"
                """
        )
    )

[<Fact>]
let ``an attribute argument cannot call Path Combine`` () =
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module Test
                open System
                [<Obsolete(__SOURCE_DIRECTORY__ + "/moved" + "/here.fs")>]
                let f () = 1
                """
        )
    )

[<Fact>]
let ``an expression tuple list is deliberate`` () =
    let _, _, tuples =
        cleanupsIn (
            fsharp
                """
                module Test
                let edits (r: int) (t: string) = [ r, t, "code" ]
                """
        )

    Assert.Empty tuples

// ---- regressions ----

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
        syntaxIn (
            fsharp
                """
                module Test
                let ``_`` = 1
                let f () = ``_`` + 1
                """
        )
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.Backticks)
    )

[<Fact>]
let ``a same-file type under the short name blocks the suffix trim`` () =
    // [<My>] would resolve to type My, not MyAttribute
    Assert.Empty(
        syntaxIn (
            fsharp
                """
                module Test
                type My() = class end
                type MyAttribute() =
                    inherit System.Attribute()

                [<MyAttribute>]
                let f () = 1
                """
        )
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.AttributeSuffix)
    )

[<Fact>]
let ``spaced names and backticks inside strings are untouched`` () =
    // detection is AST-ident-based: string CONTENT is invisible, and a
    // multi-word name is not a plain identifier
    Assert.Empty(
        syntaxIn (
            fsharp
                """
                module Test
                let ``yes fsharp supports long variables like this`` = " `` "
                """
        )
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one failwith-context hint, got %A" other

[<Fact>]
let ``static failwith message gains the enclosing arguments`` () =
    assertFailwithContext
        (fsharp
            """
            module Test
            let mymethod (x: int) =
                failwith "Error"
            """)
        (fsharp
            """
            module Test
            let mymethod (x: int) =
                failwith $"Error, calling mymethod with x: {x}"
            """)

[<Fact>]
let ``every parameter is reported in order`` () =
    assertFailwithContext
        (fsharp
            """
            module Test
            let locate (name: string) (index: int) =
                failwith "Not found"
            """)
        (fsharp
            """
            module Test
            let locate (name: string) (index: int) =
                failwith $"Not found, calling locate with name: {name}, index: {index}"
            """)

[<Fact>]
let ``the innermost enclosing function wins`` () =
    assertFailwithContext
        (fsharp
            """
            module Test
            let outer (a: int) =
                let inner (b: int) =
                    failwith "Bad"
                inner a
            """)
        (fsharp
            """
            module Test
            let outer (a: int) =
                let inner (b: int) =
                    failwith $"Bad, calling inner with b: {b}"
                inner a
            """)

[<Fact>]
let ``an already interpolated message is left to its author`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod x =
                    failwith $"Error {x}"
                """
        )
    )

[<Fact>]
let ``a message already naming a parameter is left alone`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod (count: int) =
                    failwith "count must be positive"
                """
        )
    )

[<Fact>]
let ``a parameterless function has nothing to report`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod () =
                    failwith "Error"
                """
        )
    )

[<Fact>]
let ``a top-level failwith outside any function is left alone`` () =
    Assert.Empty(failwithContextIn "module Test\nlet value: int = failwith \"Error\"")

[<Fact>]
let ``braces would need escaping so the message is left alone`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod (x: int) =
                    failwith "Bad {shape}"
                """
        )
    )

[<Fact>]
let ``a percent sign would change meaning when interpolated`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod (x: int) =
                    failwith "Over 100% used"
                """
        )
    )

[<Fact>]
let ``a shadowed failwith is not ours to rewrite`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let failwith (s: string) = ()
                let mymethod (x: int) =
                    failwith "Error"
                """
        )
    )

[<Fact>]
let ``wildcard parameters carry nothing to report`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let mymethod _ =
                    failwith "Error"
                """
        )
    )

[<Fact>]
let ``a parameter whose type prints nothing useful is not quoted`` () =
    // a byte array prints "System.Byte[]", a generic 'a whatever it is
    // bound to, a stream its type name: with no parameter worth quoting
    // there is no note
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decode (bytes: byte[]) =
                    failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decode x =
                    failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decode (s: System.IO.Stream) (f: int -> int) =
                    failwith "Error"
                """
        )
    )

    // ... and a mixed list quotes only the printing ones
    assertFailwithContext
        (fsharp
            """
            module Test
            let decode (bytes: byte[]) (offset: int) =
                failwith "Error"
            """)
        (fsharp
            """
            module Test
            let decode (bytes: byte[]) (offset: int) =
                failwith $"Error, calling decode with offset: {offset}"
            """)

[<Fact>]
let ``a fieldless union, an enum, an option and a small record print usefully`` () =
    assertFailwithContext
        (fsharp
            """
            module Test
            type Mode =
                | Fast
                | Slow
            type Point = { X: int; Y: int }
            let run (mode: Mode) (at: Point option) =
                failwith "Error"
            """)
        (fsharp
            """
            module Test
            type Mode =
                | Fast
                | Slow
            type Point = { X: int; Y: int }
            let run (mode: Mode) (at: Point option) =
                failwith $"Error, calling run with mode: {mode}, at: {at}"
            """)

    // a union WITH fields prints its payload's type names
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                type Shape =
                    | Circle of System.IO.Stream
                    | Square of byte[]
                let run (shape: Shape) =
                    failwith "Error"
                """
        )
    )

[<Fact>]
let ``an invariant message explains itself without arguments`` () =
    // "unreachable - linear let", "varargs NYI", "not possible", "invalid
    // case.": the branch was never meant to run, and no argument says why
    // it did
    for message in
        [
            "unreachable - linear let"
            "varargs NYI"
            "not possible"
            "impossible"
            "invalid case."
            "Suave.Web.split: invalid case"
            "not implemented"
            "internal error; should not have successfully decrypted data"
            "invalid state"
        ] do
        Assert.Empty(failwithContextIn $"module Test\nlet run (n: int) =\n    failwith \"{message}\"")

[<Fact>]
let ``a message that is the function's own name is fslex's fallthrough`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let rule (n: int) =
                    failwith "rule"
                """
        )
    )

[<Fact>]
let ``secrets in scope are not for the log`` () =
    // a parser throwing on freshly decrypted session data: interpolating
    // the blob would log it. The function, a parameter, or an enclosing
    // module or type can carry the smell
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decryptSession (blob: string) =
                    failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let parse (token: string) =
                    failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let parse (apiKey: string) =
                    failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                namespace Test
                module Authentication =
                    let parseData (blob: string) =
                        failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                type CredentialStore() =
                    member _.Parse(blob: string) =
                        let inner (line: string) = failwith "Error"
                        inner blob
                """
        )
    )

    // an author and a tokenizer are not secrets
    assertFailwithContext
        (fsharp
            """
            namespace Test
            module Tokenizer =
                let author (name: string) =
                    failwith "Error"
            """)
        (fsharp
            """
            namespace Test
            module Tokenizer =
                let author (name: string) =
                    failwith $"Error, calling author with name: {name}"
            """)

[<Fact>]
let ``a test file's failwith is an assertion the runner already describes`` () =
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                namespace Xunit
                type FactAttribute() =
                    inherit System.Attribute()

                namespace Test
                open Xunit
                module Tests =
                    let expectOk (name: string) =
                        failwith "HSTS missing"
                    [<Fact>]
                    let ``a test`` () = expectOk "x"
                """
        )
    )

[<Fact>]
let ``a message thrown twice is not a message read back`` () =
    // `failwith "Index overrun."` twice in one function: two throws
    // sharing a text are not one reading the other, both get the note
    let twoThrows =
        failwithContextIn (
            fsharp
                """
                module Test
                let entry (idx: int) =
                    if idx <= 0 then failwith "Index overrun."
                    elif idx < 10 then idx
                    else failwith "Index overrun."
                """
        )

    Assert.Equal(2, twoThrows.Length)

    // ... while the same text spelled anywhere ELSE is somebody reading it
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let expected = "Index overrun."
                let entry (idx: int) =
                    if idx <= 0 then failwith "Index overrun."
                    else idx
                """
        )
    )

[<Fact>]
let ``a parameter is mentioned as a word, not as letters`` () =
    // `x` is not mentioned by "no text property", nor `ty` by "open
    // generic type"
    assertFailwithContext
        (fsharp
            """
            module Test
            let read (x: string) =
                failwith "no text property"
            """)
        (fsharp
            """
            module Test
            let read (x: string) =
                failwith $"no text property, calling read with x: {x}"
            """)

[<Fact>]
let ``a tuple parameter is left out, the named ones stay`` () =
    // `writeResource name (conn: Connection, _)`: the tuple carries no
    // name to quote, and does not disqualify the whole function
    assertFailwithContext
        (fsharp
            """
            module Test
            let write (name: string) (conn: int, _) =
                failwith "error"
            """)
        (fsharp
            """
            module Test
            let write (name: string) (conn: int, _) =
                failwith $"error, calling write with name: {name}"
            """)

[<Fact>]
let ``a function's wildcard arm is named so its argument can be quoted`` () =
    // `toOpcode = function ... | _ -> failwith "Invalid opcode."`:
    // the one argument has no name, so the arm that throws gets one
    let source =
        fsharp
            """
            module Test
            type Opcode =
                | Text
                | Binary
            let toOpcode = function
                | 0uy -> Text
                | 1uy -> Binary
                | _ -> failwith "Invalid opcode."
            """

    match failwithContextIn source with
    | [ s ] ->
        let edits =
            (s.Range, s.OriginalText, s.ReplacementText) :: Option.toList s.PatternEdit

        let patched = applyAll source edits

        Assert.Equal(
            fsharp
                """
                module Test
                type Opcode =
                    | Text
                    | Binary
                let toOpcode = function
                    | 0uy -> Text
                    | 1uy -> Binary
                    | value -> failwith $"Invalid opcode., calling toOpcode with value: {value}"
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one function-arm hint, got %A" other

    // a `function` over a type that prints nothing stays quiet, and so does
    // a throw under a NESTED match, whose wildcard is not the argument
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decode = function
                    | Some(bytes: byte[]) -> bytes.Length
                    | None -> failwith "Error"
                """
        )
    )

    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let decode = function
                    | (n: int) when n > 0 ->
                        match n % 2 with
                        | 0 -> n
                        | _ -> failwith "Error"
                    | _ -> 0
                """
        )
    )

[<Fact>]
let ``a File factory result leaks like a bare constructor`` () =
    // File.OpenRead is THE way to open a file; ownership transfers to the
    // caller exactly as with `new FileStream(...)`
    let suggestions =
        useBindingsIn (
            fsharp
                """
                let f (path: string) =
                    let stream = System.IO.File.OpenRead path
                    let n = stream.ReadByte()
                    n
                """
        )

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
    // and TorchSharp code is full of it
    let _, _, tuples =
        cleanupsIn (
            fsharp
                """
                module Test
                let grid = Array3D.zeroCreate<int> 3 3 3
                let read = grid[0, 1, 2]
                let write () = grid[0, 1, 2] <- 5
                """
        )

    Assert.Empty tuples

[<Fact>]
let ``the legacy dot-bracket indexer is not a single-tuple list either`` () =
    let _, _, tuples =
        cleanupsIn (
            fsharp
                """
                module Test
                let grid = Array3D.zeroCreate<int> 3 3 3
                let read = grid.[0, 1, 2]
                """
        )

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
        cleanupsIn (
            fsharp
                """
                module Test
                let f (xs: 'a list) = xs.Length
                let n = f [ 1, 2 ]
                """
        )

    match tuples with
    | [ s ] -> Assert.Equal(2, s.Elements)
    | other -> failwithf "Expected exactly one single-tuple note, got %A" other

[<Fact>]
let ``new stays where a union case would capture the construction`` () =
    // in expression position a UNION CASE wins over a type name, so `new` is
    // the only thing forcing the constructor path. With a LazyTexture class
    // beside a Texture.LazyTexture case, dropping `new` turns a six-argument
    // construction into a one-argument case application, and the tuple is
    // checked against the case payload
    let source =
        fsharp
            """
            module Test
            type Thing(a: int, b: int) =
                member _.Sum = a + b

            type Wrapper =
                | Thing of Thing

            let shadowed = new Thing(1, 2)
            """

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
    // and the bare name fails with "takes 2 argument(s) but is here given 0".
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected the one-fragment construction to qualify, got %A" other

// ---- FR0086 and an expected FormattableString ----

let private holeFreeIn (source: string) =
    syntaxIn source
    |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)

[<Fact>]
let ``a hole-free interpolation annotated as FormattableString keeps its dollar`` () =
    // the `$` is what makes the conversion to FormattableString available; a
    // plain string never converts
    Assert.Empty(
        holeFreeIn (
            fsharp
                """
                module Test
                let s3: System.FormattableString = $"I have no holes"
                """
        )
    )

[<Fact>]
let ``a hole-free interpolation passed to a method keeps its dollar`` () =
    // only the typed tree could say whether the parameter is a
    // FormattableString; a syntactic rule declines rather than guess
    Assert.Empty(
        holeFreeIn (
            fsharp
                """
                module Test
                let s = System.FormattableString.Invariant($"no holes")
                """
        )
    )

[<Fact>]
let ``a hole-free interpolation bound plainly still loses its dollar`` () =
    match holeFreeIn "module Test\nlet s = $\"no holes\"" with
    | [ s ] -> Assert.Equal("\"no holes\"", s.ReplacementText)
    | other -> failwithf "Expected the plain case to keep its fix, got %A" other

[<Fact>]
let ``a hole-free interpolation passed to an F# function keeps its dollar`` () =
    // Ionide's `Log.setMessageI $"..."` takes a FormattableString and its
    // spelling does not say so
    Assert.Empty(
        holeFreeIn (
            fsharp
                """
                module Test
                let setMessageI (m: System.FormattableString) = m.Format
                let s = setMessageI $"Enter loading projects"
                """
        )
    )

[<Fact>]
let ``FR0092 leaves a message the file reads back elsewhere`` () =
    // the test below asserts on the exact text: amending it breaks
    // the assertion
    Assert.Empty(
        failwithContextIn (
            fsharp
                """
                module Test
                let gen (prompt: string) =
                    failwith "model inference failed"
                let check () =
                    try gen "q" with e -> e.Message = "model inference failed"
                """
        )
    )

[<Fact>]
let ``FR0086 strips the dollar from a printfn argument when the typed tree shows no FormattableString`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                printfn $"Status: Processing"
            """

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
        fsharp
            """
            module Test
            let log (m: System.FormattableString) = m.Format
            let f () =
                log $"Status: Processing"
            """

    let tree, sourceText, checkResults = parseAndCheck source

    Assert.Empty(
        RedundantSyntax.find (Some checkResults) tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

[<Fact>]
let ``FR0086 keeps the dollar in an argument without the typed tree`` () =
    let source =
        fsharp
            """
            module Test
            let f () =
                printfn $"Status: Processing"
            """

    let tree, sourceText = parse source

    Assert.Empty(
        RedundantSyntax.find None tree sourceText
        |> List.filter (fun s -> s.Kind = RedundantSyntax.Kind.HoleFreeInterpolation)
    )

[<Fact>]
let ``FR0077 also offers stubs returning the empty value of each member's type`` () =
    let source =
        fsharp
            """
            module Test
            type IThing =
                abstract member Go: unit -> int
                abstract member Stop: string -> unit
                abstract member Tags: string list
                abstract member Name: string

            let t =
                { new IThing with
                    member _.Go() = 1 }
            """

    match missingIn source with
    | [ s ] ->
        Assert.Contains("member _.Stop(arg0) = ()", s.EmptyInsertText)
        Assert.Contains("member _.Tags = []", s.EmptyInsertText)
        Assert.Contains("member _.Name = \"\"", s.EmptyInsertText)
        Assert.DoesNotContain("NotImplementedException", s.EmptyInsertText)
        let patched = applyEdit source s.Range s.EmptyInsertText
        assertTypechecks "The empty-value stub file" patched
    | other -> failwithf "Expected exactly one implement-missing fix, got %A" other

[<Fact>]
let ``FR0081: a dot-segment prefix is relative-path notation, not a join`` () =
    // `"./" + path` — Path.Combine cannot spell a `./` prefix
    Assert.Empty(pathsIn "module Test\nlet relative (path: string) = \"./\" + path")

[<Fact>]
let ``FR0081: appending parent segments is not a join either`` () =
    Assert.Empty(pathsIn "module Test\nlet up (prefix: string) = prefix + \"../\"")

[<Fact>]
let ``FR0081: a document pointer joined in a JSON module is not a filesystem path`` () =
    // `doc.Path() + "/" + name` is a JSON pointer
    Assert.Empty(
        pathsIn (
            fsharp
                """
                module JsonRuntime
                let pointer (jsonPath: string) (name: string) = jsonPath + "/" + name
                """
        )
    )

[<Fact>]
let ``FR0079: the editor fix is the one element itself`` () =
    match
        singlesIn (
            fsharp
                """
                module Test
                open System.Threading.Tasks
                let run (t: Task<int>) = Task.WhenAll [| t |]
                """
        )
    with
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
        cleanupsIn (
            fsharp
                """
                module Test
                let xs = [ 1, 2, 3 ]
                let ys = [| 1.5, 2.5 |]
                """
        )

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
        fsharp
            """
            module Test
            open System
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.Threading.Tasks", s.Namespace)
        Assert.Equal(3, s.Uses)
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                open System
                open System.Threading.Tasks
                let a = Task.FromResult 1
                let b = Task.Delay 10
                let c (t: Task<int>) = t.Result
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: an open whose extension member would split a tupled call is declined`` () =
    // F#'s method-call syntax hands `x.M (a, b)` over as TWO arguments once
    // a two-parameter overload of M is in scope, and an open can bring one:
    // `seen.Contains (entity, ct)` is the tuple argument of
    // List<T>.Contains until `open System.Linq` arrives, then stops
    // compiling far from the edit. Three spellings would normally
    // earn the open; here they earn a note that names the mechanism
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let seen = List<string * int>()
            let check (e: string) (ct: int) = if not (seen.Contains (e, ct)) then seen.Add(e, ct)
            let a (xs: int[]) = System.Linq.Enumerable.Sum xs
            let b (xs: int[]) = System.Linq.Enumerable.Max xs
            let c (xs: int[]) = System.Linq.Enumerable.Min xs
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System.Linq") with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("'Contains'", s.Reason.Value)
        Assert.Contains("tupled argument", s.Reason.Value)
    | other -> failwithf "Expected a declined System.Linq finding, got %A" other

[<Fact>]
let ``FR0147: the same file without a tupled call gets its System.Linq open`` () =
    // the guard is about the calls in the file, not about the namespace
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let seen = List<string * int>()
            let check (e: string) (ct: int) = if not (seen.Contains((e, ct))) then seen.Add(e, ct)
            let a (xs: int[]) = System.Linq.Enumerable.Sum xs
            let b (xs: int[]) = System.Linq.Enumerable.Max xs
            let c (xs: int[]) = System.Linq.Enumerable.Min xs
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System.Linq") with
    | [ s ] ->
        Assert.Equal(None, s.Reason)
        let patched = applyAll source s.Edits
        Assert.Contains("open System.Linq", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected an offered System.Linq finding, got %A" other

[<Fact>]
let ``FR0147: the tupled-call guard holds for any namespace with the extension, not System.Linq alone`` () =
    // a project's own namespace exporting a generic `Contains` extension, from
    // another of its files, does exactly what Enumerable's does
    let extensions =
        fsharp
            """
            namespace Ext
            open System.Runtime.CompilerServices
            [<Extension>]
            type ListExt =
                [<Extension>]
                static member Contains(xs: System.Collections.Generic.List<'T>, a: 'T, b: int) = b > 0
                [<Extension>]
                static member Sum(xs: int[]) = Array.sum xs
                [<Extension>]
                static member Max(xs: int[]) = Array.max xs
                [<Extension>]
                static member Min(xs: int[]) = Array.min xs
            """

    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let seen = List<string * int>()
            let check (e: string) (ct: int) = if not (seen.Contains (e, ct)) then seen.Add(e, ct)
            let a (xs: int[]) = Ext.ListExt.Sum xs
            let b (xs: int[]) = Ext.ListExt.Max xs
            let c (xs: int[]) = Ext.ListExt.Min xs
            """

    let tree, sourceText, checkResults = parseAndCheckSecond extensions source

    match
        QualifiedNames.find 3 2 tree sourceText checkResults
        |> List.filter (fun s -> s.Namespace = "Ext")
    with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("'Contains'", s.Reason.Value)
    | other -> failwithf "Expected a declined Ext finding, got %A" other

[<Fact>]
let ``FR0147: a tupled call that already resolves to an instance overload of that arity is no clash`` () =
    // `s.EndsWith("x", StringComparison.Ordinal)` is String's own
    // two-parameter overload; System's MemoryExtensions.EndsWith cannot
    // take it over, so `open System` goes in rather than a note
    let source =
        fsharp
            """
            module Test
            let a (s: string) = s.EndsWith("x", System.StringComparison.Ordinal)
            let b () = System.DateTime.UtcNow
            let c () = System.Environment.TickCount
            let d () = System.GC.Collect()
            """

    match qualifiedIn source |> List.filter (fun s -> s.Namespace = "System") with
    | [ s ] ->
        Assert.Equal(None, s.Reason)
        let patched = applyAll source s.Edits
        Assert.Contains("open System", patched)
        Assert.Contains("""s.EndsWith("x", StringComparison.Ordinal)""", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected an offered System finding, got %A" other

[<Fact>]
let ``FR0147: only the namespace part goes, a type stays qualified by its name`` () =
    let source =
        fsharp
            """
            module Test
            let a (p: string) = System.IO.File.Exists p
            let b (p: string) = System.IO.File.ReadAllText p
            let c (p: string) = System.IO.Path.GetFileName p
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        let patched = applyAll source s.Edits

        Assert.Contains(
            fsharp
                """
                open System.IO
                let a (p: string) = File.Exists p
                """,
            patched
        )

        Assert.Contains("Path.GetFileName p", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: two uses of a shallow namespace are not worth an open`` () =
    Assert.Empty(
        qualifiedIn (
            fsharp
                """
                module Test
                let a (p: string) = System.IO.File.Exists p
                let b (p: string) = System.IO.File.ReadAllText p
                """
        )
    )

[<Fact>]
let ``FR0147: a namespace the file already opens only gets its uses shortened`` () =
    let source =
        fsharp
            """
            module Test
            open System.IO
            let a (p: string) = System.IO.File.Exists p
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                open System.IO
                let a (p: string) = File.Exists p
                """,
            patched
        )
    | other -> failwithf "Expected one shortening, got %A" other

[<Fact>]
let ``FR0147: a namespace whose open would clash with a name the file defines is noted, not fixed`` () =
    // the file's own `File` is why the author qualified System.IO.File
    let source =
        fsharp
            """
            module Test
            type File = { Name: string }
            let a (p: string) = System.IO.File.Exists p
            let b (p: string) = System.IO.File.ReadAllText p
            let c (p: string) = System.IO.Path.GetFileName p
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        Assert.Empty s.Edits
        Assert.Equal(Some "this file defines 'File' itself", s.Reason)
    | other -> failwithf "Expected one clash note, got %A" other

[<Fact>]
let ``FR0147: a clash note names the clashing identifier and where it comes from`` () =
    // "would clash with a name this file already uses" leaves the reader to
    // find the name; the note says which and whence
    let fromAnotherOpen =
        fsharp
            """
            module Test
            open System.Timers
            let a (t: System.Threading.Timer) = t.Dispose()
            let b (t: System.Threading.Timer) = t.Dispose()
            let c (t: System.Threading.Timer) = t.Dispose()
            """

    match qualifiedIn fromAnotherOpen with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Equal(Some "'Timer' (open System.Timers) already comes from another open of this file", s.Reason)
    | other -> failwithf "Expected one clash note, got %A" other

    // `FSComp.SR.x` many times, and `SR` already in scope from `Internal.Utilities` — the note names SR and
    // the open that brings it
    let lib =
        fsharp
            """
            namespace Internal.Utilities
            module SR =
                let a () = 1
            namespace FSComp
            module SR =
                let b () = 2
            """

    let user =
        fsharp
            """
            module Test
            open Internal.Utilities
            let x () = FSComp.SR.b () + FSComp.SR.b () + FSComp.SR.b () + SR.a ()
            """

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
        qualifiedIn (
            fsharp
                """
                module Test
                let a = System.Threading.Tasks.Task.FromResult 1
                let b = System.Threading.Tasks.Task.FromResult 2
                let c = System.Threading.Tasks.Task.FromResult 3
                """
        )
    with
    | [ s ] ->
        Assert.NotEmpty s.Edits
        Assert.Equal(None, s.Reason)
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``FR0147: the default thresholds are six uses, or four for a deep namespace`` () =
    let tree, sourceText, checkResults =
        parseAndCheck (
            fsharp
                """
                module Test
                let a = System.Threading.Tasks.Task.FromResult 1
                let b = System.Threading.Tasks.Task.FromResult 2
                let c = System.Threading.Tasks.Task.FromResult 3
                let d (p: string) = System.IO.File.Exists p
                let e (p: string) = System.IO.File.Exists p
                let f (p: string) = System.IO.File.Exists p
                let g (p: string) = System.IO.File.Exists p
                let h (p: string) = System.IO.File.Exists p
                """
        )

    // three deep uses and five shallow ones: neither reaches the default
    Assert.Empty(QualifiedNames.find 6 4 tree sourceText checkResults)

    let tree2, sourceText2, checkResults2 =
        parseAndCheck (
            fsharp
                """
                module Test
                let a = System.Threading.Tasks.Task.FromResult 1
                let b = System.Threading.Tasks.Task.FromResult 2
                let c = System.Threading.Tasks.Task.FromResult 3
                let d = System.Threading.Tasks.Task.FromResult 4
                """
        )

    match QualifiedNames.find 6 4 tree2 sourceText2 checkResults2 with
    | [ s ] -> Assert.Equal(4, s.Uses)
    | other -> failwithf "Expected the deep namespace at four uses, got %A" other

[<Fact>]
let ``FR0147: the open lands beside the opens of the same family`` () =
    let source =
        fsharp
            """
            module Test
            open System
            open System.IO
            open Microsoft.FSharp.Collections
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.StartsWith(
            fsharp
                """
                module Test
                open System
                open System.IO
                open System.Threading.Tasks
                open Microsoft.FSharp.Collections

                """,
            patched
        )
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: namespaces come deepest first, and their opens end up shallow to deep`` () =
    let source =
        fsharp
            """
            module Test
            let a (s: string) = System.String.IsNullOrEmpty s
            let b (s: string) = System.String.IsNullOrEmpty s
            let c (s: string) = System.String.IsNullOrEmpty s
            let d = System.Collections.Generic.List<int>()
            let e = System.Collections.Generic.Dictionary<int, int>()
            """

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
            fsharp
                """
                module Test
                open System
                open System.Collections.Generic
                let a (s: string) = String.IsNullOrEmpty s
                """,
            patched
        )

        Assert.Contains("let d = List<int>()", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected the deep namespace first and the shallow one second, got %A" other

[<Fact>]
let ``FR0147: an open the file already has is never inserted again`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let d = System.Collections.Generic.List<int>()
            let e = System.Collections.Generic.Dictionary<int, int>()
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Empty(s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open"))
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                open System.Collections.Generic
                let d = List<int>()
                let e = Dictionary<int, int>()
                """,
            patched
        )
    | other -> failwithf "Expected one shortening, got %A" other

[<Fact>]
let ``FR0147: an existing open System.Collections gets Generic after it and System before it`` () =
    let source =
        fsharp
            """
            module Test
            open System.Collections
            let a (s: string) = System.String.IsNullOrEmpty s
            let b (s: string) = System.String.IsNullOrEmpty s
            let c (s: string) = System.String.IsNullOrEmpty s
            let d = System.Collections.Generic.List<int>()
            let e = System.Collections.Generic.Dictionary<int, int>()
            """

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
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private consume (s: Stream) =
                    use s = s
                    s.ReadByte()
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    consume stream
                """
        )
    )

[<Fact>]
let ``a disposable handed to a same-file function that keeps it names the leak`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private consume (s: Stream) = s.ReadByte()
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    consume stream
                """
        )
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.Function("consume", true)), s.Destination)
        Assert.Contains("in this file, which does not dispose it", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``a disposable in a tuple element is followed to the matching parameter`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private consume (name: string, s: Stream) =
                    s.Dispose()
                    name
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    consume ("x", stream)
                """
        )
    )

[<Fact>]
let ``a leak in the entry point says so`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                [<EntryPoint>]
                let main (argv: string[]) =
                    let stream = new FileStream(argv.[0], FileMode.Open)
                    printfn "%d" (stream.ReadByte())
                    0
                """
        )
    with
    | [ s ] ->
        Assert.Equal(Some("let", "use"), s.Fix)
        Assert.Equal(Some UseBinding.ScopeContext.EntryPoint, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leaked handle in the entry point is an ordinary leak`` () =
    // the OS reclaims the handle at exit; there is no unflushed work
    match
        useBindingsIn (
            fsharp
                """
                module Test
                [<EntryPoint>]
                let main (argv: string[]) =
                    let cts = new System.Threading.CancellationTokenSource()
                    printfn "%b" cts.IsCancellationRequested
                    0
                """
        )
    with
    | [ s ] -> Assert.Equal(None, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leak in an action method is a per-request leak`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type HttpGetAttribute() =
                    inherit System.Attribute()
                type Api() =
                    [<HttpGet>]
                    member _.Get(path: string) =
                        let stream = new FileStream(path, FileMode.Open)
                        stream.ReadByte()
                """
        )
    with
    | [ s ] -> Assert.Equal(Some UseBinding.ScopeContext.RequestHandler, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``a leak in a controller member is a per-request leak`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type ControllerBase() =
                    class
                    end
                type Api() =
                    inherit ControllerBase()
                    member _.Get(path: string) =
                        let stream = new FileStream(path, FileMode.Open)
                        stream.ReadByte()
                """
        )
    with
    | [ s ] -> Assert.Equal(Some UseBinding.ScopeContext.RequestHandler, s.Context)
    | other -> failwithf "Expected exactly one use-binding fix, got %A" other

[<Fact>]
let ``FR0147: a file without a module line gets the open before its first declaration`` () =
    // the implicit module of a last file or a script has no header line to
    // go under; the "header" range is the first declaration's own line
    let source =
        fsharp
            """
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                open System.Threading.Tasks
                let a = Task.FromResult 1
                let b = Task.Delay 10
                let c (t: Task<int>) = t.Result
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: an expression head naming a type from elsewhere is a clash, a module of that name is not`` () =
    // `Queue.Synchronized` is System.Collections.Queue; opening
    // System.Collections.Generic would re-bind `Queue` to the generic one
    let clashing =
        fsharp
            """
            module Test
            open System.Collections
            let q () = Queue.Synchronized(Queue())
            let a = System.Collections.Generic.List<int>()
            let b = System.Collections.Generic.List<int>()
            let c = System.Collections.Generic.List<int>()
            """

    match qualifiedIn clashing with
    | [ s ] ->
        Assert.Equal("System.Collections.Generic", s.Namespace)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one clash note, got %A" other

    // `List.map` is the F# List module, which coexists with the generic List
    let coexisting =
        fsharp
            """
            module Test
            let xs = List.map id [ 1 ]
            let a = System.Collections.Generic.List<int>()
            let b = System.Collections.Generic.List<int>()
            let c = System.Collections.Generic.List<int>()
            """

    match qualifiedIn coexisting with
    | [ s ] -> Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``a disposable handed to one of two same-named functions is not followed`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                module A =
                    let consume (s: Stream) =
                        use s = s
                        s.ReadByte()
                module B =
                    let consume (s: Stream) = s.ReadByte()
                open B
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    consume stream
                """
        )
    with
    | [ s ] -> Assert.Equal(Some(UseBinding.Destination.Function("consume", false)), s.Destination)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``FR0147: a short name another open already brings is a clash, even for a namespace that is open`` () =
    // System.Timers has a Timer too: the author qualified System.Threading's
    // on purpose (as with FSharp.Data.HttpMethod beside System.Net.Http's)
    let freshOpen =
        fsharp
            """
            module Test
            open System.Timers
            let a (t: System.Threading.Timer) = t.Dispose()
            let b (t: System.Threading.Timer) = t.Dispose()
            let c (t: System.Threading.Timer) = t.Dispose()
            """

    match qualifiedIn freshOpen with
    | [ s ] ->
        Assert.Equal("System.Threading", s.Namespace)
        Assert.Empty s.Edits
    | other -> failwithf "Expected one clash note, got %A" other

    // already open, still qualified: nothing to say at all
    let alreadyOpen =
        fsharp
            """
            module Test
            open System.Threading
            open System.Timers
            let a (t: System.Threading.Timer) = t.Dispose()
            let b (t: System.Threading.Timer) = t.Dispose()
            let c (t: System.Threading.Timer) = t.Dispose()
            """

    Assert.Empty(qualifiedIn alreadyOpen)

let private qualifiedInSecond (lib: string) (user: string) =
    let tree, sourceText, checkResults = parseAndCheckSecond lib user
    QualifiedNames.find 3 2 tree sourceText checkResults

[<Fact>]
let ``FR0147: a module named like its namespace is not the namespace`` () =
    // `namespace rec Toro` holds a `module Toro`; `Toro.noGrad` names
    // the module, and under `open Toro` a bare `noGrad` reaches nothing
    let lib =
        fsharp
            """
            namespace Toro
            module Toro =
                let noGrad (f: unit -> 'a) : 'a = f ()
            """

    let user =
        fsharp
            """
            module Example
            open Toro
            let a = Toro.noGrad (fun () -> 1)
            let b = Toro.noGrad (fun () -> 2)
            let c = Toro.noGrad (fun () -> 3)
            """

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: a same-project module of the introduced name is a clash`` () =
    // Utils.Utils.Expect beside Expecto.Expect — the qualified
    // Expecto.Expect is the author's way of reaching the other
    let lib =
        fsharp
            """
            namespace Lib
            module Expect =
                let equal (a: int) (b: int) = ()
            namespace Utils
            module Utils =
                module Expect =
                    let equal (a: int) (b: int) (msg: string) = ()
            """

    let user =
        fsharp
            """
            module Tests
            open Lib
            open Utils.Utils
            let a = Expect.equal 1 1 "m"
            let b = Lib.Expect.equal 1 1
            let c = Lib.Expect.equal 2 2
            let d = Lib.Expect.equal 3 3
            """

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: a same-project namespace still gets its open`` () =
    let lib =
        fsharp
            """
            namespace Lib.Deep
            type Thing() =
                static member Make() = Thing()
            """

    let user =
        fsharp
            """
            module Example
            let a = Lib.Deep.Thing.Make()
            let b = Lib.Deep.Thing.Make()
            let c = Lib.Deep.Thing.Make()
            """

    match qualifiedInSecond lib user with
    | [ s ] ->
        Assert.Equal("Lib.Deep", s.Namespace)
        Assert.NotEmpty s.Edits
    | other -> failwithf "Expected one qualified-names fix, got %A" other

[<Fact>]
let ``FR0147: the open goes under the module line, not under the doc comment above it`` () =
    // a doc comment precedes the module line, and the module's range
    // starts at the comment
    let source =
        fsharp
            """
            /// Doc line one
            /// Doc line two
            module Test
            let a = System.Threading.Tasks.Task.FromResult 1
            let b = System.Threading.Tasks.Task.Delay 10
            let c (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                /// Doc line one
                /// Doc line two
                module Test
                open System.Threading.Tasks
                let a = Task.FromResult 1
                let b = Task.Delay 10
                let c (t: Task<int>) = t.Result
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one qualified-names finding, got %A" other

[<Fact>]
let ``FR0147: an open further down the file covers nothing above it`` () =
    // an open of System.Text.RegularExpressions far down the file: the
    // uses above it are not "already open", and the new open cannot land
    // beside that one either
    let source =
        fsharp
            """
            module Test
            let a = System.Text.RegularExpressions.Regex("x")
            let b = System.Text.RegularExpressions.Regex("y")
            let c = System.Text.RegularExpressions.Regex("z")
            open System.Text.RegularExpressions
            let d = Regex("w")
            """

    match qualifiedIn source with
    | [ s ] ->
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                open System.Text.RegularExpressions
                let a = Regex("x")
                let b = Regex("y")
                let c = Regex("z")
                open System.Text.RegularExpressions
                let d = Regex("w")
                """,
            patched
        )

        assertTypechecks "Patched source" patched
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
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one finding per block, got %A" other

[<Fact>]
let ``FR0147: a namespace shadowed by a module of its name is never opened`` () =
    // `[<RequireQualifiedAccess>] module OpenGL` in namespace Nu beside
    // `namespace Nu.OpenGL` — `open Nu.OpenGL` resolves to the module and
    // is refused, so the qualified spelling stays
    let lib =
        fsharp
            """
            namespace Nu
            [<RequireQualifiedAccess>]
            module OpenGL =
                let version = 1
            namespace Nu.OpenGL
            type Thing() =
                static member Make() = Thing()
            """

    let user =
        fsharp
            """
            module Example
            let a = Nu.OpenGL.Thing.Make()
            let b = Nu.OpenGL.Thing.Make()
            let c = Nu.OpenGL.Thing.Make()
            """

    // `open Nu` with `OpenGL.Thing` is fine (the module name still
    // qualifies the access); `open Nu.OpenGL` is what the compiler refuses
    for s in qualifiedInSecond lib user do
        for _, _, text in s.Edits do
            Assert.DoesNotContain("open Nu.OpenGL", text)

[<Fact>]
let ``FR0147: an active pattern another open brings shadows the constructor of that name`` () =
    // `(|Ident|_|)` from an opened module over
    // FSharp.Compiler.Syntax.Ident — the shortened `Ident(...)` applies the
    // pattern ("This value is not a function")
    let lib =
        fsharp
            """
            namespace Lib.Syntax
            type Ident(text: string) =
                member _.Text = text
            namespace Lib.Helpers
            module Patterns =
                let (|Ident|_|) (s: string) = if s = "" then None else Some s
            """

    let user =
        fsharp
            """
            module Example
            open Lib.Syntax
            open Lib.Helpers.Patterns
            let a = Lib.Syntax.Ident("a")
            let b = Lib.Syntax.Ident("b")
            let c = Lib.Syntax.Ident("c")
            """

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0147: an open inside a nested module does not count for the file`` () =
    // nested test modules with their own opens; a
    // qualified System.IO in a later nested module still needs the open
    let source =
        fsharp
            """
            module Test
            module First =
                open System.Text
                let a = StringBuilder()
            module Second =
                let p = System.IO.Path.Combine("a", "b")
                let q = System.IO.File.Exists p
                let r = System.IO.File.Exists "c"
            """

    match qualifiedIn source with
    | [ s ] ->
        Assert.Equal("System.IO", s.Namespace)
        let patched = applyAll source s.Edits

        Assert.Equal(
            fsharp
                """
                module Test
                open System.IO
                module First =
                    open System.Text
                    let a = StringBuilder()
                module Second =
                    let p = Path.Combine("a", "b")
                    let q = File.Exists p
                    let r = File.Exists "c"
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one qualified-names fix, got %A" other

// ---- FR0085: a function spelled like the type keeps the `new` ----

[<Fact>]
let ``FR0085: a same-named function brought by open keeps new`` () =
    // `type Parse` in one module, `let Parse (_: 'a)` in a second, both opened:
    // `new Parse()` builds the class and `Parse()` calls the function: the
    // tag goes from "ctor" to "function", and it compiles either way, so
    // nothing downstream catches it
    let clashing =
        fsharp
            """
            module Test
            module A =
                type Parse(tag: string) =
                    new() = Parse "ctor"
                    member _.Tag = tag
            module B =
                let Parse (_: 'a) = A.Parse "function"
            module C =
                open A
                open B
                let make () = new Parse()
            """

    let tree, sourceText, checkResults = parseAndCheck clashing
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // the same file without B opened: nothing captures the name, `new` goes
    let clean =
        fsharp
            """
            module Test
            module A =
                type Parse(tag: string) =
                    new() = Parse "ctor"
                    member _.Tag = tag
            module C =
                open A
                let make () = new Parse()
            """

    let tree, sourceText, checkResults = parseAndCheck clean
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: a same-named function declared beside the type keeps new`` () =
    // the same-file guard cannot see a function in ANOTHER file. Where its
    // signature disagrees the bare form is a type error and the build check
    // puts it back; where it is GENERIC it typechecks and quietly calls the
    // function instead of the constructor, which nothing downstream catches
    let generic =
        fsharp
            """
            module Test
            type Widget(a: int, b: int) =
                member _.Sum = a + b
            let Widget (_: 'a) = Widget(0, 0)
            let make () = new Widget(1, 2)
            """

    let tree, sourceText, checkResults = parseAndCheck generic
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // no sibling of that name: the `new` still goes
    let plain =
        fsharp
            """
            module Test
            type Widget(a: int, b: int) =
                member _.Sum = a + b
            let make () = new Widget(1, 2)
            """

    let tree, sourceText, checkResults = parseAndCheck plain
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: new string keeps its new - the bare name is the conversion function`` () =
    // `string (chars, i, n)` is FSharp.Core's
    // `string` applied to a TUPLE - it yields "(System.Char[], 1, 3)", typechecks
    // as string either way, and every id built so becomes that literal
    let lowercase =
        fsharp
            """
            module Test
            let take (output: char[]) (index: int) = new string (output, index + 1, 12 - index)
            """

    let tree, sourceText, checkResults = parseAndCheck lowercase
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    // the TYPE spelling names no function, so it still drops
    let uppercase =
        fsharp
            """
            module Test
            let take (output: char[]) (index: int) = new System.String (output, index + 1, 12 - index)
            """

    let tree, sourceText, checkResults = parseAndCheck uppercase
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``FR0085: a function bound with the type's name keeps new`` () =
    // `let SharedRow(elems) = new SharedRow(elems, hash)`;
    // without `new` the bare name is the function, called with the wrong arguments
    let shadowed =
        fsharp
            """
            module Test
            type SharedRow(elems: int[], hash: int) =
                member _.Hash = hash
            let SharedRow(elems: int[]) = new SharedRow(elems, elems.Length)
            let make (xs: int[]) = new SharedRow(xs, 1)
            """

    let tree, sourceText, checkResults = parseAndCheck shadowed
    Assert.Empty(RedundantNew.find tree sourceText checkResults)

    let plain =
        fsharp
            """
            module Test
            type SharedRow(elems: int[], hash: int) =
                member _.Hash = hash
            let make (xs: int[]) = new SharedRow(xs, 1)
            """

    let tree, sourceText, checkResults = parseAndCheck plain
    Assert.Single(RedundantNew.find tree sourceText checkResults) |> ignore

[<Fact>]
let ``a disposable handed to a disposable owner's property or Add is adopted`` () =
    // HttpRequestMessage disposes its Content, MultipartContent its parts
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                let send (client: HttpClient) (body: string) =
                    use request = new HttpRequestMessage(HttpMethod.Post, "http://x")
                    let content = new StringContent(body)
                    request.Content <- content
                    client.Send request
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                let build (body: string) =
                    use multipart = new MultipartFormDataContent()
                    let part = new StringContent(body)
                    multipart.Add(part, "body")
                    multipart.Headers.ContentLength
                """
        )
    )

[<Fact>]
let ``FR0075: HttpClient, a request message and its contents, a SemaphoreSlim are nobody's leak`` () =
    // CR0060's noOwnership list: a client is a shared lifetime; a request
    // and its StringContent own nothing unmanaged and a handler mock reads
    // them back after the send (a `use` there breaks the test); a
    // SemaphoreSlim's wait handle is only allocated on contended use
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                let fetch (url: string) =
                    let client = new HttpClient()
                    client.GetStringAsync(url).Result
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Net.Http
                let send (client: HttpClient) (body: string) =
                    let request = new HttpRequestMessage(HttpMethod.Post, "http://x")
                    let content = new StringContent(body)
                    request.Content <- content
                    client.Send(request).StatusCode
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Threading
                let guard (work: unit -> int) =
                    let gate = new SemaphoreSlim(1)
                    gate.Wait()
                    let r = work ()
                    gate.Release() |> ignore
                    r
                """
        )
    )

[<Fact>]
let ``FR0147: a union case an F#-compiled assembly's namespace brings is a clash`` () =
    // `type SymbolKind = | Ident | ...` in an F# library's namespace beside
    // FCS's Ident class — an F# assembly nests its types under namespace
    // entities, which a top-level scan never sees. FSharp.Core is such an
    // assembly: its
    // Microsoft.FSharp.Control brings `Async`
    let lib =
        fsharp
            """
            namespace Lib.Ctl
            type Async(x: int) =
                member _.X = x
            """

    let user =
        fsharp
            """
            module Example
            open Microsoft.FSharp.Control
            let a = Lib.Ctl.Async(1).X
            let b = Lib.Ctl.Async(2).X
            let c = Lib.Ctl.Async(3).X
            """

    match qualifiedInSecond lib user with
    | [ s ] -> Assert.Empty s.Edits
    | [] -> ()
    | other -> failwithf "Expected a clash note or silence, got %A" other

// ---- FR0140: a greedy last constructor argument gets its parentheses ----

[<Fact>]
let ``FR0140: a lambda argument is parenthesised before the named properties`` () =
    // `TypeProviderConfig(fun _ -> false)` — appended
    // properties would land inside the lambda as a tuple
    let source =
        fsharp
            """
            module Test
            type Cfg(f: int -> bool) =
                member val Hosted = false with get, set
                member val Name = "" with get, set
            let make () =
                let cfg = Cfg(fun _ -> false)
                cfg.Hosted <- true
                cfg.Name <- "x"
                cfg
            """

    let tree, sourceText, checkResults = parseAndCheck source

    match ObjectInitializer.find tree sourceText checkResults with
    | [ s ] ->
        Assert.Equal("""Cfg((fun _ -> false), Hosted = true, Name = "x")""", s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected one construction rewrite, got %A" other

[<Fact>]
let ``FR0147: a shortening that lands on an FSharp.Core name is withheld`` () =
    // `Tagged.Map<_, _>.FromList` under an
    // `open Internal.Utilities.Collections.Tagged` — shortened to
    // `Map<_, _>` it reaches FSharp.Core's Map, which has no FromList
    // (`Tagged.Map<_, _>` is an ABBREVIATION of the three-parameter type; a
    // real type of the name would shadow FSharp.Core's and shorten fine)
    let lib =
        fsharp
            """
            namespace Tagged
            type Map<'K, 'V, 'Tag> =
                { Items: ('K * 'V) list }
                static member FromList(tag: 'Tag, xs: ('K * 'V) list) : Map<'K, 'V, 'Tag> =
                    ignore tag
                    { Items = xs }
            type Map<'K, 'V> = Map<'K, 'V, int>
            """

    let user =
        fsharp
            """
            module Example
            open Tagged
            let a = Tagged.Map<int, int>.FromList(0, [ 1, 2 ])
            let b = Tagged.Map<int, int>.FromList(0, [])
            let c = Tagged.Map<int, int>.FromList(0, [ 3, 4 ])
            """

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
    // `FSharp.Compiler.Diagnostics.Metrics.Meter` (a module value) shortened
    // to `Metrics.Meter` under `open System.Diagnostics` reaches
    // System.Diagnostics.Metrics.Meter, the type
    let lib =
        fsharp
            """
            namespace Diag.Metrics
            type Meter(name: string) =
                member _.Name = name
            namespace Own
            module Metrics =
                let Meter = "m"
            """

    let user =
        fsharp
            """
            module Example
            open Own
            open Diag
            let a = Own.Metrics.Meter
            let b = Own.Metrics.Meter + "x"
            let c = Own.Metrics.Meter + "y"
            """

    let _, _, checkResults = parseAndCheckSecond lib user

    Assert.Empty(
        checkResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
    )

    Assert.Empty(qualifiedInSecond lib user)

[<Fact>]
let ``FR0088: a nullary case drops its wildcard altogether, a case with data keeps one`` () =
    // `Constructor(_)` is accepted for a
    // case that takes no data, `Constructor _` is not
    let _, wilds, _ =
        cleanupsIn (
            fsharp
                """
                type K =
                    | Ctor
                    | Mem of int
                let f k =
                    match k with
                    | Ctor(_) -> 0
                    | Mem(_) -> 1
                """
        )

    match wilds |> List.sortBy (fun s -> s.Range.StartLine) with
    | [ ctor; mem ] ->
        Assert.Equal("", ctor.ReplacementText)
        Assert.Equal(" _", mem.ReplacementText)
    | other -> failwithf "Expected two wildcard cleanups, got %A" other

[<Fact>]
let ``FR0147: an open that would capture a bare union-case construction is withheld`` () =
    // `Byte('x'B)` is its own Constant case
    // until `open System` makes it the System.Byte constructor
    let lib =
        fsharp
            """
            namespace Lint
            type Constant =
                | Byte of byte
                | Str of string
            """

    let user =
        fsharp
            """
            module Example
            open Lint
            let a = Byte(1uy)
            let x = System.Math.Abs 1
            let y = System.Math.Max(1, 2)
            let z = System.Math.Min(1, 2)
            """

    let _, _, checkResults = parseAndCheckSecond lib user

    Assert.Empty(
        checkResults.Diagnostics
        |> Array.filter (fun d -> d.Severity = FSharp.Compiler.Diagnostics.FSharpDiagnosticSeverity.Error)
    )

    for s in qualifiedInSecond lib user do
        Assert.Empty s.Edits

[<Fact>]
let ``FR0075: a disposable a local function's task uses after the scope is advice, not a use`` () =
    // the CancellationTokenSource lives on in a returned task's loop, and
    // `use` would dispose it before the loop runs
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let start () =
                let cts = new CancellationTokenSource()
                let loop () = task { do! Task.Delay(1, cts.Token) }
                loop ()
            """

    match useBindingsIn source with
    | [ s ] -> Assert.Equal(None, s.Fix)
    | other -> failwithf "Expected one advisory finding, got %A" other

[<Fact>]
let ``FR0075: a disposable used only inside its own scope's task still gets use`` () =
    let source =
        fsharp
            """
            module Test
            open System.Threading
            open System.Threading.Tasks
            let run () =
                task {
                    let cts = new CancellationTokenSource()
                    do! Task.Delay(1, cts.Token)
                    return 1
                }
            """

    match useBindingsIn source with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a stream wrapper over a caller's stream is not the scope's to dispose`` () =
    // `use resWriter = new BinaryWriter(resStream)` would close the
    // caller's stream at the end of an append
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                let append (resStream: System.IO.Stream) (data: byte[]) =
                    let w = new System.IO.BinaryWriter(resStream)
                    w.Write data
                """
        )
    )

[<Fact>]
let ``FR0075: a reader over a path still gets use`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                let read (path: string) =
                    let r = new System.IO.StreamReader(path)
                    let s = r.ReadToEnd()
                    s.Length
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other


// ---- FR0080 TabIndentation: block comments and strings ----

[<Fact>]
let ``FR0080 a tab inside a literate block comment is prose, not indentation`` () =
    // a literate script keeps a tab-indented shell transcript inside
    // `(** ... *)`; the compiler never sees FS1161 there
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

[<Fact>]
let ``FR0080 a string literal inside a block comment is lexed as the compiler lexes it`` () =
    // the compiler reads `"*)"` inside a comment as a string, so the comment
    // runs on to the real `*)`; the tabbed line between is prose.
    Assert.Empty(tabsIn "(* \"*)\" '\"'\n\tlet tabbed = 1\n*)\nlet v = 1")

    // and the mirror: code after such a comment is code, tabs and all
    match tabsIn "(* \"*)\" *)\nlet f x =\n\tx + 1" with
    | [ s ] -> Assert.Equal(1, s.Edits.Length)
    | other -> failwithf "Expected exactly one tab note, got %A" other


// ---- FR0073 MatchBang: blank lines around the removed let! ----

[<Fact>]
let ``a blank line between the let! and its match goes with the binding`` () =
    // left behind, the blank line would open the block where the `let!`
    // had been
    assertMatchBang
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    let! x = fetch ()

                    match x with
                    | Some v -> return v
                    | None -> return 0
                }
            """)
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    match! fetch () with
                    | Some v -> return v
                    | None -> return 0
                }
            """)

[<Fact>]
let ``a let! between two blank lines leaves a single one`` () =
    // two consecutive blank lines would be left above the match!
    assertMatchBang
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    let y = 1

                    let! x = fetch ()

                    match x with
                    | Some v -> return v + y
                    | None -> return y
                }
            """)
        (fsharp
            """
            module Test
            let fetch () = async { return Some 1 }
            let run () =
                async {
                    let y = 1

                    match! fetch () with
                    | Some v -> return v + y
                    | None -> return y
                }
            """)


[<Fact>]
let ``FR0074: a multi-line inner record keeps one field per line`` () =
    // the flattened fields must not be joined into one overlong line; each
    // field that started a line still does, at the outer field's column
    assertFlattened
        (fsharp
            """
            module Test
            type Inner = { Y: int; Z: int }
            type Outer = { X: Inner; N: int }
            let f (r: Outer) (v: int) =
                { r with
                    X =
                        { r.X with
                            Y = v
                            Z = v + 1 }
                    N = 2 }
            """)
        (fsharp
            """
            X.Y = v
                    X.Z = v + 1
            """)

[<Fact>]
let ``FR0074: fields aligned after the copy source stay aligned`` () =
    assertFlattened
        (fsharp
            """
            module Test
            type Inner = { Y: int; Z: int }
            type Outer = { X: Inner; N: int }
            let f (r: Outer) (v: int) =
                { r with X = { r.X with Y = v
                                        Z = v + 1 } }
            """)
        (fsharp
            """
            X.Y = v
                         X.Z = v + 1
            """)

[<Fact>]
let ``FR0147: uses under one #if get their open under the same condition`` () =
    // a namespace needed only
    // under a condition must not become a dependency of every build
    let source =
        fsharp
            """
            module Test
            open System
            #if !FOO
            let a = System.Text.Encoding.UTF8
            let b = System.Text.Encoding.ASCII
            let c = System.Text.Encoding.Unicode
            #endif
            """

    match qualifiedIn source with
    | [ s ] ->
        let opens = s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open")

        match opens with
        | [ (r, _, text) ] ->
            Assert.Equal(
                fsharp
                    """
                    open System.Text

                    """,
                text
            )

            Assert.Equal(4, r.StartLine)
        | other -> failwithf "Expected one open inside the #if, got %A" other
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: an open under #if is no anchor for unconditional uses`` () =
    let source =
        fsharp
            """
            module Test
            open System
            #if !FOO
            open System.Collections.Generic
            #endif
            let a = System.Text.Encoding.UTF8
            let b = System.Text.Encoding.ASCII
            let c = System.Text.Encoding.Unicode
            """

    match qualifiedIn source with
    | [ s ] ->
        match s.Edits |> List.filter (fun (_, _, r) -> r.StartsWith "open") with
        | [ (r, _, _) ] -> Assert.Equal(3, r.StartLine)
        | other -> failwithf "Expected the open right after `open System`, got %A" other
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``FR0147: an assignment target is a spelling too`` () =
    // `System.Diagnostics.Trace.AutoFlush <- true` must not keep its prefix
    // while the reads beside it lose theirs
    let source =
        fsharp
            """
            module Test
            open System.Diagnostics
            let f () =
                System.Diagnostics.Trace.AutoFlush <- true
                System.Diagnostics.Trace.AutoFlush <- false
                System.Diagnostics.Trace.Flush()
            """

    match qualifiedIn source with
    | [ s ] -> Assert.Equal(3, s.Edits |> List.filter (fun (_, _, r) -> r = "") |> List.length)
    | other -> failwithf "Expected one suggestion with three shortenings, got %A" other

[<Fact>]
let ``FR0147: a name an enclosing namespace provides is not introduced`` () =
    // every file under a namespace sees that namespace's SR module; an
    // open to spell `SR.x` would make SR mean two modules
    let lib =
        fsharp
            """
            namespace Outer
            module SR =
                let x = 1
            namespace Lib2
            module SR =
                let y = 2
            """

    let user =
        fsharp
            """
            namespace Outer.Inner
            module M =
                let a = Lib2.SR.y
                let b = Lib2.SR.y + 1
                let c = Lib2.SR.y + 2
            """

    for s in qualifiedInSecond lib user do
        Assert.Empty s.Edits

// ---- FR0075: ownership transfers through containers, stores, closes and no-op disposables ----

[<Fact>]
let ``FR0075: a disposable returned inside a tuple is the caller's`` () =
    // `(port, cts)` returned after a loop closure captured the cts; a
    // MemoryStream returned in a 5-tuple after it was handed to a writer
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private fill (s: Stream) = s.WriteByte 1uy
                let make (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    fill stream
                    (stream.Length, stream)
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable returned through upcasts inside a tuple is the caller's`` () =
    // `(node :> IDisposable, node :> aset<'B>)`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System
                open System.IO
                let make (path: string) : IDisposable * Stream =
                    let stream = new FileStream(path, FileMode.Open)
                    (stream :> IDisposable, stream :> Stream)
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable stored into a returned record is the caller's`` () =
    // a buffer goes into a mesh record whose Dispose disposes it
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Mesh = { Data: FileStream; Count: int }
                let load (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    stream.ReadByte() |> ignore
                    { Data = stream; Count = 1 }
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable returned from a computation expression in a tuple is the caller's`` () =
    // `return tcGlobals, frameworkTcImports` long after `new TcImports(...)`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private register (s: Stream) = ()
                let load (path: string) =
                    async {
                        let stream = new FileStream(path, FileMode.Open)
                        register stream
                        return 1, stream
                    }
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable rebound under its own name through an upcast and returned is the caller's`` () =
    // `let ilModuleReader = ilModuleReader :> ILModuleReader`
    // before caching and returning it
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private stash (s: Stream) = ()
                let load (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    let stream = stream :> Stream
                    stash stream
                    stream
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable handed on and then returned is the caller's`` () =
    // `ActivitySource.AddActivityListener(l); l` — the return
    // decides the owner whatever else the scope did with the value
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private register (s: Stream) = ()
                let load (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    register stream
                    stream
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable returned from a match arm after a copy is the caller's`` () =
    // `resStream.CopyTo ms; ms.Position <- 0L; ms`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let load (path: string) =
                    use src = File.OpenRead path
                    match src with
                    | null -> failwith "missing"
                    | _ ->
                        let ms = new MemoryStream()
                        src.CopyTo ms
                        ms.Position <- 0L
                        ms
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable returned inside a union case is the caller's`` () =
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let tryOpen (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    stream.ReadByte() |> ignore
                    Some stream
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable stored into a field of the enclosing type belongs to the type`` () =
    // `billboardEffect <- ValueSome e`, `audioServiceOpt <- ValueSome
    // audio` — FR0032/FR0047 judge
    // the type's Dispose; this scope is not the owner
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Holder() =
                    let mutable effect: FileStream voption = ValueNone
                    member _.Load(path: string) =
                        let e = new FileStream(path, FileMode.Open)
                        effect <- ValueSome e
                    member _.Loaded = effect.IsSome
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable stored into a property belongs to the holder`` () =
    // `res.Raster <- sr` on a resources object
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Res() =
                    member val Raster: FileStream = null with get, set
                let ensure (res: Res) (path: string) =
                    if isNull res.Raster then
                        let sr = new FileStream(path, FileMode.Open)
                        res.Raster <- sr
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable stored into a collection belongs to the collection's holder`` () =
    // a socket array filled (`listenSockets.[i] <- s`) and stopped one by
    // one later; a pool adding to an `inUse` list
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let openAll (paths: string[]) =
                    let streams = Array.zeroCreate<FileStream> paths.Length
                    for i in 0 .. paths.Length - 1 do
                        let s = new FileStream(paths.[i], FileMode.Open)
                        streams.[i] <- s
                        s.ReadByte() |> ignore
                    streams
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Pool() =
                    let inUse = ResizeArray<FileStream>()
                    member _.Acquire(path: string) =
                        let s = new FileStream(path, FileMode.Open)
                        inUse.Add s
                        s.ReadByte()
                """
        )
    )

[<Fact>]
let ``FR0075: a disposable stored into a module-level ref cell belongs to the module`` () =
    // `cleanupTimer := Some timer`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private current: FileStream option ref = ref None
                let start (path: string) =
                    match current.Value with
                    | Some _ -> ()
                    | None ->
                        let s = new FileStream(path, FileMode.Open)
                        current := Some s
                """
        )
    )

[<Fact>]
let ``FR0075: a part added to a use-bound multipart content is adopted`` () =
    // `formdata.Add(upload, "file", "pix.gif")`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                open System.Net.Http
                let post (path: string) =
                    use fs = File.OpenRead path
                    use formdata = new MultipartFormDataContent()
                    let upload = new StreamContent(fs)
                    upload.Headers.ContentType <- Headers.MediaTypeHeaderValue("image/gif")
                    formdata.Add(upload, "file", "pix.gif")
                    formdata.Headers.ContentLength
                """
        )
    )

[<Fact>]
let ``FR0075: disposing through an IDisposable upcast is disposal`` () =
    // `(daemon :> IDisposable).Dispose()`
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System
                open System.IO
                let run (path: string) =
                    let stream = new FileStream(path, FileMode.Open)
                    let b = stream.ReadByte()
                    (stream :> IDisposable).Dispose()
                    b
                """
        )
    )

[<Fact>]
let ``FR0075: closing a stream or writer is disposal`` () =
    // `ms.Close()` before `ms.ToArray()`, `stream.Close()` after
    // a closure reopened it
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let copy (src: Stream) =
                    let ms = new MemoryStream()
                    src.CopyTo ms
                    ms.Close()
                    ms.ToArray()
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let write (path: string) =
                    let w = new StreamWriter(path)
                    w.Write "x"
                    w.Close()
                """
        )
    )

[<Fact>]
let ``FR0075: Close on a type where it is not Dispose is no disposal`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                type Conn() =
                    member _.Close() = ()
                    interface System.IDisposable with
                        member _.Dispose() = ()
                let run () =
                    let c = new Conn()
                    c.Close()
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a MemoryStream over a caller's buffer, a StringReader or a StringWriter own no resource`` () =
    // Dispose on these is a no-op, there is nothing to leak
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private dec (s: Stream) = s.ReadByte()
                let decode (buf: byte[]) =
                    let wbuf = new MemoryStream(buf)
                    dec wbuf |> ignore
                    Array.sub buf 0 (int wbuf.Position)
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private enc (s: Stream) = s.WriteByte 1uy
                let encode (raw: byte[]) =
                    let tmp = Array.zeroCreate<byte> (raw.Length * 4 + 8)
                    let tmpBuf = new MemoryStream(tmp, 0, tmp.Length, true, true)
                    enc tmpBuf
                    tmp
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let private emit (w: TextWriter) = w.Write "x"
                let render () =
                    let sb = System.Text.StringBuilder()
                    let writer = new StringWriter(sb)
                    emit writer
                    let reader = new StringReader("")
                    reader.ReadLine() |> ignore
                    sb.ToString()
                """
        )
    )

[<Fact>]
let ``FR0075: a MemoryStream over its own buffer still gets use`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let make () =
                    let ms = new MemoryStream(1024)
                    ms.WriteByte 1uy
                    let n = ms.Length
                    n
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a stream wrapper over a member's stream parameter is not the scope's to dispose`` () =
    // `static member ReadResFile(stream: Stream)` wraps it in a
    // BinaryReader, AppendVersionToResourceStream(resStream, ...) in a
    // BinaryWriter; writeBinaryAux wraps its tupled `stream` parameter
    // inside a tuple-bound nested let
    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                type Res() =
                    static member Read(stream: Stream) =
                        let reader = new BinaryReader(stream, System.Text.Encoding.Unicode)
                        reader.ReadUInt32()
                    static member Append(resStream: Stream, isDll: bool) =
                        let w = new BinaryWriter(resStream, System.Text.Encoding.Unicode)
                        w.Write isDll
                """
        )
    )

    Assert.Empty(
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let writeBinaryAux (stream: Stream, options: int) =
                    let a, b =
                        let os = new BinaryWriter(stream, System.Text.Encoding.UTF8)
                        os.Write options
                        1, 2
                    a + b
                """
        )
    )

[<Fact>]
let ``FR0075: a hash algorithm from its Create factory is locally constructed`` () =
    // `MD5.Create()` and `SHA1.Create()` never disposed
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Security.Cryptography
                let hash (bytes: byte[]) =
                    let sha = SHA1.Create()
                    let h = sha.ComputeHash bytes
                    h
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a construction hidden behind an upcast is still a construction`` () =
    // `new StringWriter(sb) :> TextWriter` (a no-op
    // disposable, but the shape hides every construction)
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let read (path: string) =
                    let stream = new FileStream(path, FileMode.Open) :> Stream
                    let b = stream.ReadByte()
                    b
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

[<Fact>]
let ``FR0075: a plain-valued member call as the scope's result is read before use disposes it`` () =
    // `md5.ComputeHash bytes` is the result — a byte[], computed
    // before the scope exits; only a task, sequence or object still tied to
    // the disposable outlives it
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.Security.Cryptography
                let hash (bytes: byte[]) =
                    let md5 = MD5.Create()
                    md5.ComputeHash bytes
                """
        )
    with
    | [ s ] -> Assert.Equal(Some("let", "use"), s.Fix)
    | other -> failwithf "Expected one use finding, got %A" other

    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let fetch (path: string) =
                    let reader = new StreamReader(path)
                    reader.ReadToEndAsync()
                """
        )
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some UseBinding.Destination.ReadInResult, s.Destination)
        Assert.Contains("the scope's result reads it", UseBinding.describeEscape s)
    | other -> failwithf "Expected one advisory, got %A" other

[<Fact>]
let ``FR0075: a disposable stored into a local mutable is named as such`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let pick (path: string) =
                    let mutable best: FileStream option = None
                    let s = new FileStream(path, FileMode.Open)
                    best <- Some s
                    best.IsSome
                """
        )
    with
    | [ s ] ->
        Assert.Equal(None, s.Fix)
        Assert.Equal(Some(UseBinding.Destination.StoredLocally "best"), s.Destination)
        Assert.Contains("stored in the local 'best'", UseBinding.describeEscape s)
    | other -> failwithf "Expected exactly one advisory, got %A" other

[<Fact>]
let ``FR0075: a disposable captured by a closure says so`` () =
    match
        useBindingsIn (
            fsharp
                """
                module Test
                open System.IO
                let defer (run: (unit -> int) -> unit) (path: string) =
                    let s = new FileStream(path, FileMode.Open)
                    run (fun () -> s.ReadByte())
                """
        )
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
    // the token source is disposed when
    // the starter returns, and the loop reads .Token on every interval
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let start () =
                use cts = new CancellationTokenSource()

                task {
                    do! Task.Delay(1000, cts.Token)
                    return 1
                }
            """

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("cts", s.Name)
        Assert.Equal("task", s.Builder)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                    task {
                        use cts = new CancellationTokenSource()
                        do! Task.Delay
                """,
            patched
        )

        Assert.DoesNotContain(
            fsharp
                """
                    use cts = new CancellationTokenSource()

                    task
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: the computation reached through a binding is seen too`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let start () =
                use cts = new CancellationTokenSource()

                let loop =
                    task {
                        do! Task.Delay(1000, cts.Token)
                        return 1
                    }

                loop
            """

    match escapingUsesIn source with
    | [ s ] -> Assert.Equal("cts", s.Name)
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: a use the computation never reads is fine`` () =
    Assert.Empty(
        escapingUsesIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let start () =
                    use cts = new CancellationTokenSource()
                    ignore cts

                    task {
                        do! Task.Delay 1000
                        return 1
                    }
                """
        )
    )

[<Fact>]
let ``FR0150: a use consumed inside the scope is fine`` () =
    // nothing escapes: the task is awaited before the scope returns
    Assert.Empty(
        escapingUsesIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let start () =
                    task {
                        use cts = new CancellationTokenSource()
                        do! Task.Delay(1000, cts.Token)
                        return 1
                    }
                """
        )
    )

[<Fact>]
let ``FR0150: a statement between the use and the computation that reads it holds the fix back`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let start () =
                use cts = new CancellationTokenSource()
                let token = cts.Token

                task {
                    do! Task.Delay(1000, cts.Token)
                    return 1
                }
            """

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("cts", s.Name)
        Assert.Empty s.Edits
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: unrelated statements between the use and the computation stay outside it`` () =
    // the binding moves in; the greeting it does not touch stays where it was
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let start (name: string) =
                use cts = new CancellationTokenSource()
                let greeting = "hello " + name
                printfn "%s" greeting

                task {
                    do! Task.Delay(1000, cts.Token)
                    return greeting.Length
                }
            """

    match escapingUsesIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                    let greeting = "hello " + name
                    printfn "%s" greeting
                """,
            patched
        )

        Assert.Contains(
            fsharp
                """
                    task {
                        use cts = new CancellationTokenSource()
                        do! Task.Delay
                """,
            patched
        )

        Assert.DoesNotContain(
            fsharp
                """
                    use cts = new CancellationTokenSource()
                    let greeting
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: the fix through a binding keeps the statements before it in place`` () =
    let source =
        fsharp
            """
            open System.Threading
            open System.Threading.Tasks
            let start (n: int) =
                use cts = new CancellationTokenSource()
                let doubled = n * 2
                let label = string doubled

                let loop =
                    task {
                        do! Task.Delay(doubled, cts.Token)
                        return label
                    }

                loop
            """

    match escapingUsesIn source with
    | [ s ] ->
        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        Assert.Contains(
            fsharp
                """
                    let doubled = n * 2
                    let label = string doubled
                """,
            patched
        )

        Assert.Contains(
            fsharp
                """
                        task {
                            use cts = new CancellationTokenSource()
                            do! Task.Delay
                """,
            patched
        )

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: an async computation is the same shape`` () =
    let source =
        fsharp
            """
            open System.Threading
            let start () =
                use cts = new CancellationTokenSource()

                async {
                    do! Async.Sleep 1000
                    return cts.Token.IsCancellationRequested
                }
            """

    match escapingUsesIn source with
    | [ s ] ->
        Assert.Equal("async", s.Builder)

        let patched =
            s.Edits
            |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
            |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected exactly one escaping-use note, got %A" other

[<Fact>]
let ``FR0150: a computation the scope consumes itself is not escaping`` () =
    // the task is drained before the scope returns: the use is correct
    Assert.Empty(
        escapingUsesIn (
            fsharp
                """
                open System.Threading
                open System.Threading.Tasks
                let start () =
                    use cts = new CancellationTokenSource()

                    let t =
                        task {
                            do! Task.Delay(1000, cts.Token)
                            return 1
                        }

                    t.Result
                """
        )
    )

[<Fact>]
let ``FR0092: an assertion pinning a production throw's text loosens to a prefix check`` () =
    // the enrichment APPENDS to the message; `should equal` would go false,
    // `should startWith` stays true to the assertion's intent. Only a literal
    // that is a production throw qualifies: the stub's own message is left
    let source =
        fsharp
            """
            module Tests
            open FsUnit.Xunit
            open Xunit
            let a (ex: exn) = ex.Message |> should equal "model inference failed"
            let b (ex: exn) = Assert.Equal("model inference failed", ex.Message)
            let c (ex: exn) = ex.Message |> should equal "stub failed"
            """

    let _, sourceText = parse source

    let edits =
        FailwithContext.findAssertions sourceText "Tests.fs" [ "\"model inference failed\"" ]
        |> List.map (fun (r, original, replacement) -> r.StartLine, original, replacement)
        |> List.sort

    Assert.Equal<(int * string * string) list>(
        [
            4, "should equal \"model inference failed\"", "should startWith \"model inference failed\""
            5, """Assert.Equal("model inference failed",""", """Assert.StartsWith("model inference failed","""
        ],
        edits
    )

[<Fact>]
let ``FR0092: a mention the loosening cannot rewrite vetoes the enrichment`` () =
    // both halves read this one predicate, so they agree whichever project
    // is analysed first: the production throw is enriched only where every
    // test mention is a form that becomes a prefix check
    let literal = "\"model inference failed\""

    Assert.True(
        FailwithContext.everyMentionRewritable
            (fsharp
                """
                ex.Message |> should equal "model inference failed"
                Assert.Equal("model inference failed", ex.Message)
                """)
            literal
    )

    // NUnit's dialect is not recognised
    Assert.False(
        FailwithContext.everyMentionRewritable """Assert.AreEqual("model inference failed", ex.Message)""" literal
    )

    // a test-side stub throwing the same text is not an assertion at all
    Assert.False(
        FailwithContext.everyMentionRewritable
            (fsharp
                """
                let stub () = failwith "model inference failed"
                ex.Message |> should equal "model inference failed"
                """)
            literal
    )

    // no mention at all is trivially fine
    Assert.True(FailwithContext.everyMentionRewritable "let x = 1" literal)

    // a prefix check an earlier enrichment left behind stays true under the next
    Assert.True(
        FailwithContext.everyMentionRewritable
            (fsharp
                """
                Assert.StartsWith("model inference failed", ex.Message)
                ex.Message |> should startWith "model inference failed"
                """)
            literal
    )

[<Fact>]
let ``FR0092: an assertion on anything but a Message is neither loosened nor covered`` () =
    // `Assert.Equal("Error", s.LogMethod)` spells the text of a `failwith
    // "Error"` in a doc comment; turning it into StartsWith would enrich
    // nothing. A mention about something other than an exception's text is
    // not an assertion the enrichment can keep true - it vetoes instead
    let literal = "\"Error\""

    let source =
        fsharp
            """
            module Tests
            let a (s: Finding) = Assert.Equal("Error", s.LogMethod)
            """

    let _, sourceText = parse source
    Assert.Empty(FailwithContext.findAssertions sourceText "Tests.fs" [ literal ])
    Assert.False(FailwithContext.everyMentionRewritable source literal)

    // the same text on a Message still loosens, with its receiver spelled any way
    let onMessage =
        fsharp
            """
            module Tests
            let a (ex: exn) = Assert.Equal("Error", ex.InnerException.Message)
            let b (ex: exn) = ex.Message |> should equal "Error"
            """

    let _, onMessageText = parse onMessage
    Assert.Equal(2, (FailwithContext.findAssertions onMessageText "Tests.fs" [ literal ]).Length)
    Assert.True(FailwithContext.everyMentionRewritable onMessage literal)

[<Fact>]
let ``FR0147: an F#-style extension in the namespace's AutoOpen module is seen by the tupled-call guard`` () =
    // `open Ext` opens the AutoOpen module with it, and the optional
    // extension there splits `seen.Contains (e, ct)` exactly as a C#-style
    // one does (the identical FS0001)
    let extensions =
        fsharp
            """
            namespace Ext
            [<AutoOpen>]
            module Exts =
                type System.Collections.Generic.List<'T> with
                    member xs.Contains(a: 'T, b: int) = b > 0
            type Helpers =
                static member Sum(xs: int[]) = Array.sum xs
                static member Max(xs: int[]) = Array.max xs
                static member Min(xs: int[]) = Array.min xs
            """

    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let seen = List<string * int>()
            let check (e: string) (ct: int) = if not (seen.Contains (e, ct)) then seen.Add(e, ct)
            let a (xs: int[]) = Ext.Helpers.Sum xs
            let b (xs: int[]) = Ext.Helpers.Max xs
            let c (xs: int[]) = Ext.Helpers.Min xs
            """

    let tree, sourceText, checkResults = parseAndCheckSecond extensions source

    match
        QualifiedNames.find 3 2 tree sourceText checkResults
        |> List.filter (fun s -> s.Namespace = "Ext")
    with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("'Contains'", s.Reason.Value)
    | other -> failwithf "Expected a declined Ext finding, got %A" other

[<Fact>]
let ``FR0147: the tupled-call guard declines one namespace, not the file`` () =
    // System.Linq brings a `Contains` extension beside `seen.Contains (e, ct)`
    // and is declined; System.Threading.Tasks brings none and is opened in
    // the same pass
    let source =
        fsharp
            """
            module Test
            open System.Collections.Generic
            let seen = List<string * int>()
            let check (e: string) (ct: int) = if not (seen.Contains (e, ct)) then seen.Add(e, ct)
            let a (xs: int[]) = System.Linq.Enumerable.Sum xs
            let b (xs: int[]) = System.Linq.Enumerable.Max xs
            let c (xs: int[]) = System.Linq.Enumerable.Min xs
            let d = System.Threading.Tasks.Task.FromResult 1
            let e = System.Threading.Tasks.Task.Delay 10
            let f (t: System.Threading.Tasks.Task<int>) = t.Result
            """

    let found = qualifiedIn source

    match found |> List.filter (fun s -> s.Namespace = "System.Linq") with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("'Contains'", s.Reason.Value)
    | other -> failwithf "Expected a declined System.Linq finding, got %A" other

    match found |> List.filter (fun s -> s.Namespace = "System.Threading.Tasks") with
    | [ s ] ->
        Assert.Equal(None, s.Reason)
        let patched = applyAll source s.Edits
        Assert.Contains("open System.Threading.Tasks", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected an offered System.Threading.Tasks finding, got %A" other
