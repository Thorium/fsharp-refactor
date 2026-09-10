module FSharp.Refactor.Tests.ScriptReferencesTests

open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0144 ScriptReferences ----

/// A packages directory on disk with the given `lib/<tfm>` folders each
/// holding Sql.dll, and a script beside it with one directive line.
let private withPackage
    (folders: string list)
    (directive: string)
    (sdkMajor: int option)
    (test: ScriptReferences.Suggestion list -> unit)
    =
    let root =
        Path.Combine(Path.GetTempPath(), "fsharp-refactor-scriptrefs-" + Path.GetRandomFileName())

    let scripts = Path.Combine(root, "scripts")
    Directory.CreateDirectory scripts |> ignore

    try
        for folder in folders do
            let dir = Path.Combine(root, folder.Replace('/', Path.DirectorySeparatorChar))
            Directory.CreateDirectory dir |> ignore
            File.WriteAllText(Path.Combine(dir, "Sql.dll"), "")

        let script = Path.Combine(scripts, "Run.fsx")
        let text = directive + "\nprintfn \"hi\"\n"
        File.WriteAllText(script, text)
        let tree, sourceText = parseNamed script text

        let options =
            match sdkMajor with
            | Some major ->
                [ $"-r:C:\\dotnet\\packs\\Microsoft.NETCore.App.Ref\\{major}.0.0\\ref\\net{major}.0\\System.Runtime.dll" ]
            | None -> []

        test (ScriptReferences.find script tree sourceText options)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

let private single (suggestions: ScriptReferences.Suggestion list) =
    match suggestions with
    | [ s ] -> s
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a net45 reference moves to the newest net4y the package has`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/net461"
          "packages/Sql.1.2.3/lib/net451"
          "packages/Sql.1.2.3/lib/netstandard2.0" ]
        "#r @\"../packages/Sql.1.2.3/lib/net45/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("@\"../packages/Sql.1.2.3/lib/net461/Sql.dll\"", s.ReplacementText)
            Assert.Contains("also present: net451, netstandard2.0", s.Message))

[<Fact>]
let ``a net45 reference prefers netstandard2.0 over 2.1 when no net4y is left`` () =
    // the .NET Framework loads netstandard2.0, never 2.1
    withPackage
        [ "packages/Sql.1.2.3/lib/netstandard2.1"
          "packages/Sql.1.2.3/lib/netstandard2.0" ]
        "#r \"../packages/Sql.1.2.3/lib/net45/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("\"../packages/Sql.1.2.3/lib/netstandard2.0/Sql.dll\"", s.ReplacementText)
            Assert.DoesNotContain("netstandard2.1", s.Message))

[<Fact>]
let ``a netstandard reference prefers the newest netX not above the SDK`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/net10.0"
          "packages/Sql.1.2.3/lib/net8.0"
          "packages/Sql.1.2.3/lib/netstandard2.0" ]
        "#r @\"../packages/Sql.1.2.3/lib/netstandard1.6/Sql.dll\""
        (Some 8)
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("@\"../packages/Sql.1.2.3/lib/net8.0/Sql.dll\"", s.ReplacementText))

[<Fact>]
let ``an include directory is re-pointed too`` () =
    withPackage [ "packages/Sql.1.2.3/lib/net48" ] "#I @\"../packages/Sql.1.2.3/lib/net481\"" None (fun suggestions ->
        let s = single suggestions
        Assert.Equal("@\"../packages/Sql.1.2.3/lib/net48\"", s.ReplacementText))

[<Fact>]
let ``a version folder moves to the newest sibling version`` () =
    withPackage
        [ "packages/Sql.1.3.0/lib/net48"; "packages/Sql.1.2.9/lib/net48" ]
        "#r @\"..\\packages\\Sql.1.2.3\\lib\\net48\\Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("@\"..\\packages\\Sql.1.3.0\\lib\\net48\\Sql.dll\"", s.ReplacementText))

[<Fact>]
let ``an existing path and a package reference are left alone`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/net48" ]
        "#r @\"../packages/Sql.1.2.3/lib/net48/Sql.dll\"\n#r \"nuget: Sql, 1.2.3\""
        None
        Assert.Empty

[<Fact>]
let ``netcoreapp is the last resort, behind any netstandard`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/netcoreapp3.1"
          "packages/Sql.1.2.3/lib/netstandard2.0" ]
        "#r @\"../packages/Sql.1.2.3/lib/netstandard1.6/Sql.dll\""
        (Some 8)
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("@\"../packages/Sql.1.2.3/lib/netstandard2.0/Sql.dll\"", s.ReplacementText)
            Assert.Contains("also present: netcoreapp3.1", s.Message))

[<Fact>]
let ``a folder whose name contains the segment is not the one rewritten`` () =
    // `Foo.net45/lib/net45`: only the framework folder moves
    withPackage
        [ "packages/Foo.net45/lib/net461" ]
        "#r @\"../packages/Foo.net45/lib/net45/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.Equal("@\"../packages/Foo.net45/lib/net461/Sql.dll\"", s.ReplacementText))

[<Fact>]
let ``a rooted path is walked from its root`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsharp-refactor-scriptrefs-rooted-" + Path.GetRandomFileName())

    let lib = Path.Combine(root, "packages", "Sql.1.2.3", "lib", "net461")
    Directory.CreateDirectory lib |> ignore
    Directory.CreateDirectory(Path.Combine(root, "scripts")) |> ignore

    try
        File.WriteAllText(Path.Combine(lib, "Sql.dll"), "")
        let script = Path.Combine(root, "scripts", "Run.fsx")
        let stale = Path.Combine(root, "packages", "Sql.1.2.3", "lib", "net45", "Sql.dll")
        let text = $"#r @\"{stale}\"\nprintfn \"hi\"\n"
        File.WriteAllText(script, text)
        let tree, sourceText = parseNamed script text

        match ScriptReferences.find script tree sourceText [] with
        | [ s ] ->
            let expected =
                Path.Combine(root, "packages", "Sql.1.2.3", "lib", "net461", "Sql.dll")

            Assert.Equal($"@\"{expected}\"", s.ReplacementText)
        | other -> failwithf "Expected one suggestion, got %A" other
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``a package that is not on disk at all becomes a package reference`` () =
    // paket's `storage: none` keeps the package in the nuget cache and writes
    // no `packages/` copy, so no sibling folder can be re-pointed to
    withPackage
        [ "packages/Other.9.9.9/lib/net48" ]
        "#r @\"../packages/Sql.1.2.3/lib/netstandard2.0/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.True(s.IsNugetReference, "the package is absent, so the fix is a package reference")
            Assert.Equal("\"nuget: Sql, 1.2.3\"", s.ReplacementText))

[<Fact>]
let ``a version-less package folder gives a package reference without one`` () =
    // paket's layout is `packages/Sql/lib/...` - the path carries no version,
    // and no lock file is opened to find one
    withPackage
        [ "packages/Other/lib/net48" ]
        "#r @\"../packages/Sql/lib/netstandard2.0/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.True(s.IsNugetReference, "expected a package reference")
            Assert.Equal("\"nuget: Sql\"", s.ReplacementText))

[<Fact>]
let ``a re-pointable reference stays a path, never a package reference`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/net461" ]
        "#r @\"../packages/Sql.1.2.3/lib/net45/Sql.dll\""
        None
        (fun suggestions ->
            let s = single suggestions
            Assert.False(s.IsNugetReference, "a sibling exists, so the path is re-pointed instead")
            Assert.Equal("@\"../packages/Sql.1.2.3/lib/net461/Sql.dll\"", s.ReplacementText))

[<Fact>]
let ``an #I search directory gets no package reference`` () =
    // a package reference is not a search path, so there is nothing to offer
    withPackage [ "packages/Other/lib/net48" ] "#I @\"../packages/Sql/lib/net451\"" None (fun suggestions ->
        Assert.Empty suggestions)

[<Fact>]
let ``a reference that resolves is left alone`` () =
    withPackage
        [ "packages/Sql.1.2.3/lib/net451" ]
        "#r @\"../packages/Sql.1.2.3/lib/net451/Sql.dll\""
        None
        (fun suggestions -> Assert.Empty suggestions)

[<Fact>]
let ``a net4x asset gets no package reference`` () =
    // a net451 asset says the script runs on the .NET Framework's fsi.exe,
    // which cannot resolve `#r "nuget: ..."` at all
    withPackage [ "packages/Other/lib/net48" ] "#r @\"../packages/Sql/lib/net451/Sql.dll\"" None (fun suggestions ->
        Assert.Empty suggestions)

[<Fact>]
let ``a package that IS on disk gets no package reference, whatever else is wrong`` () =
    // only the file name is misspelled here. The package is present, so a
    // local path is still the better reference - it can be pointed at a debug
    // build, where a package reference downloads to a cache and cannot
    withPackage
        [ "packages/Sql.1.2.3/lib/netstandard2.0" ]
        "#r @\"../packages/Sql.1.2.3/lib/netstandard2.0/Sqll.dll\""
        None
        (fun suggestions -> Assert.Empty suggestions)
