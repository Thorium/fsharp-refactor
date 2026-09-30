/// `--define` and the config's `"defines"`: preprocessor symbols a run
/// defines for every build and script check. Parsing, the environment
/// value MSBuild gets, the hint for a script whose `#r` of the project sits
/// under an undefined `#if`, and one end-to-end run that finds code only a
/// defined symbol compiles. In the "ProjectSources" collection: the run's
/// symbols are process-wide (RunDefines), as are `main`'s per-run stores.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.DefinesTests

open System
open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tool

/// Run `test` with the run's symbols set to `symbols`, restoring none after.
let private withDefinesResult (symbols: string list) (test: unit -> 'T) : 'T =
    Program.RunDefines.set symbols

    try
        test ()
    finally
        Program.RunDefines.set []

let private withDefines (symbols: string list) (test: unit -> unit) = withDefinesResult symbols test

// ---- parsing ----

[<Fact>]
let ``a define value is one symbol or a separated list of them`` () =
    Assert.Equal(Ok [ "LOCAL_BUILD" ], Program.RunDefines.parse "LOCAL_BUILD")
    Assert.Equal(Ok [ "A"; "B"; "C" ], Program.RunDefines.parse "A;B, C")
    Assert.Equal(Ok [ "_under"; "x1" ], Program.RunDefines.parse "_under;;x1;")

[<Fact>]
let ``a define value that is not a symbol is an error naming it`` () =
    for bad in [ "1ABC"; "A-B"; "A B"; "$(Foo)" ] do
        match Program.RunDefines.parse bad with
        | Ok symbols -> Assert.Fail $"'{bad}' parsed as %A{symbols}"
        | Error message -> Assert.Contains("not a preprocessor symbol", message)

    Assert.True(Result.isError (Program.RunDefines.parse ";"))

[<Fact>]
let ``the config's defines are an array or one separated string, and not a rule`` () =
    Assert.Equal<string list>(
        [ "LOCAL_BUILD"; "EXTRA" ],
        Configuration.parseDefines """{ "defines": [ "LOCAL_BUILD", "EXTRA" ] }"""
    )

    Assert.Equal<string list>([ "A"; "B" ], Configuration.parseDefines """{ "defines": "A;B" }""")
    // anything that is not a symbol is dropped, not passed to the compiler
    Assert.Equal<string list>([ "OK" ], Configuration.parseDefines """{ "defines": [ "OK", "no good", 3 ] }""")
    Assert.Empty(Configuration.parseDefines """{ "apiChanges": true }""")
    Assert.Empty(Configuration.parseDefines "not json")
    // a reserved key: never read as a rule switch
    Assert.False((Configuration.parse """{ "defines": [ "X" ] }""").ContainsKey "defines")

// ---- the environment value a child MSBuild gets ----

[<Fact>]
let ``defines reach MSBuild appended to whatever DefineConstants the environment carries`` () =
    Assert.Equal(None, Program.RunDefines.environmentValue "")

    withDefines [ "LOCAL_BUILD"; "EXTRA" ] (fun () ->
        Assert.Equal(Some "LOCAL_BUILD;EXTRA", Program.RunDefines.environmentValue "")
        Assert.Equal(Some "FROM_ENV;LOCAL_BUILD;EXTRA", Program.RunDefines.environmentValue "FROM_ENV;")
        Assert.Equal<string[]>([| "--define:LOCAL_BUILD"; "--define:EXTRA" |], Program.RunDefines.flags ()))

// ---- the hint for a #r under an undefined #if ----

let private dualScript =
    [
        "#if LOCAL_BUILD"
        "#r \"../src/Lib/bin/Debug/net10.0/Lib.dll\""
        "#else"
        "#r \"nuget: Lib\""
        "#endif"
        "#if !INTERACTIVE && OTHER"
        "#r \"Lib.dll\""
        "#endif"
    ]

let private isLibReference (line: string) =
    line.TrimStart().StartsWith "#r" && line.Contains "Lib.dll"

[<Fact>]
let ``a reference under an undefined if names the symbols that would switch it on`` () =
    Assert.Equal<string list>([ "LOCAL_BUILD"; "OTHER" ], Program.undefinedGuardsOf dualScript isLibReference)

    // defined, it guards nothing; a negated symbol never counts, nor does an #else half
    withDefines [ "LOCAL_BUILD" ] (fun () ->
        Assert.Equal<string list>([ "OTHER" ], Program.undefinedGuardsOf dualScript isLibReference))

    let nugetOnly (line: string) = line.Contains "nuget:"
    Assert.Empty(Program.undefinedGuardsOf dualScript nugetOnly)

[<Fact>]
let ``a line is live only where the compiler reads it: elif, else, negation, nesting`` () =
    let script =
        [
            "#if A"
            "a"
            "#elif B"
            "b"
            "#else"
            "c"
            "#endif"
            "#if !A && (B || C)"
            "d"
            "#if INTERACTIVE"
            "e"
            "#endif"
            "#endif"
            "f"
        ]

    let contentLive (symbols: string list) =
        withDefinesResult symbols (fun () ->
            Seq.zip script (Program.directiveScopes script)
            |> Seq.filter (fun (line, _) -> line.Length = 1)
            |> Seq.map (fun (_, (live, _)) -> live)
            |> List.ofSeq)

    // fsi defines INTERACTIVE; nothing else: the else branch and f
    Assert.Equal<bool list>([ false; false; true; false; false; true ], contentLive [])
    // B: the elif, and d with its nested e
    Assert.Equal<bool list>([ false; true; false; true; true; true ], contentLive [ "B" ])
    // A: the if only; !A closes d and e
    Assert.Equal<bool list>([ true; false; false; false; false; true ], contentLive [ "A" ])

    // what would switch a closed line on: only positive symbols on the way to it
    let target (line: string) = line = "d" || line = "e"
    Assert.Equal<string list>([ "B"; "C" ], Program.undefinedGuardsOf script target)

// ---- end to end ----

let private framework = $"net{Environment.Version.Major}.0"

let private runTool (args: string[]) =
    use captured = new StringWriter()
    let oldOut = Console.Out
    let oldErr = Console.Error
    Console.SetOut captured
    Console.SetError captured

    let code =
        try
            Program.main args
        finally
            Console.SetOut oldOut
            Console.SetError oldErr

    code, captured.ToString()

[<Fact>]
let ``code under a defined symbol is fixed, and the project keeps its own defines`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-defines-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory root |> ignore

    try
        let project = Path.Combine(root, "Lib.fsproj")

        File.WriteAllText(
            project,
            $"""<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup>
    <TargetFramework>{framework}</TargetFramework>
    <DefineConstants>$(DefineConstants);OWN_SYMBOL</DefineConstants>
  </PropertyGroup>
  <ItemGroup><Compile Include="Lib.fs" /></ItemGroup>
</Project>
"""
        )

        // `seen` exists only when TRACE (the SDK's, in every configuration) and
        // OWN_SYMBOL (the project's) are both defined: a
        // run that replaced the project's DefineConstants instead of adding
        // to them would not compile the LOCAL_BUILD half at all
        let source =
            String.Join(
                "\n",
                [
                    "module Lib"
                    ""
                    "#if TRACE && OWN_SYMBOL"
                    "let seen = 1"
                    "#endif"
                    ""
                    "#if LOCAL_BUILD"
                    "let check (x: int) ="
                    "    if x < seen then raise (System.Exception \"too small\")"
                    "    x"
                    "#endif"
                    ""
                ]
            )

        let libFile = Path.Combine(root, "Lib.fs")
        File.WriteAllText(libFile, source)

        // without the symbol the LOCAL_BUILD half is not in the parse tree
        let _, withoutOutput = runTool [| project; "--codes"; "FR0024"; "--no-color" |]
        Assert.Equal(source, File.ReadAllText libFile)
        Assert.DoesNotContain("defining LOCAL_BUILD", withoutOutput)

        let code, output =
            runTool [| project; "--codes"; "FR0024"; "--no-color"; "--define"; "LOCAL_BUILD" |]

        let fixedSource = File.ReadAllText libFile
        Assert.True((code = 0), output)
        Assert.Contains("defining LOCAL_BUILD (--define)", output)
        Assert.Contains("failwith \"too small\"", fixedSource)
        Assert.DoesNotContain("raise", fixedSource)
    finally
        Program.RunDefines.set []

        try
            Directory.Delete(root, true)
        with _ ->
            ()
