/// Text.directiveRegionsOf and the two gates over it: the `#if` regions of
/// a file come from the parser's trivia, not from a regex over lines.
module FSharp.Refactor.Tests.DirectiveRegionTests

open System
open System.IO
open Xunit
open FSharp.Refactor

let private withFile (source: string) (test: string -> unit) =
    let path =
        Path.Combine(Path.GetTempPath(), "fsref-directive-" + Guid.NewGuid().ToString "N" + ".fs")

    File.WriteAllText(path, source)

    try
        test path
    finally
        File.Delete path

[<Fact>]
let ``a DEBUG region is read with its lines and its name`` () =
    withFile
        (fsharp
            """
            module M
            #if DEBUG
            let f x = x
            #else
            let f x = x + 1
            #endif
            let g = f 1
            """)
        (fun path ->
            match Text.directiveRegionsOf path with
            | Some [ r ] ->
                Assert.Equal(2, r.StartLine)
                Assert.Equal(6, r.EndLine)
                Assert.Equal<string list>([ "DEBUG" ], r.Names)
            | other -> failwithf "Expected one region, got %A" other

            Assert.True(Text.hasConfigurationConditional path))

[<Fact>]
let ``a condition names everything it tests`` () =
    withFile
        (fsharp
            """
            module M
            #if !DEBUG && NET8_0 || TRACE
            let f x = x
            #endif
            """)
        (fun path ->
            match Text.directiveRegionsOf path with
            | Some [ r ] -> Assert.Equal<string list>([ "DEBUG"; "NET8_0"; "TRACE" ], r.Names)
            | other -> failwithf "Expected one region, got %A" other)

[<Fact>]
let ``a framework region is no configuration conditional`` () =
    withFile
        (fsharp
            """
            module M
            #if NET8_0
            let f x = x
            #else
            let f x = x + 1
            #endif
            """)
        (fun path ->
            Assert.False(Text.hasConfigurationConditional path)
            Assert.False(Text.namedInDirectiveRegion [ path ] "f"))

[<Fact>]
let ``a directive quoted in a comment or a string is text`` () =
    // a regex over lines would read both as `#if DEBUG`
    withFile "module M\n(*\n#if DEBUG\n*)\nlet s = \"\"\"\n#if DEBUG\n\"\"\"\nlet f x = x" (fun path ->
        Assert.Equal(Some [], Text.directiveRegionsOf path)
        Assert.False(Text.hasConfigurationConditional path))

[<Fact>]
let ``nested regions each get their own entry`` () =
    withFile
        (fsharp
            """
            module M
            #if NET8_0
            #if DEBUG
            let f x = x
            #endif
            #endif
            """)
        (fun path ->
            match Text.directiveRegionsOf path with
            | Some [ inner; outer ] ->
                Assert.Equal((3, 5), (inner.StartLine, inner.EndLine))
                Assert.Equal((2, 6), (outer.StartLine, outer.EndLine))
            | other -> failwithf "Expected two regions, got %A" other

            Assert.True(Text.namedInDirectiveRegion [ path ] "f"))

[<Fact>]
let ``a name inside a configuration region is found, one outside is not`` () =
    withFile
        (fsharp
            """
            module M
            let g = 1
            #if DEBUG
            let h = g + f 1
            #endif
            let k = f 2
            """)
        (fun path ->
            Assert.True(Text.namedInDirectiveRegion [ path ] "f")
            Assert.True(Text.namedInDirectiveRegion [ path ] "g")
            Assert.False(Text.namedInDirectiveRegion [ path ] "k")
            // a word, not a substring
            Assert.False(Text.namedInDirectiveRegion [ path ] "ff"))

[<Fact>]
let ``an unreadable file is taken to branch`` () =
    let path =
        Path.Combine(Path.GetTempPath(), "fsref-directive-missing-" + Guid.NewGuid().ToString "N" + ".fs")

    Assert.Equal(None, Text.directiveRegionsOf path)
    Assert.True(Text.hasConfigurationConditional path)
    Assert.True(Text.namedInDirectiveRegion [ path ] "f")

[<Fact>]
let ``a rewritten file is read again`` () =
    withFile
        (fsharp
            """
            module M
            let f x = x
            """)
        (fun path ->
            Assert.False(Text.hasConfigurationConditional path)

            File.WriteAllText(
                path,
                fsharp
                    """
                    module M
                    #if DEBUG
                    let f x = x
                    #endif
                    """
            )

            File.SetLastWriteTimeUtc(path, DateTime.UtcNow.AddSeconds 5.0)
            Assert.True(Text.hasConfigurationConditional path))
