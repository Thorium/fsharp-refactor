module FSharp.Refactor.Tests.ConfigurationTests

open System
open System.IO
open Xunit
open FSharp.Refactor

[<Fact>]
let ``rules default to enabled`` () =
    let rules = Configuration.parse "{}"
    Assert.True(Configuration.isEnabledIn rules "FR0001" "MatchToIf")

[<Fact>]
let ``rule disabled by code`` () =
    let rules = Configuration.parse """{ "rules": { "FR0001": false } }"""
    Assert.False(Configuration.isEnabledIn rules "FR0001" "MatchToIf")
    Assert.True(Configuration.isEnabledIn rules "FR0004" "ConversionMove")

[<Fact>]
let ``rule disabled by analyzer name case-insensitively`` () =
    let rules = Configuration.parse """{ "rules": { "conversionMove": false } }"""
    Assert.False(Configuration.isEnabledIn rules "FR0004" "ConversionMove")

[<Fact>]
let ``fsharplint-style enabled object is understood`` () =
    let rules =
        Configuration.parse """{ "rules": { "FR0005": { "enabled": false }, "FR0006": { "enabled": true } } }"""

    Assert.False(Configuration.isEnabledIn rules "FR0005" "CeStrip")
    Assert.True(Configuration.isEnabledIn rules "FR0006" "ActivePattern")

[<Fact>]
let ``rule keys may sit at the root without a rules wrapper`` () =
    let rules = Configuration.parse """{ "FR0007": false }"""
    Assert.False(Configuration.isEnabledIn rules "FR0007" "MutableRemoval")

[<Fact>]
let ``explicit code entry wins over a name entry`` () =
    let rules =
        Configuration.parse """{ "rules": { "FR0001": true, "matchToIf": false } }"""

    Assert.True(Configuration.isEnabledIn rules "FR0001" "MatchToIf")

[<Fact>]
let ``comments and trailing commas are tolerated`` () =
    let rules =
        Configuration.parse
            """{
  // disable the composition hint
  "rules": { "FR0003": false, }
}"""

    Assert.False(Configuration.isEnabledIn rules "FR0003" "Composition")

[<Fact>]
let ``malformed json fails open`` () =
    let rules = Configuration.parse "{ not json at all"
    Assert.True(Configuration.isEnabledIn rules "FR0001" "MatchToIf")

[<Fact>]
let ``unknown keys and non-boolean values are ignored`` () =
    let rules =
        Configuration.parse """{ "ignoreFiles": ["x"], "rules": { "FR0004": "nope", "FR0003": false } }"""

    Assert.True(Configuration.isEnabledIn rules "FR0004" "ConversionMove")
    Assert.False(Configuration.isEnabledIn rules "FR0003" "Composition")

[<Fact>]
let ``config file is discovered upward from the analyzed file`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-cfg-" + Guid.NewGuid().ToString "N")

    let nested = Path.Combine(root, "src", "deep")
    Directory.CreateDirectory nested |> ignore

    try
        File.WriteAllText(Path.Combine(root, Configuration.ConfigFileName), """{ "rules": { "FR0001": false } }""")

        let analyzed = Path.Combine(nested, "Code.fs")
        Assert.False(Configuration.isRuleEnabled analyzed "FR0001" "MatchToIf")
        Assert.True(Configuration.isRuleEnabled analyzed "FR0004" "ConversionMove")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``nearest config wins`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-cfg-" + Guid.NewGuid().ToString "N")

    let nested = Path.Combine(root, "sub")
    Directory.CreateDirectory nested |> ignore

    try
        File.WriteAllText(Path.Combine(root, Configuration.ConfigFileName), """{ "rules": { "FR0001": false } }""")
        File.WriteAllText(Path.Combine(nested, Configuration.ConfigFileName), """{ "rules": { "FR0004": false } }""")

        let analyzed = Path.Combine(nested, "Code.fs")
        // the nested config is the effective one; the outer one is not merged
        Assert.False(Configuration.isRuleEnabled analyzed "FR0004" "ConversionMove")
        Assert.True(Configuration.isRuleEnabled analyzed "FR0001" "MatchToIf")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``no config file means everything enabled`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-cfg-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory root |> ignore

    try
        let analyzed = Path.Combine(root, "Code.fs")
        Assert.True(Configuration.isRuleEnabled analyzed "FR0001" "MatchToIf")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``FR0099 is off by default`` () =
    // it lexes every file containing a line-ending semicolon and rarely
    // finds anything — cost out of proportion to a cosmetic default
    let rules = Configuration.parse "{}"
    Assert.False(Configuration.isEnabledIn rules "FR0099" "TrailingSemicolon")

[<Fact>]
let ``the configuration can turn FR0099 back on`` () =
    let rules = Configuration.parse """{ "rules": { "FR0099": true } }"""
    Assert.True(Configuration.isEnabledIn rules "FR0099" "TrailingSemicolon")

[<Fact>]
let ``an explicit --codes ask outranks the default-off status`` () =
    Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", "FR0002,FR0099")

    try
        Assert.True(Configuration.isRuleEnabled "Test.fs" "FR0099" "TrailingSemicolon")
    finally
        Environment.SetEnvironmentVariable("FSREF_FORCE_CODES", null)

    Assert.False(Configuration.isRuleEnabled "Test.fs" "FR0099" "TrailingSemicolon")

[<Fact>]
let ``FR0002 is off by default`` () =
    // the one measured rewrite that slows the rewritten code: +53% and a
    // closure per call on its benchmark pair — opt-in, not a default
    let rules = Configuration.parse "{}"
    Assert.False(Configuration.isEnabledIn rules "FR0002" "OptionModule")

[<Fact>]
let ``the configuration can turn FR0002 back on`` () =
    let rules = Configuration.parse """{ "rules": { "FR0002": true } }"""
    Assert.True(Configuration.isEnabledIn rules "FR0002" "OptionModule")

[<Fact>]
let ``paket-files is ignored by default`` () =
    // vendored/generated code a compilation nonetheless includes: fixing
    // it is churn, sweeping it repeatedly is where multi-project runs die
    Assert.True(Configuration.isIgnoredPath @"C:\repo\paket-files\owner\lib\File.fs")
    Assert.True(Configuration.isIgnoredPath "/repo/paket-files/owner/lib/File.fs")
    Assert.False(Configuration.isIgnoredPath @"C:\repo\src\File.fs")

[<Fact>]
let ``a name containing an ignored segment is not itself ignored`` () =
    // segment match, not substring: my-paket-files-tool.fs is real code
    Assert.False(Configuration.isIgnoredPath @"C:\repo\src\my-paket-files-tool.fs")

[<Fact>]
let ``ignored paths silence every rule`` () =
    Assert.False(Configuration.isRuleEnabled @"C:\repo\paket-files\ext\Code.fs" "FR0001" "MatchToIf")

[<Fact>]
let ``config ignorePaths are additive`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-ign-" + Guid.NewGuid().ToString "N")

    let gen = Path.Combine(root, "generated")
    Directory.CreateDirectory gen |> ignore

    try
        File.WriteAllText(Path.Combine(root, Configuration.ConfigFileName), """{ "ignorePaths": ["generated"] }""")

        Assert.False(Configuration.isRuleEnabled (Path.Combine(gen, "Code.fs")) "FR0001" "MatchToIf")
        Assert.True(Configuration.isRuleEnabled (Path.Combine(root, "Code.fs")) "FR0001" "MatchToIf")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``glob ignorePaths match within and across segments`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-glob-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory(Path.Combine(root, "src", "gen")) |> ignore

    try
        File.WriteAllText(
            Path.Combine(root, Configuration.ConfigFileName),
            """{ "ignorePaths": ["*.g.fs", "src/gen/**"] }"""
        )

        // * stays within one segment...
        Assert.True(Configuration.isIgnoredPath (Path.Combine(root, "Types.g.fs")))
        Assert.False(Configuration.isIgnoredPath (Path.Combine(root, "Types.fs")))
        // ...and ** crosses them
        Assert.True(Configuration.isIgnoredPath (Path.Combine(root, "src", "gen", "deep", "Code.fs")))
        Assert.False(Configuration.isIgnoredPath (Path.Combine(root, "src", "Code.fs")))
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``an auto-generated header disables every rule`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-auto-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory root |> ignore

    try
        let generated = Path.Combine(root, "Output.fs")
        File.WriteAllText(generated, "// <auto-generated>\nmodule Output\nlet x = 1\n")
        let handWritten = Path.Combine(root, "Code.fs")
        File.WriteAllText(handWritten, "module Code\nlet x = 1\n")

        Assert.False(Configuration.isRuleEnabled generated "FR0001" "MatchToIf")
        Assert.True(Configuration.isRuleEnabled handWritten "FR0001" "MatchToIf")
        // a path that does not exist is not generated — it fails open
        Assert.True(Configuration.isRuleEnabled (Path.Combine(root, "Missing.fs")) "FR0001" "MatchToIf")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``rule parameters read from object-valued entries`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-param-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory root |> ignore

    try
        File.WriteAllText(
            Path.Combine(root, Configuration.ConfigFileName),
            """{ "FR0114": { "enabled": true, "thenAtLeast": 30 } }"""
        )

        let file = Path.Combine(root, "Code.fs")
        Assert.Equal(30, Configuration.parameterInt file "FR0114" "PyramidFlip" "thenAtLeast" 20)
        // an unset knob falls back to the rule's default
        Assert.Equal(3, Configuration.parameterInt file "FR0114" "PyramidFlip" "elseAtMost" 3)
        // and the object-valued entry still toggles the rule on
        Assert.True(Configuration.isRuleEnabled file "FR0114" "PyramidFlip")
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``suppressions policy parses and defaults to all`` () =
    Assert.Equal("all", Configuration.parseSuppressions "{}")
    Assert.Equal("no-correctness", Configuration.parseSuppressions """{ "suppressions": "no-correctness" }""")
    Assert.Equal("none", Configuration.parseSuppressions """{ "suppressions": "NONE" }""")
    // a typo cannot silently harden a run
    Assert.Equal("all", Configuration.parseSuppressions """{ "suppressions": "strict" }""")
    Assert.Equal("all", Configuration.parseSuppressions "{ not json")

[<Fact>]
let ``suppressions policy is discovered like any other setting`` () =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-sup-" + Guid.NewGuid().ToString "N")

    Directory.CreateDirectory root |> ignore

    try
        File.WriteAllText(Path.Combine(root, Configuration.ConfigFileName), """{ "suppressions": "no-correctness" }""")

        Assert.Equal("no-correctness", Configuration.suppressionPolicy (Path.Combine(root, "Code.fs")))
        Assert.Equal("all", Configuration.suppressionPolicy (Path.Combine(Path.GetTempPath(), "nowhere.fs")))
    finally
        Directory.Delete(root, true)

[<Fact>]
let ``a FAKE-generated AssemblyInfo header is recognised`` () =
    // SQLProvider's AssemblyInfo.fs opens "// Auto-Generated by FAKE; do
    // not edit" — no XML marker, so the old sniff missed it and the sweep
    // edited a file FAKE rewrites on every build
    let path =
        Path.Combine(Path.GetTempPath(), $"fsref-gen-{Path.GetRandomFileName()}.fs")

    File.WriteAllText(path, "// Auto-Generated by FAKE; do not edit\nnamespace System\nopen System.Reflection\n")

    try
        Assert.True(Configuration.isGeneratedFile path)
    finally
        File.Delete path

[<Fact>]
let ``a GeneratedCode attribute is recognised`` () =
    let path =
        Path.Combine(Path.GetTempPath(), $"fsref-gen-{Path.GetRandomFileName()}.fs")

    File.WriteAllText(
        path,
        "module Generated\n\nopen System.CodeDom.Compiler\n\n[<GeneratedCode(\"protoc\", \"3.0\")>]\ntype T() = class end\n"
    )

    try
        Assert.True(Configuration.isGeneratedFile path)
    finally
        File.Delete path

[<Fact>]
let ``an fslex line directive marks the file generated`` () =
    // fslex and fsyacc output carries no banner, only `# 3 "lex.fsl"`
    // directives pointing back at the grammar
    let path =
        Path.Combine(Path.GetTempPath(), $"fsref-gen-{Path.GetRandomFileName()}.fs")

    File.WriteAllText(
        path,
        "module internal Lexer\n\nopen System\n# 3 \"..\\..\\src\\Compiler\\lex.fsl\"\nlet token (lexbuf: int) = lexbuf\n"
    )

    try
        Assert.True(Configuration.isGeneratedFile path)
    finally
        File.Delete path

[<Fact>]
let ``ordinary source is not mistaken for generated`` () =
    let path =
        Path.Combine(Path.GetTempPath(), $"fsref-gen-{Path.GetRandomFileName()}.fs")

    File.WriteAllText(path, "module Test\n\nlet f (x: int) = x + 1\n")

    try
        Assert.False(Configuration.isGeneratedFile path)
    finally
        File.Delete path
