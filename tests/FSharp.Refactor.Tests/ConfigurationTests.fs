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

// ---- publicApi / apiChanges: the two halves of --api-changes ----

[<Fact>]
let ``publicApi is unset by default, and unset is the conservative reading`` () =
    Assert.Equal<bool option>(None, Configuration.parsePublicApi "{}")
    Assert.False(Configuration.parseApiChanges "{}")

[<Fact>]
let ``publicApi false says the assembly is a leaf`` () =
    Assert.Equal<bool option>(Some false, Configuration.parsePublicApi """{ "publicApi": false }""")
    Assert.Equal<bool option>(Some true, Configuration.parsePublicApi """{ "publicApi": true }""")

[<Fact>]
let ``apiChanges true is the flag as a standing decision`` () =
    Assert.True(Configuration.parseApiChanges """{ "apiChanges": true }""")

[<Fact>]
let ``a non-boolean publicApi reads as unset rather than as true`` () =
    Assert.Equal<bool option>(None, Configuration.parsePublicApi """{ "publicApi": "yes" }""")
    Assert.False(Configuration.parseApiChanges """{ "apiChanges": 1 }""")

[<Fact>]
let ``run-level keys at the root are not read as rules`` () =
    // rule keys may sit at the root, so publicApi/apiChanges/suppressions
    // have to be excluded there or a future rule of that name collides
    let rules =
        Configuration.parse """{ "publicApi": false, "apiChanges": true, "FR0001": false }"""

    Assert.False(rules.ContainsKey "publicapi")
    Assert.False(rules.ContainsKey "apichanges")
    Assert.True(rules.ContainsKey "fr0001")

[<Fact>]
let ``a rule named publicApi inside the rules wrapper is still a rule`` () =
    let rules = Configuration.parse """{ "rules": { "publicApi": false } }"""
    Assert.True(rules.ContainsKey "publicapi")

// ---- --create-config ----

[<Fact>]
let ``the generated config parses, and every rule in it carries its own default`` () =
    // the file's whole promise is that it changes nothing until edited: a
    // value that did not match the default would silently reconfigure the
    // repository that ran --create-config
    let text = FSharp.Refactor.Tool.Program.defaultConfigText ()
    let rules = Configuration.parse text

    Assert.NotEmpty rules

    for code, _ in RuleCatalog.allRules do
        Assert.Equal(Configuration.isEnabledIn Map.empty code "", Configuration.isEnabledIn rules code "")

[<Fact>]
let ``the generated config lists every rule the catalog knows`` () =
    let rules = Configuration.parse (FSharp.Refactor.Tool.Program.defaultConfigText ())

    let missing =
        RuleCatalog.allRules
        |> List.map fst
        |> List.filter (fun code -> not (rules.ContainsKey(code.ToLowerInvariant())))

    Assert.Empty missing

[<Fact>]
let ``the generated config's run-level keys read back at their defaults`` () =
    let text = FSharp.Refactor.Tool.Program.defaultConfigText ()

    // publicApi is commented out on purpose: its default is not a fixed
    // value but the compilation's own answer, so writing one would be the
    // one line in the file that changed something
    Assert.Equal<bool option>(None, Configuration.parsePublicApi text)
    Assert.False(Configuration.parseApiChanges text)
    Assert.Equal("all", Configuration.parseSuppressions text)
    Assert.Empty(Configuration.parseIgnorePaths text)
    Assert.Empty(Configuration.parseHints text)

[<Theory>]
[<InlineData("{}", false)>]
[<InlineData("""{ "publicApi": true }""", false)>]
[<InlineData("""{ "publicApi": false }""", true)>]
[<InlineData("""{ "apiChanges": true }""", true)>]
// apiChanges is the wider of the two and wins over a publicApi that says
// the surface matters
[<InlineData("""{ "publicApi": true, "apiChanges": true }""", true)>]
let ``publicApi false and apiChanges each open the shape-change scope`` (json: string) (expected: bool) =
    // a directory per case: the parsed config is cached against the file's
    // last-write time, and two writes inside one filesystem tick would
    // read back as the first one
    let root = Path.Combine(Path.GetTempPath(), $"fsref-cfg-{Path.GetRandomFileName()}")

    Directory.CreateDirectory root |> ignore
    let source = Path.Combine(root, "Thing.fs")
    File.WriteAllText(source, "module Thing\n\nlet x = 1\n")
    File.WriteAllText(Path.Combine(root, Configuration.ConfigFileName), json)

    try
        Assert.Equal(expected, Configuration.publicSurfaceOpen source)
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

// ---- the compilation's own answer, when the config is silent ----

[<Theory>]
// an executable has no external linker: its public surface is not an API
[<InlineData("Thing.fs", "--target:exe", true)>]
[<InlineData("Thing.fs", "--target:winexe", true)>]
// fsc takes the single-dash spelling too
[<InlineData("Thing.fs", "-target:exe", true)>]
[<InlineData("Thing.fs", "--target:library", false)>]
// no target flag at all reads as a library, the conservative answer
[<InlineData("Thing.fs", "--nowarn:64", false)>]
let ``the target flag decides for a project`` (file: string) (flag: string) (expected: bool) =
    let leaf = Visibility.compilationIsLeaf [ file ] [ flag; "--noframework" ]
    Assert.Equal(expected, Visibility.isApplication file leaf)

[<Fact>]
let ``a script is a leaf, and what it loads is not`` () =
    // a script compilation is the script plus everything it #loads. The
    // script links to nothing and nothing links to it; a #loaded .fs
    // belongs to whatever project owns it, which a script reading it says
    // nothing about
    let leaf = Visibility.compilationIsLeaf [ "Helper.fs"; "loader.fsx" ] []

    Assert.True(Visibility.isApplication "loader.fsx" leaf)
    Assert.False(Visibility.isApplication "Helper.fs" leaf)

[<Fact>]
let ``a script compilation ignores the target flag for its loaded sources`` () =
    // whatever a host reports for a script's target, a #loaded file's
    // assembly is not the script's
    let leaf =
        Visibility.compilationIsLeaf [ "Helper.fs"; "loader.fsx" ] [ "--target:exe" ]

    Assert.False(Visibility.isApplication "Helper.fs" leaf)

[<Fact>]
let ``the executable test reads the argument without allocating`` () =
    // it runs against every compiler argument of every compilation, and a
    // project carries hundreds of -r: references
    Assert.True(Visibility.compilationIsLeaf [ "A.fs" ] [ "-r:X.dll"; " --TARGET:Exe " ])
    Assert.False(Visibility.compilationIsLeaf [ "A.fs" ] [ "--target:exemplar" ])
    Assert.False(Visibility.compilationIsLeaf [ "A.fs" ] [ "-r:target:exe.dll" ])

// ---- a signature file may declare a PRIVATE name ----

[<Fact>]
let ``a private name the signature declares is not free to change shape`` () =
    // Deedle's vendored FSharp.Data writes
    //     val private ( |SubtypePrimitives|_| ) : ... -> (...) option
    // and FR0011 gave the implementation a voption return alone, which
    // stopped the project compiling. "Private is the one visibility a
    // signature never mentions" was the assumption; `val private` is legal
    // and simply optional, so the gate has to look rather than assume.
    let root = Path.Combine(Path.GetTempPath(), $"fsref-sig-{Path.GetRandomFileName()}")

    Directory.CreateDirectory root |> ignore
    let implementation = Path.Combine(root, "Inference.fs")

    try
        File.WriteAllText(implementation, "module M\n")

        File.WriteAllText(
            Path.Combine(root, "Inference.fsi"),
            "module M\n\nval private ( |SubtypePrimitives|_| ) : int -> int option\nval other: int -> int\n"
        )

        Assert.True(Text.signatureMentions implementation "|SubtypePrimitives|_|")
        Assert.True(Text.signatureMentions implementation "other")
        // a name the signature does not declare is hidden behind it, and
        // the 15 other FR0011 sites in Deedle depend on staying offered
        Assert.False(Text.signatureMentions implementation "notDeclared")
        // whole-word: `other` must not match inside `otherwise`
        Assert.False(Text.signatureMentions implementation "othe")
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

[<Fact>]
let ``no signature file means nothing is declared`` () =
    let root = Path.Combine(Path.GetTempPath(), $"fsref-sig-{Path.GetRandomFileName()}")

    Directory.CreateDirectory root |> ignore
    let implementation = Path.Combine(root, "Lone.fs")

    try
        File.WriteAllText(implementation, "module M\n")
        Assert.False(Text.signatureMentions implementation "anything")
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

// ---- what the scope gate holds back ----

[<Fact>]
let ``the host is told apart by whether it installed a cross-file parser`` () =
    // editors offer the widened findings as light bulbs, because a light
    // bulb is per-site consent from the one person who knows whether that
    // record crosses a wire; a batch run has nobody to ask and only counts
    // them. The CLI installs a parser, editors do not — no new flag needed
    ProjectSources.configure None
    Assert.False(ProjectSources.available ())

    try
        ProjectSources.configure (Some(fun _ -> None))
        Assert.True(ProjectSources.available ())
    finally
        ProjectSources.configure None
