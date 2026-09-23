/// The generated config must tell the truth about the rules' tunables.
///
/// `--create-config` writes every knob at "this build's default", and the
/// defaults it writes come from `RuleCatalog.knobs` while the rules read
/// theirs from the `Configuration.parameter*` call that asks for them.
/// Two places, so they can drift — and a config file that states a wrong
/// default is worse than one that states none, because a user who keeps
/// the line has pinned a value they never chose.
///
/// These tests hold the two together: with NO configuration present,
/// every knob in the catalogue must read back exactly what the catalogue
/// says, and every knob must be one the rules actually consult.
module FSharp.Refactor.Tests.ConfigKnobTests

open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tool

/// Every `Configuration.parameterBool/parameterInt` call in the analyzer
/// and tool sources, as (code, knob, default-as-written).
///
/// The default a rule actually uses is the FALLBACK argument of its own
/// lookup — `parameterBool` returns it whenever no config carries the
/// knob — so it cannot be observed by calling `Configuration` from a test
/// (that would only read back whatever the test itself passed). It is
/// read from the source instead, which is exactly where it could drift
/// away from the catalogue.
let private callSites =
    let root = Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "src")

    let pattern =
        System.Text.RegularExpressions.Regex
            @"Configuration\.parameter(?:Bool|Int)\s+\w+(?:\.\w+)*\s+""(FR\d{4})""\s+""\w+""\s+""(\w+)""\s+([\w.]+)"

    Directory.EnumerateFiles(root, "*.fs", SearchOption.AllDirectories)
    |> Seq.filter (fun f -> not (f.Contains @"\obj\" || f.Contains @"\bin\"))
    |> Seq.collect (fun f -> pattern.Matches(File.ReadAllText f))
    |> Seq.map (fun m -> m.Groups.[1].Value, m.Groups.[2].Value, m.Groups.[3].Value)
    |> Seq.distinct
    |> Seq.toList

/// `AttributeMerge.DefaultWrapColumn` and friends are spelled as names at
/// the call site; resolve the ones the catalogue covers.
let private namedDefaults =
    dict
        [
            "AttributeMerge.DefaultMaxAttributes", string AttributeMerge.DefaultMaxAttributes
            "AttributeMerge.DefaultWrapColumn", string AttributeMerge.DefaultWrapColumn
        ]

let private resolve (written: string) =
    match namedDefaults.TryGetValue written with
    | true, value -> value
    | _ ->
        // `0`/`1` are the bool spelling `parameterBool` accepts
        match written with
        | "0" -> "false"
        | "1" -> "true"
        | other -> other

[<Fact>]
let ``every catalogued knob is spelled once per rule`` () =
    for code, knobs in RuleCatalog.knobs do
        let names = knobs |> List.map _.Name
        Assert.Equal<string list>(List.distinct names, names)
        Assert.NotEmpty names
        Assert.False(names |> List.exists (fun n -> n = "enabled"), $"{code}: 'enabled' is not a knob")

[<Fact>]
let ``every catalogued rule exists`` () =
    let known = RuleCatalog.codesIn (Set.ofList RuleCatalog.all)

    for code, _ in RuleCatalog.knobs do
        Assert.True(known.Contains code, $"{code} is catalogued as tunable but is not a rule")

[<Fact>]
let ``the catalogue's default is the one the rule actually falls back to`` () =
    Assert.NotEmpty callSites

    for code, knobs in RuleCatalog.knobs do
        for knob in knobs do
            match callSites |> List.tryFind (fun (c, k, _) -> c = code && k = knob.Name) with
            | None -> failwith $"{code}.{knob.Name} is catalogued but no rule reads it"
            | Some(_, _, written) -> Assert.Equal(knob.Default, resolve written)

[<Fact>]
let ``every knob a rule reads is catalogued`` () =
    let missing =
        callSites
        |> List.filter (fun (code, name, _) -> RuleCatalog.knobsOf code |> List.forall (fun k -> k.Name <> name))
        |> List.map (fun (code, name, _) -> $"{code}.{name}")

    Assert.True(
        missing.IsEmpty,
        "rules read knobs the catalogue does not list, so --create-config hides them: "
        + String.concat ", " missing
    )

[<Fact>]
let ``the generated config parses and carries every knob`` () =
    let text = Program.defaultConfigText ()

    for code, knobs in RuleCatalog.knobs do
        for knob in knobs do
            Assert.Contains($"\"{knob.Name}\": {knob.Default}", text)

        // the rule is written as an object, not a bare bool
        Assert.Contains($"\"{code}\": {{ \"enabled\": ", text)

[<Fact>]
let ``a rule with no knobs stays a bare bool`` () =
    let text = Program.defaultConfigText ()
    Assert.Contains("\"FR0172\": true,", text)

[<Fact>]
let ``the generated config is pure ASCII`` () =
    // This file is written to a repository and opened by whatever the
    // reader happens to use. A `>` arrow or an em dash is UTF-8, and a
    // Windows console or editor under an OEM codepage renders those as
    // mojibake. A byte-order mark does not save it - a console that
    // ignores the mark prints the mark itself as garbage too - so the
    // content stays ASCII instead, which every codepage agrees on.
    let text = Program.defaultConfigText ()

    let offenders =
        text
        |> Seq.filter (fun c -> c > '\127')
        |> Seq.distinct
        |> Seq.map (fun c -> $"U+%04X{int c} '%c{c}'")
        |> List.ofSeq

    Assert.True(
        offenders.IsEmpty,
        "the generated config carries non-ASCII, which renders as mojibake outside UTF-8: "
        + String.concat ", " offenders
    )
