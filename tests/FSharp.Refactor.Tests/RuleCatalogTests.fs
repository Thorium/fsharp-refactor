module FSharp.Refactor.Tests.RuleCatalogTests

open System.IO
open System.Text.RegularExpressions
open Xunit
open FSharp.Refactor

/// Every code Rules.md documents in full — one `### FRnnnn` section per rule.
/// That file is the user-facing list, so it is the right thing to hold the
/// catalog against. Its quick table is checked separately, below: a rule can
/// be in one and missing from the other, and both are worth catching.
let private documentedCodes () =
    let rules =
        Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "Rules.md") |> File.ReadAllText

    Regex.Matches(rules, @"^### (FR\d{4}) ", RegexOptions.Multiline)
    |> Seq.map (fun m -> m.Groups.[1].Value)
    |> Set.ofSeq

[<Fact>]
let ``every documented rule has a category`` () =
    let documented = documentedCodes ()
    Assert.NotEmpty documented
    let missing = Set.difference documented RuleCatalog.known

    Assert.True(
        Set.isEmpty missing,
        sprintf "These rules have no category, so they silently read as idiom: %s" (String.concat ", " missing)
    )

[<Fact>]
let ``the catalog invents no rules`` () =
    let unknown = Set.difference RuleCatalog.known (documentedCodes ())

    Assert.True(
        Set.isEmpty unknown,
        sprintf "The catalog lists rules Rules.md does not document: %s" (String.concat ", " unknown)
    )

[<Fact>]
let ``categories partition the rules`` () =
    let counted =
        RuleCatalog.all
        |> List.sumBy (fun c -> (RuleCatalog.codesIn (Set.singleton c)).Count)

    Assert.Equal(RuleCatalog.known.Count, counted)

[<Fact>]
let ``the substantive set is correctness and performance`` () =
    let substantive = RuleCatalog.codesIn RuleCatalog.substantive
    Assert.Contains("FR0075", substantive) // a disposable that never gets disposed
    Assert.Contains("FR0038", substantive) // a needless allocation
    Assert.DoesNotContain("FR0083", substantive) // an empty attribute argument list
    Assert.DoesNotContain("FR0099", substantive) // a line-ending semicolon

[<Fact>]
let ``category names round-trip`` () =
    for category in RuleCatalog.all do
        Assert.Equal(Some category, RuleCatalog.parse (RuleCatalog.name category))

[<Fact>]
let ``an unknown category does not parse`` () =
    Assert.Equal(None, RuleCatalog.parse "urgent")

[<Fact>]
let ``the README's kind summary matches the rules it lists`` () =
    // the summary table states a count per kind, and adding a rule used to
    // move the real count and leave the summary behind. The rules themselves
    // now live in Rules.md, so the count is held against the CATALOG rather
    // than against a second copy of the list in prose
    let readme =
        Path.Combine(__SOURCE_DIRECTORY__, "..", "..", "README.md") |> File.ReadAllText

    let actual =
        RuleCatalog.allRules
        |> List.countBy (fun (_, category) -> RuleCatalog.name category)
        |> Map.ofList

    let claimed =
        Regex.Matches(
            readme,
            @"^\| `(correctness|performance|idiom|cosmetic)` \|.*\| (\d+) \|$",
            RegexOptions.Multiline
        )
        |> Seq.map (fun m -> m.Groups.[1].Value, int m.Groups.[2].Value)
        |> Map.ofSeq

    Assert.NotEmpty claimed

    for KeyValue(kind, stated) in claimed do
        let counted = actual.TryFind kind |> Option.defaultValue 0
        Assert.True((stated = counted), $"README says %d{stated} %s{kind} rules; the catalog has %d{counted}")

// ---- Rules.md: the quick-reference table ----

let private repoFile name =
    Path.Combine(__SOURCE_DIRECTORY__, "..", "..", name) |> File.ReadAllText

/// The table's rows: code, category, enabled flag, api flag. An empty flag
/// cell renders as a single space between its pipes.
let private rulesTableRows () =
    Regex.Matches(repoFile "Rules.md", @"^\| (FR\d{4}) \| (\w+) \| (v?) ?\| (v?) ?\| (v?) ?\|", RegexOptions.Multiline)
    |> Seq.map (fun m -> m.Groups.[1].Value, m.Groups.[2].Value, m.Groups.[3].Value = "v", m.Groups.[4].Value = "v")
    |> List.ofSeq

[<Fact>]
let ``Rules.md has exactly one row per catalogued rule`` () =
    let rows = rulesTableRows () |> List.map (fun (code, _, _, _) -> code)
    let missing = RuleCatalog.known - Set.ofList rows
    let unknown = Set.ofList rows - RuleCatalog.known

    let duplicated =
        rows |> List.countBy id |> List.filter (fun (_, n) -> n > 1) |> List.map fst

    Assert.True(missing.IsEmpty, $"Rules.md lacks a row for: %A{missing}")
    Assert.True(unknown.IsEmpty, $"Rules.md lists codes the catalog does not know: %A{unknown}")
    Assert.True(duplicated.IsEmpty, $"Rules.md lists twice: %A{duplicated}")

[<Fact>]
let ``Rules.md categories match the catalog`` () =
    for code, category, _, _ in rulesTableRows () do
        let expected = RuleCatalog.name (RuleCatalog.categoryOf code)

        Assert.True(
            System.String.Equals(category, expected, System.StringComparison.OrdinalIgnoreCase),
            $"{code}: Rules.md says {category}, the catalog says {expected}"
        )

[<Fact>]
let ``Rules.md enabled column matches the default-off list`` () =
    // an analyzer's name is what `whenEnabled` receives beside its code —
    // the default-off list keys some rules by that name
    let names =
        Regex.Matches(
            repoFile "src/FSharp.Refactor.Analyzers/Analyzers.fs",
            @"whenEnabled ctx\.FileName ""(FR\d{4})"" ""(\w+)""",
            RegexOptions.Multiline
        )
        |> Seq.map (fun m -> m.Groups.[1].Value, m.Groups.[2].Value)
        |> Seq.distinct
        |> Map.ofSeq

    for code, _, enabled, _ in rulesTableRows () do
        let name = names.TryFind code |> Option.defaultValue ""
        let expected = Configuration.isEnabledIn Map.empty code name

        Assert.True(
            (enabled = expected),
            $"{code} ({name}): Rules.md says enabled={enabled}, Configuration says {expected}"
        )

[<Fact>]
let ``Rules.md advisory rows match the catalog's advisory set`` () =
    let dashRows =
        Regex.Matches(repoFile "Rules.md", @"^\| (FR\d{4}) \|.*\| — \|\s*$", RegexOptions.Multiline)
        |> Seq.map (fun m -> m.Groups.[1].Value)
        |> Set.ofSeq

    let missing = Set.difference dashRows RuleCatalog.advisory
    let extra = Set.difference RuleCatalog.advisory dashRows
    Assert.True(missing.IsEmpty, $"Rules.md marks as advisory but the catalog does not: %A{missing}")
    Assert.True(extra.IsEmpty, $"the catalog marks as advisory but Rules.md offers a fix: %A{extra}")

[<Fact>]
let ``Rules.md priority column matches the catalog's priority set`` () =
    let flagged =
        Regex.Matches(repoFile "Rules.md", @"^\| (FR\d{4}) \| \w+ \| v? ?\| v? ?\| v \|", RegexOptions.Multiline)
        |> Seq.map (fun m -> m.Groups.[1].Value)
        |> Set.ofSeq

    let missing = Set.difference RuleCatalog.priority flagged
    let extra = Set.difference flagged RuleCatalog.priority
    Assert.True(missing.IsEmpty, $"the catalog marks as priority but Rules.md does not: %A{missing}")
    Assert.True(extra.IsEmpty, $"Rules.md marks as priority but the catalog does not: %A{extra}")
