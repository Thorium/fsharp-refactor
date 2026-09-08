/// Opt-in corpus validation, activated by environment variables so CI and
/// plain `dotnet test` runs skip it silently:
///
///   FSREF_CORPUS_ROOTS = C:\git\RepoA;C:\git\RepoB
///       runs every parse-only fix rule over each .fs file under the
///       roots, applies every suggested edit individually, and verifies
///       the patched file still parses — the guard that caught fixes
///       splicing #if/#else/#endif blocks apart
///
///   FSREF_APPLY_ARGS = --project|C:\path\X.fsproj|--codes|FR0002
///       runs the full apply tool (arguments separated by `|`) through the
///       test host — the working channel on machines where Smart App
///       Control blocks freshly built executables
module FSharp.Refactor.Tests.CorpusValidation

open System
open System.IO
open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tool
open FSharp.Refactor.Tests.Parsing

[<Fact>]
let ``corpus fixes still parse`` () : unit =
    match Environment.GetEnvironmentVariable "FSREF_CORPUS_ROOTS" with
    | null
    | "" -> ()
    | roots ->
        let failures = ResizeArray<string>()
        let mutable applied = 0
        let mutable filesSeen = 0
        let mutable unparseable = 0

        // per-rule hit counts, plus a few real example sites each: a count
        // alone says a rule fires a lot, the samples say whether it should
        let hits = Collections.Generic.Dictionary<string, int>()
        let samples = Collections.Generic.Dictionary<string, ResizeArray<string>>()

        let countHit (code: string) (where: string) =
            hits.[code] <-
                (match hits.TryGetValue code with
                 | true, n -> n
                 | false, _ -> 0)
                + 1

            match samples.TryGetValue code with
            | true, existing ->
                if existing.Count < 4 then
                    existing.Add where
            | false, _ ->
                let fresh = ResizeArray()
                fresh.Add where
                samples.[code] <- fresh

        /// file(line,col) plus the source line, so a sample can be judged
        /// without opening the file
        let siteOf (file: string) (source: string) (r: FSharp.Compiler.Text.range) =
            let lines = source.Replace("\r\n", "\n").Split '\n'

            let text =
                if r.StartLine >= 1 && r.StartLine <= lines.Length then
                    lines.[r.StartLine - 1].Trim()
                else
                    ""

            $"{file}({r.StartLine},{r.StartColumn}): {text}"

        // A plain file walk: project and solution membership are irrelevant,
        // because the rules here are parse-only. Scripts count too — a
        // parse-only rule applies to an .fsx exactly as it does to an .fs,
        // and scripts are where a lot of real-world F# actually lives.
        let files =
            roots.Split ';'
            |> Seq.collect (fun root ->
                if Directory.Exists root then
                    seq {
                        yield! FileWalk.files "*.fs" root
                        yield! FileWalk.files "*.fsx" root
                    }
                else
                    Seq.empty)

        for file in files do
            // a file that cannot be read is not a rule failure
            let source =
                try
                    File.ReadAllText file
                with
                | :? IOException
                | :? UnauthorizedAccessException -> ""

            let asName =
                if file.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase) then
                    "Test.fsx"
                else
                    "Test.fs"

            try
                // A file that does not parse is not ours to fix — plenty of
                // real repositories carry deliberately-broken fixtures. What
                // matters is that no rule THROWS on the recovered tree, so
                // the rules still run; only the patch validation below is
                // skipped, being meaningless when the input was already
                // unparseable.
                let tree, hadParseErrors, sourceText = tryParseNamed asName source
                filesSeen <- filesSeen + 1

                if hadParseErrors then
                    unparseable <- unparseable + 1

                let suggestions =
                    [ for s in RedundantParens.find tree sourceText -> s.Range, s.ReplacementText, "FR0013"
                      for s in MethodCallParens.find tree sourceText -> s.Range, s.ReplacementText, "FR0094"
                      for s in LambdaBuiltin.find tree sourceText -> s.Range, s.ReplacementText, "FR0095"
                      for s in PatternParens.find tree sourceText -> s.Range, s.ReplacementText, "FR0096"
                      for s in TypeSyntax.findRedundantParens tree sourceText -> s.Range, s.ReplacementText, "FR0097"
                      for s in TypeSyntax.findAbbreviations tree sourceText -> s.Range, s.ReplacementText, "FR0098"
                      for s in TrailingSemicolon.find tree sourceText -> s.Range, s.ReplacementText, "FR0099"
                      for s in MatchToIf.find tree sourceText -> s.Range, s.ReplacementText, "FR0001"
                      for s in RaiseFailwith.find tree sourceText -> s.Range, s.ReplacementText, "FR0024"
                      for s in
                          AttributeMerge.find
                              AttributeMerge.DefaultMaxAttributes
                              AttributeMerge.DefaultWrapColumn
                              tree
                              sourceText -> s.Range, s.ReplacementText, "FR0060"
                      for s in HintEngine.find [] tree sourceText None -> s.Range, s.ReplacementText, "FR0011/12"
                      for s in Simplification.find tree sourceText None -> s.Range, s.ReplacementText, "FR0010"
                      for s in ConversionMove.find tree sourceText -> s.Range, s.ReplacementText, "FR0004"
                      for s in StructDu.find (Visibility.apiChangesAllowed ()) tree sourceText ->
                          s.InsertRange, s.InsertText, "FR0016"
                      for s in RedundantSyntax.find None tree sourceText ->
                          s.Range, s.ReplacementText, $"FR008x/{s.Kind}"
                      for s in MatchBangRule.find tree sourceText do
                          for range, _, replacement in s.Edits -> range, replacement, "FR0073"
                      for s in MatchBangRule.findWhileBang tree sourceText do
                          for range, _, replacement in s.Edits -> range, replacement, "FR0078"
                      for s in IndexedLoop.find tree sourceText do
                          for range, _, replacement in s.Edits -> range, replacement, "FR0101"
                      for s in TypeTestChain.find tree sourceText -> s.Range, s.ReplacementText, "FR0103" ]

                // note-only rules: nothing to patch, but count them so a rule
                // that fires wildly on real code shows up here
                let voptions, structs, structTuples =
                    StructHints.find (Visibility.apiChangesAllowed ()) tree sourceText

                for s in voptions do
                    countHit "FR0069" (siteOf file source s.Range)

                for s in structs do
                    countHit "FR0070" (siteOf file source s.Range)

                for s in structTuples do
                    countHit "FR0093" (siteOf file source s.Range)

                for s in PathSeparator.find tree sourceText do
                    countHit "FR0081" (siteOf file source s.Range)

                for s in DuFieldNames.find (Visibility.apiChangesAllowed ()) tree sourceText do
                    countHit "FR0022" (siteOf file source s.Range)

                // multi-edit rules (FR0073/FR0078) must apply as a set;
                // single edits verify individually
                for range, replacement, code in suggestions do
                    if code <> "FR0073" && code <> "FR0078" then
                        applied <- applied + 1
                        countHit code (siteOf file source range)
                        let patched = applyEdit source range replacement

                        if not (hadParseErrors || (parsesCleanlyNamed asName patched)) then
                            failures.Add $"{code} {file}({range.StartLine},{range.StartColumn}): -> {replacement}"

                let multiEditSets =
                    [ for s in MatchBangRule.find tree sourceText -> s.Edits
                      for s in MatchBangRule.findWhileBang tree sourceText -> s.Edits ]

                for edits in multiEditSets do
                    applied <- applied + 1

                    let patched =
                        edits
                        |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
                        |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) source

                    if not (hadParseErrors || (parsesCleanlyNamed asName patched)) then
                        failures.Add $"multi-edit {file}: {edits.Length} edits"
            with ex ->
                // a rule THREW: that is a catastrophic failure, unlike a
                // file that simply does not parse
                failures.Add $"THREW {file}: {ex.Message}"

        let byRule =
            hits
            |> Seq.sortByDescending (fun kv -> kv.Value)
            |> Seq.map (fun kv ->
                let examples =
                    match samples.TryGetValue kv.Key with
                    | true, xs -> xs |> Seq.map (fun s -> "\n           " + s) |> String.concat ""
                    | false, _ -> ""

                $"  {kv.Value, 6}  {kv.Key}{examples}")
            |> String.concat "\n"

        let report =
            $"files: {filesSeen} ({unparseable} did not parse), fixes applied: {applied}, rules threw: {failures.Count}\n"
            + "\nper rule:\n"
            + byRule
            + "\n\nfailures:\n"
            + String.concat "\n" failures

        File.WriteAllText(Path.Combine(Path.GetTempPath(), "fsref-corpus-validation.txt"), report)
        Assert.True(failures.Count = 0, report)

[<Fact>]
let ``run apply tool from env`` () : unit =
    match Environment.GetEnvironmentVariable "FSREF_APPLY_ARGS" with
    | null
    | "" -> ()
    | args ->
        let argv = args.Split '|'
        use captured = new StringWriter()
        let oldOut = Console.Out
        let oldErr = Console.Error
        Console.SetOut captured
        Console.SetError captured

        let code =
            try
                Program.main argv
            finally
                Console.SetOut oldOut
                Console.SetError oldErr

        File.WriteAllText(Path.Combine(Path.GetTempPath(), "fsref-apply-run.txt"), captured.ToString())
        Assert.True((code = 0), sprintf "exit %d:\n%s" code (captured.ToString()))
