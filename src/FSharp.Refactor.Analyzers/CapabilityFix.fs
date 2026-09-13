/// Dual-framework emission for CAPABILITY fixes — rewrites that need an
/// overload newer than some of a project's target frameworks.
///
/// On a single-target project the fix is applied plainly. But a
/// multi-targeted project compiles the same line for net48 and net10
/// alike, and a plain `AsSpan` breaks the legacy half — the SQLProvider
/// lesson, three times over. When the apply tool signals such a run AND
/// the file already speaks conditional compilation, the fix emits both
/// worlds instead:
///
///     #if NETSTANDARD21              // the project's OWN constant
///         Int32.Parse(s.AsSpan(6, 5))
///     #else
///         Int32.Parse(s.Substring(6, 5))
///     #endif
///
/// Deliberately trivial: the guard is the PROJECT'S OWN constant (the
/// tool recognizes one whose TargetFramework conditions cover exactly
/// the modern half), whole-line wrapping, single-line fixes only.
/// A file with no `#if` anywhere stays free of them: the plain fix is
/// used, and the all-frameworks build check remains the arbiter.
module FSharp.Refactor.CapabilityFix

open System
open FSharp.Analyzers.SDK
open FSharp.Compiler.Text

/// The guard constant for dual emission — the PROJECT'S OWN, never an
/// invented one. The apply tool reads the fsproj's DefineConstants and
/// recognizes a constant whose $(TargetFramework) conditions cover the
/// modern frameworks and none of the legacy ones (SQLProvider's
/// NETSTANDARD21, say); that name arrives here for framework passes
/// where dual emission applies. A project defining no such constant gets
/// no #if from us — the fix stays plain and the all-frameworks build
/// remains the arbiter. Editors never set the variable, so light bulbs
/// stay plain everywhere.
let dualGuardConstant () : string voption =
    match Environment.GetEnvironmentVariable "FSREF_DUAL_TFM" with
    | null
    | "" -> ValueNone
    | c when c |> Seq.forall (fun ch -> Char.IsLetterOrDigit ch || ch = '_') -> ValueSome c
    | _ -> ValueNone

/// Set on a pass over a framework WIDER than the project's narrowest,
/// when the project offers no framework-shaped constant to guard with.
/// A capability fix there can only be applied plainly, into code the
/// narrow framework also compiles, and the all-frameworks build then
/// reverts it — taking every innocent fix in those files with it.
/// SwaggerProvider paid 62 applied fixes and 7 files reverted for a
/// handful of char overloads.
///
/// Nothing can be emitted safely in that position, so nothing is: the
/// rule keeps its advice and drops the fix.
let guardUnavailable () =
    Environment.GetEnvironmentVariable "FSREF_NO_GUARD" = "1"

/// `obj/project.assets.json` per project: the file's write stamp and the
/// lowest FSharp.Core major it resolves across the project's targets.
let private assetsMinFSharpCore =
    System.Collections.Concurrent.ConcurrentDictionary<string, DateTime * int voption>()

/// The lowest FSharp.Core major among the targets `obj/project.assets.json`
/// resolved for the project beside `projectFile`; ValueNone without a
/// restore, or when no target lists FSharp.Core. The assets file is where
/// every target's resolution meets — implicit (SDK-chosen), explicit and
/// conditioned `<PackageReference>`s, central package versions and paket
/// all end up there — which the project file alone cannot tell.
let private assetsMinFSharpCoreMajor (projectFile: string) : int voption =
    try
        let dir = System.IO.Path.GetDirectoryName(System.IO.Path.GetFullPath projectFile)
        let assets = System.IO.Path.Combine(dir, "obj", "project.assets.json")

        if not (System.IO.File.Exists assets) then
            ValueNone
        else
            let stamp = System.IO.File.GetLastWriteTimeUtc assets

            match assetsMinFSharpCore.TryGetValue assets with
            | true, (seen, found) when seen = stamp -> found
            | _ ->
                let found =
                    use doc = System.Text.Json.JsonDocument.Parse(System.IO.File.ReadAllText assets)

                    match doc.RootElement.TryGetProperty "targets" with
                    | true, targets when targets.ValueKind = System.Text.Json.JsonValueKind.Object ->
                        let versions =
                            [ for target in targets.EnumerateObject() do
                                  if target.Value.ValueKind = System.Text.Json.JsonValueKind.Object then
                                      for package in target.Value.EnumerateObject() do
                                          if
                                              package.Name.StartsWith(
                                                  "FSharp.Core/",
                                                  StringComparison.OrdinalIgnoreCase
                                              )
                                          then
                                              // `9.0.300-beta.1`: the prerelease tag is no part of the version
                                              let text =
                                                  package.Name.Substring("FSharp.Core/".Length).Split '-' |> Array.head

                                              match Version.TryParse text with
                                              | true, version -> version
                                              | _ -> () ]

                        match versions with
                        | [] -> ValueNone
                        | _ -> ValueSome (List.min versions).Major
                    | _ -> ValueNone

                assetsMinFSharpCore.[assets] <- (stamp, found)
                found
    with _ -> // an unreadable assets file gates nothing more than the compilation's own reference; fsharpanalyzer: ignore-line FR0055
        ValueNone

/// The LOWEST FSharp.Core major among the project's target frameworks. A
/// multi-targeted project compiles every file against each framework's
/// FSharp.Core, so a rewrite that needs FSharp.Core 9 (`Result.isOk`,
/// `[<TailCall>]`) has to hold for the narrowest one — FsToolkit's net9.0
/// pass offered both on files its netstandard2.0 target compiles against
/// FSharp.Core 6, and the all-frameworks build put two files back. The
/// compilation's own reference only speaks for its own framework; the
/// restore's `obj/project.assets.json` beside the project lists every
/// target's, so the answer is the same in the apply tool and in an editor.
/// FSREF_MIN_FSHARP_CORE, when set, overrides it (an explicit floor for a
/// project whose restore is not on disk). ValueNone leaves a gate to the
/// compilation's own reference.
let minFSharpCoreMajor (projectFile: string) : int voption =
    match Environment.GetEnvironmentVariable "FSREF_MIN_FSHARP_CORE" with
    | null
    | "" -> assetsMinFSharpCoreMajor projectFile
    | v ->
        let major = v.Split '.' |> Array.head

        match Int32.TryParse major with
        | true, n when n >= 0 -> ValueSome n
        | _ -> ValueNone

/// Does the file already use conditional compilation? Only then may a
/// fix introduce more of it.
let usesConditionals (source: ISourceText) =
    // ISourceText is an indexer, not a sequence, so the range is the thing
    // being searched. Seq.exists short-circuits exactly as the hand-rolled
    // flag loop did
    seq { 0 .. source.GetLineCount() - 1 }
    |> Seq.exists (fun i -> source.GetLineString(i).TrimStart().StartsWith "#if")

/// The directive condition governing a line, scanned upward with nesting
/// tracked: an `#endif` above us opens a balanced region to skip; an
/// `#else`/`#elif` crossed at depth zero means we live in the NEGATIVE
/// branch of whatever `#if` follows. Returns the `#if` line's text for a
/// positive branch, "" for a negative one, None outside any region.
let private enclosingCondition (source: ISourceText) (lineNumber: int) =
    let mutable depth = 0
    let mutable negativeBranch = false
    let mutable result = ValueNone
    let mutable i = lineNumber - 2 // zero-based line above the fix line

    while result.IsNone && i >= 0 do
        let t = source.GetLineString(i).TrimStart()

        if t.StartsWith "#endif" then
            depth <- depth + 1
        elif (t.StartsWith "#else" || t.StartsWith "#elif") && depth = 0 then
            negativeBranch <- true
        elif t.StartsWith "#if" then
            if depth = 0 then
                result <- ValueSome(if negativeBranch then "" else t)
            else
                depth <- depth - 1

        i <- i - 1

    result

let private sdkModernGuard =
    System.Text.RegularExpressions.Regex @"NET([5-9]|\d\d)_0_OR_GREATER"

/// Is the line already guarded so that the legacy frameworks never
/// compile it — under the project's own guard constant, or an SDK
/// NET*_OR_GREATER someone wrote by hand? Then the plain fix is safe and
/// wrapping would only nest noise.
let private alreadyModernGuarded (guardConstant: string) (source: ISourceText) (lineNumber: int) =
    match enclosingCondition source lineNumber with
    | ValueSome condition ->
        condition <> ""
        && not (condition.Contains '!')
        && (condition.Contains guardConstant || sdkModernGuard.IsMatch condition)
    | ValueNone -> false

/// The capability fix: plain replacement normally; the #if/#else/#endif
/// pair when a dual-framework run is signalled and the file already uses
/// conditionals. `r` is the sub-range the plain fix would replace.
let make (source: ISourceText) (r: range) (fromText: string) (toText: string) : Fix =
    let plain =
        { FromRange = r
          FromText = fromText
          ToText = toText }

    match dualGuardConstant () with
    | ValueNone -> plain
    | ValueSome guard when
        not (r.StartLine = r.EndLine && usesConditionals source)
        // a line the legacy frameworks never compile needs no second world
        || alreadyModernGuarded guard source r.StartLine
        ->
        plain
    | ValueSome guard ->
        let line = source.GetLineString(r.StartLine - 1)

        // stale range protection: the plain fix's own FromText check
        // happens at apply time, but the whole-line variant replaces the
        // line, so verify the target text here instead
        if
            r.EndColumn > line.Length
            || line.Substring(r.StartColumn, r.EndColumn - r.StartColumn) <> fromText
        then
            plain
        else
            let fixedLine =
                line.Substring(0, r.StartColumn) + toText + line.Substring(r.EndColumn)

            let lineRange =
                Range.mkRange r.FileName (Position.mkPos r.StartLine 0) (Position.mkPos r.StartLine line.Length)

            { FromRange = lineRange
              FromText = line
              ToText = $"#if {guard}\n{fixedLine}\n#else\n{line}\n#endif" }
