/// Optional per-repository configuration, fsharplint.json-style.
///
/// A file named `fsharprefactor.json` is searched upward from the
/// analyzed file's directory; the nearest one wins. Rules are keyed by code
/// or analyzer name (case-insensitive) and every rule defaults to enabled:
///
///     {
///       "rules": {
///         "FR0001": false,
///         "conversionMove": { "enabled": false }
///       }
///     }
///
/// The `rules` wrapper is optional — rule keys may also sit at the root.
/// A malformed or unreadable file fails open (everything enabled) so a bad
/// config can never break the user's editor; unknown keys are ignored.
///
/// A few root keys configure the RUN rather than a rule — `hints`,
/// `ignorePaths`, `suppressions`, `publicApi`, `apiChanges` — and are
/// never read as rule names, so a future rule of one of those names
/// cannot silently collide with them.
///
/// Lookups are cached: directory discovery is revalidated after a short
/// interval and the parsed file is reloaded when its timestamp changes, so
/// config edits are picked up without restarting the editor.
module FSharp.Refactor.Configuration

open System
open System.Collections.Concurrent
open System.IO
open System.Text.Json

[<Literal>]
let ConfigFileName = "fsharprefactor.json"

/// Root keys that configure the RUN, not a rule. Excluded from the rule
/// map when rule keys sit at the root, so `"apiChanges": true` there can
/// never be read as a rule named apiChanges.
let private reservedRootKeys =
    set [ "rules"; "hints"; "ignorepaths"; "suppressions"; "publicapi"; "apichanges" ]

/// Parse the config text into a rule-key -> enabled map (keys lowercased).
/// Pure and total: malformed input yields an empty map (fail open).
let parse (json: string) : Map<string, bool> =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)
        let root = doc.RootElement

        let rulesElement, atRoot =
            match root.TryGetProperty "rules" with
            | true, rules when rules.ValueKind = JsonValueKind.Object -> rules, false
            | _ -> root, true

        rulesElement.EnumerateObject()
        |> Seq.filter (fun property -> not (atRoot && reservedRootKeys.Contains(property.Name.ToLowerInvariant())))
        |> Seq.choose (fun property ->
            let enabled =
                match property.Value.ValueKind with
                | JsonValueKind.True -> Some true
                | JsonValueKind.False -> Some false
                | JsonValueKind.Object ->
                    match property.Value.TryGetProperty "enabled" with
                    | true, e when e.ValueKind = JsonValueKind.True -> Some true
                    | true, e when e.ValueKind = JsonValueKind.False -> Some false
                    | _ -> None
                | _ -> None

            enabled |> Option.map (fun e -> property.Name.ToLowerInvariant(), e))
        |> Map.ofSeq
    with
    | :? JsonException
    | :? InvalidOperationException -> Map.empty

/// Rules that are OFF unless the configuration turns them on.
///
///   FR0099 (trailing semicolons) lexes every file containing `;\n` and
///   sat in the slowest-analyzer list on every run, for a finding that
///   barely occurs in real code — cost out of proportion to value.
///
///   FR0002 (match option → Option combinators) is the most expensive
///   idiom rewrite on the measured board — the only one that makes the
///   USER'S code slower (+53% and a 24-byte closure per call on the
///   gate's pair) — and among the highest-churn. Nice to read, costs to
///   run: an opt-in, not a default.
///   FR0114 (pyramid flip) reorders branches for a style — short exit
///   first — that plenty of teams hold exactly the other way around
///   (happy path first). An opt-in, not a default.
///   FR0141 (generative loop) names a rewrite it cannot carry out. The
///   loops it finds drive a model, a stream, a channel or a graph
///   frontier, and their state is mostly mutable OBJECTS — a
///   StringBuilder, a Dictionary, a torch cache — which recursion carries
///   along unchanged rather than removing. The observation is worth
///   having on demand; volunteered on every run it is noise about a
///   rewrite that often will not pay. An opt-in, not a default.
///   FR0019 (Equals without GetHashCode) duplicates the compiler: FS0346
///   warns on every shape the rule can find, and F# records and unions
///   get both for free. An opt-in, not a default.
let private defaultOff =
    set
        [ "fr0002"
          "fr0134"
          "datetimeoffsetmigration"
          "optionmodule"
          "fr0099"
          "trailingsemicolon"
          "fr0114"
          "pyramidflip"
          "fr0141"
          "generativeloop"
          "fr0019"
          "equalshashcode" ]
// FR0130 and FR0133 both once described themselves as off by default while
// never being listed here, so every sweep ran them; aligning the code to
// that text took away the [<Literal>]s and the backtick names sweeps had
// always produced, and a user comparing versions asked where they went.
// The behaviour a sweep has shown is the contract; the text was wrong. Both
// stay on, and a repository that finds either churn turns it off in
// fsharprefactor.json.

/// Is the rule enabled in a parsed rule map? An explicit code entry wins
/// over a name entry; absent rules are enabled unless default-off.
let isEnabledIn (rules: Map<string, bool>) (code: string) (analyzerName: string) : bool =
    let code = code.ToLowerInvariant()
    let name = analyzerName.ToLowerInvariant()

    rules.TryFind code
    |> Option.orElseWith (fun () -> rules.TryFind name)
    |> Option.defaultValue (not (defaultOff.Contains code || defaultOff.Contains name))

/// Walk up from `directory` looking for the config file, stopping at the
/// repository root (the first directory holding .git) — a stray
/// fsharprefactor.json above the checkout must not silently reconfigure
/// every repository beneath it.
[<TailCall>]
let rec private findConfigUpward (directory: string) : string option =
    if String.IsNullOrEmpty directory then
        None
    else
        let candidate = Path.Combine(directory, ConfigFileName)

        if File.Exists candidate then
            Some candidate
        elif
            Directory.Exists(Path.Combine(directory, ".git"))
            || File.Exists(Path.Combine(directory, ".git"))
        then
            None
        else
            match Path.GetDirectoryName directory with
            | null -> None
            | parent -> findConfigUpward parent

// A few long-lived caches (per our own guidance: few static dictionaries,
// accessed via GetOrAdd/AddOrUpdate only).
let private discoveryRevalidateAfter = TimeSpan.FromSeconds 5.0

let private discoveryCache =
    ConcurrentDictionary<string, DateTime * string option>()

/// Additional hint-engine rules from the config's `hints.add` array
/// (fsharplint-style). Pure and total: anything malformed yields an empty list.
let parseHints (json: string) : string list =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)

        match doc.RootElement.TryGetProperty "hints" with
        | true, hints when hints.ValueKind = JsonValueKind.Object ->
            match hints.TryGetProperty "add" with
            | true, add when add.ValueKind = JsonValueKind.Array ->
                add.EnumerateArray()
                |> Seq.choose (fun item ->
                    if item.ValueKind = JsonValueKind.String then
                        Some(item.GetString())
                    else
                        None)
                |> List.ofSeq
            | _ -> []
        | _ -> []
    with
    | :? JsonException
    | :? InvalidOperationException -> []

/// Extra ignored path patterns from the config's `ignorePaths` array —
/// ADDITIVE over the built-in defaults. Pure and total: anything
/// malformed yields an empty list.
let parseIgnorePaths (json: string) : string list =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)

        match doc.RootElement.TryGetProperty "ignorePaths" with
        | true, paths when paths.ValueKind = JsonValueKind.Array ->
            paths.EnumerateArray()
            |> Seq.choose (fun item ->
                if item.ValueKind = JsonValueKind.String then
                    Some(item.GetString())
                else
                    None)
            |> List.ofSeq
        | _ -> []
    with
    | :? JsonException
    | :? InvalidOperationException -> []

/// The parsed content of one config file.
type ConfigData =
    {
        Rules: Map<string, bool>
        Hints: string list
        IgnorePaths: string list
        /// Numeric knobs per rule, from object-valued rule entries:
        ///     { "FR0114": { "enabled": true, "thenAtLeast": 30 } }
        /// Keys are lowercased rule code (or analyzer name) then parameter
        /// name; every rule documents its own knobs and their defaults.
        Parameters: Map<string, Map<string, int>>
        /// The team's suppression-comment policy, `"suppressions"`:
        ///   "all"            every suppression comment silences its finding
        ///                    (the default, and what editors do regardless)
        ///   "no-correctness" comments on correctness-category rules are
        ///                    reported anyway (though never auto-fixed)
        ///   "none"           every suppression comment is reported anyway
        Suppressions: string
        /// `"publicApi"`: does anything OUTSIDE this assembly link against
        /// its public declarations?
        ///
        /// F# makes a declaration public by default, so "public" in a
        /// parse tree is mostly the absence of a decision rather than one.
        /// The scope-gated rules — the ones whose fix changes a
        /// declaration's compiled SHAPE in place, `[<Struct>]`,
        /// `[<Literal>]`, named union fields — hold back on public
        /// declarations because a consumer in another assembly would see
        /// the change and nothing here can check it. `false` says there is
        /// no such consumer (an application, an internal tool, a leaf
        /// project), and those rules then treat public as internal.
        ///
        /// It says nothing about fixes that must edit OTHER FILES —
        /// currying a function and rewriting its call sites project-wide
        /// is a different risk, and stays behind `apiChanges`. A companion
        /// .fsi still wins over both: a signature file is the author's own
        /// statement of what is exported.
        ///
        /// None = unset, and the conservative reading (public is an API).
        PublicApi: bool option
        /// `"apiChanges"`: `--api-changes` as a per-repository setting,
        /// for the repositories where it is always the right answer.
        /// Covers everything the flag does, cross-file rewrites included,
        /// and so implies `publicApi: false`.
        ApiChanges: bool
    }

/// The `"suppressions"` policy string; unknown values read as "all" so a
/// typo cannot silently harden a run.
let parseSuppressions (json: string) : string =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)

        match doc.RootElement.TryGetProperty "suppressions" with
        | true, v when v.ValueKind = JsonValueKind.String ->
            match v.GetString().ToLowerInvariant() with
            | "no-correctness" -> "no-correctness"
            | "none" -> "none"
            | _ -> "all"
        | _ -> "all"
    with
    | :? JsonException
    | :? InvalidOperationException -> "all"

/// A root-level boolean setting. Pure and total: anything malformed, or a
/// value that is not a JSON boolean, reads as unset.
let private parseRootBool (name: string) (json: string) : bool option =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)

        match doc.RootElement.TryGetProperty name with
        | true, v when v.ValueKind = JsonValueKind.True -> Some true
        | true, v when v.ValueKind = JsonValueKind.False -> Some false
        | _ -> None
    with
    | :? JsonException
    | :? InvalidOperationException -> None

/// The `"publicApi"` setting; unset reads as None, the conservative
/// reading.
let parsePublicApi (json: string) : bool option = parseRootBool "publicApi" json

/// The `"apiChanges"` setting; unset reads as false, so a config can only
/// ever WIDEN what a default run does, never quietly widen a run that
/// already passed the flag.
let parseApiChanges (json: string) : bool =
    parseRootBool "apiChanges" json |> Option.defaultValue false

/// Numeric rule parameters from object-valued rule entries. Pure and
/// total: anything malformed yields an empty map.
let parseParameters (json: string) : Map<string, Map<string, int>> =
    try
        let options =
            JsonDocumentOptions(CommentHandling = JsonCommentHandling.Skip, AllowTrailingCommas = true)

        use doc = JsonDocument.Parse(json, options)
        let root = doc.RootElement

        let rulesElement, atRoot =
            match root.TryGetProperty "rules" with
            | true, rules when rules.ValueKind = JsonValueKind.Object -> rules, false
            | _ -> root, true

        rulesElement.EnumerateObject()
        |> Seq.filter (fun property -> not (atRoot && reservedRootKeys.Contains(property.Name.ToLowerInvariant())))
        |> Seq.choose (fun property ->
            if property.Value.ValueKind = JsonValueKind.Object then
                let knobs =
                    property.Value.EnumerateObject()
                    |> Seq.choose (fun knob ->
                        match knob.Value.ValueKind with
                        | JsonValueKind.Number ->
                            match knob.Value.TryGetInt32() with
                            | true, v -> Some(knob.Name.ToLowerInvariant(), v)
                            | _ -> None
                        // an on/off knob reads naturally as a JSON bool; it is
                        // stored as 0/1 so one map serves both kinds
                        | JsonValueKind.True -> Some(knob.Name.ToLowerInvariant(), 1)
                        | JsonValueKind.False -> Some(knob.Name.ToLowerInvariant(), 0)
                        | _ -> None)
                    |> Map.ofSeq

                if knobs.IsEmpty then
                    None
                else
                    Some(property.Name.ToLowerInvariant(), knobs)
            else
                None)
        |> Map.ofSeq
    with
    | :? JsonException
    | :? InvalidOperationException -> Map.empty

let private emptyConfig =
    { Rules = Map.empty
      Hints = []
      IgnorePaths = []
      Parameters = Map.empty
      Suppressions = "all"
      PublicApi = None
      ApiChanges = false }

let private parseCache = ConcurrentDictionary<string, DateTime * ConfigData>()

/// The effective configuration for a file being analyzed. Discovery is
/// memoized per directory with a short revalidation window; the parsed
/// content is reloaded when the config file's timestamp changes.
let configFor (analyzedFile: string) : ConfigData =
    let directory =
        // invalid path characters mean no config directory to search
        try
            Path.GetDirectoryName(analyzedFile: string)
        with
        | :? ArgumentException
        | :? PathTooLongException -> null

    if String.IsNullOrEmpty directory then
        emptyConfig
    else
        let _, configPath =
            discoveryCache.AddOrUpdate(
                directory,
                (fun dir -> DateTime.UtcNow, findConfigUpward dir),
                (fun dir (checkedAt, cached) ->
                    if DateTime.UtcNow - checkedAt > discoveryRevalidateAfter then
                        DateTime.UtcNow, findConfigUpward dir
                    else
                        checkedAt, cached)
            )

        match configPath with
        | None -> emptyConfig
        | Some path ->
            // a vanished or unreadable config reads as never-written, which
            // forces a re-read attempt on the next call
            let lastWrite =
                try
                    File.GetLastWriteTimeUtc path
                with
                | :? IOException
                | :? UnauthorizedAccessException
                | :? ArgumentException -> DateTime.MinValue

            let readCurrent (p: string) =
                // a config deleted or locked mid-read means no config
                let content =
                    try
                        File.ReadAllText p
                    with
                    | :? IOException
                    | :? UnauthorizedAccessException -> ""

                lastWrite,
                { Rules = parse content
                  Hints = parseHints content
                  IgnorePaths = parseIgnorePaths content
                  Parameters = parseParameters content
                  Suppressions = parseSuppressions content
                  PublicApi = parsePublicApi content
                  ApiChanges = parseApiChanges content }

            let _, config =
                parseCache.AddOrUpdate(
                    path,
                    readCurrent,
                    (fun p (cachedWrite, cached) ->
                        if cachedWrite <> lastWrite then
                            readCurrent p
                        else
                            cachedWrite, cached)
                )

            config

/// The effective rule map for a file being analyzed.
let rulesFor (analyzedFile: string) : Map<string, bool> = (configFor analyzedFile).Rules

/// Extra hint-engine rules configured for a file being analyzed.
let hintsFor (analyzedFile: string) : string list = (configFor analyzedFile).Hints

/// The repository's own answer to "may a declaration that is public only
/// because F# has no other default be reshaped in place?", when it has
/// one. `Some true` — `"publicApi": false`, or `"apiChanges": true`, both
/// of which open it. `Some false` — `"publicApi": true`, an explicit no,
/// which a project the host would otherwise open (an executable that
/// serializes its own types, or loads plugins by reflection) uses to opt
/// back out. `None` — the config is silent, and the host decides.
///
/// Deliberately NOT a licence for cross-file rewrites: those ask a
/// different question — whether the fix may edit files other than the one
/// being analyzed — and keep their own gate.
let publicSurfaceSetting (analyzedFile: string) : bool option =
    let config = configFor analyzedFile

    if config.ApiChanges then
        Some true
    else
        config.PublicApi |> Option.map not

/// The setting alone, with a silent config reading as "keep the gate
/// closed" — the answer for a caller that knows nothing about the
/// compilation.
let publicSurfaceOpen (analyzedFile: string) : bool =
    publicSurfaceSetting analyzedFile |> Option.defaultValue false

/// Does the repository ask for `--api-changes` on every run, cross-file
/// rewrites included?
let apiChangesFor (analyzedFile: string) : bool = (configFor analyzedFile).ApiChanges

/// The single entry point the analyzers use: is this rule enabled for this file?
/// Build-generated sources (AssemblyInfo.fs, AssemblyAttributes.fs under
/// obj/) are not the user's code; no rule has business flagging them.
/// Neither is a codegen output living in src/ proper: files opening with
/// the conventional `<auto-generated` marker (Myriad, T4, protobuf and
/// friends all emit it) are skipped wherever they sit. The header sniff
/// reads a few lines once per path and caches the verdict for the process
/// lifetime — unlike the config caches there is no revalidation, so an
/// editor session sees a header added mid-session only after restart. A
/// header appearing on a live file is rare enough not to pay a timestamp
/// check on every rule of every keystroke for it.
let private generatedHeaderCache = ConcurrentDictionary<string, bool>()

/// Markers a generator leaves behind. The XML-comment form is the
/// convention, but plenty of tools write their own prose: SQLProvider's
/// AssemblyInfo.fs opens "// Auto-Generated by FAKE; do not edit", which
/// the `<auto-generated` sniff missed entirely — and so the sweep edited
/// a file FAKE rewrites on every build.
let private generatedMarkers =
    [ "<auto-generated"
      "auto-generated"
      "autogenerated"
      "generated by"
      "do not edit" ]

/// And the attribute forms, which sit on a declaration rather than in a
/// header: `[<GeneratedCode(...)>]` is what a code generator stamps onto
/// what it emits, and `[<CompilerGenerated>]` likewise.
let private generatedAttributes =
    [ "[<GeneratedCode"; "[<CompilerGenerated"; "[<assembly: GeneratedCode" ]

let private lineDirective =
    Text.RegularExpressions.Regex(@"^#\s*\d+\s+""", Text.RegularExpressions.RegexOptions.Compiled)

let private hasGeneratedHeader (path: string) =
    generatedHeaderCache.GetOrAdd(
        path,
        fun p ->
            try
                // 30 lines rather than 5: a header marker sits at the top,
                // but an attribute follows the namespace and opens
                let head = File.ReadLines p |> Seq.truncate 30 |> Seq.toList

                head
                |> List.exists (fun line ->
                    generatedMarkers
                    |> List.exists (fun m -> line.Contains(m, StringComparison.OrdinalIgnoreCase)))
                || head
                   |> List.exists (fun line ->
                       generatedAttributes
                       |> List.exists (fun a -> line.Contains(a, StringComparison.OrdinalIgnoreCase)))
                // a `# 3 "lex.fsl"` line directive is what fslex and fsyacc
                // leave in their output (no auto-generated banner at all);
                // fantomas's generated lexer carried 14 notes and every
                // fix there is lost at the next build
                || head |> List.exists (fun line -> lineDirective.IsMatch line)
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false
    )

let isGeneratedFile (analyzedFile: string) =
    analyzedFile.Contains @"\obj\"
    || analyzedFile.Contains "/obj/"
    || hasGeneratedHeader analyzedFile

/// Path patterns never analyzed unless the repository says otherwise:
/// generated or EXTERNAL code that a compilation nonetheless includes —
/// paket vendors whole source files into paket-files, and fixing someone
/// else's vendored code is churn nobody asked for (and re-analyzing it
/// in every project that includes it is time nobody has).
let private defaultIgnoredSegments = [ "paket-files"; ".paket"; "node_modules" ]

/// Does the path fall under an ignored pattern — a built-in default or a
/// config `ignorePaths` entry (additive)? A bare name matches as a whole
/// path SEGMENT; an entry containing a slash matches as a normalized
/// substring; an entry containing `*` is a glob (`*` within a segment,
/// `**` across segments: `*.g.fs`, `src/generated/**`).
let private globCache =
    ConcurrentDictionary<string, Text.RegularExpressions.Regex>()

let private globRegex (pattern: string) =
    globCache.GetOrAdd(
        pattern,
        fun p ->
            // split first, so only the literal text between wildcards is
            // ever regex-escaped: a** b*.fs -> "a" ".*" "b" "[^/]*" ".fs"
            let translated =
                p.Split "**"
                |> Array.map (fun acrossSegments ->
                    acrossSegments.Split '*'
                    |> Array.map Text.RegularExpressions.Regex.Escape
                    |> String.concat "[^/]*")
                |> String.concat ".*"

            Text.RegularExpressions.Regex($"(^|/){translated}($|/)", Text.RegularExpressions.RegexOptions.Compiled)
    )

let isIgnoredPath (analyzedFile: string) : bool =
    let normalized = analyzedFile.Replace('\\', '/').ToLowerInvariant()
    let segments = normalized.Split '/'

    let matches (pattern: string) =
        let p = pattern.Replace('\\', '/').ToLowerInvariant().Trim '/'

        if p.Contains '*' then (globRegex p).IsMatch normalized
        elif p.Contains '/' then normalized.Contains p
        else Array.contains p segments

    defaultIgnoredSegments |> List.exists matches
    || (configFor analyzedFile).IgnorePaths |> List.exists matches

/// Codes the apply tool's run explicitly asked for — the ones TYPED in
/// --codes, never a --categories expansion (a category is a filter, not
/// an ask). An explicit ask turns a rule on even when it is default-off
/// or config-disabled — naming it outranks defaults.
let private forcedOn (code: string) (analyzerName: string) =
    match Environment.GetEnvironmentVariable "FSREF_FORCE_CODES" with
    | null
    | "" -> false
    | s ->
        s.Split ','
        |> Array.exists (fun c ->
            let c = c.Trim()

            c.Equals(code, StringComparison.OrdinalIgnoreCase)
            || c.Equals(analyzerName, StringComparison.OrdinalIgnoreCase))

/// A rule's numeric knob from the effective configuration, falling back
/// to the rule's own default. Looked up under the rule CODE first, the
/// analyzer name second, both case-insensitive.
let parameterInt (analyzedFile: string) (code: string) (analyzerName: string) (knob: string) (fallback: int) : int =
    let parameters = (configFor analyzedFile).Parameters
    let knob = knob.ToLowerInvariant()

    let lookup (key: string) =
        parameters.TryFind(key.ToLowerInvariant()) |> Option.bind (Map.tryFind knob)

    lookup code
    |> Option.orElseWith (fun () -> lookup analyzerName)
    |> Option.defaultValue fallback

/// A rule's on/off knob. Written as a JSON bool or as 0/1 - both land in
/// the same map - and looked up exactly like `parameterInt`.
let parameterBool (analyzedFile: string) (code: string) (analyzerName: string) (knob: string) (fallback: bool) : bool =
    parameterInt analyzedFile code analyzerName knob (if fallback then 1 else 0)
    <> 0

/// `task { }` blocks the COMPILER said fell back to a dynamic state machine,
/// as file path -> the lines its `task`/`backgroundTask` keywords sit on.
///
/// FS3511 is emitted at codegen, so no analyzer can see it — but the apply
/// tool builds the project before it rewrites anything, and the warning
/// carries the builder's own position ("R.fs(7,5): warning FS3511"). That
/// makes it advice a rule can act on: the tail extraction invents a
/// `runTail` that earns its keep only where the fallback is real, so it can
/// wait to be told. An empty map (the IDE, or a build that compiled nothing
/// because it was already up to date) simply means no site is known.
let private dynamicFallback =
    System.Collections.Concurrent.ConcurrentDictionary<string, Set<int>>(StringComparer.OrdinalIgnoreCase)

let setDynamicFallbackSites (sites: (string * int) seq) =
    for file, line in sites do
        let key = System.IO.Path.GetFullPath file

        dynamicFallback.AddOrUpdate(key, Set.singleton line, (fun _ existing -> existing.Add line))
        |> ignore

/// Lines in this file where the compiler reported FS3511.
let dynamicFallbackLines (analyzedFile: string) : Set<int> =
    let key =
        try
            System.IO.Path.GetFullPath analyzedFile
        with _ -> // fsharpanalyzer: ignore-line FR0055
            analyzedFile

    match dynamicFallback.TryGetValue key with
    | true, lines -> lines
    | _ -> Set.empty

/// The repository root above a file: the nearest ancestor holding `.git` or
/// a solution. None when the file is not inside one.
let private repositoryRoot (analyzedFile: string) =
    let rec up (dir: System.IO.DirectoryInfo) =
        if isNull dir then
            None
        elif
            System.IO.Directory.Exists(System.IO.Path.Combine(dir.FullName, ".git"))
            || System.IO.File.Exists(System.IO.Path.Combine(dir.FullName, ".git"))
            || System.IO.Directory.EnumerateFiles(dir.FullName, "*.sln*") |> Seq.isEmpty |> not
        then
            Some dir.FullName
        else
            up dir.Parent

    try
        up (System.IO.FileInfo(System.IO.Path.GetFullPath analyzedFile).Directory)
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

/// Every test source of the repository, read once: (path, text) for each
/// `.fs`/`.fsx` whose path names a test (`isTestSourcePath`), build output
/// excluded.
let private testSources =
    System.Collections.Concurrent.ConcurrentDictionary<string, (string * string)[]>(StringComparer.OrdinalIgnoreCase)

/// A path below the root, forward-slashed and in its own case, for the "is
/// this a test file" question. Asked of the ABSOLUTE path, a repository
/// under `C:\git\contest-app` or `...\latest\...` would make every file a
/// test source and no file a production one.
let private relativeTo (root: string) (p: string) =
    let full = p.Replace('\\', '/')
    let rootSlash = root.Replace('\\', '/').TrimEnd('/') + "/"

    if full.StartsWith(rootSlash, StringComparison.OrdinalIgnoreCase) then
        full.Substring rootSlash.Length
    else
        full

let private relativeLower (root: string) (p: string) = (relativeTo root p).ToLowerInvariant()

let private testWords = [ "test"; "tests"; "spec"; "specs" ]

/// Is this path (relative to the repository, any separator) a TEST source?
///
/// `test`, `tests`, `spec` or `specs` as a WORD of some segment: a whole
/// directory (`tests/`, `Spec/`), or bounded inside a name by a separator
/// or a camel-case rise — `Foo.Tests.fs`, `FooTests.fs`, `Foo.Spec.fs`,
/// `test_helpers.fs`, `TestHelpers.fs`, `Lib.Tests/`. Never a mere
/// substring: `Contest`, `LatestPrices`, `Attestation`, `ProtestHandler`
/// are production code, and a note that named one of them as the test
/// pinning its own failure text was simply wrong. Case-insensitive on the
/// word, so the camel rule reads the ORIGINAL case.
let isTestSourcePath (relativePath: string) =
    let isWordAt (segment: string) (i: int) (word: string) =
        let j = i + word.Length

        String.Compare(segment, i, word, 0, word.Length, StringComparison.OrdinalIgnoreCase) = 0
        // bounded on the left: the start, a non-identifier character, or
        // a camel-case rise (`FooTests`: lower before, upper here)
        && (i = 0
            || not (Char.IsLetterOrDigit segment.[i - 1])
            || (Char.IsUpper segment.[i] && not (Char.IsUpper segment.[i - 1])))
        // and on the right: the end, a non-identifier character, or the
        // next word's rise (`TestHelpers`)
        && (j = segment.Length
            || not (Char.IsLetterOrDigit segment.[j])
            || (Char.IsUpper segment.[j] && not (Char.IsUpper segment.[j - 1])))

    relativePath.Replace('\\', '/').Split('/')
    |> Array.exists (fun segment ->
        testWords
        |> List.exists (fun word ->
            let rec scan (from: int) =
                if from > segment.Length - word.Length then
                    false
                else
                    match segment.IndexOf(word, from, StringComparison.OrdinalIgnoreCase) with
                    | -1 -> false
                    | i -> isWordAt segment i word || scan (i + 1)

            scan 0))

let private readTestSources (root: string) =
    testSources.GetOrAdd(
        root,
        fun root ->
            try
                System.IO.Directory.EnumerateFiles(root, "*.fs*", System.IO.SearchOption.AllDirectories)
                |> Seq.filter (fun p ->
                    let lower = relativeLower root p

                    (lower.EndsWith ".fs" || lower.EndsWith ".fsx")
                    && isTestSourcePath (relativeTo root p)
                    && not (
                        lower.Contains "/obj/"
                        || lower.Contains "/bin/"
                        || lower.Contains "/node_modules/"
                    ))
                |> Seq.choose (fun p ->
                    try
                        Some(p, System.IO.File.ReadAllText p)
                    with _ -> // fsharpanalyzer: ignore-line FR0055
                        None)
                |> Array.ofSeq
            with _ -> // fsharpanalyzer: ignore-line FR0055
                [||]
    )

/// Every test source in this file's repository that carries the literal
/// VERBATIM, quotes included: (path, text). The text of an exception is
/// observable behaviour, and a test pinning it is the observer: enriching
/// the message under such a test breaks the test (Fuuga's
/// DraftAndRefineTests, FSharp.Data's XmlProvider), and nothing at build
/// time says so.
let testFilesMentioning (analyzedFile: string) (literal: string) : (string * string) list =
    match repositoryRoot analyzedFile with
    | None -> []
    | Some root ->
        // the throw itself is a mention, so the file being analysed can
        // never be the test pinning it - a helper under `tests/` that
        // throws the text is the one place this scan is asked about
        let self =
            try
                System.IO.Path.GetFullPath analyzedFile
            with _ -> // fsharpanalyzer: ignore-line FR0055
                analyzedFile

        readTestSources root
        |> Array.filter (fun (path, text) ->
            text.Contains literal
            && not (String.Equals(System.IO.Path.GetFullPath path, self, StringComparison.OrdinalIgnoreCase)))
        |> List.ofArray

/// The string literals thrown by `failwith` in the repository's PRODUCTION
/// sources, read once. Projects are analysed in name order, not dependency
/// order, so a test project can come before the code it tests: the assertion
/// side cannot wait to be told which messages this run enriched. Instead it
/// asks the question the other way round - is the text I pin a production
/// throw at all? - which gives the same answer whichever project goes first.
let private productionThrows =
    System.Collections.Concurrent.ConcurrentDictionary<string, string list>(StringComparer.OrdinalIgnoreCase)

let productionFailwithLiterals (analyzedFile: string) : string list =
    match repositoryRoot analyzedFile with
    | None -> []
    | Some root ->
        productionThrows.GetOrAdd(
            root,
            fun root ->
                try
                    // a plain string literal handed straight to failwith
                    let pattern =
                        System.Text.RegularExpressions.Regex(@"\bfailwith\s+(""(?:[^""\\]|\\.)*"")")

                    System.IO.Directory.EnumerateFiles(root, "*.fs", System.IO.SearchOption.AllDirectories)
                    |> Seq.filter (fun p ->
                        let lower = relativeLower root p

                        not (isTestSourcePath (relativeTo root p))
                        && not (
                            lower.Contains "/obj/"
                            || lower.Contains "/bin/"
                            || lower.Contains "/node_modules/"
                        ))
                    |> Seq.collect (fun p ->
                        try
                            pattern.Matches(System.IO.File.ReadAllText p)
                            |> Seq.map (fun m -> m.Groups.[1].Value)
                        with _ -> // fsharpanalyzer: ignore-line FR0055
                            Seq.empty)
                    |> Seq.distinct
                    |> List.ofSeq
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    []
        )


/// The effective suppression-comment policy for a file:
/// "all" | "no-correctness" | "none".
let suppressionPolicy (analyzedFile: string) : string = (configFor analyzedFile).Suppressions

let isRuleEnabled (analyzedFile: string) (code: string) (analyzerName: string) : bool =
    not (isGeneratedFile analyzedFile)
    && not (isIgnoredPath analyzedFile)
    && (forcedOn code analyzerName
        || isEnabledIn (rulesFor analyzedFile) code analyzerName)

// Application-control reputation nudge: this comment exists to vary the
// build hash when a freshly built analyzer DLL gets transiently blocked.
