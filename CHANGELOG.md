# Changelog

The analyzers package, the `fsharp-refactor` tool and both editor extensions share one version. The NuGet packages carry the notes of the last six versions; this file keeps every one.

## 0.8.39

- A script's `#r` of the project is redirected to the sources only where the compiler reads it: `#if`/`#elif`/`#else` nesting and `!`, `&&`, `||` in conditions are followed with the run's symbols (and `INTERACTIVE`), so a `#r` in the half that `--define PACKAGE` switches off no longer makes the script a consumer, and a `#r` under `#elif` gets the right hint.
- `--define <symbols>` (repeatable, `;`-separated; `--define:A`, `-d:A`) and `"defines"` in fsharprefactor.json define preprocessor symbols for the whole run: every MSBuild the run starts gets them through the `DefineConstants` environment variable, which projects add to (a `-p:DefineConstants` global property would replace DEBUG, TRACE and the project's own constants), and every script and `--parse-only` compilation through `--define:`. Code under `#if LOCAL_BUILD` is analysed, fixed and verified; the MCP server keeps its startup symbols and `analyze` takes `defines`.
- A script whose `#r` of the project's built assembly sits under an `#if` the run does not define says which symbol would switch it on and how to pass it, instead of only that the reference did not resolve.
- A script whose live `#r` of the project's assembly names a build that does not exist (`bin/Release/...` when the run built Debug, another framework's folder) is read against the project's sources anyway, instead of being written off because FCS dropped the missing file: the reference is answered by the project's own compilation either way.

## 0.8.38

- `--api-changes` typechecks only the scripts whose `#load` chain can reach the project's sources, read from their text first; a tree of example scripts no longer stalls the run in silence, and both script phases say what they are waiting on.
- A git worktree nested inside its own repository (`.claude/worktrees/...`) is no longer swept as more of the tree; a worktree beside its repository and a submodule still are.

## 0.8.37

- FR0118 passes the token only to work that is waited for (`do!`, `let!`, `return!`, `match!`, returned, blocked on, combined); fire-and-forget calls (`|> ignore`, `|> Async.Start`, a bare statement, a store) stay as written.

## 0.8.36

- FR0015 numbers a function's second regex (`postcodeRegex2`) before falling back to the function's whole name (GitHub PRs #7, #8).
- FR0168 takes a user member named like a throwing BCL one (`Get`, `First`, `Last`) as a read and offers the TryParse fix; BCL and FSharp.Core throwing names and user `Parse`/`Single`/indexers still keep the try.
- Tests: a failing typecheck or parse assertion lists the compiler errors; the README check accepts CRLF; legacy .NET Framework tests run on Windows only.
- Packaging: every pack writes a `.snupkg` symbol package, the analyzers package's pdbs included.

## 0.8.35

- FR0147 no longer adds an `open` that also reaches another namespace through a partial path (`open Core` opening Microsoft.FSharp.Core, FS0893); it notes it instead (GitHub issues #1-#6).
- FR0162 stays quiet on a slot that is reset, and a store inside a lambda under the emptiness test no longer counts as guarded.
- FR0035 leaves module-level literals under 8 elements alone and converts those under 16 through the HashSet companion, not an F# Set; `{ "FR0035": { "minElements": 8, "setMinElements": 16 } }` moves the floors.
- Fable projects: FR0130 takes only private and internal values; FR0038 drops its culture note; JavaScript-bound projects get no FR0162 note and an FR0055 note without the cancellation claim; browser-bound projects get no FR0121 note for `DateTime.Today`/`DateTime.Now`.
- FR0015 names a hoisted regex after its binding (`isPostcode` → `postcodeRegex`), falls back to the whole name, reuses a pattern already hoisted in the same module (not where a local of that name or another `#if` intervenes), numbers further regexes in the same pass and inserts hoists at one point together.
- FR0168's success binder is `parsed` or another unused name; a trailing `try` after `else`/`then`/`->`/`=` moves to its own lines only where layout allows; an unannotated Parse argument is written `(s: string)`.
- FR0164 counts only a `let mutable` whose scope encloses the loop condition; FR0013 stays quiet where `.editorconfig` sets `fsharp_space_before_lowercase_invocation = false`, unless `--codes` or fsharprefactor.json names it.
- Tool: `--codes` and `--categories` skip the other rules' analyzers entirely; later passes re-sweep only the files the previous pass changed and those compiled after them; FR0006's active patterns for one match go in one pass.
- Tool output: one line per finding with its edit count, and each pass totals "N edit(s) applied, from M finding(s)".
- Deep-stack workers run each job under the caller's execution context, so a `--codes` run no longer switches rules off for later in-process runs (tests, `--mcp`).

## 0.8.34

- FR0172 names a tail read beside the second element as `h :: (s :: _ as t)` and declines arms where moved text would push lines offside or change their reading.
- FR0168 keeps the try when the Parse argument can throw on its own (index, `Substring`, conversion, `.Value`/`.Head`, downcast, `List.head`/`Option.get`/`Map.find`/`Map.pick`); getters, user calls and `Trim` still fix; `TimeSpan` joins the overflowing Parse types.
- FR0170 keeps the loop only where it sees the dictionary written before a read (receiver handed on or rebound, a store through an alias or same-file setter, a same-file function touching a dictionary, a `yield`/`let!`/`do!` in `seq`/`task`); otherwise it fixes.
- FR0060's eager-filter probe takes a dotted read as total unless a segment is known to throw (`.Value`, `.Head`/`.Tail`, an indexer, `.Force()`, `.Span`).
- FR0166's length guard proves the cut for an immutable value and for a `let mutable` not written between the guard and the cut.
- FR0167 and FR0173 spell `FSharp.Core.Operators.nonNull` and `FSharp.Core.Operators.max`, which user definitions cannot capture.
- FR0164's RemoveAll fix falls back to the snapshot for a condition reading a `let mutable` or a Span, or a loop holding a comment.
- Analyzers await their deep-stack worker instead of blocking a thread-pool thread, fixing a deadlock on large projects.

## 0.8.33

- About thirty rules no longer rescan the whole file per candidate: on an 18k-line file FR0169, FR0092, FR0055 and FR0050/FR0107 drop from seconds to milliseconds; messages and fixes unchanged.
- Dry-run sweeps of large projects run 1.7x to 2.5x faster.
- The api pass ignores a build-order-only `ProjectReference` (`ReferenceOutputAssembly` false) unless the dll is also referenced directly.
- Solution end-to-end tests carry `Category=Slow`; `dotnet test --filter "Category!=Slow"` skips them.

## 0.8.32

- FR0173 accepts a multi-line mapper only as a lambda whose body starts on its own line.

## 0.8.31

- FR0035 turns a list whose element can carry a float into a `Set` only when every element is a written-out non-NaN constant.
- FR0167's String twins go through `nonNull` on FSharp.Core 9+, so a sweep applies them.
- FR0041 sweeps `Array.contains v arr` on `int[]`/`int64[]` to `Enumerable.Contains(arr, v)`; the aggregations stay notes.
- FR0174 sweeps a nullable column of an exact type compared by `=`/`<`/`<=`/`>`/`>=` with a non-null value outside any `not`.
- FR0071 no longer hoists a division by a signed integral `-1` or anything in a file under `open Checked`.

## 0.8.30

- New FR0174 (performance, fix): filter in the query, not after `ToList()` - moves `Where`/`Select` of value columns before the copy; a sweep takes integer, bool, enum and Guid comparisons, the editor the string, decimal, date and nullable ones; the `pipelines` knob (default off) covers `|> Seq.toList |> List.filter`.
- FR0049 takes a `.Result` behind an `IsCompleted`/`IsFaulted`/`IsCanceled` probe in the same condition, or on the `Task.WhenAny` winner, as complete.
- FR0173 sweeps every count as `Array.init (max 0 n) f`, moves a multi-line mapper with its lines, and counts an inclusive bound as `n + 1`.
- Silent rewrites closed in FR0004, FR0005, FR0006, FR0010, FR0021, FR0023, FR0026, FR0029, FR0034, FR0035, FR0049, FR0050, FR0053, FR0060 (total predicates only), FR0071, FR0075, FR0100, FR0118, FR0119, FR0160, FR0166, FR0170 and FR0157 (record-field rewrites now editor-only).
- Non-compiling fixes closed in FR0009, FR0015, FR0016, FR0018, FR0022, FR0030, FR0031, FR0059, FR0069, FR0099, FR0101, FR0123 and FR0137; FR0032/FR0047 dispose wrappers before their sources.
- Tool: a non-UTF-8 file without BOM is read in the system code page and written back byte for byte; every verification build runs; a timed-out check puts back the whole run; a put-back takes the files rewritten with it; an analyzer error in a referencing C# project counts as a code error.

## 0.8.29

- New FR0173 (performance, fix): map over a range becomes `init` - `[| 0 .. n - 1 |] |> Array.map f` → `Array.init n f`, 2x faster on half the allocation; a sweep applies it only where the count is provably non-negative.
- New FR0172 (idiom, fix): list index reads become a cons pattern - `| itms -> g itms.[0]` → `| itmsHead :: _ -> g itmsHead` where earlier arms exclude the short lists.
- FR0156 also converts a `let mutable` list fed by `xs <- xs @ [ e ]` (250x faster) or by `e :: xs` read through `List.rev`; FR0050 leaves that shape alone and FR0051's note names the list expression.
- FR0071 no longer hoists an array literal out of a loop; list literals still hoist.
- FR0015's per-call hoist is a knob: `{ "FR0015": { "perCall": false } }` keeps only loop hoists (on by default).
- Property suite runs generated programs before and after each fix and compares their traces; `FSREF_EXECUTION_RUNS` sets the count (25 by default, 60 in CI).
- PerfClaims gains cases for FR0168, FR0170 and FR0171.

## 0.8.28

- New FR0168 (performance, fix): Parse in a try becomes TryParse - `try T.Parse s with _ -> 0` → `match T.TryParse s with`; FR0055 stands down there.
- New FR0169 (correctness, note): a `seq` enumerated twice on one path.
- New FR0170 (performance, fix): iterate dictionary pairs, not keys - `for k in d.Keys do ... d.[k]` → `for KeyValue(k, v) in d do`.
- New FR0171 (performance, fix): UTF-8 literal as byte string - `Encoding.UTF8.GetBytes "OK"` → `"OK"B`.
- Guards ported from CSharp.Refactor: FR0004 needs a pure source before an early-stopping consumer; FR0016/FR0070 refuse structs that are boxed, locked, null-tested, implement an interface or exceed 32 bytes; FR0075/FR0032 skip `HttpClient`, `HttpRequestMessage`, `SemaphoreSlim`, `ManualResetEventSlim` and `Task`; FR0151 knows `AggregateException`, `SqlException` and `FileNotFoundException`.
- FR0037's HttpClient note and FR0165 stay quiet in test files; FR0142 accepts TUnit.
- FR0015 hoists a Regex from any function body, not only loops; FR0118 adds `ct.ThrowIfCancellationRequested()` to an unobserved loop; FR0164's filter shape becomes `RemoveAll`.

## 0.8.27

- New correctness rules, twins of CR0160-CR0171: FR0159 integer division before widening to float; FR0160 rethrow loses the caught exception; FR0161 mutating a struct copy from a property; FR0162 racy check-then-assign on a module mutable; FR0163 unreferenced `System.Threading.Timer` gets collected; FR0164 collection edited while iterating over it; FR0165 local and UTC `DateTime` mixed.
- FR0159's literal-operand and product-dividend cases are editor-only unless `{ "FR0159": { "all": true } }`.
- FR0055 notes (and offers to rewrite) a narrow catch used as TryParse; FR0118 notes an awaiting loop that never observes its token; FR0123 notes lock waits with no `finally` release and moves the release into one.
- New FR0166 (performance): cut-and-compare becomes ordinal `StartsWith`/`EndsWith`.
- New FR0167 (performance): walk the string, not `ToCharArray()`.
- FR0106 also takes `StringBuilder.Append` and `TextWriter.Write`/`WriteLine`; FR0106, FR0166 and FR0167 fire only where `String` has span overloads (netstandard2.1, .NET Core).
- FR0015 takes CR0108's shapes: `Regex.Match(...).Success` and `Matches(...).Count` tests become `Contains`/`StartsWith`, a literal `Regex.Split` becomes `String.Split`.
- FR0066 no longer counts a hole filled from a constant as a value; FR0127 treats a `123456` literal as a made-up key; FR0012 fires beside boolean operators (`isNull x || flag`).
- Fixes: FR0065's comment-out placement, FR0080 on strings inside block comments, `[<TestCaseSource>]` as a test marker, the VS extension's tagger (FS0760); the property suite now typechecks its generated code.

## 0.8.26

- New property-based suite, `tests/FSharp.Refactor.PropertyTests` (FsCheck), checking parse, fixed-point and truth-table invariants.
- FR0012, FR0013, FR0094, FR0097, FR0098, FR0108 and FR0109 add a space where a bare replacement would glue onto the next token (`bwith`).
- FR0012's purity probe reads interpolated-string parts by case.

## 0.8.25

- Help links in SARIF and the HTML report point at the rule's own Rules.md section (`Rules.md#fr0103--idiom`).
- The VSIX lists a content type for every part again, so it installs as a valid package.

## 0.8.24

- Tool: the build-configuration probe reads compile items by their spelled path, fixing extra Release passes on case-sensitive file systems.
- Tool: waits at most 10 s for a finished child build's output and runs child builds with MSBuild node reuse off, fixing hangs.

## 0.8.23

- FR0157 keeps a match with a guarded catch-all, a `| null ->` arm or an ambiguous variable pattern, resolves constants by declaration, and deletes an unguarded dead `| null ->` arm.
- FR0156 refuses non-unit loop statements, delegate element types and Span reads; FR0158 stands down on a Span read or without a typed tree.
- FR0071 hoists only arithmetic, comparison and boolean operators over values no call in the loop changes (following same-file callees), `/` and `%` by a non-zero literal included.
- FR0050 spells `sum`/`sumBy` for floating accumulators only; FR0107 needs an effect-free predicate, following same-file predicates into their bodies.
- FR0004 keeps the eager copy before a lambda that mutates or names the source; FR0003 composes only stages with literal or immutable arguments.
- FR0044 rewrites to `reraise ()` only a binder of the whole exception; FR0118 leaves calls in `with` handlers and `finally` alone; FR0075 treats tasks and token sources handed on as in flight.
- FR0015 uses the ordinal `StartsWith` and keeps a regex ending in `$`; FR0039's fix is OrdinalIgnoreCase and keeps an existing StringComparison argument.
- FR0029 keeps a throwing `let` inside a task that leaves the file through a public or interface member.
- FR0110 spells a raising arm in a computation expression with `return`/`yield`; FR0055's IO-only narrowing needs the typed tree to agree; FR0142 keeps tests returning a value; FR0002 keeps matches calling the enclosing `let rec`.
- Map-fusion hints fuse only effect-free mappers; built-in hints stand down where the typed tree has errors; FR0012 without a typed tree stands down only inside computation expressions.
- Non-compiling fixes closed in FR0049 (taskify `return`), FR0013 (indexed application), FR0095, FR0147 and FR0155; the byref-like guard works again for seven rules.
- Tool: a verification build hitting the time cap puts fixes back as unverified, while a pre-existing failure identical with and without the fixes keeps them; referencing csproj/vbproj projects are built during verification; XML comments in project files are ignored.
- Tool: a throwing rule is reported and skipped (and counted in the exit code); abandoned typechecks are cancelled at the cap; private SDK environment is reset between checkouts.
- Config: root `"Hints": false` disables FR0012; the strings "true"/"false"/"on"/"off" count as booleans.
- VS extension: no writes to an exited sidecar, fixes pinned to the snapshot they were computed on, errors kept off the UI thread.

## 0.8.22

- FR0157's serializer guard also checks values passed to reflective serializers such as `JsonSerializer.Serialize`.
- FR0157's union takes the narrowest visibility of its slots, so a run without `--api-changes` never adds a public type.
- Two tests assuming Windows paths pass on Linux.

## 0.8.21

- Api pass: a failed in-memory check of a sibling project is confirmed by a real build before cross-project edits are put back, and the referenced project is rebuilt.
- FR0156 keeps parentheses that belong to an application (`Some(List.ofSeq acc)`).
- FR0157 never gives two unions in one file the same name.

## 0.8.20

- New FR0158 (idiom): index-walking while loop becomes a tail-recursive local function.
- New FR0156 (idiom): ResizeArray filled by `Add` becomes a list expression (20% faster); arrays only with `{ "FR0156": { "arrays": true } }`.
- New FR0157 (idiom): closed string-literal set becomes a `[<RequireQualifiedAccess>]` union; under `--api-changes` it sees referencing projects' call sites and keeps an exported signature behind an adapter.
- FR0154 is now a correctness rule and rewrites only the miss arm to `GetOrAdd`; a calling factory gets a `Lazy` hint, and Task/ValueTask/Async values a note only.
- Tool reads a compilation's symbol uses once, indexed, making FR0157's analysis a few seconds per project.

## 0.8.19

- A project branching on `#if DEBUG`/`RELEASE`/`TRACE` gets a second pass and a verification build in the other configuration, referencing projects included.
- FR0090/FR0091 call-site migration skips a function named inside a configuration region or in a string literal.
- The tool withholds any multi-line fix spanning a `#if`, `#else` or `#endif` line.

## 0.8.18

- The compiler-argument query no longer cleans the project, and the FS3511 harvest is cached under local app data, so an unchanged project builds incrementally.
- A multi-targeted project builds all frameworks in one parallel build and typechecks the next framework ahead on its own checker.
- A file whose only directives are INTERACTIVE/COMPILED is swept once across frameworks.
- A script sweep leaves `#load`ed project sources to their project.
- PerfClaims benchmarks the proposed FR0155 (`[<Sealed>]` on internal classes).

## 0.8.17

- A test project (xunit, NUnit, MSTest, Expecto) reshapes its declarations without `--api-changes` (FR0090, FR0091, FR0069, FR0093, FR0049).
- Project type providers are instantiated before `#r` scripts are read against .NET Framework references.
- FR0147 checks every bare name, AutoOpen values included, against what an open brings; locals are no clash; qualified union-case patterns are shortened too.
- FR0094 keeps parentheses inside a `_.` shorthand lambda; FR0029 leaves `return (* note *) value` in place.
- FR0035 uses the HashSet companion where the element type lacks `comparison`.
- FR0034, FR0009, FR0029, FR0142 and FR0049 stand down where a byref-like value (Span) would be captured.
- FR0142 no longer holds back a test for its own class's `static let mutable`.
- A typecheck is abandoned after 15 minutes (`FSREF_CHECK_MINUTES`).

## 0.8.16

- FR0034 spells a backticked option as the source does.
- Hint rules fire only where their left-side names resolve to FSharp.Core, sparing computation-expression custom operations such as `id`.
- FR0042 keeps a space between an operator and `$`.

## 0.8.15

- Tool: the alignment backstop (and FR0094/FR0013's `Text.alignmentHazard`) checks the offside anchors an edit moves, no longer withholding safe edits.
- FR0092's test-side loosening rides in the production fix as cross-file edits, and only for assertions on an exception's `Message`.
- FR0142 indents continuation lines correctly when a `let`'s expression starts on the next line.

## 0.8.14

- FR0094/FR0013 keep parentheses before an aligned next line, and the tool holds edits that would shift such a line.
- FR0111 indents `elif` continuation lines correctly; FR0011 and FR0130 leave bodies split by `#if` alone.
- FSharp.Core-gated rewrites honour the oldest FSharp.Core of every project compiling the file; a later failing compilation puts earlier rewrites back.
- FR0003 keeps a lambda under a constructor in a generic value; FR0008 leaves an attributed function's tuple alone.
- FR0116 moves every member out of a `let rec` group in one pass, in dependency order, with its comment, and its message carries its insert again.
- FR0012 spells `not (a || b || c)`; FR0132 skips code-like comments; FR0118 parenthesises a trailing lambda; FR0072 keeps cases on a deeper wildcard's line; FR0108 keeps the literal outside a bool-pinning context.
- FR0147 keeps a prefix whose head is a value, union case or active pattern in scope, and checks tupled calls against existing overloads.
- `FSREF_BUILD_MINUTES` raises the 15-minute build cap.
- Under `--api-changes` a script `#r`ing the built assembly is a call site migrated with the definition.
- The per-file second look no longer fails FS0222 on an executable's anonymous-module last file.

## 0.8.12

- New FR0154: ConcurrentDictionary `TryGetValue` plus store becomes `GetOrAdd`.
- FR0014 spells its miss arm `| false, _ ->`.
- FR0010, FR0012 and FR0034 withhold rewrites inside LINQ expression-tree arguments.
- FR0075 refuses escaping or self-active disposables, dropped tasks and builders without `Using`.
- Guard and output fixes in FR0002, FR0005, FR0006, FR0007, FR0010, FR0012, FR0015, FR0023, FR0029, FR0042, FR0043, FR0044, FR0049, FR0055, FR0072, FR0073, FR0101, FR0105, FR0111, FR0116, FR0130, FR0142, FR0147 and FR0151.
- FSharp.Core-gated rewrites (`Result.isOk`, `[<TailCall>]`) use the lowest FSharp.Core in obj/project.assets.json; `FSREF_MIN_FSHARP_CORE` overrides.
- Tool: typechecks from the project directory, restores sibling, script and linker files on put-back, keeps innocent fixes, reports the put-back count and exit reason, and gives FR0149, FR0150 and FR0153 their own switches.

## 0.8.11

- FR0147 notes, rather than inserts, an `open` whose extension members would capture a tupled call.
- FR0092 leaves a `failwith` alone when a test asserts its text; under `--api-changes` it enriches it and loosens the assertion to a prefix match.
- FR0015 hoists a Regex constructed with a literal pattern out of loops and collection-function lambdas, above any comment or doc block.
- `--api-changes` rewrites call sites in sibling projects of the same solution (FR0090, FR0091); InternalsVisibleTo friends are consulted.
- A cross-file suggestion is put back whole rather than half-applied.

## 0.8.10

- FR0085 keeps `new` where the bare name would resolve to a function (`new string(chars, i, n)`).
- FR0029's tail extraction is offered where the build reports FS3511 or the tail exceeds `tailLines` (raised from 10 to 40), silent otherwise; `extractTail` and `hoistReturnOnAsync` knobs; the return hoist guards a `use` and directive blocks.
- FR0065 offers to comment out a dead protocol or the whole setting; `dropLegacyProtocols` knob; protocol detection reads `[<Obsolete>]`.
- FR0028 no longer flags deliberate `Array.chunkBySize` batching.
- FR0015 rewrites a literal-pattern `Regex.Replace` to `String.Replace` where the two agree.
- Rule knobs accept JSON booleans.

## 0.8.8

- Fixes to a standalone script are no longer rolled back on every run.
- FR0127 ignores loopback connection strings; new FR0153 (note): credential in a `[<Literal>]` should be a development one.
- FR0144 offers `#r "nuget: Id, Version"` where the package is not on disk.
- Microsoft.Extensions.Logging.Abstractions pinned to 8.0.0.
- Rule descriptions moved from the README into Rules.md.

## 0.8.7

- FR0102 no longer fires on a receiver the loop rebinds; `Text.patBoundNames` now reads named-field, cons, record and optional patterns (RecursiveAppend, Reraise and QualifiedNames benefit too).
- QualifiedNames asks for referenced assemblies once per project.

## 0.8.4

- FR0121 quiet on expression-tree translator arms; FR0102 bounded indexes; FR0032 names a disposable base.
- FR0055 respects an acknowledging comment and keeps the log receiver in scope, with the IO-only catch limited to single-call bodies.
- FR0065 offers SHA-256 for MD5; FR0126 offers the Process argument list.

## 0.8.3

- New FR0147 (repeated qualified names become an open) and FR0146 (unparametrized SQL).
- Priority flag on likely-defect rules, notes-only review mode, workspace targets, HTML and CSV reports.
- Editor quick fixes for FR0032, FR0038, FR0046, FR0047, FR0055, FR0061, FR0062, FR0079, FR0089 and FR0105; alternative fixes as separate messages.
- FR0066 widened to helpers and one-hop strings; FR0120 and FR0124 cover Microsoft.Extensions.Logging, Serilog and Logary; FR0127 covers connection strings and tokens.
- FR0075 and FR0028 false positives removed.

## 0.8.2

- FR0130, FR0133 and FR0016 edit the companion signature file in step, or withhold the fix; FR0130 and FR0133 are on by default again.
- FR0004 judges the callback of a moved operation and moves nothing over a module-level or captured collection under a callback.
- FR0074 checks the flattened path head against everything in scope; FR0085 keeps `new` for a type name split across namespace fragments; FR0095 reads scope, not the whole file.

## 0.7.5

- FR0038, FR0039 and FR0106 keep their advice but drop the edit where the project offers no framework guard; FR0119 also where there is no guard at all.

## 0.7.4

- FR0140 parenthesises the value it moves into a construction.
- The all-frameworks arbiter counts errors both ways; the generated-file sniff reads thirty lines and knows prose and attribute markers.
- VS extension analyses only F# sources, never vendored, package or generated paths.
- `--parse-only` ignores framework-conditional DefineConstants.
- FR0039 pairs with the project's framework guard; FR0119 withholds a multi-edit fix that would need one.

## 0.7.3

- New FR0140: property assignments after construction fold into named-property construction.
- FR0141 stays silent inside async and task, and notes a while loop leaving through a boolean flag.
- FR0089 no longer flags the F# 6 multi-dimensional indexer `grid[0, 1, 2]`.
- FR0107 documentation corrected; SARIF reports name the published URL; 140 rules.

## 0.7.2

- New FR0139: Seq functions become Array ones where the typed tree proves an array.
- FR0030 no longer emits unparseable code for a range source; FR0119 binds only on a computation expression's statement spine.
- FR0029 tail extraction stops at a `use`; FR0005 cures the shape older versions wrote; FR0039 keeps backticked receivers.
- A failed verification no longer leaves kept fixes suppressed; benchmarks target .NET 10.

## 0.7.1

- The package carries both analyzer SDK builds in analyzers/dotnet/fs: `FSharp.Refactor.Analyzers.Ionide.dll` for stock Ionide (SDK 0.35.0) and the 0.37.2 build for the CLI and newer FsAutoComplete.
- New Visual Studio extension (VSIX): squiggles and light-bulb fixes in VS 2022-2026 from an FsAutoComplete sidecar.

## 0.7.0

- Under `--api-changes`, internal declarations migrate project-wide (FR0069 voption, FR0093 struct tuples, FR0049 taskify); never public or InternalsVisibleTo ones.
- FR0029 adds branch-return tail extraction and per-arm `match`/`match!` splitting; rules see inside `match!` arms.
- Solution runs order the narrowest target first, sweep shared directive-free files once, and skip typechecks of fully swept compilations.
- New rules: FR0132 trailing comments become XML docs; FR0133 five-word test names become double-backtick sentences; FR0134 UtcNow-fed DateTime fields become DateTimeOffset (opt-in); FR0135 markdown script comments become literate cells; FR0136 `Guid()` becomes `Guid.Empty`; FR0137 fuses consecutive map passes; FR0138 hand-rolled emptiness tests become `String.IsNullOrEmpty`; FR0139 Seq to Array where proven (2.3x on exists).
- FR0022 mines field names from case names and comments; FR0035 gains the module-level set quick fix; FR0039 fixes the method-call shape; FR0005 collapses no-op `return!` wrappers.
- The multi-pass loop warns on non-convergence, and a failed verification rolls back only the fixes at the error sites; 138 rules.

## 0.6.8

- A run prints its fixes and holds advisory notes to one summary line (`--notes` lists them, `--report` exports SARIF).
- FR0029 applies its own FS3511 advice; FR0049 rewrites blocking binds to `let!`/`do!` (sync-direction swaps opt-in).
- Suppression policy (`suppressions`: all/no-correctness/none, `--honor-suppressions`) and per-rule config parameters.
- New rules FR0117-FR0131: or-pattern folding, CancellationToken passing, awaitable twins, exception-less catch logging, DateTime pitfalls, invalid regexes, Monitor to lock, message-template logging, invisible Unicode, process sinks, API-key literals, obsolete crypto constructors, guard equality to patterns, `[<Literal>]` constants, `[<TailCall>]`.
- match/match!/function parity for arm rules; SHA1 editor alternatives on FR0065; 130 rules.
