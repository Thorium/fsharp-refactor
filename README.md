# FSharp.Refactor

> Let's remove parentheses from the internet

Functional refactoring suggestions for F#. 

- light bulb quick fixes in your editor
- command-line tool that applies them in bulk.

Suggestions are `Hint` severity: they mark an opportunity, not a defect, and
never gate your build.

---

# Using it

## Quick start

Nothing to configure — the tool reads your project, reports what it would
change, and only edits when you tell it to:

```bash
dotnet tool install --global fsharp-refactor
fsharp-refactor Your.fsproj --dry-run
```

That prints every fix it would make, with file and position, and writes
nothing. When the list looks right, drop the flag to apply them:

```bash
fsharp-refactor Your.fsproj
```

It refuses a compilation that does not already build, and fails loudly if applying
ever introduces an error. 

If you are ready to change public methods, add `--api-changes` to improve more.

#### For light bulbs while you type, see [VS Code / Ionide](#vs-code--ionide) and [Visual Studio](#visual-studio-20222026) IDE-plugin instructions below.

<img width="1136" height="215" alt="image" src="https://github.com/user-attachments/assets/cd4e3ed3-1ca6-40b6-bab4-da590e6d0410" />

#### For agentic scenarios the dotnet tool supports MCP.

Using the tool:
Point it at whatever you have — the kind is read off the path:

| | |
|---|---|
| `Your.fsproj` | one project |
| `Thing.fs` | one source file — its project is found and analysed, but only that file is edited |
| `build.fsx` | one script — no MSBuild step at all, so it starts instantly. A script with unresolvable references is not refused: the syntactic rules still run over it (an fsi-run script may reference things only the run supplies) |
| `Your.sln`, `Your.slnx` | every F# project the solution lists |
| `src/` | the solution in that directory, or the projects beneath it |
| `"src/**/*.fsproj"` | everything the glob matches |

## What it changes

Examples:

| | Before | After |
|---|---|---|
| Correctness | `let s = new FileStream(p, m)` | `use s = new FileStream(p, m)` |
| Correctness | `raise (Exception "boom")` | `failwith "boom"` |
| Performance | `s.Contains "x"` | `s.Contains 'x'` |
| Performance | `xs \|> Seq.toList \|> List.map f` | `xs \|> Seq.map f \|> Seq.toList` |
| Idiom | `match b with \| true -> 1 \| false -> 0` | `if b then 1 else 0` |
| Redundancy | `new StringBuilder()` | `StringBuilder()` |
| Redundancy | `[<SerializableAttribute>]` | `[<Serializable>]` |
| Diagnostics | `failwith "Error"` | `failwith $"Error, calling f with x: {x}"` |

A spread of what the 150-odd rules do — the full list is in
[Refactorings](#refactorings):

## Editor and CI setup

The analyzers ship as [`FSharp.Refactor.Analyzers`](https://www.nuget.org/packages/FSharp.Refactor.Analyzers).
The package is a development dependency: it only produces hints and quick
fixes — nothing from it flows into your compiled output.

NOTE: EVEN WHEN ADDING A NUGET REFERENCE, THIS ANALYSER WILL NOT COME TO OUTPUT PATH (BIN) AND WILL NOT BE PART OF YOUR PROJECT.

### VS Code / Ionide

**Easiest**: install the
[FSharp.Refactor VS Code extension](src/FSharp.Refactor.VsCode/README.md)
— it bundles the analyzers and (with your consent) wires them into
Ionide's settings globally, so every F# project gets the hints with no
per-project setup.

Or wire a single project by hand: reference the package from the project
you want analyzed:

```xml
<PackageReference Include="FSharp.Refactor.Analyzers" Version="*" PrivateAssets="all" />
```

then point Ionide at the restored analyzers in `.vscode/settings.json`:

```json
{
  "FSharp.enableAnalyzers": true,
  "FSharp.analyzersPath": [
    "~/.nuget/packages/fsharp.refactor.analyzers/<version>/analyzers/dotnet/fs"
  ]
}
```

replacing `<version>` with the version restore actually picked (the NuGet
cache always keys folders by version, so this one path cannot float; check
with `ls ~/.nuget/packages/fsharp.refactor.analyzers/`). On Windows the
cache lives under `%USERPROFILE%\.nuget\packages`. Suggestions
appear as `Hint`-severity diagnostics with a light-bulb one-click fix.

The package ships the analyzers built against TWO FSharp.Analyzers.SDK
versions side by side — `FSharp.Refactor.Analyzers.Ionide.dll` for SDK
0.35.0 (what stock Ionide's FsAutoComplete bundles, 7.31.x and earlier)
and `FSharp.Refactor.Analyzers.dll` for SDK 0.37.2 (the CLI, and
FsAutoComplete 0.84+). The SDK loads only the assembly matching its own
version and logs a skip line for the other, so every host picks the one
it can use and no configuration choice is needed.

**If no suggestions appear**, open Output → "F# Language Service": it
names the analyzer dlls it scanned and how many analyzers loaded, and a
version-pairing skip is spelt out there rather than surfacing in the
editor.

### Visual Studio 2022–2026

Install the
[FSharp.Refactor Visual Studio extension](src/FSharp.Refactor.Vsix/README.md)
([user-facing overview](src/FSharp.Refactor.Vsix/MarketplaceOverview.md)):
squiggles and `Ctrl+.` quick fixes in full Visual Studio, analyzed
through an FsAutoComplete sidecar. One prerequisite:
`dotnet tool install -g fsautocomplete`.

### CLI / CI

```bash
dotnet tool install --global fsharp-analyzers
fsharp-analyzers --project src/YourProject.fsproj --analyzers-path ~/.nuget/packages/fsharp.refactor.analyzers/<version>/analyzers/dotnet/fs --code-root . --report analysis.sarif
```

`fsharp-analyzers` is the analyzer HOST, and it is the dotnet tool you
install. This package is not a tool: it is a library of analyzer assemblies
the host loads, so it is passed as a directory rather than installed. That
directory sits in the NuGet cache because an analyzer package deliberately
has no `lib/` folder and is marked a development dependency — a
`PackageReference` therefore puts nothing in your `bin`, and after a restore,
the cache is where the assemblies live. `--analyzers-path` takes any folder
holding them and searches it recursively.

The CLI only REPORTS; it never edits your files, which is what you want in
CI (SARIF output works in GitHub code scanning). To apply the fixes, use our
own tool below. Individual rules can be turned off per repository with a
`fsharprefactor.json` — see [Configuration](#configuration) below.

### Applying fixes from the command line

The [`fsharp-refactor`](https://www.nuget.org/packages/fsharp-refactor)
dotnet tool applies the quick fixes directly to your files:

```bash
dotnet tool install --global fsharp-refactor
fsharp-refactor Your.fsproj [--dry-run] [--codes FR0002,FR0031] [--api-changes] [--jobs 4] [--max-passes 5]
```

(or from this repository:
`dotnet run --project src/FSharp.Refactor.Tool -c Release -- Your.fsproj ...`)

For a project it takes the exact compiler arguments from MSBuild; for a
script FCS resolves the references itself and MSBuild never runs. Either
way it then runs every analyzer, applies non-overlapping fixes bottom-up,
and re-analyzes until a pass applies nothing — a fix can enable further
fixes. It refuses a compilation that already has errors, and fails loudly
if applying ever introduces one.

| Flag | |
|---|---|
| `--dry-run` | Report only: lists every fix it would make, with file and position, and writes nothing. Rewriting is never implicit — drop the flag to let it edit. |
| `--codes FR0002,FR0031` | Restrict the run to chosen rules. |
| `--categories <list>` | Restrict the run to kinds of rule: `correctness`, `performance`, `idiom`, `cosmetic`. Combined with `--codes` it narrows further, in either order. See [Someone else's codebase](#someone-elses-codebase). |
| `--jobs <n>` | Typecheck that many files at once (default 4, clamped to 2–4 by core count). Trades CPU for wall clock; because FCS reuses each file's prefix within one incremental build, the gain peaks around 4 and reverses if pushed higher. `--jobs 1` is the sequential sweep. |
| `--framework <tfm>` | Analyse against this target framework instead of the narrowest one — see below. |
| `--max-passes <n>` | Fix-then-reanalyze iterations (default 5). |
| `--help` | The same list, from the tool itself (`-h` and `/?` also work). |
| `--api-changes` | Also apply the cross-file fixes described below. |
| `--no-if-defs` | Never emit `#if`/`#else`/`#endif` pairs for capability fixes on multi-targeted projects (see below). The fixes stay plain, and any the legacy frameworks reject are put back by the final build check. |
| `--report <file>` | Write every finding the run surfaced to a file; the extension picks the format. `.sarif` (or `.json`) is SARIF 2.1.0 — what GitHub code scanning renders as inline PR annotations; `.html` is a self-contained page with per-rule grouping, highlighted source, before/after fixes and category filters; `.csv` is one row per finding for a spreadsheet. Pairs naturally with `--dry-run` for a CI lint gate. See [CI setup](#ci-setup-sarif) below. A many-target run rewrites the report after every target, so a crash or a Ctrl-C an hour in still leaves what was found. Pointing the tool at a workspace of checkouts — a directory with no solution of its own whose sub-directories carry theirs, `C:git` say — analyses each checkout on its own (its solutions honoured, its `fsharprefactor.json` applied) into the one report, with paths relative to the workspace. |
| `--baseline <sarif>` | The ratchet: findings whose fingerprints appear in this earlier `--report` output are neither reported nor fixed — only what is NEW surfaces. Fingerprints hash the rule code, file name and normalized surrounding source, so they survive line shifts, other edits in the file, and different checkouts. Triage once, ratchet forever. |
| `--fail-on-findings` | Exit 3 when any finding survives the filters — the hard CI gate. The full exit contract: 0 clean, 1 analysis or apply failure, 2 usage error, 3 findings (only with this flag). |
| `--notes [on|off|only]` | `--notes` (or `--notes on`) lists fix-less advisory notes inline; `--notes only` is the review pass described next.  By default a run prints its FIXES — the product — and ends with one per-category note count (`41 advisory note(s) held: …`); SARIF (`--report`) and `--format json` always carry the notes in full, which is where CI and agents read them. |
| `--notes only` | A review pass: every rule runs, only the findings WITHOUT a fix are listed inline, and nothing is written. That is the 37 advisory rules (an em dash in [Rules.md](Rules.md)'s fix column) plus the cases where a fixing rule can only advise. `fsharp-refactor src/Your.fsproj --notes only --report notes.html` writes them as a page. |
| `--format json` | Machine-readable stdout: progress prose moves to stderr and the run's findings leave as one JSON document (code, severity, fixable, position, message, fingerprint, source snippet). The default output stays human-readable. |
| `--rules` | Print the rule catalog — code, category, enabled-by-default (honors `--format json`). |
| `--create-config` | Write a `fsharprefactor.json` of this build's defaults — every rule, every run-level key, one comment each — into the current directory, or into `<what>` when that is a directory. It changes nothing until you edit it, and never overwrites an existing config. |
| `--mcp` | Serve the tool as an MCP server over stdio (newline-delimited JSON-RPC, no extra dependencies): tools `analyze` (target, codes/categories, parseOnly, apply) and `list_rules`. One warm typechecker lives across calls, so the first analyze pays the reference parse and the rest answer from a hot cache — the economics agent loops need. |
| `--parse-only` | For a codebase that cannot COMPILE on this machine — a type provider needing its database, references that cannot restore. No MSBuild, no reference resolution: sources come straight from the fsproj's `<Compile>` items, and only the 55 of 113 analyzers that never consult the typechecker run (the typed rules are excluded outright, not trusted to self-silence). **It is not a substitute for a real run, and what survives is skewed the wrong way**: measured across the corpus, roughly a quarter of the correctness rules and a quarter of the performance rules still fire, against three quarters of the cosmetic ones — so a clean `--parse-only` says very little, and says least about the things worth knowing. Findings lost run to 38% on a typed-heavy codebase and under 10% on one the cosmetic rules dominate. Safety shifts accordingly: instead of a build, the gate is that a pass must not RAISE the compilation's error count over its baseline, and the usual parse-level protections (comment guard, overlap holds) still apply. Limitations: `#if` branches behind conditional or computed `DefineConstants` are not parsed, wildcard `<Compile>` globs are refused, and multi-framework passes collapse to one. Review the diff — the all-frameworks build arbiter is exactly what this mode does without. |

### CI setup (SARIF)

A dry run plus `--report` gives CI the full findings list without
touching a file; uploading the SARIF turns each finding into an inline
annotation on the pull request. Paths in the report are relative to the
repository that holds the target (the nearest `.git` above it), so the
tool may run from anywhere; each result carries the rule's description
and help link, the finding's own text with three lines of context, the
fix as a SARIF `fixes` entry (code scanning renders it as a suggested
change), a stable fingerprint, and the run's invocation record:

```yaml
  refactor-lint:
    runs-on: ubuntu-latest
    permissions:
      security-events: write     # required by upload-sarif
      contents: read
    steps:
      - uses: actions/checkout@v4
      - uses: actions/setup-dotnet@v4
      - run: dotnet tool install --global fsharp-refactor
      - run: fsharp-refactor src/Your.fsproj --dry-run --report findings.sarif
      - uses: github/codeql-action/upload-sarif@v3
        if: always()
        with:
          sarif_file: findings.sarif
          category: fsharp-refactor
```

Two honest notes. First, a dry run exits 0 whether or not it found
anything — findings are hints, not errors, and only a broken build or a
crashed run fails the step. Annotations therefore inform without
blocking; to make findings HARD-fail the job, add an explicit check:

```bash
jq -e '.runs[0].results | length == 0' findings.sarif
```

Second, scope the gate before turning it on: `--categories
correctness,performance` keeps the signal defensible on a shared
repository (see [Someone else's codebase](#someone-elses-codebase)),
and a `fsharprefactor.json` turns off anything the team has decided
against. The suppression comments described under
[Configuration](#configuration) silence individual findings at the
line, for both the gate and editors, in one place.

#### Running alongside other analyzer packages

The `fsharp-analyzers` host loads every analyzer assembly it is
pointed at, so one invocation — and one FCS typecheck, the expensive
part — can run this package together with others built on the same
SDK, all findings landing in one report. With
[G-Research's analyzers](https://github.com/G-Research/fsharp-analyzers),
whose current release pins the same `FSharp.Analyzers.SDK` as this
package (0.37.2):

```bash
fsharp-analyzers --project src/Your.fsproj \
  --analyzers-path ~/.nuget/packages/fsharp.refactor.analyzers/<version>/analyzers/dotnet/fs \
                   ~/.nuget/packages/g-research.fsharp.analyzers/<version>/analyzers/dotnet/fs \
  --code-root . --report findings.sarif
```

Rule codes are disjoint (`FR*` here, `GRA*` there), and the
`fsharpanalyzer: ignore-line` suppression comments work for their codes
too — the machinery lives in the shared SDK, not in any one package.

The SDK is strict about version agreement between the host and every
analyzer assembly it loads; a mismatch means analyzers silently fail
to load rather than erroring loudly. The day the two packages pin
different SDK minors, fall back to separate CI jobs — each producing
its own SARIF and uploading under its own `category:` (code scanning
keeps the streams apart) — at the cost of typechecking the project
once per job. Applying fixes stays this package's own tool either way:
`fsharp-refactor` applies only its own rules, and report-only
analyzers have nothing to collide with.

### Someone else's codebase

Every rule is one of four kinds, shown in the last column of
[Refactorings](#refactorings):

| Kind | | Count |
|---|---|---|
| `correctness` | The code does something other than what it looks like it does: a race, a swallowed exception, a disposable that leaks, a comparison that never holds | 51 |
| `performance` | Correct, but doing work it need not: allocations that need not happen, repeated work, a scan where a lookup would do | 32 |
| `idiom` | The same behaviour written the way F# writes it. Worth doing, and worth agreeing on first — it is a matter of house style as much as anything | 51 |
| `cosmetic` | The punctuation and spelling of code. Real cleanups, and nobody's idea of a welcome pull request from a stranger | 17 |

Thirteen rules carry a **priority** flag on top of their category — the
likely defects and security holes too costly to hold back: FR0020,
FR0028, FR0032, FR0046, FR0047, FR0048, FR0061, FR0063, FR0065, FR0066,
FR0122, FR0126 and FR0127. Swallowed exceptions (FR0055) and public
mutables (FR0062) stay plain correctness: bad habits more often than
live defects. Their notes print
without `--notes`, editors show them as warnings, and SARIF carries them
at warning level. [Rules.md](Rules.md) marks them in its Priority column.

This matters when the repository is not yours. Running everything over a
project you do not maintain and opening a pull request from the result is a
good way to waste an afternoon of someone's life: no maintainer wants
"removed an empty attribute argument list" across two hundred files, and a
diff that size buries anything that mattered. A disposable that is never
disposed is a different conversation entirely.

So for a codebase you are a guest in:

```bash
fsharp-refactor Their.fsproj --categories correctness,performance --dry-run
```

That is the set that earns its review time. For your own code, run the lot.

The category claims are measured, not assumed:

```bash
dotnet run -c Release --project benchmarks/PerfClaims
```

re-checks them on your machine, on BOTH axes — wall clock and allocation
(GC pressure is performance too). The contract: a performance rule's
rewrite must win on at least one axis, and an idiom rule's must hold
parity. FR0050 once emitted `Seq.sum` for a list — ~50%% slower than the
mutable loop it replaced, plus an enumerator allocation — which is how
the benchmark file, the rule's module-resolved output, and its idiom
recategorization all came to exist.

### Multi-targeted projects

Nothing extra to do: a multi-targeted project is worked through framework
by framework, narrowest first.

Capability fixes get both worlds — using the project's own vocabulary.
When a project also targets frameworks older than an overload (net4x,
netstandard2.0), the tool reads the fsproj's `DefineConstants` and looks
for a framework-shaped constant — `NETSTANDARD21`, `NET8`, digits
required — whose `'$(TargetFramework)' == '...'` conditions cover only
the modern frameworks. Names denoting a legacy framework (`NET48`,
`NET451`, `NETSTANDARD2_0`) are refused outright whatever their
conditions say: the SDK defines exactly those constants during the
legacy compilations themselves, where no fsproj parse can see them. Flavor names sharing the same condition
(SQLProvider defines `MICROSOFTSQL` right beside `NETSTANDARD21`) are
passed over: their meaning is the flavor, and a sibling project
compiling the same shared file may define them on legacy frameworks
too. If a constant qualifies and the file already uses conditional
compilation, FR0038 and FR0106 emit a pair instead of a fix the legacy
half cannot compile:

```fsharp
#if NETSTANDARD21
let orderNumber (s: string) = Int32.Parse(s.AsSpan(6, 5))
#else
let orderNumber (s: string) = Int32.Parse(s.Substring(6, 5))
#endif
```

No invented constants, ever: a project defining no such constant gets the
plain fix, and the final all-frameworks build stays the arbiter (a fix
the legacy half rejects is put back). Constants appearing in a
`DefineConstants` element whose condition the tool cannot fully read
(anything beyond `'$(TargetFramework)' == 'X'` chained with `Or`) are
disqualified rather than guessed at. A line already inside a positive
region of the chosen constant — or a hand-written `NET*_OR_GREATER` —
gets the plain fix (nothing legacy compiles it), a file with no `#if`
anywhere stays free of them, and editors always suggest the plain form.
`--no-if-defs` turns the pairing off entirely for a run that should never
add conditional compilation, whatever the project defines.

Large solutions stay affordable through three levers: one FCS checker
serves the whole run (twenty projects share nearly all their reference
assemblies, parsed once); a shared source file swept under one set of
conditional-compilation defines is never re-swept by the next project
that compiles it identically; and a multi-targeted project whose sources
contain no `#if` at all gets a single-framework sweep, with the final
all-frameworks build still verifying the rest.

That is not busywork. A rule gated on what the target can resolve behaves
differently per framework — `s.Contains 'x'` is offered under `net8.0`,
where the char overload exists, and does not compile for a `netstandard2.0`
target that lacks it. And each framework activates its own `#if` branches,
so code behind another one's is not in the parse tree at all. One pass
could only ever see part of the code.

Narrowest first means the fixes valid everywhere land before any that suit
only a wider surface, and every pass ends by building **all** the
frameworks, so a fix that does not generalise fails loudly instead of
passing as success.

Given this, one plain `fsharp-refactor Your.fsproj` produces:

```fsharp
let has (s: string) =
#if NETSTANDARD2_0
    s.Contains "x"      // still a string: no char overload here
#else
    s.Contains 'x'      // rewritten under the net8.0 pass
#endif
```

`--framework <tfm>` restricts a run to one framework if you want it.

### Allow changes to public API like types

Public types and function signature changes are not done by default.
Sometimes they would make the program more efficient:

Changing `type Item = { X: Option System.Guid }` to `type Item = { X: VOption System.Guid }`
would often make sense because Guid is already a struct, so `ValueOption` is better here.
But that could affect to external users and serialization.

`--api-changes` opts into rewrites that change internal or public
signatures — currying a tupled function (FR0090) and reordering its
parameters data-last (FR0091) — rewriting every call site in the project.
Without it those are held back and only counted. It also widens the
contained-type hints (FR0022, FR0069, FR0070, FR0093) to public types.
Consumers outside the project are why this is opt-in: their call sites
cannot be rewritten, so each rule only fires where a missed one would fail
to compile rather than change behaviour silently. Naming a single source
file skips these entirely — asking for one file and getting edits in its
callers would be a surprise.

The flag bundles two separable things: fixes that edit OTHER files, and
the widening of in-place shape changes to public declarations. Only the
first needs asking for: an assembly nothing links against — an executable,
a script — gets the second by itself, and a library opts in with
`"publicApi": false` in `fsharprefactor.json`. Either way it reaches the
editors, where the flag never has.
See [Is your public surface an API?](#is-your-public-surface-an-api).

## Refactorings

The one-line version of this list — every rule with a from → to example,
whether it is on by default, and whether its fix needs `--api-changes` —
is [Rules.md](Rules.md): the source each rule fires on and the fix it offers; the tests keep that table complete.

Roadmap based on ["F# refactoring possibilities"](https://www.slideshare.net/ThoriumT/f-refactoring-possibilities):

| Code | Refactoring | Kind |
|------|-------------|--------|
| FR0001 | Boolean `match` → `if-else` | idiom |
| FR0002 | Manual `Some/None` (and `ValueSome/ValueNone`) match → `Option`/`ValueOption` `map`/`bind`/`flatten`/`defaultValue`/`defaultWith`/`isSome`/`isNone` (spelled `x.IsSome`/`x.IsNone` where the receiver's type is settled, as FR0010 does)/`iter`/`exists`/`forall` + map-then-default combos. OFF BY DEFAULT: the measured board's one rewrite that slows the rewritten code (+53%, one closure per call) — enable via `"FR0002": true` or `--codes FR0002` when the readability trade suits | idiom |
| FR0003 | Extract function composition (`f >> g`) from pipeline/nested-application lambdas | idiom |
| FR0004 | Move `List`/`Seq`/`Array` conversion past the next pipeline operation (or drop it before consuming ops). Moving INTO Seq is offered only for operations that SHRINK their input: measured, `Seq.toList |> List.map f` → `Seq.map f |> Seq.toList` runs 35% slower for 12% less allocation, because `Seq.toList` rebuilds the result through an enumerator where `List.map` walked cons cells, and a length-preserving operation has no smaller output to pay for that. `filter` does (−4% time, −13% allocation), and moving into Array wins outright (map −39% time, −44% allocation). Moving into List is never offered | performance |
| FR0005 | Strip do-nothing CE wrapping (`async { return! c }`, rewrap identity, immediately-run wraps, `task { return x }` → `Task.FromResult`) | idiom |
| FR0006 | Extract a `when` guard into an active pattern | idiom |
| FR0007 | Remove `mutable` from never-mutated local bindings and type-level `let mutable` fields (class lets are private to the type, so the whole mutation scope is visible) | idiom |
| FR0008 | Tupled → curried parameters for `private` functions (definition + all call sites) | idiom |
| FR0009 | Manual `Ok/Error` match → `Result.map`/`bind`/`mapError`/`isOk`/`isError`/`defaultValue`/`defaultWith`/`iter` | idiom |
| FR0010 | Simplifications: `if c then true else false` → `c`; `x = None` → `x.IsNone` (`<> None` → `IsSome`; `Option.isSome x` and `x |> Option.isNone` → the property too; the module form stays on an unannotated parameter, whose type is not settled where it is read; withheld when the branch reads `x.Value` or `Option.get x`, where FR0034 binds the payload instead); `List.length xs = 0` → `List.isEmpty xs` (List/Seq/Array/Set/Map) | idiom |
| FR0011 | Trivial partial active patterns → `[<return: Struct>]` `ValueSome`/`ValueNone` (perf: no allocation per match attempt) | performance |
| FR0012 | Term-rewriting hints (fsharplint-style `lhs ===> rhs` rules): comparison flips, `x = true`, null checks via `isNull`, map fusion, `isEmpty (filter ...)` → `exists`, `sum (map ...)` → `sumBy`, `map id`, `id >>`, `compare ... = 0`, and more — extensible per repository | idiom |
| FR0013 | Redundant parentheses around single atomic arguments to a *function*: `List.max([4; 3])` → `List.max [4; 3]`, `Some("x")` → `Some "x"` | cosmetic |
| FR0014 | `ContainsKey` + indexer double lookup → single `TryGetValue` (two lookups become one — measured 1.26x — and on `ConcurrentDictionary` also a race fix); F# `Map` gets the `TryFind` option idiom | performance |
| FR0015 | Literal regex patterns → `StartsWith`/`EndsWith`/`Contains`; static `Regex` calls inside loops are hoisted to a `let private xRegex = Regex "..."` module binding (advice-only when the `open` is missing or the name is taken; a call under `#if` hoists under the same `#if`) | performance |
| FR0016 | Small value-type-only unions → `[<Struct>]` (perf: no heap allocation per value) Edits the companion .fsi in step | performance |
| FR0017 | `Async` discarded with `ignore` (never runs) — fix-less hint pointing at `Async.Ignore`/`Async.Start`; also a `ValueTask`/`ValueTask<T>` discarded with `ignore` (outcome lost, single consumption; plain `Task` is excluded) | correctness |
| FR0018 | Check-then-add → single `TryAdd` (race fix on `ConcurrentDictionary`, double-lookup fix on `Dictionary`) | correctness |
| FR0019 | `Equals` override without `GetHashCode` (hash-based collections misbehave); off by default — the compiler's FS0346 already warns on every shape this rule can see | correctness |
| FR0020 | Abstract member used during construction (override runs before derived init) | correctness |
| FR0021 | Redundant `.ToString()` inside interpolated strings | performance |
| FR0022 | Non-public union cases with unnamed tuple fields take the field names the code already spells, from the strongest source that yields them: their match sites (`\| Line(qty, price) ->`), a clear trailing comment (`// qty and price`, `// qty * price`, `// qty, price` — type-note comments like `// string * int` are recognized and excluded), or the case's own `XAndY` name (`InterestAndRate of float * float` → `interest: float * rate: float`). Definition-only edit, positional sites stay valid | idiom |
| FR0023 | Private two-parameter functions called as `fun x -> f x k` are reordered data-last, all in one fix: the definition swaps to `let private f k x`, direct calls swap their arguments, and the lambda — which under the new order would read `fun x -> f k x` — eta-reduces to the partial application `f k` (`List.map (fun x -> scale x 2)` ends up as `List.map (scale 2)`) | idiom |
| FR0024 | `raise (Exception msg)` → `failwith msg` (plain `System.Exception` only — the raised type and message are unchanged) | idiom |
| FR0025 | Null test wrapping a value into an option → `Option.ofObj` / `ValueOption.ofObj` (`if isNull x then None else Some x`, the negated and `= null` forms, and the two-clause `match x with null -> ...`; `Some`/`None` typed-gated to FSharp.Core) | idiom |
| FR0026 | Mutable backing field + trivial get/set member → `member val X = init with get, set` (field must be untouched elsewhere in the type; pure-atom initializer) | idiom |
| FR0027 | GC-lifetime note (no fix): a lambda that captures `this` — directly or through an instance `let` field — handed to an event/observable sink (`.Add`, `.Subscribe`, `.AddHandler`, `Observable.add`, ...) keeps the whole object alive until the handler is removed; sinks are typed-gated so collection `.Add`s never fire; a handler on an `Event<_>` created in the same scope cannot outlive `this` and stays quiet, and the note tells a process-wide publisher (`AppDomain.CurrentDomain.*`, `Console.*` — the real leak) from one handed in | correctness |
| FR0028 | N+1 note (no fix): a `for` over an `IQueryable` nested inside another loop executes one database query per outer iteration; typed-gated so in-memory sequences never fire, and an outer loop batched with `chunkBySize` suppresses the note | performance |
| FR0029 | Task state-machine advice (FS3511 itself is emitted at codegen, invisible to analyzers): a `let rec` in a resumable `task { }` body is flagged always (definite dynamic-fallback producer); oversized tasks (≥8 awaits or ≥60 lines) get the shrinking moves, three of them as automatic fixes — plain leading `let`s hoist above the builder (caveat in the message: a throw there then surfaces at the call instead of faulting the Task), a body that IS an if/else with at least one awaiting arm splits into per-branch tasks (arms cut as line regions between the `then`/`else`/`}` anchors, so their comments travel; a synchronous arm becomes a trivially static task), a long non-awaiting tail wraps into a local function inside the CE (a nested function's body is not resumable code, and closures capture the CE locals — no parameters, no annotations), and an awaiting closing block those shapes cannot carry — early returns, try/finally AROUND the awaits — becomes its own task-returning local function consumed with `return!`, two smaller state machines instead of one. What remains is advice: elif chains, tails referencing prefix `let!` bindings or foreign local mutables. The non-awaiting tail is measured structurally — the statement suffix after the last await on the spine or in the branch holding it; handlers, `finally` bodies and re-awaiting loop bodies never count, a `return!` is an await, and the note is anchored on the first tail statement (a tail inside a branch is advice only) | performance |
| FR0030 | A loop whose whole body is a single `ResizeArray.Add` of the loop variable becomes one `AddRange` call (`for x in xs do acc.Add x` → `acc.AddRange xs`); a projected body (`acc.Add(x * 2)`) stays a loop — the `Seq.map` spelling measured no faster than the loop and read worse (suave); `Add` is typed-gated|> Seq.map (fun x -> x * 2))`); `Add` is typed-gated to `List<'T>` so `HashSet.Add` never matches | performance |
| FR0031 | String `+` chains mixing literals and string values → interpolated string (`"Hello " + name + "!"` → `$"Hello {name}!"`); every operand must be a literal or typed-`string` identifier/path and the `+` itself must resolve to FSharp.Core, so a custom `(+)` never rewrites; literals containing `{`/`}`/`%` leave the chain alone. AT MOST TWO holes: a 3-hole interpolation falls off the compiler's String.Concat optimization onto String.Format — measured 4.9x slower with 2.3x the allocation of the + chain, which is itself already ONE String.Concat call | idiom |
| FR0032 | A type that creates a disposable field (`let stream = new FileStream(...)`) without implementing `IDisposable` is noted (no fix); injected constructor parameters don't count — the injector owns them; an interface that inherits `IDisposable` counts as implementing it; `StringReader`, `StringWriter` and buffer-backed `MemoryStream` fields own nothing and are not noted | correctness |
| FR0033 | An instance member touching no instance state — no self identifier, instance `let` field, primary-constructor parameter, or `base` — can be `static member` (note only: call sites change). Every name an instance `let` binds counts as state, tuple-destructured ones and let-bound functions included; a constructor parameter read inside a lambda or a record copy counts; the note follows the Visibility gate (private/internal members always, public ones under `--api-changes`, beside a signature file only private ones); `inline` members, `()`/`defaultof` stub bodies, and types whose instances are boxed to `obj` in the file (reflection or dynamic dispatch consumes them) stay quiet | idiom |
| FR0034 | `if x.IsSome then x.Value + 1 else e` → `match x with \| Some v -> v + 1 \| None -> e` (`.Value` throws when misused; the match cannot); handles the `IsNone`/negated and `x <> None`/`x = None` forms, multi-line branches (a match laid out over lines under an `if` that opens its line), else-less unit `if`, `x.Value.P` prefixes, and spells `ValueSome`/`ValueNone` when the receiver is a voption (typed-gated, so custom `IsSome`/`Value` members never match); boolean combos rewrite to combinators — `x.IsSome && p x.Value` → `Option.exists`, `x.IsNone \|\| p x.Value` → `Option.forall`, chains join inside the lambda | idiom |
| FR0035 | `List/Array/Seq.contains x ys` inside a loop — or inside a callback given to a collection function — scans `ys` linearly per iteration. When `ys` is a startup-built module binding — immutable, unshadowed, never reassigned — the FIX converts: when EVERY use of the name is one of the probes and the binding is a list/array/`seq` literal, the binding itself becomes the set (`\|> Set.ofList`/`ofArray`/`ofSeq` — no companion, still immutable, `Set`'s own `.Contains` takes the probes, measured 2.5× over the list scan even at five elements); when other uses pin the binding's type, a private HashSet companion lands beside it instead (built once, `open`-aware spelling) and every probe converts together. Otherwise the note recommends the same by hand, worthwhile only for long loops over more than a handful of elements, measured with the build cost charged (probing the loop variable itself never fires) | performance |
| FR0036 | Fragile runtime type comparisons (notes): `GetType().Name = "..."` breaks silently on renames/namespaces — compare types instead; `x.GetType() = typeof<T>` is exact-type equality — `x :? T` if subtypes are fine; quiet inside a `when` guard of a `:? T as x` clause that narrows to exactly T on purpose | correctness |
| FR0037 | Build-once types constructed inside a loop: `ConcurrentDictionary`, `HttpClient`, `JsonSerializerOptions` (CA1869), `Regex`, `SearchValues.Create` (CA1870) — all expensive by design; note suggests hoisting out or making static. `HttpClient` gets its own wording: per-iteration construction exhausts sockets under load, and the right lifetime (a shared instance, or `IHttpClientFactory` under DI) is the author's call | performance |
| FR0038 | Char overloads for single-character strings (CA1834/1847/1865-67): `s.Contains "x"` → `s.Contains 'x'` and `sb.Append "x"` → `sb.Append 'x'` (both ordinal already — fix); `s.StartsWith("x", StringComparison.Ordinal)` → `s.StartsWith('x')` (fix); bare `StartsWith`/`EndsWith`/`IndexOf` are culture-sensitive where the char overload is ordinal, so those get an advisory note only; receivers typed-gated to `String`/`StringBuilder`, and the whole rule stays out of `query { }` and quotations, where the string overload is the shape the LINQ translator recognises. Where the project's narrowest target has no char overload (`Contains(char)` is netstandard2.1+), the editor offers the portable form instead — `s.Contains "x"` → `s.IndexOf 'x' >= 0`, both ordinal and compiling on every framework; `Contains` only, since changing a culture-sensitive method is the author's call, not a portability fix | performance |
| FR0039 | Allocating case-insensitive comparisons (CA1862): `x.ToLower() = "literal"` gets a FIX to `String.Equals(x, "literal", StringComparison.OrdinalIgnoreCase)` when the literal is pure ASCII — measured across all of Unicode, the two spellings then diverge for exactly two compatibility characters no config value or role string contains (U+212A KELVIN SIGN when the literal has a k; U+017F LONG S in the upper direction when it has an s); qualified spelling when the file lacks `open System`, `<>` wraps in `not`. In EDITORS the light bulb offers a second action — the culture-aware `InvariantCultureIgnoreCase` spelling — while the CLI auto-applies only the ordinal primary: a bulk tool does not guess at linguistics. FR0031 offers the same pairing: interpolation primary, one explicit String.Concat call as the editor alternative. The method-call shape gets the same fix: `path.ToLower().StartsWith "file:"` → `path.StartsWith("file:", StringComparison.OrdinalIgnoreCase)` for StartsWith/EndsWith/Contains/IndexOf/LastIndexOf — gated on the literal's case AGREEING with the lowering direction (`.ToLower().StartsWith "FILE:"` can never match, and silently making it match is a behavior change), and Contains additionally on its StringComparison overload existing in the references (netstandard2.1+). Everything else — non-ASCII literals, `a.ToLower() = b.ToLower()`, non-literal arguments — stays a note: the comparison type is the author's deliberate choice (per the .NET string best-practices guide, which names exactly this rewrite) | performance |
| FR0040 | Redundant membership guards (CA1853/1868, fix): `if d.ContainsKey k then d.Remove k \|> ignore` → `d.Remove k \|> ignore`, `if not (s.Contains x) then s.Add x \|> ignore` → `s.Add x \|> ignore` — the operations already return `false` on a miss; typed-gated to `Dictionary`/`HashSet`/`SortedSet` | performance |
| FR0041 | `Array.sum/average/min/max/contains` on `int[]`/`int64[]` is a scalar loop; on .NET 8+ System.Linq's `Sum()`/`Average()`/`Min()`/`Max()`/`Contains()` are SIMD-vectorized (`Contains` measured ~5x at 1000 elements, ~6x at 100k; note only: LINQ `Sum` throws on overflow where `Array.sum` wraps; floats excluded — NaN semantics differ; quiet inside `query { }`, where the code is a quotation for a provider's translator and the LINQ spelling may not translate) | performance |
| FR0042 | Fully applied `sprintf` → typed interpolated string (`sprintf "asdf %s" x` → `$"asdf %s{x}"`); specifiers are kept verbatim so the output is byte-identical; guards: regular literal with no `{`/`}`, simple arguments only, no `%a`/`%t`/`*`-widths, partial applications never match | idiom |
| FR0043 | In an interpolated string that *already* has a typed hole, the remaining plain holes gain specifiers (`$"%s{name} is {age}"` → `$"%s{name} is %d{age}"`) — free compile-time type pinning since the string is on the printf path anyway; specifier-free strings are left on the F# 8 `String.Concat` fast path, and only ToString-identical specifiers are used (`%s`/`%d`/`%c`; never `%b` or `%f`) | idiom |
| FR0044 | `raise ex` in a `with` handler resets the stack trace → `reraise ()` (CA2200, fix); skipped inside lambdas/nested trys where `reraise` would not compile or would mean a different exception; inside a computation expression, where `reraise ()` is not allowed, a try/with whose only arm rethrows (`with ex -> raise ex`, `return raise ex`) is removed — its body stays and an unmatched exception propagates with its trace intact | correctness |
| FR0045 | `x = nan` / `x <> Double.NaN` never holds (IEEE 754) → `System.Double.IsNaN x` / negated (CA2242, fix); `Single.NaN` uses `Single.IsNaN` | correctness |
| FR0046 | `lock "str"` / `lock typeof<T>` / `lock (x.GetType())` — weak-identity objects are process-wide singletons, so the monitor is shared with strangers (CA2002, note): use a dedicated `let lockObj = obj ()`; the editor offers a private lock object declared next to the locked value (or before the enclosing binding) — `lock this`, `lock stdout` and `lock x <| ...` are recognised too | correctness |
| FR0047 | A type implementing `IDisposable` whose `Dispose` never touches one of its `new`-constructed disposable fields (CA2213, note) — the mirror of FR0032; the interface `Dispose` is followed one hop into `this.Dispose()` or a let-bound `dispose ()`. A `Dispose` that USES the field without releasing it says so separately — `member this.Dispose() = cts.Cancel()` cancels the token and leaves the handle (fantomas's LSPFantomasService and CloudAgent's connection factory both do), where releasing means `Dispose`/`DisposeAsync`/`Close` on it, directly or through an upcast. Quiet when the body hands off to `base.Dispose()`, and in a file that opens `System.Reactive`/`FSharp.Control.Reactive`, where a `Dispose` that unsubscribes rather than releases is the design | correctness |
| FR0048 | `String.Format("{0} of {1}", x)` — a placeholder without an argument throws `FormatException` at runtime (CA2241, note); `{{` escapes handled, culture-first overload ignored | correctness |
| FR0049 | Sync-over-async (CA1849/VSTHRD): `.Result`, `.Wait()`, `GetAwaiter().GetResult()`, `Async.RunSynchronously`, `Thread.Sleep` **inside** `async`/`task { }` invite thread-pool starvation and deadlocks (typed-gated receivers; `Thread.Sleep n` gets a `do! Async.Sleep n` / `do! Task.Delay n` fix in statement position, and so do `t.Wait()` — `do! t`, a `Task<T>` upcast — and `Task.WaitAll(...)` — `do! Task.WhenAll(...)`, or `let! _ =` when the joined tasks carry values; `Task.WaitAll(tasks, timeout)` stays); a blocking call inside the delegate of `Assert.Throws<E>(fun () -> ...)` moves with the assert to `ThrowsAsync` — a `let!` for xUnit and MSTest, a plain replacement for NUnit, whose ThrowsAsync returns the exception; a `let x = <blocking>` as a direct CE statement gets the bind fix across the whole matrix — `.GetAwaiter().GetResult()`, `.Result`, and single-argument `Async.RunSynchronously` (pipe or direct form) all become `let! x = ...`, with the asymmetric adapters applied: task { } binds Tasks AND Asyncs with a plain `let!`, async { } binds Asyncs natively but Tasks go behind `Async.AwaitTask` (ValueTasks have no AwaitTask overload and stay advice there); `.Result`/`.Wait()`/`GetResult()` **outside** CEs get the boundary note — wrap in `task { }` or use the sync API — and `X.FooAsync(args).GetAwaiter().GetResult()` can swap to `X.Foo(args)` when the typed tree proves a synchronous sibling with the same argument count exists — but only as an editor action or behind `{ "FR0049": { "syncSwap": 1 } }`, never auto-applied: async-in-sync is usually a waypoint toward a full-async refactor, and the tool must not walk the code backward (`Async.RunSynchronously` outside a CE is F#'s intended sync boundary and stays quiet); `Task.Run(fun () -> c |> Async.RunSynchronously)` inside `task { }` becomes `c |> Async.StartAsTask` (fix), the one fix offered inside a lambda because it deletes the lambda: both queue the computation to the thread pool, but StartAsTask does not park a pool thread on the result (`Async.StartImmediateAsTask` is the wrong twin, running on the CALLING thread until the first await). The `|> ignore` spelling keeps its `do!` through a `:> Task` upcast, since `do!` refuses a `Task<T>`. One behavioural difference, in the rare non-happy path: a cancelled computation surfaces as a CANCELLED task rather than one faulted with OperationCanceledException, which is the more honest of the two; and the TASKIFY fix: a FILE-PRIVATE sync function draining a task at its boundary becomes task-returning (body wrapped in `task { }`, drains bound with `let!`/`return!`, tails `return`-prefixed) with every caller — each required to sit in a task/async CE in a bindable shape — awaiting it, `Async.AwaitTask`-bridged in `async`; one unconvertible caller vetoes everything. Quiet when the task is known complete — under its own `IsCompleted`/`IsCompletedSuccessfully` probe, a `Task.FromResult`/`CompletedTask`/`ValueTask.FromResult` value, or after the receiver's own `Wait(...)` above; `.Result` on the antecedent inside its own `ContinueWith` continuation gets its own note instead — a faulted antecedent throws wrapped in an AggregateException there, and the continuation is a bind: the plain `t.ContinueWith(fun a -> ... a.Result ...)` becomes `task { let! r = t; return ... r ... }` (fix, for a value-returning single-line continuation that only reads `a.Result` — one that tests IsFaulted handles the antecedent itself and stays a note); before FSharp.Core 6, or on Fable, `ContinueWith` IS the bind and nothing is reported, and the taskify fix follows the same gate, or after the receiver's own `Wait(...)` above; `Task.WaitAll(tasks, timeout|token)` outside a CE is the bounded idiom like `t.Wait(timeout)`; the spine of `[<EntryPoint>]` main, a runner ending in an exit-code literal, and `.fsx` top-level statements are the console's blocking point (no boundary note), and so is a wait in a function choreographed around a thread (a signal, a `Thread`, `Interlocked` — the body FR0142 refuses to convert for the same reason: no boundary note there, a bind inside such a CE stays a note without its fix, and the taskify fix never converts such a function; `Thread.Sleep` alone is a pause, not choreography); a wait in a `finally` of async/task gets an honest note and no fix (no bind is legal there); `ManualResetEventSlim`/`SemaphoreSlim`/`CountdownEvent.Wait()`, `WaitHandle.WaitOne()`, `Barrier.SignalAndWait()`, `Thread.Join()` and `Monitor.Wait` inside a CE get an advice-only note | correctness |
| FR0050 | `let mutable total = 0` + `for x in xs do total <- total + x` → `let total = xs \|> List.sum` (fix); projections → `sumBy`, general combines → `fold (fun acc x -> ...) init` — same expression, same bindings, no mutable. The module matches the source's resolved kind: measured, `List.sum`/`Array.sum` run LEVEL with the loop while `Seq.sum` is ~50% slower on a list, so this is an idiom rule, and the rewrite never spells `Seq` when it knows better | idiom |
| FR0107 | `let mutable found = false` + `for x in xs do if p x then found <- true` → `let found = xs \|> List.exists (fun x -> p x)` (fix); the `true`-initialized dual becomes `forall` with the predicate negated. Tightly gated because `exists` SHORT-CIRCUITS where the flag loop kept iterating: the loop body must be the one `if` (no `else`) optionally preceded by pure, immutable, single-line `let` bindings, which fold into the lambda; the predicate must never mention the flag and must be visibly effect-free (any assignment, sequencing, statement construct or `ignore` inside it disqualifies), nothing may reassign the flag afterward, and the source must resolve to a real List/Array/Seq. Module-resolved like FR0050; measured level with the loop on the no-hit worst case, faster on any hit | idiom |
| FR0108 | Boolean identity literals drop (fix): `x && true`, `true && x`, `x \|\| false`, `false \|\| x` — the literal contributes nothing, the expression is the other operand. `x && false` and `true \|\| x` stay: their value is constant but `x`'s evaluation (and its effects) changes. Deliberately fires inside `query { }` too — removing a node leaves a strictly simpler tree of shapes the translator already accepted | idiom |
| FR0110 | An incomplete DU match with no wildcard (the FS0025 warning shape) gains the missing arm(s) as `\| Case -> raise (System.NotImplementedException())` (fix) — FR0072's dual: that rule expands a wildcard hiding real cases, this one closes a match that has none. Coverage counts only unguarded plain case patterns (a `when` may reject); at most three missing cases, past that a wildcard was probably the intent; multi-line matches only, new arms adopt the last clause's `\|` column | correctness |
| FR0111 | `else` holding a whole nested `if` flattens to `elif` (fix) — only when the `else` sits at the outer `if`'s column (offside rules for `elif`) and nothing but whitespace separates the keywords | cosmetic |
| FR0112 | An if/elif chain comparing ONE identifier against distinct int/string/char literals becomes a `match` (fix). The scrutinee must be a bare identifier — a call re-evaluated per comparison today would be evaluated once after the rewrite — and every `=` must resolve to FSharp.Core's (match patterns use structural equality) | idiom |
| FR0113 | Nested ifs merge into one `&&` (fix), in the two exactly-semantics-preserving shapes: identical else-branches (`if a then (if b then X else E) else E` — one branch runs either way, so even an effectful E is unchanged), and no else at all (unit result). An `\|\|`-topped condition gains parens before joining the `&&`. The tempting third shape — inner if without else while the outer has one — is deliberately absent: the merge would run E where the original ran nothing | idiom |
| FR0114 | Pyramid-of-doom flip (fix, OFF by default): a then-branch of 20+ lines behind an else of 3 or fewer (both thresholds configurable, see Configuration) flips — condition negated (an existing `not` unwraps instead), short exit first, big block last. Off because plenty of teams hold the exact opposite style (happy path first); turn on per repository when short-exit-first IS the house style | idiom |
| FR0115 | Base case first behind a compound guard (note): `match v with \| x when a && b -> base \| _ -> err` hides the base case behind a guard every new error condition must be threaded into; inverted — error guards first, base case as the final arm — the match reads top-down and extends by appending. Advice only: which case is "the base" is intent — and only when the wildcard arm visibly fails (raises, `failwith`, `Error`/`None`), so a wildcard computing an ordinary alternative is left alone | idiom |
| FR0116 | A member of a `let rec ... and` group that references no sibling takes part in no recursion and moves out, as a plain `let` above the group (fix) — callers in the group still see it, and it can call nothing in the group by construction. A self-recursive member (calls itself, nobody else) leaves as its own `let rec`; when the group's HEAD is the non-recursive one nothing moves at all — its `let rec` becomes `let` and the next binding is re-crowned `let rec`. No attributes on moved bindings, membership judged conservatively (any textual mention of a sibling keeps it in) | idiom |
| FR0130 | A module-level constant binding (string/number/char/bool literal RHS, no attributes) gains `[<Literal>]` (fix): a true CLR const — const-folded at use sites, usable in patterns and attribute arguments. Contained bindings by default (`[<Literal>]` compiles a public field to a const, a binary-compatibility change — `--api-changes` opts in). Local `let`s cannot take attributes, so the rule is module-level by construction Edits the companion .fsi in step: its val gains the attribute and the value | idiom |
| FR0131 | A module-level `let rec` whose every self-call provably sits in tail position gains `[<TailCall>]` (fix): pure metadata, no codegen change — the compiler then emits FS3569 if a later edit pushes a recursive call out of tail position. Verified structurally (match arms, if/elif/else, let bodies, sequencing, pipes; full application only); any mention of the name inside a lambda, try/with, CE, `use` scope or argument vetoes. Needs FSharp.Core 8+ (typed gate); single non-mutual bindings only | idiom |
| FR0132 | A PUBLIC declaration (binding, type, union case) with no XML doc but a trailing same-line `//` comment gets that comment promoted to the `///` position (fix) — same text, but only the doc position reaches tooltips and generated docs. Instruction comments (`fsharpanalyzer:`, TODO/FIXME/HACK) and private declarations are left alone; the insert spells `/` + the original comment, so the comment-loss guards pass by construction | idiom |
| FR0133 | A five-plus-word camel or snake name — `thisIsMyVeryComplexMethod`, `this_is_my_very_complex_case` — becomes the double-backtick name ` ``this is my very complex method`` ` at its definition and every use (fix). Local and file-private bindings only, plus TEST-attributed functions (`[<Test>]`/`[<Fact>]`/...) at any visibility when the project's uses prove nothing calls them cross-file — serialization APIs legitimately demand snake_case, and a public name is a contract. Names with ALL-CAPS acronym runs (`APRUnitRate`) are skipped. TEST-attributed names rewrite BY DEFAULT — there the name is nothing but a display name and the backtick spelling is the F# testing convention; local and file-private names are the config opt-in `{"FR0133": {"locals": 1}}`, since some editors still fumble backtick-name intellisense Renames the companion .fsi val in step | cosmetic |
| FR0134 | A file-private record field `Seen: DateTime` migrates to `DateTimeOffset` in one all-or-nothing edit set (fix) — the instant keeps the clock it was read from, closing the FR0121 class of server-timezone accidents. Strict envelope: every write is `DateTime.UtcNow`/`.Now`/`.MinValue`/`.MaxValue` with Now and UtcNow never mixed (DateTime comparisons ignore Kind — mixing was already a bug, and fixing it silently is still a behavior change); every read is a parity member (`Year`..`Second`, `Add*`/`Subtract`, `DayOfWeek`...), a same-field comparison, or a same-field subtraction. `.Date` (type escapes), `ToString` (format changes) and any unfollowed dataflow bail. OFF BY DEFAULT — a serialization-shape change the repository owner opts into via `"FR0134": true` | idiom |
| FR0135 | A multi-line `(* ... *)` block comment in an `.fsx` script carrying clear MARKDOWN — a fenced code block or a `###` heading — becomes the literate `(** ... *)` cell it reads as (fix: one star). FSharp.Formatting silently drops markdown from plain comments; the compiler sees no difference either way. Existing `(**` cells and `(*** command ***)` cells are left alone | cosmetic |
| FR0136 | The zero-argument Guid constructor — `Guid()` / `new System.Guid()` — is the classic .NET slip: it reads like "a new guid" but produces `00000000-…`. The fix states the value as `Guid.Empty` (identical value and type, so the CLI applies it freely); the editor also offers `Guid.NewGuid()` — the likely intent, but a behavior change only a human confirms. Typed-gated to `System.Guid`, qualification preserved; `Guid(bytes)` and friends are deliberate and stay | correctness |
| FR0137 | Two consecutive `map` stages of the same collection module fuse into one pass (fix): `xs \|> Array.map fst \|> Array.map f` → `xs \|> Array.map (fst >> f)` — the intermediate array stops existing (for `Seq`, one lazy wrapper fewer); `map id` disappears into the next stage outright. Fusing interleaves the two functions per element where the eager form ran the first over every element first, so the rule only fires when the first mapper is a provably pure `fst`/`snd`/`id` — an arbitrary first mapper's side effects could be observed reordering | performance |
| FR0138 | Hand-rolled string emptiness tests become the BCL predicate that says what they mean (fix): `isNull x \|\| x = ""` → `String.IsNullOrEmpty x`, `not (isNull x) && x <> ""` → `not (String.IsNullOrEmpty x)`, and the `Trim()`-based spellings → `String.IsNullOrWhiteSpace x` — exact rewrites (null short-circuits the `\|\|` exactly as the predicate answers; no-argument `Trim` strips precisely the `Char.IsWhiteSpace` set the predicate tests), and the Trim forms stop allocating a trimmed copy per call. Bare `x.Trim() = ""` without a null guard is EDITOR-only: null throws in the original and answers true in the rewrite — almost always the intended robustness, but a behavior change a human signs. Subjects must be identifiers or dotted paths (pure reads) | idiom |
| FR0139 | A `Seq.` function applied to something the typed tree proves is an **array** (fix): `arr \|> Seq.head` → `arr \|> Array.head`. Measured on **.NET 10** (the runtime the benchmarks target, because the answers differ from .NET 8): head 17.1→2.6ns, tryFind 583→233ns, find 707→237ns, fold 567→239ns, forall 572→237ns, length 3.1→2.2ns. Arrays ONLY: a `Seq.` call on a list or a lazy source can be the author's point, and on an `IQueryable` the `Seq` functions are what the provider translates. Excluded by measurement rather than by taste — `iter`/`iteri` (236.6 vs 235.4ns, a wash), collection-returning functions (`Seq.map` is `seq<'b>` where `Array.map` is `'b[]`, which ripples into the consumer), `item` (`Array.item` throws `IndexOutOfRangeException` where `Seq.item` throws `ArgumentException`), the numeric aggregates (FR0041 sends those to vectorised LINQ), and `contains` on REFERENCE arrays (`Seq.contains` 938ns actually beats `Array.contains` at 1024ns). `contains` on `int[]`/`int64[]` has TWO better answers, so it offers two: the CLI applies the FASTER one — vectorised `Enumerable.Contains` (**587→109ns**), spelled `System.Linq.`-qualified unless the file opens it — and an editor offers the idiomatic `Array.contains` (587→464ns) beside it for anyone who would rather not bring System.Linq in | performance |
| FR0140 | A construction immediately followed by property assignments on the new object folds into F#'s named-property construction (fix): `let h = Henkilo()` + `h.Id <- 1L` + `h.Etunimi <- "x"` becomes `let h = Henkilo(Id = 1L, Etunimi = "x")`. Not a constructor overload and not faster — the same calls in the same order — but the object reads as constructed rather than assembled, and the half-built value stops being nameable. Only the UNINTERRUPTED run of assignments straight after the binding folds in; anything in between could observe the half-built object, so the fold stops there. Each property must be distinct and typed-settable, and no assigned value may mention the object itself | idiom |
| FR0141 | A `while` loop that carries STATE forward by mutation and leaves through a boolean flag is a tail-recursive function written inside out (note, OFF BY DEFAULT): raising the flag is not a `break`, so the rest of that iteration still runs and the loop leaves only at the next condition check. A tail-recursive function would take the state as parameters and return where the decision is made. The note counts the statements that would still run, and says so only when there are any. Silent inside `async` and `task`: in a task recursion is not even available (a resumable state machine grows the stack on a recursive `return!`, as FSharp.Azure.Quantum's polling loop records in a comment), and in an async the recursive function must return `Async<_>`, so the change reaches the signature rather than the loop. Deliberately NOT the search loop either — a carried value whose every assignment is `x <- x + <literal>` is an index, and that shape already short-circuits and allocates nothing (measured 12x faster than `Array.exists` on an early hit, so a pipeline there would be a regression dressed as a cleanup). Note only: naming the function and its parameters is the author's | idiom |
| FR0142 | A test (Fact, Theory, Test, TestCase, TestMethod) whose body blocks on async work - Async.RunSynchronously, .Result, .Wait(), GetAwaiter().GetResult() on a Task - returns the work instead: the body becomes a task block cast to System.Threading.Tasks.Task and each blocking statement a let!/do! bind (fix); `Task.WaitAll(...)` becomes `do! Task.WhenAll(...)` and `Assert.Throws<E>(fun () -> <blocking>)` the framework's async assert with the lambda returning the awaitable (bound with `let!` for xUnit and MSTest, replaced in place for NUnit). The shapes are shared with FR0049. xUnit, NUnit 3+ and MSTest await a Task-returning test, so the thread is free while the work is in flight; a test method shape is the framework business, not a consumer, so no API change. Only spine-level blocking sites move; FsCheck Property and Expecto builders stay out | performance |
| FR0143 | A script whose `#load` chain misses a file of the project it loads from gets it loaded, in the project's order (fix): the compiler's FS0039 names what is missing, the `#load` paths name the project, and its fsproj lists the compile item that declares the name. A missing NAMESPACE from a ProjectReference gets a `#r` to that project's newest built assembly, or a note to build it first. Runs on scripts that do not typecheck — that is its input. | correctness |
| FR0144 | A script `#r` or `#I` path the package no longer has is re-pointed at what it has now (fix): the first missing segment, when it is a target-framework folder (net451, netstandard1.6) or a `Name.1.2.3` version folder, is swapped for the sibling under which the rest of the path exists — a file for `#r`, a directory for `#I`. Ranked for the runtime the original implies: a net4x original wants the newest net4y, then netstandard2.0 and below, never 2.1 or netX.0; anything else wants the newest netX.0 not above the SDK the script is checked against, then netstandard 2.1, 2.0, older, and netcoreapp only as a last resort; a version folder takes the newest. Quoting and separators stay as written; other candidates are listed. `.fsx` only; runs without a typecheck. | correctness |
| FR0145 | A record expression that leaves fields unassigned (FS0764) gets them (fix): read off the typed tree through the labels it does assign, each with the empty value its type makes obvious — `None`, `ValueNone`, `[]`, `[||]`, `Map.empty`, `Set.empty`, `Seq.empty`, `()` — and, where none is obvious, a `raise (System.NotImplementedException "Field")` placeholder that fails when the record is built; the editor also offers zero values (`false`, `0`, `""`, `Unchecked.defaultof<_>`). The apply tool takes only the all-obvious case. Runs on files with type errors, like FR0077. | correctness |
| FR0146 | A SQL command whose text carries no parameter at all — a full-table statement, or values written into the text (note): possible, but suspicious; parameters are where the values were supposed to go | correctness |
| FR0147 | A namespace spelled out at every use — six times, or four when three segments deep, tunable with `{ "FR0147": { "uses": 6, "deepUses": 4 } }` — becomes one `open` after the file's last open, and every use loses the prefix; namespaces only, by the symbol's own namespace, so `System.IO.File.Exists` shortens to `File.Exists` and the longest namespace wins; a namespace whose open would clash with a name the file defines or already uses unqualified is noted, never fixed — the note names the clashing identifiers and where they come from (the file's own definition, another open, an FSharp.Core abbreviation, an unqualified use) | idiom |
| FR0148 | A public `Dispose()` on a type that does not implement `IDisposable` — directly, through an interface inheriting it, or through a base type (typed) — is a resource nothing can `use` (CA1063, note); fsharp.formatting's FsiSession hid an FCS evaluation session behind one | correctness |
| FR0149 | A computation handed to `Async.Start`/`Async.StartImmediate` has nobody to observe a failure — no caller to return to, no Task to fault — so an exception in it is **unhandled on a thread-pool thread and terminates the process** (measured in fsi: `try async { failwith "y" } \|> Async.Start with _ -> ()` dies). A `try/with` around the call catches nothing, because the work never runs on that thread; `StartImmediate` differs only up to the first await. `Async.StartAsTask` (fault in the Task) and `Async.RunSynchronously` (raised on the caller) are observable and never reported. Handled means the body IS a `try ... with`, or `Async.Catch` appears and a match consumes both `Choice1Of2` and `Choice2Of2` — producing the `Choice` is not handling it. Only a body this file can see is judged: an inline `async { }` or a one-hop binding in the same file. Normally no fix: the repair is a handler whose body is a design decision, and where it goes changes the behaviour — wrapped around a looping computation it still stops on the first failure, inside the loop it keeps running — so the note names that choice when the body loops. The exception is a `try/with` that wraps the start AND NOTHING ELSE: the author already wrote the handler for this computation, so the editor offers it moved inside, every clause verbatim (typed patterns and `when` guards included, which the `Async.Catch` spelling could not carry — and `Async.Catch` does not even pipe into `Async.Start`, whose argument is `Async<unit>`). A tupled start keeps its cancellation token, so that form gets no move | correctness |
| FR0150 | A `use`-bound disposable read by a `task`/`async` the scope RETURNS: `use` disposes at the end of the scope, the computation runs after it, and the first read past the return throws `ObjectDisposedException` (suave's ConnectionHealthChecker died on its first interval this way). The editor offers the move — the same `use` inside the computation, disposing when the work finishes — when nothing between the binding and the computation touches it; constructing later is a timing change, so a sweep never makes it. G-Research's `DisposedBeforeAsyncRunAnalyzer` covers the same shape and recommends the same repair; this one requires the computation to actually read the binder (theirs flags the shape either way) and carries the move as an edit. Already running theirs? `"FR0150": false` | correctness |
| FR0151 | An exception handler that reads only `.Message` (or `.ToString()`) from a type whose real diagnosis lives elsewhere. `ReflectionTypeLoadException.Message` is the fixed string "Unable to load one or more of the requested types." and names no cause - `LoaderExceptions` holds one exception per failure, and `Types` is PARTIALLY POPULATED rather than null, so the types that did load are in it. `WebException.Message` never contains the server's error body; that is only in `Response.GetResponseStream()`. The ReflectionTypeLoadException case gets a fix (editor only, like FR0049's sync swap - it compiles either way, but what gets logged is the author's call) that joins the loader exceptions and FILTERS NULLS, because on .NET Framework those elements can be null. But the FIRST fix offered is a different one: .NET loads every referenced assembly, so what failed is routinely a dependency this code never uses - a localization satellite, an optional plugin - while `e.Types` already holds the types that DID load, nulls standing in for the rest. Where the try body is a `GetTypes()` call, so both branches are provably `Type[]`, the editor offers the filtered `e.Types` in place of a `reraise()`/`raise`: not failing at all beats reporting the failure better. It is not a silent swallow, though - the rewrite KEEPS the rethrow for the case where nothing loaded (`Types` can be null outright, and filtering can empty it, and then the original failure really was fatal), and appends a `// TODO: log e.LoaderExceptions as a warning` where the rethrow ends its line, never where a trailing comment would swallow an `else`. Reading either member counts as an informed handler, in the clause BODY or in its `when` guard - the corpus writes `when not (isNull wex.Response)` and that handler already knows where the body is; WebException is note-only, since reading the body needs two `use` bindings and a null-Response guard. A table, so AggregateException/SqlException slot in later. Distinct from FR0120, which treats `ex.Message` as handled on purpose because logging only the message can be a PII choice - this rule fires only where the message is provably uninformative | correctness |
| FR0152 | `ConcurrentDictionary.GetOrAdd` whose VALUE TYPE is a `Task`, `ValueTask` or `Lazy`. Those REMEMBER a failure instead of raising it: a faulted entry stays in the dictionary and every later reader is handed the same failure, so one transient error - a timeout, a cold dependency - outlives whatever caused it and the dependency looks down long after it recovered. Remove the entry when the value faults. Gated on the value type, so a factory that simply THROWS is never reported: GetOrAdd propagates that and stores nothing, and the next caller retries. Note-only - the remedy is a change to how the cache is designed | correctness |
| FR0129 | A when-guard that only equality-tests the clause's own binder against a literal IS the literal pattern (fix): `| x when x = "A" ->` becomes `| "A" ->`, per clause, on match/match!/`function` alike — gated on the body never mentioning the binder (it no longer exists after the rewrite) and the compared value being a constant the pattern language can spell | idiom |
| FR0128 | The obsolete `*Managed`/`*CryptoServiceProvider` crypto constructors (SYSLIB0021) become the static factories (fix): `new SHA256Managed()` → `SHA256.Create()`, `new RNGCryptoServiceProvider()` → `RandomNumberGenerator.Create()` — the SAME algorithm, so behavior is preserved; weak algorithms keep their FR0065 note separately. Zero-argument constructors only | idiom |
| FR0127 | A string literal matching a provider's DOCUMENTED credential format — `sk-ant-…` (Anthropic), `sk-…`/`sk-proj-…` (OpenAI), `AIza…` (Google), `ghp_`/`github_pat_` (GitHub), `AKIA…` (AWS), `xoxb-…` (Slack), PEM private-key headers — is a leaked key until proven otherwise (note): not entropy guessing, format anchoring; a literal that says `test` anywhere is a test account's credential and stays quiet | correctness |
| FR0126 | A dynamically built string (interpolation, concat, sprintf, String.Format) reaching `Process.Start`, a `ProcessStartInfo` construction, or an `.Arguments <-` set is the command/argument-injection sink (note) — doubly so when the string carries LLM or agent output; pass a fixed executable with an argument LIST instead. The process sibling of FR0066 | correctness |
| FR0125 | Invisible and bidirectional Unicode in source (bidi controls U+202A-202E/U+2066-2069 — Trojan Source CVE-2021-42574; the Unicode tag block U+E0001/U+E0020-E007F — the prompt-smuggling channel; zero-width spaces U+200B/U+2060-2064; mid-file BOMs). Inside a REGULAR string literal the fix rewrites the character as its `XXXX` escape — same string, now visible; elsewhere it stays a note. ZWJ/ZWNJ are deliberately exempt: emoji and Persian/Arabic text use them legitimately | correctness |
| FR0124 | Structured-log templates that lie (notes): a template naming more or fewer placeholders than it receives arguments logs holes or drops values silently; duplicate placeholder names overwrite each other in the sink; and an interpolated string as the template destroys structured logging outright — every message becomes a distinct event and the values lose their property names. A leading exception argument is skipped before counting. The template sibling of FR0048, typed-gated to Microsoft.Extensions.Logging; Serilog and Logary (`Message.eventX` pipelines filled by `setField`) are covered beside Microsoft.Extensions.Logging | correctness |
| FR0123 | The canonical `Monitor.Enter x; try body finally Monitor.Exit x` IS F#'s `lock x (fun () -> body)` spelled dangerously — the fix rewrites it (body lines travel verbatim, comments included; the whole released-on-all-paths rule family closes at the source). Gated on single-argument Enter (the `(x, &taken)` overload carries protocol), identical lock text in Enter and Exit, and the typed Monitor entity. A bare `Monitor.Enter` with no try at all is the leak note; a `try/finally` that is the first statement after the Enter (with more following) is recognised as the guard | correctness |
| FR0122 | A literal regex pattern .NET rejects is a GUARANTEED ArgumentException on first use — construction compiles the pattern without running any input, so the check is cheap and exact (note; static `Regex.IsMatch/Match/Matches/Replace/Split` second arguments and `Regex(...)` constructions) | correctness |
| FR0121 | Wall-clock traps on servers: `DateTime.UtcNow.Date` cuts a calendar date at a timezone-random instant — UTC midnight is nobody's midnight — and `DateTime.Today` is the SERVER's date, which the end user never sees (note; convert to the user's timezone first). A bare `DateTime.Now` offers the `UtcNow` rewrite in editors and applies on the CLI only under `{ "FR0121": { "utcNow": 1 } }` — Fable/desktop code legitimately wants local time. `DateTime.Now.Date`-style calendar reads are excluded from the fix entirely: swapping Now for UtcNow underneath one manufactures the first bug. `DateTime.Now` handed to a non-Utc timestamp setter (`File.SetLastWriteTime`) takes local time and stays; `Now` read through a member is reached too — `.Ticks` as a version number gets the rewrite, `.ToString(...)` the note only | correctness |
| FR0120 | A LogError/LogCritical/LogWarning inside an exception handler that never mentions the caught exception gains it as the first argument (fix) — the ILogger exception-first overload lets the SINK decide rendering; the editor also offers `ex.GetBaseException()` for wrapped/aggregate root causes. ANY existing mention of the exception in the arguments counts as handled, `ex.Message` included: message-only logging is a legitimate GDPR/PII choice this rule must not escalate. Typed-gated to Microsoft.Extensions.Logging | correctness |
| FR0119 | A blocking call inside `task { }`/`async { }` where the typed tree proves a `<Name>Async` twin exists (same parameter prefix, `T` → `Task<T>` return, an extra trailing optional CancellationToken tolerated) rewrites to the twin (fix): `let x = reader.ReadLine()` → `let! x = reader.ReadLineAsync()`, statements gain `do!` when the twin returns non-generic Task, and `async { }` bridges with `\|> Async.AwaitTask` (real Tasks only there). The preventive half of FR0049, and FR0118 hands the rewritten call its token on the next pass. Never inside a body choreographed around a thread (a signal, a `Thread`, `Interlocked` — the refusal FR0142 and FR0049 share), lambdas, nested CEs, finally blocks or handlers | correctness |
| FR0118 | A CancellationToken in scope should reach the calls that take one (fix, two shapes): a call omitting the token when the resolved method has a same-name overload with the same parameter prefix plus a trailing token (or a trailing optional token) gains `, ct`; and `CancellationToken.None` passed as an argument while a real token is in scope is replaced by it — the chain was being cut one call too early. Typed-gated end to end; requires exactly ONE token parameter on the enclosing binding (two make the choice a human call), .NET tupled call shapes, and never rewrites a stored `None` binding | correctness |
| FR0117 | Adjacent match arms with identical single-line bodies and no guards fold into one or-pattern arm (fix). Match order is semantics, so only a CONTIGUOUS run merges, in place — the same patterns are tried in the same order. Patterns must provably bind nothing (or-patterns demand identical bindings; a lone lowercase identifier reads as a binder and is refused); literal payloads like `Some 1`/`Some 2` are fine. Composes with FR0112: an equality chain becomes a match on one pass, and its duplicate arms fold on the next | idiom |
| FR0109 | Idempotent duplicates collapse (fix): `a \|\| a` and `a && a` → `a` — only when the operands are textually identical and contain no function or method call (operators, `not`, property chains and indexing pass). `tryConnect () \|\| tryConnect ()` is the deliberate retry idiom and never matches; the message also flags the likelier truth, a copy-paste that meant another operand | idiom |
| FR0051 | `acc <- acc @ [x]` / `acc <- Array.append acc [\|x\|]` inside a loop copies the accumulator per iteration — O(n²) (note): use a ResizeArray, or cons and `List.rev`. Also `acc <- acc + s` on a STRING (typed-proven) in any loop — the slowest string builder measured, 36x a StringBuilder at 1000 pieces; the note names StringBuilder or collect-then-`String.concat` | performance |
| FR0052 | `q.Count = 0` on `ConcurrentQueue`/`Stack`/`Bag` → `q.IsEmpty` (CA1836, fix): their `Count` walks segments, `IsEmpty` peeks | performance |
| FR0053 | `BitConverter.ToString(bytes).Replace("-", "")` → `System.Convert.ToHexString bytes` (CA1872, fix) | performance |
| FR0054 | `raise`/`failwith` inside `Equals`/`GetHashCode`/`ToString`/`Dispose` overrides (CA1065, note): implicit callers (hash containers, debuggers, formatting, finalization) never expect them to throw; raises inside the member's own `try` stay quiet | correctness |
| FR0055 | `try ... with _ -> ()` (or `:? Exception -> ()`) swallows every exception including cancellation, and `with _ -> ""` / `0` / `false` / `Unchecked.defaultof` / `None` / `ValueNone` / `null` / `[]` additionally disguises the failure as a result (note): log or `reraise ()`, and catch the specific type; deliberately ignoring a *specific* exception stays quiet, and a bool fallback is quiet only for the genuine probe idiom — a try body answering with the opposite literal (`try ...; true with _ -> false`); the editor offers, where the shape allows: a guard instead of the catch (pure-arithmetic body with one integer or decimal division; float division never throws, so no guard there), `TryParse` for a one-call `Parse` body, an IO-only catch for file IO, and a log line in the file's own logging idiom naming the exception, the method and its parameters. Test files — a test framework `open` (Xunit, NUnit.Framework, Expecto, MSTest, Fuchu, TUnit), a test attribute or an Expecto test builder; the one predicate FR0055, FR0092 and FR0132 share — are quiet: a test's catch-all is the observation, not a leak. A catch-all after a `reraise ()` arm for cancellation, or followed by an unconditional failure, is a decision and stays quiet; the one-call teardown idiom (`try x.Dispose()/Close()/Shutdown()/Cancel() with _ -> ()`) and a try around a missing-path probe that never throws (`File.Exists`, `GetLastWriteTime`) are named for what they are — the latter's advice is to delete the try; fallbacks caught too: a variable, a tuple carrying a default, a `MaxValue` sentinel, and a `when` guard that never looks at the exception | correctness |
| FR0057 | XML doc drift (note): a doc comment with `<param>` tags that misses some actual parameters — the compiler warns about *unknown* names (FS3390) but not *missing* ones; fully undocumented functions are a style choice and stay quiet; the editor offers to scaffold an empty `<param>` tag per missing name, a sweep never writes one | cosmetic |
| FR0058 | A `let rec` re-entering itself through `seq`/`taskSeq`/`asyncSeq { }` builds a fresh enumerator per recursion level — every element pays O(depth) `MoveNext`s (note): walk with an explicit `Stack`/queue inside a single builder | performance |
| FR0059 | A `private` function returning `Some`/`None` moves to `ValueSome`/`ValueNone` (fix): definition constructors and every match site rewritten together — no heap allocation per call; any use where `option` is load-bearing (`List.tryPick f`, `Option.*` pipelines, `let`-bound results, explicit annotations) suppresses the whole suggestion | performance |
| FR0060 | Consecutive attribute brackets merge: `[<Attr1>] [<Attr2>]` (stacked or same-line) → `[<Attr1; Attr2>]` (fix); comments between brackets and `[<assembly: ...>]` targets suppress it | cosmetic |
| FR0061 | `invalidArg "facotr" ...` / `ArgumentException("msg", "wrongName")` — the parameter-name string must name a real parameter of the enclosing function (CA2208, note); `nameof` keeps it honest | correctness |
| FR0062 | Non-private module-level `let mutable` is visible global mutable state (CA2211, note) — but only when it CHURNS: two-plus assignment sites in the file, or self-referential updates (`x <- x + 1`). Assigned at most once and never from itself, it reads as the two legitimate patterns — the poor-man's-DI seam a test assembly swaps, or the set-once startup config — and stays quiet, as do private mutables and private/internal modules; the editor offers `private` in one click, a sweep only notes | correctness |
| FR0063 | `raise`/`failwith` inside `finally` replaces any exception already in flight (CA2219, note); raises the finally itself catches stay quiet | correctness |
| FR0064 | Raising runtime-reserved exceptions (`OutOfMemoryException`, `StackOverflowException`, `IndexOutOfRangeException`, `NullReferenceException`, ...) misleads catchers and debuggers (CA2201, note); a match whose sibling arms raise three or more distinct exception types is a fault-injection dispatch table and stays quiet | correctness |
| FR0065 | Weak cryptography (CA5350/5351, note): MD5/SHA1/DES/TripleDES/RC2 construction, TLS certificate-validation bypass via `ServerCertificateValidationCallback`, and broken/deprecated protocol constants (`SecurityProtocolType`/`SslProtocols` Ssl2/Ssl3/Tls/Tls11 — prefer setting nothing and letting the OS negotiate, or Tls12+)  Editor alternatives: SHA1 swaps to SHA256/SHA512 (mind persisted hashes), and a weak protocol constant swaps to `Tls12` — safe even mid-OR-chain since flags-OR is idempotent, minding endpoints that only speak the legacy protocol. Quiet for the WebSocket handshake's SHA-1 when the file spells RFC 6455's GUID, and for a SHA-1 constructed in a match arm whose sibling constructs SHA-256 (a format option the caller chose) | correctness |
| FR0066 | SQL assembled from strings (CA2100, note): interpolation holes, `+` chains or `sprintf` flowing into `CommandText` or a `*Command` constructor — parameterize instead; the text is followed one hop through a `let`, and `CreateCommand(con, text)` and helpers named for SQL (`executeSql`, `runQuery`) count as sinks | correctness |
| FR0067 | `DateTime.Parse s` / `Double.Parse s` without a culture reads differently per server culture (CA1305); the editor offers the fix with `CultureInfo.InvariantCulture` (wire and config data — the clear default) and a `CurrentCulture` alternative that makes today's implicit behavior deliberate, spelled short under an existing `open System.Globalization` and fully qualified otherwise. The CLI auto-applies invariant under `{"FR0067": {"invariant": 1}}`. Integer parses are low-risk and stay quiet, and so is a Fable project — the target runtime's parsing is not culture-bound | correctness |
| FR0068 | Duplicate enum literal values (`Red = 1 ... Crimson = 1`) silently conflate cases (CA1069, note); `[<Flags>]` enums (one bit under two names) and a zero `Default`/`None` alias declared right beside its twin are deliberate synonyms and stay quiet | correctness |
| FR0069 | A private/internal record field `X: int option` / `DateTime option` / `Guid option` boxes the struct payload; `voption` keeps it flat. For a strictly FILE-PRIVATE type this is a fix: the field type and every use migrate as one edit set (`Some`/`None` constructions and patterns → `ValueSome`/`ValueNone`, `Option.xxx` → `ValueOption.xxx`, `defaultArg` → `defaultValueArg`, `= None` comparisons, `.IsSome`/`.IsNone`/`.Value` untouched) — sound because private means this file, so the typed symbol's uses are complete. Any use outside those shapes (binding the option value, flowing one in from a variable) keeps the note, as do internal/public types | performance |
| FR0070 | A private/internal record of at most four small struct fields gains `[<Struct>]` (fix), removing a heap allocation per instance — every field is an immutable small struct, so copies are semantically invisible. The fix needs the definition to head its decl (`type`, not `and`) with no other attributes (`[<CLIMutable>]` would conflict outright); a PUBLIC record under `--api-changes` stays a note, since `[<Struct>]` there is an ABI and serialization change | performance |
| FR0071 | A pure binding inside a `for`/`while`/collection lambda that depends on nothing the loop changes is re-evaluated every iteration; the fix hoists it above the loop, keeping the `#if` it was written under (the directive opens its own line above the anchor) | performance |
| FR0072 | A DU match wildcard standing in for only 1-2 concrete cases is an open else; the fix expands them (`_` → `D`), so future union growth raises incomplete-match warnings | correctness |
| FR0073 | `let! x = comp` whose binder exists only to be matched collapses to `match! comp with` (F# 4.5+) | idiom |
| FR0074 | Nested record copy-and-update flattens to F# 8 path syntax: `{ r with X = { r.X with Y = v } }` → `{ r with X.Y = v }` (LangVersion-gated; fields named after their type stay nested — the flattened path would resolve as the type) | idiom |
| FR0075 | A locally constructed disposable bound with `let` is never disposed: fix to `use` when every mention stays in scope, advice naming the destination when it is handed to a function or captured — a same-file function is read one hop: disposing the parameter (`use`, `.Dispose()`, handing it to another disposable's constructor) counts as adoption, keeping it names the leak; under `[<EntryPoint>]` a leaked stream, writer or transaction is called out as lost work (.NET runs no finalizers at exit; other handles the OS reclaims), and in an ASP.NET action, controller or SignalR hub member the leak is per request and carries warning weight; returning it (also inside a tuple, record, upcast or `Some`/`ValueSome`/`Ok`), passing it to another disposable's constructor, or storing it in a field, property, collection (`Add`, `xs.[i] <-`), module value or ref cell is an ownership transfer, not a leak (the holder is FR0032/FR0047's business) — a transfer silences the rule even when the value was also handed elsewhere; a store into a local mutable stays a note naming the local; manual `Dispose()` calls, `(x :> IDisposable).Dispose()` and `Close()` on streams, writers, readers and sockets exempt; `StringReader`, `StringWriter` and a `MemoryStream` over a caller's buffer own nothing and are skipped; `MD5`/`SHA*`/`Aes`/`RandomNumberGenerator.Create()` count as constructions | correctness |
| FR0076 | `List/Array.map f \|> ignore` allocates a discarded list — fix to `iter (f >> ignore)`; `Seq.map f \|> ignore` is lazy and runs NOTHING (advice, the FR0017 family) | performance |
| FR0077 | An object expression missing interface members (FS0366) gets `NotImplementedException` stubs for every missing method/property, inherited interfaces in their own `interface X with` sections — the only rule that runs on non-compiling code, which is its point The editor also offers stubs that return the empty value of each member type (`()`, `None`, `[]`, zeros, `Unchecked.defaultof<_>`) instead of raising; the sweep applies only the raising form. | correctness |
| FR0078 | The three-part mutable-condition loop idiom (`let! first` / `let mutable go` / rebind at loop end) collapses to F# 8 `while!` — a lone stale-bool `while` never matches, `while!` re-evaluates per iteration | idiom |
| FR0079 | `Task.WhenAll [\| t \|]` / `Task.WaitAll` / `Async.Parallel [ c ]` over a single-element literal adds indirection for nothing (CA1842/CA1843, note — the direct form changes the result type, so the author picks the landing shape) | performance |
| FR0080 | Leading TABs (FS1161 — pasted code often brings them) expand to four spaces per tab, every affected line in one fix; files with triple-quoted/verbatim strings are skipped (a tab could be string content) | correctness |
| FR0081 | Path fragments joined with a hard-coded `/` or `\` separator → `Path.Combine` advice; `\` fires alone, `/` needs positive path evidence (path-ish names, rooted/extension literals, or a literal existing on disk) and URL-smelling chains never fire — a same-file binding is resolved one hop for that test (`gitHome + "/" + name` where `gitHome = "https://github.com/" + owner`); a join that is only compared or searched for is a key, not a path; path evidence is read per operand, and a call counts only through the file-system API it invokes, so `path` in a function's name is no evidence | idiom |
| FR0082 | `[<FooAttribute>]` → `[<Foo>]` — the compiler resolves the short form | cosmetic |
| FR0083 | `[<Foo()>]` → `[<Foo>]` — an empty attribute argument list says nothing | cosmetic |
| FR0084 | ` ``name`` ` backticks around a plain non-keyword identifier do nothing; stripped per site | cosmetic |
| FR0085 | `new` on a non-IDisposable construction is noise — F# convention reserves `new` for disposables (the compiler warns the inverse as FS0760); typed-gated | cosmetic |
| FR0086 | `$"no holes"` → `"no holes"` — hole-free interpolation; skipped when escaped braces would need unescaping | cosmetic |
| FR0087 | The pattern `x :: []` → `[ x ]` | idiom |
| FR0088 | `Case(_, _)` → `Case _` when every field is a wildcard (typed-gated to real union cases; survives field-count changes) | cosmetic |
| FR0089 | `[ 1, 2 ]` is a SINGLE-tuple list — `,` builds a tuple, `;` separates elements (note; the classic paste trap, single-tuple lists are sometimes intended); quiet when the slot the literal fills expects tuples — a parameter typed `(k * v) list`/`seq` (`Map.ofList [ k, v ]`, `dict [ 1, 1 ]`, a tupled method argument), or an annotation spelling the tuple out | correctness |
| FR0090 | Tupled → curried for internal/public functions with every project call site rewritten (cross-file; `fsharp-refactor --api-changes` only, editors get the private-only FR0008) | idiom |
| FR0091 | Data-last parameter reorder for internal/public functions with every project call site rewritten (cross-file; `fsharp-refactor --api-changes` only, editors get the private-only FR0023). The two parameters must have different concrete types, so that a call site outside the project — which we can neither see nor fix — fails to compile rather than silently swapping two interchangeable arguments | idiom |
| FR0092 | A constant `failwith "Error"` gains the enclosing function's arguments — `failwith $"Error, calling mymethod with x: {x}"` — so the log says which call failed, not just which line. Static messages only; an already-interpolated one was written deliberately, as was one that already names a parameter. NOTE: the exception TEXT is observable behavior — a test asserting the exact message will need updating (found the honest way: one such assertion in a 4,949-test suite). Quotes only arguments whose type prints (primitives, strings, enums, small records — never readers, streams, sockets, functions or compiler contexts); quiet on invariant messages (unreachable, not possible, NYI, internal error, invalid case), in security-named scopes (auth/session/crypt/token/password/secret), in test files, and for a message that is the function's own name; two throws sharing a text both get the note, a tuple parameter no longer disqualifies the function, and a `function` names its wildcard arm to quote the argument | idiom |
| FR0093 | A private/internal record field `X: int * int` is a reference tuple — one heap object per value — where `struct (int * int)` stores it inline. At most four elements, since a struct tuple is copied by value. For a strictly FILE-PRIVATE type the fix migrates the field and every use in one edit set (literal-tuple constructions, match/let destructurings, literal comparisons — `struct` spelled onto each); any use passing the tuple along whole (`fst`, a binder) keeps it a note | performance |
| FR0094 | Redundant parentheses around a single atomic argument to an instance *method*: `s.Contains("x")` → `s.Contains "x"`. Separate from FR0013 so either preference can be switched off alone. Left alone where the line continues into an application (`s.Contains("x") <> false` would read as if `"x" <> false` were the argument), under a projection, and for uppercase-headed paths — `System.Uri("x")` is a constructor, whose parens are load-bearing | cosmetic |
| FR0095 | A lambda that restates a built-in: `fun x -> x` → `id`, `fun (a, b) -> a` → `fst`, `fun (a, b) -> b` → `snd`. One unannotated parameter only, and never as a direct argument to a .NET method, where the lambda-to-delegate conversion is doing work a function value may not | idiom |
| FR0096 | Redundant parentheses around a pattern: `\| (Some y) ->` → `\| Some y ->`, `let f (x) = x` → `let f x = x`. The whole pattern of a match clause, or a bare atom elsewhere — `Some (x, y)`, `Some (Some x)`, `f (x: int)` and member parameters all keep theirs | cosmetic |
| FR0097 | Redundant parentheses around a type: `(x: (int))` → `(x: int)`, `(string) list` → `string list`. Function and tuple types keep theirs, where the parens bind the type together | cosmetic |
| FR0098 | The BCL name of a type F# abbreviates: `System.Int32` → `int`, `System.String` → `string`, `System.Object` → `obj`. Only the fully qualified form; a bare `Int32` depends on the opens and on what the file declares | cosmetic |
| FR0099 | A `;` ending a line does nothing in light syntax: `let x = 1;` → `let x = 1`. Kept where it separates rather than terminates — inside a list, array, record, anonymous record or attribute group — and everywhere in a file that sets `#light "off"`. `;;` is left alone. OFF BY DEFAULT: it lexes every file containing a line-ending `;` and rarely finds anything — enable via `"FR0099": true` in fsharprefactor.json, or ask for it with `--codes FR0099` | cosmetic |
| FR0100 | A match branch that says it is unfinished and then returns a stand-in — `\| Jordan ->` / `// Not supported yet` / `None` / `ValueNone` / `false` — becomes `raise (NotImplementedException())`, so the gap reports itself instead of reaching callers as a real-looking result. The comment must sit inside the branch, between the arrow and the value, where it describes that branch and nothing else; a bare `TODO` elsewhere never counts, and `\| Unknown -> None` with no such comment is left alone. `null` and `Unchecked.defaultof<_>` need the comment too — `\| [] -> Unchecked.defaultof<'T>` is the entire contract of a SingleOrDefault, and `\| null -> null` passes a sentinel through. Only fires where sibling branches actually compute, so a table of constants is not mistaken for a stub | correctness |
| FR0101 | The Python `range(len(xs))` loop: `for i in 0 .. xs.Length - 1 do ... xs.[i]` → `for item in xs do ... item`, when the index's every use is indexing that same collection. Fix rewrites the header and each `xs.[i]`/`xs[i]`; an index also used as a value wants `iteri`, which changes shape enough to stay the author's call, and any `xs.[i] <- ...` keeps the loop | idiom |
| FR0102 | Positional indexing into an F# LIST inside a loop — `names.[i]` walks i cons cells per access, the quietest quadratic in F#. Typed: arrays, ResizeArray and dictionaries share the syntax and are fine; `List.item`/`List.nth` pin the type by name. Constant indexes (`xs.[0]`) and receivers bound inside the loop — by a let, a lambda parameter or a match arm's pattern — are skipped; `xs.Length`/`List.length xs` on a loop-invariant list inside a loop body gets the same note (a `for` header evaluates once and is fine). Advice: iterate directly (FR0101 fixes the canonical shape) or convert once with `List.toArray` | performance |
| FR0103 | The Python isinstance ladder: an if/elif chain of `shape :? T` tests with `shape :?> T` casts in the branches becomes one `match` with `\| :? T as v ->` patterns — one type test per branch instead of test-plus-cast, and the unsafe `:?>` (an InvalidCastException waiting for a branch reorder) disappears. Needs two or more bare type-tests on the same plain identifier, single-line branches, and every cast targeting its own branch's type; a compound condition or a cross-cast keeps the chain | idiom |
| FR0104 | A singleton append to an accumulator in a RECURSIVE call — `collect (acc @ [x]) rest` copies the whole accumulator every step, O(n²), and it is the shape first drafts produce more when told to avoid mutation. Note only: the repair is `x :: acc` with one `List.rev` in the base case, or an array/ResizeArray when the result is consumed positionally — the base case changes either way. A general `a @ b` merge is left alone | performance |
| FR0105 | Arithmetic (`+`, `-`, `*`) on a NEAR-LIMIT integer constant — within a factor of two of `Int32.MaxValue`, or ten-ish digits into int64 territory. F# operators are unchecked by default, so overflow wraps silently and the corrupted value flows on. Note only: `open Microsoft.FSharp.Core.Operators.Checked` makes the scope throw instead, a wider type removes the ceiling, or the wraparound is intended and deserves saying so. Decimal spellings only (hex is a mask), unsigned skipped, and a file already opening Checked is left alone; a multiplication by a million or more (the time-unit conversions) and `Int32.MaxValue + e` count too; the editor offers widening to int64 first and `Checked.( op )` second | correctness |
| FR0106 | `Int32.Parse(s.Substring(6, 5))` → `Int32.Parse(s.AsSpan(6, 5))` (fix — a one-identifier swap). The Substring copy is discarded the moment the parser reads it; AsSpan parses in place, measured 2.6x and allocation-free. Fires only when the Substring is DIRECTLY the parser's argument (no escape), the receiver is typed-proven string, and the compilation actually offers the `ReadOnlySpan<char>` overload — which is how netstandard2.0/net4x stay untouched with no TFM sniffing. Framework methods (StartsWith, Contains, interpolation) already run on spans internally and need no rule | performance |

## Configuration

Rules can be disabled per repository with an optional `fsharprefactor.json`,
searched upward from each analyzed file, stopping at the repository root (the
nearest file wins). Keys are rule codes or analyzer names, case-insensitive;
a malformed file fails open so it can never break the editor. Comments and
trailing commas are tolerated.

`fsharp-refactor --create-config` writes one for you: every rule this build
knows at its current default, every run-level key at its own default, one
comment each. Nothing in it changes anything until you edit a line — flip
what you disagree with, delete the rest to keep following the defaults as
they change. It refuses to overwrite an existing config.

```json
{
  "rules": {
    "FR0003": false,
    "conversionMove": { "enabled": false }
  }
}
```

Rules with tunable thresholds read numeric properties from the same
object-valued entries. FR0114 takes `thenAtLeast` (default 20), how long
a then-branch must be before flipping is suggested, and `elseAtMost`
(default 3), how short the else must stay:

```json
{
  "rules": {
    "FR0114": { "enabled": true, "thenAtLeast": 30, "elseAtMost": 2 }
  }
}
```

FR0060 takes `maxAttributes` (default 4), how many attributes may share
one `[<A; B>]` bracket, and `wrapColumn` (default 110), how wide the
merged line may get. Both are house style rather than correctness, and
the rule simply declines to merge past either limit:

```json
{
  "rules": {
    "FR0060": { "enabled": true, "maxAttributes": 6, "wrapColumn": 120 }
  }
}
```

Paths can be excluded too — additively over the built-in defaults
(`paket-files`, `.paket`, `node_modules`), which cover generated and
vendored code a compilation nonetheless includes:

```json
{
  "ignorePaths": [ "generated", "external/imported" ]
}
```

A bare name matches as a whole path segment; an entry containing a slash
matches anywhere in the normalized path; an entry containing `*` is a
glob — `*` stays within a segment, `**` crosses them (`*.g.fs`,
`src/generated/**`). Ignored files are neither analyzed nor even
type-checked by the apply tool's sweep — on a paket-heavy solution that
is a lot of vendored source nobody wants "fixed". Files opening with the
conventional `// <auto-generated>` marker are skipped automatically
wherever they sit, as is everything under `obj/`.

Individual findings can be silenced in place with the F# analyzer SDK's
own suppression comments — the same ones editors honor, so one comment
silences both the light bulb and the apply tool (a suppressed finding is
neither reported nor fixed):

```fsharp
// fsharpanalyzer: ignore-line-next FR0106
let orderNumber (s: string) = Int32.Parse(s.Substring(6, 5))

let inline dodgy (s: string) = s.Substring(0, 3) // fsharpanalyzer: ignore-line FR0106

// fsharpanalyzer: ignore-file FR0031, FR0038
// fsharpanalyzer: ignore-region-start FR0002
// fsharpanalyzer: ignore-region-end
```

Suppression comments are also easy to reach for, and a team may not want
a correctness finding silenceable with one line of punctuation the way a
naming nit is. The `"suppressions"` policy draws that line:

```json
{ "suppressions": "no-correctness" }
```

- `"all"` (default) — every suppression comment silences its finding.
- `"no-correctness"` — comments on correctness-category rules are
  reported anyway; idiom, cosmetic, and performance suppressions still
  work. An overridden finding is never auto-FIXED — the tool does not
  rewrite code over someone's explicit comment — it is reported (and
  fails `--fail-on-findings`) until addressed or the comment is judged
  worth honoring.
- `"none"` — every suppression comment is reported anyway.

`--honor-suppressions` on the command line overrides the policy to
`"all"` for that run. A repo that wants suppressions inert on developer
machines but honored by the pipeline commits `"no-correctness"` (or
`"none"`) in its config and passes the flag in CI only. Whatever the
policy, the run summary counts what comments silenced — suppression is
never silent. Note the policy only governs this tool: editors honor the
SDK's comments natively, so the light bulb stays silenceable regardless.

### Is your public surface an API?

Two of the config's keys decide how much of `--api-changes` applies
without the flag, and they are worth keeping apart, because they gate
two different risks.

```json
{ "publicApi": false }
```

F# makes a declaration public by default, so `public` in a parse tree is
usually the absence of a decision rather than one. The scope-gated rules —
the ones whose fix changes a declaration's compiled SHAPE in place,
`[<Struct>]`, `[<Literal>]`, named union fields, a field's `option`
becoming `voption` — hold back on public declarations because a consumer
in another assembly would see the change and nothing here can check it.
`"publicApi": false` says there is no such consumer: an application, an
internal tool, a leaf project. Those rules then treat public as internal,
in the apply tool AND in the editors, where `--api-changes` has never been
reachable. It licenses no edit outside the file being analysed.

**With no setting, the compilation answers.** An `OutputType` of `Exe` or
`WinExe` has no external linker — nothing can reference its public
declarations — so it is read as a leaf and the gate opens by itself. A
library is not, and stays closed. Write `"publicApi": true` to overrule
that: an executable that serializes its own public types, or loads plugins
by reflection, wants the conservative behaviour back.

Scripts are answered file by file rather than as a whole compilation. A
`.fsx` is the ultimate leaf — it links to nothing and nothing links to it —
so its own declarations are in scope. What it `#load`s is not: that source
belongs to whatever project owns it, quite possibly a library, and a script
reading it says nothing about who else compiles it.

The scripts that get a vote are the `.fsx` under the solution or project
folders being run, and their subfolders - not the whole drive, and not a
path `ignorePaths` excludes: a path this repository has told the tool to
ignore is external code, and external code does not decide how this
repository's declarations are shaped. So the guarantee is that no script
INSIDE the tree this run is responsible for is left calling a name that
moved.

```json
{ "apiChanges": true }
```

The other risk: a fix that must edit OTHER FILES — currying a function
(FR0090) or reordering its parameters (FR0091) and rewriting every call
site in the project. This is `--api-changes` as a standing decision, for a
repository where it is always the right answer; it covers everything the
flag does and so implies `publicApi: false`. A run started with the flag
is unaffected, and the config can only ever widen, never take the flag
away. The run says so when it picks the setting up.

A companion `.fsi` still wins over both: a signature file is the author's
own statement of what is exported — including the `val private` it is free
to write — so a shape change beside one stands down for any name the
signature declares. And FR0092 (constant `failwith` messages) is not a
visibility rule at all — its risk is a test or a caller reading the text —
so it stays behind the flag alone.

**What the gate holds back is reported, not hidden.** A run ends with, say

```
  7 finding(s) held back by scope: 4 FR0070, 3 FR0022 — public declarations
  this run may not reshape. Set "publicApi": false in fsharprefactor.json if
  nothing outside this assembly links to them or serializes them.
```

so the decision is a decision, not something to guess at. Answer it once
and the tool applies all of them; nobody should be retyping by hand what
the tool could have written.

**Editors offer them anyway, with the caveat attached.** A light bulb is
per-site consent from the one person who can actually answer the question,
and it costs a click rather than a manual edit, so in an editor these
findings appear on public declarations too:

> Union 'Shape' holds only small value types; `[<Struct>]` avoids a heap
> allocation per value. **CHANGES THE PUBLIC SHAPE: safe only if nothing
> outside this assembly links to it or serializes it (JSON, XML, protobuf —
> the tool cannot tell).**

That last clause is not modesty. Serialization cannot be detected:
System.Text.Json, Newtonsoft, `XmlSerializer`, `DataContract`, protobuf,
MessagePack and whatever a *consumer* wired up by reflection all read the
compiled shape, and a guard that enumerated some of them would break the
rest silently. So the tool never infers that a shape change is safe to
serialize — it says what changes and leaves the judgement to the reader.
The apply tool, having nobody to ask, only counts them.

A disabled rule skips its analysis entirely, so the file also works as a
performance lever on large codebases. Internally all analyzers share one
memoized AST traversal per file version, so the editor pays for a single
walk per keystroke regardless of how many rules are active.

Every rule defaults to enabled except two:

- FR0099 (line-ending semicolons) lexes every file containing one and
  rarely finds anything — cost out of proportion to a cosmetic default.
- FR0002 (match option → Option combinators) is the one measured rewrite
  that makes YOUR code slower — +53% and a closure allocation per call on
  its benchmark pair. Nice to read, costs to run; opt in when that trade
  suits the codebase.

Turn either on with `"FR0099": true` / `"FR0002": true`, or ask
explicitly: the apply tool treats `--codes FR0002` as outranking both the
default-off status and a config disable — naming a rule is an ask. A
`--categories` filter deliberately is not one: `--categories idiom` runs
the idiom rules that are on, and does not quietly wake the default-off
ones.

The same file can add custom FR0012 term-rewriting rules using FSharpLint's
hint syntax (single-letter identifiers are metavariables):

```json
{
  "hints": {
    "add": [
      "Option.isSome x |> not ===> Option.isNone x"
    ]
  }
}
```

Custom rules get the same safety treatment as the built-ins: bindings are
parenthesized as needed, and a rule whose right side drops or duplicates a
metavariable only fires on pure atoms (never discarding a side effect).

---

# Improving it

Contributions welcome. This section is for working ON the analyzers; everything
above is for using them.

## Trying your changes

Build the analyzers, then point either host at the build output instead of the
NuGet cache.

In an editor, via the target repo's `.vscode/settings.json`:

```json
{
  "FSharp.enableAnalyzers": true,
  "FSharp.analyzersPath": ["<path-to>/FSharp.Refactor.Analyzers/bin/Debug/net8.0"]
}
```

Open an F# file containing e.g. `match x with | true -> 1 | false -> 2` — a
hint appears offering `if x then 1 else 2`.

Or from the CLI:

```bash
fsharp-analyzers --project YourProject.fsproj --analyzers-path src/FSharp.Refactor.Analyzers/bin/Debug/net8.0 --code-root .
```

Note: analyzers must be built against an FSharp.Compiler.Service compatible with
the host FsAutoComplete. This project currently pins FSharp.Analyzers.SDK 0.37.2
(FCS 43.12.201). See the SDK's version-pairing table when updating.

## Building and testing

```bash
dotnet build
dotnet test
```

This project eats its own dog food. Before committing:

```bash
dotnet tool restore
dotnet fantomas src tests
dotnet dotnet-fsharplint lint src/FSharp.Refactor.Analyzers/FSharp.Refactor.Analyzers.fsproj
dotnet dotnet-fsharplint lint src/FSharp.Refactor.Tool/FSharp.Refactor.Tool.fsproj
dotnet dotnet-fsharplint lint tests/FSharp.Refactor.Tests/FSharp.Refactor.Tests.fsproj
```

and the analyzers are run against their own source, expecting zero findings.
Both projects, not just the analyzers — the apply tool is F# we ship too, and
it went a long time unchecked:

```bash
dotnet tool run fsharp-analyzers --project src/FSharp.Refactor.Analyzers/FSharp.Refactor.Analyzers.fsproj --analyzers-path src/FSharp.Refactor.Analyzers/bin/Debug/net8.0 --code-root .
dotnet tool run fsharp-analyzers --project src/FSharp.Refactor.Tool/FSharp.Refactor.Tool.fsproj --analyzers-path src/FSharp.Refactor.Analyzers/bin/Debug/net8.0 --code-root .
```

Test inputs are string literals, so formatting tools never touch the
deliberately-shaped source fragments the tests exercise.

## Design principles

1. **Never break user code.** A fix is only offered when it is provably safe to apply;
   borderline cases simply don't produce a suggestion. Fixes are minimal range-based
   text edits applied by the editor, so they are always a single native undo step.
2. **Minimal edits.** Original formatting outside the edited range is untouched —
   no whole-file reformatting.
3. **Pure core, thin adapters.** Each refactoring is a pure function
   `ParsedInput -> ISourceText -> Suggestion list`, unit-tested directly against
   source strings. The SDK analyzer entry points in `Analyzers.fs` are one-liners.
4. **Hints point toward idiomatic F# only.** Every analyzer rewrites `a → b`
   where `b` is the more idiomatic form; we never ship a hint that moves code
   *away* from idiomatic F#. That is why suggestions are `Hint` severity, not
   warnings: they mark an opportunity, not a defect, and they never gate CI.
   Genuinely reversible rewrites where neither direction is more idiomatic
   (`if ↔ match`, tupled ↔ curried) belong in FsAutoComplete's codefix
   infrastructure as user-invoked `refactor.rewrite` actions, and should be
   contributed there rather than here.

## Our Vision, and Other projects in the same field

AI Agent compatibility: This project does distinct the F# code from generated Python smell. Meanwhile, some past rules (like function length and cyclomatic complexity) are expected to gains less attention in the future.
This project has focus on idiomatic F#, code performance and best practices, and less interest on code structure/naming/maintainability.

This project aims to be compatible with other products, so you won't end-up having oscillation/fight between suggested changes.

| Tool | Same rules | Status |
|---|---|---|
| FxCop and [MS Code Analysis](https://learn.microsoft.com/en-us/dotnet/fundamentals/code-analysis/quality-rules/) | Many | We have implemented the MinimumRecommendedRules, and some performance etc. rules relevant to F# |
| [FSharpLint](https://fsprojects.github.io/FSharpLint/) | Many | Instead of just listing, we have quick-fixes and auto-fix. Rules are compatible with this project. |
| [Resharper F#](https://github.com/JetBrains/resharper-fsharp) | Many | Have many same features, meanwhile using totally different AST. |
| [Resharper C#](https://www.jetbrains.com/resharper/features/) | Partial | Resharper has heavy focus on OO meanwhile we focus on FP. Many C# issues don't exist in F# at all (like clojure captures, etc.). |
| [Linq.Expression.Optimizer](https://thorium.github.io/Linq.Expression.Optimizer/) | Some | We optimize compile-time, meanwhile this tool optimize runtime-code |
| [SonarQube](https://docs.sonarsource.com/sonarqube-cloud/standards/ai-code-assurance/quality-profiles-for-agentic-ai) | Minor | Most of SonarQube rules are opinionated enterprise development rules ported from Java. But we have some of the same .NET relevant rules. |
| [G-Research FSharp Analyzers](https://g-research.github.io/fsharp-analyzers/) | Not really | Good rules to focus maintainability. Different focus. Should work well together. |
| [Fantomas](https://fsprojects.github.io/fantomas/) | None | Different focus: Fantomas is a code layout tool. We are compatible so you can use both. |
| [FSharp.Analyzers.SDK](https://ionide.io/FSharp.Analyzers.SDK/) | None | Our tool, fsharp-refactor, is built on FSharp.Analyzers.SDK |

