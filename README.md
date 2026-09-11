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
| `correctness` | The code does something other than what it looks like it does: a race, a swallowed exception, a disposable that leaks, a comparison that never holds | 52 |
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
parameters data-last (FR0091) — rewriting every call site in the project,
in the scripts that `#load` it, and in the sibling projects of the same
solution that reference it (the test project, typically) or compile one
of its sources directly (a linked file; such a fix line says
` note: linked file`). Without it those are held back and only counted. It
also widens the contained-type hints (FR0022, FR0069, FR0070, FR0093) to
public types. Consumers outside
the run are why this is opt-in: their call sites cannot be rewritten, so
a public function changes shape only when every project referencing it
in the run is an F# project that typechecks — a referencing C# project, a
sibling with errors, a script `#r`ing the built assembly or a bare project
with no solution above it holds the public surface as it is, and the run
says so — and each rule only fires where a call site it still cannot see
would fail to compile rather than change behaviour silently. Naming a
single source file skips these entirely — asking for one file and getting
edits in its callers would be a surprise.

The flag bundles two separable things: fixes that edit OTHER files, and
the widening of in-place shape changes to public declarations. Only the
first needs asking for: an assembly nothing links against — an executable,
a script — gets the second by itself, and a library opts in with
`"publicApi": false` in `fsharprefactor.json`. Either way it reaches the
editors, where the flag never has.
See [Is your public surface an API?](#is-your-public-surface-an-api).

## Refactorings

Every rule lives in [Rules.md](Rules.md): a one-line table for scanning —
what each fires on, the fix it offers, whether it is on by default, whether
its fix needs `--api-changes` — followed by a section per rule with the full
reasoning. The tests keep that file and the catalog in step.

Roadmap based on ["F# refactoring possibilities"](https://www.slideshare.net/ThoriumT/f-refactoring-possibilities).

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

A few entries are on/off switches rather than thresholds, and read a JSON
bool as happily as `1`. FR0029 takes `tailLines` (default 40), how many
non-awaiting lines after the last await earn a tail extraction on a task
the compiler did NOT warn about — where FS3511 names the task, the apply
tool reads that off the build and the extraction is offered regardless —
and `hoistReturnOnAsync` (default false), which extends just the return
hoist, not the FS3511 advice, to `async { }`:

```json
{
  "rules": {
    "FR0029": { "tailLines": 25, "hoistReturnOnAsync": true }
  }
}
```

FR0065 takes `dropLegacyProtocols` (default false). Retiring `Ssl3`/`Tls`/
`Tls11` changes what the process negotiates with a remote endpoint, so it
is an editor offer by default; setting this lets an unattended run comment
the dead protocol out of the flags. `--api-changes` deliberately does not
grant it — that flag is about callers needing a recompile, which is a
different risk:

```json
{
  "rules": {
    "FR0065": { "dropLegacyProtocols": true }
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

