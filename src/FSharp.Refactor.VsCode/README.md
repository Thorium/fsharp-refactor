# FSharp.Refactor for VS Code

**[Get it from the Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=TuomasHietanen.fsharp-refactor-vscode)**


View -> Command Palette -> FSharp.Refactor to drive the command line tool for the full project:

<img width="590" height="189" alt="image" src="https://github.com/user-attachments/assets/aecd7d21-bcb5-4eaf-b932-332809dc7113" />


And IDE light bulbs while you type

<img width="1010" height="302" alt="image" src="https://github.com/user-attachments/assets/e8a2e72a-3096-4963-824a-3f6a91a085b9" />


150+ functional refactoring hints with one-click quick fixes for F#,
delivered through Ionide.

VS Code has no analyzer concept of its own — F# analyzers load through
Ionide → FsAutoComplete → FSharp.Analyzers.SDK, from the directories the
`FSharp.analyzersPath` setting names. This extension bundles the
FSharp.Refactor analyzer assemblies (both SDK builds: FsAutoComplete
loads the one matching its own SDK version and skips the other) and, on
first activation, **asks** to append its analyzers directory to that
setting and turn `FSharp.enableAnalyzers` on. Decline and it stays out of
your settings; the `FSharp.Refactor: Wire analyzers into Ionide` command
re-offers it any time, and the `Remove` command undoes it.

After wiring and a window reload, open any F# file: suggestions appear as
`Hint`-severity squiggles with `FR`-prefixed codes, each carrying a
light-bulb quick fix (`Ctrl+.`).

Six more commands:

- `FSharp.Refactor: Status (versions and wiring)` — the extension and
  analyzers versions, whether the analyzers directory is wired into
  `FSharp.analyzersPath` (and any stale entry from an older version),
  Ionide's version and the FsAutoComplete it runs, and whether the
  `fsharp-refactor` dotnet tool is installed. The first thing to run when
  no hints appear.
- `FSharp.Refactor: Run the tool on this workspace` — the light bulbs fix
  one finding at a time; this runs the sweep. Picks a solution or project
  of the workspace, then `Report only` (`--dry-run`), `Apply fixes`, or
  `Apply fixes with --api-changes`, in the integrated terminal. Every pass
  the tool applies is build-verified and rolled back on error, as on the
  command line; it offers to install the tool when it is missing.
- `FSharp.Refactor: Run the tool with --api-changes` — the same sweep with
  the scope gate opened: rules that only fix private or internal
  declarations by default also rewrite public ones, and cross-file
  signature changes (FR0090, FR0091) rewrite their call sites project-wide.
  Asks report-only or apply first.
- `FSharp.Refactor: Write a SARIF report for this workspace` — a dry run
  with `--report`, for code scanning or as the `--baseline` of a later run.
  Asks where to write it; `.csv` and `.html` paths are written in those
  formats instead.
- `FSharp.Refactor: Create or open the configuration file` — writes a
  `fsharprefactor.json` of this build's defaults into the workspace root and
  opens it, or opens the one already there (an existing config holds your
  decisions and is never replaced). Every rule, plus `publicApi`,
  `apiChanges`, `ignorePaths` and `suppressions`, each with a comment. It
  changes nothing until you edit a line.
- `FSharp.Refactor: Review advisory notes as a page` — the findings that
  carry no fix, as a self-contained HTML page opened in your browser.
  Unlike everything else the tool does, these are only worth anything if a
  person reads them; the SARIF report is for CI, this is for you. Runs
  `--notes only` and writes nothing to your code.

Alternative without this extension: reference the
`FSharp.Refactor.Analyzers` NuGet package and point `FSharp.analyzersPath`
at the restored package — per-project instead of global; see the
[project README](https://github.com/Thorium/fsharp-refactor).

## Building

```
pwsh -File CreateVsCodeVsix.ps1
code --install-extension artifacts/fsharp-refactor-<version>.vsix
```

The version is stamped from the repo's `Directory.Build.props`, the same
single source as the NuGet packages and the Visual Studio extension.

## The durable fix

Mutating user settings is a workaround for Ionide having no extension
point for third-party analyzer directories. The right long-term shape is
an Ionide `contributes`-style API where an extension declares its
analyzer paths and Ionide collects them — worth proposing upstream; this
extension then shrinks to a manifest entry.
