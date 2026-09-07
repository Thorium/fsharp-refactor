# FSharp.Refactor for Visual Studio (classic VSIX)

**[Get it from the Visual Studio Marketplace](https://marketplace.visualstudio.com/items?itemName=TuomasHietanen.fSharp-refactor)**

Tools > FSharp.Refactor -menu to drive the command line tool for the full project:

<img width="354" height="188" alt="image" src="https://github.com/user-attachments/assets/62409f1e-a177-49f0-9b5b-616f6b88ea25" />


And IDE light bulbs while you type

<img width="1136" height="215" alt="image" src="https://github.com/user-attachments/assets/cd4e3ed3-1ca6-40b6-bab4-da590e6d0410" />


Squiggles and light-bulb quick fixes from the FSharp.Refactor analyzers
inside full Visual Studio, using the classic in-proc MEF editor surfaces:

- `ErrorTagger.fs` — `IViewTaggerProvider`/`ITagger<IErrorTag>` on content
  type `F#`, rendering each FR diagnostic with the editor's hinted-
  suggestion style.
- `SuggestedActions.fs` — `ISuggestedActionsSourceProvider`/
  `ISuggestedAction` (the light bulb), titles and edits straight from the
  sidecar's code actions.
- `FsacClient.fs` + `Lsp.fs` — an **FsAutoComplete sidecar** spoken to
  over LSP stdio. Out-of-process on purpose: VS's own F# tools load their
  own FSharp.Compiler.Service in-proc, and loading ours beside it is the
  assembly-binding wound Visual F# Power Tools kept reopening. We consume
  exactly two things: `publishDiagnostics` (filtered to FR codes — VS
  already shows compiler errors) and `textDocument/codeAction`.
- `BufferSessions.fs` — didOpen/didChange sync per `ITextBuffer`,
  debounced.

## Build + try

```bash
powershell -File src/FSharp.Refactor.Vsix/CreateVsix.ps1
```

then install into the experimental instance and start it:

```bash
VSIXInstaller /rootSuffix:Exp src/FSharp.Refactor.Vsix/artifacts/FSharp.Refactor.vsix
devenv /rootSuffix Exp
```

Open an F# project (`C:\git\refactortest` is a ready trigger corpus) and
watch for dotted suggestion underlines; `Ctrl+.` on one shows the fixes.

FsAutoComplete is located as the global dotnet tool
(`%USERPROFILE%\.dotnet\tools\fsautocomplete.exe`, install with
`dotnet tool install -g fsautocomplete`), or from an `fsac\` folder beside
the extension dll if you bundle one. The bundled `analyzers\` folder
carries both SDK builds of the analyzers; FSAC loads the one its
FSharp.Analyzers.SDK version pairs with and log-skips the other.

## The menu, and why it was invisible for a day

The compiled command table has to be embedded INSIDE a managed `.resources`
set. Not as a standalone manifest resource:

```xml
<!-- WRONG. Looks perfect, reads back fine, merges NOTHING. -->
<EmbeddedResource Include="$(IntermediateOutputPath)FSharpRefactor.cto"
                  LogicalName="Menus.ctmenu" />
```

`PackageRegistration(UseManagedResourcesOnly = true)` makes the shell resolve
`ProvideMenuResource("Menus.ctmenu", 1)` as an ENTRY INSIDE the package's
resource set â€” which is what the VSSDK's `MergeWithCTO=true` on a `.resx`
produces, and the one thing the VSSDK does for you that this hand-rolled
packaging did not. Nothing ever looks in the standalone stream, and the miss
is completely silent: no error, no warning, no ActivityLog entry.

So `EmbedCto.ps1` writes `VSPackage.resources` and
`FSharpRefactorPackage.resources`, each holding one entry `Menus.ctmenu` whose
value is the `.cto` bytes, and both are embedded. Its target uses
`DependsOnTargets="CompileCommandTable"` â€” with `AfterTargets` MSBuild ran it
BEFORE VSCT and cheerfully embedded a 0-byte table.

There were TWO faults, and fixing either alone changed nothing visible. The
second: a `<Menu type="Menu">` needs

```xml
<CommandFlag>AlwaysCreate</CommandFlag>
```

or the shell declines to create the submenu when it cannot see children at
merge time. With merging fixed but this missing, a probe button parented into
a built-in group appeared while our submenu still did not â€” which is exactly
how the two faults were told apart.

Placement matters separately: do not parent a submenu to
`IDG_VS_TOOLS_EXT_TOOLS`. That is the EXTERNAL TOOLS group, which the shell
fills dynamically. Use a group of your own under `IDM_VS_MENU_TOOLS`, the
shape the VSSDK samples use.

### If the menu is missing again, read this before you start guessing

A package that loads is NOT evidence of anything. Menu merging happens at
configuration time and package loading at solution time; they share nothing.
Ours logged `Begin/End package load [FSharp.Refactor]` cleanly and registered
all seven commands while contributing nothing whatsoever to the menus.

What is worth doing, roughly in order:

- **Drop a probe button** into a built-in group that certainly renders, e.g.
  `IDG_VS_TOOLS_OPTIONS` (where `Options...` lives). One launch then splits
  "the table does not merge at all" from "the table merges and our placement
  is wrong". This is the single highest-value hour in the whole exercise.
- **Instrument the loader.** `InitializeAsync` traces entry, the number of
  commands registered, the concrete type when the `IMenuCommandService` match
  falls through, and any exception. A silent loader makes "loads fine" and
  "registers nothing" indistinguishable.
- **Read the Exp private registry** without admin: `RegLoadAppKey` in
  advapi32 plus `RegistryKey.FromHandle`. `reg load` needs privileges you do
  not have. Look at `<hive>_Config\Packages\{pkg guid}` (is `$PackageFolder$`
  substituted?) and `<hive>_Config\Menus`.

And what is NOT worth doing, all of it tried:

- `1033\devenv.CTM` is a COMPRESSED CFCT v5. VSCT 17.9 refuses it
  (`VSCTCompressionReadUInt32 returned failure`) and grep finds nothing in it
  â€” not our strings, not our GUIDs, not even built-in menu names. Only its
  SIZE carries any signal.
- `Error loading UI library ... HrLoadNativeUILibrary failed with 0x800a006f`
  is noise. XamlLanguagePackage, TypeScriptPackage and friends log it too,
  with working menus.
- The `language="en-GB"` on a decompiled `.cto` is the decompiler stamping the
  machine's culture into its own output. It survives `-Len-US` on both compile
  and decompile and says nothing about the stored table.

### Two traps that cost real time

`devenv /log` takes an OPTIONAL FILENAME. `devenv /rootSuffix Exp /log
<path>` does not open `<path>`, it OVERWRITES it with the activity log. Put
`/log` last, with nothing after it.

`CreatePkgDef.exe` still cannot run here (`ReflectionTypeLoadException` on
`IAsyncServiceProvider3`), so the pkgdef stays hand-written â€” including the
`[$RootKey$\BindingPaths\{pkg guid}]` block that `[<ProvideBindingPath>]`
would have generated.

F#, unrelated but adjacent: `base.InitializeAsync(...)` cannot be called from
inside `task { }` (FS0491 â€” the CE body is a closure). Start it outside the
builder and `do!` the resulting task.
## Status

**Working end to end, verified live in VS 2026** (squiggles, light bulb,
fixes applied). The marketplace listing text lives in
`MarketplaceOverview.md`; `publishManifest.json` + the CI `vsix` job
handle publishing on version tags (needs the `VS_MARKETPLACE_PAT`
secret).

Installing into the experimental instance with
`VSIXInstaller /quiet /rootSuffix:Exp artifacts\FSharp.Refactor.vsix`
copies the files but stamps the REAL instance's
`Extensions\extensions.configurationchanged`, so the Exp instance never
rescans and composes nothing (an empty-handed start, no log at all).
Create that marker file under
`%LOCALAPPDATA%\Microsoft\VisualStudio\18.0_*Exp\Extensions\` before
launching `devenv /rootSuffix Exp <file.fs>`; the log then shows
`fsac: bundled`, `fsac started for <solution dir>` and `diagnostics for`
within seconds.

Fast dev loop, no reinstall: build, then copy
`bin\Release\net48\FSharp.Refactor.Vsix.dll` over the installed copy
under `%LOCALAPPDATA%\Microsoft\VisualStudio\18.0_*Exp\Extensions\<random>\`
and delete that instance's `ComponentModelCache` (required when MEF
exports changed). Everything traces to `%TEMP%\FSharpRefactor.Vsix.log`.

How the V1 shortcuts were closed:

- Code actions are fetched from the sidecar in `HasSuggestedActionsAsync`
  (off the UI thread) and cached per snapshot version and span;
  `GetSuggestedActions` answers from the cache and only waits on the
  sidecar (5s cap) when the two calls disagree.
- The sidecar roots at the TOPMOST solution above the first opened file,
  so FSAC sees every project; failing a solution, the nearest project.
- Every fix has a preview pane: what it removes and what it inserts.
- FsAutoComplete is bundled (`CreateVsix.ps1` copies the newest payload
  from the global tool store, or installs one into `obj\fsac-tool`;
  `-NoFsac` skips it) and preferred over the global tool.
- Settings without an options page: `%APPDATA%\FSharp.Refactor\vsix.json`
  with `fsac` (a `.dll` runs under `dotnet`, anything else as it is),
  `analyzers` (a list of directories) and `root`; the environment
  variables `FSHARP_REFACTOR_FSAC`, `FSHARP_REFACTOR_ANALYZERS` (`;`
  separated) and `FSHARP_REFACTOR_ROOT` win over the file. Read once per
  Visual Studio session.

Still open: a Tools > Options page needs a VSPackage registration
(pkgdef) this hand-rolled packaging does not produce.
