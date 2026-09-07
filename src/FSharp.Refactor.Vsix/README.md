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
