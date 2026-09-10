# FSharp.Refactor for Visual Studio

Functional refactoring hints with **one-click quick fixes** for F# — 137
rules covering correctness, performance, and idiomatic F#, running live in
the Visual Studio editor.

Squiggles mark each finding (recolorable under *Fonts and Colors →
FSharp.Refactor Hint*), and `Ctrl+.` applies the fix:

- `isNull x || x = ""` → `String.IsNullOrEmpty x`
- `match value with Some v -> v + 1 | None -> 0` → `Option.map ... |> Option.defaultValue`
- `Guid()` (the classic accidental-empty-guid slip) → `Guid.Empty` or `Guid.NewGuid()` — your call
- `d.ContainsKey k` + `d[k]` double lookup → one `TryGetValue`
- `sprintf "%s %d" a b` → interpolated string, format-preserving
- `path.ToLower().StartsWith "file:"` → `path.StartsWith("file:", StringComparison.OrdinalIgnoreCase)`
- a fixed lookup list probed in a loop → converted to a `Set`
- blocking `.Result` inside `task { }` → `let!`
- …and 130 more, every fix engineered to preserve behavior — the full
  rule list is in [Rules.md](https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md).

The same rules run in VS Code (Ionide) via the
[FSharp.Refactor.Analyzers](https://www.nuget.org/packages/FSharp.Refactor.Analyzers)
NuGet package, and in bulk from the command line with the
[fsharp-refactor](https://www.nuget.org/packages/fsharp-refactor) dotnet
tool, which applies fixes across a whole solution with type-checked
verification of every change.

## Requirements

The extension analyzes through an [FsAutoComplete](https://github.com/ionide/FsAutoComplete)
sidecar process. Install it once:

```
dotnet tool install -g fsautocomplete
```

Open an F# project, give the first analysis a few seconds, and the
squiggles appear. Diagnostics use `FR`-prefixed codes; compiler errors and
warnings stay with Visual Studio's own F# tooling — this extension only
adds the refactoring layer.

## Troubleshooting

The extension logs to `%TEMP%\FSharpRefactor.Vsix.log`: sidecar startup,
analyzer loading, diagnostics arriving, and every applied fix. If nothing
shows, that file says why.
