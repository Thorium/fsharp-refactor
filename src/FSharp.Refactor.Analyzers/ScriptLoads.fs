/// Refactoring (FR0143, fix): a script whose `#load` chain misses a file
/// of the project it loads from gets that file loaded, in the project's
/// own order.
///
///     #load "../src/Lib/Helpers.fs"              #load "../src/Lib/Helpers.fs"
///     #load "../src/Lib/Braiding.fs"      →      #load "../src/Lib/FMatrix.fs"
///                                                #load "../src/Lib/Braiding.fs"
///
/// The compiler already names what is missing — `FS0039: The value,
/// namespace, type or module 'FMatrix' is not defined` in Braiding.fs —
/// and the `#load` paths say which project directory the files come from.
/// That project's fsproj lists its compile items in order; the one that
/// defines the missing name and is not loaded is the fix, inserted before
/// the first loaded file that follows it in the project. A script written
/// before a file was added to the project is exactly this shape
/// (FSharp.Azure.Quantum's TopologicalMeasurementTest.fsx).
///
/// A missing NAMESPACE (`open Lib.Core` → `The namespace 'Core' is not
/// defined`) is looked for in the loaded project's ProjectReferences: the
/// referenced project that declares it is what the script needs a `#r` to,
/// and its newest built assembly under `bin` is referenced the way sibling
/// scripts do. Not built yet: the finding says so and offers nothing.
///
/// This rule runs on a script that does NOT typecheck — that is its
/// point — so the apply tool admits it where the typed rules stay silent.
///
/// Safety rules:
///   - `.fsx` files only, with at least one `#load`
///   - the missing name must resolve to exactly one unloaded compile item
///     of a project the script already loads from, by file name or by a
///     `module`/`namespace`/`type` declaration in its first lines
///   - wildcard compile items are not read; a project directory holding
///     several fsproj files is not read either
module FSharp.Refactor.ScriptLoads

open System
open System.IO
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open System.Text.RegularExpressions

/// The name FS0039 complains about: "'X' is not defined".
let private notDefined = Regex("'([^']+)' is not defined", RegexOptions.Compiled)

type Suggestion =
    {
        /// Zero-width, at the start of the line the directive goes before.
        InsertRange: range
        /// The directive line to insert, or None when the finding is advice.
        InsertText: string option
        Message: string
    }

let private normalize (path: string) =
    try
        Path.GetFullPath(path).Replace('/', '\\').ToLowerInvariant()
    with _ -> // an unreadable path matches nothing; fsharpanalyzer: ignore-line FR0055
        path.ToLowerInvariant()

/// A string argument of a hash directive at a script's top level.
type Directive =
    {
        /// `load`, `r`, `I`, ...
        Ident: string
        /// The argument's value, unquoted.
        Value: string
        /// The whole directive line's range.
        Range: range
        /// The argument's own range, quotes included.
        ArgumentRange: range
    }

/// The string-argument hash directives of a script, in source order.
let directives (tree: ParsedInput) : Directive list =
    match tree with
    | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
        [ for SynModuleOrNamespace(decls = decls) in modules do
              for decl in decls do
                  match decl with
                  | SynModuleDecl.HashDirective(ParsedHashDirective(ident, args, range), _) ->
                      for arg in args do
                          match arg with
                          | ParsedHashDirectiveArgument.String(value = v; range = argRange) ->
                              yield
                                  { Ident = ident
                                    Value = v
                                    Range = range
                                    ArgumentRange = argRange }
                          | _ -> ()
                  | _ -> () ]
    | _ -> []

/// The single fsproj of a directory, when there is exactly one.
let private projectIn (dir: string) =
    try
        match Directory.GetFiles(dir, "*.fsproj") with
        | [| one |] -> Some one
        | _ -> None
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

let private attributeValues (text: string) (element: string) (attribute: string) =
    Regex.Matches(text, $"<{element}\\s+[^>]*?{attribute}=\"([^\"]+)\"")
    |> Seq.map (fun m -> m.Groups.[1].Value)
    |> List.ofSeq

/// The project's compile items in order, resolved; wildcards are skipped.
let private compileItems (fsproj: string) =
    try
        let dir = Path.GetDirectoryName fsproj

        attributeValues (File.ReadAllText fsproj) "Compile" "Include"
        |> List.filter (fun f -> not (f.Contains '*'))
        |> List.map (fun f -> Path.GetFullPath(Path.Combine(dir, f.Replace('\\', '/'))))
    with _ -> // fsharpanalyzer: ignore-line FR0055
        []

let private projectReferences (fsproj: string) =
    try
        let dir = Path.GetDirectoryName fsproj

        attributeValues (File.ReadAllText fsproj) "ProjectReference" "Include"
        |> List.map (fun f -> Path.GetFullPath(Path.Combine(dir, f.Replace('\\', '/'))))
        |> List.filter File.Exists
    with _ -> // fsharpanalyzer: ignore-line FR0055
        []

let private assemblyName (fsproj: string) =
    try
        let m = Regex.Match(File.ReadAllText fsproj, "<AssemblyName>([^<]+)</AssemblyName>")

        if m.Success then
            m.Groups.[1].Value.Trim()
        else
            Path.GetFileNameWithoutExtension fsproj
    with _ -> // fsharpanalyzer: ignore-line FR0055
        Path.GetFileNameWithoutExtension fsproj

/// Does this source file declare the name — as a module, a namespace
/// segment, or a type — in its first lines? Its file name counts too.
let private declares (name: string) (file: string) =
    String.Equals(Path.GetFileNameWithoutExtension file, name, StringComparison.Ordinal)
    || (try
            let pattern =
                $"^\\s*(module|namespace|type)\\s+(rec\\s+|internal\\s+|private\\s+|public\\s+)*([\\w.]+\\.)?{Regex.Escape name}\\b"

            File.ReadLines file
            |> Seq.truncate 80
            |> Seq.exists (fun line -> Regex.IsMatch(line, pattern))
        with _ -> // fsharpanalyzer: ignore-line FR0055
            false)

/// The newest built assembly of a project, under its bin directory.
let private builtAssembly (fsproj: string) =
    try
        let bin = Path.Combine(Path.GetDirectoryName fsproj, "bin")

        if Directory.Exists bin then
            Directory.GetFiles(bin, assemblyName fsproj + ".dll", SearchOption.AllDirectories)
            // a reference assembly (bin\...\ref\X.dll) has no IL: a #r to it
            // typechecks, so the fix would be kept, and the script would
            // fail the moment fsi ran it
            |> Array.filter (fun path ->
                let segments =
                    path.Replace('/', '\\').Split('\\') |> Array.map (fun s -> s.ToLowerInvariant())

                not (Array.contains "ref" segments || Array.contains "refint" segments))
            |> Array.sortByDescending File.GetLastWriteTimeUtc
            |> Array.tryHead
        else
            None
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

let private relativeTo (scriptDir: string) (file: string) =
    Path.GetRelativePath(scriptDir, file).Replace('\\', '/')

/// The names FS0039 reports as not defined, with the file each came from.
let private missingNames (diagnostics: FSharpDiagnostic[]) =
    [ for d in diagnostics do
          if d.ErrorNumber = 39 then
              let m = notDefined.Match d.Message

              // a module, namespace or type is what a #load can supply; a
              // value (`'x'`, `'fsi'`) is not, and a file that happens to
              // carry its name would be loaded — and RUN — for nothing
              if m.Success && Char.IsUpper m.Groups.[1].Value.[0] then
                  yield m.Groups.[1].Value, normalize d.FileName ]
    |> List.distinct

let find (script: string) (tree: ParsedInput) (diagnostics: FSharpDiagnostic[]) : Suggestion list =
    if not (script.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)) then
        []
    else
        let scriptDir = Path.GetDirectoryName(Path.GetFullPath script)
        let all = directives tree

        let loads =
            [ for d in all do
                  if d.Ident = "load" then
                      yield Path.GetFullPath(Path.Combine(scriptDir, d.Value.Replace('\\', '/'))), d.Range ]

        let references =
            [ for d in all do
                  if d.Ident = "r" then
                      yield Path.GetFileName(d.Value.Replace('\\', '/')).ToLowerInvariant() ]

        // a script whose OWN #load or #r names a file that is not there is
        // stale or unbuilt, and every "not defined" it reports stems from
        // that: fantomas's docs scripts `#r` an artifacts dll that was never
        // built, and fsharp.formatting's Script.fsx loads a Library1.fs that
        // no longer exists — the FS0039s are not a missing #load
        //
        // A `#r` by NAME — no path separator, no source extension:
        // `#r "System.Xml.Linq"`, FAKE 4's `#I "packages/FAKE/tools"` and
        // `#r "FakeLib.dll"` — is looked for beside the script and in every
        // `#I` directory, and when it is in neither it is still not broken:
        // the compiler resolves such a reference from its reference set,
        // and whether the script typechecks against it is a matter for
        // the script. Only a `#load`, or a `#r` with a PATH that leads
        // nowhere, is broken.
        let existsIn (dir: string) (value: string) =
            try
                File.Exists(Path.GetFullPath(Path.Combine(dir, value)))
            with _ -> // an unopenable value is no evidence either way; fsharpanalyzer: ignore-line FR0055
                false

        let includeDirs =
            [ for d in all do
                  if d.Ident = "I" then
                      yield Path.Combine(scriptDir, d.Value.Replace('\\', '/')) ]

        let brokenDirective =
            all
            |> List.exists (fun d ->
                let value = d.Value.Replace('\\', '/')
                // `nuget: X`, `paket: X`: a package, not a path
                let prefixed = d.Value.Contains ':' && not (Path.IsPathRooted d.Value)

                let byName =
                    not (value.Contains '/')
                    && not (value.EndsWith(".fs", StringComparison.OrdinalIgnoreCase))
                    && not (value.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase))

                match d.Ident with
                | "load" -> not prefixed && not (existsIn scriptDir value)
                | "r" ->
                    not prefixed
                    && not (existsIn scriptDir value)
                    && not (includeDirs |> List.exists (fun dir -> existsIn dir value))
                    && not byName
                | _ -> false)

        if loads.IsEmpty || brokenDirective then
            []
        else
            let loadedSet = loads |> List.map (fst >> normalize) |> Set.ofList
            let scriptKey = normalize script

            // the projects the script loads from, each with its compile order
            let projects =
                loads
                |> List.map (fun (file, _) -> Path.GetDirectoryName file)
                |> List.distinct
                |> List.choose projectIn
                |> List.map (fun fsproj -> fsproj, compileItems fsproj)

            let lineStart (r: range) =
                Range.mkRange r.FileName (Position.mkPos r.StartLine 0) (Position.mkPos r.StartLine 0)

            let afterLine (r: range) =
                Range.mkRange r.FileName (Position.mkPos (r.EndLine + 1) 0) (Position.mkPos (r.EndLine + 1) 0)

            let firstLoad = loads |> List.minBy (fun (_, r) -> r.StartLine)
            let lastLoad = loads |> List.maxBy (fun (_, r) -> r.EndLine)

            [ for name, inFile in missingNames diagnostics do
                  if loadedSet.Contains inFile || inFile = scriptKey then
                      // a compile item of a loaded project that declares the
                      // name and is not loaded
                      let candidate =
                          projects
                          |> List.tryPick (fun (fsproj, items) ->
                              items
                              |> List.tryFind (fun item ->
                                  // a signature file cannot be loaded on its own
                                  // (FS0240: no corresponding implementation);
                                  // fantomas's docs got `#load "EditorConfig.fsi"`
                                  not (item.EndsWith(".fsi", StringComparison.OrdinalIgnoreCase))
                                  && not (loadedSet.Contains(normalize item))
                                  && declares name item)
                              |> Option.map (fun item -> fsproj, items, item))

                      match candidate with
                      | Some(_, items, item) ->
                          let index = items |> List.findIndex (fun i -> normalize i = normalize item)

                          // before the first loaded file that follows it in
                          // the project; after the last load otherwise
                          let dependent =
                              loads
                              |> List.sortBy (fun (_, r) -> r.StartLine)
                              |> List.tryFind (fun (file, _) ->
                                  match items |> List.tryFindIndex (fun i -> normalize i = normalize file) with
                                  | Some i -> i > index
                                  | None -> false)

                          let at, insertText =
                              match dependent with
                              | Some(_, r) -> lineStart r, $"#load \"{relativeTo scriptDir item}\"\n"
                              | None -> afterLine (snd lastLoad), $"#load \"{relativeTo scriptDir item}\"\n"

                          let needing =
                              if inFile = scriptKey then
                                  Path.GetFileName script
                              else
                                  Path.GetFileName(fst (loads |> List.find (fun (f, _) -> normalize f = inFile)))

                          yield
                              { InsertRange = at
                                InsertText = Some insertText
                                Message =
                                  $"'{name}' is not defined in {needing}: the project defines it in {Path.GetFileName item}, which this script does not #load. The fix loads it in the project's order." }
                      | None ->
                          // a namespace of a referenced project: `#r` its assembly
                          let referenced =
                              projects
                              |> List.collect (fun (fsproj, _) -> projectReferences fsproj)
                              |> List.distinct
                              |> List.tryFind (fun refProj -> compileItems refProj |> List.exists (declares name))

                          match referenced with
                          | Some refProj ->
                              let dll = assemblyName refProj + ".dll"

                              if not (references |> List.contains (dll.ToLowerInvariant())) then
                                  match builtAssembly refProj with
                                  | Some built ->
                                      yield
                                          { InsertRange = lineStart (snd firstLoad)
                                            InsertText = Some $"#r \"{relativeTo scriptDir built}\"\n"
                                            Message =
                                              $"'{name}' is not defined: it lives in {Path.GetFileName refProj}, a ProjectReference of the loaded project. The fix references its built assembly." }
                                  | None ->
                                      yield
                                          { InsertRange = lineStart (snd firstLoad)
                                            InsertText = None
                                            Message =
                                              $"'{name}' is not defined: it lives in {Path.GetFileName refProj}, a ProjectReference of the loaded project, which has no built assembly under its bin directory yet — build it, then #r the dll here." }
                          | None -> () ]
            |> List.distinctBy (fun s -> s.InsertText, s.InsertRange.StartLine)
