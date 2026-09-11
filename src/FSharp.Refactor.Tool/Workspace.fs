/// The projects around a project: what a solution lists, what a project
/// references, and so which projects of a run can SEE a given project's
/// declarations.
///
/// The api-changing pass (FR0090/FR0091) reshapes a definition together
/// with every call site, and a call site in a sibling project of the same
/// solution — the test project, typically — is one the project's own
/// compilation never shows. Finding those siblings is a question about
/// project files, not compilations, so it is answered here from the
/// files alone: no MSBuild, nothing built, nothing read but XML and the
/// solution's project list. Everything is read-only discovery; whether a
/// sibling is then typechecked and rewritten is the pass's decision.
module FSharp.Refactor.Tool.Workspace

open System
open System.IO
open System.Text.RegularExpressions

/// Every project type a solution can list, C# and VB included: a C#
/// project referencing an F# one is a caller the pass cannot read, and
/// it must be SEEN to be declined.
let private projectExtensions = [ ".fsproj"; ".csproj"; ".vbproj" ]

let private isProjectFile (path: string) =
    projectExtensions
    |> List.exists (fun ext -> path.EndsWith(ext, StringComparison.OrdinalIgnoreCase))

/// Is this an F# project — the only kind whose compilation the pass can
/// typecheck and whose call sites it can rewrite?
let isFSharpProject (path: string) =
    path.EndsWith(".fsproj", StringComparison.OrdinalIgnoreCase)

let private samePath (a: string) (b: string) =
    String.Equals(Path.GetFullPath a, Path.GetFullPath b, StringComparison.OrdinalIgnoreCase)

/// The project paths a solution lists — every language — resolved against
/// the solution's own directory and filtered to files that exist. `.slnx`
/// is XML with one `Path="..."` per project; the classic `.sln` has one
/// `Project(...) = "Name", "path", "{guid}"` line per entry, and solution
/// folders in the same shape without an extension, which the extension
/// filter drops.
let projectsInSolution (solutionPath: string) : string list =
    let dir = Path.GetDirectoryName(Path.GetFullPath solutionPath)

    let text =
        try
            File.ReadAllText solutionPath
        with
        | :? IOException
        | :? UnauthorizedAccessException -> ""

    let paths =
        if solutionPath.EndsWith(".slnx", StringComparison.OrdinalIgnoreCase) then
            Regex.Matches(text, "Path\\s*=\\s*\"([^\"]+)\"")
            |> Seq.map (fun m -> m.Groups.[1].Value)
        else
            Regex.Matches(text, "\"([^\"]+\\.(?:fs|cs|vb)proj)\"")
            |> Seq.map (fun m -> m.Groups.[1].Value)

    paths
    |> Seq.filter isProjectFile
    |> Seq.map (fun p -> Path.GetFullPath(Path.Combine(dir, p.Replace('\\', Path.DirectorySeparatorChar))))
    |> Seq.filter File.Exists
    |> Seq.distinctBy (fun p -> p.ToLowerInvariant())
    |> List.ofSeq

/// How a `<ProjectReference Include="...">` names its target. An Include
/// can carry several paths separated by semicolons, and the two MSBuild
/// properties that mean "this directory" resolve; a path built from any
/// other property cannot be resolved without MSBuild - but it still names
/// a project, and a referencer passed over is a call site missed. So such
/// a reference keeps the file name it ends in (`$(FSharpSourcesRoot)\
/// FSharp.Core\FSharp.Core.fsproj`, twenty-eight times in dotnet/fsharp)
/// and matches by that, and one with no recognisable file name at all
/// (`$(Ref)`) is taken to reference ANY project of the workspace: the
/// cost of reading a sibling that turns out not to call is a typecheck,
/// the cost of missing one is a broken build.
type ProjectReference =
    /// A path on disk.
    | Resolved of string
    /// Only the project file's own name is known.
    | ByName of string
    /// Nothing recognisable: may be any project.
    | Unresolvable

/// Every reference of a project file, in the shapes above.
let projectReferenceShapesOf (projectPath: string) : ProjectReference list =
    let text =
        try
            File.ReadAllText projectPath
        with
        | :? IOException
        | :? UnauthorizedAccessException -> ""

    let dir = Path.GetDirectoryName(Path.GetFullPath projectPath)

    Regex.Matches(text, "<ProjectReference\\s[^>]*?Include\\s*=\\s*\"([^\"]+)\"", RegexOptions.IgnoreCase)
    |> Seq.collect (fun m -> m.Groups.[1].Value.Split(';', StringSplitOptions.RemoveEmptyEntries))
    |> Seq.map (fun reference ->
        reference
            .Trim()
            .Replace("$(MSBuildThisFileDirectory)", dir + string Path.DirectorySeparatorChar)
            .Replace("$(MSBuildProjectDirectory)", dir))
    |> Seq.map (fun reference ->
        if reference.Contains "$(" then
            let name = reference.Substring(reference.LastIndexOfAny [| '\\'; '/' |] + 1)

            if isProjectFile name && not (name.Contains "$(") then
                ByName name
            else
                Unresolvable
        else
            try
                Resolved(Path.GetFullPath(Path.Combine(dir, reference.Replace('\\', Path.DirectorySeparatorChar))))
            with
            | :? ArgumentException
            | :? PathTooLongException
            | :? NotSupportedException -> Unresolvable)
    |> Seq.distinct
    |> List.ofSeq

/// The references that resolve to a path on disk.
let projectReferencesOf (projectPath: string) : string list =
    projectReferenceShapesOf projectPath
    |> List.choose (function
        | Resolved p -> Some p
        | _ -> None)
    |> List.distinctBy (fun p -> p.ToLowerInvariant())

/// Does a reference name this project?
let private namesProject (reference: ProjectReference) (project: string) =
    match reference with
    | Resolved p -> samePath p project
    | ByName name -> String.Equals(name, Path.GetFileName project, StringComparison.OrdinalIgnoreCase)
    | Unresolvable -> true

/// The source files of `project` that another project of the workspace
/// compiles DIRECTLY, through a `<Compile Include="..\Common\X.fs">` link
/// (SQLProvider's provider projects each compile the Common sources):
/// (linking project, the shared files). Such a project is not a
/// referencer - it holds its own copy of every declaration in the file,
/// and its own call sites of them, which a pass over `project` cannot
/// see. An Include with a wildcard or a property cannot be resolved and
/// is passed over.
let sharedSourcesOf (workspace: string list) (project: string) (sources: string seq) : (string * string list) list =
    let own =
        sources
        |> Seq.map (fun s -> (Path.GetFullPath s).ToLowerInvariant())
        |> Set.ofSeq

    let compileItems (projectPath: string) =
        let text =
            try
                File.ReadAllText projectPath
            with
            | :? IOException
            | :? UnauthorizedAccessException -> ""

        let dir = Path.GetDirectoryName(Path.GetFullPath projectPath)

        Regex.Matches(text, "<Compile\\s[^>]*?Include\\s*=\\s*\"([^\"]+)\"", RegexOptions.IgnoreCase)
        |> Seq.collect (fun m -> m.Groups.[1].Value.Split(';', StringSplitOptions.RemoveEmptyEntries))
        |> Seq.map (fun item -> item.Trim())
        |> Seq.filter (fun item -> not (item.Contains "$(" || item.Contains "*"))
        |> Seq.choose (fun item ->
            try
                Some(Path.GetFullPath(Path.Combine(dir, item.Replace('\\', Path.DirectorySeparatorChar))))
            with
            | :? ArgumentException
            | :? PathTooLongException
            | :? NotSupportedException -> None)
        |> List.ofSeq

    workspace
    |> List.filter (fun p -> not (samePath p project))
    |> List.choose (fun p ->
        match
            compileItems p
            |> List.filter (fun item -> own.Contains(item.ToLowerInvariant()))
        with
        | [] -> None
        | shared -> Some(p, shared))

/// The name of the assembly a project builds: its `<AssemblyName>` when
/// the project spells one out, else the project file's own name — the
/// SDK default. This is the name an InternalsVisibleTo attribute carries.
let assemblyNameOf (projectPath: string) : string =
    let text =
        try
            File.ReadAllText projectPath
        with
        | :? IOException
        | :? UnauthorizedAccessException -> ""

    let m = Regex.Match(text, "<AssemblyName>\\s*([^<]+?)\\s*</AssemblyName>")

    if m.Success && not (m.Groups.[1].Value.Contains "$(") then
        m.Groups.[1].Value
    else
        Path.GetFileNameWithoutExtension projectPath

/// The solutions in `dir` that list `project`, nearest first as the caller
/// walks up.
let private solutionsListing (project: string) (dir: string) =
    try
        [ yield! Directory.EnumerateFiles(dir, "*.slnx")
          yield! Directory.EnumerateFiles(dir, "*.sln") ]
        |> List.filter (fun sln -> projectsInSolution sln |> List.exists (samePath project))
    with
    | :? IOException
    | :? UnauthorizedAccessException -> []

/// The projects that share a workspace with `project`, the project itself
/// included, or None when there is no workspace to enumerate.
///
/// A solution is the workspace when the run was pointed at one, and
/// otherwise the nearest ancestor directory holding a solution that lists
/// the project — the union of every such solution there, as the run
/// itself takes the union of a directory's solutions. The search stops at
/// the repository root (`.git`), since a solution above that belongs to
/// someone else. A run pointed at a directory with no solution took every
/// project beneath it, so that directory is the workspace then. A bare
/// project with no solution above it and no directory run around it has
/// no workspace: nothing can be said about who references it, and the
/// caller keeps public declarations as they are.
let workspaceOf (runTarget: string) (project: string) : string list option =
    let target =
        try
            Some(Path.GetFullPath runTarget)
        with
        | :? ArgumentException
        | :? PathTooLongException
        | :? NotSupportedException -> None

    let solutionRun =
        target
        |> Option.filter (fun t ->
            File.Exists t
            && (t.EndsWith(".sln", StringComparison.OrdinalIgnoreCase)
                || t.EndsWith(".slnx", StringComparison.OrdinalIgnoreCase)))
        |> Option.map (fun t -> projectsInSolution t)
        |> Option.filter (List.exists (samePath project))

    match solutionRun with
    | Some projects -> Some projects
    | None ->
        let mutable dir = Path.GetDirectoryName(Path.GetFullPath project)
        let mutable found = None
        let mutable atEdge = false

        while found.IsNone && not atEdge && not (String.IsNullOrEmpty dir) do
            match solutionsListing project dir with
            | [] -> ()
            | solutions ->
                found <-
                    solutions
                    |> List.collect projectsInSolution
                    |> List.distinctBy (fun p -> p.ToLowerInvariant())
                    |> Some

            let parent = Path.GetDirectoryName dir

            atEdge <-
                Directory.Exists(Path.Combine(dir, ".git"))
                || String.IsNullOrEmpty parent
                || parent = Path.GetPathRoot dir

            dir <- parent

        match found with
        | Some projects -> Some projects
        | None ->
            let under (root: string) (path: string) =
                let root = root.TrimEnd(Path.DirectorySeparatorChar, Path.AltDirectorySeparatorChar)

                (Path.GetFullPath path)
                    .StartsWith(root + string Path.DirectorySeparatorChar, StringComparison.OrdinalIgnoreCase)

            match target with
            | Some t when Directory.Exists t && under t project ->
                projectExtensions
                |> List.collect (fun ext -> FileWalk.files ("*" + ext) t |> List.ofSeq)
                |> List.map Path.GetFullPath
                |> List.distinctBy (fun p -> p.ToLowerInvariant())
                |> Some
            | _ -> None

/// The projects of `workspace` that can see `project`'s declarations:
/// those referencing it directly, and those referencing one of THOSE —
/// an SDK project reference is transitive, so a project two hops away
/// compiles against the assembly as well. Order is stable for output.
let referencersOf (workspace: string list) (project: string) : string list =
    let references = workspace |> List.map (fun p -> p, projectReferenceShapesOf p)

    let mutable reached = [ project ]
    let mutable frontier = [ project ]

    while not frontier.IsEmpty do
        let next =
            references
            |> List.filter (fun (p, refs) ->
                not (reached |> List.exists (samePath p))
                && refs |> List.exists (fun r -> frontier |> List.exists (namesProject r)))
            |> List.map fst

        reached <- reached @ next
        frontier <- next

    reached |> List.filter (fun p -> not (samePath p project))
