/// The read-only discovery behind the api pass's sibling projects: what a
/// solution lists, what a project references, and which projects can see
/// a given one — from files alone, no MSBuild.
module FSharp.Refactor.Tests.WorkspaceTests

open System
open System.IO
open FSharp.Refactor.Tool
open Xunit

/// A throwaway directory tree: (relative path, content) pairs written under
/// a fresh root, handed to `body` with the root.
let private withTree (files: (string * string) list) (body: string -> unit) =
    let root =
        Path.Combine(Path.GetTempPath(), "fsref-workspace-" + Guid.NewGuid().ToString "N")

    try
        for relative, content in files do
            let path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))
            Directory.CreateDirectory(Path.GetDirectoryName path) |> ignore
            File.WriteAllText(path, content)

        body root
    finally
        try
            Directory.Delete(root, true)
        with _ ->
            ()

let private fsproj (references: string list) =
    let items =
        references
        |> List.map (fun r -> $"    <ProjectReference Include=\"{r}\" />")
        |> String.concat "\n"

    $"<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup><TargetFramework>net8.0</TargetFramework></PropertyGroup>\n  <ItemGroup>\n{items}\n  </ItemGroup>\n</Project>\n"

let private sln (projects: (string * string) list) =
    let lines =
        projects
        |> List.map (fun (name, path) ->
            $"Project(\"{{F2A71F9B-5D33-465A-A702-920D77279786}}\") = \"{name}\", \"{path}\", \"{{11111111-1111-1111-1111-111111111111}}\"\nEndProject")
        |> String.concat "\n"

    $"Microsoft Visual Studio Solution File, Format Version 12.00\n{lines}\nGlobal\nEndGlobal\n"

let private names (paths: string list) =
    paths |> List.map Path.GetFileName |> List.sort

[<Fact>]
let ``a classic solution lists its F#, C# and VB projects, solution folders left out`` () =
    withTree
        [ "All.sln",
          sln
              [ "Lib", "src\\Lib\\Lib.fsproj"
                "Consumer", "src\\Consumer\\Consumer.csproj"
                "Legacy", "src\\Legacy\\Legacy.vbproj"
                "Folder", "Folder" ]
          "src/Lib/Lib.fsproj", fsproj []
          "src/Consumer/Consumer.csproj", "<Project />"
          "src/Legacy/Legacy.vbproj", "<Project />" ]
        (fun root ->
            Assert.Equal<string list>(
                [ "Consumer.csproj"; "Legacy.vbproj"; "Lib.fsproj" ],
                names (Workspace.projectsInSolution (Path.Combine(root, "All.sln")))
            ))

[<Fact>]
let ``an slnx solution lists its projects by Path`` () =
    withTree
        [ "All.slnx",
          "<Solution>\n  <Project Path=\"src/Lib/Lib.fsproj\" />\n  <Project Path=\"tests/Tests/Tests.fsproj\" />\n  <Project Path=\"missing/Gone.fsproj\" />\n</Solution>\n"
          "src/Lib/Lib.fsproj", fsproj []
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Lib/Lib.fsproj" ] ]
        (fun root ->
            // a listed project that is not on disk is not a project
            Assert.Equal<string list>(
                [ "Lib.fsproj"; "Tests.fsproj" ],
                names (Workspace.projectsInSolution (Path.Combine(root, "All.slnx")))
            ))

[<Fact>]
let ``project references resolve against the project directory`` () =
    withTree
        [ "src/Lib/Lib.fsproj", fsproj []
          "src/Other/Other.fsproj", fsproj []
          "tests/Tests/Tests.fsproj",
          fsproj
              [ "..\\..\\src\\Lib\\Lib.fsproj"
                "$(MSBuildThisFileDirectory)../../src/Other/Other.fsproj;$(SomeProperty)/Unknown.fsproj" ] ]
        (fun root ->
            // semicolons separate; a path built from an unknown property
            // cannot be resolved without MSBuild and is passed over
            Assert.Equal<string list>(
                [ "Lib.fsproj"; "Other.fsproj" ],
                names (Workspace.projectReferencesOf (Path.Combine(root, "tests", "Tests", "Tests.fsproj")))
            ))

[<Fact>]
let ``the assembly name is the AssemblyName property or the project file's name`` () =
    withTree
        [ "src/Lib/Lib.fsproj", fsproj []
          "src/Named/Named.fsproj",
          "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <PropertyGroup>\n    <AssemblyName>Company.Named</AssemblyName>\n  </PropertyGroup>\n</Project>\n" ]
        (fun root ->
            Assert.Equal("Lib", Workspace.assemblyNameOf (Path.Combine(root, "src", "Lib", "Lib.fsproj")))

            Assert.Equal(
                "Company.Named",
                Workspace.assemblyNameOf (Path.Combine(root, "src", "Named", "Named.fsproj"))
            ))

[<Fact>]
let ``referencers include the projects two hops away and every language`` () =
    // Tests -> Lib directly; App -> Core -> Lib, so App compiles against
    // Lib too (SDK project references are transitive); Consumer.csproj
    // references Lib and must be seen even though it cannot be read;
    // Unrelated references nothing
    withTree
        [ "src/Lib/Lib.fsproj", fsproj []
          "src/Core/Core.fsproj", fsproj [ "../Lib/Lib.fsproj" ]
          "src/App/App.fsproj", fsproj [ "../Core/Core.fsproj" ]
          "src/Consumer/Consumer.csproj",
          "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <ItemGroup>\n    <ProjectReference Include=\"../Lib/Lib.fsproj\" />\n  </ItemGroup>\n</Project>\n"
          "src/Unrelated/Unrelated.fsproj", fsproj []
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Lib/Lib.fsproj" ] ]
        (fun root ->
            let workspace =
                [ "src/Lib/Lib.fsproj"
                  "src/Core/Core.fsproj"
                  "src/App/App.fsproj"
                  "src/Consumer/Consumer.csproj"
                  "src/Unrelated/Unrelated.fsproj"
                  "tests/Tests/Tests.fsproj" ]
                |> List.map (fun p -> Path.Combine(root, p.Replace('/', Path.DirectorySeparatorChar)))

            let lib = Path.Combine(root, "src", "Lib", "Lib.fsproj")

            Assert.Equal<string list>(
                [ "App.fsproj"; "Consumer.csproj"; "Core.fsproj"; "Tests.fsproj" ],
                names (Workspace.referencersOf workspace lib)
            )

            // Core's referencers: App only
            Assert.Equal<string list>(
                [ "App.fsproj" ],
                names (Workspace.referencersOf workspace (Path.Combine(root, "src", "Core", "Core.fsproj")))
            ))

[<Fact>]
let ``the workspace is the solution the run was pointed at`` () =
    withTree
        [ "All.sln", sln [ "Lib", "src\\Lib\\Lib.fsproj"; "Tests", "tests\\Tests\\Tests.fsproj" ]
          "src/Lib/Lib.fsproj", fsproj []
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Lib/Lib.fsproj" ] ]
        (fun root ->
            let lib = Path.Combine(root, "src", "Lib", "Lib.fsproj")

            match Workspace.workspaceOf (Path.Combine(root, "All.sln")) lib with
            | Some projects -> Assert.Equal<string list>([ "Lib.fsproj"; "Tests.fsproj" ], names projects)
            | None -> failwith "expected the solution's projects")

[<Fact>]
let ``a bare project finds the nearest ancestor solution that lists it`` () =
    // the run was pointed at Lib.fsproj alone; the solution two
    // directories up lists it, so its other projects are the siblings —
    // and a solution that does NOT list the project is not its workspace
    withTree
        [ "All.sln", sln [ "Lib", "src\\Lib\\Lib.fsproj"; "Tests", "tests\\Tests\\Tests.fsproj" ]
          "Other.sln", sln [ "Tests", "tests\\Tests\\Tests.fsproj" ]
          "src/Lib/Lib.fsproj", fsproj []
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Lib/Lib.fsproj" ] ]
        (fun root ->
            let lib = Path.Combine(root, "src", "Lib", "Lib.fsproj")

            match Workspace.workspaceOf lib lib with
            | Some projects -> Assert.Equal<string list>([ "Lib.fsproj"; "Tests.fsproj" ], names projects)
            | None -> failwith "expected the ancestor solution's projects")

[<Fact>]
let ``a directory run without a solution takes every project beneath it`` () =
    withTree
        [ "src/Lib/Lib.fsproj", fsproj []
          "src/Consumer/Consumer.csproj", "<Project />"
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Lib/Lib.fsproj" ] ]
        (fun root ->
            let lib = Path.Combine(root, "src", "Lib", "Lib.fsproj")

            match Workspace.workspaceOf root lib with
            | Some projects ->
                Assert.Equal<string list>([ "Consumer.csproj"; "Lib.fsproj"; "Tests.fsproj" ], names projects)
            | None -> failwith "expected every project under the directory")

[<Fact>]
let ``a bare project with no solution above it has no workspace`` () =
    // .git marks the repository root: the search stops there, and a
    // solution above the repository is someone else's
    withTree
        [ "Above.sln", sln [ "Lib", "repo\\src\\Lib\\Lib.fsproj" ]
          "repo/.git/HEAD", "ref: refs/heads/main\n"
          "repo/src/Lib/Lib.fsproj", fsproj [] ]
        (fun root ->
            let lib = Path.Combine(root, "repo", "src", "Lib", "Lib.fsproj")
            Assert.True((Workspace.workspaceOf lib lib).IsNone))

[<Fact>]
let ``a reference through an MSBuild property still names its project by file name`` () =
    // dotnet/fsharp: `$(FSharpSourcesRoot)\FSharp.Core\FSharp.Core.fsproj`,
    // twenty-eight times. Unresolvable as a path, but the file name says
    // which project it is, and a referencer passed over is a call site missed
    withTree
        [ "src/Lib/Lib.fsproj", fsproj []
          "src/Other/Other.fsproj", fsproj []
          "tests/Tests/Tests.fsproj", fsproj [ "$(SourcesRoot)\src\Lib\Lib.fsproj" ]
          "tests/Any/Any.fsproj", fsproj [ "$(Ref)" ] ]
        (fun root ->
            let p (relative: string) =
                Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))

            let workspace =
                [ p "src/Lib/Lib.fsproj"
                  p "src/Other/Other.fsproj"
                  p "tests/Tests/Tests.fsproj"
                  p "tests/Any/Any.fsproj" ]

            Assert.Equal<Workspace.ProjectReference list>(
                [ Workspace.ByName "Lib.fsproj" ],
                Workspace.projectReferenceShapesOf (p "tests/Tests/Tests.fsproj")
            )

            Assert.Equal<Workspace.ProjectReference list>(
                [ Workspace.Unresolvable ],
                Workspace.projectReferenceShapesOf (p "tests/Any/Any.fsproj")
            )

            // by name for Lib; a reference nothing can be read from may be
            // any project, so Any references both
            Assert.Equal<string list>(
                [ "Any.fsproj"; "Tests.fsproj" ],
                names (Workspace.referencersOf workspace (p "src/Lib/Lib.fsproj"))
            )

            Assert.Equal<string list>(
                [ "Any.fsproj" ],
                names (Workspace.referencersOf workspace (p "src/Other/Other.fsproj"))
            ))

[<Fact>]
let ``a project compiling another's source directly is reported with the shared files`` () =
    // SQLProvider's provider projects each compile the Common sources
    // through `<Compile Include="..\Common\X.fs">`; they reference nothing
    // and hold their own call sites
    withTree
        [ "src/Common/Common.fsproj",
          "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <ItemGroup>\n    <Compile Include=\"Shared.fs\" />\n    <Compile Include=\"Own.fs\" />\n  </ItemGroup>\n</Project>\n"
          "src/Common/Shared.fs", "module Shared"
          "src/Common/Own.fs", "module Own"
          "src/Provider/Provider.fsproj",
          "<Project Sdk=\"Microsoft.NET.Sdk\">\n  <ItemGroup>\n    <Compile Include=\"..\Common\Shared.fs\" />\n    <Compile Include=\"Provider.fs\" />\n    <Compile Include=\"$(Generated)\Gen.fs\" />\n    <Compile Include=\"**/*.fs\" />\n  </ItemGroup>\n</Project>\n"
          "src/Provider/Provider.fs", "module Provider"
          "tests/Tests/Tests.fsproj", fsproj [ "../../src/Common/Common.fsproj" ] ]
        (fun root ->
            let p (relative: string) =
                Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar))

            let common = p "src/Common/Common.fsproj"

            let workspace =
                [ common; p "src/Provider/Provider.fsproj"; p "tests/Tests/Tests.fsproj" ]

            match Workspace.sharedSourcesOf workspace common [ p "src/Common/Shared.fs"; p "src/Common/Own.fs" ] with
            | [ linking, [ shared ] ] ->
                Assert.Equal("Provider.fsproj", Path.GetFileName linking)
                Assert.Equal("Shared.fs", Path.GetFileName shared)
            | other -> failwithf "Expected Provider.fsproj sharing Shared.fs alone, got %A" other

            // a referencer is not a linker
            Assert.Empty(
                Workspace.sharedSourcesOf workspace (p "tests/Tests/Tests.fsproj") [ p "tests/Tests/Tests.fs" ]
            ))
