/// The Tools > FSharp.Refactor menu: the commands the VS Code extension
/// puts in its palette, which Visual Studio had none of.
///
/// Everything else in this extension is MEF — taggers, light bulbs, the
/// FsAutoComplete sidecar — and needs no shell package at all. A menu
/// does: Visual Studio learns about commands from a compiled command table
/// (FSharpRefactor.vsct -> .cto) that a registered package owns, so this
/// file is the one piece of shell plumbing here.
///
/// These commands drive the `fsharp-refactor` global tool, which the rest
/// of the extension never touches — the analyzers run in-process through
/// FSAC, the tool is a separate program that rewrites files. Its output
/// goes to an Output pane rather than a terminal: Visual Studio has no
/// integrated terminal, and a pane is the better home anyway — it
/// persists, it is searchable, and it does not take the keyboard.
namespace FSharp.Refactor.Vsix

open System
open System.ComponentModel.Design
open System.Diagnostics
open System.IO
open System.Runtime.InteropServices
open System.Threading
open System.Threading.Tasks
open Microsoft.VisualStudio.Shell
open Microsoft.VisualStudio.Shell.Interop

module internal Commands =

    [<Literal>]
    let PackageGuidString = "bb3ca01c-1bbf-44bb-8417-fed850034c4a"

    [<Literal>]
    let CommandSetGuidString = "295a52d6-afe3-414f-ad26-14b36f327d99"

    /// Must match the IDSymbol values in FSharpRefactor.vsct.
    module Ids =
        [<Literal>]
        let Run = 0x0100
        [<Literal>]
        let RunApiChanges = 0x0101
        [<Literal>]
        let Report = 0x0102
        [<Literal>]
        let CreateConfig = 0x0103
        [<Literal>]
        let ReviewNotes = 0x0104
        [<Literal>]
        let Status = 0x0105
        [<Literal>]
        let About = 0x0106

    [<Literal>]
    let RepositoryUrl = "https://github.com/Thorium/fsharp-refactor"

    [<Literal>]
    let Tool = "fsharp-refactor"

    /// One pane for the life of the session, named so it is findable in the
    /// Output window's drop-down.
    let private paneGuid = Guid "3f2a9c14-6b7d-4e58-9a30-2c5d81f4b7a2"

    let mutable private pane: IVsOutputWindowPane = null

    let private ensurePane (provider: IAsyncServiceProvider) =
        async {
            if isNull pane then
                do! Async.SwitchToContext(Threading.SynchronizationContext.Current)

                match! provider.GetServiceAsync(typeof<SVsOutputWindow>) |> Async.AwaitTask with
                | :? IVsOutputWindow as window ->
                    let mutable id = paneGuid
                    // visible = 1, clearWithSolution = 0: the findings outlive
                    // closing a solution, which is when you want to read them
                    window.CreatePane(&id, "FSharp.Refactor", 1, 0) |> ignore
                    let mutable found = Unchecked.defaultof<IVsOutputWindowPane>

                    if window.GetPane(&id, &found) = 0 then
                        pane <- found
                | _ -> ()

            return pane
        }

    /// OutputStringThreadSafe is the one write that does not require the UI
    /// thread, which is the whole point: the tool's stdout arrives on a
    /// reader thread and a solution-wide run produces thousands of lines.
    let private write (text: string) =
        if not (isNull pane) then
            pane.OutputStringThreadSafe text |> ignore

    let private writeLine (text: string) = write (text + Environment.NewLine)

    let private showPane () =
        ThreadHelper.ThrowIfNotOnUIThread()

        if not (isNull pane) then
            pane.Activate() |> ignore

    /// The solution's own directory and file, which is what every run needs as
    /// its target. No solution open is not an error worth a dialog stack —
    /// it is simply nothing to run on.
    let private solutionFile (provider: IAsyncServiceProvider) =
        async {
            match! provider.GetServiceAsync(typeof<SVsSolution>) |> Async.AwaitTask with
            | :? IVsSolution as solution ->
                let mutable dir = ""
                let mutable file = ""
                let mutable opts = ""

                if
                    solution.GetSolutionInfo(&dir, &file, &opts) = 0
                    && not (String.IsNullOrEmpty file)
                then
                    return Some(dir, file)
                else
                    return None
            | _ -> return None
        }

    let private box' (title: string) (text: string) =
        ThreadHelper.ThrowIfNotOnUIThread()

        VsShellUtilities.ShowMessageBox(
            ServiceProvider.GlobalProvider,
            text,
            title,
            OLEMSGICON.OLEMSGICON_INFO,
            OLEMSGBUTTON.OLEMSGBUTTON_OK,
            OLEMSGDEFBUTTON.OLEMSGDEFBUTTON_FIRST
        )
        |> ignore

    /// Save every dirty document before the tool touches the disk.
    ///
    /// The tool rewrites source files underneath Visual Studio. With unsaved
    /// editors open there are then two versions of the same file â€” the buffer
    /// VS holds and the one just written â€” and whichever the user saves next
    /// silently discards the other. Saving first also makes a --dry-run report
    /// describe the code the user is actually looking at.
    let private saveDirtyDocuments () =
        ThreadHelper.ThrowIfNotOnUIThread()

        try
            // The RUNNING DOCUMENT TABLE, not IVsSolution: the dirty buffers
            // are documents, and SaveSolutionElement acts on the solution
            // element. VSITEMID_NIL with a null hierarchy and no cookie means
            // "every dirty document".
            match ServiceProvider.GlobalProvider.GetService typeof<SVsRunningDocumentTable> with
            | :? IVsRunningDocumentTable as rdt ->
                rdt.SaveDocuments(uint32 __VSRDTSAVEOPTIONS.RDTSAVEOPT_SaveIfDirty, null, 0xFFFFFFFFu, 0u)
                |> ignore
            | _ -> ()

            // and the solution/project files themselves, which the tool reads
            // to find what to sweep and which need not be open in an editor
            match ServiceProvider.GlobalProvider.GetService typeof<SVsSolution> with
            | :? IVsSolution as solution ->
                solution.SaveSolutionElement(uint32 __VSSLNSAVEOPTIONS.SLNSAVEOPT_SaveIfDirty, null, 0u)
                |> ignore
            | _ -> ()
        with e -> // a failed save must not stop the run; fsharpanalyzer: ignore-line FR0055
            FsacClient.clientTrace $"package: could not save open documents - {e.Message}"

    /// Yes/No, for the one question every run asks: report, or rewrite?
    let private askApply (what: string) =
        ThreadHelper.ThrowIfNotOnUIThread()

        let answer =
            VsShellUtilities.ShowMessageBox(
                ServiceProvider.GlobalProvider,
                $"{what}\r\n\r\nYes — apply the fixes (every pass is build-verified and rolled back on error).\r\nNo — report only, change nothing.\r\n\r\nOpen documents are saved first, because the tool rewrites files on disk.",
                "FSharp.Refactor",
                OLEMSGICON.OLEMSGICON_QUERY,
                OLEMSGBUTTON.OLEMSGBUTTON_YESNOCANCEL,
                OLEMSGDEFBUTTON.OLEMSGDEFBUTTON_SECOND
            )

        // 6 = Yes, 7 = No, anything else is Cancel
        match answer with
        | 6 -> ValueSome true
        | 7 -> ValueSome false
        | _ -> ValueNone

    /// Run the tool to completion, streaming both streams into the pane.
    /// Returns the exit code, or None when it could not be started at all —
    /// which on this path means the global tool is not installed.
    let private runTool (arguments: string) (workingDirectory: string) =
        async {
            writeLine ""
            writeLine $"> {Tool} {arguments}"

            try
                let info =
                    ProcessStartInfo(Tool, arguments,
                        UseShellExecute = false,
                        CreateNoWindow = true,
                        RedirectStandardOutput = true,
                        RedirectStandardError = true,
                        WorkingDirectory = workingDirectory
                    )

                use proc = new Process()
                proc.StartInfo <- info
                proc.EnableRaisingEvents <- true

                proc.OutputDataReceived.Add(fun e ->
                    if not (isNull e.Data) then
                        writeLine e.Data)

                proc.ErrorDataReceived.Add(fun e ->
                    if not (isNull e.Data) then
                        writeLine e.Data)

                proc.Start() |> ignore
                proc.BeginOutputReadLine()
                proc.BeginErrorReadLine()
                proc.WaitForExit()
                return Some proc.ExitCode
            with e ->
                writeLine $"could not start {Tool}: {e.Message}"

                writeLine
                    $"install it with:  dotnet tool install -g {Tool}   (the analyzers and light bulbs work without it)"

                return None
        }

    /// The tool's version, or None when it is not on the PATH.
    let private toolVersion () =
        try
            let info =
                ProcessStartInfo(Tool, "--version",
                    UseShellExecute = false,
                    CreateNoWindow = true,
                    RedirectStandardOutput = true
                )
            use proc = Process.Start info
            let text = proc.StandardOutput.ReadToEnd()
            proc.WaitForExit()
            let trimmed = text.Trim()

            if String.IsNullOrEmpty trimmed then None else Some trimmed
        with _ ->
            None

    // ---- the commands ----------------------------------------------------------

    /// Every command that runs the tool wants the same three things: a
    /// solution to point at, the pane visible, and the work off the UI thread.
    let private onSolution (package: AsyncPackage) (build: string -> string option) =
        ThreadHelper.ThrowIfNotOnUIThread()

        ThreadHelper.JoinableTaskFactory.RunAsync(fun () ->
            task {
                do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()
                let! _ = ensurePane (package :> IAsyncServiceProvider) |> Async.StartAsTask
                match! solutionFile (package :> IAsyncServiceProvider) |> Async.StartAsTask with
                | None -> box' "FSharp.Refactor" "Open a solution first - the tool runs on a solution or a project."
                | Some(dir, file) ->
                    match build file with
                    | None -> () // the command asked something and was answered Cancel
                    | Some arguments ->
                        // the match! above may have resumed off the UI thread,
                        // and both of the next two calls require it
                        do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()
                        showPane ()
                        saveDirtyDocuments ()

                        do!
                            (runTool arguments dir |> Async.StartAsTask) :> Task
            }
            :> Task)
        |> ignore

    let runCommand (package: AsyncPackage) =
        onSolution package (fun file ->
            match askApply "Run fsharp-refactor on this solution?\r\n\r\nIf this repository's fsharprefactor.json sets \"apiChanges\", the run rewrites the public surface and call sites too, exactly as the --api-changes command does." with
            | ValueNone -> None
            | ValueSome true -> Some $"\"%s{file}\""
            | ValueSome false -> Some $"\"%s{file}\" --dry-run")

    let runApiChangesCommand (package: AsyncPackage) =
        onSolution package (fun file ->
            let question =
                "Run with --api-changes?\r\n\r\nThis also rewrites call sites project-wide, and widens the rules that change a declaration's compiled shape to public declarations."

            match askApply question with
            | ValueNone -> None
            | ValueSome true -> Some $"\"%s{file}\" --api-changes"
            | ValueSome false -> Some $"\"%s{file}\" --api-changes --dry-run")

    let reportCommand (package: AsyncPackage) =
        onSolution package (fun file ->
            let out = Path.Combine(Path.GetDirectoryName file, "fsharp-refactor.sarif")
            Some $"\"%s{file}\" --dry-run --report \"%s{out}\"")

    /// The advisory findings as a page, opened in the browser. These carry no
    /// fix, so unlike everything else the tool produces they are worth nothing
    /// unless a person reads them; the SARIF report is for CI, this is for you.
    let reviewNotesCommand (package: AsyncPackage) =
        ThreadHelper.ThrowIfNotOnUIThread()

        ThreadHelper.JoinableTaskFactory.RunAsync(fun () ->
            task {
                do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()
                let! _ = ensurePane (package :> IAsyncServiceProvider) |> Async.StartAsTask
                match! solutionFile (package :> IAsyncServiceProvider) |> Async.StartAsTask with
                | None -> box' "FSharp.Refactor" "Open a solution first."
                | Some(dir, file) ->
                    let out = Path.Combine(dir, "fsharp-refactor-notes.html")
                    showPane ()

                    let! code =
                        runTool $"\"%s{file}\" --dry-run --notes only --report \"%s{out}\"" dir |> Async.StartAsTask

                    do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()

                    if code = Some 0 && File.Exists out then
                        try
                            let start = ProcessStartInfo out
                            start.UseShellExecute <- true
                            Process.Start start |> ignore
                        with e ->
                            writeLine $"wrote %s{out} but could not open it: %s{e.Message}"
            }
            :> Task)
        |> ignore

    /// Write a fsharprefactor.json of the current defaults and open it - or
    /// open the one already there, which holds someone's decisions and is
    /// never replaced (the tool refuses to overwrite for the same reason).
    let createConfigCommand (package: AsyncPackage) =
        ThreadHelper.ThrowIfNotOnUIThread()

        ThreadHelper.JoinableTaskFactory.RunAsync(fun () ->
            task {
                do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()
                let! _ = ensurePane (package :> IAsyncServiceProvider) |> Async.StartAsTask
                match! solutionFile (package :> IAsyncServiceProvider) |> Async.StartAsTask with
                | None -> box' "FSharp.Refactor" "Open a solution first."
                | Some(dir, _) ->
                    let config = Path.Combine(dir, "fsharprefactor.json")

                    if not (File.Exists config) then
                        showPane ()

                        let! _ =
                            runTool $"--create-config \"%s{dir}\"" dir |> Async.StartAsTask

                        do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()

                    if File.Exists config then
                        VsShellUtilities.OpenDocument(ServiceProvider.GlobalProvider, config)
            }
            :> Task)
        |> ignore

    /// Everything a "why do I see no hints?" question needs, in one place.
    let statusCommand (package: AsyncPackage) =
        ThreadHelper.ThrowIfNotOnUIThread()

        ThreadHelper.JoinableTaskFactory.RunAsync(fun () ->
            task {
                do! ThreadHelper.JoinableTaskFactory.SwitchToMainThreadAsync()
                let! _ = ensurePane (package :> IAsyncServiceProvider) |> Async.StartAsTask
                showPane ()

                let assembly = Reflection.Assembly.GetExecutingAssembly()
                let here = Path.GetDirectoryName assembly.Location
                let version = string (assembly.GetName().Version)
                let analyzers = Path.Combine(here, "analyzers")
                let fsac = Path.Combine(here, "fsac", "fsautocomplete.dll")
                let temp = Environment.GetEnvironmentVariable "TEMP"

                let log =
                    if String.IsNullOrEmpty temp then
                        "(TEMP unset)"
                    else
                        Path.Combine(temp, "FSharpRefactor.Vsix.log")

                let present (path: string) (exists: bool) =
                    sprintf "%s %s" path (if exists then "(present)" else "(MISSING)")

                let tool =
                    match toolVersion () with
                    | Some v -> v
                    | None -> $"not installed - dotnet tool install -g %s{Tool}"

                writeLine ""
                writeLine $"FSharp.Refactor extension %s{version}"
                writeLine $"  installed at  %s{here}"
                writeLine (sprintf "  analyzers     %s" (present analyzers (Directory.Exists analyzers)))
                writeLine (sprintf "  bundled FSAC  %s" (present fsac (File.Exists fsac)))
                writeLine $"  apply tool    %s{tool}"
                writeLine $"  sidecar log   %s{log}"
            }
            :> Task)
        |> ignore

    let aboutCommand () =
        ThreadHelper.ThrowIfNotOnUIThread()

        let version = string (Reflection.Assembly.GetExecutingAssembly().GetName().Version)

        let tool =
            match toolVersion () with
            | Some v -> v
            | None -> "not installed"

        let text =
            sprintf
                "FSharp.Refactor %s\r\n\r\nRefactoring hints and one-click quick fixes for F#.\r\n\r\nApply tool: %s\r\n\r\n%s"
                version
                tool
                RepositoryUrl

        box' "About FSharp.Refactor" text

// ---- the package -----------------------------------------------------------

/// Registered through FSharp.Refactor.Vsix.pkgdef, which CreatePkgDef.exe
/// generates from these attributes in CreateVsix.ps1.
///
/// Background-loaded on SolutionExists rather than at startup: an
/// extension nobody used today should cost nothing, and there is no menu
/// worth showing before a solution is open anyway.
[<PackageRegistration(UseManagedResourcesOnly = true, AllowsBackgroundLoading = true)>]
[<Guid(Commands.PackageGuidString)>]
[<ProvideMenuResource("Menus.ctmenu", 1)>]
[<ProvideAutoLoad(Microsoft.VisualStudio.VSConstants.UICONTEXT.SolutionExists_string,
                  PackageAutoLoadFlags.BackgroundLoad)>]
type FSharpRefactorPackage() =
    inherit AsyncPackage()

    override this.InitializeAsync(cancellationToken: CancellationToken, _progress: IProgress<ServiceProgressData>) =
        // Started OUT here on purpose: `task { }` compiles its body to a
        // closure, and F# refuses a `base.` call from inside one (FS0491), so
        // the base implementation cannot be awaited where it reads best. It
        // starts first and is awaited before anything else runs.
        let baseInit = base.InitializeAsync(cancellationToken, _progress)

        task {
            // The loader used to run silently, which made "the menu is not
            // there" undiagnosable: a package that loads cleanly and a package
            // that registers nothing look identical from outside. Everything
            // here traces to %TEMP%\FSharpRefactor.Vsix.log beside the rest.
            FsacClient.clientTrace "package: InitializeAsync entered"

            try
                do! baseInit
                do! this.JoinableTaskFactory.SwitchToMainThreadAsync cancellationToken

                match! this.GetServiceAsync(typeof<IMenuCommandService>) with
                | :? OleMenuCommandService as commands ->
                    let commandSet = Guid Commands.CommandSetGuidString

                    let mutable added = 0

                    let add id (handler: unit -> unit) =
                        commands.AddCommand(MenuCommand(EventHandler(fun _ _ -> handler ()), CommandID(commandSet, id)))
                        added <- added + 1

                    add Commands.Ids.Run (fun () -> Commands.runCommand this)
                    add Commands.Ids.RunApiChanges (fun () -> Commands.runApiChangesCommand this)
                    add Commands.Ids.Report (fun () -> Commands.reportCommand this)
                    add Commands.Ids.CreateConfig (fun () -> Commands.createConfigCommand this)
                    add Commands.Ids.ReviewNotes (fun () -> Commands.reviewNotesCommand this)
                    add Commands.Ids.Status (fun () -> Commands.statusCommand this)
                    add Commands.Ids.About (fun () -> Commands.aboutCommand ())

                    FsacClient.clientTrace $"package: {added} commands registered for command set {commandSet}"
                | other ->
                    // the silent escape: no handler is attached to ANY command
                    // and the only symptom is a menu that does nothing
                    let got =
                        if isNull (box other) then
                            "null"
                        else
                            other.GetType().FullName

                    FsacClient.clientTrace $"package: NO commands registered - IMenuCommandService came back as {got}"
            with e ->
                FsacClient.clientTrace $"package: InitializeAsync FAILED - {e.GetType().FullName}: {e.Message}"
                System.Runtime.ExceptionServices.ExceptionDispatchInfo.Capture(e).Throw()
        }
        :> Task
