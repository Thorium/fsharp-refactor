/// Typechecking for generated programs. One checker, one set of options
/// computed once (a generated program carries no `#r`, so they never
/// change), and a version counter per check, so a program's check costs
/// its own typecheck and nothing else — the example-based suite's
/// `parseAndCheck` resolves the script's references on every call, which
/// is fine for one test and too slow for a hundred generated programs.
///
/// The program is checked as the script `Test.fsx` of a two-file project
/// whose first file, `Stubs.fs`, declares the namespaces some rules gate
/// on — a test framework's attributes, a logger — since a script cannot
/// open a namespace of its own and no package is referenced. A rule that
/// wants the project's typed results (FR0155) gets them from `Project`,
/// computed on first use.
module FSharp.Refactor.PropertyTests.Typed

open System.IO
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

let private checker = FSharpChecker.Create(keepAssemblyContents = true)

let private directory =
    let dir = Path.Combine(Path.GetTempPath(), "fsref-properties")
    Directory.CreateDirectory dir |> ignore
    dir

let private stubsPath = Path.Combine(directory, "Stubs.fs")
let private scriptPath = Path.Combine(directory, "Test.fsx")

/// The namespaces a script cannot declare and some rules require by name:
/// xunit's attributes (FR0142 awaits a Task only under a framework it
/// trusts) and Microsoft.Extensions.Logging's logger with the extension
/// methods FR0120 and FR0124 read.
let stubs =
    """namespace Xunit

type FactAttribute() =
    inherit System.Attribute()

type TheoryAttribute() =
    inherit System.Attribute()

namespace Microsoft.Extensions.Logging

type ILogger =
    interface
    end

[<System.Runtime.CompilerServices.Extension>]
type LoggerExtensions =
    [<System.Runtime.CompilerServices.Extension>]
    static member LogError(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, message, args)

    [<System.Runtime.CompilerServices.Extension>]
    static member LogError(logger: ILogger, ex: exn, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, ex, message, args)

    [<System.Runtime.CompilerServices.Extension>]
    static member LogWarning(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, message, args)

    [<System.Runtime.CompilerServices.Extension>]
    static member LogWarning(logger: ILogger, ex: exn, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, ex, message, args)

    [<System.Runtime.CompilerServices.Extension>]
    static member LogInformation(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, message, args)

    [<System.Runtime.CompilerServices.Extension>]
    static member LogDebug(logger: ILogger, message: string, [<System.ParamArray>] args: obj[]) =
        ignore (logger, message, args)
"""

let private options =
    lazy
        (File.WriteAllText(stubsPath, stubs)

         let options, _ =
             checker.GetProjectOptionsFromScript(scriptPath, SourceText.ofString "", assumeDotNetFramework = false)
             |> Async.RunSynchronously

         { options with
             ProjectFileName = Path.Combine(directory, "Properties.fsproj")
             SourceFiles = [| stubsPath; scriptPath |]
         })

let private gate = obj ()
let mutable private version = 0

/// A typechecked program: the tree, the text, the check results, the
/// error messages the check produced, and the project's results on
/// demand.
type Checked =
    {
        Tree: ParsedInput
        Source: ISourceText
        Check: FSharpCheckFileResults
        Errors: string list
        Project: Lazy<FSharpCheckProjectResults>
    }

/// Parse and typecheck a program as the project's script.
let check (source: string) : Checked =
    lock gate (fun () ->
        let sourceText = SourceText.ofString source
        version <- version + 1
        let v = version
        File.WriteAllText(scriptPath, source)

        let parseResults, answer =
            checker.ParseAndCheckFileInProject(scriptPath, v, sourceText, options.Value)
            |> Async.RunSynchronously

        match answer with
        | FSharpCheckFileAnswer.Succeeded results ->
            {
                Tree = parseResults.ParseTree
                Source = sourceText
                Check = results
                Errors =
                    [
                        for d in results.Diagnostics do
                            if d.Severity = FSharpDiagnosticSeverity.Error then
                                $"({d.StartLine},{d.StartColumn}) FS{d.ErrorNumber:D4} {d.Message}"
                    ]
                Project =
                    lazy
                        (lock gate (fun () ->
                            // the script on disk may have moved on: put this program back first
                            File.WriteAllText(scriptPath, source)

                            checker.ParseAndCheckProject
                                { options.Value with
                                    Stamp = Some(int64 v)
                                }
                            |> Async.RunSynchronously))
            }
        | FSharpCheckFileAnswer.Aborted -> failwithf "typecheck aborted:\n%s" source)
