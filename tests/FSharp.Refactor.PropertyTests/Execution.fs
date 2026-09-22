/// Running a generated program, so a property can compare what it DID
/// before and after a fix. Parsing and typechecking say a rewrite is
/// well-formed; only running it says the rewrite kept the meaning — the
/// gap that let FR0071 hoist an array literal out of a loop, where every
/// iteration then shared one buffer, through a suite that only ever
/// checked the result still compiled.
///
/// One F# Interactive session for the whole run: creating it costs about
/// a second, each program after that about 50 ms. A program is evaluated
/// as a nested module of its own, so two programs cannot see each other's
/// names, and its trace is read back through `trace ()`, which clears the
/// log first and so answers the same on every call.
module FSharp.Refactor.PropertyTests.Execution

open System.IO
open System.Text
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Interactive.Shell

let private gate = obj ()
let mutable private counter = 0

let private session =
    lazy
        (let inStream = new StringReader("")
         let outStream = new StringWriter(StringBuilder())
         let errStream = new StringWriter(StringBuilder())

         let argv = [| "dotnet"; "fsi"; "--noninteractive"; "--nologo"; "--gui-" |]

         FsiEvaluationSession.Create(
             FsiEvaluationSession.GetDefaultConfiguration(),
             argv,
             inStream,
             outStream,
             errStream
         ))

/// Indent every non-blank line, so a top-level program becomes the body
/// of a module. Uniform indentation moves no offside line.
let private indented (source: string) =
    source.Replace("\r\n", "\n").Split '\n'
    |> Array.map (fun line -> if line.Trim() = "" then "" else "    " + line)
    |> String.concat "\n"

let private errorsOf (diagnostics: FSharpDiagnostic[]) =
    diagnostics
    |> Array.filter (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)
    |> Array.map _.Message
    |> Array.toList

/// Run a program and return what it appended to its log. The program
/// declares `trace`; see `Effects.program`.
let trace (source: string) : Result<string, string> =
    lock gate (fun () ->
        counter <- counter + 1
        let name = $"P{counter}"
        let fsi = session.Value

        let text = $"module {name} =\n{indented source}\n"

        try
            match fsi.EvalInteractionNonThrowing text with
            | Choice2Of2 e, _ -> Error $"evaluating: {e.Message}"
            | Choice1Of2 _, diagnostics ->
                match errorsOf diagnostics with
                | [] ->
                    match fsi.EvalExpressionNonThrowing $"{name}.trace ()" with
                    | Choice1Of2(Some value), _ -> Ok(string value.ReflectionValue)
                    | Choice1Of2 None, _ -> Error "the program produced no trace"
                    | Choice2Of2 e, _ -> Error $"tracing: {e.Message}"
                | messages -> Error(String.concat "; " messages)
        with e -> // an FSI session that falls over must fail the property, not the run
            Error $"fsi: {e.Message}")
