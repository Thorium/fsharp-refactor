/// The apply tool's run-scoped decisions for the compilation being
/// analysed, as one value the analyzers read.
///
/// Editors never set it: the SDK hosts the same analyzers there with the
/// defaults, which are the narrow, always-safe rules. The apply tool sets
/// it once per compilation and resets it after — a test project turns
/// `ApiChanges` on for itself alone, a framework pass carries its dual
/// constant, a `--codes` list names what was typed — so a decision made
/// for one compilation can never leak into the next, which is what the
/// FSREF_* environment variables this replaces once let happen (a leaked
/// no-guard flag dropped the capability fixes of every later target).
///
/// Process-wide, like the flags were: one compilation is analysed at a
/// time, and the sweep's parallel file checks all belong to it.
module FSharp.Refactor.Scope

open System

type AnalysisScope =
    {
        /// `--api-changes` (or `"apiChanges": true`, or a test project):
        /// the caller owns every caller, cross-file rewrites included.
        ApiChanges: bool
        /// Codes and analyzer names the run explicitly asked for with
        /// `--codes` — never a `--categories` expansion. Naming a rule
        /// turns it on over its default-off status and a config disable.
        ForcedCodes: Set<string>
        /// The project's own framework-shaped constant, on the modern
        /// passes of a project with legacy targets: capability fixes emit
        /// `#if <constant>` pairs around code the legacy half cannot
        /// compile. ValueNone: fixes go in plainly.
        DualTfmConstant: string voption
        /// A pass over a framework wider than the project's narrowest, with
        /// no constant to guard with: a capability fix has nowhere safe to
        /// live and keeps its advice without the edit.
        GuardUnavailable: bool
        /// A project of another language (C#, VB) in the workspace
        /// references this one and cannot be built here, so no check of
        /// this run can see what it links to: the public surface keeps
        /// its shape whatever `ApiChanges` says. FSharp.Azure.Quantum's C#
        /// project cast to a union's nested case class; the union went
        /// `[<Struct>]` under --api-changes, the F# project's build
        /// passed, and the C# one stopped compiling. The apply tool
        /// builds such a consumer as part of its verification where it
        /// can, and sets this — saying why — where it cannot.
        PublicSurfaceHeld: bool
    }

/// What an editor sees, and what a run starts from.
let editor =
    {
        ApiChanges = false
        ForcedCodes = Set.empty
        DualTfmConstant = ValueNone
        GuardUnavailable = false
        PublicSurfaceHeld = false
    }

let mutable private current = editor

/// The scope of the compilation being analysed.
let scope () = current

let set (s: AnalysisScope) = current <- s

let reset () = current <- editor

/// Run `body` under `s`, restoring whatever was in force before — the
/// shape the tests and the corpus harness want.
let under (s: AnalysisScope) (body: unit -> 'a) =
    let before = current
    current <- s

    try
        body ()
    finally
        current <- before

/// Was this code or analyzer name typed in `--codes`?
let forced (code: string) (analyzerName: string) =
    current.ForcedCodes
    |> Set.exists (fun c ->
        c.Equals(code, StringComparison.OrdinalIgnoreCase)
        || c.Equals(analyzerName, StringComparison.OrdinalIgnoreCase))
