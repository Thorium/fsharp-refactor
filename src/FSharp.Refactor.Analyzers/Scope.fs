/// The apply tool's run-scoped decisions for the compilation being
/// analysed, as one value the analyzers read.
///
/// Editors never set it: the SDK hosts the same analyzers there with the
/// defaults, which are the narrow, always-safe rules. The apply tool sets
/// it once per compilation and resets it after — a test project turns
/// `ApiChanges` on for itself alone, a framework pass carries its dual
/// constant, a `--codes` list names what was typed — so a decision made
/// for one compilation can never leak into the next (a leaked no-guard
/// flag would drop the capability fixes of every later target).
///
/// Process-wide: one compilation is analysed at a
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
        /// its shape whatever `ApiChanges` says: a C# project that casts
        /// to a union's nested case class stops compiling when the union
        /// goes `[<Struct>]`, while the F# build still passes. The apply tool
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

/// The codes the run is restricted to - `--codes`, narrowed by
/// `--categories` - or None for every rule. A rule outside it is off, so
/// its analyzer never runs: filtering only the messages would pay a slow
/// rule's full cost (minutes per pass, for FR0147) and throw every message
/// away.
///
/// An AsyncLocal, unlike the rest of the scope: it SWITCHES RULES OFF,
/// and a process-wide switch would take them from whatever else runs
/// beside the run - a test class in parallel with a test driving the
/// tool. It flows into the tasks and threads the run starts (the sweep's
/// checks, DeepStack's workers) and nowhere else.
let private allowedCodes = System.Threading.AsyncLocal<Set<string> option>()

let restrictTo (codes: Set<string> option) = allowedCodes.Value <- codes

/// Does the run's restriction, if any, let this code or analyzer name run?
let allowed (code: string) (analyzerName: string) =
    match allowedCodes.Value with
    | None -> true
    | Some codes ->
        codes
        |> Set.exists (fun c ->
            c.Equals(code, StringComparison.OrdinalIgnoreCase)
            || c.Equals(analyzerName, StringComparison.OrdinalIgnoreCase))
