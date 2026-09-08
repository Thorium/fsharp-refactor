/// Refactoring (FR0144, fix): a script's `#r` or `#I` path that no longer
/// exists is re-pointed at the sibling that does — the package's current
/// target-framework folder, or its current version folder.
///
///     #r @"../packages/Sql.1.2.3/lib/net451/Sql.dll"
///          →  #r @"../packages/Sql.1.2.3/lib/net461/Sql.dll"
///     #I @"../packages/Sql.1.2.3/lib/netstandard1.6"
///          →  #I @"../packages/Sql.1.2.3/lib/netstandard2.0"
///
/// Packages move their target folders between versions — net451 to
/// net461, netstandard1.6 to netstandard2.0, net481 to net48 — and the
/// compiler only says the reference is invalid. The path itself says
/// where to look: the first segment that does not exist, when it is a
/// target-framework folder or a `Name.1.2.3` version folder, has siblings,
/// and the ones under which the rest of the path still exists (a file for
/// `#r`, a directory for `#I`) are the candidates.
///
/// Ranking follows what the script runs on. A `net4x` original means the
/// .NET Framework: the newest `net4y` first, then `netstandard2.0` and
/// below — never `netstandard2.1` or `netX.0`, which that runtime cannot
/// load. Anything else means a modern runtime: the newest `netX.0` not
/// above the SDK the script is checked against (read off the reference
/// assemblies in the compiler options), then `netstandard2.1`, `2.0`,
/// older; `netcoreapp` is a dead family and the last resort. Newest first
/// within a family. A version folder is replaced by the newest sibling
/// version.
///
/// The fix rewrites only the changed segment inside the directive, so the
/// quoting (`@"..."` or `"..."`) and the separators stay as written; the
/// message lists the other candidates. `.fsx` only; runs without a
/// typecheck, like FR0143.
module FSharp.Refactor.ScriptReferences

open System
open System.IO
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text
open System.Text.RegularExpressions

/// Runs of path separators, kept as split pieces so a rewrite preserves them.
let private separatorRuns = Regex(@"([\\/]+)", RegexOptions.Compiled)

type Suggestion =
    {
        /// The directive argument, quotes included.
        Range: range
        OriginalText: string
        ReplacementText: string
        Message: string
    }

/// A parsed target-framework folder name.
type private Framework =
    | NetFramework of int // net45 = 45, net481 = 481
    | NetStandard of decimal // 2.0, 2.1
    | NetCoreApp of decimal // 3.1
    | Net of int // net6.0 = 6

let private parseFramework (segment: string) : Framework option =
    let s = segment.ToLowerInvariant()

    let number (text: string) =
        match
            Decimal.TryParse(
                text,
                Globalization.NumberStyles.AllowDecimalPoint,
                Globalization.CultureInfo.InvariantCulture
            )
        with
        | true, v -> Some v
        | _ -> None

    if s.StartsWith "netstandard" then
        number (s.Substring 11) |> Option.map NetStandard
    elif s.StartsWith "netcoreapp" then
        number (s.Substring 10) |> Option.map NetCoreApp
    elif s.StartsWith "net" && s.Length > 3 then
        let rest = s.Substring 3
        // net6.0, net8.0-windows: modern; net45, net481: framework
        let core = rest.Split('-').[0]

        if core.Contains '.' then
            match Int32.TryParse(core.Split('.').[0]) with
            | true, major when major >= 5 -> Some(Net major)
            | _ -> None
        else
            match Int32.TryParse core with
            | true, v when v >= 20 && v < 500 -> Some(NetFramework v)
            | _ -> None
    else
        None

/// Newest first within a family; families ordered by what the runtime
/// the original implies can load.
let private rank (original: Framework) (sdkMajor: int option) (candidate: Framework) : int option =
    match original, candidate with
    // .NET Framework: net4y newest first, then netstandard <= 2.0
    | NetFramework _, NetFramework v -> Some(1000 - v)
    | NetFramework _, NetStandard v when v <= 2.0m -> Some(2000 - int (v * 10m))
    | NetFramework _, _ -> None
    // modern: netX.0 not above the SDK, newest first; then netstandard
    // 2.1, 2.0, older; netcoreapp is a dead family, the last resort
    | _, Net major ->
        match sdkMajor with
        | Some sdk when major > sdk -> None
        | _ -> Some(1000 - major)
    | _, NetStandard v -> Some(2000 - int (v * 10m))
    | _, NetCoreApp v -> Some(3000 - int (v * 10m))
    | _, NetFramework _ -> None

/// `Name.1.2.3` → (Name, [1;2;3]).
let private parseVersioned (segment: string) =
    let m = Regex.Match(segment, @"^(.+?)\.(\d+(?:\.\d+)+)$")

    if m.Success then
        Some(m.Groups.[1].Value, m.Groups.[2].Value.Split '.' |> Array.map int |> List.ofArray)
    else
        None

/// The major version of the SDK the script is checked against, read off
/// its reference assemblies (`...\ref\net10.0\...`).
let sdkMajorOf (compilerOptions: string seq) =
    compilerOptions
    |> Seq.tryPick (fun o ->
        let m = Regex.Match(o, @"[\\/]ref[\\/]net(\d+)\.0[\\/]")

        if m.Success then Some(int m.Groups.[1].Value) else None)

let private exists (isDirectory: bool) (path: string) =
    if isDirectory then
        Directory.Exists path
    else
        File.Exists path

/// For a missing path: the index of the first missing segment and the
/// replacement segments that make the rest of the path exist, best first.
let private candidates (isDirectory: bool) (scriptDir: string) (segments: string list) (sdkMajor: int option) =
    let rec firstMissing (prefix: string) (index: int) (rest: string list) =
        match rest with
        | [] -> None
        | segment :: tail ->
            let here = Path.Combine(prefix, segment)

            if Directory.Exists here || (tail.IsEmpty && exists isDirectory here) then
                firstMissing here (index + 1) tail
            else
                Some(prefix, index, segment, tail)

    match firstMissing scriptDir 0 segments with
    | None -> ValueNone
    | Some(parent, index, missing, tail) when Directory.Exists parent ->
        let siblings =
            try
                Directory.GetDirectories parent |> Array.map Path.GetFileName |> List.ofArray
            with _ -> // fsharpanalyzer: ignore-line FR0055
                []

        let leadsToTarget (sibling: string) =
            let full =
                List.fold (fun p s -> Path.Combine(p, s)) (Path.Combine(parent, sibling)) tail

            if tail.IsEmpty then
                exists isDirectory full
            else
                exists isDirectory full

        let ranked =
            match parseFramework missing, parseVersioned missing with
            | Some original, _ ->
                siblings
                |> List.choose (fun s ->
                    parseFramework s
                    |> Option.bind (rank original sdkMajor)
                    |> Option.map (fun r -> r, s))
                |> List.filter (fun (_, s) -> leadsToTarget s)
                |> List.sortBy fst
                |> List.map snd
            | None, Some(name, _) ->
                siblings
                |> List.choose (fun s ->
                    match parseVersioned s with
                    | Some(n, v) when String.Equals(n, name, StringComparison.OrdinalIgnoreCase) -> Some(v, s)
                    | _ -> None)
                |> List.filter (fun (_, s) -> leadsToTarget s)
                |> List.sortByDescending fst
                |> List.map snd
            | None, None -> []

        if ranked.IsEmpty then
            ValueNone
        else
            ValueSome(index, ranked)
    | Some _ -> ValueNone

let find (script: string) (tree: ParsedInput) (source: ISourceText) (compilerOptions: string seq) : Suggestion list =
    if not (script.EndsWith(".fsx", StringComparison.OrdinalIgnoreCase)) then
        []
    else
        let scriptDir = Path.GetDirectoryName(Path.GetFullPath script)
        let sdkMajor = sdkMajorOf compilerOptions

        [ for d in ScriptLoads.directives tree do
              let isDirectory =
                  match d.Ident with
                  | "I" -> true
                  | "r" -> false
                  | _ -> false

              // `#r "nuget: ..."`, `#r "System.Net.Http"`: not paths
              let isPath =
                  (d.Ident = "r" || d.Ident = "I")
                  && not (d.Value.Contains ':' && not (d.Value.Length > 1 && d.Value.[1] = ':'))
                  && (d.Value.Contains '/' || d.Value.Contains '\\')

              if isPath then
                  // the root (`C:\`, `\\server\share\`) is walked from as
                  // one piece; the rest is split into segments
                  let root, relative =
                      if Path.IsPathRooted d.Value then
                          let r = Path.GetPathRoot d.Value
                          r, d.Value.Substring r.Length
                      else
                          scriptDir, d.Value

                  let segments =
                      relative.Split([| '/'; '\\' |], StringSplitOptions.RemoveEmptyEntries)
                      |> List.ofArray

                  match candidates isDirectory root segments sdkMajor with
                  | ValueSome(index, best :: others) ->
                      let original = textOfRange source d.ArgumentRange
                      let missing = List.item index segments

                      // swap the one segment BY POSITION inside the text as
                      // written — quoting and separators stay, and a folder
                      // elsewhere in the path that merely contains the
                      // segment's name (`Foo.net45/lib/net45`) is not the
                      // one rewritten
                      let replacement =
                          let pieces = separatorRuns.Split original

                          // path segments are the non-separator pieces whose
                          // text ends with the segment name (the first piece
                          // carries the quote and any `@` or drive)
                          let mutable seen = -1
                          let mutable done' = false

                          let rebuilt =
                              pieces
                              |> Array.map (fun piece ->
                                  if done' || piece = "" || piece.[0] = '\\' || piece.[0] = '/' then
                                      piece
                                  else
                                      let isRoot =
                                          seen = -1
                                          && Path.IsPathRooted d.Value
                                          && piece.TrimStart('@', '"').Contains ':'

                                      if isRoot then
                                          piece
                                      else
                                          seen <- seen + 1

                                          // the last piece carries the closing quote
                                          let core = piece.TrimEnd '"'
                                          let quotes = piece.Substring core.Length

                                          if seen = index && core.EndsWith(missing, StringComparison.Ordinal) then
                                              done' <- true
                                              core.Substring(0, core.Length - missing.Length) + best + quotes
                                          else
                                              piece)

                          if done' then String.Join("", rebuilt) else original

                      // and the rewritten path must exist: a swap that lands
                      // nowhere would keep the error count level and be kept
                      let rewrittenExists =
                          let full =
                              segments
                              |> List.mapi (fun i s -> if i = index then best else s)
                              |> List.fold (fun p s -> Path.Combine(p, s)) root

                          exists isDirectory full

                      if replacement <> original && rewrittenExists then
                          let alternatives =
                              match others with
                              | [] -> ""
                              | more ->
                                  let joined = String.Join(", ", more)
                                  $"; also present: {joined}"

                          yield
                              { Range = d.ArgumentRange
                                OriginalText = original
                                ReplacementText = replacement
                                Message =
                                  $"#{d.Ident} path does not exist: '{missing}' is gone, and '{best}' is what the package has now{alternatives}. The fix re-points the directive." }
                  | _ -> () ]
