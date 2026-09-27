/// The `.editorconfig` a file answers to, read the way EditorConfig says:
/// every `.editorconfig` from the file's directory up to the first one
/// that sets `root = true`, the nearest winning, and within one file the
/// later matching section winning. Enough of the glob language for the
/// sections F# repositories write - `*`, `**`, `?`, `{a,b}` alternatives
/// and `[...]` character classes - and nothing that needs a package: these
/// analyzers also load inside every editor.
///
/// The consumer is the formatter's configuration. Fantomas reads its
/// settings from here, and a rule that rewrites what the formatter was told
/// to keep would fight it on every save: `fsharp_space_before_lowercase_
/// invocation = false` is how a repository says it writes `f(x)`.
module FSharp.Refactor.EditorConfig

open System
open System.Collections.Concurrent
open System.IO
open System.Text
open System.Text.RegularExpressions

/// One `.editorconfig`: whether it is the root, and its sections in order,
/// each a glob matcher and its key/value pairs (keys lowercased).
type private Parsed =
    {
        IsRoot: bool
        Sections: ((string -> bool) * (string * string) list) list
    }

/// An EditorConfig glob as a regex over a path relative to the file's
/// directory, `/`-separated. A glob with no `/` matches a file name at any
/// depth, as EditorConfig specifies.
let private globRegex (glob: string) =
    let body = StringBuilder()
    let mutable i = 0
    let mutable braces = 0

    while i < glob.Length do
        let c = glob.[i]

        match c with
        | '*' when i + 1 < glob.Length && glob.[i + 1] = '*' ->
            body.Append ".*" |> ignore
            i <- i + 1
        | '*' -> body.Append "[^/]*" |> ignore
        | '?' -> body.Append "[^/]" |> ignore
        | '{' ->
            braces <- braces + 1
            body.Append "(?:" |> ignore
        | '}' when braces > 0 ->
            braces <- braces - 1
            body.Append ')' |> ignore
        | ',' when braces > 0 -> body.Append '|' |> ignore
        | '[' ->
            let close = glob.IndexOf(']', i + 1)

            if close > i then
                let inner = glob.Substring(i + 1, close - i - 1)

                let inner =
                    if inner.StartsWith '!' then
                        "^" + inner.Substring 1
                    else
                        inner

                body.Append('[').Append(inner.Replace("\\", "\\\\")).Append(']') |> ignore
                i <- close
            else
                body.Append "\\[" |> ignore
        | c -> body.Append(Regex.Escape(string c)) |> ignore

        i <- i + 1

    let pattern = body.ToString()

    let anchored =
        if glob.Contains '/' then
            "^" + pattern.TrimStart('/') + "$"
        else
            $"(?:^|/){pattern}$"

    Regex(anchored, RegexOptions.IgnoreCase ||| RegexOptions.CultureInvariant)

let private parse (text: string) : Parsed =
    let mutable isRoot = false
    let sections = ResizeArray<(string -> bool) * ResizeArray<string * string>>()

    for raw in text.Split '\n' do
        let line = raw.Trim()

        if line = "" || line.StartsWith '#' || line.StartsWith ';' then
            ()
        elif line.StartsWith '[' && line.EndsWith ']' then
            // a glob this translation cannot turn into a regex (`[z-a]`)
            // matches nothing rather than throwing out of an analyzer: an
            // editor loads these on every keystroke
            let matches: string -> bool =
                try
                    (globRegex (line.Substring(1, line.Length - 2))).IsMatch
                with :? ArgumentException ->
                    fun _ -> false

            sections.Add(matches, ResizeArray())
        else
            match line.IndexOf '=' with
            | -1 -> ()
            | eq ->
                let key = line.Substring(0, eq).Trim().ToLowerInvariant()
                let value = line.Substring(eq + 1).Trim()

                if sections.Count = 0 then
                    if key = "root" then
                        isRoot <- value.Equals("true", StringComparison.OrdinalIgnoreCase)
                else
                    (snd sections.[sections.Count - 1]).Add((key, value))

    {
        IsRoot = isRoot
        Sections =
            sections
            |> Seq.map (fun (matches, pairs) -> matches, List.ofSeq pairs)
            |> List.ofSeq
    }

/// Parsed files by path, reloaded when the write time moves.
let private cache =
    ConcurrentDictionary<string, DateTime * Parsed>(StringComparer.OrdinalIgnoreCase)

let private read (path: string) : Parsed option =
    try
        if File.Exists path then
            let written = File.GetLastWriteTimeUtc path

            let _, parsed =
                cache.AddOrUpdate(
                    path,
                    (fun p -> written, parse (File.ReadAllText p)),
                    (fun p (stamp, old) ->
                        if stamp = written then
                            stamp, old
                        else
                            written, parse (File.ReadAllText p))
                )

            Some parsed
        else
            None
    with
    | :? IOException
    | :? UnauthorizedAccessException -> None

/// The value of `key` for `analyzedFile`, or None when no `.editorconfig`
/// on the way up sets it.
let value (analyzedFile: string) (key: string) : string option =
    let key = key.ToLowerInvariant()

    let fullPath =
        try
            Some(Path.GetFullPath analyzedFile)
        with
        | :? ArgumentException
        | :? PathTooLongException
        | :? NotSupportedException -> None

    match fullPath with
    | None -> None
    | Some fullPath ->
        // from the file's directory upward, nearest first; a nearer file's
        // answer wins, so the first one that sets the key decides
        let rec walk (directory: string) =
            if String.IsNullOrEmpty directory then
                None
            else
                let answer, isRoot =
                    match read (Path.Combine(directory, ".editorconfig")) with
                    | Some parsed ->
                        let relative = Path.GetRelativePath(directory, fullPath).Replace('\\', '/')

                        let answer =
                            parsed.Sections
                            |> List.filter (fun (matches, _) -> matches relative)
                            |> List.collect snd
                            |> List.filter (fun (k, _) -> k = key)
                            |> List.tryLast
                            |> Option.map snd

                        answer, parsed.IsRoot
                    | None -> None, false

                match answer with
                | Some _ -> answer
                | None when isRoot -> None
                | None ->
                    match Path.GetDirectoryName directory with
                    | null -> None
                    | parent -> walk parent

        walk (Path.GetDirectoryName fullPath)

/// Does the formatter's configuration say this file writes `f(x)` - Fantomas
/// told to put no space before the parenthesised argument of a lowercase
/// call? Its default is `f (x)`, so the setting is a deliberate choice, and
/// FR0013 taking the parentheses away would undo it on every sweep.
let keepsLowercaseCallParens (analyzedFile: string) =
    value analyzedFile "fsharp_space_before_lowercase_invocation"
    |> Option.exists (fun v -> v.Equals("false", StringComparison.OrdinalIgnoreCase))
