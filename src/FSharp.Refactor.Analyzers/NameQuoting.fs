/// FR0133 (fix): a long camel- or snake-case name — five
/// words or more — becomes a double-backtick name, everywhere it is used:
///
///     let thisIsMyVeryComplexMethod x =        let ``this is my very complex method`` x =
///     let this_is_my_very_complex_case = ..    let ``this is my very complex case`` = ..
///
/// Scope decides safety:
///   - LOCAL bindings and strictly FILE-PRIVATE module bindings: every
///     use is in this file by scoping, so the file's typed uses rename
///     them all.
///   - TEST-attributed bindings ([<Test>], [<Fact>], [<Theory>], ...)
///     rename even when public — the name IS the display name there —
///     but only when the project's uses confirm nothing calls them from
///     another file.
///   - everything else stays: serialization APIs legitimately demand
///     snake_case, and a public name is a contract.
///
/// Names carrying an ALL-CAPS run (APRUnitRate) are skipped — acronyms
/// are words already. Test-attributed names rewrite BY DEFAULT — there
/// the name is nothing but a display name, and the backtick spelling is
/// the F# testing convention. Local and file-private names are opt-in
/// (`{"FR0133": {"locals": 1}}`): the readability is real, but some
/// editors still fumble backtick-name intellisense and debugging.
module FSharp.Refactor.NameQuoting

open System
open System.IO
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        Name: string
        Quoted: string
        /// Every occurrence, definition included.
        Edits: (range * string * string) list
    }

let private testAttributes =
    set
        [
            "Test"
            "Fact"
            "Theory"
            "TestMethod"
            "Property"
            "TestCase"
            "TestCaseSource"
        ]

let private aZRegex = Regex "(?=[A-Z])"

let private aZazAZaz09Regex = Regex @"^[A-Za-z][A-Za-z0-9_]*$"
let private aZ2Regex = Regex "[A-Z]{2}"

/// The double-backtick spelling, when the name earns one: five or more
/// words, plain camel/snake, no acronym runs.
let quotedForm (name: string) : string option =
    if aZ2Regex.IsMatch name || not (aZazAZaz09Regex.IsMatch name) then
        None
    else
        let words =
            name.Split '_' |> Array.collect aZRegex.Split |> Array.filter (fun s -> s <> "")

        if words.Length > 4 then
            Some(words |> Array.map (fun w -> w.ToLowerInvariant()) |> String.concat " ")
        else
            None

/// A run of identifier characters: a plain name (`[A-Za-z][A-Za-z0-9_]*`)
/// written anywhere lies inside one such run.
let private identifierRun = Regex(@"[A-Za-z0-9_]+", RegexOptions.Compiled)

/// The identifier runs of a file on disk, cached by its write time and length.
let private fileRuns =
    System.Collections.Concurrent.ConcurrentDictionary<
        string,
        struct (DateTime * int64 * System.Collections.Generic.HashSet<string>)
     >(
        StringComparer.OrdinalIgnoreCase
    )

/// Does this file spell the name as a whole identifier run? `None` when it
/// cannot be read.
let private fileSpells (path: string) (name: string) : bool option =
    try
        let info = FileInfo path

        let runs =
            match fileRuns.TryGetValue path with
            | true, struct (stamp, length, runs) when stamp = info.LastWriteTimeUtc && length = info.Length -> runs
            | _ ->
                let runs =
                    System.Collections.Generic.HashSet<string>(
                        identifierRun.Matches(File.ReadAllText path) |> Seq.map (fun m -> m.Value),
                        StringComparer.Ordinal
                    )

                fileRuns.[path] <- struct (info.LastWriteTimeUtc, info.Length, runs)
                runs

        Some(runs.Contains name)
    with _ -> // an unreadable file answers nothing; fsharpanalyzer: ignore-line FR0055
        None

/// Every `` ``text`` `` of a source: the text between a double backtick and
/// the next backtick, when a second one follows it.
let private doubleBacktickTexts (text: string) =
    let found = System.Collections.Generic.HashSet<string>()

    let rec scan (from: int) =
        match text.IndexOf("``", from, StringComparison.Ordinal) with
        | -1 -> ()
        | i ->
            match text.IndexOf('`', i + 2) with
            | j when j > i + 2 && j + 1 < text.Length && text.[j + 1] = '`' ->
                found.Add(text.Substring(i + 2, j - i - 2)) |> ignore
                scan (i + 1)
            | _ -> scan (i + 1)

    scan 0
    found

let find
    (includeLocals: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (projectCheck: FSharpCheckProjectResults option)
    : Suggestion list =
    // a companion .fsi declares the binding under its OLD name, and only the
    // implementation side of a rename compiles to "the names differ" — so
    // the signature's `val` is renamed in the same edit set, or, where the
    // signature cannot be read, every rename in the file is withheld
    let signature = SignatureFile.read parseTree.FileName

    match signature with
    | SignatureFile.Unreadable -> []
    | _ when OptionModule.hasErrors check -> []
    | _ ->
        let index = AstIndex.ofTree parseTree

        // a name mentioned inside ANY string literal may be a reflection or
        // attribute reference — [<TestCaseSource("mySourceName")>] resolves
        // by string at runtime, where a rename compiles clean and the test
        // run breaks. One mention vetoes the candidate.
        let stringMentions =
            lazy
                (Array.append
                    (index.Exprs
                     |> Array.choose (fun (_, e) ->
                         match e with
                         | SynExpr.Const(SynConst.String(text = t), _) -> Some t
                         | _ -> None))
                    // ATTRIBUTE arguments are where these references live —
                    // [<TestCaseSource("...")>] — and they are not in Exprs
                    (index.Attributes |> Array.map (fun (_, a) -> textOfRange source a.ArgExpr.Range)))

        // a name sits inside one identifier run of a string, so the distinct
        // runs answer for every string at once
        let stringRuns =
            lazy
                (stringMentions.Value
                 |> Seq.collect (fun t -> identifierRun.Matches t |> Seq.map (fun m -> m.Value))
                 |> Seq.distinct
                 |> Array.ofSeq)

        let mentionedInString (name: string) =
            stringRuns.Value
            |> Array.exists (fun r -> r.Length >= name.Length && r.Contains name)

        // this file's typed uses by display name, read once: a symbol's uses
        // are the ones of its name that are effectively the same symbol
        let usesByName =
            lazy
                (check.GetAllUsesOfAllSymbolsInFile()
                 |> Seq.groupBy (fun u -> u.Symbol.DisplayName)
                 |> dict)

        let usesInFile (symbol: FSharp.Compiler.Symbols.FSharpSymbol) =
            match usesByName.Value.TryGetValue symbol.DisplayName with
            | true, uses ->
                uses
                |> Seq.filter (fun u -> u.Symbol.IsEffectivelySameAs symbol)
                |> Seq.distinctBy (fun u -> u.IsFromDefinition, u.Range)
                |> Array.ofSeq
            | _ -> check.GetUsesOfSymbolInFile symbol

        // the project's other files, for the "is it spelled elsewhere" question
        let otherFiles (thisFile: string) =
            try
                (OptionModule.projectContext check).ProjectOptions.SourceFiles
                |> Array.filter (fun f ->
                    not (String.Equals(Path.GetFullPath f, thisFile, StringComparison.OrdinalIgnoreCase)))
                |> Some
            with _ -> // no file list: every rename asks the project; fsharpanalyzer: ignore-line FR0055
                None

        let otherFilesOf = lazy (otherFiles (Path.GetFullPath parseTree.FileName))

        let spelledElsewhere (name: string) =
            match otherFilesOf.Value with
            | Some files -> files |> Array.exists (fun f -> fileSpells f name <> Some false)
            | None -> true

        let binderOf (p: SynPat) =
            match p with
            | SynPat.Named(ident = SynIdent(ident = pid); accessibility = acc) -> Some(pid, acc)
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ pid ]); accessibility = acc) -> Some(pid, acc)
            | _ -> None

        // (binder, quoted, mustProveInFile): local and file-private names
        // are in-file by scoping; a test-attributed public name must PROVE
        // its uses stay in this file through the project results
        let candidates =
            [ // module-level bindings: file-private, or test-attributed
                for path, decl in index.Decls do
                    match decl with
                    | SynModuleDecl.Let(
                        bindings = [ SynBinding(attributes = attrs; accessibility = acc; headPat = pat) ]) ->
                        match binderOf pat with
                        | Some(id, patAcc) ->
                            match quotedForm id.idText with
                            | Some quoted ->
                                let isTest =
                                    attrs
                                    |> List.collect (fun l -> l.Attributes)
                                    |> List.exists (fun a ->
                                        match a.TypeName with
                                        | SynLongIdent(id = ids) when not ids.IsEmpty ->
                                            let n = (List.last ids).idText
                                            testAttributes.Contains n || testAttributes.Contains(n + "Attribute")
                                        | _ -> false)

                                let filePrivate =
                                    (match acc with
                                     | Some(SynAccess.Private _) -> true
                                     | _ -> false)
                                    || (match patAcc with
                                        | Some(SynAccess.Private _) -> true
                                        | _ -> false)
                                    || path
                                       |> List.exists (fun node ->
                                           match node with
                                           | SyntaxNode.SynModule(SynModuleDecl.NestedModule(
                                               moduleInfo = SynComponentInfo(accessibility = Some(SynAccess.Private _)))) ->
                                               true
                                           | _ -> false)

                                if isTest then
                                    yield id, quoted, not filePrivate, filePrivate
                                elif filePrivate && includeLocals then
                                    yield id, quoted, false, true
                            | None -> ()
                        | None -> ()
                    | _ -> ()

                // local bindings: scope is the enclosing function
                for _, e in index.Exprs do
                    match e with
                    | LetOrUseE lou when includeLocals && not (lou.IsBang || lou.IsUse) ->
                        for SynBinding(headPat = pat) in lou.Bindings do
                            match binderOf pat with
                            | Some(id, _) ->
                                match quotedForm id.idText with
                                | Some quoted -> yield id, quoted, false, true
                                | None -> ()
                            | None -> ()
                    | _ -> ()
            ]

        // a quoted form is free only when no candidate of another name quotes
        // to it and the file spells no such name already: two names renamed
        // to one, or one onto an existing name, rebind each other's uses
        let quotedInFile =
            lazy (doubleBacktickTexts (source.GetSubTextString(0, source.Length)))

        let quotedFree =
            candidates
            |> List.groupBy (fun (_, quoted, _, _) -> quoted)
            |> List.filter (fun (quoted, group) ->
                (group
                 |> List.distinctBy (fun (pid: Ident, _, _, _) -> pid.idText)
                 |> List.length)
                    =
                    1
                && not (quotedInFile.Value.Contains quoted))
            |> List.map fst
            |> Set.ofList

        [
            for id, quoted, mustProveInFile, declaredPrivately in
                candidates |> List.filter (fun (_, quoted, _, _) -> quotedFree.Contains quoted) do
                match OptionModule.identUseAt check source id with
                | Some symbolUse ->
                    let thisFile = Path.GetFullPath(id.idRange.FileName).ToLowerInvariant()

                    let confinedToFile =
                        not (mentionedInString id.idText)
                        && (not mustProveInFile
                            || (match projectCheck with
                                | Some pc ->
                                    // Not an --api-changes rule: it renames only
                                    // where every use is in this file, and stands
                                    // down otherwise. But the PROOF has the same
                                    // blind spot the migrations do — a `#load`ing
                                    // script's call is in no project symbol table
                                    // and in no build check — so a use invisible
                                    // here would read as "confined" and leave the
                                    // script calling a name that no longer exists.
                                    // The script is not rewritten; the rename
                                    // simply stands down, which is this rule's own
                                    // answer to a use it cannot reach.
                                    // a use spells the name, so a project
                                    // whose other files never do has none
                                    // there: the project-wide query, a walk
                                    // of every file's uses, is asked only
                                    // when one does
                                    let projectUses =
                                        if spelledElsewhere id.idText then
                                            pc.GetUsesOfSymbol symbolUse.Symbol
                                        else
                                            [||]

                                    Array.append projectUses (ProjectSources.outsideUsesOf symbolUse.Symbol)
                                    |> Array.forall (fun u ->
                                        String.Equals(
                                            Path.GetFullPath u.Range.FileName,
                                            thisFile,
                                            StringComparison.OrdinalIgnoreCase
                                        ))
                                | None -> false))

                    if confinedToFile then
                        let uses = usesInFile symbolUse.Symbol

                        // every occurrence must be exactly the bare ident —
                        // a use range wider or narrower than the name means
                        // a spelling this rewrite does not understand
                        let editable =
                            uses
                            |> Array.forall (fun u ->
                                u.Range.StartLine = u.Range.EndLine && textOfRange source u.Range = id.idText)

                        if editable && uses.Length > 0 then
                            match SignatureFile.renameEdits declaredPrivately signature id.idText $"``{quoted}``" with
                            | ValueSome signatureEdits ->
                                {
                                    Range = id.idRange
                                    Name = id.idText
                                    Quoted = quoted
                                    Edits =
                                        ([ for u in uses -> u.Range, id.idText, $"``{quoted}``" ]
                                         |> List.distinctBy (fun (r, _, _) -> r.StartLine, r.StartColumn))
                                        @ signatureEdits
                                }
                            | ValueNone -> ()
                | None -> ()
        ]
