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
        [ "Test"
          "Fact"
          "Theory"
          "TestMethod"
          "Property"
          "TestCase"
          "TestCaseSource" ]

/// The double-backtick spelling, when the name earns one: five or more
/// words, plain camel/snake, no acronym runs.
let quotedForm (name: string) : string option =
    if
        Regex.IsMatch(name, "[A-Z]{2}")
        || not (Regex.IsMatch(name, @"^[A-Za-z][A-Za-z0-9_]*$"))
    then
        None
    else
        let words =
            name.Split '_'
            |> Array.collect (fun part -> Regex.Split(part, "(?=[A-Z])"))
            |> Array.filter (fun s -> s <> "")

        if words.Length > 4 then
            Some(words |> Array.map (fun w -> w.ToLowerInvariant()) |> String.concat " ")
        else
            None

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

        let mentionedInString (name: string) =
            stringMentions.Value |> Array.exists (fun t -> t.Contains name)

        let binderOf (p: SynPat) =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id); accessibility = acc) -> Some(id, acc)
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); accessibility = acc) -> Some(id, acc)
            | _ -> None

        // (binder, quoted, mustProveInFile): local and file-private names
        // are in-file by scoping; a test-attributed public name must PROVE
        // its uses stay in this file through the project results
        let candidates =
            [ // module-level bindings: file-private, or test-attributed
              for path, decl in index.Decls do
                  match decl with
                  | SynModuleDecl.Let(bindings = [ SynBinding(attributes = attrs; accessibility = acc; headPat = pat) ]) ->
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
                  | _ -> () ]

        [ for id, quoted, mustProveInFile, declaredPrivately in candidates do
              let lineText = source.GetLineString(id.idRange.EndLine - 1)

              match check.GetSymbolUseAtLocation(id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ]) with
              | Some symbolUse ->
                  let thisFile = System.IO.Path.GetFullPath(id.idRange.FileName).ToLowerInvariant()

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
                                  Array.append
                                      (pc.GetUsesOfSymbol symbolUse.Symbol)
                                      (ProjectSources.outsideUsesOf symbolUse.Symbol)
                                  |> Array.forall (fun u ->
                                      System.IO.Path.GetFullPath(u.Range.FileName).ToLowerInvariant() = thisFile)
                              | None -> false))

                  if confinedToFile then
                      let uses = check.GetUsesOfSymbolInFile symbolUse.Symbol

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
                              { Range = id.idRange
                                Name = id.idText
                                Quoted = quoted
                                Edits =
                                  ([ for u in uses -> u.Range, id.idText, $"``{quoted}``" ]
                                   |> List.distinctBy (fun (r, _, _) -> r.StartLine, r.StartColumn))
                                  @ signatureEdits }
                          | ValueNone -> ()
              | None -> () ]
