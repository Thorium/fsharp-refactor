/// Refactoring note (portability): concatenating path fragments with a
/// hard-coded separator builds the path by hand.
///
///     dir + "\\" + file          // wrong separator off Windows
///     root + "/" + sub + "/" + f
///         →  Path.Combine(dir, file) handles separators, duplicates,
///            and platform differences
///
/// Advice only, deliberately:
///   - Path.Combine treats a ROOTED second argument as absolute (the
///     first is discarded) — the concatenation does not, so the rewrite
///     is not universally identical
///   - a URL is not a file path: forward-slash joins on anything smelling
///     of URLs (url/uri/http/route/endpoint/link/href, or a literal
///     containing "://") never fire, since Path.Combine would produce
///     backslashes on Windows
module FSharp.Refactor.PathSeparator

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// "/" or "\\", for the message.
        Separator: string
    }

/// Left-to-right operands of a `+` chain.
[<TailCall>]
let rec private plusOperandsLoop (acc: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
        op.idText = "op_Addition"
        ->
        plusOperandsLoop (rhs :: acc) lhs
    | leaf -> leaf :: acc

/// Names that say the slash-joined thing is NOT a filesystem path: web
/// addresses, and document pointers (`doc.Path() + "/" + name` in a JSON
/// runtime is a JSON pointer, spelled with forward slashes by definition).
let private urlSmell =
    Regex(
        @"(?i)url|uri|http|link|route|endpoint|href|slug|query|(?<!\.)\b(json|xml|xpath|html|pointer)",
        RegexOptions.Compiled
    )

/// Positive path evidence, required for forward-slash joins ('\' is
/// path-ish on its own): path-flavored identifiers, the classic directory
/// sources (__SOURCE_DIRECTORY__, Environment.CurrentDirectory, assembly
/// locations, AppContext.BaseDirectory), a rooted or extension-bearing
/// literal — or a literal that actually EXISTS on this machine, the
/// strongest signal there is.
let private pathSmell =
    Regex(
        @"(?i)path|dir|file|folder|root|temp|home|cache|log|__SOURCE_DIRECTORY__|CurrentDirectory|BaseDirectory|GetEntryAssembly|GetExecutingAssembly|\.Location",
        RegexOptions.Compiled
    )

let private rootedLiteral =
    Regex(@"^([A-Za-z]:[\\/]|\\\\|~[\\/]|\.{1,2}[\\/])", RegexOptions.Compiled)

let private extensionLiteral = Regex(@"\.\w{1,5}$", RegexOptions.Compiled)

/// A filesystem API in the function position of an operand: the only
/// path evidence a CALL operand can give. `textOfPath (List.map fst path)`
/// beside `getNameOfScopeRef scoref` builds the compiler's mangled
/// compilation path, and "path" in a function's name is not a directory.
let private fileApi =
    Regex(
        @"\b(Path|File|Directory|FileInfo|DirectoryInfo|Environment|AppContext|AppDomain|Assembly)\.|__SOURCE_DIRECTORY__|CurrentDirectory|BaseDirectory|GetEntryAssembly|GetExecutingAssembly|\.Location\b",
        RegexOptions.Compiled
    )

let private bindsName (name: string) (SynBinding(headPat = p)) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = name
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) -> id.idText = name
    | _ -> false

/// `./`, `../`, `../../` — relative-path notation, not a separator.
let private dotSegments = Regex(@"^[/\\]?(\.{1,2}[/\\])+$", RegexOptions.Compiled)

let private existsOnDisk (text: string) =
    try
        rootedLiteral.IsMatch text
        && (System.IO.Directory.Exists text || System.IO.File.Exists text)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// A string literal that is a separator or starts/ends with one.
let private separatorOf (text: string) =
    if text = "/" || text.StartsWith '/' || text.EndsWith '/' then
        Some "/"
    elif text = "\\" || text.StartsWith '\\' || text.EndsWith '\\' then
        Some "\\"
    else
        None

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // contexts that must stay COMPILE-TIME literals — Path.Combine is a
    // function call and cannot appear there: [<Literal>] binding bodies,
    // attribute arguments, and type-provider static arguments
    let literalOnlyRanges =
        [ for _, decl in index.Decls do
              match decl with
              | SynModuleDecl.Let(bindings = bindings) ->
                  for SynBinding(attributes = attrs; expr = body) in bindings do
                      if hasAttributeNamed "Literal" attrs then
                          yield body.Range
              | _ -> ()
          for _, attr in index.Attributes -> attr.ArgExpr.Range ]

    let mustStayLiteral (path: SyntaxNode list) (r: range) =
        literalOnlyRanges |> List.exists (fun lr -> Range.rangeContainsRange lr r)
        || path
           |> List.exists (fun node ->
               match node with
               | SyntaxNode.SynType _ -> true // a type-provider static arg
               | _ -> false)

    // an identifier's right-hand side, one hop: the nearest enclosing
    // `let x = ...` on the path, else a module-level `let x = ...` of this
    // file — `gitHome + "/" + gitName + ".git"` is a URL because `gitHome`
    // was bound to `"https://github.com/" + gitOwner` fifty lines up
    // (every FAKE build script of a certain vintage)
    let definitionOf (path: SyntaxNode list) (name: string) =
        let ofBindings (bindings: SynBinding list) =
            bindings
            |> List.tryPick (fun b ->
                if bindsName name b then
                    let (SynBinding(expr = rhs)) = b
                    Some rhs
                else
                    None)

        let local =
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynExpr(LetOrUseE lou) -> ofBindings lou.Bindings
                | _ -> None)

        match local with
        | Some rhs -> Some rhs
        | None ->
            index.Decls
            |> Array.tryPick (fun (_, decl) ->
                match decl with
                | SynModuleDecl.Let(bindings = bindings) -> ofBindings bindings
                | _ -> None)

    // a chain compared or searched for — `"content/" + n.file = page`
    // (fsharplint's docs generator) — is a key, not a path to build
    let isCompared (path: SyntaxNode list) =
        let comparison (op: SynExpr) =
            match op with
            | SingleIdent id ->
                (match id.idText with
                 | "op_Equality"
                 | "op_Inequality" -> true
                 | _ -> false)
            | _ -> false

        let searched (f: SynExpr) =
            match f with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                (match (List.last ids).idText with
                 | "Contains"
                 | "ContainsKey"
                 | "StartsWith"
                 | "EndsWith"
                 | "Equals" -> true
                 | _ -> false)
            | _ -> false

        match path with
        // the left operand: App(isInfix, op, chain)
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op)) :: _ when comparison op -> true
        // the right operand: App(App(isInfix, op, lhs), chain)
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = op))) :: _ when comparison op ->
            true
        // `set.Contains(chain)` / `s.Contains chain`
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f)) :: _ when searched f -> true
        | SyntaxNode.SynExpr(SynExpr.Paren _) :: SyntaxNode.SynExpr(SynExpr.App(funcExpr = f)) :: _ when searched f ->
            true
        | _ -> false

    [ for path, expr in index.Exprs do
          match expr with
          | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = _); argExpr = _) when
              op.idText = "op_Addition"
              && isSingleLine expr.Range
              // outermost chain node only
              && (match path with
                  | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Addition"))) :: _
                  | SyntaxNode.SynExpr(SynExpr.App(funcExpr = IdentName "op_Addition")) :: _ -> false
                  | _ -> true)
              ->
              let operands = plusOperandsLoop [] expr

              let literalTexts =
                  operands
                  |> List.choose (fun o ->
                      match o with
                      | SynExpr.Const(SynConst.String(text, _, _), _) -> Some text
                      | _ -> None)

              // A separator only JOINS when the chain has something on both
              // sides of it. `Path.GetFileName d + "/"` appends a trailing
              // marker and `"/" + name` prefixes a root — neither is a
              // Path.Combine, and Path.Combine cannot even express the
              // first. An inner literal always joins; an outer one has to
              // carry text on the far side of its separator, so
              // `dir + "/file.txt"` still counts and `dir + "/"` does not.
              let separators =
                  let total = List.length operands

                  operands
                  |> List.indexed
                  |> List.choose (fun (i, o) ->
                      match o with
                      // `"./" + path` and `prefix + "../"` prepend or
                      // append dot-segments: relative-path notation, which
                      // Path.Combine cannot spell — not a join
                      | SynExpr.Const(SynConst.String(text, _, _), _) when dotSegments.IsMatch text -> None
                      | SynExpr.Const(SynConst.String(text, _, _), _) ->
                          separatorOf text
                          |> Option.filter (fun sep ->
                              let sepChar = sep.[0]

                              if i > 0 && i < total - 1 then true
                              elif i = total - 1 then text.TrimEnd sepChar <> ""
                              else text.TrimStart sepChar <> "")
                      | _ -> None)
                  |> List.distinct

              // an inner separator literal joining non-literal parts,
              // nothing URL-ish anywhere in the chain
              let smellsOfUrl =
                  literalTexts |> List.exists (fun t -> t.Contains "://")
                  || urlSmell.IsMatch(textOfRange source expr.Range)
                  // the file's own name says what kind of path it builds:
                  // JsonRuntime.fs joins JSON pointers, not directories
                  || urlSmell.IsMatch(System.IO.Path.GetFileName expr.Range.FileName)
                  // a name bound one hop away to something URL-shaped
                  || operands
                     |> List.exists (fun o ->
                         match o with
                         | SynExpr.Ident id ->
                             definitionOf path id.idText
                             |> Option.exists (fun rhs ->
                                 let rhsText = textOfRange source rhs.Range
                                 rhsText.Contains "://" || urlSmell.IsMatch rhsText)
                         | _ -> false)

              let hasNonLiteralPart =
                  operands
                  |> List.exists (fun o ->
                      match o with
                      // __SOURCE_DIRECTORY__ parses as a Const, but it IS
                      // the joined-onto directory
                      | SynExpr.Const(SynConst.SourceIdentifier _, _) -> true
                      | SynExpr.Const _ -> false
                      | _ -> true)

              // BOTH separators need positive evidence. A lone backslash
              // used to read as path-ish on its own, but a corpus run over
              // FsAutoComplete showed where that goes wrong: escape-sequence
              // building (`result <- result + "\\" + string c`) is full of
              // backslash literals and has nothing to do with paths.
              // Evidence is path-flavored names, a rooted or
              // extension-bearing literal, or a literal existing on disk.
              // evidence that this is a FILESYSTEM path, not just something
              // path-shaped: a rooted or extension-bearing literal, or one
              // that actually exists on this machine
              let hasStrongEvidence =
                  literalTexts
                  |> List.exists (fun t -> rootedLiteral.IsMatch t || extensionLiteral.IsMatch t || existsOnDisk t)

              // A chain opening with a forward-slash literal is as likely a
              // URL path as a filesystem one — `"/img/userimages/" + fileId`
              // is a web route, and Path.Combine would turn it into
              // backslashes. A path-flavored NAME is too weak to tell those
              // apart (`fileId` matches "file"), so the leading-slash case
              // wants the stronger evidence.
              let opensWithSlashLiteral =
                  match operands with
                  | SynExpr.Const(SynConst.String(text, _, _), _) :: _ -> text.StartsWith '/'
                  | _ -> false

              // evidence is read per OPERAND: a name or property chain
              // (`rootDir`, `fi.FullName`) by its spelling, a call only by
              // the filesystem API it invokes — `textOfPath xs` names a
              // function, not a directory
              let operandEvidence (o: SynExpr) =
                  match stripParens o with
                  | SynExpr.Const(SynConst.SourceIdentifier _, _) -> true
                  | SynExpr.Const _ -> false
                  | SynExpr.App _
                  | SynExpr.New _ -> fileApi.IsMatch(textOfRange source o.Range)
                  | other -> pathSmell.IsMatch(textOfRange source other.Range)

              let hasPathEvidence (_separator: string) =
                  if opensWithSlashLiteral then
                      hasStrongEvidence
                  else
                      operands |> List.exists operandEvidence || hasStrongEvidence

              match separators with
              | [ separator ] when
                  hasNonLiteralPart
                  && not smellsOfUrl
                  && not (isCompared path)
                  && hasPathEvidence separator
                  && not (mustStayLiteral path expr.Range)
                  ->
                  { Range = expr.Range
                    Separator = separator }
              | _ -> ()
          | _ -> () ]
