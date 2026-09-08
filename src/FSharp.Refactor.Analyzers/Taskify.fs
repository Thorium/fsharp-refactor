/// FR0049 (taskify fix): a FILE-PRIVATE synchronous function that drains a
/// task at its boundary becomes task-returning, and every caller — each
/// already inside a task/async CE — awaits it:
///
///     let private fetch (c: HttpClient) =            let private fetch (c: HttpClient) =
///         let t = c.GetStringAsync "u"                   task {
///         t.GetAwaiter().GetResult()          →              let t = c.GetStringAsync "u"
///                                                            return! t
///     task {                                             }
///         let s = fetch client                       task {
///         ...                                            let! s = fetch client
///                                                        ...
///
/// Sound-by-construction gates, all mandatory:
///   - the function is STRICTLY file-private (its own `private`, or a
///     private enclosing module): F# scoping then guarantees every use
///     lives in this file, so GetUsesOfSymbolInFile is authoritative and
///     the whole fix stays single-file — the editor can offer it too.
///     Under --api-changes in the CLI, effectively-INTERNAL definitions
///     widen to project-wide callers, each classified against its own
///     file's parse tree via ProjectSources; public stays out — callers
///     in sibling repositories are invisible to any scan.
///   - every blocking site in the body is either the RHS of a simple
///     `let x = <blocking>` statement (→ `let! x = receiver`) or a tail
///     terminal (→ `return! receiver`); every other tail terminal is
///     `return`-prefixed. A blocking site inside a lambda, try/with,
///     nested CE or any other shape vetoes the fix.
///   - every use is a FULL application forming the RHS of a simple `let`
///     (→ `let!`, with Async.AwaitTask in async) or a `return` payload
///     (→ `return!`), inside a task/async/backgroundTask CE, outside
///     lambdas, nested CEs and no-bind zones. One unconvertible caller
///     vetoes everything — the fix is all-or-nothing by suggestion group.
///   - no return-type annotation (it would need a Task<_> rewrite), not
///     inline, not mutual, no self-recursion.
module FSharp.Refactor.Taskify

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The function name's range — the message anchor.
        Range: range
        Name: string
        /// (range, original, replacement) — the whole rewrite: body wrap,
        /// bind conversions, and every call-site edit. All in this file.
        Edits: (range * string * string) list
    }

let private ceBuilders = set [ "async"; "task"; "backgroundTask" ]

let private isBlank (line: string) = System.String.IsNullOrWhiteSpace line

let private leadingSpaces (line: string) =
    line.Length - line.TrimStart(' ').Length

/// Wrap in parens unless a bare identifier path.
let private asArgument (text: string) =
    if System.Text.RegularExpressions.Regex.IsMatch(text, @"^[A-Za-z_][\w'.]*$") then
        text
    else
        $"({text})"

/// The application spine head and argument count.
[<TailCall>]
let rec private spine (count: int) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = _) -> spine (count + 1) f
    | head -> head, count

/// One file's async geography: its CEs, closure zones, no-bind zones and
/// statement owners — everything both the body transform and a call-site
/// classification need to know about a file.
let private geographyOf (parseTree: ParsedInput) (source: ISourceText) =
    let index = AstIndex.ofTree parseTree

    let ces =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                ceBuilders.Contains builder
                ->
                Some(builder, body.Range)
            | _ -> None)

    let lambdaRanges =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.Lambda _
            | SynExpr.MatchLambda _ -> Some e.Range
            | _ -> None)

    let ceRanges =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.ComputationExpr(expr = body) -> Some body.Range
            | SynExpr.ArrayOrListComputed(expr = body) -> Some body.Range
            | _ -> None)

    let noBindRanges =
        index.Exprs
        |> Array.collect (fun (_, e) ->
            match e with
            | SynExpr.TryFinally _
            | SynExpr.TryWith _ -> [| e.Range |]
            | _ -> [||])

    {| Index = index
       Ces = ces
       InnermostCe =
        fun (r: range) ->
            ces
            |> Array.filter (fun (_, ceRange) -> Range.rangeContainsRange ceRange r)
            |> Array.sortBy (fun (_, ceRange) -> ceRange.EndLine - ceRange.StartLine, ceRange.EndColumn)
            |> Array.tryHead
       LambdaRanges = lambdaRanges
       CeRanges = ceRanges
       NoBindRanges = noBindRanges
       InsideAny =
        fun (ranges: range[]) (r: range) ->
            ranges
            |> Array.exists (fun z -> Range.rangeContainsRange z r && not (Range.equals z r))
       LetBindingOwning =
        fun (target: range) ->
            index.Exprs
            |> Array.tryPick (fun (_, e) ->
                match e with
                | LetOrUseE lou when not (lou.IsBang || lou.IsUse || lou.IsRecursive) ->
                    match lou.Bindings with
                    | [ SynBinding(
                            isMutable = false
                            returnInfo = None
                            headPat = SynPat.Named _
                            expr = rhs
                            trivia = btrivia) ] when Range.equals rhs.Range target -> Some btrivia.LeadingKeyword.Range
                    | _ -> None
                | _ -> None)
       ReturnOwning =
        fun (target: range) ->
            index.Exprs
            |> Array.tryPick (fun (_, e) ->
                match e with
                | SynExpr.YieldOrReturn(flags = (false, true); expr = payload) when
                    Range.equals (stripParens payload).Range target
                    || Range.equals payload.Range target
                    ->
                    Some e.Range
                | _ -> None) |}

/// Per-file call-site classifier: is this use of an arity-N function a
/// bindable statement inside a task/async CE of THAT file, and what are
/// its edits once the function returns a task? None vetoes.
let private classifierFor (parseTree: ParsedInput) (source: ISourceText) =
    let geo = geographyOf parseTree source

    fun (arity: int) (useRange: range) ->
        // the full application this use heads
        let app =
            geo.Index.Exprs
            |> Array.choose (fun (_, e) ->
                let head, count = spine 0 e

                match head with
                | SynExpr.Ident _
                | SynExpr.LongIdent _ when Range.rangeContainsRange head.Range useRange && count = arity -> Some e
                | _ -> None)
            |> Array.sortBy (fun e -> e.Range.EndLine - e.Range.StartLine, e.Range.EndColumn - e.Range.StartColumn)
            |> Array.tryHead

        match app, geo.InnermostCe useRange with
        | Some app, Some(builder, ceRange) when
            // a lambda between the CE and the call is a closure — the
            // builder cannot bind there
            not (
                geo.LambdaRanges
                |> Array.exists (fun l -> Range.rangeContainsRange ceRange l && Range.rangeContainsRange l app.Range)
            )
            && not (
                geo.CeRanges
                |> Array.exists (fun other ->
                    Range.rangeContainsRange ceRange other
                    && not (Range.equals other ceRange)
                    && Range.rangeContainsRange other app.Range)
            )
            && not (geo.InsideAny geo.NoBindRanges app.Range)
            ->
            let appText = textOfRange source app.Range

            let awaited =
                if builder = "async" then
                    $"Async.AwaitTask {asArgument appText}"
                else
                    appText

            match geo.LetBindingOwning app.Range with
            | Some kw when textOfRange source kw = "let" ->
                Some(
                    (kw, "let", "let!")
                    :: (if builder = "async" then
                            [ app.Range, appText, awaited ]
                        else
                            [])
                )
            | _ ->
                match geo.ReturnOwning app.Range with
                | Some retRange -> Some [ retRange, textOfRange source retRange, $"return! {awaited}" ]
                | None -> None
        | _ -> None

let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    (projectCheck: FSharpCheckProjectResults option)
    : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the boundary blocking sites, typed-gated by FR0049 itself
        let boundarySites =
            SyncOverAsync.find parseTree source check
            |> List.filter (fun s ->
                s.Builder.IsNone
                && (match s.Kind with
                    | SyncOverAsync.BlockKind.TaskResult
                    | SyncOverAsync.BlockKind.AwaiterGetResult -> true
                    | _ -> false))

        if boundarySites.IsEmpty then
            []
        else
            // shared geography of the file, SyncOverAsync-style
            let geo = geographyOf parseTree source
            let insideAny = geo.InsideAny
            let lambdaRanges = geo.LambdaRanges
            let ceRanges = geo.CeRanges
            let noBindRanges = geo.NoBindRanges
            let letBindingOwning = geo.LetBindingOwning
            let classifyThisFile = classifierFor parseTree source

            [ for declPath, decl in index.Decls do
                  match decl with
                  | SynModuleDecl.Let(isRecursive = false; bindings = [ binding ]) ->
                      match binding with
                      | SynBinding(
                          accessibility = access
                          isInline = false
                          isMutable = false
                          returnInfo = None
                          headPat = SynPat.LongIdent(
                              longDotId = SynLongIdent(id = [ fid ])
                              argPats = SynArgPats.Pats pats
                              accessibility = patAccess)
                          expr = body
                          trivia = trivia) when not pats.IsEmpty ->
                          // strictly file-private: its own modifier or a
                          // private enclosing module
                          let isFilePrivate =
                              (match access with
                               | Some(SynAccess.Private _) -> true
                               | _ -> false)
                              || (match patAccess with
                                  | Some(SynAccess.Private _) -> true
                                  | _ -> false)
                              || declPath
                                 |> List.exists (fun node ->
                                     match node with
                                     | SyntaxNode.SynModule(SynModuleDecl.NestedModule(
                                         moduleInfo = SynComponentInfo(accessibility = Some(SynAccess.Private _)))) ->
                                         true
                                     | _ -> false)

                          let sitesInBody =
                              boundarySites
                              |> List.filter (fun s -> Range.rangeContainsRange body.Range s.Range)

                          // internal (or effectively-internal) definitions
                          // widen to project-wide callers under
                          // --api-changes — public stays out: callers in a
                          // sibling repository are invisible to the scan
                          let assemblyScope =
                              not isFilePrivate
                              && Visibility.apiChangesAllowed ()
                              && ProjectSources.available ()
                              // InternalsVisibleTo makes "internal ⇒ every
                              // caller is in this project" false — a friend
                              // assembly's call sites are invisible to the
                              // scan AND to the verification build
                              && (projectCheck |> Option.exists (ProjectSources.hasInternalsVisibleTo >> not))
                              // and neither is a file #loaded by a script we
                              // could not read
                              && not (ProjectSources.isUnreadable parseTree.FileName)
                              && Visibility.scopeMatches
                                  Visibility.Scope.Assembly
                                  declPath
                                  (match patAccess with
                                   | Some a -> Some a
                                   | None -> access)

                          if
                              (isFilePrivate || assemblyScope)
                              && not sitesInBody.IsEmpty
                              // a body choreographed around a thread (a
                              // signal, a Thread, Interlocked) continues on
                              // the thread it waited on; task-returning it
                              // would not — the same refusal as FR0142's
                              && not (BlockingSites.threadBound source body)
                              && sitesInBody |> List.forall (fun s -> s.Receiver.IsSome)
                              // a blocking site under a lambda or inside a
                              // try/with survives the wrap unconverted
                              && sitesInBody
                                 |> List.forall (fun s ->
                                     not (insideAny lambdaRanges s.Range)
                                     && not (insideAny ceRanges s.Range)
                                     && not (insideAny noBindRanges s.Range))
                              // body on its own line(s) below the `let` line
                              && body.Range.StartLine > trivia.LeadingKeyword.Range.StartLine
                              && (source.GetLineString(body.Range.StartLine - 1))
                                  .Substring(0, body.Range.StartColumn)
                                  .Trim() = ""
                          then
                              // ---- the body rewrite ----
                              // classify every blocking site: let-RHS or tail
                              // terminal; walk the tails, prefixing `return `
                              let siteAt (r: range) =
                                  sitesInBody |> List.tryFind (fun s -> Range.equals s.Range r)

                              let bindEdits = ResizeArray<range * string * string>()
                              let mutable convertible = true
                              let coveredSites = System.Collections.Generic.HashSet<string>()

                              let keyOf (r: range) = $"{r.StartLine}:{r.StartColumn}"

                              let rec walkTails (e: SynExpr) =
                                  match e with
                                  | SynExpr.Paren(expr = inner) -> walkTails inner
                                  | SynExpr.Match(clauses = cs) ->
                                      cs |> List.iter (fun (SynMatchClause(resultExpr = r)) -> walkTails r)
                                  | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some e2) ->
                                      walkTails t
                                      walkTails e2
                                  | SynExpr.IfThenElse(elseExpr = None) ->
                                      // one-armed if: no expression tail to return
                                      convertible <- false
                                  | LetOrUseE lou when not lou.IsBang -> walkTails lou.Body
                                  | SynExpr.Sequential(expr2 = e2) -> walkTails e2
                                  // statement-shaped tails cannot take a
                                  // `return ` prefix — `return while ...` and
                                  // `return x <- 1` do not parse
                                  | SynExpr.TryWith _
                                  | SynExpr.TryFinally _
                                  | SynExpr.While _
                                  | SynExpr.For _
                                  | SynExpr.ForEach _
                                  | SynExpr.Do _
                                  | SynExpr.LongIdentSet _
                                  | SynExpr.Set _
                                  | SynExpr.DotSet _
                                  | SynExpr.DotIndexedSet _ -> convertible <- false
                                  | terminal ->
                                      match siteAt terminal.Range with
                                      | Some site ->
                                          // the tail IS the blocking drain
                                          let recv = textOfRange source site.Receiver.Value
                                          coveredSites.Add(keyOf site.Range) |> ignore

                                          bindEdits.Add(
                                              terminal.Range,
                                              textOfRange source terminal.Range,
                                              $"return! {recv}"
                                          )
                                      | None ->
                                          // any other tail returns its value;
                                          // a try/with or lambda tail hiding a
                                          // blocking site was vetoed above
                                          let at =
                                              Range.mkRange
                                                  terminal.Range.FileName
                                                  terminal.Range.Start
                                                  terminal.Range.Start

                                          bindEdits.Add(at, "", "return ")

                              walkTails body

                              // non-tail blocking sites must each be a simple
                              // let RHS: `let r = t.Result` → `let! r = t`
                              for site in sitesInBody do
                                  if convertible && not (coveredSites.Contains(keyOf site.Range)) then
                                      match letBindingOwning site.Range with
                                      | Some kw when
                                          textOfRange source kw = "let" && Range.rangeContainsRange body.Range kw
                                          ->
                                          let recv = textOfRange source site.Receiver.Value
                                          bindEdits.Add(kw, "let", "let!")
                                          bindEdits.Add(site.Range, textOfRange source site.Range, recv)
                                      | _ -> convertible <- false

                              // ---- the wrap ----
                              let bodyIndent = body.Range.StartColumn
                              let indentText = System.String(' ', bodyIndent)

                              let bodyLines =
                                  [ body.Range.StartLine .. body.Range.EndLine ]
                                  |> List.map (fun l -> source.GetLineString(l - 1))

                              let wrappable =
                                  bodyLines
                                  |> List.forall (fun l -> not ((l.Contains "\"\"\"") || (l.Contains "@\"")))
                                  // a PLAIN literal can span lines too; the
                                  // indent would splice spaces into its text
                                  && not (
                                      geo.Index.Exprs
                                      |> Array.exists (fun (_, e) ->
                                          (match e with
                                           | SynExpr.Const(SynConst.String _, _)
                                           | SynExpr.InterpolatedString _ -> true
                                           | _ -> false)
                                          && e.Range.StartLine < e.Range.EndLine
                                          && e.Range.StartLine <= body.Range.EndLine
                                          && e.Range.EndLine >= body.Range.StartLine)
                                  )

                              // ---- the call sites ----
                              let arity = pats.Length

                              let useEdits = ResizeArray<range * string * string>()

                              let thisFile = System.IO.Path.GetFullPath(fid.idRange.FileName).ToLowerInvariant()

                              let siblingClassifiers =
                                  System.Collections.Generic.Dictionary<
                                      string,
                                      (int -> range -> (range * string * string) list option) option
                                   >()

                              let classifierForFile (path: string) =
                                  let key = System.IO.Path.GetFullPath(path).ToLowerInvariant()

                                  if key = thisFile then
                                      Some classifyThisFile
                                  else
                                      match siblingClassifiers.TryGetValue key with
                                      | true, c -> c
                                      | _ ->
                                          let c =
                                              ProjectSources.tryParse path
                                              |> Option.map (fun (tree, src) -> classifierFor tree src)

                                          siblingClassifiers.[key] <- c
                                          c

                              let usesOk =
                                  let lineText = source.GetLineString(fid.idRange.EndLine - 1)

                                  match
                                      check.GetSymbolUseAtLocation(
                                          fid.idRange.EndLine,
                                          fid.idRange.EndColumn,
                                          lineText,
                                          [ fid.idText ]
                                      )
                                  with
                                  | None -> false
                                  | Some symbolUse ->
                                      let uses =
                                          if isFilePrivate then
                                              check.GetUsesOfSymbolInFile symbolUse.Symbol
                                              |> Seq.filter (fun u -> not u.IsFromDefinition)
                                              |> Seq.toList
                                          else
                                              match projectCheck with
                                              | Some pc ->
                                                  // a `#load`ing script calls this
                                                  // definition from outside the
                                                  // compilation, and no build check
                                                  // covers it — see ProjectSources
                                                  Array.append
                                                      (pc.GetUsesOfSymbol symbolUse.Symbol)
                                                      (ProjectSources.outsideUsesOf symbolUse.Symbol)
                                                  |> Seq.filter (fun u -> not u.IsFromDefinition)
                                                  |> Seq.toList
                                              | None -> []

                                      not uses.IsEmpty
                                      && uses
                                         |> List.forall (fun u ->
                                             // no self-recursion
                                             if
                                                 System.IO.Path.GetFullPath(u.Range.FileName).ToLowerInvariant() = thisFile
                                                 && Range.rangeContainsRange binding.RangeOfBindingWithRhs u.Range
                                             then
                                                 false
                                             else
                                                 match classifierForFile u.Range.FileName with
                                                 | Some classify ->
                                                     match classify arity u.Range with
                                                     | Some edits ->
                                                         useEdits.AddRange edits
                                                         true
                                                     | None -> false
                                                 | None -> false)

                              if convertible && wrappable && usesOk then
                                  let wrapEdits =
                                      [ // one edit per line start: the first
                                        // carries the `task {` line too, so no
                                        // two edits share a position
                                        for l in body.Range.StartLine .. body.Range.EndLine do
                                            let text = source.GetLineString(l - 1)

                                            let opening =
                                                if l = body.Range.StartLine then
                                                    $"{indentText}task {{\n"
                                                else
                                                    ""

                                            if l = body.Range.StartLine || not (isBlank text) then
                                                let at =
                                                    Range.mkRange
                                                        body.Range.FileName
                                                        (Position.mkPos l 0)
                                                        (Position.mkPos l 0)

                                                at, "", (opening + (if isBlank text then "" else "    "))
                                        // closing brace below the body
                                        let atEnd = Range.mkRange body.Range.FileName body.Range.End body.Range.End
                                        atEnd, "", $"\n{indentText}}}" ]

                                  { Range = fid.idRange
                                    Name = fid.idText
                                    Edits =
                                      wrapEdits
                                      @ (bindEdits |> Seq.map (fun (r, o, n) -> r, o, n) |> List.ofSeq)
                                      @ (useEdits |> Seq.map (fun (r, o, n) -> r, o, n) |> List.ofSeq) }
                      | _ -> ()
                  | _ -> () ]
