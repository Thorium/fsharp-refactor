/// Idiom: a match arm that binds a whole list only to index its first
/// element (or its first two, or take its tail) is a cons pattern.
///
///     match xs with
///     | [] -> f ()
///     | itms -> g itms.[0]
///
///     match xs with
///     | [] -> f ()
///     | itmsHead :: _ -> g itmsHead
///
/// `itms.[0]`, `itms[0]`, `itms.Head`, `List.head itms` (and `itms |> …`)
/// all become the head name; `.[1]` / `List.item 1` the second; `.Tail` /
/// `List.tail` the tail, which stays `_` when nothing reads it. The arm's
/// only uses of the name must be those; a `.Length`, an `IsEmpty`, a
/// higher index, or the list passed on whole leaves the arm alone — the
/// pattern would then name a head the arm does not need and the list
/// would still have to be bound.
///
/// Measured: no run-time difference (both shapes 2-7 ns, 0 B, within
/// noise across runs). `xs.[0]` on a list is `List.nth` walking zero
/// cells, so the point is not speed; it is that the pattern states the
/// shape the arm relies on, and the compiler's exhaustiveness check takes
/// over from the `ArgumentException` `Item` raises on a list that turned
/// out shorter.
///
/// Exactness is that check: `| itms -> itms.[0]` on an EMPTY list throws,
/// `| h :: _ -> h` would fall through (FS0025, MatchFailureException), so
/// the arm must already be unreachable for the short lists. An earlier
/// unguarded `[]` arm (or `[] | [_]`, `x :: []`, …) proves length 0 out;
/// `[1]` additionally needs length 1 out. The proof also settles the
/// type: `[]` matches an F# list and nothing else, so no check results
/// are needed — `[||]` is an array, and an array arm never qualifies
/// (arrays index in O(1) and have no head/rest pattern). It must be a
/// list-shaped pattern for exactly that reason: an earlier `| _ ->` or
/// `| name ->` covers every length, but it covers every array, string and
/// union with it, and the cons pattern it would license over an array does
/// not compile (the arm is dead code the compiler already warns about).
///
/// A rebinding of the name inside the arm — a lambda parameter, a `let`,
/// a nested arm, a loop variable — stands the rule down: the indexed
/// value would then be another list. So does a file that declares a
/// `List` module of its own, since this rule reads `List.head` by name
/// with nothing to resolve; `itms.head` lowercase is somebody's extension
/// member, not the list's `Head`.
module FSharp.Refactor.ListHeadPattern

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole clause: pattern through result.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The name the arm bound the list to.
        Name: string
        /// The cons pattern that replaces it.
        Pattern: string
    }

[<RequireQualifiedAccess>]
type private Part =
    | Head
    | Second
    | Tail

[<return: Struct>]
let private (|IntLiteral|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Const(SynConst.Int32 n, _) -> ValueSome n
    | _ -> ValueNone

let private partOfIndex (k: int) =
    match k with
    | 0 -> ValueSome Part.Head
    | 1 -> ValueSome Part.Second
    | _ -> ValueNone

/// `List.head` / `List.tail`, whose module name the caller has checked.
let private partOfFunction (f: string) =
    match f with
    | "head" -> ValueSome Part.Head
    | "tail" -> ValueSome Part.Tail
    | _ -> ValueNone

/// The list's own properties. Only the capitalised spellings: `itms.head`
/// on a list is an extension member somebody wrote, not `List.head`.
let private partOfProperty (m: string) =
    match m with
    | "Head" -> ValueSome Part.Head
    | "Tail" -> ValueSome Part.Tail
    | _ -> ValueNone

/// A pattern that matches every value: binds or ignores, never tests.
let rec private irrefutable (p: SynPat) =
    match p with
    | SynPat.Wild _
    | SynPat.Named _ -> true
    | SynPat.Paren(pat = inner)
    | SynPat.Typed(pat = inner)
    | SynPat.Attrib(pat = inner) -> irrefutable inner
    | SynPat.As(lhsPat = l; rhsPat = r) -> irrefutable l && irrefutable r
    | SynPat.Tuple(elementPats = ps) -> ps |> List.forall irrefutable
    | _ -> false

/// Does the pattern match every LIST of exactly `n` elements? A bare `_`
/// or a name matches every length, but it also matches every array, string
/// and union: the arm that proves the short lists out is the arm that
/// proves the type, so only a list-shaped pattern counts here. (An earlier
/// catch-all makes this arm dead code the compiler already warns about,
/// and rewriting it to a cons pattern over an array would not compile.)
let rec private coversLength (n: int) (p: SynPat) =
    match p with
    | SynPat.Paren(pat = inner)
    | SynPat.Typed(pat = inner)
    | SynPat.Attrib(pat = inner) -> coversLength n inner
    | SynPat.ArrayOrList(isArray = false; elementPats = ps) -> ps.Length = n && ps |> List.forall irrefutable
    | SynPat.ListCons(lhsPat = l; rhsPat = r) -> n >= 1 && irrefutable l && coversLength (n - 1) r
    | SynPat.Or(lhsPat = l; rhsPat = r) -> coversLength n l || coversLength n r
    | SynPat.As(lhsPat = l; rhsPat = r) -> coversLength n l || coversLength n r
    | _ -> false

/// The clauses of any match form, with the range the fix spans.
[<return: Struct>]
let private (|Clauses|_|) (e: SynExpr) =
    match e with
    | SynExpr.Match(clauses = cs)
    | SynExpr.MatchBang(clauses = cs)
    | SynExpr.MatchLambda(matchClauses = cs) -> ValueSome cs
    | _ -> ValueNone

let private listModule (core: bool) (m: Ident) (f: Ident) (names: string list) =
    core && m.idText = "List" && List.contains f.idText names

/// Offset of a position inside the text `textOfRange` yields for `outer`
/// (lines joined by a single `\n`).
let private offsetIn (source: ISourceText) (outer: range) (p: pos) =
    let mutable offset = 0

    for line in outer.StartLine .. p.Line - 1 do
        let lineLength = source.GetLineString(line - 1).Length

        offset <-
            offset
            + (if line = outer.StartLine then
                   lineLength - outer.StartColumn
               else
                   lineLength)
            + 1

    offset
    + (if p.Line = outer.StartLine then
           p.Column - outer.StartColumn
       else
           p.Column)

/// Does this file declare a `List` module of its own? `List.head itms`
/// is read by name — this rule is parse-only, with no symbol to resolve —
/// and a shadowing module would make it another function entirely.
let private shadowsListModule (index: AstIndex.Index) =
    index.Decls
    |> Array.exists (fun (_, decl) ->
        match decl with
        | SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = ids)) ->
            ids |> List.exists (fun id -> id.idText = "List")
        | _ -> false)

let private freshNames (full: string) (baseNames: string list) =
    let taken (candidate: string) =
        Regex.IsMatch(full, identifierPattern candidate)

    baseNames
    |> List.map (fun baseName ->
        [ baseName; baseName + "2"; baseName + "3" ]
        |> List.tryFind (fun candidate -> not (taken candidate))
        |> Option.defaultValue baseName)

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let within (outer: range) (r: range) = Range.rangeContainsRange outer r

    // one scan of the file for the names already in it, however many arms
    // qualify
    let fileText =
        lazy (String.concat "\n" [ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ])

    let coreList = not (shadowsListModule index)

    [
        for _, expr in index.Exprs do
            match expr with
            | Clauses clauses ->
                let clauses = List.toArray clauses

                for i in 0 .. clauses.Length - 1 do
                    match clauses.[i] with
                    | SynMatchClause(pat = SynPat.Named(ident = SynIdent(ident = name); isThisVal = false) as pat) as clause ->
                        let clauseRange = clause.Range
                        let nameText = name.idText

                        // an earlier unguarded arm covering each short length
                        let excluded (n: int) =
                            clauses
                            |> Seq.take i
                            |> Seq.exists (fun (SynMatchClause(pat = p; whenExpr = guard)) ->
                                guard.IsNone && coversLength n p)

                        if excluded 0 then
                            let inClause =
                                index.Exprs
                                |> Array.filter (fun (_, e) -> within clauseRange e.Range)
                                |> Array.map snd

                            // every spelling of the name in the arm: an
                            // Ident, or a dotted path starting with it
                            let occurrences =
                                inClause
                                |> Array.choose (fun e ->
                                    match e with
                                    | SynExpr.Ident id when id.idText = nameText -> Some e.Range
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) when
                                        first.idText = nameText
                                        ->
                                        Some e.Range
                                    | _ -> None)

                            // (part, range replaced, occurrence it accounts for)
                            let useOf (e: SynExpr) =
                                match e with
                                | SynExpr.DotIndexedGet(objectExpr = SynExpr.Ident id as o; indexArgs = IntLiteral k) when
                                    id.idText = nameText
                                    ->
                                    partOfIndex k |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | SynExpr.App(
                                    flag = ExprAtomicFlag.Atomic
                                    funcExpr = SynExpr.Ident id as o
                                    argExpr = SynExpr.ArrayOrListComputed(isArray = false; expr = IntLiteral k)) when
                                    id.idText = nameText
                                    ->
                                    partOfIndex k |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: m :: _)) when
                                    first.idText = nameText
                                    ->
                                    partOfProperty m.idText
                                    |> ValueOption.map (fun part ->
                                        part, Range.unionRanges first.idRange m.idRange, e.Range)
                                | SynExpr.App(
                                    funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                                    argExpr = SynExpr.Ident id as o) when
                                    id.idText = nameText && listModule coreList m f [ "head"; "tail" ]
                                    ->
                                    partOfFunction f.idText |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | SynExpr.App(
                                    funcExpr = SynExpr.App(
                                        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                                        argExpr = IntLiteral k)
                                    argExpr = SynExpr.Ident id as o) when
                                    id.idText = nameText && listModule coreList m f [ "item"; "nth" ]
                                    ->
                                    partOfIndex k |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | PipeApp(SynExpr.Ident id as o,
                                          SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))) when
                                    id.idText = nameText && listModule coreList m f [ "head"; "tail" ]
                                    ->
                                    partOfFunction f.idText |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | PipeApp(SynExpr.Ident id as o,
                                          SynExpr.App(
                                              funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ]))
                                              argExpr = IntLiteral k)) when
                                    id.idText = nameText && listModule coreList m f [ "item"; "nth" ]
                                    ->
                                    partOfIndex k |> ValueOption.map (fun part -> part, e.Range, o.Range)
                                | _ -> ValueNone

                            let uses = inClause |> Array.choose (useOf >> ValueOption.toOption)

                            let accounted =
                                occurrences
                                |> Array.forall (fun o -> uses |> Array.exists (fun (_, _, acc) -> Range.equals acc o))

                            let parts = uses |> Array.map (fun (p, _, _) -> p) |> Set.ofArray

                            // a rebinding of the name inside the arm
                            let rebound =
                                let bindsName (p: SynPat) =
                                    patBoundNames p |> List.contains nameText

                                (index.Pats
                                 |> Array.exists (fun (_, p) ->
                                     within clauseRange p.Range
                                     && not (Range.equals p.Range pat.Range)
                                     && (match p with
                                         | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = nameText
                                         | _ -> false)))
                                || (inClause
                                    |> Array.exists (fun e ->
                                        match e with
                                        | SynExpr.Lambda(
                                            args = SynSimplePats.SimplePats(pats = simple); parsedData = parsed) ->
                                            (simple
                                             |> List.exists (fun s ->
                                                 match s with
                                                 | SynSimplePat.Id(ident = id) -> id.idText = nameText
                                                 | _ -> false))
                                            || (match parsed with
                                                | Some(ps, _) -> ps |> List.exists bindsName
                                                | None -> false)
                                        | SynExpr.For(ident = id) -> id.idText = nameText
                                        | SynExpr.ForEach(pat = p) -> bindsName p
                                        | LetOrUseE lou ->
                                            lou.Bindings |> List.exists (fun (SynBinding(headPat = p)) -> bindsName p)
                                        | Clauses cs ->
                                            cs |> List.exists (fun (SynMatchClause(pat = p)) -> bindsName p)
                                        | _ -> false))

                            if
                                accounted
                                && not parts.IsEmpty
                                && not rebound
                                && (not (parts.Contains Part.Second) || excluded 1)
                            then
                                let names =
                                    freshNames
                                        fileText.Value
                                        [ nameText + "Head"; nameText + "Second"; nameText + "Tail" ]

                                let headName, secondName, tailName = names.[0], names.[1], names.[2]

                                let nameOf part =
                                    match part with
                                    | Part.Head -> headName
                                    | Part.Second -> secondName
                                    | Part.Tail -> tailName

                                let spelled part =
                                    if parts.Contains part then nameOf part else "_"

                                let pattern =
                                    if parts.Contains Part.Second then
                                        $"{spelled Part.Head} :: {spelled Part.Second} :: {spelled Part.Tail}"
                                    else
                                        $"{spelled Part.Head} :: {spelled Part.Tail}"

                                let edits =
                                    (name.idRange, pattern) :: [ for part, r, _ in uses -> r, nameOf part ]
                                    |> List.sortBy (fun (r, _) -> r.StartLine, r.StartColumn)

                                // the uses never nest (an index is a literal), so
                                // overlapping ranges would mean a shape this rule
                                // did not foresee: leave it
                                let overlapping =
                                    edits
                                    |> List.pairwise
                                    |> List.exists (fun ((a, _), (b, _)) -> Position.posGeq a.End b.Start)

                                // a clause spanning a `#if` has two texts, and
                                // the fix would rewrite only the one it saw
                                if not overlapping && not (spansDirective source clauseRange) then
                                    let original = textOfRange source clauseRange

                                    let replacement =
                                        let sb = System.Text.StringBuilder()
                                        let mutable cursor = 0

                                        for r, text in edits do
                                            let start = offsetIn source clauseRange r.Start
                                            let finish = offsetIn source clauseRange r.End
                                            sb.Append(original, cursor, start - cursor).Append(text) |> ignore
                                            cursor <- finish

                                        sb.Append(original, cursor, original.Length - cursor).ToString()

                                    {
                                        Range = clauseRange
                                        OriginalText = original
                                        ReplacementText = replacement
                                        Name = nameText
                                        Pattern = pattern
                                    }
                    | _ -> ()
            | _ -> ()
    ]
