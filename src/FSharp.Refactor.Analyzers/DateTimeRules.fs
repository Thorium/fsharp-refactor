/// FR0121: wall-clock traps on servers.
///
/// 1. `DateTime.UtcNow.Date` (note, always): truncating a UTC instant to
///    a date crosses NOBODY's midnight — the cut point is a random time
///    of day in every user's timezone. `DateTime.Today` is the same bug
///    in local clothing: the SERVER's calendar date, which the end user
///    never knows. Which timezone's date was meant is unknowable, so
///    this stays advice.
///
/// 2. `DateTime.Now` as a complete expression: on a server the local
///    clock is a deployment accident; `DateTime.UtcNow` records an
///    instant. The rewrite is offered in EDITORS and applied by the CLI
///    only under `{ "FR0121": { "utcNow": 1 } }` — Fable and desktop
///    software legitimately want local time, so the default never
///    rewrites. `DateTime.Now.Date`-style continuations are excluded
///    from the fix entirely: swapping Now for UtcNow under a calendar
///    read CREATES bug 1.
///
/// Both shapes are typed-gated to System.DateTime/System.DateTimeOffset.
module FSharp.Refactor.DateTimeRules

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

[<RequireQualifiedAccess>]
type WallClockKind =
    /// UtcNow.Date / Today: a timezone-random calendar cut.
    | UtcDateCut of text: string
    /// A bare DateTime.Now: the opt-in UtcNow rewrite.
    | LocalNow

type Suggestion =
    {
        Range: range
        Kind: WallClockKind
        /// For LocalNow: the `Now` ident to rewrite to `UtcNow`.
        FixRange: range option
    }

let private entityOf (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as mfv ->
            (try
                mfv.DeclaringEntity
                |> Option.bind (fun e -> e.TryFullName)
                |> Option.defaultValue ""
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 "")
        | _ -> ""
    | None -> ""

let private isDateTimeEntity (name: string) =
    name = "System.DateTime" || name = "System.DateTimeOffset"

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // `dt.Date <> DateTime.Today` is a same-day test against a date
        // this machine produced (a fill-in date, a parse default): both
        // sides are the same clock, so the calendar cut is not a bug there
        let sameDayCompare (path: SyntaxNode list) (r: range) =
            let endsWithDate (e: SynExpr) =
                match e with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    (List.last ids).idText = "Date"
                | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    (List.last ids).idText = "Date"
                | _ -> false

            let isCompare (op: SynExpr) =
                match op with
                | SynExpr.Ident id
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) ->
                    id.idText = "op_Equality" || id.idText = "op_Inequality"
                | _ -> false

            match path with
            // Today on the right: outer App(App(op, lhs), Today)
            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = op; argExpr = lhs))) :: _ when
                isCompare op && not (Range.rangeContainsRange lhs.Range r)
                ->
                endsWithDate lhs
            // Today on the left: inner App(op, Today), then outer App(_, rhs)
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op)) :: SyntaxNode.SynExpr(SynExpr.App(
                argExpr = rhs)) :: _ when isCompare op -> endsWithDate rhs
            | _ -> false

        // an expression-tree translator reproduces the clock ON PURPOSE:
        // the arm that maps a member NAMED "Now" (or "Today") to the call
        // (SQLProvider's evaluator: `when me.Member.Name = "Now" ->
        // DateTime.Now`) is a translation table, not a clock read. The
        // nearest enclosing match arm names the member in its guard or
        // its pattern.
        let clockNames = set [ "Now"; "UtcNow"; "Today" ]

        let literalIn (wanted: Set<string>) (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.Const(SynConst.String(text = s), _) when Range.rangeContainsRange r e.Range ->
                    wanted.Contains s
                | _ -> false)
            || index.Pats
               |> Array.exists (fun (_, p) ->
                   match p with
                   | SynPat.Const(SynConst.String(text = s), _) when Range.rangeContainsRange r p.Range ->
                       wanted.Contains s
                   | _ -> false)

        let translatorArm (path: SyntaxNode list) (names: string list) =
            let wanted = Set.intersect clockNames (set names)

            // the guard runs for every dotted name in the file: only a clock
            // read pays for the scan of its arm
            not wanted.IsEmpty
            && (path
                |> List.tryPick (fun node ->
                    match node with
                    | SyntaxNode.SynMatchClause(SynMatchClause(pat = p; whenExpr = w)) -> Some(p, w)
                    | _ -> None)
                |> Option.exists (fun (p, w) ->
                    literalIn wanted p.Range
                    || (match w with
                        | Some guard -> literalIn wanted guard.Range
                        | None -> false)))

        // the non-Utc timestamp setters take LOCAL time —
        // `File.SetLastWriteTime(path, DateTime.Now)` (fsdocs) is right as
        // written, and UtcNow there would stamp the file hours off
        let localTimeSetters =
            set
                [ "SetCreationTime"
                  "SetLastWriteTime"
                  "SetLastAccessTime"
                  "CreationTime"
                  "LastWriteTime"
                  "LastAccessTime" ]

        let feedsLocalSetter (path: SyntaxNode list) =
            path
            |> List.truncate 3
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))) ->
                    ids.Length >= 2
                    && localTimeSetters.Contains (List.last ids).idText
                    && (match ids.[ids.Length - 2].idText with
                        | "File"
                        | "Directory" -> true
                        | _ -> false)
                | SyntaxNode.SynExpr(SynExpr.LongIdentSet(SynLongIdent(id = ids), _, _))
                | SyntaxNode.SynExpr(SynExpr.DotSet(longDotId = SynLongIdent(id = ids))) ->
                    not ids.IsEmpty && localTimeSetters.Contains (List.last ids).idText
                | _ -> false)

        [ for path, expr in index.Exprs do
              match expr with
              | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                  ids.Length >= 2
                  && not (sameDayCompare path expr.Range)
                  && not (translatorArm path (ids |> List.map (fun i -> i.idText)))
                  && not (feedsLocalSetter path)
                  ->
                  let names = ids |> List.map (fun i -> i.idText)

                  // ...UtcNow.Date ANYWHERE in the chain (`.AddDays` etc may
                  // follow the cut), and Today likewise
                  let utcDateAt =
                      names
                      |> List.pairwise
                      |> List.tryFindIndex (fun (a, b) -> a = "UtcNow" && b = "Date")

                  match utcDateAt with
                  | Some i when isDateTimeEntity (entityOf check source (List.item i ids)) ->
                      { Range = expr.Range
                        Kind = WallClockKind.UtcDateCut(String.concat "." names)
                        FixRange = None }
                  | _ ->
                      let todayAt = names |> List.tryFindIndex ((=) "Today")

                      match todayAt with
                      | Some i when i > 0 && entityOf check source (List.item i ids) = "System.DateTime" ->
                          { Range = expr.Range
                            Kind = WallClockKind.UtcDateCut(String.concat "." names)
                            FixRange = None }
                      | _ ->
                          // a COMPLETE DateTime.Now — nothing after Now, so
                          // the UtcNow rewrite cannot create a calendar bug —
                          // or Now read as an INSTANT (`.Ticks` as a version
                          // number goes backwards at the DST fall-back;
                          // `.ToBinary`, `.ToFileTime`), which UtcNow serves
                          // just as well. `Now.ToString(...)` renders the
                          // local calendar, so it gets the note but not the
                          // rewrite. DateTimeOffset.Now stays quiet entirely:
                          // it CARRIES its offset, which is often the point
                          let reversed =
                              match List.rev names with
                              | "ToString" :: rest -> Some false, rest
                              | rest -> Some true, rest

                          match reversed with
                          | Some rewritable, "Now" :: _ ->
                              let nowId = ids |> List.find (fun i -> i.idText = "Now")

                              if entityOf check source nowId = "System.DateTime" then
                                  { Range = expr.Range
                                    Kind = WallClockKind.LocalNow
                                    FixRange = if rewritable then Some nowId.idRange else None }
                          | Some _, ("Ticks" | "ToBinary" | "ToFileTime") :: "Now" :: _ ->
                              let nowId = ids |> List.find (fun i -> i.idText = "Now")

                              if entityOf check source nowId = "System.DateTime" then
                                  { Range = expr.Range
                                    Kind = WallClockKind.LocalNow
                                    FixRange = Some nowId.idRange }
                          | _ -> ()
              | _ -> () ]
