/// FR0175 (correctness, fix), twin of the C# rule: a custom date format
/// whose specifier cannot mean what its position says.
///
///     d.ToString "yyyyMMddhhmmss"   ->  d.ToString "yyyyMMddHHmmss"
///     d.ToString "yyyy-mm-dd"       ->  d.ToString "yyyy-MM-dd"
///     d.ToString "HH:MM:ss"         ->  d.ToString "HH:mm:ss"
///
/// Three slips, each read off the format alone:
///
/// 1. `h`/`hh` with no `t` designator anywhere: a 12-hour clock without
///    AM/PM writes 14:05 and 02:05 as the same text.
/// 2. `m`/`mm` between year and day (a `y` or `d` neighbour, no hour or
///    second neighbour) in a format with no `M`: minutes where the month
///    belongs.
/// 3. `M`/`MM` after the hours or before the seconds (no year or day
///    neighbour) in a format with no `m`: the month where the minutes
///    belong.
///
/// The two swapped for each other ("yyyy-mm-dd HH:MM") are both repaired:
/// the `M` that would vouch for the `mm` is itself in a minute's place.
///
/// A neighbour is the next letter run on either side with only separator
/// characters between; an escaped or quoted section breaks adjacency. A
/// one-character format is a standard format and a `%` marks single
/// specifiers - both are left alone.
///
/// Typed rule: `ToString`, `ParseExact` or `TryParseExact` must resolve to
/// DateTime, DateTimeOffset, DateOnly or TimeOnly. TimeSpan never matches -
/// `hh` is its only hour specifier. The format must be a literal whose
/// source text is its value (no string escapes), so the edit lands on the
/// character it names.
///
/// A format handed to a parser is reported the same way, but the rewrite
/// changes what the parser accepts, so only an editor offers it.
///
/// The 12-hour repair is a sweep's only for a timestamp - a format that
/// also names a year or a day - in a file where no other literal renders
/// or spells AM/PM. A clock face (`hh:mm`) may show its designator in
/// another element, and `d.ToString "hh:mm" + " " + d.ToString "tt"` is
/// correct as written; there the note stands and the editor offers.
module FSharp.Refactor.DateFormat

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type Slip =
    | TwelveHour
    | MinutesForMonth
    | MonthForMinutes

type Suggestion =
    {
        /// The format literal.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The format as written and as repaired, without quotes.
        Format: string
        Repaired: string
        Slips: Slip list
        /// The literal is a ParseExact/TryParseExact format.
        IsParse: bool
        /// The repair cannot be the wrong reading, so a sweep applies it.
        /// False for a parser's format, and for a 12-hour clock that may
        /// be deliberate: a time with no date beside it, or a file that
        /// renders the AM/PM designator in another literal.
        SweepSafe: bool
    }

[<Struct>]
type private Run =
    {
        Letter: char
        Start: int
        Length: int
        /// Only separator characters lie between the previous run and this one.
        Adjacent: bool
    }

let private isLetter (c: char) =
    (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z')

let private runsOf (format: string) : Run[] voption =
    let runs = ResizeArray<Run>()
    let mutable i = 0
    let mutable literalSince = false
    let mutable wellFormed = true

    while wellFormed && i < format.Length do
        let c = format.[i]

        if c = '\\' then
            literalSince <- true
            i <- i + 2
        elif c = '\'' || c = '"' then
            let close = format.IndexOf(c, i + 1)

            if close < 0 then
                wellFormed <- false
            else
                literalSince <- true
                i <- close + 1
        elif isLetter c then
            let rec advanceJ j =
                if j < format.Length && format.[j] = c then
                    advanceJ (j + 1)
                else
                    j

            let j = advanceJ i

            runs.Add
                {
                    Letter = c
                    Start = i
                    Length = j - i
                    Adjacent = not literalSince
                }

            literalSince <- false
            i <- j
        else
            i <- i + 1

    if wellFormed then ValueSome(runs.ToArray()) else ValueNone

/// The repaired format and the slips it had, or None when the format is
/// sound, standard, or not one the rule reads.
let repair (format: string) : (string * Slip list) option =
    if format.Length < 2 || format.Contains '%' then
        None
    else
        match runsOf format with
        | ValueNone -> None
        | ValueSome runs ->
            let has (letter: char) =
                runs |> Array.exists (fun r -> r.Letter = letter)

            let left (k: int) =
                if k > 0 && runs.[k].Adjacent then
                    ValueSome runs.[k - 1].Letter
                else
                    ValueNone

            let right (k: int) =
                if k + 1 < runs.Length && runs.[k + 1].Adjacent then
                    ValueSome runs.[k + 1].Letter
                else
                    ValueNone

            let neighbourIn (letters: string) (k: int) =
                (match left k with
                 | ValueSome c -> letters.Contains c
                 | ValueNone -> false)
                || (match right k with
                    | ValueSome c -> letters.Contains c
                    | ValueNone -> false)

            // minutes written where a date field belongs
            let minutesInDate (k: int) =
                runs.[k].Letter = 'm' && neighbourIn "yd" k && not (neighbourIn "hHs" k)

            // a month written where a time field belongs; MMM and MMMM are
            // month names, never minutes
            let monthInTime (k: int) =
                runs.[k].Letter = 'M'
                && runs.[k].Length <= 2
                && not (neighbourIn "yd" k)
                && ((match left k with
                     | ValueSome c -> c = 'h' || c = 'H'
                     | ValueNone -> false)
                    || right k = ValueSome 's')

            let every (letter: char) (slipped: int -> bool) =
                runs
                |> Array.indexed
                |> Array.forall (fun (k, r) -> r.Letter <> letter || slipped k)

            let noDesignator = not (has 't')
            // the other field is absent, or is itself the swapped one
            // ("yyyy-mm-dd HH:MM")
            let noMonth = every 'M' monthInTime
            let noMinute = every 'm' minutesInDate
            let chars = format.ToCharArray()
            let slips = ResizeArray<Slip>()

            let rewrite (run: Run) (letter: char) (slip: Slip) =
                for p in run.Start .. run.Start + run.Length - 1 do
                    chars.[p] <- letter

                if not (slips.Contains slip) then
                    slips.Add slip

            runs
            |> Array.iteri (fun k run ->
                match run.Letter with
                // an `h` run touching an `H` run would merge into one longer
                // run and change its meaning
                | 'h' when
                    noDesignator
                    && not (run.Start > 0 && format.[run.Start - 1] = 'H')
                    && not (run.Start + run.Length < format.Length && format.[run.Start + run.Length] = 'H')
                    ->
                    rewrite run 'H' Slip.TwelveHour
                | 'm' when noMonth && minutesInDate k -> rewrite run 'M' Slip.MinutesForMonth
                | 'M' when noMinute && monthInTime k -> rewrite run 'm' Slip.MonthForMinutes
                | _ -> ())

            if slips.Count = 0 then
                None
            else
                Some(System.String chars, List.ofSeq slips)

/// The format names a year or a day: a timestamp rather than a clock face.
let private hasDatePart (format: string) =
    match runsOf format with
    | ValueSome runs -> runs |> Array.exists (fun r -> r.Letter = 'y' || r.Letter = 'd')
    | ValueNone -> false

/// AM/PM written out, or a format that renders the designator.
let private designator =
    System.Text.RegularExpressions.Regex(
        @"tt|\b[AaPp]\.?[Mm]\b\.?",
        System.Text.RegularExpressions.RegexOptions.Compiled
    )

let private dateTypes =
    set
        [
            "System.DateTime"
            "System.DateTimeOffset"
            "System.DateOnly"
            "System.TimeOnly"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the member resolves to one of the date types
        let onDateType (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.exists dateTypes.Contains
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false

        // a format inside `query { }` or a quotation is translated, not
        // run: the provider decides what it means
        let translatedRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName "query"; argExpr = SynExpr.ComputationExpr(expr = body)) ->
                    Some body.Range
                | SynExpr.Quote(quotedExpr = q) -> Some q.Range
                | _ -> None)

        let inTranslatedContext (r: range) =
            translatedRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

        // a 12-hour clock with no `tt` is no slip when the designator is
        // rendered beside it: `d.ToString "hh:mm" + " " + d.ToString "tt"`.
        // Any literal of the file that renders or spells AM/PM counts
        let designatorElsewhere =
            lazy
                (index.Exprs
                 |> Array.exists (fun (_, e) ->
                     match e with
                     | SynExpr.Const(SynConst.String(text = text), _) -> designator.IsMatch text
                     | SynExpr.InterpolatedString(contents = parts) ->
                         parts
                         |> List.exists (fun part ->
                             match part with
                             | SynInterpolatedStringPart.String(text, _) -> designator.IsMatch text
                             | SynInterpolatedStringPart.FillExpr(qualifiers = Some format) ->
                                 designator.IsMatch format.idText
                             | _ -> false)
                     | _ -> false))

        let literal (isParse: bool) (e: SynExpr) : Suggestion option =
            match stripParens e with
            | SynExpr.Const(SynConst.String(text = text; range = r), _) ->
                match repair text with
                | Some(repaired, slips) ->
                    let written = textOfRange source r
                    let at = written.IndexOf(text, System.StringComparison.Ordinal)

                    // the value must sit in the source verbatim, between
                    // plain quotes: an escape would shift every position
                    let opening = if at >= 0 then written.Substring(0, at) else ""
                    let closing = if at >= 0 then written.Substring(at + text.Length) else ""

                    if
                        (opening = "\"" || opening = "@\"" || opening = "\"\"\"")
                        && (closing = "\"" || closing = "\"\"\"")
                    then
                        Some
                            {
                                Range = r
                                OriginalText = written
                                ReplacementText = opening + repaired + closing
                                Format = text
                                Repaired = repaired
                                Slips = slips
                                IsParse = isParse
                                SweepSafe =
                                    not isParse
                                    && (not (List.contains Slip.TwelveHour slips)
                                        || (hasDatePart text && not (designatorElsewhere.Force())))
                            }
                    else
                        None
                | None -> None
            | _ -> None

        // the format argument of ParseExact/TryParseExact: one literal or an
        // array of them
        let rec literalsOf (e: SynExpr) : SynExpr list =
            match stripParens e with
            | SynExpr.ArrayOrList(isArray = true; exprs = items) -> items
            | SynExpr.ArrayOrListComputed(isArray = true; expr = body) ->
                let rec flatten (b: SynExpr) =
                    match b with
                    | SynExpr.Sequential(expr1 = a; expr2 = rest) -> a :: flatten rest
                    | single -> [ single ]

                flatten body
            | single -> [ single ]

        let ofCall (callee: Ident) (arg: SynExpr) : Suggestion list =
            match callee.idText with
            | "ToString" when onDateType callee ->
                match stripParens arg with
                | SynExpr.Tuple(exprs = format :: _) -> literal false format |> Option.toList
                | format -> literal false format |> Option.toList
            | "ParseExact"
            | "TryParseExact" when onDateType callee ->
                match stripParens arg with
                | SynExpr.Tuple(exprs = _ :: formats :: _) -> literalsOf formats |> List.choose (literal true)
                | _ -> []
            | _ -> []

        let found =
            [
                for _, e in index.Exprs do
                    match e with
                    | SynExpr.App(
                        isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                        ids.Length >= 2 && not (inTranslatedContext e.Range)
                        ->
                        yield! ofCall (List.last ids) arg
                    | SynExpr.App(
                        isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                        not (ids.IsEmpty || inTranslatedContext e.Range)
                        ->
                        yield! ofCall (List.last ids) arg
                    | _ -> ()
            ]

        // a writer and its reader: with a 12-hour parser format in the
        // file, repairing only the `ToString` side would write hours the
        // unchanged parser rejects - the pair is the author's to change
        let twelveHourReader =
            found
            |> List.exists (fun s -> s.IsParse && List.contains Slip.TwelveHour s.Slips)

        if twelveHourReader then
            found
            |> List.map (fun s ->
                if List.contains Slip.TwelveHour s.Slips then
                    { s with SweepSafe = false }
                else
                    s)
        else
            found
