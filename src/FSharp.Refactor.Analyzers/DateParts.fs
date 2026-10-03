/// FR0176 (correctness, fix), twin of the C# rule: a date assembled from
/// the parts of two different instants.
///
///     DateTime(now.Year, now.AddMonths(-1).Month, 25)
///     ->  DateTime(now.AddMonths(-1).Year, now.AddMonths(-1).Month, 25)
///
/// The month is read after a shift and the year before it (or the other
/// way round). Whenever the shift crosses a year boundary the two disagree:
/// "the 25th of last month" computed in January lands in December of the
/// CURRENT year, eleven months ahead.
///
/// The shapes: a `DateTime`, `DateTimeOffset` or `DateOnly` constructor
/// whose year argument is `X.Year` and whose month argument is `Y.Month`,
/// where one of X and Y is the other with one `.AddMonths`, `.AddDays` or
/// `.AddYears` call appended.
///
/// A sweep repairs the direction above only: the year was the plain part,
/// so the result changes exactly where the shift crosses a year boundary.
/// The reverse - `DateTime(now.AddMonths(1).Year, now.Month, 1)` - is the
/// same slip, but reading the MONTH from the shifted instant changes the
/// date in every month, and whether the next month or this one was meant
/// is not in the code: the editor offers it.
///
/// The fix reads both from the shifted instant. It is offered when the
/// receiver is a plain name or property chain and the shift's argument a
/// literal or a name - the expression is written a second time, so it
/// must be safe to evaluate twice. Anything else is a note.
///
/// A day argument read across a shift (`DateTime(now.Year, now.Month,
/// now.AddDays(1).Day)`) is noted only: the day can belong to another
/// month, and which month was meant is not in the code.
module FSharp.Refactor.DateParts

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The constructor call.
        Range: range
        /// The receiver read before the shift, as written.
        BaseText: string
        /// The receiver read after the shift, as written.
        ShiftedText: string
        /// The part read from the wrong instant: "year", "month" or "day".
        Part: string
        /// The edit making the unshifted part read the shifted receiver.
        Fix: (range * string * string) option
        /// The edit changes the result only where the shift crosses a year
        /// boundary - the year was the plain part. With the MONTH plain,
        /// reading it from the shifted instant changes the date every
        /// time, so that direction is an editor's offer.
        SweepSafe: bool
    }

type private Read =
    {
        /// The unshifted receiver, whitespace removed.
        Base: string
        /// The shift's method and argument, whitespace removed.
        Shift: (string * string) voption
        /// The whole receiver of the property, as written.
        ReceiverRange: range
        /// Receiver and shift argument are safe to write twice.
        Pure: bool
        Property: Ident
    }

let private shifts = set [ "AddMonths"; "AddDays"; "AddYears" ]

let private dateTypes =
    set [ "System.DateTime"; "System.DateTimeOffset"; "System.DateOnly" ]

let private squeeze (text: string) =
    text |> String.filter (fun c -> not (System.Char.IsWhiteSpace c))

let private rangeOfIdents (ids: Ident list) =
    Range.unionRanges ids.Head.idRange (List.last ids).idRange

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the identifier is one of the date types, or a member of one
        let onDateType (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                (try
                    match symbolUse.Symbol with
                    | :? FSharpEntity as entity -> entity.TryFullName |> Option.exists dateTypes.Contains
                    | :? FSharpMemberOrFunctionOrValue as mfv ->
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.exists dateTypes.Contains
                    | _ -> false
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

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

        // a literal, a name, or the negation of one
        let rec plainArgument (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const _
            | SynExpr.Ident _ -> true
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _ ])) -> true
            | SynExpr.App(funcExpr = IdentName "op_UnaryNegation"; argExpr = inner) -> plainArgument inner
            | _ -> false

        let namesOf (ids: Ident list) =
            ids |> List.map (fun i -> i.idText) |> String.concat "."

        // `X.Year` / `X.AddMonths(k).Month`, with what X is
        let readOf (property: string) (e: SynExpr) : Read option =
            match stripParens e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2 && (List.last ids).idText = property
                ->
                let receiver = ids |> List.take (ids.Length - 1)

                Some
                    {
                        Base = namesOf receiver
                        Shift = ValueNone
                        ReceiverRange = rangeOfIdents receiver
                        Pure = true
                        Property = List.last ids
                    }
            | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ p ])) when p.idText = property ->
                match stripParens receiver with
                | SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                    ids.Length >= 2 && shifts.Contains (List.last ids).idText
                    ->
                    Some
                        {
                            Base = namesOf (ids |> List.take (ids.Length - 1))
                            Shift =
                                ValueSome((List.last ids).idText, squeeze (textOfRange source (stripParens arg).Range))
                            ReceiverRange = receiver.Range
                            Pure = plainArgument arg
                            Property = p
                        }
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.DotGet(expr = inner; longDotId = SynLongIdent(id = [ m ]))
                    argExpr = arg) when shifts.Contains m.idText ->
                    Some
                        {
                            Base = squeeze (textOfRange source (stripParens inner).Range)
                            Shift = ValueSome(m.idText, squeeze (textOfRange source (stripParens arg).Range))
                            ReceiverRange = receiver.Range
                            Pure = false
                            Property = p
                        }
                | _ -> None
            | _ -> None

        // one side shifted, the other not, over the same receiver
        let across (a: Read) (b: Read) =
            a.Base = b.Base && a.Shift.IsNone <> b.Shift.IsNone

        let ofArguments (callRange: range) (arguments: SynExpr list) : Suggestion option =
            match arguments with
            | yearArg :: monthArg :: rest ->
                let year = readOf "Year" yearArg
                let month = readOf "Month" monthArg
                let day = rest |> List.tryHead |> Option.bind (readOf "Day")

                match year, month with
                | Some y, Some m when across y m && onDateType y.Property && onDateType m.Property ->
                    let shifted, plain, part = if m.Shift.IsSome then m, y, "year" else y, m, "month"
                    let shiftedText = textOfRange source shifted.ReceiverRange
                    let plainText = textOfRange source plain.ReceiverRange

                    // AddYears keeps the month: a shifted year beside the
                    // plain month is one consistent instant, and a shifted
                    // month beside the plain year is a shift that changes
                    // nothing - which year was meant is not in the code
                    // (whole years written in months - `AddMonths(-12)` - too)
                    let byYears =
                        match shifted.Shift with
                        | ValueSome("AddYears", _) -> true
                        | ValueSome("AddMonths", months) ->
                            match System.Int32.TryParse(months.Trim('(', ')')) with
                            | true, n -> n % 12 = 0
                            | false, _ -> false
                        | _ -> false

                    if byYears && part = "month" then
                        None
                    else
                        Some
                            {
                                Range = callRange
                                BaseText = plainText
                                ShiftedText = shiftedText
                                Part = part
                                Fix =
                                    if
                                        shifted.Pure
                                        && plain.Pure
                                        && not byYears
                                        && not (spansDirective source callRange)
                                    then
                                        Some(plain.ReceiverRange, plainText, shiftedText)
                                    else
                                        None
                                SweepSafe = part = "year"
                            }
                | _ ->
                    match month, day with
                    | Some m, Some d when across m d && onDateType m.Property && onDateType d.Property ->
                        let shifted, plain = if d.Shift.IsSome then d, m else m, d

                        Some
                            {
                                Range = callRange
                                BaseText = textOfRange source plain.ReceiverRange
                                ShiftedText = textOfRange source shifted.ReceiverRange
                                Part = "day"
                                Fix = None
                                SweepSafe = false
                            }
                    | _ -> None
            | _ -> None

        let isDateName (ids: Ident list) =
            match List.tryLast ids with
            | Some last ->
                (last.idText = "DateTime"
                 || last.idText = "DateTimeOffset"
                 || last.idText = "DateOnly")
                && onDateType last
            | None -> false

        [
            for _, e in index.Exprs do
                if not (inTranslatedContext e.Range) then
                    match e with
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                        argExpr = SynExpr.Paren(expr = SynExpr.Tuple(exprs = arguments))) when isDateName ids ->
                        yield! ofArguments e.Range arguments |> Option.toList
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.Ident id
                        argExpr = SynExpr.Paren(expr = SynExpr.Tuple(exprs = arguments))) when isDateName [ id ] ->
                        yield! ofArguments e.Range arguments |> Option.toList
                    | SynExpr.New(
                        targetType = SynType.LongIdent(SynLongIdent(id = ids))
                        expr = SynExpr.Paren(expr = SynExpr.Tuple(exprs = arguments))) when isDateName ids ->
                        yield! ofArguments e.Range arguments |> Option.toList
                    | _ -> ()
        ]
