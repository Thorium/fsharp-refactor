/// FR0165 (correctness): a local-time value compared with a UTC one.
///
///     if DateTime.Now > startedUtc then ...        // startedUtc = DateTime.UtcNow
///     let age = DateTime.UtcNow - DateTime.Today
///
/// `DateTime.Now`/`DateTime.Today` and `DateTime.UtcNow` differ by the
/// machine's UTC offset, so a comparison or a subtraction across the two
/// flips with the timezone and twice a year with daylight saving; the
/// code is right where it was written and wrong where it runs. C#'s twin
/// is CR0169.
///
/// A side's KIND is read syntactically and confirmed by the typechecker:
/// `DateTime.Now`/`Today` are local, `DateTime.UtcNow` is UTC, and a
/// `.Date`/`.AddX(...)`/`.Subtract(timespan)` keeps the kind of what it
/// was called on; an identifier bound ONCE in this file (`let startedUtc
/// = DateTime.UtcNow`, a module `let`, a local `let`) carries its
/// right-hand side's kind. `ToUniversalTime()`, `ToLocalTime()`,
/// `DateTime.SpecifyKind` and a `DateTime(..., DateTimeKind.X)` make the
/// kind explicit and stand the rule down; a `let mutable`, a parameter, a
/// field, anything written more than once or from something the rule
/// cannot classify is unknown and quiet. The shapes: `=`, `<>`, `<`,
/// `<=`, `>`, `>=` and `-` between two sides of different kinds,
/// `a.CompareTo b`, `a.Equals b`, `a.Subtract b` and `DateTime.Compare(a,
/// b)`. Note only: which kind is the right one is the author's call.
module FSharp.Refactor.DateTimeKindMix

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type Kind =
    | Local
    | Utc

type Suggestion =
    {
        /// The comparison or subtraction.
        Range: range
        /// The local side as written.
        LocalText: string
        /// The UTC side as written.
        UtcText: string
        /// `>`, `-`, `CompareTo`...
        Operation: string
    }

let private comparisons =
    dict
        [
            "op_Equality", "="
            "op_Inequality", "<>"
            "op_LessThan", "<"
            "op_LessThanOrEqual", "<="
            "op_GreaterThan", ">"
            "op_GreaterThanOrEqual", ">="
            "op_Subtraction", "-"
        ]

/// The members that keep the kind of their receiver.
let private kindKeepers =
    set
        [
            "Date"
            "AddDays"
            "AddHours"
            "AddMinutes"
            "AddSeconds"
            "AddMilliseconds"
            "AddTicks"
            "AddMonths"
            "AddYears"
            "Subtract"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the identifier resolves to a member of System.DateTime
        let onDateTime (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.map ((=) "System.DateTime")
                        |> Option.defaultValue false
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false

        // every name this file binds exactly once, immutably, with the
        // expression it is bound to
        let bindings =
            let fromBindings (bs: SynBinding list) =
                bs
                |> List.choose (fun b ->
                    match b with
                    | SynBinding(isMutable = false; headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = rhs)
                    | SynBinding(
                        isMutable = false
                        headPat = SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)))
                        expr = rhs) -> Some(id.idText, rhs)
                    | _ -> None)

            let all =
                [
                    for _, d in index.Decls do
                        match d with
                        | SynModuleDecl.Let(bindings = bs) -> yield! fromBindings bs
                        | _ -> ()
                    for _, e in index.Exprs do
                        match e with
                        | LetOrUseE lou when not lou.IsBang -> yield! fromBindings lou.Bindings
                        | _ -> ()
                ]

            // a name is known only when the file binds it in exactly ONE
            // pattern anywhere — the `let` itself. A parameter, a lambda
            // argument, a match arm or a `for` variable of the same name
            // elsewhere (`let now = DateTime.Now` in one function, a `now`
            // parameter in another) would be read as that `let`
            let patternCount =
                index.Pats
                |> Array.choose (fun (_, p) ->
                    match p with
                    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                    | _ -> None)
                |> Array.countBy id
                |> Map.ofArray

            all
            |> List.filter (fun (name, _) -> patternCount.TryFind name = Some 1)
            |> Map.ofList

        // `a.CompareTo b`: the receiver, spanning its own identifiers
        let receiverOf (ids: Ident list) =
            let recv = ids |> List.take (ids.Length - 1)

            SynExpr.LongIdent(
                false,
                SynLongIdent(recv, [], []),
                None,
                Range.unionRanges recv.Head.idRange (List.last recv).idRange
            )


        // an expression that is plainly a TimeSpan: `TimeSpan.FromHours 1.0`,
        // `TimeSpan(...)`, `TimeSpan.Zero`, or a name bound to one. `x - t`
        // and `x.Subtract t` keep x's kind only for such a t; against a
        // DateTime, or anything the rule cannot tell from one, the result is
        // a duration (or unknown) and carries no kind
        let rec isTimeSpan (depth: int) (e: SynExpr) =
            depth <= 8
            && (match stripParens e with
                | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                    ids.Length >= 2
                    ->
                    ids.[ids.Length - 2].idText = "TimeSpan"
                | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id) -> id.idText = "TimeSpan"
                | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
                    (List.last ids).idText = "TimeSpan"
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                    ids.[ids.Length - 2].idText = "TimeSpan"
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ]))
                | SynExpr.Ident id -> bindings.TryFind id.idText |> Option.exists (isTimeSpan (depth + 1))
                | _ -> false)

        // the kind an expression carries, or None where it is unknown or
        // made explicit
        let rec kindOf (depth: int) (e: SynExpr) : Kind option =
            if depth > 8 then
                None
            else
                match stripParens e with
                | SynExpr.Typed(expr = inner) -> kindOf depth inner
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) ->
                    bindings.TryFind id.idText |> Option.bind (kindOf (depth + 1))
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                    let names = ids |> List.map (fun i -> i.idText)

                    // DateTime.Now / DateTime.UtcNow / DateTime.Today, then
                    // kind-keeping members; a name the file binds, then
                    // kind-keeping members
                    let rec walk (kind: Kind option) (rest: Ident list) =
                        match rest with
                        | [] -> kind
                        | m :: tail when kindKeepers.Contains m.idText -> walk kind tail
                        | _ -> None

                    match names with
                    | _ when
                        (match List.tryFindIndex (fun n -> n = "Now" || n = "Today" || n = "UtcNow") names with
                         | Some i -> i > 0 && ids.[i - 1].idText = "DateTime" && onDateTime ids.[i]
                         | None -> false)
                        ->
                        let i = names |> List.findIndex (fun n -> n = "Now" || n = "Today" || n = "UtcNow")
                        let kind = if names.[i] = "UtcNow" then Kind.Utc else Kind.Local
                        walk (Some kind) (ids |> List.skip (i + 1))
                    | _ ->
                        match bindings.TryFind names.Head with
                        | Some rhs -> walk (kindOf (depth + 1) rhs) ids.Tail
                        | None -> None
                | SynExpr.Ident id -> bindings.TryFind id.idText |> Option.bind (kindOf (depth + 1))
                // `x.AddDays 1` / `x.Subtract span` as applications
                | SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                    ids.Length >= 2 && kindKeepers.Contains (List.last ids).idText
                    ->
                    // Subtract of anything but a plain TimeSpan is a duration
                    // or unknown: no kind
                    if (List.last ids).idText = "Subtract" && not (isTimeSpan (depth + 1) arg) then
                        None
                    else
                        kindOf (depth + 1) (receiverOf ids)
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ]))
                    argExpr = arg) when kindKeepers.Contains m.idText ->
                    if m.idText = "Subtract" && not (isTimeSpan (depth + 1) arg) then
                        None
                    else
                        kindOf (depth + 1) recv
                | SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ])) when kindKeepers.Contains m.idText ->
                    kindOf (depth + 1) recv
                // `x + span` keeps the kind (a DateTime adds nothing but a
                // TimeSpan); `x - span` too, for a plain TimeSpan — `x - y`
                // of two DateTimes is a duration, the shape the rule reports
                // rather than a side
                | SynExpr.App(
                    funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                    op.idText = "op_Addition"
                    ->
                    match kindOf (depth + 1) lhs, kindOf (depth + 1) rhs with
                    | Some k, None -> Some k
                    | None, Some k -> Some k
                    | _ -> None
                | SynExpr.App(
                    funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                    op.idText = "op_Subtraction" && isTimeSpan (depth + 1) rhs
                    ->
                    kindOf (depth + 1) lhs
                | _ -> None

        let mixed (a: SynExpr) (b: SynExpr) =
            match kindOf 0 a, kindOf 0 b with
            | Some Kind.Local, Some Kind.Utc -> Some(a, b)
            | Some Kind.Utc, Some Kind.Local -> Some(b, a)
            | _ -> None

        let suggestion (r: range) (operation: string) (local: SynExpr, utc: SynExpr) =
            {
                Range = r
                LocalText = textOfRange source local.Range
                UtcText = textOfRange source utc.Range
                Operation = operation
            }

        // `DateTime.Now - DateTime.UtcNow` IS the machine's UTC offset — the
        // one subtraction across kinds that is meant
        let isClockRead (e: SynExpr) =
            match stripParens e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                (match (List.last ids).idText with
                 | "Now"
                 | "UtcNow" -> true
                 | _ -> false)
                && ids.[ids.Length - 2].idText = "DateTime"
            | _ -> false

        [
            for _, e in index.Exprs do
                match e with
                // a = b, a - b ...
                | SynExpr.App(
                    funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
                    comparisons.ContainsKey op.idText
                    && not (op.idText = "op_Subtraction" && isClockRead lhs && isClockRead rhs)
                    ->
                    match mixed lhs rhs with
                    | Some sides -> suggestion e.Range comparisons.[op.idText] sides
                    | None -> ()
                // a.CompareTo b / a.Equals b / a.Subtract b
                | SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                    ids.Length >= 2
                    && (match (List.last ids).idText with
                        | "CompareTo"
                        | "Equals"
                        | "Subtract" -> true
                        | _ -> false)
                    && onDateTime (List.last ids)
                    ->
                    let receiver = receiverOf ids

                    match mixed receiver (stripParens arg) with
                    | Some sides -> suggestion e.Range (List.last ids).idText sides
                    | None -> ()
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ]))
                    argExpr = arg) when
                    (m.idText = "CompareTo" || m.idText = "Equals" || m.idText = "Subtract")
                    && onDateTime m
                    ->
                    match mixed recv (stripParens arg) with
                    | Some sides -> suggestion e.Range m.idText sides
                    | None -> ()
                // DateTime.Compare(a, b)
                | SynExpr.App(
                    isInfix = false
                    funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                    argExpr = SynExpr.Paren(expr = SynExpr.Tuple(exprs = [ a; b ]))) when
                    ids.Length >= 2
                    && (List.last ids).idText = "Compare"
                    && onDateTime (List.last ids)
                    ->
                    match mixed a b with
                    | Some sides -> suggestion e.Range "Compare" sides
                    | None -> ()
                | _ -> ()
        ]
