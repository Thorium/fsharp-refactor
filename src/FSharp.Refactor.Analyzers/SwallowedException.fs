/// Refactoring note (correctness): a catch-all handler that does nothing —
/// or quietly substitutes a default value — swallows every exception.
///
///     try work () with _ -> ()              // hides bugs AND cancellation
///     try work () with :? Exception -> ()
///     try read () with _ -> ""              // masks failure as an answer
///     try count () with _ -> 0
///     try get () with _ -> Unchecked.defaultof<_>
///
/// An empty catch of System.Exception silently eats programming errors,
/// OperationCanceledException, and everything else; a default-value catch
/// additionally disguises the failure as a legitimate result. Advice: the
/// best fix is usually no catch at all — a guard on the value that would
/// throw — then a specific exception type, then at least a log line.
///
/// The editor offers, where the shape allows:
///   - the GUARD, for a body that is pure arithmetic with one division by
///     a non-literal: `if x = 0 then fallback else a / x` — the catch is
///     removable because nothing else in the body throws
///   - TryParse, for a body that is one `Int32.Parse s`-style call:
///     `match Int32.TryParse s with | true, v -> Some v | _ -> None`
///   - a NARROWER catch, for a body doing file IO: `:? IOException |
///     :? UnauthorizedAccessException` instead of everything
///   - a LOG LINE in the file's own logging idiom (Microsoft.Extensions
///     .Logging, Serilog or Logary, whichever the file already uses),
///     naming the exception, the method and its parameters, as the
///     handler's first statement
/// A sweep only notes: whether the catch can go is the author's call.
///
/// Only trivially empty or constant-default bodies with catch-all patterns
/// (`_`, a bare binder, or `:? System.Exception`) are flagged; a handler
/// that catches a SPECIFIC exception type and deliberately ignores it is a
/// decision, not an accident, and stays quiet.
module FSharp.Refactor.SwallowedException

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text
open System.Text.RegularExpressions

/// One editor offer: what it does, and its edits.
type Offer =
    { Label: string
      Edits: (range * string * string) list }

type Suggestion =
    {
        Range: range
        /// The handler pattern's text, for the message.
        PatternText: string
        /// The substituted default's text (`""`, `0`, `Unchecked.defaultof`),
        /// or None for an empty `()` body.
        FallbackText: string option
        /// The teardown idiom: the body is one Dispose/Close/Shutdown/
        /// Cancel/Complete/Delete/Reset call (optionally nulling the field
        /// after it) — a best-effort release on the way out, worth a lower
        /// note than a swallow around real work.
        Teardown: bool
        /// The body is one call to a probe that does not throw for a
        /// missing path — `File.Exists`, `File.GetLastWriteTime` — so the
        /// advice is to delete the try, not to guard a value.
        Probe: string option
        /// The editor's offers, best first.
        Offers: Offer list
    }

/// A pattern that matches every exception.
let private isCatchAll (pat: SynPat) =
    match pat with
    | SynPat.Wild _
    | SynPat.Named _ -> true
    | SynPat.IsInst(SynType.LongIdent(SynLongIdent(id = ids)), _) ->
        not ids.IsEmpty && (List.last ids).idText = "Exception"
    | SynPat.As(lhsPat = SynPat.IsInst(SynType.LongIdent(SynLongIdent(id = ids)), _)) ->
        not ids.IsEmpty && (List.last ids).idText = "Exception"
    | _ -> false

/// The name a catch-all binds the exception to, if any.
let private binderOf (pat: SynPat) =
    match pat with
    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
    | SynPat.As(rhsPat = SynPat.Named(ident = SynIdent(ident = id))) -> Some id.idText
    | _ -> None

/// A body that substitutes a default-ish value for the exception: a bare
/// constant, `Unchecked.defaultof<_>`, None/ValueNone, or an empty
/// collection literal.
let private isDefaultFallback (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Unit, _) -> false // handled as the empty body
    // bools are decided by the caller, which can see the try BODY: the
    // `try ping (); true with _ -> false` probe stays quiet, while
    // `try parse s with _ -> false` disguises the failure as an answer
    | SynExpr.Const(SynConst.Bool _, _) -> false
    | SynExpr.Const _ -> true
    | SynExpr.Null _ -> true
    | IdentName("None" | "ValueNone") -> true
    | SynExpr.ArrayOrList(_, [], _) -> true
    // dotted defaults: String.Empty, DateTime.MinValue, TimeSpan.Zero,
    // Array.empty, Map.empty, ...
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        not ids.IsEmpty
        && (match (List.last ids).idText with
            | "Empty"
            | "empty"
            | "MinValue"
            | "MaxValue"
            | "Zero"
            | "Default" -> true
            | _ -> false)
        ->
        true
    | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
        not ids.IsEmpty && (List.last ids).idText = "defaultof"
    | _ -> false

[<return: Struct>]
let inline private (|IsDefaultFallback|_|) input =
    if isDefaultFallback input then
        ValueSome input
    else
        ValueNone

/// The expression a block evaluates to — the tail of its Sequential chain.
[<TailCall>]
let rec private lastExprOf (e: SynExpr) =
    match e with
    | SynExpr.Sequential(expr2 = e2) -> lastExprOf e2
    | SynExpr.Paren(expr = inner) -> lastExprOf inner
    | _ -> e

/// Is a bool-literal catch-all the PROBE idiom — the try body answering
/// with the opposite literal (`try ping (); true with _ -> false`, or the
/// inverted did-it-throw probe)? Then the failure IS the answer. Any other
/// body makes the literal a disguised default like the rest.
let private isBoolProbe (tryBody: SynExpr) (fallback: bool) =
    match lastExprOf tryBody with
    | SynExpr.Const(SynConst.Bool bodyValue, _) -> bodyValue <> fallback
    | _ -> false

// ---- the offers ----

let private arithmeticOps =
    set
        [ "op_Addition"
          "op_Subtraction"
          "op_Multiply"
          "op_Division"
          "op_Modulus"
          "op_UnaryNegation" ]

/// Is the expression arithmetic over names and literals only — nothing
/// that can throw but a division? Returns the non-literal divisors. A
/// dotted operand is only as pure as `dottedIsPure` proves it: `opt.Value`,
/// `lazy.Value` and `s.Length` are property getters, and a getter throws.
let rec private pureArithmetic (dottedIsPure: SynExpr -> bool) (e: SynExpr) : (bool * SynExpr list) =
    match e with
    | SynExpr.Paren(expr = inner) -> pureArithmetic dottedIsPure inner
    | SynExpr.Const(SynConst.Unit, _) -> false, []
    | SynExpr.Const _
    | SynExpr.Ident _ -> true, []
    | SynExpr.LongIdent _ -> dottedIsPure e, []
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = l); argExpr = r) when
        arithmeticOps.Contains op.idText
        ->
        let okL, dl = pureArithmetic dottedIsPure l
        let okR, dr = pureArithmetic dottedIsPure r

        let divisor =
            match op.idText, stripParens r with
            | ("op_Division" | "op_Modulus"), SynExpr.Const _ -> []
            | ("op_Division" | "op_Modulus"), d -> [ d ]
            | _ -> []

        okL && okR, dl @ dr @ divisor
    | SynExpr.App(funcExpr = SingleIdent op; argExpr = inner) when op.idText = "op_UnaryNegation" ->
        pureArithmetic dottedIsPure inner
    | _ -> false, []

/// A dotted operand the typed check proves cannot throw when read: every
/// segment a module or namespace, a record (or anonymous record) field, or
/// a plain value — never a member, so no property getter, no `.Value` on
/// an option, a Nullable or a Lazy, no `.Length` on a null string.
let private dottedOperandIsPure (check: FSharpCheckFileResults option) (source: ISourceText) (e: SynExpr) =
    match check, e with
    | Some check, SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
        let safeSymbol (symbol: FSharpSymbol) =
            match symbol with
            | :? FSharpEntity as entity -> entity.IsFSharpModule || entity.IsNamespace
            | :? FSharpField as field ->
                field.IsAnonRecordField
                || (field.DeclaringEntity |> Option.exists (fun entity -> entity.IsFSharpRecord))
            | :? FSharpMemberOrFunctionOrValue as v -> not v.IsMember
            | _ -> false

        let resolves (prefix: Ident list) =
            try
                let id = List.last prefix
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match
                    check.GetSymbolUseAtLocation(
                        r.EndLine,
                        r.EndColumn,
                        lineText,
                        prefix |> List.map (fun i -> i.idText)
                    )
                with
                | Some symbolUse -> safeSymbol symbolUse.Symbol
                | None -> false
            with _ -> // unresolved reads as unsafe; fsharpanalyzer: ignore-line FR0055
                false

        [ 1 .. ids.Length ] |> List.forall (fun n -> resolves (List.take n ids))
    | _ -> false

let private parseTypes =
    set
        [ "Int32"
          "Int64"
          "Int16"
          "Byte"
          "UInt32"
          "UInt64"
          "Double"
          "Single"
          "Decimal"
          "DateTime"
          "DateTimeOffset"
          "TimeSpan"
          "Guid"
          "Boolean" ]

/// `T.Parse arg` / `T.Parse(arg)` with one argument.
let private parseCall (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2
        && (List.last ids).idText = "Parse"
        && parseTypes.Contains ids.[ids.Length - 2].idText
        ->
        match stripParens arg with
        | SynExpr.Tuple _ -> None
        | single -> Some(ids |> List.take (ids.Length - 1) |> identText, single)
    | _ -> None

let private ioSmell =
    Regex(
        @"\b(File|Directory|Path|FileInfo|DirectoryInfo|FileStream|StreamReader|StreamWriter|BinaryReader|BinaryWriter)\b",
        RegexOptions.Compiled
    )

/// The logging idiom this file already uses: the receiver of an MEL call
/// (`logger`), Serilog's static `Log`, or a Logary pipeline's sink text.
type private LogIdiom =
    | Mel of receiver: string
    | Serilog
    | Logary of sink: string

let private melMethods =
    set
        [ "LogError"
          "LogWarning"
          "LogInformation"
          "LogDebug"
          "LogCritical"
          "LogTrace" ]

let private serilogMethods =
    set [ "Error"; "Warning"; "Information"; "Debug"; "Fatal"; "Verbose" ]

let private logIdiomOf (index: AstIndex.Index) (source: ISourceText) =
    let rec stages (e: SynExpr) =
        match e with
        | SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)
            argExpr = right) when op.idText = "op_PipeRight" -> stages left @ [ right ]
        | other -> [ other ]

    index.Exprs
    |> Array.tryPick (fun (_, e) ->
        match e with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
            ids.Length >= 2 && melMethods.Contains (List.last ids).idText
            ->
            Some(Mel(ids |> List.take (ids.Length - 1) |> identText))
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ]))) when
            melMethods.Contains m.idText
            ->
            Some(Mel(textOfRange source recv.Range))
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ l; m ]))) when
            l.idText = "Log" && serilogMethods.Contains m.idText
            ->
            Some Serilog
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) when
            op.idText = "op_PipeRight"
            ->
            let chain = stages e

            let isLogaryEvent (s: SynExpr) =
                match s with
                | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                    ids.Length >= 2
                    && ids.[ids.Length - 2].idText = "Message"
                    && (List.last ids).idText.StartsWith "event"
                | _ -> false

            if chain |> List.exists isLogaryEvent then
                Some(Logary(textOfRange source (List.last chain).Range))
            else
                None
        | _ -> None)

/// The enclosing binding's name and parameter names, from the path.
let private enclosingFunction (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynBinding(SynBinding(
            headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats args))) when
            not ids.IsEmpty
            ->
            Some((List.last ids).idText, args |> List.collect patBoundNames)
        | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)))) ->
            Some(id.idText, [])
        | _ -> None)

/// The log statement, in the idiom, for an exception bound to `ex`.
let private logLine (idiom: LogIdiom) (ex: string) (method': string) (parameters: string list) =
    let placeholders =
        match parameters with
        | [] -> ""
        | [ p ] -> $" with parameter {{{p}}}"
        | ps ->
            " with parameters "
            + (ps |> List.map (fun p -> "{" + p + "}") |> String.concat " ")

    let template = $"Exception: {{Message}} in method {{Method}}{placeholders}"

    match idiom with
    | Mel receiver ->
        let args = [ $"{ex}.Message"; $"\"{method'}\"" ] @ parameters |> String.concat ", "
        $"{receiver}.LogError({ex}, \"{template}\", {args})"
    | Serilog ->
        let args = [ $"{ex}.Message"; $"\"{method'}\"" ] @ parameters |> String.concat ", "
        $"Log.Error({ex}, \"{template}\", {args})"
    | Logary sink ->
        let fields =
            [ $"Message\" {ex}.Message"; $"Method\" \"{method'}\"" ]
            @ (parameters |> List.map (fun p -> $"{p}\" {p}"))
            |> List.map (fun f -> $" |> Message.setField \"{f}")
            |> String.concat ""

        $"Message.eventError \"{template}\"{fields} |> Message.addExn {ex} |> {sink}"

/// The zero of a divisor's type, as F# spells it — `0`, `0L`, `0uy` — from
/// the typed check; None when the type is unknown or has no literal zero,
/// and the guard is not offered. Floats are left out on purpose: float
/// division never throws (it yields infinity or NaN), so the catch was
/// never reached and a guard would change the result, not remove a catch.
/// Decimals too: decimal `+`, `*` and even `/` throw OverflowException, so
/// the catch guarded more than the division and a zero check cannot
/// replace it.
let private zeroOf (check: FSharpCheckFileResults option) (source: ISourceText) (divisor: SynExpr) =
    let ident =
        match divisor with
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    match check, ident with
    | Some check, Some id ->
        let r = id.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        let names =
            match divisor with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> ids |> List.map (fun i -> i.idText)
            | _ -> [ id.idText ]

        let zeroOfType (declared: FSharpType) =
            try
                let t = OptionModule.stripAbbreviations declared

                match
                    (if t.HasTypeDefinition then
                         t.TypeDefinition.TryFullName
                     else
                         None)
                with
                | Some "System.Int32" -> Some "0"
                | Some "System.Int64" -> Some "0L"
                | Some "System.Int16" -> Some "0s"
                | Some "System.Byte" -> Some "0uy"
                | Some "System.SByte" -> Some "0y"
                | Some "System.UInt32" -> Some "0u"
                | Some "System.UInt64" -> Some "0UL"
                | Some "System.UInt16" -> Some "0us"
                | _ -> None
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                None

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, names) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v -> zeroOfType v.FullType
            // a record field divisor (`r.Count`): the operand check has
            // already proven the read pure
            | :? FSharpField as f -> zeroOfType f.FieldType
            | _ -> None
        | None -> None
    | _ -> None

/// The test frameworks whose files this rule leaves alone: a swallowed
/// exception in a test is a different habit from one in a service, and the
/// test runner reports the failure either way.
/// The shared answer (AstIndex.isTestFile): a test framework's `open`, a
/// test attribute, or an Expecto test builder.
let isTestFile (index: AstIndex.Index) (source: ISourceText) = AstIndex.isTestFile index source

/// Find empty and default-substituting catch-all handlers.
/// A comment on the handler is the author acknowledging the swallow —
/// `with _ -> () // content length is not important` (Owin.Compression),
/// `with _ -> () // best-effort icon` (Kasino) — a decision, not an
/// accident, and not worth a note.
let private acknowledged (source: ISourceText) (clause: SynMatchClause) (result: SynExpr) =
    let commented (line: int) =
        let text = source.GetLineString(line - 1)
        let i = text.IndexOf "//"

        i > 0
        && (text.Substring(0, i) |> Seq.filter (fun c -> c = '"') |> Seq.length) % 2 = 0

    commented clause.Range.StartLine || commented result.Range.EndLine

/// A union case that CARRIES the failure rather than hiding it: `Error "x"`,
/// `Failure "x"`, `Choice2Of2 ""`, a user's `ParseError ""`. The bare
/// `with _ -> Error "x"` is quiet already; a tuple or record slot holding
/// one reports the failure just the same.
let private carriesFailure (case: string) =
    case = "Choice2Of2"
    || case.EndsWith "Error"
    || case.EndsWith "Failure"
    || case.EndsWith "Failed"

/// A slot that IS a default: bare, or a union case wrapping one
/// (`Completed None`).
let private carriesDefault (e: SynExpr) =
    match stripParens e with
    | IsDefaultFallback _ -> true
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident case; argExpr = arg) when
        case.idText.Length > 0
        && System.Char.IsUpper case.idText.[0]
        && not (carriesFailure case.idText)
        ->
        isDefaultFallback (stripParens arg)
    | _ -> false

/// One slot of a tuple or record fallback: a default, or a name.
let private isValueSlot (e: SynExpr) =
    match stripParens e with
    | SynExpr.Ident _
    | SynExpr.LongIdent _ -> true
    | other -> carriesDefault other

/// A fallback that hands back a value in place of the failure: a default
/// literal, a variable (`with _ -> path` returns the input as if the work
/// had succeeded — fsi), or a tuple or record carrying a default in one of
/// its slots (`with _ -> (istate, Completed None)`).
let rec private isValueFallback (e: SynExpr) =
    match stripParens e with
    | IsDefaultFallback _ -> true
    | SynExpr.Ident _ -> true
    | SynExpr.Tuple(exprs = items) -> items |> List.forall isValueSlot && items |> List.exists carriesDefault
    | SynExpr.Record(recordFields = fields) ->
        let values = fields |> List.choose (fun (SynExprRecordField(expr = v)) -> v)

        values |> List.forall isValueSlot && values |> List.exists carriesDefault
    | _ -> false



/// Teardown methods: a best-effort release whose failure the caller has
/// nowhere to report.
let private teardownMethods =
    set
        [ "dispose"
          "close"
          "shutdown"
          "cancel"
          "complete"
          "delete"
          "reset"
          "abort"
          "disconnect"
          "kill"
          "release"
          "unregister" ]

/// The method name a call applies: `x.Dispose()`, `File.Delete path`,
/// `conn.shutdown()`.
let private calledMethod (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = f) ->
        match f with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idText
        | _ -> None
    | _ -> None

/// `x <- null` after the release.
let private isNullAssignment (e: SynExpr) =
    match stripParens e with
    | SynExpr.LongIdentSet(expr = SynExpr.Null _)
    | SynExpr.Set(rhsExpr = SynExpr.Null _)
    | SynExpr.DotSet(rhsExpr = SynExpr.Null _) -> true
    | _ -> false

/// `try x.Dispose() with _ -> ()`, or the same followed by `x <- null`.
let private isTeardown (tryBody: SynExpr) =
    let releases (e: SynExpr) =
        calledMethod e
        |> Option.exists (fun m -> teardownMethods.Contains(m.ToLowerInvariant()))

    match stripParens tryBody with
    | SynExpr.Sequential(expr1 = e1; expr2 = e2) -> releases e1 && isNullAssignment e2
    | body -> releases body

/// Probes that answer for a missing path instead of throwing (they still
/// throw for a malformed one): a try around them adds nothing.
let private probeApis =
    set
        [ "File.Exists"
          "Directory.Exists"
          "Path.Exists"
          "File.GetLastWriteTime"
          "File.GetLastWriteTimeUtc"
          "File.GetCreationTime"
          "File.GetCreationTimeUtc"
          "File.GetLastAccessTime"
          "File.GetLastAccessTimeUtc"
          "Directory.GetLastWriteTime"
          "Directory.GetLastWriteTimeUtc"
          "Directory.GetCreationTime"
          "Directory.GetCreationTimeUtc" ]

let private probeOf (tryBody: SynExpr) =
    match stripParens tryBody with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        ids.Length >= 2
        ->
        let name = ids.[ids.Length - 2].idText + "." + (List.last ids).idText
        if probeApis.Contains name then Some name else None
    | _ -> None

/// An earlier arm of the same `with` that re-raises cancellation: the
/// catch-all after it is no longer blind to the one exception the rule
/// worries about most (the compiler's NameResolution).
let private cancellationRethrown (earlier: SynMatchClause list) =
    let isCancellation (p: SynPat) =
        let named (ids: Ident list) =
            not ids.IsEmpty
            && (match (List.last ids).idText with
                | "OperationCanceledException"
                | "TaskCanceledException" -> true
                | _ -> false)

        match p with
        | SynPat.IsInst(SynType.LongIdent(SynLongIdent(id = ids)), _)
        | SynPat.As(lhsPat = SynPat.IsInst(SynType.LongIdent(SynLongIdent(id = ids)), _)) -> named ids
        | _ -> false

    let rethrows (e: SynExpr) =
        match stripParens e with
        | SynExpr.App(funcExpr = SynExpr.Ident f) ->
            (match f.idText with
             | "reraise"
             | "raise"
             | "rethrow" -> true
             | _ -> false)
        | _ -> false

    earlier
    |> List.exists (fun (SynMatchClause(pat = p; resultExpr = r)) -> isCancellation p && rethrows r)

/// The statement after the try, when the try is the first half of a
/// sequence: `try Environment.Exit n with _ -> ()` followed by `failwith`
/// converts the swallow into a failure (DiagnosticsLogger's exiter).
let private continuationRaises (path: SyntaxNode list) (tryRange: range) =
    let raises (e: SynExpr) =
        let rec first (e: SynExpr) =
            match e with
            | SynExpr.Sequential(expr1 = e1) -> first e1
            | SynExpr.Paren(expr = inner) -> first inner
            | _ -> e

        match first e with
        | SynExpr.App(funcExpr = SynExpr.Ident f)
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SynExpr.Ident f)) ->
            (match f.idText with
             | "failwith"
             | "failwithf"
             | "raise"
             | "reraise"
             | "invalidOp"
             | "invalidArg"
             | "nullArg" -> true
             | _ -> false)
        | _ -> false

    match path with
    | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = e1; expr2 = e2)) :: _ when Range.equals e1.Range tryRange ->
        raises e2
    | _ -> false

[<return: Struct>]
let inline private (|IsValueFallback|_|) input =
    if isValueFallback input then ValueSome input else ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults option) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let idiom = lazy (logIdiomOf index source)

    // a test file yields nothing to walk
    let exprs = if isTestFile index source then [||] else index.Exprs

    let dottedIsPure = dottedOperandIsPure check source

    // under `open Checked` (Microsoft.FSharp.Core.Operators.Checked) every
    // `+`, `-` and `*` throws OverflowException, so the catch guarded more
    // than the division and no zero check can stand in for it
    let checkedOpen =
        index.Decls
        |> Array.exists (fun (_, d) ->
            match d with
            | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                not ids.IsEmpty && (List.last ids).idText = "Checked"
            | _ -> false)

    [ for path, expr in exprs do
          match expr with
          | SynExpr.TryWith(tryExpr = tryBody; withCases = clauses) when not (continuationRaises path expr.Range) ->
              for i, clause in List.indexed clauses do
                  // a guard that never looks at the exception (`with _ when
                  // watch -> ()`) still swallows every one of them; a guard
                  // on the exception itself is a decision
                  let guarded =
                      match clause with
                      | SynMatchClause(pat = pat; whenExpr = Some whenGuard; resultExpr = result) ->
                          let guardText = textOfRange source whenGuard.Range

                          match binderOf pat with
                          | Some name when Regex.IsMatch(guardText, $@"\b{Regex.Escape name}\b") -> None
                          | _ -> Some(pat, result, Some whenGuard)
                      | SynMatchClause(pat = pat; whenExpr = None; resultExpr = result) -> Some(pat, result, None)

                  match guarded with
                  | Some(pat, result, whenGuard) when
                      isCatchAll pat
                      && not (acknowledged source clause result)
                      && not (cancellationRethrown (List.take i clauses))
                      ->
                      let fallback =
                          match stripParens result with
                          | UnitConst -> Some None
                          | SynExpr.Const(SynConst.Bool b, _) as body when not (isBoolProbe tryBody b) ->
                              Some(Some(textOfRange source body.Range))
                          // a tuple keeps its parentheses: `(istate, Completed None)`
                          | SynExpr.Tuple _ as body when isValueFallback body ->
                              Some(Some(textOfRange source result.Range))
                          | IsValueFallback body -> Some(Some(textOfRange source body.Range))
                          | _ -> None

                      match fallback with
                      | Some fallbackText ->
                          let bodyText = textOfRange source tryBody.Range

                          let patText =
                              match whenGuard with
                              | Some g -> textOfRange source (Range.unionRanges pat.Range g.Range)
                              | None -> textOfRange source pat.Range

                          // 1. the guard: pure arithmetic, one non-literal
                          // divisor, nothing else that throws
                          let guard =
                              match fallbackText, pureArithmetic dottedIsPure (stripParens tryBody) with
                              | Some fb, (true, [ divisor ]) when isSingleLine tryBody.Range && not checkedOpen ->
                                  // the zero is the divisor's own — 0, 0L,
                                  // 0uy — from the typed check; without the
                                  // type (or for a float or decimal) the
                                  // guard is not offered
                                  match zeroOf check source divisor with
                                  | Some zero ->
                                      let d = textOfRange source divisor.Range

                                      [ { Label =
                                            $"Fix: guard the division instead of catching — `if {d} = {zero} then {fb} else ...`; the catch goes, nothing else in the body throws"
                                          Edits =
                                            [ expr.Range,
                                              textOfRange source expr.Range,
                                              $"if {d} = {zero} then {fb} else {bodyText}" ] } ]
                                  | None -> []
                              | _ -> []

                          // 2. TryParse, for a one-call Parse body
                          let tryParse =
                              match fallbackText, parseCall tryBody with
                              | Some fb, Some(typeName, arg) ->
                                  let a = textOfRange source arg.Range

                                  let a =
                                      match arg with
                                      | SynExpr.Ident _
                                      | SynExpr.Const _
                                      | SynExpr.LongIdent _ -> a
                                      | _ -> $"({a})"

                                  let success, failure =
                                      match fb with
                                      | "None" -> "Some v", "None"
                                      | "ValueNone" -> "ValueSome v", "ValueNone"
                                      | other -> "v", other

                                  let pad = String.replicate expr.Range.StartColumn " "

                                  [ { Label =
                                        $"Fix: {typeName}.TryParse instead of a catch — the parse failing is the expected case, not an exception"
                                      Edits =
                                        [ expr.Range,
                                          textOfRange source expr.Range,
                                          $"match {typeName}.TryParse {a} with\n{pad}| true, v -> {success}\n{pad}| _ -> {failure}" ] } ]
                              | _ -> []

                          // 3. a narrower catch for file IO — for a body that IS the IO call: a
                          // multi-line body mentioning a Path beside native calls (Kasino's
                          // SDL icon) throws more than IOException
                          let narrower =
                              if ioSmell.IsMatch bodyText && isSingleLine tryBody.Range then
                                  let narrowed =
                                      match binderOf pat with
                                      | Some name ->
                                          $"(:? System.IO.IOException | :? System.UnauthorizedAccessException) as {name}"
                                      | None -> ":? System.IO.IOException | :? System.UnauthorizedAccessException"

                                  [ { Label =
                                        "Alternative: catch the IO exceptions only — IOException and UnauthorizedAccessException — and let the rest surface"
                                      Edits = [ pat.Range, patText, narrowed ] } ]
                              else
                                  []

                          // 4. a log line in the file's own idiom — when its
                          // receiver is reachable from THIS catch: a parameter
                          // of the enclosing function, a module-level value, a
                          // class `let`, or a local `let` whose scope holds the
                          // site (Fuuga: a `logger` from one function was written
                          // into six functions that have none)
                          let receiverInScope (idiom: LogIdiom) =
                              match idiom with
                              | Mel receiver ->
                                  let root = receiver.Split('.').[0]

                                  // the VALUE a binding defines, not a function's parameters:
                                  // those are in scope only inside that function
                                  let bindsRoot (SynBinding(headPat = p)) =
                                      match p with
                                      | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = root
                                      | SynPat.LongIdent(
                                          longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                                          id.idText = root
                                      | _ -> false

                                  let parameters = enclosingFunction path |> Option.map snd |> Option.defaultValue []

                                  root = "this"
                                  || root = "self"
                                  || List.contains root parameters
                                  || index.Decls
                                     |> Array.exists (fun (_, d) ->
                                         match d with
                                         // defined ABOVE the site: F# scopes top-down
                                         | SynModuleDecl.Let(bindings = bs) when
                                             d.Range.EndLine < clause.Range.StartLine
                                             ->
                                             bs |> List.exists bindsRoot
                                         | SynModuleDecl.Types(typeDefns = defns) ->
                                             defns
                                             |> List.exists (fun (SynTypeDefn(typeRepr = repr; range = tr)) ->
                                                 Range.rangeContainsRange tr clause.Range
                                                 && (match repr with
                                                     | SynTypeDefnRepr.ObjectModel(members = ms) ->
                                                         ms
                                                         |> List.exists (fun m ->
                                                             match m with
                                                             | SynMemberDefn.LetBindings(bindings = bs) ->
                                                                 bs |> List.exists bindsRoot
                                                             | _ -> false)
                                                     | _ -> false))
                                         | _ -> false)
                                  || index.Exprs
                                     |> Array.exists (fun (_, e) ->
                                         match e with
                                         | LetOrUseE lou when Range.rangeContainsRange e.Range clause.Range ->
                                             lou.Bindings |> List.exists bindsRoot
                                         | _ -> false)
                              | Serilog
                              | Logary _ -> true

                          // the exception's name for the log line: the
                          // handler's own binder, or for `_` and a bare
                          // `:? Exception` a fresh one — `ex` unless the
                          // enclosing declaration already says `ex`, in which
                          // case the fallback (or the log line's parameters)
                          // could name the wrong one
                          let binder =
                              match binderOf pat with
                              | Some name -> Some name
                              | None ->
                                  let scope =
                                      path
                                      |> List.tryPick (fun node ->
                                          match node with
                                          | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                                          | _ -> None)

                                  let text =
                                      match scope with
                                      | Some r -> textOfRange source r
                                      | None ->
                                          String.concat
                                              "\n"
                                              [ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ]

                                  [ "ex"; "exn"; "err" ]
                                  |> List.tryFind (fun candidate ->
                                      not (Regex.IsMatch(text, identifierPattern candidate)))

                          let logging =
                              match idiom.Value, binder with
                              | Some idiom, Some ex when receiverInScope idiom ->
                                  let method', parameters = enclosingFunction path |> Option.defaultValue ("?", [])

                                  // the logger itself is not a parameter worth
                                  // logging
                                  let parameters =
                                      match idiom with
                                      | Mel receiver -> parameters |> List.filter (fun p -> p <> receiver)
                                      | Logary sink -> parameters |> List.filter (fun p -> not (sink.Contains p))
                                      | Serilog -> parameters

                                  let line = logLine idiom ex method' parameters

                                  // a fallback already on its own line keeps its column and
                                  // gets the log line above it; one after the arrow moves
                                  // down under the clause with the log line first
                                  let onOwnLine = result.Range.StartLine > clause.Range.StartLine

                                  let indent =
                                      if onOwnLine then
                                          String.replicate result.Range.StartColumn " "
                                      else
                                          String.replicate (clause.Range.StartColumn + 4) " "

                                  let prefix = if onOwnLine then "" else $"\n{indent}"

                                  let bindEdit =
                                      match pat with
                                      | SynPat.Wild _ -> [ pat.Range, patText, ex ]
                                      // `:? Exception` binds nothing: without
                                      // `as ex` the log line's `ex` is FS0039
                                      | SynPat.IsInst _ ->
                                          let original = textOfRange source pat.Range
                                          [ pat.Range, original, $"{original} as {ex}" ]
                                      | _ -> []

                                  let bodyEdit =
                                      match stripParens result with
                                      | UnitConst ->
                                          [ result.Range, textOfRange source result.Range, $"{prefix}{line}" ]
                                      | _ ->
                                          [ result.Range,
                                            textOfRange source result.Range,
                                            $"{prefix}{line}\n{indent}{textOfRange source result.Range}" ]

                                  [ { Label =
                                        $"Alternative: log it the way this file logs — the exception, the method '{method'}' and its parameters — before the fallback"
                                      Edits = bindEdit @ bodyEdit } ]
                              | _ -> []

                          { Range = clause.Range
                            PatternText = patText
                            FallbackText = fallbackText
                            Teardown = fallbackText.IsNone && isTeardown tryBody
                            Probe = probeOf tryBody
                            Offers = guard @ tryParse @ narrower @ logging }
                      | None -> ()
                  | _ -> ()
          | _ -> () ]
