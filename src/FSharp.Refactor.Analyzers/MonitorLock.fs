/// FR0123 (fix): the canonical Monitor.Enter/try/finally/Monitor.Exit
/// shape IS F#'s `lock` function — which releases on all paths by
/// construction, closing the whole released-on-every-path rule family
/// at the source.
///
///     Monitor.Enter gate                lock gate (fun () ->
///     try                                   body
///         body                          )
///     finally
///         Monitor.Exit gate
///
/// The body under `try` already sits at exactly the indentation the
/// lambda needs, so it moves VERBATIM — comments included.
///
/// Gates: single-argument Enter (the `(x, &taken)` overload carries
/// protocol this rewrite would erase), the SAME lock expression text in
/// Enter and Exit, the finally holding nothing but the Exit, own-line
/// statements, and the Monitor entity typed-verified. A bare
/// Monitor.Enter with no try/finally at all is the note: the lock leaks
/// on the first exception.
///
/// The same leak under other names (findLeaks): `SemaphoreSlim
/// .Wait/WaitAsync` without `finally Release`, `ReaderWriterLockSlim
/// .Enter*Lock` without `finally Exit*Lock`, `Mutex.WaitOne` without
/// `finally ReleaseMutex` — an acquire followed by its body with no
/// try/finally (after it, or around it) spelling the release on the same
/// receiver. A `use` after the acquire whose binding spells the release,
/// and a `let`/`let!` whose right-hand side or body holds the try, count
/// as the guard. An acquire that ends its block protects nothing and
/// stays quiet: it is a wrapper whose caller decides. Where the release
/// is a statement of the same block, the statements between move under
/// a `try` and the release into its `finally` (fixFor's gates); anywhere
/// else the note stands alone.
module FSharp.Refactor.MonitorLock

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// Present for the canonical shape: whole-region replacement.
        Fix: (range * string * string) option
        LockText: string
        /// True when a try/finally with the matching Exit guards the Enter
        /// — the lock cannot leak; only the `lock` rewrite is on offer, or
        /// withheld when a gate (a computation bind, a foreign mutable, a
        /// directive) blocks it. False for a bare Enter, the actual leak.
        Guarded: bool
    }

/// `Monitor.<method> arg` with the single argument expression.
[<return: Struct>]
let private (|MonitorCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2 && (ids |> List.item (ids.Length - 2)).idText = "Monitor"
        ->
        match stripParens arg with
        | SynExpr.Tuple _ -> ValueNone // Enter(x, &taken) carries protocol
        | single -> ValueSome((List.last ids), single)
    | _ -> ValueNone

let private isMonitorEntity (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as mfv ->
            (try
                mfv.DeclaringEntity
                |> Option.bind (fun e -> e.TryFullName)
                |> Option.map ((=) "System.Threading.Monitor")
                |> Option.defaultValue false
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false
    | None -> false

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the rewrite wraps the body in a LAMBDA: computation binds
        // (do!/let!/yield) stop compiling there, and a closure cannot
        // capture a local mutable declared outside itself
        let bindLikeRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | LetOrUseE lou when lou.IsBang -> Some e.Range
                | SynExpr.DoBang _
                | SynExpr.YieldOrReturn _
                | SynExpr.YieldOrReturnFrom _
                | SynExpr.MatchBang _ -> Some e.Range
                | _ -> None)

        let containsBindLike (r: range) =
            bindLikeRanges |> Array.exists (fun b -> Range.rangeContainsRange r b)

        let localMutables =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | LetOrUseE lou when not lou.IsBang ->
                    lou.Bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(isMutable = true; headPat = SynPat.Named(ident = SynIdent(ident = id))) ->
                            Some(id.idText, b.RangeOfBindingWithRhs)
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])

        let mentionsForeignMutable (blockRange: range) (text: string) =
            localMutables
            |> Array.exists (fun (name, declRange) ->
                not (Range.rangeContainsRange blockRange declRange)
                && System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern name))

        let startsOwnLine (r: range) =
            r.StartColumn = 0
            || (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = ""

        let lineTailBlank (r: range) =
            (source.GetLineString(r.EndLine - 1)).Substring(r.EndColumn).Trim() = ""

        // Enter statements followed by a guarding try/finally, per the
        // canonical Sequential(Enter, TryFinally(body, Exit)) chain
        let guarded = System.Collections.Generic.HashSet<int * int>()

        // the try/finally that follows the Enter — either the rest of the
        // block, or the FIRST statement of it when more follows (FCS's
        // `InlineDelayInit.Value` reads `value` after the finally: the
        // Sequential then nests the TryFinally one level down, which the
        // direct shape missed and reported as a bare Enter)
        let (|GuardingTry|_|) (e: SynExpr) =
            match e with
            | SynExpr.TryFinally(tryExpr = body; finallyExpr = MonitorCall(exitId, exitArg); trivia = tfTrivia)
            | SynExpr.Sequential(
                expr1 = SynExpr.TryFinally(tryExpr = body; finallyExpr = MonitorCall(exitId, exitArg); trivia = tfTrivia)) when
                exitId.idText = "Exit"
                ->
                let tf =
                    match e with
                    | SynExpr.Sequential(expr1 = tf) -> tf
                    | _ -> e

                Some(body, exitArg, tfTrivia, tf)
            | _ -> None

        let canonical =
            [
                for _, e in index.Exprs do
                    match e with
                    | SynExpr.Sequential(
                        expr1 = MonitorCall(enterId, lockArg) & enterExpr
                        expr2 = GuardingTry(body, exitArg, tfTrivia, tf)) when enterId.idText = "Enter" ->
                        guarded.Add(enterExpr.Range.StartLine, enterExpr.Range.StartColumn) |> ignore

                        let lockText = textOfRange source lockArg.Range
                        let tryLine = tfTrivia.TryKeyword.StartLine
                        let finallyLine = tfTrivia.FinallyKeyword.StartLine

                        let fix =
                            if
                                lockText = textOfRange source exitArg.Range
                                && isMonitorEntity check source enterId
                                && startsOwnLine enterExpr.Range
                                && startsOwnLine tfTrivia.TryKeyword
                                && startsOwnLine tfTrivia.FinallyKeyword
                                // body strictly between the keyword lines, so
                                // every line — comments included — travels
                                && body.Range.StartLine > tryLine
                                && body.Range.EndLine < finallyLine
                                && lineTailBlank body.Range
                                && not (containsBindLike body.Range)
                                && not (spansDirective source e.Range)
                            then
                                let indent = String.replicate enterExpr.Range.StartColumn " "

                                let bodyLines =
                                    [ for l in tryLine + 1 .. finallyLine - 1 -> source.GetLineString(l - 1) ]
                                    |> String.concat "\n"

                                let replaceRange = Range.mkRange e.Range.FileName enterExpr.Range.Start tf.Range.End

                                let bodyRegion =
                                    Range.mkRange
                                        e.Range.FileName
                                        (Position.mkPos (tryLine + 1) 0)
                                        (Position.mkPos finallyLine 0)

                                if mentionsForeignMutable bodyRegion bodyLines then
                                    // the lambda could not capture it (FS0407)
                                    None
                                else
                                    // fantomas closes the lambda at the end of its
                                    // last line, not on a line of its own — unless
                                    // that line ends in a comment, which would
                                    // swallow the paren
                                    let body = bodyLines.TrimEnd()
                                    let lastLine = body.Substring(body.LastIndexOf '\n' + 1)

                                    let closing = if lastLine.Contains "//" then $"\n{indent})" else ")"

                                    Some(
                                        replaceRange,
                                        textOfRange source replaceRange,
                                        $"lock {lockText} (fun () ->\n{body}{closing}"
                                    )
                            else
                                None

                        yield
                            {
                                Range = enterExpr.Range
                                Fix = fix
                                LockText = lockText
                                Guarded = true
                            }
                    | _ -> ()
            ]

        // bare Enter with no guarding try at all: leaks on first exception
        let bare =
            [
                for _, e in index.Exprs do
                    match e with
                    | MonitorCall(enterId, lockArg) when
                        enterId.idText = "Enter"
                        && not (guarded.Contains(e.Range.StartLine, e.Range.StartColumn))
                        && isMonitorEntity check source enterId
                        ->
                        {
                            Range = e.Range
                            Fix = None
                            LockText = textOfRange source lockArg.Range
                            Guarded = false
                        }
                    | _ -> ()
            ]

        canonical @ bare

// ---- the other acquire/release pairs ----

/// A slot or lock taken by a call whose release is not in a `finally`:
/// `sem.Wait()` / `do! sem.WaitAsync()` / `rw.EnterReadLock()` /
/// `mutex.WaitOne()` followed by the protected body without a
/// `try ... finally <receiver>.Release()` around it. The Monitor leak note
/// with different names: the first exception in the body leaks the slot,
/// and every later waiter blocks forever.
type LeakSuggestion =
    {
        /// The acquiring call.
        Range: range
        /// `sem.Wait()` as written.
        AcquireText: string
        /// `sem.Release()` — what the finally should hold.
        ReleaseText: string
        /// The try/finally around the statements up to the release, where
        /// the shape allows it (see fixFor); otherwise the note stands alone.
        Fix: (range * string * string) option
    }

/// acquire method → (declaring type, release method)
let private acquirePairs =
    dict
        [
            "Wait", ("System.Threading.SemaphoreSlim", "Release")
            "WaitAsync", ("System.Threading.SemaphoreSlim", "Release")
            "EnterReadLock", ("System.Threading.ReaderWriterLockSlim", "ExitReadLock")
            "EnterWriteLock", ("System.Threading.ReaderWriterLockSlim", "ExitWriteLock")
            "EnterUpgradeableReadLock", ("System.Threading.ReaderWriterLockSlim", "ExitUpgradeableReadLock")
            "WaitOne", ("System.Threading.Mutex", "ReleaseMutex")
        ]

/// `recv.Method args` for a method in acquirePairs: the method identifier,
/// the receiver's text and the receiver's last identifier when it has one
/// (the typed check reads the receiver's type through it).
[<return: Struct>]
let private (|AcquireCall|_|) (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        ids.Length >= 2 && acquirePairs.ContainsKey (List.last ids).idText
        ->
        let receiver = ids |> List.take (ids.Length - 1)
        ValueSome(List.last ids, identText receiver, Some(List.last receiver))
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ]))) when
        acquirePairs.ContainsKey m.idText
        ->
        let receiverId =
            match stripParens recv with
            | SynExpr.Ident id -> Some id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | _ -> None

        ValueSome(m, textOfRange source recv.Range, receiverId)
    | _ -> ValueNone

/// The acquiring call at the head of a statement: bare, or under `do!`,
/// possibly piped on (`do! sem.WaitAsync() |> Async.AwaitTask`).
[<TailCall>]
let rec private statementHead (e: SynExpr) =
    match e with
    | SynExpr.DoBang(expr = inner) -> statementHead inner
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)) when
        op.idText = "op_PipeRight"
        ->
        statementHead left
    | SynExpr.Paren(expr = inner) -> statementHead inner
    | _ -> e

let findLeaks (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : LeakSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let symbolAt (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv -> Some mfv
                | _ -> None
            | None -> None

        // the method is the expected type's own member
        let declaredOn (expected: string) (ident: Ident) =
            match symbolAt ident with
            | Some mfv ->
                (try
                    mfv.IsMember
                    && (mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.map ((=) expected)
                        |> Option.defaultValue false)
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

        // the receiver's own type is the expected one: `WaitOne` is
        // WaitHandle's, shared with events that have nothing to release
        let receiverIs (expected: string) (receiver: Ident option) =
            match receiver |> Option.bind symbolAt with
            | Some mfv ->
                (try
                    mfv.FullType.StripAbbreviations().TypeDefinition.TryFullName = Some expected
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

        let typedGate (entity: string) (methodId: Ident) (receiver: Ident option) =
            if methodId.idText = "WaitOne" then
                receiverIs entity receiver
            else
                declaredOn entity methodId

        // the release spelled on the same receiver, anywhere in a text
        let releases (receiver: string) (release: string) (text: string) =
            System.Text.RegularExpressions.Regex.IsMatch(
                text,
                identifierPattern receiver + @"\s*\.\s*" + release + @"(?![\w'])"
            )

        // the statement after the acquire guards it when it is (or starts
        // with) a try/finally releasing the receiver, or a `use` whose
        // binding releases it on dispose
        // A `let` between the acquire and the try (`let mutable acquired = 0`
        // before a counted multi-acquire, Fuuga) is looked through to its
        // body; a `let`/`let!` whose right-hand side holds the try — the
        // `let! result = async { try ... finally sem.Release() }` idiom — or
        // a `use` whose binding releases on dispose, is the guard itself
        let rec guardsNext receiver release (next: SynExpr) =
            match next with
            | SynExpr.TryFinally(finallyExpr = f) -> releases receiver release (textOfRange source f.Range)
            | SynExpr.Sequential(expr1 = first) -> guardsNext receiver release first
            | LetOrUseE lou ->
                lou.Bindings
                |> List.exists (fun b -> releases receiver release (textOfRange source b.RangeOfBindingWithRhs))
                || guardsNext receiver release lou.Body
            | _ -> false

        // an enclosing try whose finally releases the receiver guards an
        // acquire that sits inside its body
        let guardedAbove receiver release (path: SyntaxNode list) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.TryFinally(finallyExpr = f)) ->
                    releases receiver release (textOfRange source f.Range)
                | _ -> false)

        // The fix, where the shape allows: the statements between the acquire
        // and the FIRST release of the receiver in the same block become the
        // `try` body, the release the `finally` — as CR0163 spells it. Gates:
        // a release statement exists in the block at the acquire's column,
        // nothing between it and the acquire binds a name (`let`/`let!`/`use`
        // would scope it out of what follows) unless nothing follows the
        // release, nothing between acquires or releases the receiver again,
        // every statement starts its own line and the release ends its own,
        // no string literal or directive spans the lines that move (the body
        // is re-indented by four)
        let lineTailBlank (r: range) =
            (source.GetLineString(r.EndLine - 1)).Substring(r.EndColumn).Trim() = ""

        let fixFor (acquire: SynExpr) (receiver: string) (release: string) (next: SynExpr) =
            // the block after the acquire, one statement per entry; a `let`
            // is one statement, its body the rest of the block
            let rec statements (e: SynExpr) =
                match e with
                | SynExpr.Sequential(expr1 = a; expr2 = b) -> a :: statements b
                | LetOrUseE lou -> e :: statements lou.Body
                | last -> [ last ]

            let isRelease (s: SynExpr) =
                match statementHead s with
                | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                    ids.Length >= 2 && (List.last ids).idText = release
                    ->
                    identText (ids |> List.take (ids.Length - 1)) = receiver
                | SynExpr.App(
                    isInfix = false; funcExpr = SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ]))) when
                    m.idText = release
                    ->
                    textOfRange source recv.Range = receiver
                | _ -> false

            let binds (s: SynExpr) =
                match s with
                | LetOrUseE _ -> true
                | _ -> false

            // a statement's own text: a `let`'s range runs to the end of the
            // block, so only its bindings are its own
            let ownText (s: SynExpr) =
                match s with
                | LetOrUseE lou ->
                    lou.Bindings
                    |> List.map (fun b -> textOfRange source b.RangeOfBindingWithRhs)
                    |> String.concat "\n"
                | _ -> textOfRange source s.Range

            let touchesReceiver (s: SynExpr) =
                let text = ownText s

                System.Text.RegularExpressions.Regex.IsMatch(
                    text,
                    identifierPattern receiver
                    + @"\s*\.\s*("
                    + release
                    + "|"
                    + String.concat "|" (List.ofSeq acquirePairs.Keys)
                    + @")(?![\w'])"
                )

            let ownLine (r: range) =
                (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = ""

            let chain = statements next

            match chain |> List.tryFindIndex isRelease with
            | Some k when k > 0 ->
                let body = chain |> List.take k
                let releaseStatement = chain.[k]
                let after = chain |> List.skip (k + 1)
                let indent = acquire.Range.StartColumn

                let region =
                    Range.mkRange
                        acquire.Range.FileName
                        (Position.mkPos body.Head.Range.StartLine 0)
                        releaseStatement.Range.End

                let multiLineLiteral =
                    index.Exprs
                    |> Array.exists (fun (_, e) ->
                        match e with
                        | SynExpr.Const(SynConst.String _, r)
                        | SynExpr.InterpolatedString(range = r) ->
                            Range.rangeContainsRange region r && r.StartLine <> r.EndLine
                        | _ -> false)

                // the last body statement's own lines; a `let` statement's
                // range covers its body, so the line before the release is
                // the body's last line
                let bodyLastLine = releaseStatement.Range.StartLine - 1

                if
                    (after.IsEmpty || not (body |> List.exists binds))
                    && not (body |> List.exists touchesReceiver)
                    && body |> List.forall (fun s -> s.Range.StartColumn = indent && ownLine s.Range)
                    && releaseStatement.Range.StartColumn = indent
                    && ownLine releaseStatement.Range
                    && lineTailBlank releaseStatement.Range
                    && body.Head.Range.StartLine > acquire.Range.EndLine
                    && bodyLastLine >= body.Head.Range.StartLine
                    && not multiLineLiteral
                    && not (spansDirective source region)
                then
                    let pad = String.replicate indent " "

                    let moved =
                        [
                            for l in body.Head.Range.StartLine .. bodyLastLine ->
                                let line = source.GetLineString(l - 1)
                                if line.Trim() = "" then "" else "    " + line
                        ]
                        |> String.concat "\n"

                    let releaseText =
                        (source.GetLineString(releaseStatement.Range.StartLine - 1)).Trim()

                    Some(region, textOfRange source region, $"{pad}try\n{moved}\n{pad}finally\n{pad}    {releaseText}")
                else
                    None
            | _ -> None

        [
            for path, e in index.Exprs do
                match e with
                // only an acquire FOLLOWED by a body has anything to
                // protect: one that is a whole function's body is a
                // wrapper whose caller decides
                | SynExpr.Sequential(expr1 = statement; expr2 = next) ->
                    match statementHead statement with
                    | AcquireCall source (methodId, receiver, receiverId) & call ->
                        let entity, release = acquirePairs.[methodId.idText]

                        if
                            not (guardsNext receiver release next)
                            && not (guardedAbove receiver release path)
                            && typedGate entity methodId receiverId
                        then
                            {
                                Range = call.Range
                                AcquireText = textOfRange source call.Range
                                // Release answers the previous count, which a
                                // finally must discard
                                ReleaseText =
                                    if release = "Release" then
                                        $"{receiver}.Release() |> ignore"
                                    else
                                        $"{receiver}.{release}()"
                                Fix = fixFor statement receiver release next
                            }
                    | _ -> ()
                | _ -> ()
        ]
