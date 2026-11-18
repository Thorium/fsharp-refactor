/// FR0119 (fix): a synchronous call inside `task { }` where the typed
/// tree proves an async twin exists — the preventive half of FR0049:
/// instead of flagging sync-over-async after the fact, take the
/// asynchronous road while the code is already in a task.
///
///     task {                                   task {
///         let line = reader.ReadLine()   →         let! line = reader.ReadLineAsync()
///         writer.Flush()                           do! writer.FlushAsync()
///
/// Typed gates:
///   - the resolved method's declaring entity offers `<Name>Async` with
///     the SAME parameter-type prefix (an extra trailing OPTIONAL
///     CancellationToken is fine — FR0118 hands it the token on the next
///     pass) and a Task-shaped return: `T` → `Task<T>`/`ValueTask<T>`,
///     `unit` → `Task`/`ValueTask`
///   - `let x = ...` bindings become `let!` (simple named pattern, no
///     annotation); statement position becomes `do!` only when the twin
///     returns the NON-generic Task
///   - inside `async { }` the same rewrite bridges with
///     `|> Async.AwaitTask` — real Task twins only there, AwaitTask has
///     no ValueTask overload — and never under a try/with (inside the
///     CE or around its run): AwaitTask surfaces a faulted task as
///     AggregateException, so `with :? IOException` would stop catching
///     what the blocking call threw bare
///   - never inside a lambda, a nested CE, a finally block or an
///     exception handler
///   - never `Dispose` → `DisposeAsync`: a ValueTask twin with nothing
///     to await behind it
///   - never a `MemoryStream`/`StringWriter`/`StringReader` call or
///     `Console.Out`/`Console.Error` (nothing behind the twin), EF Core's
///     `Add`/`AddRange` (async only for database value generators, EF's
///     documentation says), nor a call inside a member named for its
///     synchronous work (`writeTokenSyncReadingAsync`)
///   - in `task { }` the bind carries `.ConfigureAwait(false)` where the
///     body's own binds all do (`BlockingSites.configureAwaitWanted`)
///   - never a twin that is a member the call sits in (`x.Execute s` inside
///     `member x.ExecuteAsync s` of the twin's type or one derived from it,
///     around a lambda too: it would bind itself; a wrapper's `ReadAsync`
///     calling `inner.Read` is another type's member), a member of this file that starts work and drops it without
///     blocking (a fire-and-forget wrapper), the synchronous branch of a dual
///     sync/async body (`if isAsync then do! x.FlushAsync() else x.Flush()`),
///     a call commented as synchronous on purpose, or Microsoft.Data.Sqlite
///     (its async methods run synchronously)
///   - never a call the CE body also makes through the twin on the same
///     receiver (`writer.WriteLine()` beside `do! writer.WriteLineAsync()`:
///     both paths on purpose), nor one on a stream, reader or writer bound to
///     memory streams alone (`new StreamWriter(buffer)` over a MemoryStream)
module FSharp.Refactor.AwaitableOverload

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text
open System.Text.RegularExpressions

type Suggestion =
    {
        Range: range
        /// (range, original, replacement) edits: the binding keyword or
        /// statement prefix, plus the method name gaining its suffix.
        Fixes: (range * string * string) list
        MethodName: string
    }

let private ceBuilders = set [ "task"; "backgroundTask"; "async" ]

let private inMemoryTypes =
    set
        [
            "System.IO.MemoryStream"
            "System.IO.StringWriter"
            "System.IO.StringReader"
            "System.IO.UnmanagedMemoryStream"
        ]

/// Twins with nothing behind them, or advised against: an in-memory stream,
/// reader or writer and the console's writers complete synchronously anyway;
/// EF Core's `Add`/`AddRange` are async only for value generators that reach
/// the database (SQL Server HiLo), and EF's documentation says to use the
/// synchronous ones otherwise.
let private noTwinWanted (callText: string) (receiverType: FSharpType option) (mfv: FSharpMemberOrFunctionOrValue) =
    // the receiver's own type: `StringWriter.WriteLine` is declared on TextWriter
    let rec memoryType (t: FSharpType option) =
        match t with
        | Some t when t.HasTypeDefinition ->
            let entity = t.TypeDefinition

            (entity.TryFullName |> Option.exists inMemoryTypes.Contains)
            || memoryType entity.BaseType
        | _ -> false

    let memoryReceiver =
        try
            memoryType receiverType
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    let declaring =
        try
            mfv.DeclaringEntity
            |> Option.bind (fun e -> e.TryFullName)
            |> Option.defaultValue ""
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            ""

    let receiver =
        let i = callText.LastIndexOf '.'

        if i > 0 then
            callText.Substring(0, i).Replace("System.", "")
        else
            ""

    inMemoryTypes.Contains declaring
    || memoryReceiver
    || receiver = "Console.Out"
    || receiver = "Console.Error"
    || ((mfv.DisplayName = "Add" || mfv.DisplayName = "AddRange")
        && declaring.StartsWith "Microsoft.EntityFrameworkCore")
    // Microsoft.Data.Sqlite's async methods run synchronously (SQLite has no async I/O)
    || declaring.StartsWith "Microsoft.Data.Sqlite"

let private ioWrapperTypes =
    set
        [
            "System.IO.Stream"
            "System.IO.TextWriter"
            "System.IO.TextReader"
            "System.IO.BinaryWriter"
            "System.IO.BinaryReader"
        ]

/// A stream, reader or writer bound to memory streams alone (`use writer =
/// new StreamWriter(buffer)` over a `MemoryStream`): its twin completes
/// synchronously, as FR0118 reads the same binding.
let private overMemoryOnly
    (index: AstIndex.Index)
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (receiver: Ident option)
    =
    let rec wraps (t: FSharpType option) (depth: int) =
        match t with
        | Some t when depth < 32 && t.HasTypeDefinition ->
            let entity = t.TypeDefinition

            (entity.TryFullName |> Option.exists ioWrapperTypes.Contains)
            || wraps entity.BaseType (depth + 1)
        | _ -> false

    match receiver with
    | Some id ->
        (try
            wraps (BlockingSites.valueTypeOf check source id) 0
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
        && CancellationOverload.boundToMemoryStreams index check source id
    | None -> false

/// The CE body also calls the twin on the same receiver (`writer.WriteLine()`
/// beside `do! writer.WriteLineAsync()`): both paths are exercised on
/// purpose, as a test of a writer does.
let private twinBeside (source: ISourceText) (ceBody: range) (callee: SynExpr) (twinName: string) =
    let calleeText = textOfRange source callee.Range
    let dot = calleeText.LastIndexOf '.'

    dot > 0
    && (let receiver = calleeText.Substring(0, dot)
        let bodyText = textOfRange source ceBody

        bodyText.Contains twinName
        && Regex.IsMatch(bodyText, $@"(?<![\w'.]){Regex.Escape receiver}\s*\.\s*{Regex.Escape twinName}(?![\w'])"))

/// A member the call sits in — the innermost, or one around the lambda it
/// sits in — that is the twin: named like it, and declared by the twin's
/// type or one that derives from or implements it. `let r = x.Execute s`
/// inside `member x.ExecuteAsync s`, or an override of it, would bind the
/// method itself. A member of another type that only shares the name is
/// not that: `member _.ReadAsync buffer = task { let n = inner.Read … }`
/// wraps `inner`'s twin. A member that does not resolve counts as the twin.
let private callsItself
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (path: SyntaxNode list)
    (twin: FSharpMemberOrFunctionOrValue)
    =
    let related (own: FSharpEntity) (twinEntity: FSharpEntity) =
        let rec inherits (e: FSharpEntity) (depth: int) =
            e.IsEffectivelySameAs twinEntity
            || (depth < 32
                && (match e.BaseType with
                    | Some b when b.HasTypeDefinition -> inherits b.TypeDefinition (depth + 1)
                    | _ -> false))

        inherits own 0
        || own.AllInterfaces
           |> Seq.exists (fun i -> i.HasTypeDefinition && i.TypeDefinition.IsEffectivelySameAs twinEntity)

    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)))) when
            not ids.IsEmpty && (List.last ids).idText = twin.DisplayName
            ->
            let name = List.last ids

            try
                let lineText = source.GetLineString(name.idRange.EndLine - 1)

                match
                    OptionModule.symbolUseAt
                        check
                        (name.idRange.EndLine, name.idRange.EndColumn, lineText, [ name.idText ])
                with
                | Some symbolUse ->
                    match symbolUse.Symbol, twin.DeclaringEntity with
                    | (:? FSharpMemberOrFunctionOrValue as own), Some twinEntity ->
                        match own.DeclaringEntity with
                        | Some ownEntity -> related ownEntity twinEntity
                        | None -> false
                    | _ -> true
                | None -> true
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                true
        | _ -> false)

// a discard counts only where its line names an `…Async` call: `let _ =
// d.Remove id` drops a value, not work
let private launchRegex =
    Regex
        @"\bTask\.Run\b|\bStartNew\b|\bAsync\.Start(Immediate)?\b|\bQueueUserWorkItem\b|Async\b[^\n]*\|>\s*ignore\b|\b_\s*=[^\n]*Async\b"

let private blockRegex =
    Regex @"\.Result\b|\.Wait\s*\(|\bGetResult\s*\(|\bRunSynchronously\b|\bAwaitTask\b"

/// A member declared in this file whose body starts work and drops it
/// (`Task.Run(fun () -> x.SendAsync p) |> ignore`, `x.SendAsync p |> ignore`,
/// `Async.Start`) and never blocks on it: a fire-and-forget wrapper, not a
/// blocking call. Binding its twin makes the caller wait for what the author
/// chose not to wait for (an analytics ping before a form shows).
let private firesAndForgets
    (index: AstIndex.Index)
    (source: ISourceText)
    (fileName: string)
    (mfv: FSharpMemberOrFunctionOrValue)
    =
    let declared =
        try
            Some mfv.DeclarationLocation
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            None

    match declared with
    | Some loc when System.String.Equals(loc.FileName, fileName, System.StringComparison.OrdinalIgnoreCase) ->
        index.Exprs
        |> Array.tryPick (fun (path, _) ->
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynBinding(SynBinding(
                    headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)); expr = body)) when
                    not ids.IsEmpty && Range.equals (List.last ids).idRange loc
                    ->
                    Some body
                | _ -> None))
        |> Option.exists (fun body ->
            let text = textOfRange source body.Range
            launchRegex.IsMatch text && not (blockRegex.IsMatch text))
    | _ -> false

let private syncWordRegex =
    Regex "[a-z]Sync(Reading|Writing|Flushing|Copying|Loading|Saving|Sending|Receiving|Waiting|Blocking)(?![a-z])"

/// A member named for its synchronous work (`WriteTokenSyncReadingAsync`):
/// the sync call inside is the point. `Sync` as an inner word before the I/O
/// it does (`SyncReading`, `SyncWriting`): not the verb of `SyncContactsAsync`,
/// not `Resync`/`Synchronize`, and not the noun of `RunSyncJobAsync` or
/// `GetSyncStatusAsync`.
let private syncOnPurpose (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)))) when
            not ids.IsEmpty
            ->
            Some (List.last ids).idText
        | _ -> None)
    |> Option.exists (fun name ->
        let stem =
            if name.EndsWith "Async" then
                name.Substring(0, name.Length - 5)
            else
                name

        syncWordRegex.IsMatch stem)

[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

let private parameterShapes (displayContext: FSharpDisplayContext) (mfv: FSharpMemberOrFunctionOrValue) =
    try
        match mfv.CurriedParameterGroups |> List.ofSeq with
        | [ group ] -> Some [ for p in group -> p.Type.Format displayContext ]
        | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

let private isOptionalCancellationToken (m: FSharpMemberOrFunctionOrValue) =
    try
        let last = m.CurriedParameterGroups |> Seq.collect id |> Seq.last

        last.IsOptionalArg
        && (match last.Type.StripAbbreviations().TypeDefinition.TryFullName with
            | Some full -> full = "System.Threading.CancellationToken"
            | None -> false)
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

let private returnFullName (m: FSharpMemberOrFunctionOrValue) =
    try
        match m.ReturnParameter.Type.StripAbbreviations().TypeDefinition.TryFullName with
        | Some full -> full
        | None -> ""
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        ""

/// The async twin's return must wrap the original's: `T` → `Task<T>` /
/// `ValueTask<T>`, `unit` → `Task`/`ValueTask`. Compared structurally —
/// formatted names depend on what happens to be open at the call site.
let private returnsWrapped
    (displayContext: FSharpDisplayContext)
    (orig: FSharpMemberOrFunctionOrValue)
    (twin: FSharpMemberOrFunctionOrValue)
    =
    try
        let origFormat = orig.ReturnParameter.Type.Format displayContext

        match returnFullName twin with
        | "System.Threading.Tasks.Task"
        | "System.Threading.Tasks.ValueTask" -> origFormat = "unit"
        | n when
            n.StartsWith "System.Threading.Tasks.Task`"
            || n.StartsWith "System.Threading.Tasks.ValueTask`"
            ->
            twin.ReturnParameter.Type.StripAbbreviations().GenericArguments
            |> Seq.tryHead
            |> Option.map (fun inner -> inner.Format displayContext = origFormat)
            |> Option.defaultValue false
        | _ -> false
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// Does the twin return the NON-generic Task — the only shape `do!` binds.
let private returnsPlainTask (twin: FSharpMemberOrFunctionOrValue) =
    match returnFullName twin with
    | "System.Threading.Tasks.Task"
    | "System.Threading.Tasks.ValueTask" -> true
    | _ -> false

/// Async.AwaitTask exists for real Tasks only.
let private returnsRealTask (twin: FSharpMemberOrFunctionOrValue) =
    let n = returnFullName twin
    n = "System.Threading.Tasks.Task" || n.StartsWith "System.Threading.Tasks.Task`"

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // bodies choreographed around a thread (a signal, a Thread,
        // Interlocked): a bind there moves the continuation off the thread
        // the code waited on — the same refusal as FR0142's and FR0049's
        let threadBoundBodies =
            index.Exprs
            |> Array.collect (fun (path, _) ->
                path
                |> List.choose (fun node ->
                    match node with
                    | SyntaxNode.SynBinding(SynBinding(expr = body)) -> Some body
                    | _ -> None)
                |> Array.ofList)
            |> Array.distinctBy (fun body -> body.Range)
            |> Array.filter (BlockingSites.threadBound source)
            |> Array.map (fun body -> body.Range)

        // task/async CE bodies with their builder, for scoping and for
        // picking the bind bridge
        let ces =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                    ceBuilders.Contains builder
                    ->
                    Some(builder, body.Range)
                | _ -> None)

        // Every CE's own STATEMENT SPINE: the chain of let/use/sequential
        // nodes hanging directly off its body. `let!` and `do!` are legal
        // only there — a call nested inside ANOTHER binding's right-hand
        // side sits inside the CE's range but not on its spine, and
        // rewriting its `let` to `let!` cannot compile:
        //     async {
        //         let pair =
        //             ...
        //             let json = File.ReadAllText p   // NOT on the spine
        let spineRanges =
            let acc = ResizeArray<range>()

            let rec walk (e: SynExpr) =
                acc.Add e.Range

                match e with
                | LetOrUseE lou -> walk lou.Body
                | SynExpr.Sequential(expr1 = a; expr2 = b) ->
                    acc.Add a.Range
                    walk b
                // control flow whose branches are statement positions of
                // the same CE: a `let!` is as legal in a match arm, an if
                // branch, a try body or a loop body as at the top of the
                // block, however deep (`match res with | Choice2Of2 e -> ...
                // let err = reader.ReadToEnd()` two arms down). A `with` handler and a `finally` stay out —
                // the bind gate below excludes them on purpose
                | SynExpr.Match(clauses = clauses)
                | SynExpr.MatchBang(clauses = clauses) ->
                    for SynMatchClause(resultExpr = result) in clauses do
                        walk result
                | SynExpr.IfThenElse(thenExpr = thenExpr; elseExpr = elseExpr) ->
                    walk thenExpr
                    elseExpr |> Option.iter walk
                | SynExpr.TryWith(tryExpr = body)
                | SynExpr.TryFinally(tryExpr = body)
                | SynExpr.ForEach(bodyExpr = body)
                | SynExpr.For(doBody = body)
                | SynExpr.While(doExpr = body)
                | SynExpr.Paren(expr = body) -> walk body
                | _ -> ()

            for _, e in index.Exprs do
                match e with
                | SynExpr.App(
                    isInfix = false; funcExpr = IdentName builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
                    ceBuilders.Contains builder
                    ->
                    walk body
                | _ -> ()

            acc.ToArray()

        let onSpine (r: range) =
            spineRanges |> Array.exists (fun s -> Range.equals s r)

        let lambdaRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.Lambda _
                | SynExpr.MatchLambda _ -> [| e.Range |]
                // a LOCAL FUNCTION's body is a closure too, but its AST is
                // a binding with argument patterns, not a Lambda node — a
                // do!/let! injected there would land in a plain function
                | LetOrUseE lou when not lou.IsBang ->
                    lou.Bindings
                    |> List.choose (fun b ->
                        match b with
                        | SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))) ->
                            Some b.RangeOfBindingWithRhs
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])

        let otherCeRanges =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.ComputationExpr(expr = body) -> Some body.Range
                | SynExpr.ArrayOrListComputed(expr = body) -> Some body.Range
                | _ -> None)

        // the protected bodies of every try/with in the file: under one,
        // an async site's `Async.AwaitTask` bridge would hand the handler
        // an AggregateException where the blocking call threw the bare
        // exception (`with :? IOException` stops catching) — whether the
        // try sits inside the CE or around its run
        let tryWithBodies =
            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | SynExpr.TryWith(tryExpr = body) -> Some body.Range
                | _ -> None)

        let noBindRanges =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | SynExpr.TryFinally(finallyExpr = f) -> [| f.Range |]
                | SynExpr.TryWith(withCases = cases) ->
                    cases
                    |> List.map (fun (SynMatchClause(resultExpr = result)) -> result.Range)
                    |> Array.ofList
                | _ -> [||])

        // the INNERMOST enclosing task/async body a site sits directly in:
        // its builder decides the bridge. Nothing inside a lambda, nested
        // CE, finally, or handler qualifies
        let directBuilder (r: range) =
            if noBindRanges |> Array.exists (fun z -> Range.rangeContainsRange z r) then
                None
            else
                ces
                |> Array.filter (fun (_, ceRange) ->
                    Range.rangeContainsRange ceRange r
                    && not (
                        lambdaRanges
                        |> Array.exists (fun l -> Range.rangeContainsRange ceRange l && Range.rangeContainsRange l r)
                    )
                    && not (
                        otherCeRanges
                        |> Array.exists (fun other ->
                            Range.rangeContainsRange ceRange other
                            && not (Range.equals other ceRange)
                            && Range.rangeContainsRange other r)
                    ))
                |> Array.sortBy (fun (_, ceRange) -> ceRange.EndLine - ceRange.StartLine, ceRange.EndColumn)
                |> Array.tryHead

        // the plain `let` whose entire RHS is `target` — the let! shape
        let bindingKeywordFor (target: range) =
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
                            trivia = btrivia) ] when Range.equals rhs.Range target ->
                        // the let node's own range travels too: only a
                        // binding ON THE CE SPINE may become `let!`
                        Some(btrivia.LeadingKeyword.Range, e.Range)
                    | _ -> None
                | _ -> None)

        // statement position: a sequential element of the CE chain with a
        // successor — any of them, not only the first (the index records
        // only a chain's outermost Sequential)
        let isStatement (target: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                match e with
                | SynExpr.Sequential _ -> BlockingSites.isChainStatement e target
                | _ -> false)

        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = (CallIdent methodId as callee); argExpr = args) when
                    not (methodId.idText.EndsWith "Async")
                    // `Dispose` → `DisposeAsync` never pays: the twin returns
                    // ValueTask (outside the Task/Task<T> gate the rule
                    // documents) and there is nothing to await —
                    // `File.Create(f).Dispose()` would become
                    // `do! File.Create(f).DisposeAsync()`
                    && methodId.idText <> "Dispose"
                    ->
                    let tupled =
                        match args with
                        | SynExpr.Const(SynConst.Unit, _) -> Some 0
                        | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> Some es.Length
                        | SynExpr.Paren _ -> Some 1
                        // juxtaposed atomic argument — `writer.Write s` — is
                        // the common F# spelling; the rewrite only touches the
                        // keyword and the name, so the arg shape can stay
                        | SynExpr.Const _
                        | SynExpr.Ident _
                        | SynExpr.LongIdent _ -> Some 1
                        | _ -> None

                    match tupled, directBuilder expr.Range with
                    | Some arity, Some(builder, ceBody) ->
                        let lineText = source.GetLineString(methodId.idRange.EndLine - 1)

                        let resolved =
                            OptionModule.symbolUseAt
                                check
                                (methodId.idRange.EndLine, methodId.idRange.EndColumn, lineText, [ methodId.idText ])

                        match resolved with
                        | Some symbolUse ->
                            match symbolUse.Symbol with
                            | :? FSharpMemberOrFunctionOrValue as mfv when
                                mfv.IsMember
                                && not mfv.IsProperty
                                && not (
                                    noTwinWanted
                                        (textOfRange source callee.Range)
                                        ((match callee with
                                          | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                              Some ids.[ids.Length - 2]
                                          | SynExpr.DotGet(expr = recv) -> BlockingSites.receiverIdent recv
                                          | _ -> None)
                                         |> Option.bind (BlockingSites.valueTypeOf check source))
                                        mfv
                                )
                                && not (syncOnPurpose path)
                                ->
                                let ctx = symbolUse.DisplayContext

                                let twin =
                                    match parameterShapes ctx mfv with
                                    | Some ps when ps.Length = arity ->
                                        (try
                                            match mfv.DeclaringEntity with
                                            | Some entity ->
                                                entity.MembersFunctionsAndValues
                                                |> Seq.tryFind (fun m ->
                                                    m.DisplayName = mfv.DisplayName + "Async"
                                                    && returnsWrapped ctx mfv m
                                                    && (match parameterShapes ctx m with
                                                        | Some mps when mps.Length = arity -> mps = ps
                                                        | Some mps when mps.Length = arity + 1 ->
                                                            List.truncate arity mps = ps
                                                            && isOptionalCancellationToken m
                                                        | _ -> false))
                                            | None -> None
                                         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                             None)
                                    | _ -> None

                                // async { } bridges via Async.AwaitTask, which
                                // has no ValueTask overload — real Task only
                                let twin =
                                    match builder, twin with
                                    | "async", Some m when not (returnsRealTask m) -> None
                                    | "async", Some _ when
                                        tryWithBodies |> Array.exists (fun b -> Range.rangeContainsRange b expr.Range)
                                        ->
                                        None
                                    | _ -> twin

                                // a twin that is the member itself, a fire-and-forget
                                // wrapper, the sync branch of a dual sync/async body,
                                // a call commented as synchronous on purpose, one the
                                // body also makes through the twin, or a writer over
                                // memory streams
                                let receiverIdent =
                                    match callee with
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                        Some ids.[ids.Length - 2]
                                    | SynExpr.DotGet(expr = recv) -> BlockingSites.receiverIdent recv
                                    | _ -> None

                                let twin =
                                    match twin with
                                    | Some twinM when
                                        callsItself check source path twinM
                                        || twinBeside source ceBody callee twinM.DisplayName
                                        || overMemoryOnly index check source receiverIdent
                                        || firesAndForgets index source parseTree.FileName mfv
                                        || BlockingSites.dualPathBranch source path expr.Range (fun line ->
                                            Regex.IsMatch(line, identifierPattern twinM.DisplayName))
                                        || BlockingSites.syncByComment source expr.Range
                                        ->
                                        None
                                    | t -> t

                                match twin with
                                | Some twinM ->
                                    let renameFix = methodId.idRange, methodId.idText, methodId.idText + "Async"

                                    let bridgeFixes =
                                        if builder = "async" then
                                            let atEnd = Range.mkRange expr.Range.FileName expr.Range.End expr.Range.End

                                            [ atEnd, "", " |> Async.AwaitTask" ]
                                        else
                                            []

                                    // `.ConfigureAwait(false)` where the body's own binds all
                                    // have it: on `name(...)` as it stands, around a
                                    // juxtaposed argument in parentheses
                                    let atStart = Range.mkRange expr.Range.FileName expr.Range.Start expr.Range.Start
                                    let atEnd = Range.mkRange expr.Range.FileName expr.Range.End expr.Range.End

                                    let opening, suffixFixes =
                                        if not (BlockingSites.configureAwaitWanted index source builder ceBody) then
                                            "", []
                                        else
                                            let tight =
                                                match args with
                                                | SynExpr.Const(SynConst.Unit, _)
                                                | SynExpr.Paren _ ->
                                                    args.Range.StartLine = methodId.idRange.EndLine
                                                    && args.Range.StartColumn = methodId.idRange.EndColumn
                                                | _ -> false

                                            if tight then
                                                "", [ atEnd, "", ".ConfigureAwait(false)" ]
                                            else
                                                "(", [ atEnd, "", ").ConfigureAwait(false)" ]

                                    match bindingKeywordFor expr.Range with
                                    | Some(kw, letRange) when textOfRange source kw = "let" && onSpine letRange ->
                                        {
                                            Range = expr.Range
                                            Fixes =
                                                [ kw, "let", "let!"; renameFix ]
                                                @ (if opening = "" then [] else [ atStart, "", opening ])
                                                @ suffixFixes
                                                @ bridgeFixes
                                            MethodName = methodId.idText
                                        }
                                    | Some _ -> ()
                                    | None ->
                                        // statement position takes do! — but
                                        // only a NON-generic Task binds there,
                                        // and only ON the CE's own spine
                                        if isStatement expr.Range && onSpine expr.Range && returnsPlainTask twinM then
                                            {
                                                Range = expr.Range
                                                Fixes =
                                                    [ atStart, "", "do! " + opening; renameFix ]
                                                    @ suffixFixes
                                                    @ bridgeFixes
                                                MethodName = methodId.idText
                                            }
                                | None -> ()
                            | _ -> ()
                        | None -> ()
                    | _ -> ()
                | _ -> ()
        ]
        |> List.filter (fun s ->
            not (
                threadBoundBodies
                |> Array.exists (fun body -> Range.rangeContainsRange body s.Range)
            ))
