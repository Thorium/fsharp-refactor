/// FR0180 (performance, fix), twin of the C# rule: a `Random` constructed
/// per call, unseeded or seeded from the clock.
///
///     let jitter () = Random().Next 20
///     let pick () = (new Random(DateTime.Now.Millisecond)).Next 6
///     ->  Random.Shared.Next 20
///
/// Every call builds a generator to draw from it once. On .NET Framework
/// an unseeded one is seeded from the tick count, so two built in the same
/// tick draw the same numbers; a seed written out from the clock
/// (`DateTime.Now.Millisecond`, `Environment.TickCount`, a thread id, a
/// fresh Guid's hash) repeats that on every runtime. `Random.Shared` is one
/// thread-safe generator, properly seeded.
///
/// The shapes: `Random()` / `new Random()` with no argument, or with a
/// seed made ONLY of clock, thread and process reads, literals, casts and
/// arithmetic over them - written inside a function, a member or a
/// lambda, so it runs per call. A module-level or class-level `let rnd =
/// Random()` is constructed once and stays. A seed with any other operand
/// (a parameter, a field, a constant alone) is a decision: quiet.
///
/// The generator must be drawn from where it is built: the receiver of a
/// member call, or a local whose every use is one. An instance stored in a
/// record or a field, returned, or passed on is state somebody holds, and
/// stays the author's.
///
/// Typed rule: the type must resolve to System.Random. `Random.Shared`
/// exists from .NET 6; where the referenced framework has none, the note
/// stands without a fix.
module FSharp.Refactor.RandomShared

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The constructor call, `new` included.
        Range: range
        OriginalText: string
        /// `Random.Shared`, spelled like the constructor was; None where
        /// the framework has no `Random.Shared`.
        ReplacementText: string option
        /// The seed was written out from the clock.
        ClockSeeded: bool
    }

let private clockRoots =
    [
        [ "DateTime"; "Now" ]
        [ "DateTime"; "UtcNow" ]
        [ "DateTime"; "Today" ]
        [ "DateTimeOffset"; "Now" ]
        [ "DateTimeOffset"; "UtcNow" ]
        [ "Environment"; "TickCount" ]
        [ "Environment"; "TickCount64" ]
        [ "Thread"; "CurrentThread"; "ManagedThreadId" ]
        [ "Stopwatch"; "GetTimestamp" ]
    ]

let private arithmetic =
    set
        [
            "op_Addition"
            "op_Subtraction"
            "op_Multiply"
            "op_Modulus"
            "op_ExclusiveOr"
            "op_BitwiseAnd"
            "op_BitwiseOr"
        ]

let private conversions = set [ "int"; "int32"; "int64"; "uint32"; "abs"; "hash" ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // System.Random, and whether it has `Shared`
        let randomEntity (ident: Ident) =
            try
                match BlockingSites.symbolAt check source ident with
                | Some(:? FSharpEntity as entity) when entity.TryFullName = Some "System.Random" -> Some entity
                | Some(:? FSharpMemberOrFunctionOrValue as ctor) ->
                    ctor.DeclaringEntity
                    |> Option.filter (fun e -> e.TryFullName = Some "System.Random")
                | _ -> None
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                None

        let hasShared (entity: FSharpEntity) =
            try
                entity.MembersFunctionsAndValues
                |> Seq.exists (fun m -> m.DisplayName = "Shared" || m.CompiledName = "get_Shared")
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                false

        // `DateTime.Now.Ticks`, `System.Environment.TickCount`: a clock,
        // thread or process read under any namespace prefix
        let isClockPath (ids: Ident list) =
            let names = ids |> List.map (fun i -> i.idText)

            clockRoots
            |> List.exists (fun root ->
                let rec startsAt (rest: string list) =
                    match rest with
                    | [] -> false
                    | _ when rest.Length >= root.Length && List.take root.Length rest = root -> true
                    | _ :: tail -> startsAt tail

                startsAt names)

        // true when the expression reads nothing but clocks and literals;
        // `sawClock` records that at least one clock was read
        let rec clockOnly (sawClock: bool ref) (e: SynExpr) =
            match stripParens e with
            | SynExpr.Const _ -> true
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when isClockPath ids ->
                sawClock.Value <- true
                true
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs)
                argExpr = rhs) when arithmetic.Contains op.idText -> clockOnly sawClock lhs && clockOnly sawClock rhs
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident f; argExpr = arg) when conversions.Contains f.idText ->
                clockOnly sawClock arg
            // Guid.NewGuid().GetHashCode() / clock.GetHashCode() / Stopwatch.GetTimestamp()
            | SynExpr.App(isInfix = false; funcExpr = callee; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
                match callee with
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when isClockPath ids ->
                    sawClock.Value <- true
                    true
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                    ids.Length >= 2
                    && (ids |> List.map (fun i -> i.idText) |> List.rev |> List.take 2) = [ "NewGuid"; "Guid" ]
                    ->
                    sawClock.Value <- true
                    true
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                    ids.Length >= 3 && (List.last ids).idText = "GetHashCode"
                    ->
                    let receiver = ids |> List.take (ids.Length - 1)

                    if isClockPath receiver then
                        sawClock.Value <- true
                        true
                    else
                        false
                | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ m ])) when m.idText = "GetHashCode" ->
                    clockOnly sawClock receiver
                | _ -> false
            | _ -> false

        // constructed per call: under a function, a member with arguments
        // or a lambda
        let perCall (path: SyntaxNode list) =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.Lambda _ | SynExpr.MatchLambda _) -> true
                | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)))) ->
                    true
                | _ -> false)

        let sameSpan (a: range) (b: range) = a.Start = b.Start && a.End = b.End

        // drawn from in place: `Random().Next 6`, or `let rnd = Random()`
        // whose every mention in its scope is `rnd.Member`
        let rec drawnFrom (path: SyntaxNode list) (built: range) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren(expr = inner) as paren) :: rest when sameSpan inner.Range built ->
                drawnFrom rest paren.Range
            | SyntaxNode.SynExpr(SynExpr.DotGet(expr = receiver)) :: _ -> sameSpan receiver.Range built
            | SyntaxNode.SynBinding(SynBinding(
                isMutable = false; headPat = SynPat.Named(ident = SynIdent(ident = name)); expr = value)) :: SyntaxNode.SynExpr(SynExpr.LetOrUse _ as scope) :: _ when
                sameSpan value.Range built
                ->
                AstIndex.mentionsOf index name.idText
                |> Array.forall (fun (struct (mention, receiver)) ->
                    receiver || not (Range.rangeContainsRange scope.Range mention))
            | _ -> false

        let suggest (path: SyntaxNode list) (whole: range) (typeIds: Ident list) (arg: SynExpr) : Suggestion option =
            match
                (if drawnFrom path whole then
                     randomEntity (List.last typeIds)
                 else
                     None)
            with
            | Some entity ->
                let seeded =
                    match stripParens arg with
                    | SynExpr.Const(SynConst.Unit, _) -> Some false
                    | seed ->
                        let sawClock = ref false

                        if clockOnly sawClock seed && sawClock.Value then
                            Some true
                        else
                            None

                match seeded with
                | Some clockSeeded ->
                    let spelled =
                        textOfRange source (Range.unionRanges typeIds.Head.idRange (List.last typeIds).idRange)

                    Some
                        {
                            Range = whole
                            OriginalText = textOfRange source whole
                            ReplacementText = if hasShared entity then Some(spelled + ".Shared") else None
                            ClockSeeded = clockSeeded
                        }
                | None -> None
            | None -> None

        let isRandomName (ids: Ident list) =
            match List.tryLast ids with
            | Some last -> last.idText = "Random"
            | None -> false

        // `new Random(...)` holds the same application inside: report the
        // outer expression once
        let insideNew = System.Collections.Generic.HashSet<range>()

        [
            for path, e in index.Exprs do
                if not (insideNew.Contains e.Range) then
                    match e with
                    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when
                        isRandomName ids && perCall path
                        ->
                        insideNew.Add arg.Range |> ignore
                        yield! suggest path e.Range ids arg |> Option.toList
                    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id; argExpr = arg) when
                        isRandomName [ id ] && perCall path
                        ->
                        yield! suggest path e.Range [ id ] arg |> Option.toList
                    | SynExpr.App(
                        isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                        isRandomName ids && perCall path
                        ->
                        yield! suggest path e.Range ids arg |> Option.toList
                    | _ -> ()
        ]
