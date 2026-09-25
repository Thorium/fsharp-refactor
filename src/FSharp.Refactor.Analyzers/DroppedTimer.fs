/// FR0163 (correctness): a `System.Threading.Timer` constructed and
/// dropped — piped to `ignore`, or a statement of its own — is collectable
/// the moment the constructor returns, and the garbage collector stops it
/// mid-flight whenever it next runs.
///
///     new Timer(tick, null, 0, 1000) |> ignore      // fires until the next GC
///     use timer = new Timer(tick, null, 0, 1000)     // fires for the scope
///
/// The documentation is explicit: "As long as you are using a Timer, you
/// must keep a reference to it... The fact that a Timer is still active
/// does not prevent it from being collected." F# makes the mistake easier
/// than C# does — FS0020 pushes an unbound construction into `|> ignore`,
/// which reads as tidy and is the leak. Only `System.Threading.Timer`
/// (typed): `System.Timers.Timer` is reachable from the timer queue
/// through its own callback while enabled, and is not collected.
/// Note only: whether the timer lives in a `use`, a `let` the caller
/// returns, or a field is the design.
module FSharp.Refactor.DroppedTimer

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The construction, as dropped.
        Range: range
    }

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the constructed type, from the constructor's identifier
        let isThreadingTimer (typeId: Ident) =
            let r = typeId.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ typeId.idText ]) with
            | Some symbolUse ->
                (try
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as mfv when mfv.IsConstructor ->
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.map ((=) "System.Threading.Timer")
                        |> Option.defaultValue false
                    | :? FSharpEntity as e -> e.TryFullName = Some "System.Threading.Timer"
                    | _ -> false
                 with _ -> // an unreadable type is not the timer; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

        // `new Timer(...)` / `Timer(...)`: the type's identifier
        let construction (e: SynExpr) =
            match stripParens e with
            | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
                Some(List.last ids)
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident typeId) -> Some typeId
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
                not ids.IsEmpty
                ->
                Some(List.last ids)
            | _ -> None

        [
            for _, e in index.Exprs do
                let dropped =
                    match e with
                    // `new Timer(...) |> ignore`
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)
                        argExpr = SingleIdent ignore') when op.idText = "op_PipeRight" && ignore'.idText = "ignore" ->
                        construction left |> Option.map (fun t -> t, left)
                    // `ignore (new Timer(...))`
                    | SynExpr.App(isInfix = false; funcExpr = SingleIdent ignore'; argExpr = arg) when
                        ignore'.idText = "ignore"
                        ->
                        construction arg |> Option.map (fun t -> t, arg)
                    // a statement of its own
                    | SynExpr.Sequential(expr1 = statement) ->
                        construction statement |> Option.map (fun t -> t, statement)
                    // a local `let` (not `use`) the rest of the scope never
                    // mentions: nothing stores, returns, passes or disposes it,
                    // so the reference dies with the scope — the CR0162 shape.
                    // A mention of any kind stands the note down: what leaves
                    // the scope is not this rule's to judge
                    | LetOrUseE lou when not (lou.IsUse || lou.IsBang) ->
                        lou.Bindings
                        |> List.tryPick (fun b ->
                            match b with
                            // `let _ = new Timer(...)` is `ignore` spelled as a binding
                            | SynBinding(headPat = SynPat.Wild _; expr = rhs) ->
                                construction rhs |> Option.map (fun t -> t, rhs)
                            | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = rhs)
                            | SynBinding(
                                headPat = SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))); expr = rhs) when
                                not (
                                    System.Text.RegularExpressions.Regex.IsMatch(
                                        textOfRange source lou.Body.Range,
                                        identifierPattern id.idText
                                    )
                                )
                                ->
                                construction rhs |> Option.map (fun t -> t, rhs)
                            | _ -> None)
                    | _ -> None

                match dropped with
                // the spelling first: every statement-position application
                // reaches here, and a symbol lookup per statement is not free
                | Some(typeId, timer) when typeId.idText = "Timer" && isThreadingTimer typeId -> { Range = timer.Range }
                | _ -> ()
        ]
