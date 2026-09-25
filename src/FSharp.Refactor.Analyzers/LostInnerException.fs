/// FR0160 (correctness): a handler raises a new exception and drops the
/// one it caught — no InnerException, no original stack trace. What the
/// log shows is the wrapper; what went wrong is gone.
///
///     with ex -> raise (ConfigException("bad config"))
///  →  with ex -> raise (ConfigException("bad config", ex))
///
///     with _ -> raise (ConfigException "bad config")
///  →  with ex -> raise (ConfigException("bad config", ex))
///
/// CA2200 covers `raise ex` (FR0044 here); this is the other half — the
/// wrapper that forgets its cause. The fix is offered when the constructed
/// type has a constructor taking the same arguments plus a trailing
/// `System.Exception` (the typed check compares parameter types AND
/// names: `ArgumentNullException(paramName)` has a `(message,
/// innerException)` sibling, and `, ex` would make the name a message), and
/// the handler's binder — or a fresh `ex` bound in the pattern, free in
/// the whole declaration — becomes that argument. Gates, as the C# twin
/// (CR0165) draws them: the raise is one of the handler's own statements
/// (through sequences, `if`s, matches, `let` bodies and a computation's
/// `return`; not inside a lambda, an object expression, a local function
/// or a nested try, where it runs in another context); the constructor's
/// arguments read nothing of the caught exception (`ex.Message` in the
/// message is the author's choice); no argument is named; the trailing
/// constructor is accessible from the raise site. `failwith`/`failwithf`/
/// `invalidOp`/`invalidArg` in a handler that never reads what it caught
/// have no inner-exception overload and are noted: `raise (Exception(msg,
/// ex))` spells the same failure with its cause.
module FSharp.Refactor.LostInnerException

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The raising expression.
        Range: range
        /// The exception type constructed, or the failure function's name.
        Raised: string
        /// The caught exception's name once the fix has run (`ex`), for the
        /// message.
        Binder: string
        /// The edits: the binder in the pattern when it was missing, and
        /// the trailing argument. Empty for a `failwith` note.
        Edits: (range * string * string) list
    }

let private failureFunctions =
    set [ "failwith"; "failwithf"; "invalidOp"; "invalidArg"; "nullArg" ]

/// A suggestion's `Raised` names one of the failure functions rather than
/// an exception type.
let isFailureFunction (raised: string) = failureFunctions.Contains raised

/// The exception a handler pattern binds, and the pattern to widen when
/// it binds none.
let private binderOf (pat: SynPat) =
    match pat with
    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
    | SynPat.As(rhsPat = SynPat.Named(ident = SynIdent(ident = id))) -> Some id.idText
    | _ -> None

/// `raise (X(args))` / `raise (X args)` / `raise (new X(args))`: the type's
/// last identifier, the function expression's range and the argument.
[<return: Struct>]
let private (|RaiseNew|_|) (e: SynExpr) =
    let constructed (inner: SynExpr) =
        match inner with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident typeId; argExpr = arg) ->
            ValueSome(typeId, typeId.idRange, arg)
        | SynExpr.App(
            isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) & f; argExpr = arg) when
            not ids.IsEmpty
            ->
            ValueSome(List.last ids, f.Range, arg)
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)) & t; expr = arg) when not ids.IsEmpty ->
            ValueSome(List.last ids, t.Range, arg)
        | _ -> ValueNone

    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident raise'; argExpr = SynExpr.Paren(expr = inner)) when
        raise'.idText = "raise"
        ->
        constructed inner
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let mentions (name: string) (r: range) =
            System.Text.RegularExpressions.Regex.IsMatch(textOfRange source r, identifierPattern name)

        // the constructor the call resolves to, and its declaring type
        let constructorAt (typeId: Ident) =
            let r = typeId.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ typeId.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv when mfv.IsConstructor -> Some(symbolUse, mfv)
                | _ -> None
            | None -> None

        let shapes (displayContext: FSharpDisplayContext) (mfv: FSharpMemberOrFunctionOrValue) =
            try
                match mfv.CurriedParameterGroups |> List.ofSeq with
                | [ group ] -> Some [ for p in group -> p.Type.Format displayContext ]
                | [] -> Some []
                | _ -> None
            with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                None

        let names (mfv: FSharpMemberOrFunctionOrValue) =
            [ for p in Seq.collect id mfv.CurriedParameterGroups -> p.Name ]

        // a sibling constructor: the same parameters (types and names),
        // then an exception
        let hasInnerOverload (typeId: Ident) (arity: int) =
            match constructorAt typeId with
            | Some(symbolUse, ctor) ->
                (try
                    match shapes symbolUse.DisplayContext ctor with
                    | Some ps when ps.Length = arity ->
                        match ctor.DeclaringEntity with
                        | Some entity ->
                            // reachable from the raise site: public, or
                            // internal/protected to a type this compilation
                            // declares (the assembly under compilation has no
                            // file yet); private never
                            let accessible (m: FSharpMemberOrFunctionOrValue) =
                                m.Accessibility.IsPublic
                                || (not m.Accessibility.IsPrivate && entity.Assembly.FileName.IsNone)

                            entity.MembersFunctionsAndValues
                            |> Seq.exists (fun m ->
                                m.IsConstructor
                                && accessible m
                                && (match shapes symbolUse.DisplayContext m with
                                    | Some mps when mps.Length = arity + 1 ->
                                        List.truncate arity mps = ps
                                        // the same parameter NAMES too: the
                                        // one-string ctor of ArgumentNullException
                                        // takes a paramName, its (string, Exception)
                                        // sibling a message
                                        && List.truncate arity (names m) = names ctor
                                        && (m.CurriedParameterGroups
                                            |> Seq.collect id
                                            |> Seq.tryLast
                                            |> Option.map (fun p ->
                                                (OptionModule.stripAbbreviations p.Type).HasTypeDefinition
                                                && (OptionModule.stripAbbreviations p.Type).TypeDefinition.TryFullName =
                                                    Some "System.Exception")
                                            |> Option.defaultValue false)
                                    | _ -> false))
                        | None -> false
                    | _ -> false
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

        // the arguments of a constructor call
        let arguments (arg: SynExpr) =
            match arg with
            | SynExpr.Const(SynConst.Unit, _) -> []
            | SynExpr.Paren(expr = SynExpr.Tuple(exprs = es)) -> es
            | SynExpr.Paren(expr = inner) -> [ inner ]
            | other -> [ other ]

        // `X(message = "m")`: a positional `, ex` after a named argument
        // does not compile, and the named one may already be the inner
        let isNamedArg (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident _)) ->
                op.idText = "op_Equality"
            | _ -> false

        // the function a (possibly curried) application applies:
        // `failwithf "%s %d" a b` nests an App per argument
        let rec headIdent (e: SynExpr) =
            match e with
            | SynExpr.App(isInfix = false; funcExpr = f) -> headIdent f
            | SynExpr.Ident f -> Some f
            | _ -> None

        // the nearest handler above an expression: the try and the clause
        // the handler's own statements only: through sequences, `if`s,
        // matches, `let` bodies and a computation's `return` — not into a
        // lambda, an object expression, a local function or a nested try,
        // where the raise runs in another context, or not at all
        let handlerOf (path: SyntaxNode list) (r: range) =
            let rec walk (nodes: SyntaxNode list) =
                match nodes with
                | SyntaxNode.SynExpr(SynExpr.TryWith(withCases = clauses)) :: _ ->
                    clauses
                    |> List.tryFind (fun (SynMatchClause(resultExpr = result)) ->
                        Range.rangeContainsRange result.Range r)
                | SyntaxNode.SynExpr(SynExpr.Sequential _) :: rest
                | SyntaxNode.SynExpr(SynExpr.IfThenElse _) :: rest
                | SyntaxNode.SynExpr(SynExpr.Match _) :: rest
                | SyntaxNode.SynExpr(SynExpr.LetOrUse _) :: rest
                | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest
                | SyntaxNode.SynExpr(SynExpr.YieldOrReturn _) :: rest
                | SyntaxNode.SynExpr(SynExpr.Typed _) :: rest
                | SyntaxNode.SynExpr(SynExpr.Do _) :: rest
                | SyntaxNode.SynMatchClause _ :: rest -> walk rest
                | _ -> None

            walk path

        // the enclosing declaration, whose names a fresh binder must not
        // shadow (a parameter called `ex`)
        let declarationOf (path: SyntaxNode list) (fallback: range) =
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynBinding(SynBinding _ as b) -> Some b.RangeOfBindingWithRhs
                | _ -> None)
            |> Option.defaultValue fallback

        [
            for path, e in index.Exprs do
                match e with
                | RaiseNew(typeId, funcRange, arg) ->
                    match handlerOf path e.Range with
                    | Some(SynMatchClause(pat = pat)) ->
                        let binder = binderOf pat
                        let args = arguments arg

                        // an argument reading the caught exception in any way
                        // (`ex.Message` in the message) is the author's choice
                        let readsBinder =
                            match binder with
                            | Some name -> mentions name arg.Range
                            | None -> false

                        if
                            not readsBinder
                            && not (args |> List.exists isNamedArg)
                            && hasInnerOverload typeId args.Length
                        then
                            // the caught exception's name: the pattern's own, or
                            // a fresh one the pattern gains — free in the whole
                            // declaration, so no parameter or local is shadowed
                            let name, patEdits =
                                match binder with
                                | Some name -> name, []
                                | None ->
                                    let scope = declarationOf path e.Range

                                    let fresh =
                                        [ "ex"; "exn"; "inner" ]
                                        |> List.tryFind (fun candidate -> not (mentions candidate scope))
                                        |> Option.defaultValue "innerException"

                                    match pat with
                                    | SynPat.Wild _ -> fresh, [ pat.Range, textOfRange source pat.Range, fresh ]
                                    | SynPat.IsInst _ ->
                                        let original = textOfRange source pat.Range
                                        fresh, [ pat.Range, original, $"{original} as {fresh}" ]
                                    | _ -> fresh, []

                            let argEdit =
                                match arg with
                                | SynExpr.Const(SynConst.Unit, unitRange) -> Some(unitRange, "()", $"({name})")
                                | SynExpr.Paren(expr = inner; rightParenRange = Some rp) ->
                                    let at = Range.mkRange e.Range.FileName inner.Range.End rp.Start
                                    Some(at, textOfRange source at, $", {name}{textOfRange source at}")
                                // juxtaposed: `X "msg"` → `X("msg", ex)`
                                | other ->
                                    let at = Range.mkRange e.Range.FileName funcRange.End other.Range.End
                                    Some(at, textOfRange source at, $"({textOfRange source other.Range}, {name})")

                            // a pattern the fix could not name leaves the
                            // constructor without its argument: note only
                            match binder, patEdits, argEdit with
                            | None, [], _ ->
                                {
                                    Range = e.Range
                                    Raised = typeId.idText
                                    Binder = name
                                    Edits = []
                                }
                            | _, _, Some edit ->
                                {
                                    Range = e.Range
                                    Raised = typeId.idText
                                    Binder = name
                                    Edits = patEdits @ [ edit ]
                                }
                            | _ -> ()
                    | None -> ()
                | SynExpr.App(isInfix = false) when
                    (match headIdent e with
                     | Some f -> failureFunctions.Contains f.idText
                     | None -> false)
                    ->
                    let f = (headIdent e).Value

                    // the outermost application only: the nested ones are
                    // the same call short of its later arguments
                    let outermost =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = inner)) :: _ when Range.equals inner.Range e.Range ->
                            false
                        | _ -> true

                    if outermost then
                        match handlerOf path e.Range with
                        | Some(SynMatchClause(pat = pat; resultExpr = result)) ->
                            let unread =
                                match binderOf pat with
                                | Some name -> not (mentions name result.Range)
                                | None -> true

                            if unread then
                                {
                                    Range = e.Range
                                    Raised = f.idText
                                    Binder = binderOf pat |> Option.defaultValue "ex"
                                    Edits = []
                                }
                        | None -> ()
                | _ -> ()
        ]
