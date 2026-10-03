/// FR0178 (correctness, note), twin of the C# rule: `.Value` read in the
/// branch where the option was just tested to be empty.
///
///     if order.Reference.IsSome then
///         None
///     else
///         lookup order.Reference.Value     // throws every time it runs
///
/// The guard is upside down, or the branches are swapped: the read sits
/// where `IsSome` is known false, so it raises (`option`) or returns a
/// default that was never set (`voption` raises too) whenever the branch
/// runs.
///
/// The tests read: `x.IsSome`, `x.IsNone`, `not` of either, `x = None`,
/// `x <> None` (and the `ValueNone` spellings), `Option.isSome x`,
/// `Option.isNone x` (and `ValueOption`), alone as an `if` condition. x is
/// a name or a property chain; the test must resolve to FSharp.Core's
/// option or voption.
///
/// Quiet when the branch could have refilled the value or tests it again:
/// an assignment to x or to anything x is read through, a nested `if` or
/// `match` on x, and code under a lambda or a local function, which runs
/// when it is called and not when the branch does. An option read through
/// a property is also quiet once any call in the branch has finished
/// before the read - the call may have filled it.
///
/// Note-only: whether the test or the branches are wrong is not in the
/// code.
module FSharp.Refactor.EmptyOptionValue

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `.Value` read.
        Range: range
        /// The option as written.
        Receiver: string
        /// The test as written.
        Test: string
    }

let private optionOwners =
    set
        [
            "Microsoft.FSharp.Core.FSharpOption`1"
            "Microsoft.FSharp.Core.FSharpValueOption`1"
            "Microsoft.FSharp.Core.OptionModule"
            "Microsoft.FSharp.Core.ValueOption"
        ]

let private squeeze (text: string) =
    text |> String.filter (fun c -> not (System.Char.IsWhiteSpace c))

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the member, function or case belongs to option / voption
        let onOption (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                (try
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as value ->
                        value.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.exists optionOwners.Contains
                    | :? FSharpUnionCase as case ->
                        let owner = OptionModule.stripAbbreviations case.ReturnType

                        owner.HasTypeDefinition
                        && (owner.TypeDefinition.TryFullName |> Option.exists optionOwners.Contains)
                    | _ -> false
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | None -> false

        let isMutable (ident: Ident) =
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value ->
                    (try
                        value.IsMutable
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         true)
                | _ -> true
            | None -> true

        // the first name of the tested option, wherever the test names it
        let rec rootIdent (e: SynExpr) : Ident voption =
            match stripParens e with
            | SynExpr.Ident id -> ValueSome id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = id :: _)) when
                id.idText <> "Option" && id.idText <> "ValueOption"
                ->
                ValueSome id
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; argExpr = lhs); argExpr = rhs) ->
                match rootIdent lhs with
                | ValueSome id when id.idText <> "None" && id.idText <> "ValueNone" -> ValueSome id
                | _ -> rootIdent rhs
            | SynExpr.App(isInfix = false; argExpr = arg) -> rootIdent arg
            | _ -> ValueNone

        let names (ids: Ident list) = ids |> List.map (fun i -> i.idText)

        let idsOf (e: SynExpr) =
            match stripParens e with
            | SynExpr.Ident id -> ValueSome [ id ]
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome ids
            | _ -> ValueNone

        // the receiver's names and whether the test holds when it is Some
        let rec testOf (e: SynExpr) : (string list * bool) voption =
            match stripParens e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2
                && ((List.last ids).idText = "IsSome" || (List.last ids).idText = "IsNone")
                && onOption (List.last ids)
                ->
                ValueSome(names (ids |> List.take (ids.Length - 1)), (List.last ids).idText = "IsSome")
            | SynExpr.App(isInfix = false; funcExpr = IdentName "not"; argExpr = inner) ->
                match testOf inner with
                | ValueSome(receiver, whenSome) -> ValueSome(receiver, not whenSome)
                | ValueNone -> ValueNone
            | SynExpr.App(
                isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; f ])); argExpr = arg) when
                (f.idText = "isSome" || f.idText = "isNone") && onOption f
                ->
                match idsOf arg with
                | ValueSome ids -> ValueSome(names ids, f.idText = "isSome")
                | ValueNone -> ValueNone
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs)
                argExpr = rhs) when op.idText = "op_Equality" || op.idText = "op_Inequality" ->
                let isNone (side: SynExpr) =
                    match stripParens side with
                    | SynExpr.Ident id -> (id.idText = "None" || id.idText = "ValueNone") && onOption id
                    | _ -> false

                let receiver =
                    if isNone rhs then idsOf lhs
                    elif isNone lhs then idsOf rhs
                    else ValueNone

                match receiver with
                | ValueSome ids -> ValueSome(names ids, op.idText = "op_Inequality")
                | ValueNone -> ValueNone
            | _ -> ValueNone

        let within (outer: range) (inner: range) = Range.rangeContainsRange outer inner

        let isPrefix (prefix: string list) (whole: string list) =
            prefix.Length <= whole.Length && List.take prefix.Length whole = prefix

        // the names an assignment writes
        let assigned (e: SynExpr) =
            match e with
            | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)) -> ValueSome(names ids)
            | SynExpr.Set(targetExpr = target)
            | SynExpr.DotSet(targetExpr = target) ->
                match idsOf target with
                | ValueSome ids -> ValueSome(names ids)
                | ValueNone -> ValueNone
            | _ -> ValueNone


        // the reads of the option's value inside a region where it is known
        // to be empty
        let readsIn (condition: SynExpr) (receiver: string list) (branch: SynExpr) : Suggestion list =
            let inBranch = AstIndex.exprsWithin index branch.Range

            // the option, or what it is read through, written again
            let refilled =
                inBranch
                |> Array.exists (fun (_, inner) ->
                    match assigned inner with
                    | ValueSome target -> isPrefix target receiver || isPrefix receiver target
                    | ValueNone -> false)

            let receiverText = String.concat "." receiver

            // a second test of the same option, a lambda or a local
            // function between the region and the read
            let shielded (path: SyntaxNode list) =
                path
                |> List.exists (fun node ->
                    match node with
                    | SyntaxNode.SynExpr inner when within branch.Range inner.Range ->
                        match inner with
                        | SynExpr.Lambda _
                        | SynExpr.MatchLambda _
                        | SynExpr.ObjExpr _ -> true
                        | SynExpr.IfThenElse(ifExpr = again) ->
                            (squeeze (textOfRange source again.Range)).Contains receiverText
                        | SynExpr.Match(expr = matched)
                        | SynExpr.MatchBang(expr = matched) ->
                            (squeeze (textOfRange source matched.Range)).Contains receiverText
                        | _ -> false
                    | SyntaxNode.SynBinding(SynBinding(
                        headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)); range = r)) ->
                        within branch.Range r
                    | _ -> false)

            // a `let mutable` a closure may write
            let mutableRoot =
                lazy
                    (match rootIdent condition with
                     | ValueSome root -> isMutable root
                     | ValueNone -> true)

            // an option read through a property, or held in a mutable, can
            // be refilled by any call that finished before the read
            // (`if h.Slot.IsNone then load (); h.Slot.Value`)
            let callBefore (read: range) =
                (receiver.Length > 1 || mutableRoot.Force())
                && inBranch
                   |> Array.exists (fun (_, inner) ->
                       match inner with
                       | SynExpr.App _ -> Position.posGeq read.Start inner.Range.End
                       | _ -> false)

            let found (read: range) =
                {
                    Range = read
                    Receiver = receiverText
                    Test = textOfRange source condition.Range
                }

            if refilled then
                []
            else
                [
                    for path, inner in inBranch do
                        match inner with
                        // x.Value / x.Value.Member
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                            ids.Length > receiver.Length
                            && isPrefix receiver (names ids)
                            && ids.[receiver.Length].idText = "Value"
                            && not (shielded path)
                            && not (callBefore ids.Head.idRange)
                            ->
                            found (Range.unionRanges ids.Head.idRange ids.[receiver.Length].idRange)
                        // Option.get x / ValueOption.get x
                        | SynExpr.App(
                            isInfix = false
                            funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; f ]))
                            argExpr = arg) when
                            f.idText = "get"
                            && onOption f
                            && (match idsOf arg with
                                | ValueSome ids -> names ids = receiver
                                | ValueNone -> false)
                            && not (shielded path)
                            && not (callBefore inner.Range)
                            ->
                            found inner.Range
                        | _ -> ()
                ]

        // `None` / `ValueNone` as a match arm's whole pattern
        let isNoneArm (p: SynPat) =
            match p with
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                (id.idText = "None" || id.idText = "ValueNone") && onOption id
            | SynPat.Named(ident = SynIdent(ident = id)) ->
                (id.idText = "None" || id.idText = "ValueNone") && onOption id
            | _ -> false

        [
            for _, e in index.Exprs do
                if not (spansDirective source e.Range) then
                    match e with
                    // if x.IsSome then ... else <x is empty here>
                    | SynExpr.IfThenElse(ifExpr = condition; thenExpr = thenBranch; elseExpr = elseBranch) ->
                        match testOf condition with
                        | ValueSome(receiver, whenSome) ->
                            match (if whenSome then elseBranch else Some thenBranch) with
                            | Some branch -> yield! readsIn condition receiver branch
                            | None -> ()
                        | ValueNone -> ()
                    // x.IsNone && <x is empty here> / x.IsSome || <x is empty here>
                    | SynExpr.App(
                        isInfix = false
                        funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs)
                        argExpr = rhs) when op.idText = "op_BooleanAnd" || op.idText = "op_BooleanOr" ->
                        match testOf lhs with
                        | ValueSome(receiver, whenSome) when whenSome = (op.idText = "op_BooleanOr") ->
                            yield! readsIn lhs receiver rhs
                        | _ -> ()
                    // match x with ... | None -> <x is empty here>
                    | SynExpr.Match(expr = matched; clauses = clauses) ->
                        match idsOf matched with
                        | ValueSome ids ->
                            for SynMatchClause(pat = p; whenExpr = guard; resultExpr = result) in clauses do
                                if guard.IsNone && isNoneArm p then
                                    yield! readsIn matched (names ids) result
                        | ValueNone -> ()
                    | _ -> ()
        ]
        |> List.distinctBy (fun s -> s.Range)
