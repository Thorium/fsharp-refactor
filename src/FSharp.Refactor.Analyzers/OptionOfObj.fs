/// Refactoring: a null test that wraps the value into an option is
/// `Option.ofObj` (or `ValueOption.ofObj`).
///
///     if isNull x then None else Some x        →  Option.ofObj x
///     if x <> null then Some x else None       →  Option.ofObj x
///     match x with                             →  Option.ofObj x
///     | null -> None
///     | v -> Some v
///
/// Safety rules:
///   - the tested value must be a plain identifier: `if isNull o.P then
///     None else Some o.P` reads the property twice where `Option.ofObj o.P`
///     reads it once, which is observable for impure getters
///   - `Some`/`None` must resolve to FSharp.Core's option (or value-option)
///     cases via the typed check results, so shadowing DUs never match
///   - the file must have no type errors
module FSharp.Refactor.OptionOfObj

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        /// "Option" or "ValueOption", for the message.
        ModuleName: string
    }

/// `isNull x`, `x = null`, `null = x` → (x, negated, testIdent); and the
/// negated forms. The test identifier (isNull or the operator) is returned
/// so the caller can verify it resolves to FSharp.Core, not a shadow.
[<return: Struct>]
let private (|NullTest|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = SynExpr.Ident x) when fn.idText = "isNull" ->
        ValueSome(x, false, fn)
    | SynExpr.App(
        isInfix = false
        funcExpr = IdentName "not"
        argExpr = SynExpr.Paren(
            expr = SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = SynExpr.Ident x))) when
        fn.idText = "isNull"
        ->
        ValueSome(x, true, fn)
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = lhs); argExpr = rhs) when
        op.idText = "op_Equality" || op.idText = "op_Inequality"
        ->
        let negated = op.idText = "op_Inequality"

        match lhs, rhs with
        | SynExpr.Ident x, SynExpr.Null _
        | SynExpr.Null _, SynExpr.Ident x -> ValueSome(x, negated, op)
        | _ -> ValueNone
    | _ -> ValueNone

/// A bare `None`/`ValueNone` identifier.
[<return: Struct>]
let private (|NoneIdent|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.Ident id when id.idText = "None" || id.idText = "ValueNone" -> ValueSome id
    | _ -> ValueNone

/// `Some <ident>` / `ValueSome <ident>`, returning (caseIdent, argIdent).
[<return: Struct>]
let private (|SomeOfIdent|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident someId; argExpr = SynExpr.Ident arg) when
        someId.idText = "Some" || someId.idText = "ValueSome"
        ->
        ValueSome(someId, arg)
    | _ -> ValueNone

/// The matching pair of case names, or ValueNone for a Some/None mix-up.
let private pairModule (someId: Ident) (noneId: Ident) =
    match someId.idText, noneId.idText with
    | "Some", "None" -> ValueSome("Option", OptionModule.optionConfig.CoreFullNamePrefix)
    | "ValueSome", "ValueNone" -> ValueSome("ValueOption", OptionModule.valueOptionConfig.CoreFullNamePrefix)
    | _ -> ValueNone

/// An untyped candidate: (whole expression, tested ident, Some, None).
/// TestIdent is the isNull/operator identifier, None for the match form
/// (a `null` pattern cannot be shadowed).
type private Candidate =
    {
        Expr: SynExpr
        Tested: Ident
        SomeIdent: Ident
        NoneIdent: Ident
        TestIdent: Ident option
    }

let private findCandidates (parseTree: ParsedInput) : Candidate list =
    let candidates = ResizeArray<Candidate>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.IfThenElse(
                    ifExpr = NullTest(x, negated, testId); thenExpr = t; elseExpr = Some e; trivia = trivia) when
                    not trivia.IsElif
                    ->
                    let wrapArm, noneArm = if negated then t, e else e, t

                    match wrapArm, noneArm with
                    | SomeOfIdent(someId, arg), NoneIdent noneId when arg.idText = x.idText ->
                        candidates.Add
                            {
                                Expr = expr
                                Tested = x
                                SomeIdent = someId
                                NoneIdent = noneId
                                TestIdent = Some testId
                            }
                    | _ -> ()
                | SynExpr.Match(expr = SynExpr.Ident x; clauses = [ nullClause; wrapClause ]) ->
                    match simpleClause nullClause, simpleClause wrapClause with
                    | Some(SynPat.Null _, NoneIdent noneId), Some(wrapPat, SomeOfIdent(someId, arg)) ->
                        let bindsTested =
                            match wrapPat with
                            | SynPat.Named(ident = SynIdent(ident = v)) -> arg.idText = v.idText
                            | SynPat.Wild _ -> arg.idText = x.idText
                            | _ -> false

                        if bindsTested then
                            candidates.Add
                                {
                                    Expr = expr
                                    Tested = x
                                    SomeIdent = someId
                                    NoneIdent = noneId
                                    TestIdent = None
                                }
                    | _ -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq candidates

/// Find null tests wrapping into options. Requires typed check results;
/// emits nothing when the file has type errors.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        findCandidates parseTree
        |> List.choose (fun c ->
            match pairModule c.SomeIdent c.NoneIdent with
            | ValueSome(moduleName, corePrefix) when
                OptionModule.resolvesToCoreCase check source corePrefix c.SomeIdent
                && OptionModule.resolvesToCoreCase check source corePrefix c.NoneIdent
                // a shadowed isNull / (=) can have arbitrary semantics
                && (c.TestIdent |> Option.forall (OptionModule.resolvesToCoreOperator check source))
                ->
                Some
                    {
                        Range = c.Expr.Range
                        OriginalText = textOfRange source c.Expr.Range
                        ReplacementText = $"{moduleName}.ofObj {c.Tested.idText}"
                        ModuleName = moduleName
                    }
            | _ -> None)
