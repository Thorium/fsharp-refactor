/// Refactoring: simplify common boolean, option-comparison, and emptiness
/// idioms.
///
///     if c then true else false        →  c
///     if c then false else true        →  not c
///     x = None      /  None = x        →  x.IsNone                (typed-gated)
///     x <> None                        →  x.IsSome
///     x = ValueNone                    →  x.IsNone
///     Option.isSome x / x |> Option.isSome  →  x.IsSome
///     List.length xs = 0               →  List.isEmpty xs
///     xs |> Seq.length = 0             →  xs |> Seq.isEmpty
///     Array.length xs > 0              →  not (Array.isEmpty xs)
///     Set.count s = 0                  →  Set.isEmpty s
///
/// The property reads directly where the module function is a call; the
/// receiver must be a name (or dotted path) whose type the checker has
/// settled when it reaches the expression. An UNANNOTATED parameter's type
/// is inferred from its uses, which may come later — there `x.IsSome` is
/// FS0072 "lookup on object of indeterminate type" while `Option.isSome x`
/// infers fine — so a None comparison on such a receiver keeps the module
/// form (`x |> Option.isSome`) and a module call on it stays. A test whose
/// branch then reads the payload (`x.Value`, `Option.get x`) is a match in
/// disguise and is left to FR0034.
///
/// The emptiness rewrite is also a performance fix for Seq: `Seq.length`
/// forces the whole sequence, `Seq.isEmpty` looks at one element.
///
/// The boolean and emptiness rules are parse-only (the collection module
/// name pins the type); the None-comparison rules require typed check
/// results proving the case is really FSharp.Core's None/ValueNone.
module FSharp.Refactor.Simplification

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type SimplificationKind =
    /// `if c then true else false` / `if c then false else true`
    | BooleanIdentity
    /// `x = None`, `x <> ValueNone`, ...
    | OptionComparison
    /// `Option.isSome x`, `x |> ValueOption.isNone`, ... → the property
    | OptionProperty
    /// `List.length xs = 0`, `xs |> Seq.length > 0`, ...
    | Emptiness

type Suggestion =
    { Range: range
      OriginalText: string
      ReplacementText: string
      Kind: SimplificationKind }

/// `lhs OP rhs` for a named infix operator.
[<return: Struct>]
let private (|InfixApp|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName op; argExpr = lhs); argExpr = rhs) when
        op.StartsWith "op_"
        ->
        ValueSome(op, lhs, rhs)
    | _ -> ValueNone

/// A bare `None` or `ValueNone` expression, with the module and FullName
/// prefix needed for the rewrite and the typed gate.
[<return: Struct>]
let private (|NoneCaseIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident ident when ident.idText = "None" -> ValueSome(ident, "Option", "Microsoft.FSharp.Core.Option<")
    | SynExpr.Ident ident when ident.idText = "ValueNone" ->
        ValueSome(ident, "ValueOption", "Microsoft.FSharp.Core.ValueOption<")
    | _ -> ValueNone

/// `M.length` / `M.count` for a collection module with an isEmpty function.
[<return: Struct>]
let private (|LengthFunc|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) ->
        match m.idText, f.idText with
        | ("List" | "Seq" | "Array"), "length"
        | ("Set" | "Map"), "count" -> ValueSome(m.idText, f)
        | _ -> ValueNone
    | _ -> ValueNone

/// A length/count expression: direct `M.length xs` or piped `xs |> M.length`.
/// Returns the module name, the function ident (for the shadowing gate), the
/// collection argument, and whether it was piped.
[<return: Struct>]
let private (|LengthOf|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = LengthFunc(m, f); argExpr = arg) -> ValueSome(m, f, arg, false)
    | PipeApp(arg, LengthFunc(m, f)) -> ValueSome(m, f, arg, true)
    | _ -> ValueNone

/// The operator ident of an infix application, for symbol gating.
[<return: Struct>]
let private (|InfixOpIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op)) -> ValueSome op
    | _ -> ValueNone

/// `Option.isSome` / `Option.isNone` (and the ValueOption pair): the
/// function ident and whether it is the Some test.
[<return: Struct>]
let private (|OptionTestFunc|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) when
        (m.idText = "Option" || m.idText = "ValueOption")
        && (f.idText = "isSome" || f.idText = "isNone")
        ->
        ValueSome(f, f.idText = "isSome")
    | _ -> ValueNone

/// Is this `isSome`/`isNone` FSharp.Core's, not a user module named Option?
let private isCoreOptionTest (check: FSharpCheckFileResults) (source: ISourceText) (f: Ident) =
    let r = f.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ f.idText ]) with
    | Some symbolUse ->
        let name = OptionModule.fullNameOf symbolUse.Symbol
        name.StartsWith "Microsoft.FSharp.Core." && name.Contains "Option"
    | None -> false

/// Find simplifiable expressions. `check` enables the typed None-comparison
/// rules; without it only the parse-only rules run.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults option) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    // consulted only when an option test is found
    let evidence = lazy (OptionModule.declarationEvidence parseTree)

    let add (range: range) (replacement: string) kind =
        suggestions.Add
            { Range = range
              OriginalText = textOfRange source range
              ReplacementText = replacement
              Kind = kind }

    let noneComparison
        (range: range)
        (op: string)
        (opIdent: Ident)
        (other: SynExpr)
        (ident: Ident)
        (m: string)
        (prefix: string)
        =
        // both halves gated: None must be FSharp.Core's case AND the `=`
        // must be FSharp.Core's operator — a DSL-shadowed equality over
        // options means something else entirely
        let gate =
            check
            |> Option.exists (fun check ->
                OptionModule.resolvesToCoreCase check source prefix ident
                && OptionModule.resolvesToCoreOperator check source opIdent)

        if gate && isSingleLine other.Range then
            let fn = if op = "op_Equality" then "isNone" else "isSome"

            // the property where the receiver's type is settled; the
            // module function keeps inference going where it is not
            match other with
            | OptionModule.ReceiverPath(ids, text) when
                check
                |> Option.exists (fun c -> OptionModule.receiverSettled c source evidence.Value ids)
                ->
                let property = if op = "op_Equality" then "IsNone" else "IsSome"
                add range $"{text}.{property}" SimplificationKind.OptionComparison
            | _ -> add range (sprintf "%s |> %s.%s" (atomicText source other) m fn) SimplificationKind.OptionComparison

    let emptiness (range: range) (negated: bool) (m: string) (fIdent: Ident) (arg: SynExpr) (piped: bool) =
        // shadowing gate: `Seq.length` must be FSharp.Core's, not a user
        // module that happens to be named Seq. With typed results at hand
        // the symbol proves it; parse-only callers keep the old behavior
        let genuine =
            match check with
            | Some check ->
                let r = fIdent.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                (match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ fIdent.idText ]) with
                 | Some symbolUse ->
                     match symbolUse.Symbol with
                     | :? FSharpMemberOrFunctionOrValue as value ->
                         (OptionModule.fullNameOf value).StartsWith "Microsoft.FSharp.Collections"
                     | _ -> false
                 | None -> false)
            | None -> true

        if genuine && isSingleLine arg.Range then
            let replacement =
                match piped, negated with
                | true, false -> sprintf "%s |> %s.isEmpty" (textOfRange source arg.Range) m
                | true, true -> sprintf "%s |> %s.isEmpty |> not" (textOfRange source arg.Range) m
                | false, false -> sprintf "%s.isEmpty %s" m (textOfRange source arg.Range)
                | false, true -> sprintf "not (%s.isEmpty %s)" m (textOfRange source arg.Range)

            add range replacement SimplificationKind.Emptiness

    // a test whose branch then reads the payload (`x.Value`, `Option.get
    // x`) is a match in disguise: FR0034 binds the payload, and `IsSome`
    // beside `.Value` is the spelling to avoid, not the one to produce
    let payloadRead (path: SyntaxNode list) (test: SynExpr) (receiver: SynExpr) =
        let x =
            System.Text.RegularExpressions.Regex.Escape(textOfRange source receiver.Range)

        let reads (r: range) =
            System.Text.RegularExpressions.Regex.IsMatch(
                textOfRange source r,
                $@"{x}\.Value\b|(Option|ValueOption)\.get\s+\(?\s*{x}\b|{x}\s*\|>\s*(Option|ValueOption)\.get\b"
            )

        path
        |> List.exists (fun node ->
            match node with
            | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond) as ifExpr) when
                Range.rangeContainsRange cond.Range test.Range
                ->
                reads ifExpr.Range
            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent o)) as chain) when
                o.idText = "op_BooleanAnd" || o.idText = "op_BooleanOr"
                ->
                reads chain.Range
            | _ -> false)

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                // if c then true else false / if c then false else true
                // trivia.IsElif guard: an elif node's range starts at the elif
                // keyword, so replacing it with the bare condition would glue
                // the condition onto the preceding branch
                | SynExpr.IfThenElse(
                    ifExpr = cond; thenExpr = BoolConst thenValue; elseExpr = Some(BoolConst elseValue); trivia = trivia) when
                    not trivia.IsElif
                    && thenValue <> elseValue
                    && isSingleLine cond.Range
                    && isSafeInline cond
                    ->
                    let replacement =
                        if thenValue then
                            textOfRange source cond.Range
                        else
                            "not " + atomicText source cond

                    add expr.Range replacement SimplificationKind.BooleanIdentity
                // x = None / None = x / x <> None (and ValueNone)
                | InfixApp(("op_Equality" | "op_Inequality") as op, NoneCaseIdent(ident, m, prefix), other)
                | InfixApp(("op_Equality" | "op_Inequality") as op, other, NoneCaseIdent(ident, m, prefix)) ->
                    match expr with
                    | InfixOpIdent opIdent when not (payloadRead path expr other) ->
                        noneComparison expr.Range op opIdent other ident m prefix
                    | _ -> ()
                // Option.isSome x / x |> Option.isNone → the property
                | SynExpr.App(isInfix = false; funcExpr = OptionTestFunc(f, isSome); argExpr = receiver)
                | PipeApp(receiver, OptionTestFunc(f, isSome)) ->
                    match check, receiver with
                    | Some c, OptionModule.ReceiverPath(ids, text) when
                        isCoreOptionTest c source f
                        && OptionModule.receiverSettled c source evidence.Value ids
                        && not (payloadRead path expr receiver)
                        ->
                        let property = if isSome then "IsSome" else "IsNone"
                        add expr.Range $"{text}.{property}" SimplificationKind.OptionProperty
                    | _ -> ()
                // length/count compared with zero
                | InfixApp("op_Equality", LengthOf(m, f, arg, piped), ZeroConst)
                | InfixApp("op_Equality", ZeroConst, LengthOf(m, f, arg, piped)) ->
                    emptiness expr.Range false m f arg piped
                | InfixApp("op_Inequality", LengthOf(m, f, arg, piped), ZeroConst)
                | InfixApp("op_Inequality", ZeroConst, LengthOf(m, f, arg, piped))
                | InfixApp("op_GreaterThan", LengthOf(m, f, arg, piped), ZeroConst)
                | InfixApp("op_LessThan", ZeroConst, LengthOf(m, f, arg, piped)) ->
                    emptiness expr.Range true m f arg piped
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
