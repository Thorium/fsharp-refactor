/// Refactoring: rewrite manual Some/None (and ValueSome/ValueNone) matching
/// with Option-module (ValueOption-module) functions.
///
///     match x with | Some v -> Some (f v) | None -> None   →  x |> Option.map (fun v -> f v)
///     match x with | Some v -> f v        | None -> None   →  x |> Option.bind (fun v -> f v)
///     match x with | Some v -> v          | None -> None   →  x |> Option.flatten
///     match x with | Some v -> Some v     | None -> None   →  x
///     match x with | Some v -> v          | None -> d      →  x |> Option.defaultValue d
///     match x with | Some _ -> true       | None -> false  →  x.IsSome (x |> Option.isSome on an unannotated parameter)
///     match x with | Some _ -> false      | None -> true   →  x.IsNone
///     match x with | Some v -> f v        | None -> ()     →  x |> Option.iter (fun v -> f v)
///     match x with | Some v -> g v        | None -> d      →  x |> Option.map (fun v -> g v) |> Option.defaultValue d
///
/// The same shapes are recognized for ValueSome/ValueNone, rewritten with the
/// ValueOption module. Default values that are not pure atoms (identifiers or
/// constants) are wrapped as `defaultWith (fun () -> d)` instead, preserving
/// the original laziness: the match evaluated the default only in the None
/// branch, and `defaultValue` would evaluate it always.
///
/// Clause order may be reversed. Safety rules:
///   - exactly two clauses, no `when` guards, single-line scrutinee and bodies
///   - the case names must resolve to FSharp.Core's option/voption cases
///     (checked against the typed results, so shadowing user types never
///     produces a wrong rewrite)
///   - the file must have no type errors (the bind rule relies on the match
///     having typechecked: when the none branch is `None`, the some branch is
///     known to be option-typed)
///   - non-atomic expressions are parenthesized when inlined
module FSharp.Refactor.OptionModule

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

/// Names for one wrapper family: Some/None/Option or ValueSome/ValueNone/ValueOption.
type WrapperConfig =
    {
        /// The value-carrying case, e.g. "Some".
        SomeName: string
        /// The empty case, e.g. "None".
        NoneName: string
        /// The module whose functions replace the match, e.g. "Option".
        ModuleName: string
        /// FullName prefix that proves a case belongs to FSharp.Core.
        CoreFullNamePrefix: string
    }

let optionConfig =
    { SomeName = "Some"
      NoneName = "None"
      ModuleName = "Option"
      // anchored with '<' so a hypothetical Option2 type cannot prefix-match
      CoreFullNamePrefix = "Microsoft.FSharp.Core.Option<" }

let valueOptionConfig =
    { SomeName = "ValueSome"
      NoneName = "ValueNone"
      ModuleName = "ValueOption"
      CoreFullNamePrefix = "Microsoft.FSharp.Core.ValueOption<" }

type Suggestion =
    {
        /// Range of the whole match expression, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The module function used, e.g. "Option.map", or "" for identity.
        Target: string
    }

/// `Some v`, `Some (v)`, `Some _` as a pattern: returns the case ident (for
/// symbol resolution) and the bound variable name (None for wildcard).
let private somePat (cfg: WrapperConfig) (p: SynPat) =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ someIdent ]); argPats = SynArgPats.Pats [ arg ]) when
        someIdent.idText = cfg.SomeName
        ->
        boundVar arg |> Option.map (fun v -> someIdent, v)
    | _ -> None

/// `None` as a pattern: returns the case ident for symbol resolution.
let private nonePat (cfg: WrapperConfig) (p: SynPat) =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ noneIdent ]); argPats = SynArgPats.Pats []) when
        noneIdent.idText = cfg.NoneName
        ->
        Some noneIdent
    | _ -> None

/// `<pipe> |> M.defaultValue d` for pure atoms, else `<pipe> |> M.defaultWith (fun () -> d)`.
let private defaultCall (cfg: WrapperConfig) (source: ISourceText) (defaultBody: SynExpr) =
    if isPureAtom defaultBody then
        sprintf "%s.defaultValue %s" cfg.ModuleName (atomicText source defaultBody), $"{cfg.ModuleName}.defaultValue"
    else
        sprintf "%s.defaultWith (fun () -> %s)" cfg.ModuleName (textOfRange source defaultBody.Range),
        $"{cfg.ModuleName}.defaultWith"

/// Is this expression in IMPLICIT-YIELD position of a list/array/seq
/// comprehension or computation expression? There `| None -> ()` means
/// "yield nothing" and a non-unit branch yields — the match is control
/// flow, not a value. Rewriting it into a combinator breaks the
/// comprehension: found on Fuuga, where
///
///     [ if a then "A"
///       match g with Some g -> sprintf "G(%s)" g.Name | None -> () ]
///
/// became `Option.iter (fun g -> sprintf ...)` — Option.iter wants a
/// unit-returning function and got a string one. Walking the path
/// outward: a binding, lambda, application argument or explicit yield
/// puts the expression back in VALUE position; reaching the
/// comprehension first means implicit yield. Shared with ResultModule.
let implicitYieldPosition (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed _)
        | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) -> Some true
        | SyntaxNode.SynBinding _
        | SyntaxNode.SynExpr(SynExpr.Lambda _)
        | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
        | SyntaxNode.SynExpr(SynExpr.App _)
        // (let! / use! are LetOrUse with IsBang since FCS 43.12; their
        // right-hand sides arrive through the SynBinding barrier above)
        | SyntaxNode.SynExpr(SynExpr.YieldOrReturn _)
        | SyntaxNode.SynExpr(SynExpr.YieldOrReturnFrom _) -> Some false
        | _ -> None)
    |> Option.defaultValue false

/// A candidate found syntactically; the case idents still need to be resolved
/// against the typed results before the suggestion is emitted.
type private Candidate =
    {
        MatchRange: range
        SomeIdent: Ident
        NoneIdent: Ident
        Replacement: string
        Target: string
        /// The matched expression, for the property spelling of a test.
        Scrutinee: SynExpr
    }

/// Decide the rewrite for a wrapper match, given the normalized parts.
let private rewrite
    (cfg: WrapperConfig)
    (source: ISourceText)
    (scrutinee: SynExpr)
    (boundVar: string option)
    (someBody: SynExpr)
    (noneBody: SynExpr)
    : (string * string) option =
    let pipeSource = atomicText source scrutinee
    let m = cfg.ModuleName

    /// `Some <e>` as an expression.
    let (|SomeApp|_|) (e: SynExpr) =
        match e with
        | SynExpr.App(funcExpr = SynExpr.Ident someIdent; argExpr = arg) when someIdent.idText = cfg.SomeName ->
            Some arg
        | _ -> None

    let (|NoneIdent|_|) (e: SynExpr) =
        match e with
        | IdentName t when t = cfg.NoneName -> Some()
        | _ -> None

    match someBody, noneBody with
    // ... | None -> None
    | SomeApp(IdentName v), NoneIdent when Some v = boundVar ->
        // Some v -> Some v: the whole match is the scrutinee itself
        Some(textOfRange source scrutinee.Range, "")
    | SomeApp inner, NoneIdent ->
        let body = textOfRange source (stripParens inner).Range
        Some(sprintf "%s |> %s.map (fun %s -> %s)" pipeSource m (lambdaParam boundVar) body, $"{m}.map")
    | IdentName v, NoneIdent when Some v = boundVar -> Some($"%s{pipeSource} |> %s{m}.flatten", $"{m}.flatten")
    | body, NoneIdent ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> %s.bind (fun %s -> %s)" pipeSource m (lambdaParam boundVar) bodyText, $"{m}.bind")
    // ... | None -> <something else>
    | BoolConst true, BoolConst false -> Some($"%s{pipeSource} |> %s{m}.isSome", $"{m}.isSome")
    | BoolConst false, BoolConst true -> Some($"%s{pipeSource} |> %s{m}.isNone", $"{m}.isNone")
    | IdentName v, defaultBody when Some v = boundVar ->
        let call, target = defaultCall cfg source defaultBody
        Some($"%s{pipeSource} |> %s{call}", target)
    | body, UnitConst ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> %s.iter (fun %s -> %s)" pipeSource m (lambdaParam boundVar) bodyText, $"{m}.iter")
    // `Some v -> pred v | None -> false/true` are exists/forall
    | body, BoolConst false ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> %s.exists (fun %s -> %s)" pipeSource m (lambdaParam boundVar) bodyText, $"{m}.exists")
    | body, BoolConst true ->
        let bodyText = textOfRange source (stripParens body).Range
        Some(sprintf "%s |> %s.forall (fun %s -> %s)" pipeSource m (lambdaParam boundVar) bodyText, $"{m}.forall")
    // the map+default combo, but not when a branch itself constructs a case:
    // the rewrite would still typecheck, yet the original match reads better
    | (SomeApp _ | NoneIdent), _
    | _, (SomeApp _ | NoneIdent) -> None
    | body, defaultBody ->
        let bodyText = textOfRange source (stripParens body).Range
        let call, target = defaultCall cfg source defaultBody

        Some(
            sprintf "%s |> %s.map (fun %s -> %s) |> %s" pipeSource m (lambdaParam boundVar) bodyText call,
            $"{m}.map + {target}"
        )

/// Would code moved from `bodyRange` into a fabricated lambda capture a
/// MUTABLE LOCAL (an expression-level `let mutable`) or a byref parameter
/// declared outside it? A match arm may write `total <- total + v` freely;
/// the closure these rules manufacture around the same code was error
/// FS0407 on every F# before 10, and byref capture still is. Shared by the
/// rules that wrap a branch body in `fun ... ->` (Option/Result wrappers,
/// OptionMatch, AddRange).
let capturesMutableLocal (index: AstIndex.Index) (bodyRange: range) : bool =
    let mutableNames =
        index.Exprs
        |> Array.collect (fun (_, e) ->
            match e with
            | LetOrUseE lou when not (Range.rangeContainsRange bodyRange lou.Range) ->
                lou.Bindings
                |> List.choose (fun (SynBinding(isMutable = isMut; headPat = p)) ->
                    if isMut then
                        match p with
                        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                        | _ -> None
                    else
                        None)
                |> Array.ofList
            | _ -> [||])

    let byrefNames =
        index.Pats
        |> Array.choose (fun (_, p) ->
            match p with
            | SynPat.Typed(
                pat = SynPat.Named(ident = SynIdent(ident = id))
                targetType = SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = tids)))) when
                not tids.IsEmpty
                && (let t = (List.last tids).idText in t = "byref" || t = "inref" || t = "outref")
                ->
                Some id.idText
            | _ -> None)

    let names = Set.ofArray (Array.append mutableNames byrefNames)

    not names.IsEmpty
    && index.Exprs
       |> Array.exists (fun (_, e) ->
           match e with
           | SynExpr.Ident id -> names.Contains id.idText && Range.rangeContainsRange bodyRange id.idRange
           | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) ->
               names.Contains first.idText && Range.rangeContainsRange bodyRange first.idRange
           | SynExpr.LongIdentSet(SynLongIdent(id = first :: _), _, _) ->
               names.Contains first.idText && Range.rangeContainsRange bodyRange e.Range
           | _ -> false)

let private findCandidates (cfg: WrapperConfig) (parseTree: ParsedInput) (source: ISourceText) : Candidate list =
    let candidates = ResizeArray<Candidate>()

    let (|SomePat|_|) = somePat cfg
    let (|NonePat|_|) = nonePat cfg

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.Match(expr = scrutinee; clauses = clauses; range = m) ->
                    // a match may sit unparenthesized as an infix operand
                    // (`1 + match ...`); our pipeline replacement is not as
                    // greedy as the match was, so it must be parenthesized there
                    let inOperandPosition =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.App(argExpr = arg)) :: _ -> arg.Range = m
                        | _ -> false

                    let normalized =
                        match clauses |> List.map simpleClause with
                        | [ Some(SomePat(someIdent, boundVar), someBody); Some(NonePat noneIdent, noneBody) ]
                        | [ Some(NonePat noneIdent, noneBody); Some(SomePat(someIdent, boundVar), someBody) ] ->
                            Some(someIdent, boundVar, someBody, noneIdent, noneBody)
                        | _ -> None

                    match normalized with
                    | Some(someIdent, boundVar, someBody, noneIdent, noneBody) when
                        isSingleLine scrutinee.Range
                        && isSingleLine someBody.Range
                        && isSingleLine noneBody.Range
                        && isPlainBody someBody
                        && isPlainBody noneBody
                        && not (capturesMutableLocal (AstIndex.ofTree parseTree) someBody.Range)
                        && not (capturesMutableLocal (AstIndex.ofTree parseTree) noneBody.Range)
                        && not (implicitYieldPosition path)
                        ->
                        match rewrite cfg source scrutinee boundVar someBody noneBody with
                        | Some(replacement, target) ->
                            let replacement =
                                if inOperandPosition && not (Regex.IsMatch(replacement, @"^[\w.]+$")) then
                                    $"({replacement})"
                                else
                                    replacement

                            candidates.Add
                                { MatchRange = m
                                  SomeIdent = someIdent
                                  NoneIdent = noneIdent
                                  Replacement = replacement
                                  Target = target
                                  Scrutinee = scrutinee }
                        | None -> ()
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq candidates

/// The exceptions FCS symbol properties (FullName, ApparentEnclosingEntity,
/// member metadata) raise for compiler-internal symbols without a stable
/// answer. Anything else is a programming error and propagates.
[<return: Struct>]
let (|FcsSymbolFailure|_|) (e: exn) =
    match e with
    | :? System.InvalidOperationException
    | :? System.NotSupportedException
    | :? System.ArgumentException
    | :? System.Collections.Generic.KeyNotFoundException -> ValueSome()
    | _ -> ValueNone

/// Follow F# type abbreviations (`string` → System.String) to the real
/// definition. Shared by every typed rule that compares type names.
[<TailCall>]
let rec stripAbbreviations (t: FSharpType) =
    // the INSTANCE's abbreviated type keeps the type arguments:
    // `('Key * 'T) list` is `List<'Key * 'T>`, whereas the definition's
    // AbbreviatedType is the bare `List<'T>` of `type 'T list = List<'T>`,
    // which lost FR0089 every tuple it was looking for
    if t.IsAbbreviation then
        stripAbbreviations t.AbbreviatedType
    elif t.HasTypeDefinition && t.TypeDefinition.IsFSharpAbbreviation then
        stripAbbreviations t.TypeDefinition.AbbreviatedType
    else
        t

/// The symbol's FullName, or "" where FCS has none to give.
let fullNameOf (symbol: FSharpSymbol) =
    try
        symbol.FullName
    with FcsSymbolFailure ->
        ""

/// True when the ident at this location resolves to a union case whose
/// FullName starts with the given FSharp.Core prefix. Shared with other
/// analyzers that must prove an ident is really e.g. option's None.
let resolvesToCoreCase (check: FSharpCheckFileResults) (source: ISourceText) (prefix: string) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpUnionCase as unionCase ->
            // e.g. "Microsoft.FSharp.Core.Option<_>.Some"
            (fullNameOf unionCase).StartsWith prefix
        | _ -> false
    | None -> false

/// The full name of a member's apparent enclosing entity, or "".
let enclosingFullName (value: FSharpMemberOrFunctionOrValue) =
    try
        value.ApparentEnclosingEntity
        |> Option.bind (fun e -> e.TryFullName)
        |> Option.defaultValue ""
    with FcsSymbolFailure ->
        ""

/// True when the identifier resolves into FSharp.Core's operator modules —
/// guards rules that pattern-match on names like `isNull`, `sprintf`, or
/// `(+)` against user-defined shadowing. `sprintf` and friends live in
/// ExtraTopLevelOperators rather than Operators.
let resolvesToCoreOperator (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let fullName = fullNameOf value

            fullName.StartsWith "Microsoft.FSharp.Core.Operators"
            || fullName.StartsWith "Microsoft.FSharp.Core.ExtraTopLevelOperators"
            // the qualified printf family: Printf.sprintf and friends
            || fullName.StartsWith "Microsoft.FSharp.Core.Printf"
        | _ -> false
    | None -> false

/// True when the file's typed results contain any error diagnostics.
let hasErrors (check: FSharpCheckFileResults) =
    check.Diagnostics
    |> Array.exists (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)

/// Find all wrapper matches for one config (Option or ValueOption) that can
/// be rewritten with module functions. Requires typed check results; emits
/// nothing when the file has type errors.
/// A receiver `.IsSome` can hang off: a name or a dotted path, with its
/// root ident (whose declaration decides whether the type is settled).
[<return: Struct>]
let (|ReceiverPath|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident root -> ValueSome(root, root.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = (root :: _ as ids))) -> ValueSome(root, identText ids)
    | _ -> ValueNone

/// The declaration positions of every UNANNOTATED parameter in the file:
/// function and member arguments, lambda parameters. Their types are
/// inferred from their uses, which may come after the expression at hand.
let unannotatedParameters (index: AstIndex.Index) : Set<int * int> =
    let names = System.Collections.Generic.HashSet<int * int>()

    let rec collect (p: SynPat) =
        match p with
        | SynPat.Typed _ -> ()
        | SynPat.Named(ident = SynIdent(ident = id)) ->
            names.Add((id.idRange.StartLine, id.idRange.StartColumn)) |> ignore
        | SynPat.As(lhsPat = l; rhsPat = r) ->
            collect l
            collect r
        | SynPat.Paren(pat = inner)
        | SynPat.Attrib(pat = inner) -> collect inner
        | SynPat.Tuple(elementPats = ps)
        | SynPat.Ands(pats = ps)
        | SynPat.ArrayOrList(elementPats = ps) -> List.iter collect ps
        | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> List.iter collect ps
        | _ -> ()

    let ofBinding (SynBinding(headPat = headPat)) =
        match headPat with
        | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> List.iter collect ps
        | _ -> ()

    let rec ofMembers (members: SynMemberDefns) =
        for m in members do
            match m with
            | SynMemberDefn.Member(memberDefn = b) -> ofBinding b
            | SynMemberDefn.LetBindings(bindings = bs) -> List.iter ofBinding bs
            | SynMemberDefn.Interface(members = Some ms) -> ofMembers ms
            | SynMemberDefn.GetSetMember(memberDefnForGet = g; memberDefnForSet = s) ->
                Option.iter ofBinding g
                Option.iter ofBinding s
            | _ -> ()

    for _, decl in index.Decls do
        match decl with
        | SynModuleDecl.Let(bindings = bs) -> List.iter ofBinding bs
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeRepr = repr; members = extra) in defns do
                match repr with
                | SynTypeDefnRepr.ObjectModel(members = ms) -> ofMembers ms
                | _ -> ()

                ofMembers extra
        | _ -> ()

    for _, e in index.Exprs do
        match e with
        | LetOrUseE lou -> List.iter ofBinding lou.Bindings
        | SynExpr.Lambda(parsedData = Some(pats, _)) -> List.iter collect pats
        | SynExpr.ObjExpr(bindings = bs; members = ms) ->
            List.iter ofBinding bs
            ofMembers ms
        | _ -> ()

    Set.ofSeq names

/// Is the root's type settled where it is read — declared anywhere but as
/// an unannotated parameter of this file?
let receiverSettled (check: FSharpCheckFileResults) (source: ISourceText) (unannotated: Set<int * int>) (root: Ident) =
    let r = root.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ root.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v ->
            (try
                let d = v.DeclarationLocation

                d.FileName <> r.FileName
                || not (unannotated.Contains((d.StartLine, d.StartColumn)))
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false
    | None -> false

let findWith (cfg: WrapperConfig) (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) =
    if hasErrors check then
        []
    else
        findCandidates cfg parseTree source
        |> List.filter (fun c ->
            not (spansDirective source c.MatchRange)
            && resolvesToCoreCase check source cfg.CoreFullNamePrefix c.SomeIdent
            && resolvesToCoreCase check source cfg.CoreFullNamePrefix c.NoneIdent)
        |> List.map (fun c ->
            // an isSome/isNone test reads as the property where the
            // receiver's type is settled — the spelling FR0010 produces,
            // so the two rules agree on what a test looks like
            let replacement =
                if c.Target.EndsWith ".isSome" || c.Target.EndsWith ".isNone" then
                    match c.Scrutinee with
                    | ReceiverPath(root, text) when
                        receiverSettled check source (unannotatedParameters (AstIndex.ofTree parseTree)) root
                        ->
                        text + (if c.Target.EndsWith ".isSome" then ".IsSome" else ".IsNone")
                    | _ -> c.Replacement
                else
                    c.Replacement

            { Range = c.MatchRange
              OriginalText = textOfRange source c.MatchRange
              ReplacementText = replacement
              Target = c.Target })

/// Find Option and ValueOption matches that can be rewritten.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    findWith optionConfig parseTree source check
    @ findWith valueOptionConfig parseTree source check
