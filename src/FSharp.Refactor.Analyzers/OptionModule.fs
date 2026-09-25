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
///   - no arm reads a byref, a byref-like value (Span) or the enclosing
///     struct's `this` (its fields, its primary-constructor values) from
///     outside it (typed): the arms become a lambda, which cannot capture
///     them (FS0406)
module FSharp.Refactor.OptionModule

open System.Collections.Generic
open System.Runtime.CompilerServices
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Diagnostics
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

/// FCS's `GetSymbolUseAtLocation`, remembered per check result. A lookup
/// costs a walk of FCS's name resolutions for the file - 0.3 ms at 4k lines,
/// 0.8 ms at 18k - and the rules resolve the same identifiers over and over:
/// the same `List.map` is asked by the hint engine, map fusion and the range
/// rule, each `+` by every rule that needs FSharp.Core's operator. The answer
/// is a function of the check result and the arguments alone, so the first
/// asker pays and the rest read it. Lives and dies with the check result.
let private symbolUses =
    ConditionalWeakTable<
        FSharpCheckFileResults,
        System.Collections.Concurrent.ConcurrentDictionary<struct (int * int * string * string), FSharpSymbolUse option>
     >()

let symbolUseAt
    (check: FSharpCheckFileResults)
    (line: int, column: int, lineText: string, names: string list)
    : FSharpSymbolUse option =
    let memo =
        symbolUses.GetValue(check, fun _ -> System.Collections.Concurrent.ConcurrentDictionary())

    // a newline is in no identifier, so the names join without ambiguity
    let key = struct (line, column, lineText, String.concat "\n" names)
    memo.GetOrAdd(key, fun _ -> check.GetSymbolUseAtLocation(line, column, lineText, names))

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
    {
        SomeName = "Some"
        NoneName = "None"
        ModuleName = "Option"
        // anchored with '<' so a hypothetical Option2 type cannot prefix-match
        CoreFullNamePrefix = "Microsoft.FSharp.Core.Option<"
    }

let valueOptionConfig =
    {
        SomeName = "ValueSome"
        NoneName = "ValueNone"
        ModuleName = "ValueOption"
        CoreFullNamePrefix = "Microsoft.FSharp.Core.ValueOption<"
    }

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
        /// The two arms' bodies: what moves into the rewrite's lambda.
        Arms: range list
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
/// declared outside it? A byref cannot be captured at all (FS0407). A
/// mutable local CAN be since F# 4.0 — the compiler turns it into a ref
/// cell silently — so the closure these rules manufacture would compile;
/// the rules still refuse it, since a `total <- total + v` written as a
/// plain assignment now allocates and dereferences a cell behind the
/// author's back, and the guard errs on the side of leaving the match.
/// Shared by the rules that wrap a branch body in `fun ... ->`
/// (Option/Result wrappers, OptionMatch, AddRange).
/// The file's `let mutable` names with the range of the `let` binding each,
/// and its byref-typed parameter names: what `capturesMutableLocal` asks of
/// every arm, collected once per index.
let private mutableFacts =
    ConditionalWeakTable<AstIndex.Index, (range * string)[] * string[]>()

let private mutableFactsOf (index: AstIndex.Index) =
    mutableFacts.GetValue(
        index,
        fun index ->
            let mutableLets =
                index.Exprs
                |> Array.collect (fun (_, e) ->
                    match e with
                    | LetOrUseE lou ->
                        lou.Bindings
                        |> List.choose (fun (SynBinding(isMutable = isMut; headPat = p)) ->
                            if isMut then
                                match p with
                                | SynPat.Named(ident = SynIdent(ident = id)) -> Some(lou.Range, id.idText)
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

            mutableLets, byrefNames
    )

let capturesMutableLocal (index: AstIndex.Index) (bodyRange: range) : bool =
    let mutableLets, byrefNames = mutableFactsOf index

    // a `let mutable` inside the body is the body's own
    let mutableNames =
        mutableLets
        |> Array.choose (fun (letRange, name) ->
            if Range.rangeContainsRange bodyRange letRange then
                None
            else
                Some name)

    let names = Set.ofArray (Array.append mutableNames byrefNames)

    not names.IsEmpty
    && (names
        |> Set.exists (fun name ->
            // a bare `name`, or the head of `name.Member`
            AstIndex.mentionsOf index name
            |> Array.exists (fun struct (mention, _) -> Range.rangeContainsRange bodyRange mention))
        // `name <- v` inside the body
        || AstIndex.exprsWithin index bodyRange
           |> Array.exists (fun (_, e) ->
               match e with
               | SynExpr.LongIdentSet(SynLongIdent(id = first :: _), _, _) -> names.Contains first.idText
               | _ -> false))

/// Does the arm body at `bodyRange` mention a function bound by a `let
/// rec` (or its `and`) that encloses it on `path`? In arm position that
/// call is a TAIL call the compiler turns into a jump; moved into the
/// lambda `Option.map`/`bind`/`iter` fabricate it runs inside a closure the
/// mapper invokes, and a loop that ran in constant stack grows it per
/// iteration:
///
///     let rec loop xs acc =
///         match List.tryHead xs with
///         | Some v -> loop (List.tail xs) (acc + v)     // tail call
///         | None -> acc
///
/// A mention counts whether applied or passed on — a value spelling of
/// the name goes somewhere this scan cannot follow.
///
/// A member is recursive without a `rec`: `member this.Walk xs acc` calling
/// `this.Walk (List.tail xs) (acc + v)` in an arm is the same tail call, so
/// an enclosing member's own name reached through its self identifier
/// (`this.Walk`, `self.Walk`) counts too, and so does the QUALIFIED
/// spelling — a static member calling itself as `Walker.Walk ...` through
/// the enclosing type's name, or a module's `let rec loop` called as
/// `M.loop` through the enclosing module's.
let private mentionsRecursiveBinder (index: AstIndex.Index) (path: SyntaxNode list) (bodyRange: range) =
    let recursiveNames =
        path
        |> List.collect (fun node ->
            let bindings =
                match node with
                | SyntaxNode.SynModule(SynModuleDecl.Let(isRecursive = true; bindings = bindings)) -> bindings
                | SyntaxNode.SynExpr(LetOrUseE lou) when lou.IsRecursive -> lou.Bindings
                | SyntaxNode.SynMemberDefn(SynMemberDefn.LetBindings(isRecursive = true; bindings = bindings)) ->
                    bindings
                | _ -> []

            bindings
            |> List.choose (fun (SynBinding(headPat = p)) ->
                match p with
                | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> Some id.idText
                | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                | _ -> None))
        |> Set.ofList

    // (self identifier, member name) of every member enclosing the body
    let selfMembers =
        path
        |> List.choose (fun node ->
            let binding =
                match node with
                | SyntaxNode.SynMemberDefn(SynMemberDefn.Member(memberDefn = b)) -> Some b
                | SyntaxNode.SynBinding b -> Some b
                | _ -> None

            match binding with
            | Some(SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ self; name ])))) ->
                Some(self.idText, name.idText)
            | _ -> None)
        |> Set.ofList

    let selfCall (s: Ident) (n: Ident) =
        selfMembers
        |> Set.exists (fun (self, name) ->
            n.idText = name && (s.idText = self || s.idText = "this" || s.idText = "self"))

    // the names of every member enclosing the body, static ones included
    // (`static member Walk` has no self identifier: its head is `[Walk]`)
    let memberNames =
        path
        |> List.choose (fun node ->
            match node with
            | SyntaxNode.SynMemberDefn(SynMemberDefn.Member(
                memberDefn = SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids))))) when
                not ids.IsEmpty
                ->
                Some (List.last ids).idText
            | _ -> None)
        |> Set.ofList

    // the names of the types and modules enclosing the body: `Walker` in
    // `Walker.Walk`, `M` in `M.loop`
    let enclosingNames =
        path
        |> List.choose (fun node ->
            match node with
            | SyntaxNode.SynTypeDefn(SynTypeDefn(typeInfo = SynComponentInfo(longId = ids)))
            | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = ids)))
            | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(longId = ids)) when not ids.IsEmpty ->
                Some (List.last ids).idText
            | _ -> None)
        |> Set.ofList

    // `Walker.Walk`, `M.loop`: the enclosing type or module qualifying an
    // enclosing member's or recursive binding's own name
    let qualifiedCall (t: Ident) (n: Ident) =
        enclosingNames.Contains t.idText
        && (memberNames.Contains n.idText || recursiveNames.Contains n.idText)

    (not (recursiveNames.IsEmpty && selfMembers.IsEmpty && memberNames.IsEmpty))
    // a name leaf inside the body is an expression inside it
    && AstIndex.exprsWithin index bodyRange
       |> Array.exists (fun (_, e) ->
           match e with
           | SynExpr.Ident id ->
               recursiveNames.Contains id.idText
               && Range.rangeContainsRange bodyRange id.idRange
           | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) ->
               recursiveNames.Contains id.idText
               && Range.rangeContainsRange bodyRange id.idRange
           | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ s; n ])) ->
               (selfCall s n || qualifiedCall s n)
               && Range.rangeContainsRange bodyRange n.idRange
           | SynExpr.DotGet(expr = SynExpr.Ident s; longDotId = SynLongIdent(id = [ n ])) ->
               (selfCall s n || qualifiedCall s n)
               && Range.rangeContainsRange bodyRange n.idRange
           | _ -> false)

let private wRegex = Regex @"^[\w.]+$"

let private findCandidates (cfg: WrapperConfig) (parseTree: ParsedInput) (source: ISourceText) : Candidate list =
    let candidates = ResizeArray<Candidate>()
    // one index per file, not one per candidate match
    let index = AstIndex.ofTree parseTree

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
                        && not (capturesMutableLocal index someBody.Range)
                        && not (capturesMutableLocal index noneBody.Range)
                        && not (mentionsRecursiveBinder index path someBody.Range)
                        && not (mentionsRecursiveBinder index path noneBody.Range)
                        && not (implicitYieldPosition path)
                        ->
                        match rewrite cfg source scrutinee boundVar someBody noneBody with
                        | Some(replacement, target) ->
                            let replacement =
                                if inOperandPosition && not (wRegex.IsMatch replacement) then
                                    $"({replacement})"
                                else
                                    replacement

                            candidates.Add
                                {
                                    MatchRange = m
                                    SomeIdent = someIdent
                                    NoneIdent = noneIdent
                                    Replacement = replacement
                                    Target = target
                                    Scrutinee = scrutinee
                                    Arms = [ someBody.Range; noneBody.Range ]
                                }
                        | None -> ()
                    | _ -> ()
                | _ -> ()
        }

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
    | :? KeyNotFoundException -> ValueSome()
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
    // "" is the contract, and a NULL FullName has to honour it too: callers
    // reach straight for .StartsWith and .Length, so handing one back turns
    // a missing name into a NullReferenceException inside the analyzer.
    if isNull (box symbol) then
        ""
    else
        try
            match symbol.FullName with
            | null -> ""
            | name -> name
        with FcsSymbolFailure ->
            ""

/// True when the ident at this location resolves to a union case whose
/// FullName starts with the given FSharp.Core prefix. Shared with other
/// analyzers that must prove an ident is really e.g. option's None.
let resolvesToCoreCase (check: FSharpCheckFileResults) (source: ISourceText) (prefix: string) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
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
        |> Option.filter (isNull >> not)
        |> Option.defaultValue ""
    with FcsSymbolFailure ->
        ""

/// Does this System.String entity offer `StartsWith(char)`? The char
/// overloads arrived with netstandard2.1 / .NET Core 2.0 and net4x and
/// netstandard2.0 never had them, so their presence is the proof that the
/// compilation targets a MODERN framework — the gate the string rules
/// (FR0106, FR0166, FR0167) share, without any TFM sniffing: a legacy
/// compilation simply never proves it, and a multi-targeted project's
/// legacy pass stays quiet on its own.
let stringIsModern (stringEntity: FSharpEntity) =
    try
        stringEntity.TryFullName = Some "System.String"
        && stringEntity.MembersFunctionsAndValues
           |> Seq.exists (fun m ->
               m.LogicalName = "StartsWith"
               && m.CurriedParameterGroups.Count = 1
               && m.CurriedParameterGroups.[0].Count = 1
               && (let t = stripAbbreviations m.CurriedParameterGroups.[0].[0].Type
                   t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Char"))
    with FcsSymbolFailure ->
        false

/// The System.String entity behind a type, or None for any other type.
let stringEntityOfType (t: FSharpType) =
    try
        let t = stripAbbreviations t

        if t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.String" then
            Some t.TypeDefinition
        else
            None
    with FcsSymbolFailure ->
        None

/// The System.String entity a value is typed as, or None for any other
/// type: the receiver of a slice or a comparison, proven a string.
let stringEntityOf (value: FSharpMemberOrFunctionOrValue) =
    try
        stringEntityOfType value.FullType
    with FcsSymbolFailure ->
        None

/// True when the identifier resolves into FSharp.Core's operator modules —
/// guards rules that pattern-match on names like `isNull`, `sprintf`, or
/// `(+)` against user-defined shadowing. `sprintf` and friends live in
/// ExtraTopLevelOperators rather than Operators.
let resolvesToCoreOperator (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
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

/// The symbol an identifier resolves to at its own position, or None.
let symbolOfIdent (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) : FSharpSymbol option =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ])
    |> Option.map (fun u -> u.Symbol)

/// Names of FSharp.Core whose CALL is an effect: `callsOnlyCore` waves
/// FSharp.Core's functions through as pure, and these are the ones it
/// must not — the printf family and the standard streams, the reference
/// cell and in-place array writers, `iter` and its twins (a lambda run
/// for its effect), `lock`, `exit`, the async and mailbox starters,
/// event triggers, a lazy force, and the raisers (a fused or short-
/// circuited raiser fires in a different order than the code it replaces).
/// A path is effectful when ANY of its identifiers is listed: `Async.Start`
/// through `Async`, `Array.set` through `set`, `evt.Trigger` through
/// `Trigger`.
let effectfulCoreNames =
    set
        [
            "printf"
            "printfn"
            "eprintf"
            "eprintfn"
            "fprintf"
            "fprintfn"
            "kprintf"
            "kfprintf"
            "bprintf"
            "stdout"
            "stderr"
            "stdin"
            "incr"
            "decr"
            "lock"
            "exit"
            "iter"
            "iteri"
            "iter2"
            "iteri2"
            "Async"
            "Event"
            "Observable"
            "Task"
            "Console"
            "MailboxProcessor"
            "Start"
            "StartImmediate"
            "StartAsTask"
            "StartChild"
            "RunSynchronously"
            "Post"
            "PostAndReply"
            "PostAndAsyncReply"
            "PostAndTryAsyncReply"
            "Receive"
            "TryReceive"
            "Trigger"
            "raise"
            "reraise"
            "failwith"
            "failwithf"
            "invalidArg"
            "invalidOp"
            "nullArg"
            // a reference cell write and a lazy force are effects too
            "op_ColonEquals"
            "force"
            "Force"
            // the in-place operations of the Array module: `Array.set`,
            // `Array.fill` and the sorts write through the array they are handed
            "set"
            "fill"
            "blit"
            "sortInPlace"
            "sortInPlaceBy"
            "sortInPlaceWith"
        ]

/// The PARTIAL functions of FSharp.Core's collection and option modules:
/// total in their spelling, a throw on some input (an empty list, a short
/// list, a missing key, `None`). `callsOnlyCore` waves FSharp.Core through
/// as pure, and a throw is the one effect a pure-looking function has: a
/// fused or short-circuited caller fires it in a different order, or not
/// at all, where the code it replaces threw. Checked against the LAST
/// identifier of a path (`List.head`, `Map.find`, `Option.get`), and not
/// against `Operators.min`/`max`, which are total.
let partialCoreNames =
    set
        [
            "head"
            "tail"
            "last"
            "item"
            "nth"
            "exactlyOne"
            "reduce"
            "reduceBack"
            "find"
            "findBack"
            "findIndex"
            "findIndexBack"
            "pick"
            "get"
            "min"
            "max"
            "minBy"
            "maxBy"
            "minElement"
            "maxElement"
            "average"
            "averageBy"
            "skip"
            "take"
            "splitAt"
            "windowed"
            "chunkBySize"
            "splitInto"
            "zip"
            "zip3"
            "map2"
            "map3"
            "mapi2"
            "iter2"
            "iteri2"
            "fold2"
            "foldBack2"
            "forall2"
            "exists2"
            "sub"
            "removeAt"
            "removeManyAt"
            "insertAt"
            "insertManyAt"
            "updateAt"
            "permute"
            "transpose"
        ]

/// The `let` binding this file declares `value` with — module-level, a
/// class's `let`, or a local `let` / `let rec` inside an expression — as
/// its head identifier and its body, found by the symbol's
/// DeclarationLocation. The head may carry a type annotation (`let
/// isValid: string -> bool = fun ...`). None for a member, a parameter, a
/// pattern-bound name, a declaration in another file, or a `let mutable`:
/// a mutable holding a function (`let mutable validator = fun ...`) may
/// be reassigned, so its initial body says nothing about what a later
/// call runs.
/// Every immutable binding head of the file that `bindingDeclaredAt` can
/// answer with - module and class `let`s first, then expression `let`s, the
/// order it searches in - by the head's start line and column. Built once per
/// index; a lookup is the few heads at one position.
let private bindingHeads =
    ConditionalWeakTable<AstIndex.Index, Dictionary<struct (int * int), (Ident * SynExpr)[]>>()

let private bindingHeadsOf (index: AstIndex.Index) =
    bindingHeads.GetValue(
        index,
        fun index ->
            let headOf (SynBinding(isMutable = isMut; headPat = p; expr = body)) =
                if isMut then
                    None
                else
                    match p with
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]))
                    | SynPat.Named(ident = SynIdent(ident = id))
                    | SynPat.Typed(pat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])))
                    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))) -> Some(id, body)
                    | _ -> None

            let rec ofMembers (members: SynMemberDefns) =
                members
                |> List.collect (fun m ->
                    match m with
                    | SynMemberDefn.LetBindings(bindings = bs) -> bs
                    | SynMemberDefn.Interface(members = Some ms) -> ofMembers ms
                    | _ -> [])

            let fromDecls =
                index.Decls
                |> Seq.collect (fun (_, d) ->
                    match d with
                    | SynModuleDecl.Let(bindings = bs) -> Seq.ofList bs
                    | SynModuleDecl.Types(typeDefns = defns) ->
                        defns
                        |> Seq.collect (fun (SynTypeDefn(typeRepr = repr; members = extra)) ->
                            match repr with
                            | SynTypeDefnRepr.ObjectModel(members = ms) -> ofMembers ms @ ofMembers extra
                            | _ -> ofMembers extra)
                    | _ -> Seq.empty)

            let fromExprs =
                index.Exprs
                |> Seq.collect (fun (_, e) ->
                    match e with
                    | LetOrUseE lou -> Seq.ofList lou.Bindings
                    | _ -> Seq.empty)

            let byPosition = Dictionary<struct (int * int), ResizeArray<Ident * SynExpr>>()

            for (id: Ident, body) in Seq.append fromDecls fromExprs |> Seq.choose headOf do
                let key = struct (id.idRange.StartLine, id.idRange.StartColumn)

                match byPosition.TryGetValue key with
                | true, l -> l.Add(id, body)
                | false, _ -> byPosition.[key] <- ResizeArray [ id, body ]

            let result = Dictionary<struct (int * int), (Ident * SynExpr)[]>()

            for KeyValue(key, l) in byPosition do
                result.[key] <- l.ToArray()

            result
    )

let bindingDeclaredAt (index: AstIndex.Index) (value: FSharpMemberOrFunctionOrValue) : (Ident * SynExpr) option =
    // FCS raises a plain Exception ("DeclarationLocation property not
    // available") for a method of another assembly
    let location =
        try
            Some value.DeclarationLocation
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            None

    match location with
    | None -> None
    | Some loc ->
        let sitsAt (id: Ident, _) =
            let r = id.idRange

            r.StartLine = loc.StartLine
            && r.StartColumn = loc.StartColumn
            && System.String.Equals(r.FileName, loc.FileName, System.StringComparison.OrdinalIgnoreCase)

        match (bindingHeadsOf index).TryGetValue(struct (loc.StartLine, loc.StartColumn)) with
        | true, heads -> heads |> Array.tryFind sitsAt
        | false, _ -> None

/// Does the code in this range CALL only what provably does nothing but
/// compute? Every identifier in the range that names a FUNCTION (typed)
/// must belong to FSharp.Core (and not be one of `effectfulCoreNames`) or
/// to System.String (immutable receiver, pure members), or satisfy the
/// caller's `userFunction` test — FR0107 accepts a function this file
/// declares whose own body passes; a user method, a constructor, any
/// other .NET method fails. Plain values, property reads, union cases and
/// fields of non-function type are not calls and pass; a field or
/// record slot holding a FUNCTION is a call (`r.Validate f`), and so is
/// an active pattern. An extension member fails whatever type it
/// extends: `type System.String with member s.Shout() = ...` has
/// System.String for its apparent owner and a user body. A partial core
/// function (`List.head`, `Option.get`: `partialCoreNames`) fails too,
/// since its throw is an effect the caller would reorder. Naming a
/// function without applying it counts too: `List.exists validate xs`
/// hands the effect to a core function. An identifier that does not
/// resolve fails: the caller is about to move or drop a call and cannot
/// afford to guess. FR0107 asks it of a flag loop's predicate before
/// `exists` runs it fewer times; FR0012 asks it of two mappers before
/// `g >> f` interleaves their calls.
let callsOnlyCoreWith
    (userFunction: FSharpMemberOrFunctionOrValue -> bool)
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (index: AstIndex.Index)
    (r: range)
    =
    let pureIdent (ids: Ident list) =
        match symbolOfIdent check source (List.last ids) with
        | Some(:? FSharpMemberOrFunctionOrValue as value) ->
            (try
                let fullName = fullNameOf value
                let enclosing = enclosingFullName value

                if value.IsExtensionMember then
                    // the owner is the extended type, the body a user's
                    false
                elif fullName.StartsWith "Microsoft.FSharp." then
                    not (ids |> List.exists (fun id -> effectfulCoreNames.Contains id.idText))
                    // `List.min` throws on an empty list where `Operators.min`
                    // over two values cannot
                    && not (
                        partialCoreNames.Contains (List.last ids).idText
                        && not (fullName.StartsWith "Microsoft.FSharp.Core.Operators.")
                    )
                elif enclosing = "System.Lazy`1" then
                    // `.Value` and `.Force()` run the thunk
                    false
                elif not value.FullType.IsFunctionType then
                    true
                elif enclosing = "System.String" then
                    true
                elif value.IsMember || value.IsConstructor then
                    false
                else
                    userFunction value
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | Some(:? FSharpUnionCase) -> true
        | Some(:? FSharpField as field) ->
            (try
                not (stripAbbreviations field.FieldType).IsFunctionType
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        // an active pattern case is a call; anything else unresolved or
        // unknown fails
        | _ -> false

    AstIndex.exprsWithin index r
    |> Array.forall (fun (_, e) ->
        match e with
        | SynExpr.Ident id -> pureIdent [ id ]
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> pureIdent ids
        // a constructor or an object expression runs arbitrary code
        | SynExpr.New _
        | SynExpr.ObjExpr _ -> false
        | _ -> true)

/// `callsOnlyCoreWith` where every user function fails: FSharp.Core and
/// System.String only.
let callsOnlyCore (check: FSharpCheckFileResults) (source: ISourceText) (index: AstIndex.Index) (r: range) =
    callsOnlyCoreWith (fun _ -> false) check source index r

/// True when the file's typed results contain any error diagnostics.
let hasErrors (check: FSharpCheckFileResults) =
    check.Diagnostics
    |> Array.exists (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)

/// Find all wrapper matches for one config (Option or ValueOption) that can
/// be rewritten with module functions. Requires typed check results; emits
/// nothing when the file has type errors.
/// A receiver `.IsSome` can hang off: a name or a dotted path, as its
/// identifiers (the root's declaration decides whether the type is
/// settled; every further member must carry a declared type too).
[<return: Struct>]
let (|ReceiverPath|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident root -> ValueSome([ root ], root.idText)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = (_ :: _ as ids))) -> ValueSome(ids, identText ids)
    | _ -> ValueNone

/// What the parse tree says about where a file's names are declared: the
/// POSITIVE evidence `receiverSettled` needs before it calls a receiver's
/// type known at its use. Everything not listed — a `for` variable, a
/// match-bound name, a destructured tuple, a primary-constructor or lambda
/// parameter, an unannotated parameter — has a type inferred from uses
/// that may come later, where `x.IsSome` is FS0072 "lookup on object of
/// indeterminate type" while `Option.isSome x` infers fine.
type DeclarationEvidence =
    {
        /// Names declared under an explicit, non-variable type annotation:
        /// `(x: int option)`, `let (x: T) = …`, `| (o: T) :: _ ->`.
        Annotated: Set<int * int>
        /// Plain value bindings (`let x = …`, at any level) by the name's
        /// position: settled when their right-hand side is.
        ValueBindings: Map<int * int, SynBinding>
        /// The self identifier of a member (`member this.M`): the type
        /// being defined.
        SelfIdents: Set<int * int>
        /// Top-level declarations (nested modules flattened): a name
        /// declared in one is fully inferred once the checker has left it.
        TopLevel: range list
        /// `module rec` / `namespace rec` bodies, where declaration order
        /// settles nothing.
        RecursiveModules: range list
    }

/// A written type that pins something: `'a` and `_` do not.
let private concreteType (t: SynType) =
    match t with
    | SynType.Var _
    | SynType.Anon _ -> false
    | _ -> true

let private posOf (id: Ident) =
    id.idRange.StartLine, id.idRange.StartColumn

let declarationEvidence (parseTree: ParsedInput) : DeclarationEvidence =
    let index = AstIndex.ofTree parseTree
    let annotated = HashSet<int * int>()
    let values = Dictionary<int * int, SynBinding>()
    let selfIdents = HashSet<int * int>()
    let topLevel = ResizeArray<range>()
    let recursiveModules = ResizeArray<range>()

    // the names directly under an annotation: `(x: T)`, `([<A>] x: T)`
    let rec namedUnder (p: SynPat) =
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> annotated.Add(posOf id) |> ignore
        | SynPat.Paren(pat = inner)
        | SynPat.Attrib(pat = inner) -> namedUnder inner
        | _ -> ()

    let rec walkPat (p: SynPat) =
        match p with
        | SynPat.Typed(pat = inner; targetType = t) ->
            if concreteType t then
                namedUnder inner

            walkPat inner
        | SynPat.Paren(pat = inner)
        | SynPat.Attrib(pat = inner) -> walkPat inner
        | SynPat.As(lhsPat = l; rhsPat = r)
        | SynPat.Or(lhsPat = l; rhsPat = r)
        | SynPat.ListCons(lhsPat = l; rhsPat = r) ->
            walkPat l
            walkPat r
        | SynPat.Tuple(elementPats = ps)
        | SynPat.Ands(pats = ps)
        | SynPat.ArrayOrList(elementPats = ps) -> List.iter walkPat ps
        | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> List.iter walkPat ps
        | _ -> ()

    let ofBinding (SynBinding(headPat = headPat) as b) =
        match headPat with
        | SynPat.Named(ident = SynIdent(ident = id)) -> values.[posOf id] <- b
        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ self; _ ])) -> selfIdents.Add(posOf self) |> ignore
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

    let rec ofDecls (decls: SynModuleDecl list) =
        for decl in decls do
            match decl with
            | SynModuleDecl.NestedModule(isRecursive = isRecursive; decls = nested; range = r) ->
                if isRecursive then
                    recursiveModules.Add r

                ofDecls nested
            | _ ->
                topLevel.Add decl.Range

                match decl with
                | SynModuleDecl.Let(bindings = bs) -> List.iter ofBinding bs
                | SynModuleDecl.Types(typeDefns = defns) ->
                    for SynTypeDefn(typeRepr = repr; members = extra) in defns do
                        match repr with
                        | SynTypeDefnRepr.ObjectModel(members = ms) -> ofMembers ms
                        | _ -> ()

                        ofMembers extra
                | _ -> ()

    match parseTree with
    | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
        for SynModuleOrNamespace(isRecursive = isRecursive; decls = decls; range = r) in modules do
            if isRecursive then
                recursiveModules.Add r

            ofDecls decls
    | _ -> ()

    for _, p in index.Pats do
        walkPat p

    for _, e in index.Exprs do
        match e with
        | LetOrUseE lou -> List.iter ofBinding lou.Bindings
        // the walker does not visit a lambda's parsed patterns
        | SynExpr.Lambda(parsedData = Some(pats, _)) -> List.iter walkPat pats
        | SynExpr.ObjExpr(bindings = bs; members = ms) ->
            List.iter ofBinding bs
            ofMembers ms
        | _ -> ()

    {
        Annotated = Set.ofSeq annotated
        ValueBindings = values |> Seq.map (fun kv -> kv.Key, kv.Value) |> Map.ofSeq
        SelfIdents = Set.ofSeq selfIdents
        TopLevel = List.ofSeq topLevel
        RecursiveModules = List.ofSeq recursiveModules
    }

/// The symbol an identifier resolves to, given the dotted path leading up
/// to and including it.
let private symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (qualified: Ident list) =
    match List.tryLast qualified with
    | Some last ->
        let r = last.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        symbolUseAt check (r.EndLine, r.EndColumn, lineText, qualified |> List.map (fun i -> i.idText))
        |> Option.map (fun u -> u.Symbol)
    | None -> None

/// Is the receiver's type settled where it is read — determined BEFORE the
/// checker reaches the lookup, so `.IsSome` resolves? Only positive
/// evidence counts: the root is declared under a type annotation, is a
/// member's self identifier, is a top-level (module- or class-level) name
/// read from a later declaration, or is a `let` value whose right-hand
/// side is itself settled (a union case, a call whose declared return type
/// is not a bare type parameter, a branch of an `if`/`match` that is);
/// every further member of a dotted path must carry a declared type of its
/// own. Anything else keeps the module form.
let receiverSettled
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (evidence: DeclarationEvidence)
    (ids: Ident list)
    : bool =
    let file =
        match ids with
        | id :: _ -> id.idRange.FileName
        | [] -> ""

    let inRecursiveModule (d: range) =
        evidence.RecursiveModules |> List.exists (fun m -> Range.rangeContainsRange m d)

    // the reading position lies outside the top-level declaration that
    // declares the symbol: inference of that declaration has finished
    let leftBehind (useAt: pos) (d: range) =
        match evidence.TopLevel |> List.tryFind (fun t -> Range.rangeContainsRange t d) with
        | Some t -> not (Range.rangeContainsPos t useAt)
        | None -> false

    let nominal (t: FSharpType) =
        try
            not t.IsGenericParameter
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    let rec symbolSettled (depth: int) (useAt: pos) (symbol: FSharpSymbol) : bool =
        match symbol with
        // a module or type qualifier along the path
        | :? FSharpEntity -> true
        // `Some x`, `None`: the case's own type
        | :? FSharpUnionCase -> true
        | :? FSharpField as f -> nominal f.FieldType
        | :? FSharpMemberOrFunctionOrValue as v ->
            (try
                let d = v.DeclarationLocation

                if d.FileName <> file then
                    nominal v.ReturnParameter.Type
                elif not (inRecursiveModule d) && leftBehind useAt d then
                    nominal v.ReturnParameter.Type
                else
                    let p = d.StartLine, d.StartColumn

                    evidence.Annotated.Contains p
                    || evidence.SelfIdents.Contains p
                    || (match evidence.ValueBindings.TryFind p with
                        | Some(SynBinding(returnInfo = Some(SynBindingReturnInfo(typeName = t)))) when concreteType t ->
                            true
                        | Some(SynBinding(expr = rhs)) -> depth < 6 && rhsSettled (depth + 1) rhs
                        | None -> false)
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false

    // every identifier along a dotted path, each resolved with its prefix
    and pathSettled (depth: int) (path: Ident list) =
        let rec go prefix rest =
            match rest with
            | [] -> true
            | (id: Ident) :: tail ->
                let qualified = prefix @ [ id ]

                (match symbolAt check source qualified with
                 | Some s -> symbolSettled depth id.idRange.Start s
                 | None -> false)
                && go qualified tail

        go [] path

    and rhsSettled (depth: int) (e: SynExpr) : bool =
        match e with
        | SynExpr.Typed(targetType = t) -> concreteType t
        | SynExpr.Paren(expr = inner)
        | SynExpr.TypeApp(expr = inner) -> rhsSettled depth inner
        | SynExpr.Const _ -> true
        | SynExpr.Ident id -> pathSettled depth [ id ]
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = path)) -> pathSettled depth path
        | SynExpr.DotGet(expr = target; longDotId = SynLongIdent(id = path)) ->
            rhsSettled depth target && pathSettled depth path
        | PipeApp(_, fn) -> rhsSettled depth fn
        // an application is typed by its head's declared return type
        | SynExpr.App(funcExpr = fn) -> rhsSettled depth fn
        // branches unify: one settled branch pins them all
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some el) -> rhsSettled depth t || rhsSettled depth el
        | SynExpr.Match(clauses = clauses) ->
            clauses
            |> List.exists (fun (SynMatchClause(resultExpr = result)) -> rhsSettled depth result)
        | LetOrUseE lou -> rhsSettled depth lou.Body
        | SynExpr.Sequential(expr2 = e2) -> rhsSettled depth e2
        | SynExpr.TryWith(tryExpr = t) -> rhsSettled depth t
        | _ -> false

    not ids.IsEmpty && pathSettled 0 ids

/// A byref, or a byref-like struct (`Span<'T>`, `ReadOnlySpan<'T>`, a
/// `[<IsByRefLike>]` of the project's own): a value no closure may capture
/// and no computation expression may hold across its binds.
let isByRefLike (t: FSharpType) =
    try
        let t = stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.IsByRef
            || t.TypeDefinition.Attributes
               |> Seq.exists (fun a -> a.AttributeType.DisplayName = "IsByRefLikeAttribute"))
    with FcsSymbolFailure ->
        true

/// Does the stretch `bodyRange` read a byref or byref-like value declared
/// OUTSIDE it? A rewrite that moves that stretch into a lambda, a local
/// function or a task { } block would capture the value, which the
/// compiler refuses (FS0406 / FS0412); one declared inside moves with the
/// stretch and is fine. `capturesMutableLocal` reads the syntax and sees
/// only a `byref`-annotated parameter; this asks the typed tree about every
/// name the stretch reads, since a `let s = span.Slice(...)` carries no
/// annotation at all. A name FCS cannot type reads as captured: the
/// rewrite stands down rather than guess.
/// Every use in the file of a byref or byref-like value, with where that
/// value was declared — collected ONCE per typed file, because the rules
/// that ask (FR0142 for every test body, FR0049, FR0029, FR0018, FR0010,
/// FR0034) asked per identifier of every candidate stretch, and on
/// FunStripe's 1800-line test file that was thousands of symbol lookups:
/// testReturnsTask went from 3 s to 13 s on the file. A name FCS cannot
/// type is recorded at the use with no declaration, which every caller
/// reads as byref-like: the rewrite stands down rather than guess.
///
/// A struct's `this` is a byref (`byref<S>` in FCS's view of the self
/// identifier), so `this.Field` is caught as it is. A primary-constructor
/// value of a struct is not: `type S(x: int)` reads `x` as a plain int,
/// yet it is a field of `this`, and a closure over it captures `this`
/// (FS0406). Those uses are recorded with no declaration, captured
/// wherever they sit — typed proof: the parameters of a constructor whose
/// declaring entity is a value type.
let private byRefLikeUsesCache =
    ConditionalWeakTable<FSharpCheckFileResults, (range * range option)[]>()

/// Where the parameters of the file's struct constructors are declared.
let private structConstructorParameters (uses: FSharpSymbolUse[]) =
    let declared = HashSet<range>()

    for u in uses do
        match u.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v when u.IsFromDefinition ->
            try
                if v.IsConstructor then
                    match v.DeclaringEntity with
                    | Some entity when entity.IsValueType ->
                        for group in v.CurriedParameterGroups do
                            for p in group do
                                declared.Add p.DeclarationLocation |> ignore
                    | _ -> ()
            with _ -> // a constructor FCS cannot describe adds nothing; fsharpanalyzer: ignore-line FR0055
                ()
        | _ -> ()

    declared

let private byRefLikeUses (check: FSharpCheckFileResults) =
    byRefLikeUsesCache.GetValue(
        check,
        fun c ->
            try
                let uses = c.GetAllUsesOfAllSymbolsInFile() |> Array.ofSeq
                let structParameters = structConstructorParameters uses

                uses
                |> Seq.choose (fun u ->
                    match u.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as v ->
                        // a failure here must stay with THIS use: escaping to the
                        // handler below would empty the whole file's list, and the
                        // guard would let every Span of the file through. The
                        // `Item` indexer of a ReadOnlySpan (an inref property) has
                        // no DeclarationLocation and raises a plain exception for
                        // it, so a byref-like use whose declaration cannot be
                        // placed is recorded with none, which callers read as
                        // declared outside
                        try
                            if isByRefLike v.FullType then
                                let declared =
                                    try
                                        Some v.DeclarationLocation
                                    with _ -> // fsharpanalyzer: ignore-line FR0055
                                        None

                                Some(u.Range, declared)
                            elif
                                structParameters.Count > 0
                                && not v.IsModuleValueOrMember
                                && (try
                                        structParameters.Contains v.DeclarationLocation
                                    with _ -> // no declaration: not a constructor parameter of this file; fsharpanalyzer: ignore-line FR0055
                                        false)
                            then
                                // a field of the struct's `this`: captured
                                // wherever the stretch starts
                                Some(u.Range, None)
                            else
                                None
                        with _ -> // fsharpanalyzer: ignore-line FR0055
                            Some(u.Range, None)
                    | _ -> None)
                |> Array.ofSeq
            with _ -> // a file whose symbols cannot be enumerated: nothing is known to be byref-like, and every rule keeps its syntactic guards; fsharpanalyzer: ignore-line FR0055
                [||]
    )

let private readsByRefLikeWhere
    (declaredOutsideOnly: bool)
    (check: FSharpCheckFileResults)
    (_index: AstIndex.Index)
    (_source: ISourceText)
    (bodyRange: range)
    : bool =
    byRefLikeUses check
    |> Array.exists (fun (useRange, declaration) ->
        Range.rangeContainsRange bodyRange useRange
        && (match declaration with
            | None -> true
            | Some declared -> not (declaredOutsideOnly && Range.rangeContainsRange bodyRange declared)))

let capturesByRefLike (check: FSharpCheckFileResults) (index: AstIndex.Index) (source: ISourceText) (bodyRange: range) =
    readsByRefLikeWhere true check index source bodyRange

/// Does the stretch read ANY byref or byref-like value, its own included?
/// A stretch that becomes a `task { }` or `async { }` body keeps its
/// locals as state-machine fields, and a Span cannot be one of those
/// wherever it was declared.
let readsByRefLike (check: FSharpCheckFileResults) (index: AstIndex.Index) (source: ISourceText) (bodyRange: range) =
    readsByRefLikeWhere false check index source bodyRange

let findWith (cfg: WrapperConfig) (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) =
    if hasErrors check then
        []
    else
        let evidence = lazy (declarationEvidence parseTree)

        let index = AstIndex.ofTree parseTree

        findCandidates cfg parseTree source
        |> List.filter (fun c ->
            not (spansDirective source c.MatchRange)
            // the arms move into a lambda, which cannot capture a Span, a
            // byref, or the enclosing struct's `this` (FS0406)
            && not (c.Arms |> List.exists (capturesByRefLike check index source))
            && resolvesToCoreCase check source cfg.CoreFullNamePrefix c.SomeIdent
            && resolvesToCoreCase check source cfg.CoreFullNamePrefix c.NoneIdent)
        |> List.map (fun c ->
            // an isSome/isNone test reads as the property where the
            // receiver's type is settled — the spelling FR0010 produces,
            // so the two rules agree on what a test looks like
            let replacement =
                if c.Target.EndsWith ".isSome" || c.Target.EndsWith ".isNone" then
                    match c.Scrutinee with
                    | ReceiverPath(ids, text) when receiverSettled check source evidence.Value ids ->
                        text + (if c.Target.EndsWith ".isSome" then ".IsSome" else ".IsNone")
                    | _ -> c.Replacement
                else
                    c.Replacement

            {
                Range = c.MatchRange
                OriginalText = textOfRange source c.MatchRange
                ReplacementText = replacement
                Target = c.Target
            })

/// Find Option and ValueOption matches that can be rewritten.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    findWith optionConfig parseTree source check
    @ findWith valueOptionConfig parseTree source check
