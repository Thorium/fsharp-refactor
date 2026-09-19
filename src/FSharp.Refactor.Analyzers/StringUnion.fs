/// FR0157 (idiom): a closed set of string literals matched by name is a
/// union.
///
///     let describe (region: string) =         [<RequireQualifiedAccess>]
///         match region with                   type Region =
///         | "eu" -> "European Union"              | Eu
///         | "uk" -> "United Kingdom"              | Uk
///         | _ -> failwith "unsupported"
///                                                 override this.ToString() =
///     describe "eu"                                   match this with
///     describe "uk"                                   | Region.Eu -> "eu"
///                                                     | Region.Uk -> "uk"
///
///                                             let describe (region: Region) =
///                                                 match region with
///                                                 | Region.Eu -> "European Union"
///                                                 | Region.Uk -> "United Kingdom"
///
///                                             describe Region.Eu
///                                             describe Region.Uk
///
/// The proof is a flow analysis over the string SLOTS the matched value
/// passes through — a parameter, a `let`, a record field, a function's
/// return, a name a pattern binds, each plainly `string` or wrapped in an
/// option — connected by the values flowing between them. The set is
/// closed when every source of every slot in the component is a literal
/// (or a constant bound to one, `[<Literal>]` or not) or another slot of
/// the component, and every sink is a match on literals, a comparison
/// with one, a flow into another slot, or a print that goes through
/// `ToString`. Proven at either end — every call site passing a literal,
/// or a producing function whose every exit is one — the value can only
/// ever be one of the literals seen, and the union names each.
/// `ToString` returns the original text, so a log line or an
/// interpolated string reads exactly as before.
///
/// A match's catch-all is dropped when the proof enumerated every one of
/// its arms and nothing else (the compiler would call it a rule that never
/// matches); it stays when the proof found a literal no arm names, whose
/// case it now covers. A variable pattern that spells the name of a
/// module-level string constant — `| us -> 2` beside `let us = "..."`,
/// which binds a fresh `us` and matches every value — is treated as the
/// comparison the author meant, and the message says so.
///
/// What stands the rule down: a slot fed from anything but a literal or a
/// slot (a parameter with a call site the host cannot see, a value read
/// from input, a function used as a value or partially applied, a lambda
/// parameter, a member or property, a tuple-bound name), a use the union
/// cannot serve (a `%s` format hole, string concatenation, a method call
/// on the string, a comparison with a non-literal), fewer than two
/// distinct literals matched, a literal that makes no identifier, a
/// wildcard the proof leaves dead but cannot delete whole, a name the
/// project already uses for a type, a signature file beside any file
/// touched, a record a serializer fills, and a set no producer feeds.
///
/// A `Result<_, string>` is a slot like the others, its `Error "..."` exits
/// the sources and its `Error "..."` arms the consumer; the Ok side is not
/// followed. A slot the assembly exports (public, or internal beside
/// InternalsVisibleTo) is proven only where the host reads every caller:
/// a leaf compilation, or the apply tool's api pass with the sibling
/// projects in its world. Where it cannot, the exported function keeps its
/// public shape behind an adapter - a private twin typed with the union,
/// the compilation's own callers moved to it, and a wrapper of the old name
/// mapping at the edge (`OfString`, whose unknown arm is the match's own
/// raising catch-all; `Result.mapError string`) under a TODO.
module FSharp.Refactor.StringUnion

open System
open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Refactor.Text

type Edit =
    {
        Range: range
        Original: string
        Replacement: string
    }

type Suggestion =
    {
        /// The union's name.
        Name: string
        /// The match that triggered the analysis.
        Range: range
        /// The literals, in case order.
        Literals: string list
        /// A slot the assembly exports is among them: the change reshapes
        /// the public surface.
        Exported: bool
        /// The `| name ->` arms that were binding a variable, now the
        /// constant comparison they read as.
        ShadowedConstants: string list
        /// The functions whose signature changes - a parameter or a return
        /// retyped - by display name, for the host's template guard.
        Reshaped: string list
        Edits: Edit list
    }

/// What the host can see of the compilation.
type World =
    {
        /// Every use of a symbol the host can reach, definition included.
        UsesOf: FSharpSymbol -> FSharpSymbolUse[]
        /// A file's parse tree and source, by full path; None where the
        /// host cannot read it.
        File: string -> (ParsedInput * ISourceText) option
        /// The symbol an identifier resolves to, in any file the host can
        /// read.
        SymbolAt: string -> Ident -> FSharpSymbolUse option
        /// A file's position in the compilation order.
        FileOrder: string -> int
        /// Is the compilation's public surface the caller's to reshape?
        ScopeOpen: bool
        /// The type names the compilation declares, for the name check.
        TypeNames: Set<string>
        /// Does the assembly name InternalsVisibleTo friends (or can the host
        /// not tell)? Its internal declarations then count as exported.
        InternalsVisible: bool
        /// The compilation's source files, in order: a record field's type is
        /// looked for as a type argument in every one of them before its
        /// field is retyped, since a serializer or a reflection reads fields
        /// no construction shows.
        SourceFiles: string list
    }

// ---- the hosts' use index -------------------------------------------------

/// A compilation's symbol uses, indexed by the declaration they refer to
/// and by the position they sit at: the two questions the analysis asks,
/// each a dozen times per candidate, answered without a walk of every
/// typed tree per question.
type UseIndex =
    {
        ByDeclaration: Dictionary<string, FSharpSymbolUse[]>
        ByPosition: Dictionary<string, FSharpSymbolUse>
        /// By the file, line and column a use ENDS at: a record field read
        /// `entry.Source` is reported over the whole path, and the question
        /// comes with the field's own identifier.
        ByEnd: Dictionary<string, FSharpSymbolUse list>
    }

let private declarationKey (symbol: FSharpSymbol) =
    try
        match symbol.DeclarationLocation with
        | Some r -> Some $"{r.FileName}|{r.StartLine}|{r.StartColumn}"
        | None -> None
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

let private fullPath (file: string) =
    try
        IO.Path.GetFullPath file
    with _ -> // fsharpanalyzer: ignore-line FR0055
        file

let private positionKey (file: string) (r: range) =
    $"{fullPath file}|{r.StartLine}|{r.StartColumn}|{r.EndColumn}"

let private endKey (file: string) (r: range) =
    $"{fullPath file}|{r.EndLine}|{r.EndColumn}"

let indexUses (all: FSharpSymbolUse seq) : UseIndex =
    let byKey = Dictionary<string, ResizeArray<FSharpSymbolUse>>()

    let byPosition =
        Dictionary<string, FSharpSymbolUse>(StringComparer.OrdinalIgnoreCase)

    let byEnd =
        Dictionary<string, FSharpSymbolUse list>(StringComparer.OrdinalIgnoreCase)

    for u in all do
        match declarationKey u.Symbol with
        | Some key ->
            match byKey.TryGetValue key with
            | true, list -> list.Add u
            | false, _ -> byKey.[key] <- ResizeArray [ u ]
        | None -> ()

        byPosition.[positionKey u.Range.FileName u.Range] <- u

        let atEnd = endKey u.Range.FileName u.Range

        match byEnd.TryGetValue atEnd with
        | true, list -> byEnd.[atEnd] <- u :: list
        | false, _ -> byEnd.[atEnd] <- [ u ]

    let byDeclaration = Dictionary<string, FSharpSymbolUse[]>()

    for kv in byKey do
        byDeclaration.[kv.Key] <- kv.Value.ToArray()

    {
        ByDeclaration = byDeclaration
        ByPosition = byPosition
        ByEnd = byEnd
    }

/// Every use of a symbol across the indexes, definition included.
let usesIn (indexes: UseIndex list) (symbol: FSharpSymbol) : FSharpSymbolUse[] =
    match declarationKey symbol with
    | Some key ->
        indexes
        |> List.collect (fun i ->
            match i.ByDeclaration.TryGetValue key with
            | true, uses -> List.ofArray uses
            | false, _ -> [])
        |> Array.ofList
    | None -> [||]

/// The symbol use at an identifier, in whichever index holds its file.
let symbolIn (indexes: UseIndex list) (file: string) (id: Ident) : FSharpSymbolUse option =
    let key = positionKey file id.idRange

    indexes
    |> List.tryPick (fun i ->
        match i.ByPosition.TryGetValue key with
        | true, u -> Some u
        | false, _ ->
            // a use reported over a path the identifier ends: the one whose
            // span holds the identifier
            match i.ByEnd.TryGetValue(endKey file id.idRange) with
            | true, uses -> uses |> List.tryFind (fun u -> Range.rangeContainsRange u.Range id.idRange)
            | false, _ -> None)

// ---- slots ----------------------------------------------------------------

/// How a slot holds its string.
type private Wrap =
    | Plain
    | Wrapped
    | WrappedResult

type private Slot =
    {
        Symbol: FSharpSymbol
        Wrap: Wrap
        /// "value" (a let, a parameter, a pattern-bound name), "field",
        /// "return".
        Kind: string
    }

let private sameSymbol (a: FSharpSymbol) (b: FSharpSymbol) =
    try
        a.IsEffectivelySameAs b
    with _ -> // fsharpanalyzer: ignore-line FR0055
        false

let private optionNames =
    set
        [
            "Microsoft.FSharp.Core.FSharpOption"
            "Microsoft.FSharp.Core.Option"
            "Microsoft.FSharp.Core.FSharpValueOption"
            "Microsoft.FSharp.Core.ValueOption"
        ]

let private resultNames =
    set [ "Microsoft.FSharp.Core.FSharpResult"; "Microsoft.FSharp.Core.Result" ]

let private wrapOf (t: FSharpType) : Wrap option =
    try
        let t = OptionModule.stripAbbreviations t

        if not t.HasTypeDefinition then
            None
        else
            let name =
                let n = OptionModule.fullNameOf t.TypeDefinition

                match n.IndexOf '`' with
                | -1 -> n
                | i -> n.Substring(0, i)

            let isString (arg: FSharpType) =
                let inner = OptionModule.stripAbbreviations arg

                inner.HasTypeDefinition
                && OptionModule.fullNameOf inner.TypeDefinition = "System.String"

            if name = "System.String" then
                Some Plain
            elif
                optionNames.Contains name
                && t.GenericArguments.Count = 1
                && isString t.GenericArguments.[0]
            then
                Some Wrapped
            // Result<_, string>: the error is the string, the Ok value is nobody's
            // business here
            elif
                resultNames.Contains name
                && t.GenericArguments.Count = 2
                && isString t.GenericArguments.[1]
            then
                Some WrappedResult
            else
                None
    with _ -> // fsharpanalyzer: ignore-line FR0055
        None

/// The slot a symbol is, if it can be one.
let private slotOf (symbol: FSharpSymbol) : Slot option =
    match symbol with
    | :? FSharpMemberOrFunctionOrValue as v ->
        try
            if
                v.IsMember
                || v.IsProperty
                || v.IsConstructor
                || v.IsActivePattern
                || v.IsMutable
                || v.IsCompilerGenerated
            then
                None
            elif v.CurriedParameterGroups.Count > 0 then
                match wrapOf v.ReturnParameter.Type with
                | Some w when v.GenericParameters.Count = 0 ->
                    Some
                        {
                            Symbol = symbol
                            Wrap = w
                            Kind = "return"
                        }
                | _ -> None
            else
                match wrapOf v.FullType with
                | Some w ->
                    Some
                        {
                            Symbol = symbol
                            Wrap = w
                            Kind = "value"
                        }
                | None -> None
        with _ -> // fsharpanalyzer: ignore-line FR0055
            None
    | :? FSharpField as f ->
        try
            if
                f.IsMutable
                || f.IsUnionCaseField
                || f.IsAnonRecordField
                || f.IsLiteral
                || f.IsStatic
            then
                None
            else
                match wrapOf f.FieldType with
                | Some w ->
                    Some
                        {
                            Symbol = symbol
                            Wrap = w
                            Kind = "field"
                        }
                | None -> None
        with _ -> // fsharpanalyzer: ignore-line FR0055
            None
    | _ -> None

let private parameterCount (symbol: FSharpSymbol) =
    match symbol with
    | :? FSharpMemberOrFunctionOrValue as v ->
        try
            v.CurriedParameterGroups.Count
        with _ -> // fsharpanalyzer: ignore-line FR0055
            0
    | _ -> 0

/// Does the assembly export this declaration?
/// Does the assembly export this declaration - public, or internal with
/// InternalsVisibleTo friends who see it as public?
let private exported (internalsVisible: bool) (symbol: FSharpSymbol) =
    try
        let visible (a: FSharpAccessibility) =
            a.IsPublic || (internalsVisible && a.IsInternal)

        let entityVisible (e: FSharpEntity option) =
            match e with
            | Some e -> visible e.Accessibility
            | None -> true

        match symbol with
        | :? FSharpMemberOrFunctionOrValue as v ->
            v.IsModuleValueOrMember
            && visible v.Accessibility
            && entityVisible v.DeclaringEntity
        | :? FSharpField as f -> visible f.Accessibility && entityVisible f.DeclaringEntity
        | _ -> false
    with _ -> // what cannot be read counts as exported; fsharpanalyzer: ignore-line FR0055
        true

/// How visible a declaration is - 0 private, 1 internal, 2 public - the
/// declaring entity's visibility capping the member's: a public `let` in a
/// private module is private to the file.
let private accessibilityRank (symbol: FSharpSymbol) =
    try
        let rank (a: FSharpAccessibility) =
            if a.IsPrivate then 0
            elif a.IsInternal then 1
            else 2

        let entityRank (e: FSharpEntity option) =
            match e with
            | Some e -> rank e.Accessibility
            | None -> 2

        match symbol with
        | :? FSharpMemberOrFunctionOrValue as v -> min (rank v.Accessibility) (entityRank v.DeclaringEntity)
        | :? FSharpField as f -> min (rank f.Accessibility) (entityRank f.DeclaringEntity)
        | :? FSharpEntity as e -> rank e.Accessibility
        | _ -> 2
    with _ -> // what cannot be read is taken as public; fsharpanalyzer: ignore-line FR0055
        2

// ---- syntax around a use --------------------------------------------------

let private sameSpan (a: range) (b: range) = a.Start = b.Start && a.End = b.End

/// The expression node a symbol use IS, with its ancestors: the identifier,
/// the `r.Field` path it ends, the `M.f` it names.
let private nodeAt (index: AstIndex.Index) (r: range) =
    index.Exprs
    |> Array.tryFind (fun (_, e) ->
        match e with
        | SynExpr.Ident id -> sameSpan id.idRange r
        // a field read `r.Field` is reported over the whole path; a value
        // inside one over its own identifier
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
            sameSpan e.Range r || ids |> List.exists (fun id -> sameSpan id.idRange r)
        | _ -> false)

/// The pattern node a symbol's definition IS, with its ancestors.
let private patAt (index: AstIndex.Index) (r: range) =
    index.Pats
    |> Array.tryFind (fun (_, p) ->
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> sameSpan id.idRange r
        | _ -> false)

/// The binding whose head pattern holds this definition, with the binding's
/// ancestors.
let private bindingOf (index: AstIndex.Index) (r: range) : (SynBinding * SyntaxNode list) option =
    let inHead (b: SynBinding) =
        let (SynBinding(headPat = head)) = b
        Range.rangeContainsRange head.Range r

    let fromDecls =
        index.Decls
        |> Array.tryPick (fun (path, d) ->
            match d with
            | SynModuleDecl.Let(bindings = bindings) ->
                bindings
                |> List.tryFind inHead
                |> Option.map (fun b -> b, SyntaxNode.SynModule d :: path)
            | _ -> None)

    match fromDecls with
    | Some found -> Some found
    | None ->
        index.Exprs
        |> Array.tryPick (fun (path, e) ->
            match e with
            | LetOrUseE lou when not lou.IsBang ->
                lou.Bindings
                |> List.tryFind inHead
                |> Option.map (fun b -> b, SyntaxNode.SynExpr e :: path)
            | _ -> None)

/// The match clause whose pattern binds this definition, with the match.
let private clauseOf (index: AstIndex.Index) (r: range) : (SynExpr * SynMatchClause) option =
    index.Exprs
    |> Array.tryPick (fun (_, e) ->
        match e with
        | SynExpr.Match(clauses = clauses) ->
            clauses
            |> List.tryFind (fun (SynMatchClause(pat = p)) -> Range.rangeContainsRange p.Range r)
            |> Option.map (fun c -> e, c)
        | _ -> None)

/// The exits of a body: the expressions its value can be.
let rec private exits (e: SynExpr) : SynExpr list =
    match e with
    | SynExpr.Sequential(expr2 = b) -> exits b
    | LetOrUseE lou when not lou.IsBang -> exits lou.Body
    | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some el) -> exits t @ exits el
    | SynExpr.Match(clauses = clauses) -> clauses |> List.collect (fun (SynMatchClause(resultExpr = r)) -> exits r)
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> exits inner
    | SynExpr.TryWith(tryExpr = t; withCases = cases) ->
        exits t
        @ (cases |> List.collect (fun (SynMatchClause(resultExpr = r)) -> exits r))
    | SynExpr.TryFinally(tryExpr = t) -> exits t
    | other -> [ other ]

/// Climb from a value node through the ancestors that merely pass its
/// value on — parentheses, the branches of an if or a match, the last of a
/// sequence, a let's body, a try — to the first that consumes it. Returns
/// the remaining ancestors and the node that reached them.
[<TailCall>]
let rec private passesUpTo (path: SyntaxNode list) (child: SynExpr) : SyntaxNode list * SynExpr =
    let branchOf (p: SynExpr) =
        match p with
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner) -> sameSpan inner.Range child.Range
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = el) ->
            sameSpan t.Range child.Range
            || (match el with
                | Some el -> sameSpan el.Range child.Range
                | None -> false)
        | SynExpr.Match(clauses = clauses) ->
            clauses
            |> List.exists (fun (SynMatchClause(resultExpr = r)) -> sameSpan r.Range child.Range)
        | SynExpr.Sequential(expr2 = b) -> sameSpan b.Range child.Range
        | LetOrUseE lou -> sameSpan lou.Body.Range child.Range
        | SynExpr.TryWith(tryExpr = t; withCases = cases) ->
            sameSpan t.Range child.Range
            || cases
               |> List.exists (fun (SynMatchClause(resultExpr = r)) -> sameSpan r.Range child.Range)
        | SynExpr.TryFinally(tryExpr = t) -> sameSpan t.Range child.Range
        | _ -> false

    match path with
    | SyntaxNode.SynExpr p :: rest when branchOf p -> passesUpTo rest p
    // the SDK path carries the clause between an arm's body and its match
    | SyntaxNode.SynMatchClause(SynMatchClause(resultExpr = r)) :: rest when sameSpan r.Range child.Range ->
        passesUpTo rest child
    | _ -> path, child

/// The head identifier of an application and how many arguments the
/// application already supplies: `String.concat ", " acc` is `concat`, 2.
[<TailCall>]
let rec private applicationHead (f: SynExpr) (n: int) : (Ident * int) option =
    match f with
    | SynExpr.App(isInfix = false; funcExpr = inner) -> applicationHead inner (n + 1)
    | SynExpr.TypeApp(expr = inner)
    | SynExpr.Paren(expr = inner) -> applicationHead inner n
    | SynExpr.Ident id -> Some(id, n)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some(List.last ids, n)
    | _ -> None

/// The enclosing module path of a syntax path, outermost first.
let private modulePathOf (path: SyntaxNode list) : string list =
    path
    |> List.rev
    |> List.collect (fun node ->
        match node with
        | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(longId = ids)) -> ids |> List.map (fun i -> i.idText)
        | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = ids))) ->
            ids |> List.map (fun i -> i.idText)
        | _ -> [])

/// The `open` targets of a file, as paths.
let private opensOf (index: AstIndex.Index) : string list list =
    index.Decls
    |> Array.choose (fun (_, d) ->
        match d with
        | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
            Some(ids |> List.map (fun i -> i.idText))
        | _ -> None)
    |> Array.toList

/// A literal as a double-backtick identifier, its first letter uppercased:
/// ``Bank account couldn't be selected``. None where the text cannot be one.
let private backticked (literal: string) : string option =
    let text = literal.Trim()

    if
        text = ""
        || text.Contains "``"
        || text |> Seq.exists (fun c -> c = '\n' || c = '\r' || c = '\t')
    then
        None
    else
        Some $"``{string (Char.ToUpperInvariant text.[0])}{text.Substring 1}``"

/// A name for a case, from a literal: `no-correctness` → `NoCorrectness`. A
/// sentence — more than four spaces — keeps its words behind double
/// backticks rather than run them together, and so does a text Pascal-casing
/// cannot name (a leading digit).
let private caseNameOf (literal: string) : string option =
    let words =
        literal.Split([| ' '; '-'; '_'; '.'; '/'; ':'; ','; ';'; '\'' |], StringSplitOptions.RemoveEmptyEntries)
        |> Array.map (fun w -> w |> String.filter Char.IsLetterOrDigit)
        |> Array.filter (fun w -> w <> "")

    let spaces = literal |> Seq.filter (fun c -> c = ' ') |> Seq.length

    if words.Length = 0 then
        None
    elif spaces > 4 then
        backticked literal
    else
        let name =
            words
            |> Array.map (fun w -> string (Char.ToUpperInvariant w.[0]) + w.Substring 1)
            |> String.concat ""

        if Char.IsDigit name.[0] then
            backticked literal
        else
            Some name

let private pascal (name: string) =
    if name = "" then
        name
    else
        string (Char.ToUpperInvariant name.[0]) + name.Substring 1

/// An F# string literal for this text.
let private quote (text: string) =
    let escaped =
        text.Replace("\\", "\\\\").Replace("\"", "\\\"").Replace("\n", "\\n").Replace("\r", "\\r").Replace("\t", "\\t")

    $"\"{escaped}\""

// ---- the analysis ---------------------------------------------------------

/// A value flowing into a slot.
type private Source =
    /// A string literal: its text, its range (to rewrite), and the constant
    /// binding it came through, if any (file, ident).
    | Literal of text: string * r: range * via: (string * Ident) option
    | FromSlot of Slot
    /// `None` / `ValueNone`.
    | Nothing
    | OpenSource of string

/// A use of a slot's value.
type private Sink =
    /// `match slot with` — in this file, this match.
    | Consumer of file: string * m: SynExpr
    /// `slot = "lit"`: the literal to rewrite, with its text.
    | Compare of file: string * r: range * text: string
    | ToSlot of Slot
    /// `$"{slot}"`, `string slot`, `slot.ToString()`: fine as they are.
    | Print
    /// A print that needs one edit to keep working: a `%s` hole becoming
    /// `%O`, an operand of `+` becoming `string operand`. The file, the
    /// range and the text.
    | Rewrite of file: string * r: range * text: string
    | OpenSink of string

/// The module-level `let name = "..."` bindings of a file, nested modules
/// included: the text and the identifier of each.
let private constants (index: AstIndex.Index) : (string * Ident) list =
    index.Decls
    |> Array.toList
    |> List.collect (fun (_, d) ->
        match d with
        | SynModuleDecl.Let(bindings = bindings) ->
            bindings
            |> List.choose (fun b ->
                match b with
                | SynBinding(
                    headPat = SynPat.Named(ident = SynIdent(ident = id))
                    expr = SynExpr.Const(SynConst.String(text = text), _)) -> Some(text, id)
                | _ -> None)
        | _ -> [])

/// The constant a symbol declared at this location binds: the binding whose
/// head identifier sits at the declaration, never one that merely shares its
/// name (a nested module's `let kind = "dir"` beside the file's own
/// `let kind = "file"` resolved to the wrong text by name).
let private constantAt (index: AstIndex.Index) (declaration: range) : (string * Ident) option =
    constants index
    |> List.tryFind (fun (_, id) -> Range.rangeContainsRange id.idRange declaration)

/// The module-level constants spelling a name: the shadowing bug's
/// candidates, where FCS resolves the pattern to a fresh local and only the
/// name says which constant the author meant.
let private constantsNamed (index: AstIndex.Index) (name: string) : (string * Ident) list =
    constants index |> List.filter (fun (_, id) -> id.idText = name)

/// Does the module-level constant carry `[<Literal>]`?
let private constantIsLiteral (index: AstIndex.Index) (constIdent: Ident) =
    index.Decls
    |> Array.exists (fun (_, d) ->
        match d with
        | SynModuleDecl.Let(bindings = bindings) ->
            bindings
            |> List.exists (fun b ->
                match b with
                | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); attributes = attrs) when
                    sameSpan id.idRange constIdent.idRange
                    ->
                    hasAttributeNamed "Literal" attrs
                | _ -> false)
        | _ -> false)

/// One arm of a consumer match, as the analysis reads it.
type private Arm =
    /// A literal pattern: the text, the pattern's range, the constant it
    /// came through if any, whether a `when` guards it.
    | LiteralArm of text: string * r: range * via: (string * Ident) option * guarded: bool
    /// `| name ->` spelling a module-level constant: the shadowing bug.
    | ShadowArm of text: string * r: range * via: (string * Ident) * name: string
    /// `| _ ->`, `| name ->`: the clause, and the name's symbol if bound.
    /// `| _ ->`, `| name ->`, `| Some _ ->`, `| Error _ ->`: the clause, the
    /// name's symbol if bound, and whether it covers the WHOLE slot (a bare
    /// wildcard) or only its string-carrying case.
    | CatchAll of clause: SynMatchClause * bound: FSharpSymbol option * whole: bool
    /// `| None ->` and the like: nothing to do.
    | Inert
    | OpenArm of string

/// An exported function kept in its public shape behind a private twin.
type private Adapter =
    {
        File: string
        Name: string
        /// The head identifier of the binding that becomes the twin.
        Head: Ident
        Twin: string
        Pad: string
        /// The parameter patterns as written, for the wrapper's own head.
        ParameterText: string
        /// The return annotation as written (` : T`), or "".
        ReturnText: string
        /// Each argument the wrapper passes on, and whether it goes through
        /// `OfString`.
        Parameters: (string * bool) list
        ReturnWrap: Wrap option
        /// Where the wrapper is inserted: the end of the binding.
        End: pos
        /// The applied uses in the compilation's own files, which move to the twin.
        OwnCalls: (string * range) list
        /// The binder and the catch-all clause lines `OfString` ends with.
        OfString: (string * string list) option
    }

type private Analysis(world: World, fileName: string, index: AstIndex.Index, source: ISourceText) =
    let files =
        Dictionary<string, (AstIndex.Index * ISourceText) option>(StringComparer.OrdinalIgnoreCase)

    let full (p: string) =
        try
            IO.Path.GetFullPath p
        with _ -> // fsharpanalyzer: ignore-line FR0055
            p

    member _.FileOf(path: string) : (AstIndex.Index * ISourceText) option =
        if String.Equals(full path, full fileName, StringComparison.OrdinalIgnoreCase) then
            Some(index, source)
        else
            match files.TryGetValue path with
            | true, cached -> cached
            | false, _ ->
                let loaded =
                    world.File path |> Option.map (fun (tree, text) -> AstIndex.ofTree tree, text)

                files.[path] <- loaded
                loaded

    member _.IsCoreCase(file: string, id: Ident) =
        match world.SymbolAt file id with
        | Some u ->
            match u.Symbol with
            | :? FSharpUnionCase as c ->
                let name = OptionModule.fullNameOf c
                // "Microsoft.FSharp.Core.Option<_>.Some", "...ValueOption<_>.ValueNone"
                name.StartsWith "Microsoft.FSharp.Core.Option"
                || name.StartsWith "Microsoft.FSharp.Core.ValueOption"
                || name.StartsWith "Microsoft.FSharp.Core.FSharpOption"
                || name.StartsWith "Microsoft.FSharp.Core.FSharpValueOption"
                || name.StartsWith "Microsoft.FSharp.Core.Result"
                || name.StartsWith "Microsoft.FSharp.Core.FSharpResult"
            | _ -> false
        | None -> false

    /// `Ok`: the case of a Result that carries the value, not the error the
    /// slot is about - what it wraps is never the string.
    member this.IsOkCase(file: string, id: Ident) =
        id.idText = "Ok" && this.IsCoreCase(file, id)

    member _.IsCoreFunction(file: string, id: Ident, fullName: string) =
        match world.SymbolAt file id with
        | Some u -> OptionModule.fullNameOf u.Symbol = fullName
        | None -> false

    /// A constant the identifier names: `[<Literal>]`, or a module-level
    /// `let name = "..."`.
    member this.ConstantOf(file: string, id: Ident) : (string * (string * Ident)) option =
        match world.SymbolAt file id with
        | Some u ->
            match u.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                let literal =
                    try
                        v.LiteralValue
                    with _ -> // fsharpanalyzer: ignore-line FR0055
                        None

                match literal with
                | Some(:? string as text) ->
                    let declFile = v.DeclarationLocation.FileName
                    Some(text, (declFile, id))
                | Some _ -> None
                | None ->
                    if
                        v.IsModuleValueOrMember
                        && not v.IsMember
                        && parameterCount v = 0
                        && not v.IsMutable
                    then
                        let declFile = v.DeclarationLocation.FileName

                        // by position, not by name: the file may hold another
                        // `let <name> = "..."` in a nested module; a declaration
                        // the index does not hold at that spot is no constant
                        match this.FileOf declFile with
                        | Some(declIndex, _) ->
                            constantAt declIndex v.DeclarationLocation
                            |> Option.map (fun (text, constIdent) -> text, (declFile, constIdent))
                        | None -> None
                    else
                        None
            | _ -> None
        | None -> None

    /// What flows out of an expression.
    member this.Classify(file: string, e: SynExpr) : Source list =
        let rec go (e: SynExpr) : Source list =
            match e with
            | SynExpr.Const(SynConst.String(text = text), r) -> [ Literal(text, r, None) ]
            | SynExpr.Paren(expr = inner)
            | SynExpr.Typed(expr = inner) -> go inner
            | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some el) -> go t @ go el
            | SynExpr.IfThenElse(elseExpr = None) -> [ OpenSource "an if without an else" ]
            | SynExpr.Match(clauses = clauses) -> clauses |> List.collect (fun (SynMatchClause(resultExpr = r)) -> go r)
            | SynExpr.Sequential(expr2 = b) -> go b
            | LetOrUseE lou when not lou.IsBang -> go lou.Body
            | SynExpr.App(isInfix = false; funcExpr = SingleIdent ctor; argExpr = arg) when this.IsCoreCase(file, ctor) ->
                if this.IsOkCase(file, ctor) then [ Nothing ] else go arg
            | SingleIdent id when this.IsCoreCase(file, id) -> [ Nothing ]
            | SynExpr.Ident id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> this.ValueSource(file, id, e.Range)
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> this.ValueSource(file, List.last ids, e.Range)
            | SynExpr.App(isInfix = false) ->
                match applicationHead e 0 with
                | Some(id, argCount) ->
                    match world.SymbolAt file id with
                    | Some u ->
                        match slotOf u.Symbol with
                        | Some slot when slot.Kind = "return" && parameterCount u.Symbol = argCount -> [ FromSlot slot ]
                        | _ -> [ OpenSource $"a call of '{id.idText}'" ]
                    | None -> [ OpenSource $"'{id.idText}' does not resolve" ]
                | None -> [ OpenSource "an application" ]
            | other -> [ OpenSource $"a %s{other.GetType().Name}" ]

        go e

    /// What an identifier (or a path ending in one) contributes: a
    /// constant, a slot's value, or something the rule cannot follow.
    member this.ValueSource(file: string, id: Ident, r: range) : Source list =
        match this.ConstantOf(file, id) with
        | Some(text, via) -> [ Literal(text, r, Some via) ]
        | None ->
            match world.SymbolAt file id with
            | Some u ->
                match slotOf u.Symbol with
                | Some slot when slot.Kind <> "return" -> [ FromSlot slot ]
                | _ -> [ OpenSource $"'{id.idText}' is not a string slot" ]
            | None -> [ OpenSource $"'{id.idText}' does not resolve" ]

    /// The function a parameter slot belongs to, or the slot's own symbol.
    member this.OwnerOf(slot: Slot) : FSharpSymbol =
        if slot.Kind <> "value" then
            slot.Symbol
        else
            match world.UsesOf slot.Symbol |> Array.tryFind (fun u -> u.IsFromDefinition) with
            | None -> slot.Symbol
            | Some d ->
                match this.FileOf d.Range.FileName with
                | None -> slot.Symbol
                | Some(defIndex, _) ->
                    match bindingOf defIndex d.Range with
                    | Some(SynBinding(
                               headPat = SynPat.LongIdent(
                                   longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats args)),
                           _) when args |> List.exists (fun a -> Range.rangeContainsRange a.Range d.Range) ->
                        match world.SymbolAt d.Range.FileName (List.last ids) with
                        | Some fn -> fn.Symbol
                        | None -> slot.Symbol
                    | _ -> slot.Symbol

    /// The parameter symbol at a position of a function, from its
    /// definition.
    member this.ParameterAt(fn: FSharpSymbol, position: int) : Slot option =
        let def = world.UsesOf fn |> Array.tryFind (fun u -> u.IsFromDefinition)

        match def with
        | None -> None
        | Some d ->
            match this.FileOf d.Range.FileName with
            | None -> None
            | Some(defIndex, _) ->
                match bindingOf defIndex d.Range with
                | Some(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats args)), _) when
                    position < args.Length
                    ->
                    let rec named (p: SynPat) =
                        match p with
                        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
                        | SynPat.Paren(pat = inner)
                        | SynPat.Typed(pat = inner) -> named inner
                        | _ -> None

                    named args.[position]
                    |> Option.bind (fun id -> world.SymbolAt d.Range.FileName id)
                    |> Option.bind (fun u -> slotOf u.Symbol)
                | _ -> None

    /// The arguments an application of `node` supplies, in order,
    /// followed by the ancestors above the whole application.
    member _.ArgumentsOf(path: SyntaxNode list, node: SynExpr) : SynExpr list * SyntaxNode list * SynExpr =
        let rec climb (path: SyntaxNode list) (current: SynExpr) (args: SynExpr list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) as app) :: rest when
                sameSpan f.Range current.Range
                ->
                climb rest app (args @ [ a ])
            | SyntaxNode.SynExpr(SynExpr.TypeApp(expr = inner) as ta) :: rest when sameSpan inner.Range current.Range ->
                climb rest ta args
            // `x |> f a`: the pipe hands `x` as the last argument
            | SyntaxNode.SynExpr(SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_PipeRight"; argExpr = lhs)
                argExpr = fe) as app) :: rest when sameSpan fe.Range current.Range -> climb rest app (args @ [ lhs ])
            | _ -> args, path, current

        climb path node []

    /// Where a slot's value goes from a node that IS the value.
    member this.SinkOf(file: string, path: SyntaxNode list, node: SynExpr) : Sink =
        let path, node = passesUpTo path node

        match path with
        | SyntaxNode.SynExpr(SynExpr.Match(expr = subject) as m) :: _ when sameSpan subject.Range node.Range ->
            Consumer(file, m)
        // `Some node` / `Error node` passes the value on wrapped; `Ok node`
        // makes it a Result's VALUE, which is not the string the rule follows
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = SingleIdent ctor; argExpr = a) as app) :: rest when
            sameSpan a.Range node.Range && this.IsCoreCase(file, ctor)
            ->
            if this.IsOkCase(file, ctor) then
                OpenSink "an Ok value"
            else
                this.SinkOf(file, rest, app)
        // node = "lit" / "lit" = node
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = IdentName op; argExpr = lhs)) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; argExpr = rhs)) :: _ when
            (op = "op_Equality" || op = "op_Inequality") && sameSpan lhs.Range node.Range
            ->
            this.CompareWith(file, rhs)
        | SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName op; argExpr = lhs)
            argExpr = rhs)) :: _ when (op = "op_Equality" || op = "op_Inequality") && sameSpan rhs.Range node.Range ->
            this.CompareWith(file, lhs)
        // `string node`
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = SingleIdent f; argExpr = a)) :: _ when
            sameSpan a.Range node.Range
            && this.IsCoreFunction(file, f, "Microsoft.FSharp.Core.ExtraTopLevelOperators.string")
            ->
            Print
        // `sprintf "... %s ..." node`: the hole becomes `%O`, which prints
        // through ToString
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a)) :: _ when
            sameSpan a.Range node.Range && (this.FormatHole(file, f)).IsSome
            ->
            match this.FormatHole(file, f) with
            | Some(Some(r, hole)) when hole = "s" -> Rewrite(file, r, "O")
            | Some(Some(_, hole)) -> OpenSink $"a %%{hole} format hole"
            | _ -> OpenSink "a format hole the rule cannot place"
        // `"text" + node` / `node + "text"`: the operand becomes `string node`
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = IdentName "op_Addition"; argExpr = lhs)) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; argExpr = rhs)) :: _ when sameSpan lhs.Range node.Range && this.IsStringy(file, rhs) ->
            Rewrite(file, node.Range, this.Stringed(file, node))
        | SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_Addition"; argExpr = lhs)
            argExpr = rhs)) :: _ when sameSpan rhs.Range node.Range && this.IsStringy(file, lhs) ->
            Rewrite(file, node.Range, this.Stringed(file, node))
        // an argument of a function
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a)) :: _ when
            sameSpan a.Range node.Range
            ->
            match applicationHead f 0 with
            | Some(id, position) ->
                match world.SymbolAt file id with
                | Some u ->
                    match u.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as v when
                        not v.IsMember && parameterCount v > position && v.GenericParameters.Count = 0
                        ->
                        match this.ParameterAt(v, position) with
                        | Some slot -> ToSlot slot
                        | None -> OpenSink $"an argument of '{id.idText}'"
                    | _ -> OpenSink $"an argument of '{id.idText}'"
                | None -> OpenSink $"an argument of '{id.idText}'"
            | None -> OpenSink "an argument"
        // `node |> f`
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = IdentName "op_PipeRight"; argExpr = lhs)) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; argExpr = fe)) :: _ when sameSpan lhs.Range node.Range ->
            match applicationHead fe 0 with
            | Some(id, supplied) ->
                match world.SymbolAt file id with
                | Some u ->
                    match u.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as v when
                        not v.IsMember && parameterCount v > supplied && v.GenericParameters.Count = 0
                        ->
                        match this.ParameterAt(v, supplied) with
                        | Some slot -> ToSlot slot
                        | None -> OpenSink $"an argument of '{id.idText}'"
                    | _ -> OpenSink $"an argument of '{id.idText}'"
                | None -> OpenSink $"an argument of '{id.idText}'"
            | None -> OpenSink "a pipe"
        // a record field's value
        | SyntaxNode.SynExpr(SynExpr.Record(recordFields = fields)) :: _ ->
            let field =
                fields
                |> List.tryPick (fun (SynExprRecordField(fieldName = (SynLongIdent(id = ids), _); expr = value)) ->
                    match value with
                    | Some v when sameSpan v.Range node.Range -> List.tryLast ids
                    | _ -> None)

            match field with
            | Some id ->
                match world.SymbolAt file id |> Option.bind (fun u -> slotOf u.Symbol) with
                | Some slot -> ToSlot slot
                | None -> OpenSink $"field '{id.idText}'"
            | None -> OpenSink "a record expression"
        // the value of a let, or the result of a function
        | SyntaxNode.SynBinding(SynBinding(headPat = head; expr = body)) :: _ when sameSpan body.Range node.Range ->
            let rec named (p: SynPat) =
                match p with
                | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) -> List.tryLast ids
                | SynPat.Paren(pat = inner)
                | SynPat.Typed(pat = inner) -> named inner
                | _ -> None

            match named head |> Option.bind (fun id -> world.SymbolAt file id) with
            | Some u ->
                match slotOf u.Symbol with
                | Some slot -> ToSlot slot
                | None -> OpenSink "a binding that is not a string slot"
            | None -> OpenSink "a binding"
        // `$"...{node}..."` prints through ToString; a typed hole `%s{node}`
        // needs its `s` to become `O`, and any other letter cannot take the
        // union
        | SyntaxNode.SynExpr(SynExpr.InterpolatedString(contents = parts)) :: _ ->
            let specifierBefore =
                parts
                |> List.pairwise
                |> List.tryPick (fun (before, part) ->
                    match before, part with
                    | SynInterpolatedStringPart.String(value = lead; range = r),
                      SynInterpolatedStringPart.FillExpr(fillExpr = fill) when
                        Range.rangeContainsRange fill.Range node.Range && endsWithFormatSpecifier lead
                        ->
                        Some(lead, r)
                    | _ -> None)

            match specifierBefore with
            | None -> Print
            | Some(lead, r) ->
                let letter = lead.[lead.Length - 1]
                // the part's range runs up to and including the `{`: the letter
                // stands right before it, and the source is asked to confirm
                let at =
                    Range.mkRange
                        file
                        (Position.mkPos r.EndLine (r.EndColumn - 2))
                        (Position.mkPos r.EndLine (r.EndColumn - 1))

                let spelled =
                    match this.FileOf file with
                    | Some(_, fs) ->
                        (try
                            textOfRange fs at
                         with _ ->
                             "")
                            =
                            string letter // fsharpanalyzer: ignore-line FR0055
                    | None -> false

                if letter = 's' && spelled then
                    Rewrite(file, at, "O")
                else
                    OpenSink $"a %%{letter} hole in an interpolated string"
        // node.ToString()
        | _ ->
            match node with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2 && (List.last ids).idText = "ToString"
                ->
                Print
            | _ -> OpenSink "a use the union cannot serve"

    /// Is the expression a string on its face: a literal, an interpolation,
    /// a `string x`, or a `+` of such?
    member this.IsStringy(file: string, e: SynExpr) : bool =
        match e with
        | SynExpr.Const(SynConst.String _, _)
        | SynExpr.InterpolatedString _ -> true
        | SynExpr.Paren(expr = inner) -> this.IsStringy(file, inner)
        | SynExpr.App(isInfix = false; funcExpr = SingleIdent f) ->
            this.IsCoreFunction(file, f, "Microsoft.FSharp.Core.ExtraTopLevelOperators.string")
        | SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_Addition"; argExpr = lhs)
            argExpr = rhs) -> this.IsStringy(file, lhs) || this.IsStringy(file, rhs)
        | _ -> false

    /// `string x`, `string (f x)`.
    member this.Stringed(file: string, node: SynExpr) : string =
        let text =
            match this.FileOf file with
            | Some(_, fs) -> textOfRange fs node.Range
            | None -> ""

        if isAtomic node then
            $"string {text}"
        else
            $"string ({text})"

    /// For an application `f` whose head is a printf-family function with a
    /// literal format, the hole the NEXT argument fills: its `%%s`-letter
    /// range and letter. None where `f` is not such a call; Some None where
    /// the hole cannot be placed.
    member this.FormatHole(file: string, f: SynExpr) : (range * string) option option =
        let rec parts (e: SynExpr) (args: SynExpr list) =
            match e with
            | SynExpr.App(isInfix = false; funcExpr = inner; argExpr = a) -> parts inner (a :: args)
            | SynExpr.TypeApp(expr = inner) -> parts inner args
            | SingleIdent id -> Some(id, args)
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some(List.last ids, args)
            | _ -> None

        match parts f [] with
        | Some(head, args) when
            (match world.SymbolAt file head with
             | Some u ->
                 let name = OptionModule.fullNameOf u.Symbol

                 name.StartsWith "Microsoft.FSharp.Core.ExtraTopLevelOperators."
                 && (name.EndsWith "printf" || name.EndsWith "printfn" || name.EndsWith "failwithf")
                 || name.StartsWith "Microsoft.FSharp.Core.Printf."
             | None -> false)
            ->
            // the format is the first argument; the value is the argument
            // after those already supplied
            match args with
            | SynExpr.Const(SynConst.String(text = format), formatRange) :: supplied ->
                let holes =
                    Text.RegularExpressions.Regex.Matches(format, @"%[-+0 #]*\d*(?:\.\d+)?([a-zA-Z])|%%")
                    |> Seq.cast<Text.RegularExpressions.Match>
                    |> Seq.filter (fun m -> m.Value <> "%%")
                    |> List.ofSeq

                let index = supplied.Length

                // the hole's column is counted in the literal's VALUE: only a
                // plain literal whose source spells the value character for
                // character - no escapes, no @ or triple quotes - places it
                let spelledPlainly =
                    match this.FileOf file with
                    | Some(_, fs) -> textOfRange fs formatRange = $"\"{format}\""
                    | None -> false

                if index < holes.Length && isSingleLine formatRange && spelledPlainly then
                    let m = holes.[index]
                    let letter = m.Groups.[1]
                    // the literal's text starts one column after its opening quote
                    let column = formatRange.StartColumn + 1 + letter.Index

                    Some(
                        Some(
                            Range.mkRange
                                file
                                (Position.mkPos formatRange.StartLine column)
                                (Position.mkPos formatRange.StartLine (column + 1)),
                            letter.Value
                        )
                    )
                else
                    Some None
            | _ -> Some None
        | _ -> None

    member this.CompareWith(file: string, other: SynExpr) : Sink =
        match other with
        | SynExpr.Const(SynConst.String(text = text), r) -> Compare(file, r, text)
        | SynExpr.Paren(expr = SynExpr.Const(SynConst.String(text = text), r)) -> Compare(file, r, text)
        | SingleIdent id ->
            match this.ConstantOf(file, id) with
            | Some(text, _) -> Compare(file, other.Range, text)
            | None -> OpenSink "a comparison with a non-literal"
        | _ -> OpenSink "a comparison with a non-literal"

    /// Everything flowing into a slot.
    member this.Sources(slot: Slot) : Source list =
        let uses = world.UsesOf slot.Symbol

        match slot.Kind with
        | "field" ->
            // record expressions assigning the field
            uses
            |> Array.toList
            |> List.collect (fun u ->
                if u.IsFromDefinition then
                    []
                else
                    match this.FileOf u.Range.FileName with
                    | None -> [ OpenSource "a use in an unreadable file" ]
                    | Some(useIndex, _) ->
                        let assigned =
                            useIndex.Exprs
                            |> Array.tryPick (fun (_, e) ->
                                match e with
                                | SynExpr.Record(recordFields = fields) ->
                                    fields
                                    |> List.tryPick
                                        (fun (SynExprRecordField(fieldName = (SynLongIdent(id = ids), _); expr = v)) ->
                                            match List.tryLast ids, v with
                                            | Some last, Some v when sameSpan last.idRange u.Range -> Some v
                                            | _ -> None)
                                | _ -> None)

                        match assigned with
                        | Some v -> this.Classify(u.Range.FileName, v)
                        | None ->
                            // a record pattern binds the field's value to a name
                            // the rule does not follow; a read is a sink
                            let inPattern =
                                useIndex.Pats
                                |> Array.exists (fun (_, p) ->
                                    match p with
                                    | SynPat.Record(fieldPats = fps) ->
                                        fps
                                        |> List.exists (fun (NamePatPairField(fieldName = SynLongIdent(id = fids))) ->
                                            fids |> List.exists (fun id -> sameSpan id.idRange u.Range))
                                    | _ -> false)

                            if inPattern then [ OpenSource "a record pattern" ] else [])
        | _ ->
            match uses |> Array.tryFind (fun u -> u.IsFromDefinition) with
            | None -> [ OpenSource "a definition the host cannot see" ]
            | Some def ->
                let file = def.Range.FileName

                match this.FileOf file with
                | None -> [ OpenSource "a definition in an unreadable file" ]
                | Some(defIndex, _) ->
                    match bindingOf defIndex def.Range with
                    | Some(SynBinding(headPat = head; expr = body), _) ->
                        let rec named (p: SynPat) =
                            match p with
                            | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
                            | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) -> List.tryLast ids
                            | SynPat.Paren(pat = inner)
                            | SynPat.Typed(pat = inner) -> named inner
                            | _ -> None

                        match named head with
                        | Some id when sameSpan id.idRange def.Range ->
                            // the binding's own name: a value or a function
                            if slot.Kind = "return" then
                                exits body |> List.collect (fun e -> this.Classify(file, e))
                            else
                                this.Classify(file, body)
                        | _ ->
                            // a parameter: its position, then every call site
                            match head with
                            | SynPat.LongIdent(longDotId = SynLongIdent(id = fnIds); argPats = SynArgPats.Pats args) ->
                                let position =
                                    args |> List.tryFindIndex (fun a -> Range.rangeContainsRange a.Range def.Range)

                                let rec plain (p: SynPat) =
                                    match p with
                                    | SynPat.Named(ident = SynIdent(ident = id)) -> sameSpan id.idRange def.Range
                                    | SynPat.Paren(pat = inner)
                                    | SynPat.Typed(pat = inner) -> plain inner
                                    | _ -> false

                                match position with
                                | Some i when plain args.[i] ->
                                    match world.SymbolAt file (List.last fnIds) with
                                    | Some fn -> this.CallSiteArguments(fn.Symbol, i)
                                    | None -> [ OpenSource "a function that does not resolve" ]
                                | Some _ -> [ OpenSource "a destructured parameter" ]
                                | None -> [ OpenSource "a parameter the rule cannot place" ]
                            | _ -> [ OpenSource "a binding shape the rule does not read" ]
                    | None ->
                        // a name bound by a match clause: `Some name`, `| name ->`
                        match clauseOf defIndex def.Range with
                        | Some(SynExpr.Match(expr = subject), SynMatchClause(pat = p)) ->
                            let rec unwrapped (p: SynPat) =
                                match p with
                                | SynPat.Named(ident = SynIdent(ident = id)) -> sameSpan id.idRange def.Range
                                | SynPat.Paren(pat = inner) -> unwrapped inner
                                | SynPat.LongIdent(
                                    longDotId = SynLongIdent(id = [ ctor ]); argPats = SynArgPats.Pats [ inner ]) ->
                                    this.IsCoreCase(file, ctor)
                                    && not (this.IsOkCase(file, ctor))
                                    && unwrapped inner
                                | _ -> false

                            if unwrapped p then
                                this.Classify(file, subject)
                            else
                                [ OpenSource "a pattern the rule does not read" ]
                        | _ -> [ OpenSource "a binding the rule cannot find (a lambda or a loop?)" ]

    /// The argument every call site passes at a position.
    member this.CallSiteArguments(fn: FSharpSymbol, position: int) : Source list =
        world.UsesOf fn
        |> Array.toList
        |> List.collect (fun u ->
            if u.IsFromDefinition then
                []
            else
                match this.FileOf u.Range.FileName with
                | None -> [ OpenSource "a call site in an unreadable file" ]
                | Some(useIndex, _) ->
                    match nodeAt useIndex u.Range with
                    | Some(path, node) ->
                        let args, _, _ = this.ArgumentsOf(path, node)

                        if position < args.Length then
                            this.Classify(u.Range.FileName, args.[position])
                        else
                            [ OpenSource $"'{u.Symbol.DisplayName}' used as a value or partially applied" ]
                    | None -> [ OpenSource "a call site the rule cannot read" ])

    /// Every use of a slot's value.
    member this.Sinks(slot: Slot) : Sink list =
        world.UsesOf slot.Symbol
        |> Array.toList
        |> List.collect (fun u ->
            if u.IsFromDefinition then
                []
            else
                match this.FileOf u.Range.FileName with
                | None -> [ OpenSink "a use in an unreadable file" ]
                | Some(useIndex, _) ->
                    match nodeAt useIndex u.Range with
                    | None ->
                        // a record field named in a construction or a pattern
                        // is a source, not a read
                        if slot.Kind = "field" then
                            []
                        else
                            [ OpenSink "a use the rule cannot read" ]
                    | Some(path, node) ->
                        match slot.Kind with
                        | "return" ->
                            let args, rest, whole = this.ArgumentsOf(path, node)

                            if args.Length = parameterCount slot.Symbol then
                                [ this.SinkOf(u.Range.FileName, rest, whole) ]
                            else
                                [ OpenSink $"'{u.Symbol.DisplayName}' used as a value or partially applied" ]
                        | _ ->
                            match node with
                            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                not (sameSpan node.Range u.Range)
                                && not (sameSpan (List.last ids).idRange u.Range)
                                ->
                                // the use heads a path: x.ToString() prints, any
                                // other member is the string's
                                let after =
                                    ids
                                    |> List.skipWhile (fun id -> not (sameSpan id.idRange u.Range))
                                    |> List.tail
                                    |> List.map (fun id -> id.idText)

                                if after = [ "ToString" ] then
                                    [ Print ]
                                else
                                    [ OpenSink $"a member access '{identText ids}'" ]
                            | _ -> [ this.SinkOf(u.Range.FileName, path, node) ])

    /// The adapter that keeps an exported function's public shape, or None
    /// where the function cannot be split: a `rec` or `and` binding, one with
    /// attributes or `inline`, a parameter that is not a plain name, a use as
    /// a value, a twin name the compilation already has, or a parameter whose
    /// match has no raising catch-all to become `OfString`'s unknown arm.
    member this.AdapterFor
        (
            owner: FSharpSymbol,
            paramSlots: Slot list,
            returnSlot: Slot option,
            consumers: (string * SynExpr) list,
            catchAlls: (string * SynExpr * SynMatchClause * FSharpSymbol option * bool) list,
            ownFile: string -> bool
        ) : Adapter option =
        let def = world.UsesOf owner |> Array.tryFind (fun u -> u.IsFromDefinition)

        match def with
        | None -> None
        | Some d ->
            let file = d.Range.FileName

            match this.FileOf file with
            | None -> None
            | Some(fi, fs) ->
                match bindingOf fi d.Range with
                | Some(SynBinding(
                           attributes = []
                           isInline = false
                           // `private describeCore` replaces the head: an `internal`
                           // already there would double the modifier
                           accessibility = None
                           headPat = SynPat.LongIdent(
                               longDotId = SynLongIdent(id = [ head ]); argPats = SynArgPats.Pats args)
                           returnInfo = returnInfo) as binding,
                       SyntaxNode.SynModule(SynModuleDecl.Let(isRecursive = false; bindings = [ _ ])) :: _) when
                    sameSpan head.idRange d.Range && not args.IsEmpty
                    ->
                    let rec argument (p: SynPat) =
                        match p with
                        | SynPat.Paren(pat = SynPat.Const(SynConst.Unit, _)) -> Some "()"
                        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                        | SynPat.Paren(pat = inner)
                        | SynPat.Typed(pat = inner) -> argument inner
                        | _ -> None

                    let arguments = args |> List.map argument
                    let twin = head.idText + "Core"

                    let twinTaken =
                        world.SourceFiles
                        |> List.exists (fun f ->
                            match this.FileOf f with
                            | Some(_, s) ->
                                Text.RegularExpressions.Regex.IsMatch(
                                    s.GetSubTextString(0, s.Length),
                                    $@"\b{Text.RegularExpressions.Regex.Escape twin}\b"
                                )
                            | None -> true)

                    // every applied use in the compilation moves to the twin; a
                    // first-class use would carry the old type
                    let ownCalls =
                        world.UsesOf owner
                        |> Array.toList
                        |> List.filter (fun u -> not u.IsFromDefinition && ownFile u.Range.FileName)
                        |> List.map (fun u ->
                            match this.FileOf u.Range.FileName with
                            | Some(ui, _) ->
                                match nodeAt ui u.Range with
                                | Some(path, node) ->
                                    let supplied, _, _ = this.ArgumentsOf(path, node)

                                    if supplied.Length = parameterCount owner then
                                        Some(u.Range.FileName, u.Range)
                                    else
                                        None
                                | None -> None
                            | None -> None)

                    // the catch-all an adapted parameter's match ends with: the
                    // unknown-value arm of OfString, verbatim, so unknown input
                    // raises exactly as it did
                    let ofString =
                        paramSlots
                        |> List.tryPick (fun slot ->
                            let name = slot.Symbol.DisplayName

                            consumers
                            |> List.tryPick (fun (cf, m) ->
                                match m with
                                | SynExpr.Match(expr = SynExpr.Ident id) when
                                    cf = file
                                    && id.idText = name
                                    && Range.rangeContainsRange binding.RangeOfBindingWithRhs m.Range
                                    ->
                                    catchAlls
                                    |> List.tryPick (fun (f, mm, clause, _, whole) ->
                                        let (SynMatchClause(pat = p; resultExpr = body; whenExpr = guard)) = clause

                                        let raises =
                                            match applicationHead body 0 with
                                            | Some(h, _) ->
                                                match world.SymbolAt file h with
                                                | Some u ->
                                                    let full = OptionModule.fullNameOf u.Symbol

                                                    [
                                                        "failwith"
                                                        "failwithf"
                                                        "raise"
                                                        "invalidArg"
                                                        "invalidOp"
                                                        "nullArg"
                                                        "reraise"
                                                    ]
                                                    |> List.exists (fun n ->
                                                        full = "Microsoft.FSharp.Core.Operators." + n
                                                        || full =
                                                            "Microsoft.FSharp.Core.ExtraTopLevelOperators." + n)
                                                | None -> false
                                            | None -> false

                                        let binder =
                                            match p with
                                            | SynPat.Named(ident = SynIdent(ident = b)) -> Some b.idText
                                            | SynPat.Wild _ -> Some "value"
                                            | _ -> None

                                        // the body may name the binder and module-level or
                                        // library things, nothing local to the function
                                        let onlyTheBinder =
                                            let allowed (id: Ident) =
                                                Some id.idText = binder
                                                || (match world.SymbolAt file id with
                                                    | Some u ->
                                                        match u.Symbol with
                                                        | :? FSharpMemberOrFunctionOrValue as v ->
                                                            v.IsModuleValueOrMember
                                                        | _ -> true
                                                    | None -> false)

                                            fi.Exprs
                                            |> Array.forall (fun (_, e) ->
                                                match e with
                                                | SynExpr.Ident id when
                                                    Range.rangeContainsRange body.Range id.idRange
                                                    ->
                                                    allowed id
                                                // `local.Field`: the head of a path is what
                                                // has to be in reach
                                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) when
                                                    Range.rangeContainsRange body.Range first.idRange
                                                    ->
                                                    allowed first
                                                | _ -> true)

                                        if
                                            f = file
                                            && sameSpan mm.Range m.Range
                                            && whole
                                            && raises
                                            && guard.IsNone
                                            && onlyTheBinder
                                        then
                                            binder
                                            |> Option.bind (fun b ->
                                                reindentBlock
                                                    2
                                                    clause.Range.StartColumn
                                                    (textOfRange fs clause.Range)
                                                |> Option.map (fun moved ->
                                                    let lines = moved.Split '\n'
                                                    lines.[0] <- "| " + lines.[0].Substring 2
                                                    b, List.ofArray lines))
                                        else
                                            None)
                                | _ -> None))

                    let adaptedParameters =
                        List.zip args arguments
                        |> List.map (fun (p, name) ->
                            name,
                            paramSlots
                            |> List.exists (fun s ->
                                match s.Symbol.DeclarationLocation with
                                | Some r -> Range.rangeContainsRange p.Range r
                                | None -> false))

                    let column =
                        let t = fs.GetLineString(binding.RangeOfBindingWithRhs.StartLine - 1)
                        t.Length - t.TrimStart().Length

                    let endLine = binding.RangeOfBindingWithRhs.EndLine

                    if
                        arguments |> List.forall Option.isSome
                        && args |> List.forall (fun p -> isSingleLine p.Range)
                        && not twinTaken
                        && ownCalls |> List.forall Option.isSome
                        && (paramSlots.IsEmpty || ofString.IsSome)
                        && (not paramSlots.IsEmpty || returnSlot.IsSome)
                    then
                        Some
                            {
                                File = file
                                Name = head.idText
                                Head = head
                                Twin = twin
                                Pad = String(' ', column)
                                ParameterText = args |> List.map (fun p -> textOfRange fs p.Range) |> String.concat " "
                                ReturnText =
                                    match returnInfo with
                                    | Some(SynBindingReturnInfo(typeName = t)) -> " : " + textOfRange fs t.Range
                                    | None -> ""
                                Parameters = adaptedParameters |> List.map (fun (name, adapted) -> name.Value, adapted)
                                ReturnWrap = returnSlot |> Option.map (fun s -> s.Wrap)
                                // the wrapper takes the line after the binding, where a dead
                                // catch-all's deletion (whole lines up to that same point)
                                // sits above it; at the file's end it appends to the last line
                                End =
                                    if endLine < fs.GetLineCount() then
                                        Position.mkPos (endLine + 1) 0
                                    else
                                        Position.mkPos endLine (fs.GetLineString(endLine - 1)).Length
                                OwnCalls = ownCalls |> List.choose id
                                OfString = if paramSlots.IsEmpty then None else ofString
                            }
                    else
                        None
                | _ -> None

    /// The arms of a consumer match.
    member this.Arms(file: string, clauses: SynMatchClause list) : Arm list =
        clauses
        |> List.mapi (fun i (SynMatchClause(pat = p; whenExpr = guard) as clause) ->
            let guarded = guard.IsSome
            let later = i < clauses.Length - 1

            // a guarded catch-all is no catch-all the proof can remove: what
            // its guard turns away the arms below still meet, and what it
            // lets through never reaches them, so deleting it as dead would
            // change the answer (`| v when v.Length = 4 -> ...` above `| "POST"`)
            let catchAll (bound: FSharpSymbol option) (whole: bool) =
                if guarded then
                    [ OpenArm "a guarded catch-all" ]
                else
                    [ CatchAll(clause, bound, whole) ]

            let rec read (p: SynPat) : Arm list =
                match p with
                | SynPat.Const(SynConst.String(text = text), r) -> [ LiteralArm(text, r, None, guarded) ]
                | SynPat.Or(lhsPat = a; rhsPat = b) ->
                    // `| null | "" ->`: a catch-all beside a literal in ONE
                    // clause. Read as [CatchAll; LiteralArm ""] the proof
                    // deleted the clause as dead while its literal half was
                    // edited too - two edits over one arm, and a case with
                    // no arm left at runtime - so a catch-all half of an
                    // or-pattern with a literal stays open and the rule
                    // stands down. A plain `| null ->` clause is still the
                    // dead catch-all below
                    let arms = read a @ read b

                    let holdsLiteral =
                        arms
                        |> List.exists (fun arm ->
                            match arm with
                            | LiteralArm _
                            | ShadowArm _ -> true
                            | _ -> false)

                    if holdsLiteral then
                        arms
                        |> List.map (fun arm ->
                            match arm with
                            | CatchAll _ -> OpenArm "a null or wildcard beside a literal in one or-pattern"
                            | other -> other)
                    else
                        arms
                | SynPat.Paren(pat = inner) -> read inner
                | SynPat.Wild _ -> catchAll None true
                | SynPat.Named(ident = SynIdent(ident = id)) ->
                    match world.SymbolAt file id with
                    | Some u ->
                        match u.Symbol with
                        | :? FSharpMemberOrFunctionOrValue as v when
                            (try
                                v.LiteralValue.IsSome
                             with _ -> // fsharpanalyzer: ignore-line FR0055
                                 false)
                            ->
                            match v.LiteralValue with
                            | Some(:? string as text) ->
                                [ LiteralArm(text, p.Range, Some(v.DeclarationLocation.FileName, id), guarded) ]
                            | _ -> [ OpenArm "a non-string literal pattern" ]
                        | _ ->
                            // a fresh variable: the shadowing bug when ONE
                            // module-level constant of the name exists and
                            // arms follow, a catch-all otherwise; two constants
                            // of the name (a nested module's beside the file's)
                            // leave no way to say which the author meant
                            let candidates =
                                match this.FileOf file with
                                | Some(fi, _) -> constantsNamed fi id.idText
                                | None -> []

                            // FCS resolves the pattern to the fresh local either way;
                            // the binding's own attributes say whether the name was
                            // a [<Literal>] constant pattern all along
                            match candidates with
                            | [ text, constIdent ] when
                                (match this.FileOf file with
                                 | Some(fi, _) -> constantIsLiteral fi constIdent
                                 | None -> false)
                                ->
                                [ LiteralArm(text, p.Range, Some(file, constIdent), guarded) ]
                            | [ text, constIdent ] when later && not guarded ->
                                [ ShadowArm(text, p.Range, (file, constIdent), id.idText) ]
                            | _ :: _ :: _ -> [ OpenArm $"a pattern '{id.idText}' more than one constant spells" ]
                            | _ -> catchAll (Some u.Symbol) true
                    | None -> [ OpenArm "a pattern that does not resolve" ]
                | SynPat.LongIdent(longDotId = SynLongIdent(id = [ ctor ]); argPats = SynArgPats.Pats args) when
                    this.IsCoreCase(file, ctor)
                    ->
                    match args with
                    | [] -> [ Inert ] // None
                    | [ _ ] when this.IsOkCase(file, ctor) -> [ Inert ] // the value, not the error
                    | [ inner ] ->
                        match inner with
                        | SynPat.Wild _ -> catchAll None false
                        | SynPat.Named(ident = SynIdent(ident = id)) ->
                            match world.SymbolAt file id with
                            | Some u -> catchAll (Some u.Symbol) false
                            | None -> [ OpenArm "a pattern that does not resolve" ]
                        | _ -> read inner
                    | _ -> [ OpenArm "a pattern the rule does not read" ]
                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats []) ->
                    let last = List.last ids

                    match this.ConstantOf(file, last) with
                    | Some(text, via) -> [ LiteralArm(text, p.Range, Some via, guarded) ]
                    | None -> [ OpenArm $"a pattern '{identText ids}'" ]
                // `| null ->`: the component's proof shows every source a
                // literal, so null never arrives and the arm is as dead as a
                // trailing wildcard — it goes with the other catch-alls. A
                // union has no null arm to keep (FS0043), so a LIVE one (the
                // literals not all covered, or a guard) stands the rule down
                // where a wildcard would stay: see `liveNamesOk`
                | SynPat.Null _ -> catchAll None true
                | _ -> [ OpenArm "a pattern the rule does not read" ]

            read p)
        |> List.concat

// ---- the rule -------------------------------------------------------------

/// Everything the closure learned about one component.
type private Component =
    {
        Slots: Slot list
        Literals: (string * range * (string * Ident) option) list
        Consumers: (string * SynExpr) list
        Compares: (string * range * string) list
        Rewrites: (string * range * string) list
        Shadowed: (string * range * (string * Ident) * string) list
        ArmLiterals: (string * range * (string * Ident) option * bool) list
        CatchAlls: (string * SynExpr * SynMatchClause * FSharpSymbol option * bool) list
        Failure: string option
    }

let private closure (analysis: Analysis) (start: Slot) : Component =
    let slots = ResizeArray<Slot>()
    let literals = ResizeArray()
    let consumers = ResizeArray()
    let compares = ResizeArray()
    let rewrites = ResizeArray()
    let shadowed = ResizeArray()
    let armLiterals = ResizeArray()
    let catchAlls = ResizeArray()
    let seenMatches = ResizeArray<string * range>()
    let mutable failure = None
    let queue = Queue<Slot>()

    let enqueue (s: Slot) =
        if not (slots |> Seq.exists (fun k -> sameSymbol k.Symbol s.Symbol)) then
            slots.Add s
            queue.Enqueue s

    let fail reason =
        if failure.IsNone then
            failure <- Some reason

    enqueue start

    while queue.Count > 0 && failure.IsNone do
        let slot = queue.Dequeue()

        for s in analysis.Sources slot do
            match s with
            | Literal(text, r, via) -> literals.Add(text, r, via)
            | FromSlot other -> enqueue other
            | Nothing -> ()
            | OpenSource reason -> fail $"'{slot.Symbol.DisplayName}' is fed from {reason}"

        for s in analysis.Sinks slot do
            match s with
            | Consumer(file, m) ->
                if not (seenMatches |> Seq.exists (fun (f, r) -> f = file && sameSpan r m.Range)) then
                    seenMatches.Add(file, m.Range)
                    consumers.Add(file, m)

                    match m with
                    | SynExpr.Match(clauses = clauses) ->
                        for arm in analysis.Arms(file, clauses) do
                            match arm with
                            | LiteralArm(text, r, via, guarded) -> armLiterals.Add(text, r, via, guarded)
                            | ShadowArm(text, r, via, name) -> shadowed.Add(text, r, via, name)
                            | CatchAll(clause, bound, whole) -> catchAlls.Add(file, m, clause, bound, whole)
                            | Inert -> ()
                            | OpenArm reason -> fail $"a match on '{slot.Symbol.DisplayName}' has {reason}"
                    | _ -> ()
            | Compare(file, r, text) -> compares.Add(file, r, text)
            | Rewrite(file, r, text) -> rewrites.Add(file, r, text)
            | ToSlot other -> enqueue other
            | Print -> ()
            | OpenSink reason -> fail $"'{slot.Symbol.DisplayName}' flows into {reason}"

    {
        Slots = List.ofSeq slots
        Literals = List.ofSeq literals
        Consumers = List.ofSeq consumers
        Compares = List.ofSeq compares
        Rewrites = List.ofSeq rewrites
        Shadowed = List.ofSeq shadowed
        ArmLiterals = List.ofSeq armLiterals
        CatchAlls = List.ofSeq catchAlls
        Failure = failure
    }

/// The `string` type node inside an annotation: `string`, `string option`,
/// `option<string>`, `voption<string>`.
[<TailCall>]
let rec private stringTypeIn (t: SynType) : SynType option =
    match t with
    | SynType.LongIdent(SynLongIdent(id = [ id ])) when id.idText = "string" -> Some t
    | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)); typeArgs = [ arg ]) when
        (match List.tryLast ids with
         | Some last ->
             last.idText = "option"
             || last.idText = "voption"
             || last.idText = "Option"
             || last.idText = "ValueOption"
         | None -> false)
        ->
        stringTypeIn arg
    // Result<'ok, string>: the error is the string
    | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)); typeArgs = [ _; err ]) when
        (match List.tryLast ids with
         | Some last -> last.idText = "Result"
         | None -> false)
        ->
        stringTypeIn err
    | SynType.Paren(innerType = inner) -> stringTypeIn inner
    | _ -> None

/// The line span of a clause when it can go whole: its bar starts a line
/// and its body ends one, a trailing `//` comment allowed (it is kept).
let private clauseLines (source: ISourceText) (clause: SynMatchClause) : (int * int) option =
    let (SynMatchClause(range = r; trivia = trivia)) = clause

    let startLine =
        match trivia.BarRange with
        | Some bar -> bar.StartLine
        | None -> r.StartLine

    let firstLine = source.GetLineString(startLine - 1)
    let lastLine = source.GetLineString(r.EndLine - 1)
    let after = lastLine.Substring(min lastLine.Length r.EndColumn).Trim()

    if
        firstLine.TrimStart().StartsWith "|"
        && (after = "" || after.StartsWith "//")
        && startLine <= r.EndLine
    then
        Some(startLine, r.EndLine)
    else
        None

/// The comments a dead arm carried, each on a line of its own at the arm's
/// column: a `// TODO` on an arm the proof made unreachable is still the
/// author's note, and no fix of this tool deletes a comment silently.
let private keptComments (tree: ParsedInput) (source: ISourceText) (first: int) (last: int) (column: int) =
    commentsWithText tree source
    |> List.filter (fun (r, _) -> r.StartLine >= first && r.EndLine <= last)
    |> List.sortBy (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.map (fun (_, text) -> String(' ', column) + text)

/// Does the file hold a match with two string literal arms at all? The cheap
/// question a host asks before paying for the world.
let hasCandidates (parseTree: ParsedInput) =
    let index = AstIndex.ofTree parseTree

    index.Exprs
    |> Array.exists (fun (_, e) ->
        match e with
        | SynExpr.Match(clauses = clauses) ->
            clauses
            |> List.sumBy (fun (SynMatchClause(pat = p)) ->
                let rec literals (p: SynPat) =
                    match p with
                    | SynPat.Const(SynConst.String _, _) -> 1
                    | SynPat.Or(lhsPat = a; rhsPat = b) -> literals a + literals b
                    | SynPat.Paren(pat = inner) -> literals inner
                    | SynPat.Named _ -> 1
                    | SynPat.LongIdent(argPats = SynArgPats.Pats [ inner ]) -> literals inner
                    | SynPat.LongIdent(argPats = SynArgPats.Pats []) -> 1
                    | _ -> 0

                literals p)
            >= 2
        | _ -> false)

/// Find the closed string sets matched in this file. Requires the world.
let find (world: World) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let fileName = parseTree.FileName
    let index = AstIndex.ofTree parseTree
    let analysis = Analysis(world, fileName, index, source)

    // components already reported from this file: a second match on the
    // same slots says nothing new
    let reported = ResizeArray<Slot list>()

    // union names this file's earlier suggestions introduce: two records with a
    // `domain` field each got a `Domain` (Fuuga's generate-honesty-data.fsx),
    // a duplicate definition the build check rolled back
    let introduced = HashSet<string>()

    let candidates =
        [
            for _, expr in index.Exprs do
                match expr with
                | SynExpr.Match(expr = subject; clauses = clauses) when
                    clauses
                    |> List.sumBy (fun (SynMatchClause(pat = p)) ->
                        let rec literals (p: SynPat) =
                            match p with
                            | SynPat.Const(SynConst.String _, _) -> 1
                            | SynPat.Or(lhsPat = a; rhsPat = b) -> literals a + literals b
                            | SynPat.Paren(pat = inner) -> literals inner
                            | SynPat.Named _ -> 1 // a constant, or the shadowing bug
                            | SynPat.LongIdent(argPats = SynArgPats.Pats [ inner ]) -> literals inner
                            | SynPat.LongIdent(argPats = SynArgPats.Pats []) -> 1
                            | _ -> 0

                        literals p)
                    >= 2
                    ->
                    yield expr, subject
                | _ -> ()
        ]

    candidates
    |> List.choose (fun (matchExpr, subject) ->
        // the subject's slot
        let start =
            match analysis.Classify(fileName, subject) with
            | [ FromSlot slot ] -> Some slot
            | _ -> None

        match start with
        | None -> None
        | Some start when reported |> Seq.exists (List.exists (fun s -> sameSymbol s.Symbol start.Symbol)) -> None
        | Some start ->
            let c = closure analysis start
            reported.Add c.Slots

            match c.Failure with
            | Some _ -> None
            | None ->
                // this file reports the component only through its EARLIEST
                // consumer in compile order — one suggestion per component. A
                // closure that never met this match as a consumer (its subject
                // reached the slot some other way) has nothing to report
                let position (file: string, m: SynExpr) = world.FileOrder file, m.Range.StartLine

                let earliest =
                    match c.Consumers with
                    | [] -> None
                    | consumers -> Some(consumers |> List.minBy position)

                if
                    earliest
                    |> Option.forall (fun (file, m) -> not (file = fileName && sameSpan m.Range matchExpr.Range))
                then
                    None
                else
                    // the arms name the cases first, in the order the match reads
                    let allLiterals =
                        [
                            for text, _, via, _ in c.ArmLiterals -> text, via
                            for text, _, via, _ in c.Shadowed -> text, Some via
                            for text, _, via in c.Literals -> text, via
                            for _, _, text in c.Compares -> text, None
                        ]

                    let distinct = allLiterals |> List.map fst |> List.distinct

                    // the union's name, from the subject
                    let subjectName =
                        match subject with
                        | SynExpr.Ident id -> Some id.idText
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some (List.last ids).idText
                        | SynExpr.App _ -> applicationHead subject 0 |> Option.map (fun (id, _) -> id.idText)
                        | _ -> None

                    let armLiteralTexts =
                        (c.ArmLiterals |> List.map (fun (t, _, _, _) -> t))
                        @ (c.Shadowed |> List.map (fun (t, _, _, _) -> t))
                        |> Set.ofList

                    let anyGuarded = c.ArmLiterals |> List.exists (fun (_, _, _, g) -> g)

                    // a record field a serializer or a reflection fills: a
                    // construction with a literal is not its only source. The
                    // attributes say so, and so does the type's name as a type
                    // argument anywhere - `Deserialize<T>`, `typeof<T>`, any `X<T>`
                    let serialized =
                        c.Slots
                        |> List.exists (fun s ->
                            match s.Symbol with
                            | :? FSharpField as f ->
                                let attributeNames =
                                    try
                                        [
                                            yield! f.FieldAttributes |> Seq.map (fun a -> a.AttributeType.DisplayName)
                                            yield!
                                                f.PropertyAttributes |> Seq.map (fun a -> a.AttributeType.DisplayName)
                                            match f.DeclaringEntity with
                                            | Some e ->
                                                yield! e.Attributes |> Seq.map (fun a -> a.AttributeType.DisplayName)
                                            | None -> ()
                                        ]
                                    with _ -> // unreadable attributes count as a serializer's; fsharpanalyzer: ignore-line FR0055
                                        [ "CLIMutableAttribute" ]

                                let serializationAttribute =
                                    attributeNames
                                    |> List.exists (fun n ->
                                        let n =
                                            if n.EndsWith "Attribute" then
                                                n.Substring(0, n.Length - 9)
                                            else
                                                n

                                        n = "CLIMutable"
                                        || n = "DataContract"
                                        || n = "DataMember"
                                        || n = "Serializable"
                                        || n.StartsWith "Json"
                                        || n.StartsWith "Xml"
                                        || n.StartsWith "Bson"
                                        || n.StartsWith "Yaml"
                                        || n.StartsWith "Message")

                                let typeName =
                                    try
                                        f.DeclaringEntity |> Option.map (fun e -> e.DisplayName)
                                    with _ -> // fsharpanalyzer: ignore-line FR0055
                                        None

                                let asTypeArgument =
                                    match typeName with
                                    | None -> true
                                    | Some name ->
                                        let names (t: SynType) =
                                            match t with
                                            | SynType.LongIdent(SynLongIdent(id = ids)) ->
                                                (match List.tryLast ids with
                                                 | Some last -> last.idText = name
                                                 | None -> false)
                                            | _ -> false

                                        // a type argument of something that reads the type by
                                        // reflection - `Deserialize<T>`, `typeof<T>`, a `Json`/`Xml`
                                        // converter - not of a collection or a Task
                                        let reflective (head: string) =
                                            head = "typeof"
                                            || head = "typedefof"
                                            || head.Contains "Serializ"
                                            || head.Contains "Json"
                                            || head.Contains "Xml"
                                            || head.Contains "Bson"
                                            || head.Contains "Yaml"
                                            || head.Contains "Convert"
                                            || head.Contains "Reflect"

                                        world.SourceFiles
                                        |> List.exists (fun file ->
                                            match analysis.FileOf file with
                                            | None -> true // unreadable: assume the worst
                                            | Some(fi, _) ->
                                                fi.Exprs
                                                |> Array.exists (fun (_, e) ->
                                                    match e with
                                                    | SynExpr.TypeApp(expr = f; typeArgs = args) when
                                                        args |> List.exists names
                                                        ->
                                                        (match f with
                                                         | SynExpr.Ident id -> reflective id.idText
                                                         | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                                             ids |> List.exists (fun id -> reflective id.idText)
                                                         | _ -> true)
                                                    | _ -> false))

                                // ...and as a VALUE of the type, or a collection of it, handed
                                // to such a head with the type inferred: `JsonSerializer.Serialize
                                // items`, `items |> Serialize` - no type argument spells the
                                // record, yet every field is read by reflection
                                let asArgument =
                                    match typeName with
                                    | None -> true
                                    | Some _ ->
                                        let entityName =
                                            try
                                                f.DeclaringEntity |> Option.map OptionModule.fullNameOf
                                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                                None

                                        let rec mentions (t: FSharpType) =
                                            try
                                                let t = OptionModule.stripAbbreviations t

                                                (t.HasTypeDefinition
                                                 && Some(OptionModule.fullNameOf t.TypeDefinition) = entityName)
                                                || (t.GenericArguments |> Seq.exists mentions)
                                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                                true

                                        let reflective (head: string) =
                                            head.Contains "Serializ"
                                            || head.Contains "Json"
                                            || head.Contains "Xml"
                                            || head.Contains "Bson"
                                            || head.Contains "Yaml"
                                            || head.Contains "Convert"
                                            || head.Contains "Reflect"

                                        let reflectiveHead (e: SynExpr) =
                                            match e with
                                            | SynExpr.Ident id -> reflective id.idText
                                            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                                ids |> List.exists (fun id -> reflective id.idText)
                                            | SynExpr.TypeApp(expr = SynExpr.Ident id) -> reflective id.idText
                                            | SynExpr.TypeApp(
                                                expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
                                                ids |> List.exists (fun id -> reflective id.idText)
                                            | _ -> false

                                        // the argument's parts: a tuple's elements, a paren's inside
                                        let rec parts (e: SynExpr) =
                                            match e with
                                            | SynExpr.Paren(expr = inner) -> parts inner
                                            | SynExpr.Tuple(exprs = es) -> es |> List.collect parts
                                            | _ -> [ e ]

                                        let ofRecordType (file: string) (e: SynExpr) =
                                            let id =
                                                match e with
                                                | SynExpr.Ident id -> Some id
                                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                                    List.tryLast ids
                                                | _ -> None

                                            // a value's own type, a function's or property's result,
                                            // a field's type: what the expression IS
                                            match id |> Option.bind (world.SymbolAt file) with
                                            | Some u ->
                                                (match u.Symbol with
                                                 | :? FSharpMemberOrFunctionOrValue as v ->
                                                     mentions v.FullType || mentions (Text.resultTypeOf v)
                                                 | :? FSharpField as fld ->
                                                     (try
                                                         mentions fld.FieldType
                                                      with _ -> // fsharpanalyzer: ignore-line FR0055
                                                          true)
                                                 | _ -> false)
                                            | None -> false

                                        entityName.IsSome
                                        && world.SourceFiles
                                           |> List.exists (fun file ->
                                               match analysis.FileOf file with
                                               | None -> true
                                               | Some(fi, _) ->
                                                   // the head of an application chain and every
                                                   // argument along it: `Serialize options value`
                                                   let rec chain (e: SynExpr) (args: SynExpr list) =
                                                       match e with
                                                       | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) ->
                                                           chain f (a :: args)
                                                       | head -> head, args

                                                   fi.Exprs
                                                   |> Array.exists (fun (_, e) ->
                                                       match e with
                                                       // `x |> Serialize`
                                                       | SynExpr.App(
                                                           funcExpr = SynExpr.App(
                                                               isInfix = true
                                                               funcExpr = IdentName "op_PipeRight"
                                                               argExpr = lhs)
                                                           argExpr = f) when reflectiveHead f ->
                                                           parts lhs |> List.exists (ofRecordType file)
                                                       | SynExpr.App(isInfix = false) ->
                                                           let head, args = chain e []

                                                           reflectiveHead head
                                                           && args
                                                              |> List.collect parts
                                                              |> List.exists (ofRecordType file)
                                                       | _ -> false))

                                serializationAttribute || asTypeArgument || asArgument
                            | _ -> false)

                    let signatureBound =
                        c.Slots
                        |> List.exists (fun s ->
                            try
                                Text.hasSignatureFile s.Symbol.DeclarationLocation.Value.FileName
                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                true)

                    let isExported =
                        c.Slots
                        |> List.exists (fun s ->
                            exported world.InternalsVisible s.Symbol
                            || exported world.InternalsVisible (analysis.OwnerOf s))

                    // An exported slot whose callers the host cannot all see keeps
                    // its public signature behind an ADAPTER: the function's body
                    // moves to a private twin typed with the union, and a wrapper
                    // of the old name and shape maps at the edge - a parameter
                    // through the union's `OfString` (whose unknown-value arm is the
                    // match's own catch-all, so unknown input behaves as before), a
                    // return through `string` / `Result.mapError string` - under a
                    // TODO saying so. Callers in this compilation move to the twin;
                    // everyone else keeps calling the wrapper.
                    let ownFile (file: string) = world.FileOrder file < Int32.MaxValue

                    let adapters: Adapter list option =
                        if not (isExported && not world.ScopeOpen) then
                            Some []
                        else
                            let owners =
                                c.Slots
                                |> List.choose (fun s ->
                                    let owner = analysis.OwnerOf s

                                    if
                                        exported world.InternalsVisible owner
                                        || exported world.InternalsVisible s.Symbol
                                    then
                                        Some(s, owner)
                                    else
                                        None)

                            // a field, or a module-level value, has no edge to adapt at
                            if
                                owners
                                |> List.exists (fun (s, owner) ->
                                    s.Kind = "field" || (s.Kind = "value" && sameSymbol owner s.Symbol))
                            then
                                None
                            else
                                owners
                                |> List.groupBy (fun (_, owner) -> OptionModule.fullNameOf owner)
                                |> List.map (fun (_, group) ->
                                    let owner = snd group.Head

                                    let paramSlots =
                                        group |> List.filter (fun (s, _) -> s.Kind = "value") |> List.map fst

                                    let returnSlot =
                                        group
                                        |> List.tryPick (fun (s, _) -> if s.Kind = "return" then Some s else None)

                                    analysis.AdapterFor(
                                        owner,
                                        paramSlots,
                                        returnSlot,
                                        c.Consumers,
                                        c.CatchAlls,
                                        ownFile
                                    ))
                                |> List.fold
                                    (fun acc a ->
                                        match acc, a with
                                        | Some acc, Some a -> Some(a :: acc)
                                        | _ -> None)
                                    (Some [])

                    // every slot's declaration file must be readable: the
                    // annotations and the union go there
                    let declFiles =
                        c.Slots
                        |> List.choose (fun s ->
                            try
                                s.Symbol.DeclarationLocation |> Option.map (fun r -> r.FileName, r)
                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                None)

                    // the set has to be DISCRIMINATED somewhere: two literals the
                    // arms name, not merely two literals that flow into a value a
                    // `Some ex` passes on whole (a path, a message)
                    // ...and PRODUCED somewhere: a set the arms alone spell, with no
                    // call site and no producer in sight, is a function nothing calls
                    // - or one called from where the host cannot see (prismatic's
                    // `Logging.log level`, matched on four literals and never called)
                    if
                        distinct.Length < 2
                        || armLiteralTexts.Count < 2
                        || c.Literals.IsEmpty
                        || subjectName.IsNone
                        || signatureBound
                        || serialized
                        || adapters.IsNone
                        || declFiles.Length <> c.Slots.Length
                        || declFiles |> List.exists (fun (f, _) -> (analysis.FileOf f).IsNone)
                    then
                        None
                    else
                        // names: the union's, and one case per literal
                        let baseName = pascal subjectName.Value

                        // a field's second choice carries its record's name
                        let ownerPrefixed =
                            match start.Symbol with
                            | :? FSharpField as f ->
                                try
                                    f.DeclaringEntity |> Option.map (fun e -> e.DisplayName + baseName)
                                with _ -> // fsharpanalyzer: ignore-line FR0055
                                    None
                            | _ -> None

                        let unionName =
                            [ Some baseName; ownerPrefixed; Some(baseName + "Kind") ]
                            |> List.choose id
                            |> List.tryFind (fun n ->
                                (not (world.TypeNames.Contains n || introduced.Contains n)) && n <> "")

                        unionName |> Option.iter (introduced.Add >> ignore)

                        let caseNames =
                            distinct
                            |> List.map (fun text ->
                                // a literal that came through a constant is
                                // named after the constant
                                let viaConstant =
                                    allLiterals
                                    |> List.tryPick (fun (t, via) ->
                                        match via with
                                        | Some(_, id) when t = text -> Some(pascal id.idText)
                                        | _ -> None)

                                text,
                                (match viaConstant with
                                 | Some n -> Some n
                                 | None -> caseNameOf text))

                        // two literals Pascal-casing runs together (`a-b`, `a b`) keep
                        // their own text behind backticks, which are distinct by
                        // construction
                        let caseNames =
                            caseNames
                            |> List.map (fun (text, name) ->
                                match name with
                                | Some n when caseNames |> List.filter (fun (_, m) -> m = Some n) |> List.length > 1 ->
                                    text, backticked text
                                | _ -> text, name)

                        let caseOf (text: string) =
                            caseNames |> List.tryPick (fun (t, n) -> if t = text then n else None)

                        let namesValid =
                            unionName.IsSome
                            && caseNames |> List.forall (fun (_, n) -> n.IsSome)
                            && (caseNames |> List.choose snd |> List.distinct |> List.length) = caseNames.Length

                        if not namesValid then
                            None
                        else
                            let unionName = unionName.Value

                            // the union goes above the earliest participating
                            // declaration in compile order
                            let insertion =
                                declFiles
                                |> List.choose (fun (f, r) ->
                                    analysis.FileOf f
                                    |> Option.bind (fun (fi, fs) ->
                                        // the innermost let or type declaration holding
                                        // it: beside the declaration, inside its module
                                        fi.Decls
                                        |> Array.filter (fun (_, d) ->
                                            Range.rangeContainsRange d.Range r
                                            && (match d with
                                                | SynModuleDecl.Let _
                                                | SynModuleDecl.Types _ -> true
                                                | _ -> false))
                                        |> Array.sortByDescending (fun (path, _) -> path.Length)
                                        |> Array.tryHead
                                        |> Option.map (fun (path, d) -> f, fs, d, modulePathOf path)))
                                |> List.sortBy (fun (f, _, d, _) -> world.FileOrder f, d.Range.StartLine)
                                |> List.tryHead

                            match insertion with
                            | None -> None
                            | Some(unionFile, unionSource, decl, unionModule) ->
                                // above the declaration's own `//` comments too
                                let commentAbove (n: int) =
                                    n > 1
                                    && (let t = (unionSource.GetLineString(n - 2)).TrimStart()
                                        t.StartsWith "//" || t.StartsWith "[<")

                                let rec retreatLine line =
                                    if commentAbove line then retreatLine (line - 1) else line

                                let line = retreatLine decl.Range.StartLine

                                let column =
                                    let t = unionSource.GetLineString(decl.Range.StartLine - 1)
                                    t.Length - t.TrimStart().Length

                                let pad = String(' ', column)

                                // how a file names the union
                                let qualifierIn (file: string) (sitePath: SyntaxNode list) =
                                    match analysis.FileOf file with
                                    | None -> String.concat "." (unionModule @ [ unionName ])
                                    | Some(fi, _) ->
                                        let site = modulePathOf sitePath
                                        let opens = opensOf fi

                                        let prefixLength (p: string list) =
                                            if
                                                p.Length <= unionModule.Length && List.take p.Length unionModule = p
                                            then
                                                p.Length
                                            else
                                                0

                                        let known =
                                            [
                                                // inside the module, or a parent of it
                                                for k in 0 .. site.Length -> prefixLength (List.take k site)
                                                for o in opens -> prefixLength o
                                            ]
                                            |> List.max

                                        String.concat "." (List.skip known unionModule @ [ unionName ])

                                let edits = ResizeArray<Edit>()

                                let edit (file: string) (r: range) (replacement: string) =
                                    match analysis.FileOf file with
                                    | Some(_, fs) ->
                                        edits.Add
                                            {
                                                Range = r
                                                Original = textOfRange fs r
                                                Replacement = replacement
                                            }
                                    | None -> ()

                                // the module a range sits in: the ancestors of the innermost
                                // declaration holding it carry the module and namespace nodes
                                let pathOf (file: string) (r: range) =
                                    match analysis.FileOf file with
                                    | Some(fi, _) ->
                                        fi.Decls
                                        |> Array.filter (fun (_, d) -> Range.rangeContainsRange d.Range r)
                                        |> Array.sortByDescending (fun (path, _) -> path.Length)
                                        |> Array.tryHead
                                        |> Option.map (fun (path, d) -> SyntaxNode.SynModule d :: path)
                                        |> Option.defaultValue []
                                    | None -> []

                                // the constants that keep their name in the union's
                                // ToString: module-level, in the union's file and its
                                // module, above it — a nested module's constant of the
                                // same bare name would resolve to the outer one there
                                let constantText (text: string) =
                                    allLiterals
                                    |> List.tryPick (fun (t, via) ->
                                        match via with
                                        | Some(f, id) when
                                            t = text
                                            && String.Equals(
                                                IO.Path.GetFullPath f,
                                                IO.Path.GetFullPath unionFile,
                                                StringComparison.OrdinalIgnoreCase
                                            )
                                            && id.idRange.EndLine < line
                                            && modulePathOf (pathOf unionFile id.idRange) = unionModule
                                            ->
                                            Some id.idText
                                        | _ -> None)
                                    |> Option.defaultValue (quote text)

                                // the union is visible wherever a slot it types is, and no
                                // wider: a private type in an internal function's signature
                                // is an error, and a public type on a library that the rule
                                // added without --api-changes would widen the API by itself.
                                // Parameters and locals take their owner's visibility; a
                                // component spread over files is internal at least, since
                                // `private` is the file's
                                let unionModifier =
                                    let ranks =
                                        c.Slots
                                        |> List.map (fun s ->
                                            let owner =
                                                match s.Symbol with
                                                | :? FSharpMemberOrFunctionOrValue as v when
                                                    not v.IsModuleValueOrMember
                                                    ->
                                                    analysis.OwnerOf s
                                                | sym -> sym

                                            accessibilityRank owner)

                                    let widest = if ranks.IsEmpty then 2 else List.max ranks

                                    let files =
                                        declFiles |> List.map (fun (f, _) -> f.ToLowerInvariant()) |> List.distinct

                                    match (if files.Length > 1 then max widest 1 else widest) with
                                    | 0 -> "private "
                                    | 1 -> "internal "
                                    | _ -> ""

                                let unionText =
                                    String.concat
                                        "\n"
                                        [
                                            $"{pad}[<RequireQualifiedAccess>]"
                                            $"{pad}type {unionModifier}{unionName} ="
                                            for text in distinct do
                                                $"{pad}    | {(caseOf text).Value}"
                                            ""
                                            $"{pad}    override this.ToString() ="
                                            $"{pad}        match this with"
                                            for text in distinct do
                                                $"{pad}        | {unionName}.{(caseOf text).Value} -> {constantText text}"
                                            // the parse an adapter needs: every case, then the
                                            // catch-all the match had, verbatim
                                            match adapters.Value |> List.tryPick (fun a -> a.OfString) with
                                            | Some(binder, clauseLines) ->
                                                ""
                                                $"{pad}    static member OfString({binder}: string) ="
                                                $"{pad}        match {binder} with"

                                                for text in distinct do
                                                    $"{pad}        | {constantText text} -> {unionName}.{(caseOf text).Value}"

                                                for l in clauseLines do
                                                    $"{pad}        {l}"
                                            | None -> ()
                                            ""
                                            ""
                                        ]

                                edits.Add
                                    {
                                        Range = Range.mkRange unionFile (Position.mkPos line 0) (Position.mkPos line 0)
                                        Original = ""
                                        Replacement = unionText
                                    }

                                // literal sources, arms and comparisons become cases
                                for text, r, _ in c.Literals do
                                    edit
                                        r.FileName
                                        r
                                        $"{qualifierIn r.FileName (pathOf r.FileName r)}.{(caseOf text).Value}"

                                for text, r, _, _ in c.ArmLiterals do
                                    edit
                                        r.FileName
                                        r
                                        $"{qualifierIn r.FileName (pathOf r.FileName r)}.{(caseOf text).Value}"

                                for text, r, _, _ in c.Shadowed do
                                    edit
                                        r.FileName
                                        r
                                        $"{qualifierIn r.FileName (pathOf r.FileName r)}.{(caseOf text).Value}"

                                for file, r, text in c.Compares do
                                    edit file r $"{qualifierIn file (pathOf file r)}.{(caseOf text).Value}"

                                for file, r, text in c.Rewrites do
                                    edit file r text

                                // annotations
                                let mutable annotationsOk = true

                                for slot in c.Slots do
                                    match slot.Symbol.DeclarationLocation with
                                    | Some declRange ->
                                        match analysis.FileOf declRange.FileName with
                                        | Some(fi, _) ->
                                            let qualified =
                                                qualifierIn declRange.FileName (pathOf declRange.FileName declRange)

                                            match slot.Kind with
                                            | "field" ->
                                                let field =
                                                    fi.Decls
                                                    |> Array.tryPick (fun (_, d) ->
                                                        match d with
                                                        | SynModuleDecl.Types(typeDefns = defns) ->
                                                            defns
                                                            |> List.tryPick (fun (SynTypeDefn(typeRepr = repr)) ->
                                                                match repr with
                                                                | SynTypeDefnRepr.Simple(
                                                                    simpleRepr = SynTypeDefnSimpleRepr.Record(
                                                                        recordFields = fields)) ->
                                                                    fields
                                                                    |> List.tryPick
                                                                        (fun (SynField(fieldType = t; idOpt = id)) ->
                                                                            match id with
                                                                            | Some id when
                                                                                sameSpan id.idRange declRange
                                                                                ->
                                                                                Some t
                                                                            | _ -> None)
                                                                | _ -> None)
                                                        | _ -> None)

                                                match field |> Option.bind stringTypeIn with
                                                | Some t -> edit declRange.FileName t.Range qualified
                                                | None -> annotationsOk <- false
                                            | "return" ->
                                                match bindingOf fi declRange with
                                                | Some(SynBinding(returnInfo = Some(SynBindingReturnInfo(typeName = t))),
                                                       _) ->
                                                    match stringTypeIn t with
                                                    | Some st -> edit declRange.FileName st.Range qualified
                                                    | None -> annotationsOk <- false
                                                | Some _ -> ()
                                                | None -> annotationsOk <- false
                                            | _ ->
                                                // a typed pattern around the name
                                                match patAt fi declRange with
                                                | Some(SyntaxNode.SynPat(SynPat.Typed(targetType = t)) :: _, _) ->
                                                    match stringTypeIn t with
                                                    | Some st -> edit declRange.FileName st.Range qualified
                                                    | None -> annotationsOk <- false
                                                | Some _ -> ()
                                                | None -> ()
                                        | None -> annotationsOk <- false
                                    | None -> annotationsOk <- false

                                // catch-alls: dead ones go, live ones stay. A catch-all is dead
                                // when every case it could still meet has an arm of its own: for
                                // a wrapped slot, `| _` also stands for None or an Ok, so it
                                // goes only when that case has its arm too; `| Some _` and
                                // `| Error _` cover the string-carrying case alone
                                let dead (file: string) (m: SynExpr) (whole: bool) =
                                    match m with
                                    | SynExpr.Match(clauses = clauses) ->
                                        let emptyCaseNamed =
                                            clauses
                                            |> List.exists (fun (SynMatchClause(pat = p)) ->
                                                let rec empty (p: SynPat) =
                                                    match p with
                                                    | SynPat.LongIdent(
                                                        longDotId = SynLongIdent(id = [ ctor ])
                                                        argPats = SynArgPats.Pats []) ->
                                                        analysis.IsCoreCase(file, ctor)
                                                    | SynPat.LongIdent(
                                                        longDotId = SynLongIdent(id = [ ctor ])
                                                        argPats = SynArgPats.Pats [ _ ]) ->
                                                        analysis.IsOkCase(file, ctor)
                                                    | SynPat.Paren(pat = inner) -> empty inner
                                                    | _ -> false

                                                empty p)

                                        let armsHere =
                                            clauses
                                            |> List.collect (fun (SynMatchClause(pat = p)) ->
                                                let rec texts (p: SynPat) =
                                                    match p with
                                                    | SynPat.Const(SynConst.String(text = t), _) -> [ t ]
                                                    | SynPat.Or(lhsPat = a; rhsPat = b) -> texts a @ texts b
                                                    | SynPat.Paren(pat = inner) -> texts inner
                                                    // `Some "a"`, `Error "a"`: the literal inside
                                                    | SynPat.LongIdent(argPats = SynArgPats.Pats [ inner ]) ->
                                                        texts inner
                                                    | SynPat.Named _
                                                    | SynPat.LongIdent(argPats = SynArgPats.Pats []) ->
                                                        // a constant, or the shadowing bug: whatever the
                                                        // arms read at this range
                                                        (c.Shadowed
                                                         |> List.choose (fun (t, r, _, _) ->
                                                             if sameSpan r p.Range then Some t else None))
                                                        @ (c.ArmLiterals
                                                           |> List.choose (fun (t, r, _, _) ->
                                                               if sameSpan r p.Range then Some t else None))
                                                    | _ -> []

                                                texts p)
                                            |> Set.ofList

                                        not anyGuarded
                                        && distinct |> List.forall armsHere.Contains
                                        && (start.Wrap = Plain || not whole || emptyCaseNamed)
                                    | _ -> false

                                let mutable catchAllsOk = true

                                for file, m, clause, _, whole in c.CatchAlls do
                                    if dead file m whole then
                                        match analysis.FileOf file with
                                        | Some(_, fs) ->
                                            match clauseLines fs clause, world.File file with
                                            | Some(first, last), Some(tree, _) ->
                                                let column =
                                                    let t = fs.GetLineString(first - 1)
                                                    t.Length - t.TrimStart().Length

                                                let kept = keptComments tree fs first last column

                                                // whole lines; the file's last line takes the
                                                // line break before it instead of one after
                                                if last >= fs.GetLineCount() then
                                                    let r =
                                                        Range.mkRange
                                                            file
                                                            (Position.mkPos
                                                                (first - 1)
                                                                (fs.GetLineString(first - 2)).Length)
                                                            (Position.mkPos last (fs.GetLineString(last - 1)).Length)

                                                    edit
                                                        file
                                                        r
                                                        (kept |> List.map (fun l -> "\n" + l) |> String.concat "")
                                                else
                                                    let r =
                                                        Range.mkRange
                                                            file
                                                            (Position.mkPos first 0)
                                                            (Position.mkPos (last + 1) 0)

                                                    edit
                                                        file
                                                        r
                                                        (kept |> List.map (fun l -> l + "\n") |> String.concat "")
                                            | _ -> catchAllsOk <- false
                                        | None -> catchAllsOk <- false

                                // a live named catch-all carries the union now, so
                                // every use of its name must be one the union
                                // serves without an edit; a dead one goes with its
                                // clause, uses and all
                                let rec nullPattern (p: SynPat) =
                                    match p with
                                    | SynPat.Null _ -> true
                                    | SynPat.Paren(pat = inner) -> nullPattern inner
                                    | _ -> false

                                let liveNamesOk =
                                    c.CatchAlls
                                    |> List.forall (fun (file, m, clause, bound, whole) ->
                                        let (SynMatchClause(pat = p)) = clause

                                        let liveIsFine =
                                            match bound |> Option.bind slotOf with
                                            | Some slot ->
                                                analysis.Sinks slot
                                                |> List.forall (fun s ->
                                                    match s with
                                                    | Print -> true
                                                    | _ -> false)
                                            | None -> bound.IsNone

                                        dead file m whole
                                        // a `| null ->` arm the proof leaves live has no
                                        // spelling on the union
                                        || (not (nullPattern p) && liveIsFine))

                                // the adapters: the twin, the wrapper, the callers that move
                                for a in adapters.Value do
                                    let qualified = qualifierIn a.File (pathOf a.File a.Head.idRange)
                                    edit a.File a.Head.idRange $"private {a.Twin}"

                                    let arguments =
                                        a.Parameters
                                        |> List.map (fun (name, adapted) ->
                                            if adapted then $"({qualified}.OfString {name})" else name)
                                        |> String.concat " "

                                    let mapping =
                                        match a.ReturnWrap with
                                        | Some Plain -> " |> string"
                                        | Some Wrapped -> " |> Option.map string"
                                        | Some WrappedResult -> " |> Result.mapError string"
                                        | None -> ""

                                    let body =
                                        String.concat
                                            "\n"
                                            [
                                                $"{a.Pad}// TODO: consider changing the API to {qualified} and removing this mapping"
                                                $"{a.Pad}let {a.Name} {a.ParameterText}{a.ReturnText} ="
                                                $"{a.Pad}    {a.Twin} {arguments}{mapping}"
                                            ]

                                    // on lines of its own after the binding, or appended to a
                                    // last line without a line break
                                    let wrapper = if a.End.Column = 0 then $"\n{body}\n" else "\n\n" + body

                                    edits.Add
                                        {
                                            Range = Range.mkRange a.File a.End a.End
                                            Original = ""
                                            Replacement = wrapper
                                        }

                                    for file, r in a.OwnCalls do
                                        edit file r a.Twin

                                // with an adapter in play, the compilation's own files are
                                // the whole of the change: everyone else keeps the wrapper
                                let edits =
                                    if adapters.Value.IsEmpty then
                                        edits
                                    else
                                        ResizeArray(edits |> Seq.filter (fun e -> ownFile e.Range.FileName))

                                if not (annotationsOk && catchAllsOk && liveNamesOk) then
                                    None
                                else
                                    // one edit per range
                                    let distinctEdits =
                                        edits
                                        |> Seq.distinctBy (fun e ->
                                            e.Range.FileName,
                                            e.Range.StartLine,
                                            e.Range.StartColumn,
                                            e.Range.EndLine,
                                            e.Range.EndColumn)
                                        |> List.ofSeq

                                    Some
                                        {
                                            Name = unionName
                                            Range = matchExpr.Range
                                            Literals = distinct
                                            Exported = isExported
                                            ShadowedConstants =
                                                c.Shadowed |> List.map (fun (_, _, _, n) -> n) |> List.distinct
                                            Reshaped =
                                                c.Slots
                                                |> List.choose (fun s ->
                                                    match s.Kind with
                                                    | "return" -> Some s.Symbol.DisplayName
                                                    | "value" ->
                                                        let owner = analysis.OwnerOf s

                                                        if sameSymbol owner s.Symbol then
                                                            None
                                                        else
                                                            Some owner.DisplayName
                                                    | _ -> None)
                                                |> List.distinct
                                            Edits = distinctEdits
                                        })
