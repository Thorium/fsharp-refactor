/// Three smaller notes from the CA triage:
///
/// 1. Visible mutable module state (FR0062, CA2211): a non-private
///    module-level `let mutable` is a global variable every consumer can
///    write, with no thread safety and no change tracking.
///
/// 2. Culture-sensitive parsing (FR0067, CA1305): `DateTime.Parse s` and
///    `Double.Parse s` read differently under different server cultures
///    ("1,5" vs "1.5", day/month order); pass CultureInfo.InvariantCulture
///    (or the intended culture) explicitly.
///
/// 3. Duplicate enum values (FR0068, CA1069): two enum cases with the
///    same literal value are usually a copy-paste slip — comparisons and
///    ToString silently conflate them.
module FSharp.Refactor.MiscRules

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type MutableStateSuggestion = { Range: range; Name: string }

type CultureParseSuggestion =
    {
        Range: range
        /// e.g. "DateTime.Parse".
        CallName: string
        /// The argument-list edit adding an explicit culture: the range to
        /// replace and its replacement, parameterized by the culture NAME
        /// ("InvariantCulture" / "CurrentCulture"). The spelling adapts to
        /// the file: `CultureInfo.X` under an existing
        /// `open System.Globalization`, fully qualified otherwise.
        CultureFix: (string -> range * string * string) option
    }

type DuplicateEnumSuggestion =
    {
        Range: range
        CaseName: string
        /// The earlier case with the same value.
        OriginalName: string
    }

let private cultureSensitiveOwners =
    set [ "DateTime"; "DateTimeOffset"; "Double"; "Single"; "Decimal" ]

/// Find all three. Parse-only.
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    : MutableStateSuggestion list * CultureParseSuggestion list * DuplicateEnumSuggestion list =
    let index = AstIndex.ofTree parseTree
    let mutables = ResizeArray<MutableStateSuggestion>()
    let parses = ResizeArray<CultureParseSuggestion>()
    let enums = ResizeArray<DuplicateEnumSuggestion>()

    // FR0062: non-private module-level mutables outside private/internal
    // modules
    for path, decl in index.Decls do
        let moduleConfined =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynModule(SynModuleDecl.NestedModule(
                    moduleInfo = SynComponentInfo(accessibility = Some(SynAccess.Private _ | SynAccess.Internal _)))) ->
                    true
                | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(
                    accessibility = Some(SynAccess.Private _ | SynAccess.Internal _))) -> true
                | _ -> false)

        match decl with
        | SynModuleDecl.Let(bindings = bindings) when not moduleConfined ->
            for binding in bindings do
                // the accessibility of `let mutable private x` parses onto
                // the Named pattern, not the binding
                match binding with
                | SynBinding(
                    isMutable = true
                    accessibility = None
                    // both parse shapes of a lone binder: Named, and the
                    // no-argument LongIdent an UPPERCASE identifier takes —
                    // public mutable state is exactly where those live
                    headPat = (SynPat.Named(ident = SynIdent(ident = var); accessibility = None) | SynPat.LongIdent(
                        longDotId = SynLongIdent(id = [ var ]); argPats = SynArgPats.Pats []; accessibility = None))) ->
                    mutables.Add
                        { Range = var.idRange
                          Name = var.idText }
                | _ -> ()
        | _ -> ()

    // an existing open makes the short CultureInfo spelling resolve
    let globalizationOpened =
        index.Decls
        |> Array.exists (fun (_, d) ->
            match d with
            | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = [ s; g ]))) ->
                s.idText = "System" && g.idText = "Globalization"
            | _ -> false)

    let cultureSpelling (name: string) =
        if globalizationOpened then
            $"CultureInfo.{name}"
        else
            $"System.Globalization.CultureInfo.{name}"

    // inside `query { }` (or any quotation) the expression is TRANSLATED,
    // not run: a LINQ provider resolves method calls by signature, and the
    // two-argument Parse can turn a translatable call into a runtime
    // NotSupportedException that compiles clean. The whole suggestion
    // stands down there — the values belong to the database's type system,
    // where cultures do not exist.
    let translatedRanges =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = IdentName "query"; argExpr = SynExpr.ComputationExpr(expr = body)) ->
                Some body.Range
            | SynExpr.Quote(quotedExpr = q) -> Some q.Range
            | _ -> None)

    let inTranslatedContext (r: range) =
        translatedRanges |> Array.exists (fun z -> Range.rangeContainsRange z r)

    for _, e in index.Exprs do
        match e with
        // FR0067: single-argument Parse on culture-sensitive types
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) ->
            match List.rev ids with
            | parseId :: owner :: _ when
                parseId.idText = "Parse"
                && cultureSensitiveOwners.Contains owner.idText
                // inside a query/quotation the whole suggestion stands
                // down, note included: the expression belongs to the
                // database's type system, where cultures do not exist and
                // the only safe change is a human moving the parse out
                && not (inTranslatedContext e.Range)
                ->
                match stripParens arg with
                | SynExpr.Tuple _ -> () // culture already supplied
                | inner ->
                    // the culture edit: `Parse(s)` grows a second tuple
                    // element, a juxtaposed `Parse s` gains the parens too
                    let cultureFix =
                        if inTranslatedContext e.Range then
                            None
                        else
                            match arg with
                            | SynExpr.Paren _ ->
                                let at = Range.mkRange e.Range.FileName inner.Range.End inner.Range.End
                                Some(fun (culture: string) -> at, "", $", {cultureSpelling culture}")
                            | _ ->
                                let argText = textOfRange source arg.Range

                                Some(fun (culture: string) ->
                                    arg.Range, argText, $"({argText}, {cultureSpelling culture})")

                    parses.Add
                        { Range = e.Range
                          CallName = owner.idText + ".Parse"
                          CultureFix = cultureFix }
            | _ -> ()
        | _ -> ()

    // FR0068: duplicate literal enum values
    for _, decl in index.Decls do
        match decl with
        | SynModuleDecl.Types(typeDefns = defns) ->
            for SynTypeDefn(typeInfo = SynComponentInfo(attributes = typeAttrs); typeRepr = repr) in defns do
                match repr with
                // a [<Flags>] enum names bits, and one bit under two
                // names is how such tables are written (FCS's
                // ilnativeres.fs mirrors winnt.h: `MemProtected = 16384u |
                // NoDeferSpecExc = 16384u`) — not a slip
                | SynTypeDefnRepr.Simple(simpleRepr = SynTypeDefnSimpleRepr.Enum(cases = cases)) when
                    not (hasAttributeNamed "Flags" typeAttrs)
                    ->
                    let seen = System.Collections.Generic.Dictionary<string, string * int>()

                    // `Default = 0 | Text = 0`: a zero alias declared right
                    // beside its twin is a deliberate synonym (FCS's public
                    // FSharpTokenColorKind), not the copy-paste slip that
                    // lands far from the value it duplicates
                    let declaredAlias
                        (key: string)
                        (originalName: string)
                        (originalIndex: int)
                        (i: int)
                        (name: string)
                        =
                        key = "0"
                        && originalIndex = i - 1
                        && [ originalName; name ] |> List.exists (fun n -> n = "Default" || n = "None")

                    for i, SynEnumCase(ident = SynIdent(ident = caseId); valueExpr = valueExpr) in List.indexed cases do
                        // every integral spelling keys the same way: `16`,
                        // `0x10` and `16u` are one value (FCS's vendored
                        // ilnativeres.fs aliases its flags with `u` suffixes)
                        let key =
                            match valueExpr with
                            | SynExpr.Const(SynConst.Int32 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.Int64 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.Byte v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.SByte v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.Int16 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.UInt16 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.UInt32 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.UInt64 v, _) -> Some(string v)
                            | SynExpr.Const(SynConst.Char v, _) -> Some(string (int v))
                            | _ -> None

                        match key with
                        | Some k ->
                            match seen.TryGetValue k with
                            | true, (original, originalIndex) ->
                                if not (declaredAlias k original originalIndex i caseId.idText) then
                                    enums.Add
                                        { Range = caseId.idRange
                                          CaseName = caseId.idText
                                          OriginalName = original }
                            | _ -> seen.[k] <- (caseId.idText, i)
                        | None -> ()
                | _ -> ()
        | _ -> ()

    // FR0062 refinement: a public mutable ASSIGNED at most once in this
    // file — and never from itself — reads as the two legitimate patterns:
    // the poor-man's-DI seam a test assembly swaps (its writes live in
    // another project), or the set-once startup config. Neither has the
    // per-call churn the thread-safety note is about; repeated or
    // self-referential assignment (`x <- x + 1`) keeps the note.
    let assignments = System.Collections.Generic.Dictionary<string, int>()
    let selfReferential = System.Collections.Generic.HashSet<string>()

    for _, e in index.Exprs do
        match e with
        | SynExpr.LongIdentSet(SynLongIdent(id = ids), rhs, _) when not ids.IsEmpty ->
            let n = (List.last ids).idText

            assignments.[n] <-
                (match assignments.TryGetValue n with
                 | true, c -> c
                 | _ -> 0)
                + 1

            if System.Text.RegularExpressions.Regex.IsMatch(textOfRange source rhs.Range, identifierPattern n) then
                selfReferential.Add n |> ignore
        | _ -> ()

    let churningMutables =
        mutables
        |> Seq.filter (fun m ->
            (match assignments.TryGetValue m.Name with
             | true, c -> c
             | _ -> 0)
            >= 2
            || selfReferential.Contains m.Name)
        |> List.ofSeq

    churningMutables, List.ofSeq parses, List.ofSeq enums
