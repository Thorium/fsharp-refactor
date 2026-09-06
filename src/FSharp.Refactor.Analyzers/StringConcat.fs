/// Refactoring: a `+` chain mixing string literals and string values is an
/// interpolated string.
///
///     "Hello " + name + "!"       →  $"Hello {name}!"
///     prefix + ": " + x.Label     →  $"{prefix}: {x.Label}"
///
/// Safety rules:
///   - every operand is a regular string literal, or an identifier/dotted
///     path that resolves (typed check results) to System.String — any
///     other operand shape leaves the chain alone, so a custom (+) can
///     never be rewritten
///   - at least one literal and one non-literal (an all-literal chain is a
///     different simplification; a literal-free chain gains nothing), and at
///     least three operands — a two-term `path + ".bak"` reads fine as it is
///   - a literal containing `{`, `}`, or `%` leaves the chain alone: the
///     doubled escapes an interpolated string would need (`{{`, `%%`) read
///     worse than the concatenation they replace
///
/// Performance note: F# 8+ lowers a specifier-free interpolation with
/// string-typed holes — the only shape this rule emits — to a single n-ary
/// String.Concat, so the rewrite never routes through String.Format and is
/// equal to or cheaper than the pairwise `+` chain it replaces.
module FSharp.Refactor.StringConcat

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The String.Concat spelling of the same chain, for editors that
        /// offer both. Every operand is PROVEN a string here, so the two are
        /// exactly equivalent; the interpolation stays the primary because it
        /// reads better, and at the rule's 1–2 hole cap the compiler turns it
        /// into the same String.Concat call anyway.
        ConcatAlternative: string option
    }

/// One operand of the chain: literal source text (flagged verbatim when it
/// was an @-string) or an interpolation hole.
type private Piece =
    | Lit of text: string * verbatim: bool
    | Hole of string
    /// A hole spelled `%s{x}`: the `+` was what typed `x` as a string (an
    /// unannotated parameter), and a plain hole would let it generalise —
    /// against a signature file that is FS0034 (the F# compiler's
    /// `qualifiedMangledNameOfTyconRef tcref nm`). `%s` keeps the constraint.
    | TypedHole of string

/// The parameters bound WITHOUT an annotation by the bindings and lambdas
/// around a node: names whose string type may come from the chain alone.
let private unannotatedParameters (path: SyntaxNode list) =
    let bare (p: SynPat) =
        match p with
        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
        | SynPat.Paren(SynPat.Named(ident = SynIdent(ident = id)), _) -> Some id.idText
        | _ -> None

    path
    |> List.collect (fun node ->
        match node with
        | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats pats))) ->
            pats |> List.choose bare
        | SyntaxNode.SynExpr(SynExpr.Lambda(parsedData = Some(pats, _))) -> pats |> List.choose bare
        | _ -> [])
    |> Set.ofList

/// Left-to-right operands of a `+` chain.
[<TailCall>]
let rec private collectOperands (acc: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Addition"; argExpr = lhs); argExpr = rhs) ->
        collectOperands (rhs :: acc) lhs
    | last -> last :: acc

/// Does the identifier resolve to a System.String value or property?
let private resolvesToString (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    let isStringType (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t
            t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.String"
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            isStringType (
                try
                    value.ReturnParameter.Type
                with _ ->
                    value.FullType
            )
        // record fields resolve as FSharpField, not as a value
        | :? FSharpField as field -> isStringType field.FieldType
        | _ -> false
    | None -> false

/// Literal source text with the surrounding quotes stripped (a verbatim
/// literal's `@` included), or None when the interpolated context would
/// force awkward `{{`/`%%` escapes.
let private spliceableLiteral (verbatim: bool) (literalSource: string) =
    let prefix = if verbatim then 2 else 1
    let inner = literalSource.Substring(prefix, literalSource.Length - prefix - 1)

    if inner.Contains '{' || inner.Contains '}' || inner.Contains '%' then
        None
    else
        Some inner

/// True when the walker node is an operand of an enclosing `+`, i.e. an
/// inner node of a chain the outermost visit already handles.
let private isOperandOfPlus (path: SyntaxNode list) =
    match path with
    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = IdentName "op_Addition")) :: _ -> true
    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Addition"))) :: _ -> true
    | _ -> false

/// Find rewritable concatenation chains. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for path, expr in index.Exprs do
              match expr with
              | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent opId; argExpr = _); argExpr = _) when
                  opId.idText = "op_Addition"
                  && not (isOperandOfPlus path)
                  // string + translates in queries; String.Concat may not
                  && not (insideQuotedCode path)
                  && isSingleLine expr.Range
                  ->
                  let operands = collectOperands [] expr

                  // cheap syntactic pre-gates first: three or more operands
                  // (a two-term `path + ".bak"` reads fine as it is), with a
                  // string literal among them — only then pay for typed
                  // symbol resolution on the operands and the operator
                  let hasStringLiteral =
                      operands
                      |> List.exists (fun operand ->
                          match operand with
                          | SynExpr.Const(SynConst.String(_, (SynStringKind.Regular | SynStringKind.Verbatim), _), _) ->
                              true
                          | _ -> false)

                  if List.length operands >= 3 && hasStringLiteral then
                      let pieces =
                          operands
                          |> List.map (fun operand ->
                              match operand with
                              | SynExpr.Const(SynConst.String(_, SynStringKind.Regular, _), _) ->
                                  spliceableLiteral false (textOfRange source operand.Range)
                                  |> Option.map (fun t -> Lit(t, false))
                              | SynExpr.Const(SynConst.String(_, SynStringKind.Verbatim, _), _) ->
                                  spliceableLiteral true (textOfRange source operand.Range)
                                  |> Option.map (fun t -> Lit(t, true))
                              | SynExpr.Ident id when resolvesToString check source id ->
                                  // an unannotated parameter the chain alone
                                  // typed as a string: a plain hole would let
                                  // it generalise (FS0034 against a signature
                                  // file, the F# compiler), and a `%s` hole
                                  // would leave the String.Concat fast path for
                                  // the printf machinery — so the chain stays
                                  if (unannotatedParameters path).Contains id.idText then
                                      None
                                  else
                                      Some(Hole(textOfRange source operand.Range))
                              | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                  not ids.IsEmpty && resolvesToString check source (List.last ids)
                                  ->
                                  Some(Hole(textOfRange source operand.Range))
                              | _ -> None)

                      // at most TWO holes: the F# compiler turns small
                      // interpolations into String.Concat, but past that
                      // part count it emits the String.Format path —
                      // measured, a 3-hole interpolation runs 4.9x slower
                      // with 2.3x the allocation of the + chain it would
                      // replace, and a + chain of strings is already one
                      // String.Concat call. Readability must not tax the
                      // customer's hot path.
                      let holeCount =
                          pieces
                          |> List.sumBy (fun p ->
                              match p with
                              | Some(Hole _)
                              | Some(TypedHole _) -> 1
                              | _ -> 0)

                      let hasHole = holeCount >= 1 && holeCount <= 2

                      // a shadowed (+) can have arbitrary semantics; the
                      // typed operator gate still guards the fix, it just
                      // runs last
                      // a verbatim piece anywhere makes the whole result a
                      // verbatim interpolation ($@"..."), which is only sound
                      // when every REGULAR piece is escape-free — a `\n` or
                      // `\"` spliced into verbatim context would go literal
                      let anyVerbatim =
                          pieces
                          |> List.exists (fun p ->
                              match p with
                              | Some(Lit(_, true)) -> true
                              | _ -> false)

                      let regularsSafeForVerbatim =
                          pieces
                          |> List.forall (fun p ->
                              match p with
                              | Some(Lit(text, false)) -> not (text.Contains '\\')
                              | _ -> true)

                      if
                          pieces |> List.forall Option.isSome
                          && hasHole
                          && (not anyVerbatim || regularsSafeForVerbatim)
                          && OptionModule.resolvesToCoreOperator check source opId
                      then
                          let body =
                              pieces
                              |> List.choose id
                              |> List.map (fun piece ->
                                  match piece with
                                  | Lit(text, _) -> text
                                  | Hole text -> "{" + text + "}"
                                  | TypedHole text -> "%s{" + text + "}")
                              |> String.concat ""

                          let concatAlternative =
                              // `String` alone binds to FSharp.Core's module
                              // without `open System`; qualify when the file
                              // does not open it
                              let prefix = if opensSystemNamespace source then "" else "System."

                              let args =
                                  operands
                                  |> List.map (fun operand -> textOfRange source operand.Range)
                                  |> String.concat ", "

                              Some $"{prefix}String.Concat({args})"

                          { Range = expr.Range
                            OriginalText = textOfRange source expr.Range
                            ReplacementText = if anyVerbatim then $"$@\"{body}\"" else $"$\"{body}\""
                            ConcatAlternative = concatAlternative }
              | _ -> () ]
