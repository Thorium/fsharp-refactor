/// Refactoring: extract a `when` guard into a partial active pattern.
///
///     match x with                       let private (|IsEven|_|) input =
///     | n when isEven n -> ...      →        if isEven input then Some input else None
///     | n -> ...                         ...
///                                        match x with
///                                        | IsEven n -> ...
///                                        | n -> ...
///
/// The active pattern is inserted immediately before the enclosing
/// module-level declaration, so the guard function must be in scope there.
///
/// Safety rules:
///   - the guard must be exactly `f var` where `var` is the clause's bound
///     variable and `f` is a plain identifier or dotted path
///   - a single lowercase identifier `f` is rejected when the enclosing
///     declaration appears to bind it locally (let/fun/for/pattern binding —
///     checked conservatively on the declaration text), because the generated
///     binding would sit outside that scope; a dotted `Module.func` must
///     start with an uppercase segment
///   - skipped when the file already contains an active pattern of the same
///     name
module FSharp.Refactor.ActivePattern

open System
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The generated active-pattern name, e.g. "IsEven".
        PatternName: string
        /// Zero-width range at the insertion point (start of the enclosing declaration).
        InsertRange: range
        /// Text to insert: the pattern binding, a newline, and re-indentation.
        InsertText: string
        /// Range of `var when guard` inside the clause.
        ClauseRange: range
        OriginalClauseText: string
        /// Replacement, e.g. "IsEven n".
        ClauseText: string
    }

[<return: Struct>]
let private (|GuardFunction|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident ident when ident.idText.Length > 0 && Char.IsLower ident.idText.[0] ->
        ValueSome(ident.idText, e, false)
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
        ids.Length >= 2
        && (List.head ids).idText.Length > 0
        && Char.IsUpper (List.head ids).idText.[0]
        ->
        ValueSome((List.last ids).idText, e, true)
    | _ -> ValueNone

/// Conservative check for the enclosing declaration locally binding `name`:
/// let/use bindings, lambda parameters, for-loop variables, or a match
/// pattern binding it directly after `|`.
let private locallyBound (declText: string) (name: string) =
    // identifierPattern, not \b: F# names may end in a prime, where \b
    // finds no boundary
    let n = identifierPattern name

    [ $@"let[^\n=]*{n}"
      $@"use[^\n=]*{n}"
      $@"fun[^\n>]*{n}"
      $@"for\s+{n}"
      $@"\|\s*{n}\s*(->|when)" ]
    |> List.exists (fun pattern -> Regex.IsMatch(declText, pattern))

let private capitalize (name: string) =
    string (Char.ToUpperInvariant name.[0]) + name.Substring 1

/// The generated pattern's `input` parameter, annotated when it must be.
/// The original guard `Path.IsPathRooted p` infers from the match variable;
/// the extracted pattern's `input` has no such context, and a .NET method
/// group with overloads (IsPathRooted takes string OR ReadOnlySpan<char>)
/// then fails resolution — found live on Fuuga. An F# function infers
/// fine; a member gets its resolved parameter type spelled out; an
/// unresolvable guard skips the suggestion.
let private inputParameter (check: FSharpCheckFileResults) (source: ISourceText) (fnExpr: SynExpr) : string voption =
    let lastIdent =
        match fnExpr with
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    match lastIdent with
    | None -> ValueNone
    | Some ident ->
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as value ->
                try
                    if not value.IsMember then
                        ValueSome "input"
                    else
                        let t = value.CurriedParameterGroups.[0].[0].Type
                        ValueSome $"(input: {t.Format symbolUse.DisplayContext})"
                with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                    ValueNone
            | _ -> ValueNone
        | None -> ValueNone

/// Find `when` guards of the form `f var` that can become active patterns.
/// Requires typed check results for the guard's parameter type.
/// `structForm`: FSharp.Core 6 or newer, where `[<return: Struct>]` exists;
/// an older FSharp.Core (the TypeProviders SDK pins 4.7) gets the option-
/// returning pattern, which every FSharp.Core compiles.
let find
    (structForm: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    // only consulted when a candidate guard is found, which is rare
    let fileText =
        lazy
            ([ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ]
             |> String.concat "\n")

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.Match(clauses = clauses)
                | SynExpr.MatchBang(clauses = clauses)
                | SynExpr.MatchLambda(matchClauses = clauses) ->
                    // only plain module-level lets: inserting before a type
                    // declaration (a guard inside a member) would reference
                    // member parameters that are out of scope there, and a
                    // `let` directly under a namespace is not even legal
                    let enclosingDecl =
                        path
                        |> List.tryPick (fun node ->
                            match node with
                            | SyntaxNode.SynModule decl -> Some decl
                            | _ -> None)
                        |> Option.bind (fun decl ->
                            match decl with
                            | SynModuleDecl.Let _ -> Some decl
                            | _ -> None)

                    // the column its sibling declarations start at: the first
                    // declaration of the same module body
                    let contextColumn =
                        path
                        |> List.tryPick (fun node ->
                            match node with
                            | SyntaxNode.SynModule(SynModuleDecl.NestedModule(decls = first :: _)) ->
                                Some first.Range.StartColumn
                            | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(decls = first :: _)) ->
                                Some first.Range.StartColumn
                            | _ -> None)

                    match enclosingDecl with
                    | None -> ()
                    | Some decl ->
                        // extracted only when a candidate clause is found
                        let declText = lazy (textOfRange source decl.Range)

                        for SynMatchClause(pat = pat; whenExpr = whenExpr; resultExpr = body) in clauses do
                            match pat, whenExpr with
                            | SynPat.Named(ident = SynIdent(ident = var)),
                              Some(SynExpr.App(
                                  funcExpr = GuardFunction(fnName, fnExpr, isDotted); argExpr = SynExpr.Ident arg) as guard) when
                                arg.idText = var.idText
                                && isSingleLine guard.Range
                                && (isDotted || not (locallyBound declText.Value fnName))
                                ->
                                let patternName = capitalize fnName

                                // the generated binding is spliced at the
                                // decl's start, so that position must open
                                // its line (a one-line nested module or
                                // `;;`-chained decl would corrupt the line)
                                let ownLine =
                                    decl.Range.StartColumn = 0
                                    || (source.GetLineString(decl.Range.StartLine - 1))
                                        .Substring(0, decl.Range.StartColumn)
                                        .Trim() = ""

                                let aligned = contextColumn |> Option.forall (fun c -> c = decl.Range.StartColumn)

                                if ownLine && aligned && not (fileText.Value.Contains $"(|{patternName}|") then
                                    match inputParameter check source fnExpr with
                                    | ValueNone -> ()
                                    | ValueSome inputParam ->
                                        let fnText = textOfRange source fnExpr.Range
                                        let indent = String(' ', decl.Range.StartColumn)

                                        // new code gets the best form directly:
                                        // private (no new API surface), inline
                                        // (tiny body, FS1113-safe because the
                                        // pattern is as private as any guard it
                                        // references), and struct-returning (no
                                        // allocation per match attempt)
                                        let binding =
                                            if structForm then
                                                sprintf
                                                    "[<return: Struct>]\n%slet inline private (|%s|_|) %s =\n%s    if %s input then ValueSome input else ValueNone"
                                                    indent
                                                    patternName
                                                    inputParam
                                                    indent
                                                    fnText
                                            else
                                                sprintf
                                                    "let inline private (|%s|_|) %s =\n%s    if %s input then Some input else None"
                                                    patternName
                                                    inputParam
                                                    indent
                                                    fnText

                                        let insertAt =
                                            Range.mkRange decl.Range.FileName decl.Range.Start decl.Range.Start

                                        let clauseRange =
                                            Range.mkRange pat.Range.FileName pat.Range.Start guard.Range.End

                                        // a variable the body never reads becomes `_`:
                                        // `| c when Char.IsDigit c -> Decimal` bound `c` only
                                        // for the guard, and `| IsDigit c -> Decimal` left
                                        // it unused — FS1182, an error under
                                        // FsAutoComplete's warnings-as-errors
                                        let bodyReads =
                                            Regex.IsMatch(
                                                textOfRange source body.Range,
                                                $@"\b{Regex.Escape var.idText}\b"
                                            )

                                        let binder = if bodyReads then var.idText else "_"

                                        // a blank line separates the new definition
                                        // from the declaration it lands above — glued
                                        // together, fantomas --check rejects the file.
                                        // A guard under `#if` yields a definition under
                                        // the same `#if`; a directive has to open its
                                        // own line, so that form is inserted at column
                                        // 0 of the decl's line, ahead of its
                                        // indentation, which the generated first line
                                        // then carries itself
                                        let insertRange, insertText =
                                            match conditionToKeep source clauseRange.StartLine insertAt.StartLine with
                                            | Some condition ->
                                                Range.mkRange
                                                    decl.Range.FileName
                                                    (Position.mkPos decl.Range.StartLine 0)
                                                    (Position.mkPos decl.Range.StartLine 0),
                                                $"#if {condition}\n{indent}{binding}\n#endif\n\n"
                                            | None -> insertAt, $"{binding}\n\n{indent}"

                                        suggestions.Add
                                            { PatternName = patternName
                                              InsertRange = insertRange
                                              InsertText = insertText
                                              ClauseRange = clauseRange
                                              OriginalClauseText = textOfRange source clauseRange
                                              ClauseText = $"{patternName} {binder}" }
                            | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    // two guards using the same function would both insert the same pattern
    // definition; keep only the first suggestion per generated name
    suggestions |> Seq.distinctBy (fun s -> s.PatternName) |> List.ofSeq
