/// Refactoring (performance): simplify and speed up regular-expression use.
///
/// 1. A static Regex call whose pattern is a literal with no regex
///    metacharacters is a plain string operation (with a fix):
///
///        Regex.IsMatch(s, "^abc")   →  s.StartsWith "abc"
///
/// 2. A static Regex call with a literal pattern inside a loop re-parses the
///    pattern on every iteration. When the surroundings allow it, the fix
///    hoists a compiled-once instance above the enclosing declaration and
///    calls it instead:
///
///        let private asdfRegex = Regex "asdf"
///        ...
///        for line in lines do
///            if asdfRegex.IsMatch line then ...
///
///    The instance name is derived from the pattern text; when the name is
///    taken, the required `open` is missing, or the call shape is unusual,
///    the hint is emitted without a fix.
module FSharp.Refactor.RegexUsage

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text
open System.Text.RegularExpressions

[<RequireQualifiedAccess>]
type RegexSuggestionKind =
    /// Literal pattern rewritten to StartsWith/EndsWith/Contains.
    | StringOperation
    /// Static Regex call inside a loop; Edits may be empty (advice only).
    | HoistFromLoop

type Suggestion =
    {
        Range: range
        OriginalText: string
        Kind: RegexSuggestionKind
        /// Zero or more text edits ((range, original, replacement)).
        Edits: (range * string * string) list
    }

/// `Regex.<method>(...)` or `System.Text.RegularExpressions.Regex.<method>(...)`.
[<return: Struct>]
let private (|StaticRegexCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        ids.Length >= 2 && (ids.[ids.Length - 2]).idText = "Regex"
        ->
        ValueSome((List.last ids).idText, arg)
    | _ -> ValueNone

/// Any string literal, however it was written. `@"\d+"` is the ordinary way
/// to write a regex in F# — restricting this to plain literals quietly missed
/// most real patterns. Both consumers cope: the hoisted binding re-emits the
/// pattern's ORIGINAL source text, `@` and all, and the string-operation
/// rewrite already refuses anything carrying a quote, a control character or
/// a backslash, which is every case where the two spellings would differ.
[<return: Struct>]
let private (|StringLiteral|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.String(text,
                                    (SynStringKind.Regular | SynStringKind.Verbatim | SynStringKind.TripleQuote),
                                    _),
                    _) -> ValueSome text
    | _ -> ValueNone

/// Characters that carry meaning in a regex pattern.
let private regexMetaChars =
    set [ '\\'; '.'; '*'; '+'; '?'; '('; ')'; '['; ']'; '{'; '}'; '|'; '^'; '$' ]

/// If the pattern is literal text with at most a leading `^` / trailing `$`,
/// return the string operation and the literal.
let private literalPattern (pattern: string) : (string * string) option =
    let anchoredStart = pattern.StartsWith '^'
    let anchoredEnd = pattern.EndsWith '$' && not (pattern.EndsWith "\\$")

    let core =
        pattern
            .Substring((if anchoredStart then 1 else 0))
            .Substring(
                0,
                pattern.Length
                - (if anchoredStart then 1 else 0)
                - (if anchoredEnd then 1 else 0)
            )

    if
        core.Length = 0
        || core |> Seq.exists regexMetaChars.Contains
        // the literal is re-emitted verbatim into a string: quotes and
        // control characters would need re-escaping
        || core |> Seq.exists (fun c -> c = '"' || Char.IsControl c)
    then
        None
    else
        match anchoredStart, anchoredEnd with
        | true, false -> Some("StartsWith", core)
        | false, true -> Some("EndsWith", core)
        | false, false -> Some("Contains", core)
        // fully anchored is an equality test; readers expect `=`, but the
        // culture-sensitivity question makes that a different rewrite — skip
        | true, true -> None

/// An identifier-friendly name derived from the pattern text.
let private nameFromPattern (pattern: string) =
    let letters =
        pattern |> Seq.filter Char.IsLetterOrDigit |> Seq.truncate 12 |> Seq.toArray

    if letters.Length = 0 || Char.IsDigit letters.[0] then
        "compiledRegex"
    else
        String(Char.ToLowerInvariant letters.[0] |> Array.singleton)
        + String(letters.[1..])
        + "Regex"

/// Methods whose static (input, pattern) overloads map onto an instance call.
let private hoistableMethods = set [ "IsMatch"; "Match"; "Matches"; "Split" ]

/// Find literal-pattern IsMatch calls and loop-resident static Regex calls.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let hasRegexOpen =
        lazy
            ((AstIndex.ofTree parseTree).Decls
             |> Array.exists (fun (_, decl) ->
                 match decl with
                 | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                     (ids |> List.map (fun i -> i.idText) |> String.concat ".") = "System.Text.RegularExpressions"
                 | _ -> false))

    let fileText =
        lazy
            ([ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ]
             |> String.concat "\n")

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | StaticRegexCall(methodName, arg) ->
                    let args =
                        match stripParens arg with
                        | SynExpr.Tuple(exprs = es) -> es
                        | single -> [ single ]

                    // rule 1: IsMatch(input, "literal") -> string operation
                    match methodName, args with
                    | "IsMatch", [ input; StringLiteral pattern ] when isSingleLine input.Range ->
                        match literalPattern pattern with
                        | Some(operation, literal) ->
                            let replacement =
                                sprintf "%s.%s \"%s\"" (argumentText source input) operation literal

                            suggestions.Add
                                { Range = expr.Range
                                  OriginalText = textOfRange source expr.Range
                                  Kind = RegexSuggestionKind.StringOperation
                                  Edits = [ expr.Range, textOfRange source expr.Range, replacement ] }
                        | None -> ()
                    | _ -> ()

                    // rule 2: a static Regex call with a literal pattern inside
                    // a loop re-parses the pattern per iteration
                    let patternArg =
                        match args with
                        | [ _; (StringLiteral _ as p) ] -> Some p
                        | [ _; (StringLiteral _ as p); _ ] when methodName = "Replace" -> Some p
                        | _ -> None

                    let insideLoop =
                        path
                        |> List.exists (fun node ->
                            match node with
                            | SyntaxNode.SynExpr(SynExpr.For _)
                            | SyntaxNode.SynExpr(SynExpr.ForEach _)
                            | SyntaxNode.SynExpr(SynExpr.While _) -> true
                            | _ -> false)

                    match patternArg with
                    | Some patternExpr when insideLoop ->
                        let enclosingLet =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynModule decl -> Some decl
                                | _ -> None)
                            |> Option.bind (fun decl ->
                                match decl with
                                | SynModuleDecl.Let _ -> Some decl
                                | _ -> None)

                        let name =
                            match patternExpr with
                            | StringLiteral pattern -> nameFromPattern pattern
                            | _ -> "compiledRegex"

                        let edits =
                            match enclosingLet with
                            | Some decl when
                                hasRegexOpen.Value
                                && (hoistableMethods.Contains methodName || methodName = "Replace")
                                && not (fileText.Value.Contains name)
                                ->
                                let indent = String(' ', decl.Range.StartColumn)

                                let insertAt = Range.mkRange decl.Range.FileName decl.Range.Start decl.Range.Start

                                // a call under `#if` yields a hoisted
                                // instance under the same `#if`
                                let binding =
                                    let bare =
                                        sprintf "let private %s = Regex %s" name (textOfRange source patternExpr.Range)

                                    match conditionToKeep source expr.Range.StartLine insertAt.StartLine with
                                    | Some condition -> $"#if {condition}\n{bare}\n#endif"
                                    | None -> bare

                                let callReplacement =
                                    match methodName, args with
                                    | "Replace", [ input; _; repl ] ->
                                        sprintf
                                            "%s.Replace(%s, %s)"
                                            name
                                            (textOfRange source input.Range)
                                            (textOfRange source repl.Range)
                                    | _, [ input; _ ] -> sprintf "%s.%s %s" name methodName (argumentText source input)
                                    | _ -> ""

                                if callReplacement = "" then
                                    []
                                else
                                    [ insertAt, "", $"{binding}\n{indent}"
                                      expr.Range, textOfRange source expr.Range, callReplacement ]
                            | _ -> []

                        suggestions.Add
                            { Range = expr.Range
                              OriginalText = textOfRange source expr.Range
                              Kind = RegexSuggestionKind.HoistFromLoop
                              Edits = edits }
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree

    let all = List.ofSeq suggestions

    // a literal IsMatch in a loop produces both suggestions; the string
    // operation subsumes the hoisting advice. Two hoists deriving the same
    // binding would collide, so only the first keeps its fix.
    let seenBindings = System.Collections.Generic.HashSet<string>()

    all
    |> List.filter (fun s ->
        s.Kind = RegexSuggestionKind.StringOperation
        || all
           |> List.exists (fun o -> o.Kind = RegexSuggestionKind.StringOperation && o.Range = s.Range)
           |> not)
    |> List.map (fun s ->
        match s.Kind, s.Edits with
        | RegexSuggestionKind.HoistFromLoop, (_, _, bindingText) :: _ when not (seenBindings.Add bindingText) ->
            { s with Edits = [] }
        | _ -> s)

// ---- FR0122: the pattern must compile ----

/// A literal pattern .NET's regex engine rejects is a GUARANTEED runtime
/// ArgumentException on first use — the one class of regex bug an
/// analyzer can prove. Construction only compiles the pattern (no input
/// runs), so checking is cheap and exact.
let findInvalidPatterns (parseTree: ParsedInput) : (range * string * string) list =
    let index = AstIndex.ofTree parseTree

    // the bare `Regex(...)` spelling is a constructor only under the open;
    // elsewhere it could be anything called Regex
    let regexOpened =
        index.Decls
        |> Array.exists (fun (_, decl) ->
            match decl with
            | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                (ids |> List.map (fun i -> i.idText) |> String.concat ".") = "System.Text.RegularExpressions"
            | _ -> false)

    // the options the call spells out, when they are literal flags: a
    // pattern that is valid only under IgnorePatternWhitespace or
    // ECMAScript must be compiled the way it will run
    let optionsOf (args: SynExpr list) =
        let rec names (e: SynExpr) =
            match e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2 && ids.[ids.Length - 2].idText = "RegexOptions"
                ->
                [ (List.last ids).idText ]
            | SynExpr.App(funcExpr = f; argExpr = a) -> names f @ names a
            | SynExpr.Paren(expr = inner) -> names inner
            | _ -> []

        args
        |> List.collect names
        |> List.fold
            (fun (acc: RegexOptions) name ->
                match Enum.TryParse<RegexOptions> name with
                | true, flag -> acc ||| flag
                | _ -> acc)
            RegexOptions.None

    let check (options: RegexOptions) (patternExpr: SynExpr) =
        match patternExpr with
        | StringLiteral pattern ->
            try
                Regex(pattern, options) |> ignore
                None
            with :? ArgumentException as ex ->
                Some(patternExpr.Range, pattern, ex.Message)
        | _ -> None

    let argsOf (arg: SynExpr) =
        match stripParens arg with
        | SynExpr.Tuple(exprs = es) -> es
        | single -> [ single ]

    [ for _, expr in index.Exprs do
          match expr with
          // Regex.IsMatch(input, pattern) and friends: pattern is arg 2
          | StaticRegexCall(methodName, arg) when
              (methodName = "IsMatch"
               || methodName = "Match"
               || methodName = "Matches"
               || methodName = "Replace"
               || methodName = "Split")
              ->
              match argsOf arg with
              | _ :: patternArg :: rest ->
                  match check (optionsOf rest) patternArg with
                  | Some bad -> bad
                  | None -> ()
              | _ -> ()
          // Regex(pattern) / new Regex(pattern): pattern is arg 1
          | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = tids)); expr = arg) when
              not tids.IsEmpty && (List.last tids).idText = "Regex"
              ->
              match argsOf arg with
              | first :: rest ->
                  match check (optionsOf rest) first with
                  | Some bad -> bad
                  | None -> ()
              | [] -> ()
          // the dotted spelling anywhere, the bare one under the open
          | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
              not ids.IsEmpty && (List.last ids).idText = "Regex"
              ->
              match argsOf arg with
              | first :: rest ->
                  match check (optionsOf rest) first with
                  | Some bad -> bad
                  | None -> ()
              | [] -> ()
          | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident ctor; argExpr = arg) when
              ctor.idText = "Regex" && regexOpened
              ->
              match argsOf arg with
              | first :: rest ->
                  match check (optionsOf rest) first with
                  | Some bad -> bad
                  | None -> ()
              | [] -> ()
          | _ -> () ]
