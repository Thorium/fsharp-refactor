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
///    A lambda handed to a List/Seq/Array function runs once per element,
///    so `xs |> List.map (fun x -> Regex.IsMatch(x, "asdf"))` is the same
///    loop (LoopPerf.loopBinders decides, shared with the other loop rules).
///
///    The instance name is derived from the pattern text; when the name is
///    taken, the required `open` is missing, or the call shape is unusual,
///    the hint is emitted without a fix.
///
/// 3. A Regex CONSTRUCTED with a literal pattern inside such a loop is the
///    same cost spelled differently — FSharp.Analyzers.SDK's
///    `expandMultiProperties` built `Regex(";([a-z,A-Z,0-9,_,-]*)=")` inside
///    a `List.map` lambda and its author hoisted it by hand. The fix moves
///    the construction, source text and all, to a module binding above the
///    enclosing declaration and leaves whatever followed it in place:
///
///        let private azAZ09Regex = Regex(";([a-z,A-Z,0-9,_,-]*)=")
///        ...
///        let regex = azAZ09Regex
///        let splits = regex.Split(v)
///
///    Only a literal pattern with, at most, options spelled from
///    `RegexOptions.X` flags qualifies: a local in the options could vary
///    per element. Where this rule declines it stays silent and FR0037
///    notes the construction; where it fixes, that note stands down.
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
    /// Regex constructed inside a loop; always carries a fix (a declined
    /// construction is FR0037's note, not this rule's).
    | HoistConstruction

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

/// A dotted spelling of the Regex type: `System.Text.RegularExpressions.Regex`
/// or any shorter suffix of it that an `open` of the prefix would make valid.
/// Anything else ending in `.Regex` could be a function of that name in
/// some module, and hoisting a call is not the same as hoisting a
/// construction.
let private isRegexTypePath (ids: Ident list) =
    let full = "System.Text.RegularExpressions.Regex"
    let text = identText ids
    ids.Length >= 2 && (text = full || full.EndsWith("." + text))

/// `Regex(...)` / `Regex "..."` / `new Regex(...)` in the bare spelling, or
/// under the RegularExpressions path — the LoopPerf.ExpensiveCtor shapes,
/// narrowed to this one type. Yields the constructor argument and whether
/// the spelling is qualified: a bare `Regex` is the constructor only under
/// the open, where the dotted one resolves anywhere.
[<return: Struct>]
let private (|RegexConstruction|_|) (e: SynExpr) =
    match e with
    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = [ id ])); expr = arg) when id.idText = "Regex" ->
        ValueSome(false, arg)
    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when isRegexTypePath ids ->
        ValueSome(true, arg)
    | SynExpr.App(isInfix = false; funcExpr = IdentName "Regex"; argExpr = arg) -> ValueSome(false, arg)
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        isRegexTypePath ids
        ->
        ValueSome(true, arg)
    | _ -> ValueNone

/// An options argument built only from `RegexOptions.X` flags joined by
/// `|||`: the one shape that is the same on every iteration. A local name
/// in there could be a different value per element, and a hoisted binding
/// would freeze the first.
let rec private constantOptions (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
        ids.Length >= 2 && ids.[ids.Length - 2].idText = "RegexOptions"
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_BitwiseOr"; argExpr = left)
        argExpr = right) -> constantOptions left && constantOptions right
    | SynExpr.Paren(expr = inner) -> constantOptions inner
    | _ -> false

/// The constructor / method arguments as a list, tuple or single.
let private argsOf (arg: SynExpr) =
    match stripParens arg with
    | SynExpr.Tuple(exprs = es) -> es
    | single -> [ single ]

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

/// A pattern that is PURE literal text - no metacharacters at all, anchors
/// included. `literalPattern` above tolerates a leading `^` / trailing `$`
/// because StartsWith/EndsWith carry that meaning; a plain string Replace
/// carries none, so an anchored pattern is not the same operation.
let private plainLiteral (pattern: string) : string option =
    if
        pattern.Length = 0
        || pattern |> Seq.exists regexMetaChars.Contains
        || pattern |> Seq.exists (fun c -> c = '"' || Char.IsControl c)
    then
        None
    else
        Some pattern

/// A replacement string `String.Replace` would read differently from
/// `Regex.Replace`, which treats `$` as SUBSTITUTION syntax:
///
///     Regex.Replace("xxabcdyy", "abcd", "$&!")  =  "xxabcd!yy"
///     "xxabcdyy".Replace("abcd", "$&!")         =  "xx$&!yy"
///
/// measured, along with `$$` meaning a literal `$` to one and two characters
/// to the other. Any `$` at all disqualifies the swap.
let private plainReplacement (replacement: string) : string option =
    if
        replacement.Contains '$'
        || replacement |> Seq.exists (fun c -> c = '"' || Char.IsControl c)
    then
        None
    else
        Some replacement

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

/// The module-level `let` a node sits under, when there is one: the
/// hoisted binding lands above it. Innermost first, so under a nested
/// module it is that module's own declaration, where the same opens hold.
let private enclosingLet (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynModule(SynModuleDecl.Let _ as decl) -> Some decl
        | _ -> None)

/// The line a hoisted binding goes on: the declaration's first line,
/// extended upward over the plain `//` comment block that describes it —
/// contiguous comment lines at the declaration's own column, crossing
/// blank lines only when another comment line sits above them
/// (TaskStateMachine's extendUpOverComments, plus the column guard). The
/// `///` doc block needs no such help: a declaration's range already starts
/// at its XML doc, so the range start is above it. A `// what f does` line
/// is outside the range, and a binding inserted at the range start would
/// wedge itself between that comment and the function it describes.
/// `floorLine` is the previous declaration's last line, so the walk never
/// claims a comment that trails the declaration above.
let private hoistLine (source: ISourceText) (floorLine: int) (column: int) (startLine: int) =
    let line n = source.GetLineString(n - 1)
    let isBlank (l: string) = String.IsNullOrWhiteSpace l

    let isComment (l: string) =
        l.Length - l.TrimStart().Length = column && l.TrimStart().StartsWith "//"

    let mutable top = startLine
    let mutable probe = startLine - 1

    while probe > floorLine && (isComment (line probe) || isBlank (line probe)) do
        if isComment (line probe) then
            top <- probe

        probe <- probe - 1

    top

/// The name a hoist's insertion text declares, for the collision check
/// between two hoists in one file.
let private hoistedNameIn = Regex(@"let private (\w+) =", RegexOptions.Compiled)

/// Find literal-pattern IsMatch calls and loop-resident static Regex calls.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()
    let index = AstIndex.ofTree parseTree

    let hasRegexOpen =
        lazy
            (index.Decls
             |> Array.exists (fun (_, decl) ->
                 match decl with
                 | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
                     (ids |> List.map (fun i -> i.idText) |> String.concat ".") = "System.Text.RegularExpressions"
                 | _ -> false))

    let fileText =
        lazy
            ([ for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i ]
             |> String.concat "\n")

    // the last line of whatever declaration ends above this one (0 at the
    // top of the file): the comment walk's floor
    let floorAbove (decl: SynModuleDecl) =
        index.Decls
        |> Array.fold
            (fun acc (_, d) ->
                if d.Range.EndLine < decl.Range.StartLine then
                    max acc d.Range.EndLine
                else
                    acc)
            0

    // the insertion edit for `let private <name> = <rhs>` above `decl`,
    // indented to it; a call under `#if` yields a hoisted instance under
    // the same `#if`
    let hoistInsert (decl: SynModuleDecl) (originLine: int) (name: string) (rhs: string) =
        let indent = String(' ', decl.Range.StartColumn)

        let line =
            hoistLine source (floorAbove decl) decl.Range.StartColumn decl.Range.StartLine

        let at = Position.mkPos line decl.Range.StartColumn
        let insertAt = Range.mkRange decl.Range.FileName at at

        let binding =
            let bare = sprintf "let private %s = %s" name rhs

            match conditionToKeep source originLine insertAt.StartLine with
            | Some condition -> $"#if {condition}\n{bare}\n#endif"
            | None -> bare

        insertAt, "", $"{binding}\n{indent}"

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | StaticRegexCall(methodName, arg) ->
                    let args = argsOf arg

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

                    // rule 1b: Replace(input, "literal", "literal") is a plain
                    // string Replace - no engine, no pattern parse. Three
                    // arguments only: a RegexOptions or MatchEvaluator
                    // argument is a different operation entirely
                    match methodName, args with
                    | "Replace", [ input; StringLiteral pattern; StringLiteral replacement ] when
                        isSingleLine input.Range
                        ->
                        match plainLiteral pattern, plainReplacement replacement with
                        | Some literal, Some literalReplacement ->
                            let text =
                                sprintf
                                    "%s.Replace(\"%s\", \"%s\")"
                                    (argumentText source input)
                                    literal
                                    literalReplacement

                            suggestions.Add
                                { Range = expr.Range
                                  OriginalText = textOfRange source expr.Range
                                  Kind = RegexSuggestionKind.StringOperation
                                  Edits = [ expr.Range, textOfRange source expr.Range, text ] }
                        | _ -> ()
                    | _ -> ()

                    // rule 2: a static Regex call with a literal pattern inside
                    // a loop - or a collection-function lambda, which runs
                    // once per element - re-parses the pattern per iteration
                    let patternArg =
                        match args with
                        | [ _; (StringLiteral _ as p) ] -> Some p
                        | [ _; (StringLiteral _ as p); _ ] when methodName = "Replace" -> Some p
                        | _ -> None

                    match patternArg, LoopPerf.loopBinders path with
                    | Some patternExpr, ValueSome _ ->
                        let name =
                            match patternExpr with
                            | StringLiteral pattern -> nameFromPattern pattern
                            | _ -> "compiledRegex"

                        let edits =
                            match enclosingLet path with
                            | Some decl when
                                hasRegexOpen.Value
                                && (hoistableMethods.Contains methodName || methodName = "Replace")
                                && not (fileText.Value.Contains name)
                                ->
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
                                    [ hoistInsert
                                          decl
                                          expr.Range.StartLine
                                          name
                                          (sprintf "Regex %s" (textOfRange source patternExpr.Range))
                                      expr.Range, textOfRange source expr.Range, callReplacement ]
                            | _ -> []

                        suggestions.Add
                            { Range = expr.Range
                              OriginalText = textOfRange source expr.Range
                              Kind = RegexSuggestionKind.HoistFromLoop
                              Edits = edits }
                    | _ -> ()
                // rule 3: a Regex constructed inside a loop, pattern literal
                // and options constant. The construction's own source text
                // becomes the binding and its name takes the construction's
                // place; a `let regex = azAZ09Regex` left behind is a
                // harmless alias and `.Split(v)` after it still reads. A
                // construction spanning lines would carry its indentation
                // into the binding, so only a single-line one qualifies
                | RegexConstruction(qualified, arg) when isSingleLine expr.Range ->
                    let pattern =
                        match argsOf arg with
                        | [ StringLiteral pattern ] -> Some pattern
                        | [ StringLiteral pattern; options ] when constantOptions options -> Some pattern
                        | _ -> None

                    match pattern, enclosingLet path, LoopPerf.loopBinders path with
                    | Some pattern, Some decl, ValueSome _ when qualified || hasRegexOpen.Value ->
                        let name = nameFromPattern pattern

                        if not (fileText.Value.Contains name) then
                            suggestions.Add
                                { Range = expr.Range
                                  OriginalText = textOfRange source expr.Range
                                  Kind = RegexSuggestionKind.HoistConstruction
                                  Edits =
                                    [ hoistInsert decl expr.Range.StartLine name (textOfRange source expr.Range)
                                      expr.Range, textOfRange source expr.Range, name ] }
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree

    let all = List.ofSeq suggestions

    // a literal IsMatch in a loop produces both suggestions; the string
    // operation subsumes the hoisting advice. Two hoists deriving the same
    // NAME would collide (a static call and a construction of one pattern
    // spell different bindings under the same name), so only the first
    // keeps its fix - and a construction without a fix is not this rule's
    // to report, FR0037 notes it
    let seenNames = System.Collections.Generic.HashSet<string>()

    let hoistedName (s: Suggestion) =
        match s.Edits with
        | (_, _, insertText) :: _ ->
            let m = hoistedNameIn.Match insertText
            if m.Success then Some m.Groups.[1].Value else None
        | [] -> None

    all
    |> List.filter (fun s ->
        s.Kind = RegexSuggestionKind.StringOperation
        || all
           |> List.exists (fun o -> o.Kind = RegexSuggestionKind.StringOperation && o.Range = s.Range)
           |> not)
    |> List.choose (fun s ->
        match s.Kind, hoistedName s with
        | RegexSuggestionKind.HoistFromLoop, Some name when not (seenNames.Add name) -> Some { s with Edits = [] }
        | RegexSuggestionKind.HoistConstruction, Some name when not (seenNames.Add name) -> None
        | _ -> Some s)

/// The constructions rule 3 fixes, by range: FR0037 ("Regex built in a
/// loop") stands down on these, since the fix here already answers its
/// note. Every construction this rule declines - a pattern that is not a
/// literal, options naming a local, a taken name, a missing open - is
/// absent here and stays FR0037's to report.
let hoistedConstructions (parseTree: ParsedInput) (source: ISourceText) : range list =
    find parseTree source
    |> List.choose (fun s ->
        match s.Kind, s.Edits with
        | RegexSuggestionKind.HoistConstruction, _ :: _ -> Some s.Range
        | _ -> None)

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
