/// Helpers for turning FCS ranges back into source text.
/// All refactorings emit minimal range-based edits, so extracting the exact
/// original text of a sub-expression is the core primitive.
module FSharp.Refactor.Text

open FSharp.Compiler.Syntax
open FSharp.Compiler.SyntaxTrivia
open FSharp.Compiler.Text
open FSharp.Compiler.Tokenization
open System
open System.Collections.Generic
open System.IO
open System.Text.RegularExpressions

/// The type a use of `value` has as an expression: what it returns when
/// it is a function or member, the value's own type otherwise. FCS raises
/// on `ReturnParameter` for a plain value rather than answering, so the
/// fallback is the whole type - the same probe eight rules once spelled
/// out by hand.
let resultTypeOf (value: FSharp.Compiler.Symbols.FSharpMemberOrFunctionOrValue) =
    try
        value.ReturnParameter.Type
    with _ -> // FCS: a value has no return parameter; fsharpanalyzer: ignore-line FR0055
        value.FullType

/// The exact source text covered by a range.
let textOfRange (source: ISourceText) (r: range) : string =
    if r.StartLine = r.EndLine then
        source.GetLineString(r.StartLine - 1).Substring(r.StartColumn, r.EndColumn - r.StartColumn)
    else
        [
            for lineNumber in r.StartLine .. r.EndLine do
                let line = source.GetLineString(lineNumber - 1)

                if lineNumber = r.StartLine then
                    line.Substring r.StartColumn
                elif lineNumber = r.EndLine then
                    line.Substring(0, r.EndColumn)
                else
                    line
        ]
        |> String.concat "\n"

let isSingleLine (r: range) = r.StartLine = r.EndLine

/// A dotted identifier path as source text: [a; b] → "a.b".
let identText (ids: Ident list) =
    ids |> List.map (fun i -> i.idText) |> String.concat "."

/// True when a dotted path ends `owner.meth` — `String.Format`,
/// `Async.RunSynchronously` — without indexing into the ident list.
let pathEndsWith (owner: string) (meth: string) (ids: Ident list) =
    match List.rev ids with
    | m :: o :: _ -> m.idText = meth && o.idText = owner
    | _ -> false

/// Where a new attribute belongs on a declaration.
///
/// A declaration's range starts at its XML doc, so inserting at the range
/// start puts `[<Struct>]` ABOVE the `///` lines. That compiles, but the
/// attribute belongs against the thing it decorates, so skip the doc first.
/// Returns the position, whose column is also the indent to line up with.
let attributeInsertPos (source: ISourceText) (declRange: range) : pos =
    let isDocLine (n: int) =
        n <= source.GetLineCount()
        && (source.GetLineString(n - 1)).TrimStart().StartsWith "///"

    let rec advanceLine line =
        if isDocLine line then advanceLine (line + 1) else line

    let line = advanceLine declRange.StartLine

    let column =
        if line <= source.GetLineCount() then
            let text = source.GetLineString(line - 1)
            text.Length - text.TrimStart().Length
        else
            declRange.StartColumn

    Position.mkPos line column

/// One project file's parse artifacts, for the project-wide (API-changing)
/// rule variants: they read call sites out of files other than the one the
/// definition lives in.
type FileContext =
    {
        FileName: string
        Source: ISourceText
        ParseTree: ParsedInput
    }

/// True when any two of these ranges nest or coincide within one file.
///
/// A multi-edit suggestion is atomic — its definition edit and every
/// call-site edit apply together or not at all — so nested ranges make it
/// unappliable: splicing the outer one destroys or duplicates the inner.
/// `f (f (1, 2), 3)` is the shape that produces them.
let rangesNest (ranges: range list) =
    ranges
    |> List.indexed
    |> List.exists (fun (i, r) ->
        ranges
        |> List.skip (i + 1)
        |> List.exists (fun other ->
            r.FileName.Equals(other.FileName, StringComparison.OrdinalIgnoreCase)
            && (Range.rangeContainsRange r other || Range.rangeContainsRange other r)))

/// Strip redundant outer parens from an expression whose new context makes
/// them unnecessary (e.g. a lambda body inside our own parenthesized template).
[<TailCall>]
let rec stripParens (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner) -> stripParens inner
    | _ -> e

/// Expressions that need no parentheses when used as a pipe source or a
/// function argument.
let isAtomic (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.LongIdent _
    | SynExpr.Const _
    | SynExpr.Paren _
    | SynExpr.DotGet _ -> true
    // NOT a high-precedence application. `f(x)` and `X.Y(x)` carry
    // ExprAtomicFlag.Atomic, but F# still rejects them unparenthesised in
    // argument position: `isNull Environment.GetEnvironmentVariable("CI")`
    // is error FS0597, "this argument expression needs parentheses". A
    // corpus run over FSharp.Data caught FR0012 emitting exactly that.
    // Parenthesising is always semantically safe, so treat them as needing
    // it rather than trying to tell argument position from pipe source.
    | _ -> false

/// The expression's text, parenthesized unless it is atomic.
///
/// A call written in .NET style needs the parentheses moved rather than
/// added: F# brackets the whole application, so `f(x)` becomes `(f x)`
/// and not `(f(x))`. Only single, already-atomic arguments are moved —
/// a tuple `Path.Combine(a, b)` is the argument list and must keep its
/// parentheses, and `f (a + b)` would change meaning without them.
let atomicText (source: ISourceText) (e: SynExpr) =
    let text = textOfRange source e.Range

    if isAtomic e then
        text
    else
        match e with
        | SynExpr.App(flag = ExprAtomicFlag.Atomic; funcExpr = func; argExpr = SynExpr.Paren(expr = inner)) when
            isAtomic inner
            && (match inner with
                | SynExpr.Tuple _ -> false
                | _ -> true)
            ->
            $"({textOfRange source func.Range} {textOfRange source inner.Range})"
        | _ -> $"({text})"

/// The expression's text as a function argument: parenthesized unless atomic,
/// and always parenthesized when it starts with `-` (it would parse as
/// subtraction).
let argumentText (source: ISourceText) (e: SynExpr) =
    let text = textOfRange source e.Range

    if isAtomic e && not (text.StartsWith '-') then
        text
    else
        // shares atomicText's bracket placement: `f(x)` reads as `(f x)`
        atomicText source e

/// Pure atoms whose evaluation cannot run user code — safe to evaluate
/// eagerly where the original code evaluated them lazily. Empty collection
/// literals qualify; non-empty ones would evaluate their elements. Dotted
/// paths are deliberately excluded: `DateTime.Now` and friends are property
/// getters whose evaluation is observable.
let isPureAtom (e: SynExpr) =
    match e with
    | SynExpr.Ident _
    | SynExpr.Const _
    | SynExpr.Null _
    | SynExpr.ArrayOrList(exprs = []) -> true
    | _ -> false

/// FCS-version-independent view of a let/use/let!/use! expression. FCS
/// 43.12 packs the payload into the SynLetOrUse record (`SynExpr.LetOrUse
/// lou` + properties); 43.10 — the FCS stock Ionide's analyzer SDK 0.35
/// pairs with — spells the same fields tupled on the case. The anonymous
/// record keeps the 43.12 property spellings, so rule code written
/// against it compiles under both.
[<return: Struct>]
let (|LetOrUseE|_|) (e: SynExpr) =
#if ANALYZERS_SDK_0_35
    match e with
    | SynExpr.LetOrUse(isRecursive = isRecursive; isUse = isUse; isBang = isBang; bindings = bindings; body = body) ->
        ValueSome
            {|
                IsRecursive = isRecursive
                IsUse = isUse
                IsBang = isBang
                Bindings = bindings
                Body = body
                Range = e.Range
            |}
    | _ -> ValueNone
#else
    match e with
    | SynExpr.LetOrUse lou ->
        ValueSome
            {|
                IsRecursive = lou.IsRecursive
                IsUse = lou.IsUse
                IsBang = lou.IsBang
                Bindings = lou.Bindings
                Body = lou.Body
                Range = lou.Range
            |}
    | _ -> ValueNone
#endif

/// True when the expression is ordinary expression syntax that can be moved
/// into a lambda body. Computation-expression-only forms (`return e`,
/// `yield e`, `do! e`, `let! ...`) cannot.
let isPlainBody (e: SynExpr) =
    match e with
    | SynExpr.YieldOrReturn _
    | SynExpr.YieldOrReturnFrom _
    | SynExpr.DoBang _ -> false
    | LetOrUseE lou -> not lou.IsBang
    | _ -> true

/// An identifier expression, whether parsed as Ident or a single-segment
/// LongIdent (operators like `|>` come through as the latter).
[<return: Struct>]
let (|IdentName|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident ident -> ValueSome ident.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ ident ])) -> ValueSome ident.idText
    | _ -> ValueNone

/// Like IdentName, but yields the Ident itself (for symbol resolution).
[<return: Struct>]
let (|SingleIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident ident -> ValueSome ident
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ ident ])) -> ValueSome ident
    | _ -> ValueNone

/// True when the text ends in a printf format specifier whose leading `%`
/// is not itself escaped (`%%`) — the shape a typed interpolation hole has
/// in the literal part preceding its `{`.
let endsWithFormatSpecifier (text: string) =
    Regex.IsMatch(text, @"%[-+0# ]*[0-9]*(\.[0-9]+)?[a-zA-Z]$")
    && (let idx = text.LastIndexOf '%'
        let mutable run = 0
        let mutable i = idx - 1

        while i >= 0 && text.[i] = '%' do
            run <- run + 1
            i <- i - 1

        run % 2 = 0)

[<return: Struct>]
let (|BoolConst|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Bool b, _) -> ValueSome b
    | _ -> ValueNone

[<return: Struct>]
let (|UnitConst|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Unit, _) -> ValueSome()
    | _ -> ValueNone

[<return: Struct>]
let (|ZeroConst|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.Int32 0, _) -> ValueSome()
    | _ -> ValueNone

/// `lhs |> rhs` (the parsed shape of the infix pipe).
[<return: Struct>]
let (|PipeApp|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_PipeRight"; argExpr = lhs); argExpr = rhs) ->
        ValueSome(lhs, rhs)
    | _ -> ValueNone

/// A guard-free match clause's pattern and body.
let simpleClause (SynMatchClause(pat = pat; whenExpr = whenExpr; resultExpr = result)) =
    match whenExpr with
    | Some _ -> None
    | None -> Some(pat, result)

/// The name a case pattern binds: `v`, `(v)`, or None for `_`.
[<TailCall>]
let rec boundVar (arg: SynPat) =
    match arg with
    | SynPat.Named(ident = SynIdent(ident = v)) -> Some(Some v.idText)
    | SynPat.Wild _ -> Some None
    | SynPat.Paren(pat = inner) -> boundVar inner
    | _ -> None

/// Lambda parameter name for an optionally-bound variable.
let lambdaParam (boundVar: string option) = defaultArg boundVar "_"

/// Every name bound anywhere in a pattern (loop patterns, lambda
/// parameters, constructor arguments).
[<TailCall>]
let rec patBoundNamesLoop (acc: string list) (pending: SynPat list) =
    match pending with
    | [] -> acc
    | p :: rest ->
        let acc, next =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText :: acc, rest
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner)
            | SynPat.Paren(inner, _) -> acc, inner :: rest
            | SynPat.Tuple(elementPats = ps)
            | SynPat.ArrayOrList(elementPats = ps)
            | SynPat.Ands(pats = ps) -> acc, ps @ rest
            | SynPat.As(lhsPat = l; rhsPat = r)
            | SynPat.Or(lhsPat = l; rhsPat = r) -> acc, l :: r :: rest
            // `a :: rest` is its own node, not a LongIdent application - without
            // it the whole cons pattern bound nothing and its sub-patterns were
            // never reached
            | SynPat.ListCons(lhsPat = l; rhsPat = r) -> acc, l :: r :: rest
            // `{ Field = p }` binds through its field patterns
            | SynPat.Record(fieldPats = fields) ->
                acc, (fields |> List.map (fun (f: NamePatPairField) -> f.Pattern)) @ rest
            | SynPat.OptionalVal(ident = id) -> id.idText :: acc, rest
            // a no-argument lone identifier (the uppercase binder's parse
            // shape) BINDS the name — record it like Named
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                id.idText :: acc, rest
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> acc, ps @ rest
            // union-case fields named rather than positional -
            // `SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))` binds
            // `ids` exactly as a positional pattern would. Missing this made
            // every such binder invisible to callers that ask what a match arm
            // rebinds per iteration (LoopPerf.loopBinders, and so FR0102)
            | SynPat.LongIdent(argPats = SynArgPats.NamePatPairs(pats = ps)) ->
                acc, (ps |> List.map (fun (fieldPat: NamePatPairField) -> fieldPat.Pattern)) @ rest
            | _ -> acc, rest

        patBoundNamesLoop acc next

let patBoundNames (p: SynPat) : string list = patBoundNamesLoop [] [ p ]

/// True when the expression's source text can be inlined at an arbitrary
/// single-line expression position without changing how it parses. Anything
/// greedy enough to swallow following tokens (`else`, `then`, a pipeline
/// stage), or that needs `;`/`in` on one line, is rejected; parenthesized
/// expressions are always fine.
[<TailCall>]
let rec isSafeInline (e: SynExpr) : bool =
    match e with
    | SynExpr.Paren _ -> true
    | SynExpr.IfThenElse _
    | SynExpr.Match _
    | SynExpr.MatchLambda _
    | SynExpr.MatchBang _
    | SynExpr.Lambda _
    | SynExpr.LetOrUse _
    | SynExpr.Sequential _
    | SynExpr.TryWith _
    | SynExpr.TryFinally _
    | SynExpr.Do _
    | SynExpr.DoBang _
    | SynExpr.While _
    | SynExpr.For _
    | SynExpr.ForEach _ -> false
    // An application is only as safe as its rightmost part:
    // `f <| fun x -> x` ends in an unparenthesized lambda.
    | SynExpr.App(argExpr = arg) -> isSafeInline arg
    | SynExpr.Tuple(exprs = exprs) ->
        match exprs with
        | [] -> true
        | _ -> isSafeInline (List.last exprs)
    | SynExpr.Typed(expr = inner) -> isSafeInline inner
    | _ -> true

/// Does an attribute list carry an attribute with this (short) name?
/// Matches both `[<CustomOperation ...>]` and `[<CustomOperationAttribute ...>]`.
let hasAttributeNamed (name: string) (attrs: SynAttributes) =
    attrs
    |> List.exists (fun attrList ->
        attrList.Attributes
        |> List.exists (fun a ->
            match a.TypeName with
            | SynLongIdent(id = ids) when not ids.IsEmpty ->
                let t = (List.last ids).idText
                t = name || t = name + "Attribute"
            | _ -> false))

/// Member names of the computation-expression builder protocol. A type
/// carrying two or more of these is a CE builder, and F# requires builder
/// members to be instance members (the builder is a value).
let ceProtocolNames =
    set
        [
            "Bind"
            "Return"
            "ReturnFrom"
            "Yield"
            "YieldFrom"
            "Zero"
            "Combine"
            "Delay"
            "Run"
            "For"
            "While"
            "TryWith"
            "TryFinally"
            "Using"
            "Source"
            "MergeSources"
            "BindReturn"
        ]

/// The name of a `member this.Name ...` definition, if that is its shape.
let memberDefnName (m: SynMemberDefn) =
    match m with
    | SynMemberDefn.Member(memberDefn = SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)))) when
        not ids.IsEmpty
        ->
        Some (List.last ids).idText
    | _ -> None

/// Types whose instance-ness is a contract rather than a choice: CE builders
/// (two or more protocol members, or any [<CustomOperation>]), and subclasses
/// (`inherit ...`), whose members frameworks like SignalR dispatch on
/// instances by name.
let instanceIsContract (members: SynMemberDefn list) =
    let ceMembers =
        members
        |> List.choose memberDefnName
        |> List.filter ceProtocolNames.Contains
        |> List.distinct

    ceMembers.Length >= 2
    || members
       |> List.exists (fun m ->
           match m with
           | SynMemberDefn.ImplicitInherit _
           | SynMemberDefn.Inherit _ -> true
           | SynMemberDefn.Member(memberDefn = SynBinding(attributes = attrs)) ->
               hasAttributeNamed "CustomOperation" attrs
           | _ -> false)

/// Does the range cover a line carrying a compiler directive
/// (#if/#else/#endif)? The parse tree only sees the active branch, so a fix
/// replacing such a range would splice the directive structure apart and
/// leave code that no longer compiles under the other defines. Read from
/// the lines, not the parser's trivia: the trivia belongs to a tree this
/// guard is not handed, and a registry by file name is process-wide state
/// that another parse of the same name overwrites. The scan's one error is
/// a `#if`-looking line inside a string or a comment, and it errs toward
/// standing down.
let spansDirective (source: ISourceText) (r: range) =
    seq { r.StartLine .. r.EndLine }
    |> Seq.exists (fun line ->
        let text = (source.GetLineString(line - 1)).TrimStart()

        text.StartsWith "#if" || text.StartsWith "#else" || text.StartsWith "#endif")

/// The indentations of the lines continuing the construct on `line`: every
/// code line below it standing deeper than `line` itself, up to the first
/// that does not (that one closes every context `line` opened). Blank and
/// comment-only lines carry no offside meaning and are passed over.
/// `lineAt` is 1-based, like a range's lines.
let private continuationIndents (lineAt: int -> string) (lineCount: int) (line: int) =
    let indentOf (text: string) = text.Length - text.TrimStart().Length
    let own = indentOf (lineAt line)
    let mutable l = line + 1
    let mutable inside = true

    [
        while inside && l <= lineCount do
            let text = lineAt l
            let trimmed = text.TrimStart()

            if trimmed = "" || trimmed.StartsWith "//" then ()
            elif indentOf text > own then yield indentOf text
            else inside <- false

            l <- l + 1
    ]

/// The tokens that open an offside context: the first token after one of
/// them sets the column its block continues at on the lines below - a line
/// standing exactly there is the block's next item, one further in a
/// continuation of the current item, one short of it closes the block.
let private contextOpeners =
    set
        [
            "LPAREN"
            "LBRACK"
            "LBRACE"
            "LBRACK_BAR"
            "LBRACE_BAR"
            "BEGIN"
            "EQUALS"
            "RARROW"
            "THEN"
            "ELSE"
            "DO"
            "WITH"
            "FUN"
            "FUNCTION"
            "TRY"
            "FINALLY"
            "LAZY"
            "YIELD"
            "YIELD_BANG"
            "LARROW"
            "COLON_EQUALS"
            "ASSERT"
        ]

let private bracketOpeners =
    set [ "LPAREN"; "LBRACK"; "LBRACE"; "LBRACK_BAR"; "LBRACE_BAR"; "BEGIN" ]

let private bracketClosers =
    set [ "RPAREN"; "RBRACK"; "RBRACE"; "BAR_RBRACK"; "BAR_RBRACE"; "END" ]

/// Every string literal of a file, lexed — plain, verbatim, triple-quoted
/// and interpolated alike, a multi-line one as the text of each of its
/// lines. Read once per file for the run.
///
/// The question a call-site migration asks of it: does any string in the
/// project spell the function it is about to reshape? A code generator
/// writes calls from templates — SQLProvider.Fable's CodeGen emits
/// `Row.text r "Name"` from a string — and no symbol table lists those
/// calls, so FR0091 reordered `Row.text`'s parameters, rewrote the fifty
/// calls it could see, and left the generator producing the old order.
/// Keyed by path and stamped with the file's write time: a pass that edits
/// the file, or a resident host that lives through the user's edits, must
/// read the literals as they are now, and a file that went away must not
/// keep its entry warm.
let private stringLiteralsCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, DateTime * string[]>(StringComparer.OrdinalIgnoreCase)

let stringLiteralsOf (path: string) : string[] =
    let stamp =
        try
            File.GetLastWriteTimeUtc path
        with _ -> // fsharpanalyzer: ignore-line FR0055
            DateTime.MinValue

    let read (p: string) =
        try
            let tokenizer = FSharpSourceTokenizer([], Some p, None, None)
            let literals = ResizeArray<string>()
            let mutable state = FSharpTokenizerLexState.Initial

            for line in File.ReadLines p do
                let lineTokenizer = tokenizer.CreateLineTokenizer line
                let mutable scanning = true

                while scanning do
                    match lineTokenizer.ScanToken state with
                    | Some token, next ->
                        state <- next

                        if
                            token.CharClass = FSharpTokenCharKind.String
                            && token.RightColumn >= token.LeftColumn
                        then
                            literals.Add(
                                line.Substring(
                                    token.LeftColumn,
                                    min (line.Length - token.LeftColumn) (token.RightColumn - token.LeftColumn + 1)
                                )
                            )
                    | None, next ->
                        state <- next
                        scanning <- false

            literals.ToArray()
        with _ -> // unreadable: no literal known, the caller's other guards stand; fsharpanalyzer: ignore-line FR0055
            [||]

    let _, literals =
        stringLiteralsCache.AddOrUpdate(
            path,
            (fun p -> stamp, read p),
            (fun p (cachedStamp, cached) ->
                if cachedStamp = stamp then
                    cachedStamp, cached
                else
                    stamp, read p)
        )

    literals

/// An `#if` region of a file as the parser saw it: the lines from the
/// `#if` to its `#endif`, both branches, and the names its condition tests.
type DirectiveRegion =
    {
        StartLine: int
        EndLine: int
        Names: string list
    }

let private directiveChecker =
    lazy (FSharp.Compiler.CodeAnalysis.FSharpChecker.Create(keepAssemblyContents = false))

/// Keyed by path and stamped with the file's write time, as stringLiteralsCache.
let private directiveRegionsCache =
    System.Collections.Concurrent.ConcurrentDictionary<string, DateTime * DirectiveRegion list option>(
        StringComparer.OrdinalIgnoreCase
    )

let rec private namesInCondition (e: IfDirectiveExpression) =
    match e with
    | IfDirectiveExpression.And(a, b)
    | IfDirectiveExpression.Or(a, b) -> namesInCondition a @ namesInCondition b
    | IfDirectiveExpression.Not a -> namesInCondition a
    | IfDirectiveExpression.Ident name -> [ name ]

/// The `#if` regions of `path`, read from the parser's trivia rather than
/// matched as text: a `#if` inside a block comment or a multi-line string
/// is text, and the condition is the expression it is, not a word in a
/// line. The lexer records every directive whichever branch is taken, so
/// the parse needs no defines. None for a file that cannot be read; the
/// callers decide what not knowing means to them.
let directiveRegionsOf (path: string) : DirectiveRegion list option =
    let stamp =
        try
            File.GetLastWriteTimeUtc path
        with _ -> // fsharpanalyzer: ignore-line FR0055
            DateTime.MinValue

    let read (p: string) =
        try
            let text = File.ReadAllText p

            // a file without the characters has no directive to read, and
            // most files have none: the parse is for the ones that do
            let directives =
                if not (text.Contains "#if") then
                    []
                else
                    let parsingOptions =
                        { FSharp.Compiler.CodeAnalysis.FSharpParsingOptions.Default with
                            SourceFiles = [| p |]
                        }

                    let result =
                        directiveChecker.Value.ParseFile(p, SourceText.ofString text, parsingOptions)
                        // fsharplint:disable-next-line NoAsyncRunSynchronouslyInLibrary
                        |> Async.RunSynchronously

                    match result.ParseTree with
                    | ParsedInput.ImplFile(ParsedImplFileInput(trivia = trivia)) -> trivia.ConditionalDirectives
                    | ParsedInput.SigFile(ParsedSigFileInput(trivia = trivia)) -> trivia.ConditionalDirectives

            // one entry per open `#if`
            let open' = Stack<int * string list>()

            Some
                [
                    for directive in directives do
                        match directive with
                        | ConditionalDirectiveTrivia.If(condition, r) ->
                            open'.Push(r.StartLine, namesInCondition condition)
                        | ConditionalDirectiveTrivia.Else _ -> ()
                        | ConditionalDirectiveTrivia.EndIf r ->
                            if open'.Count > 0 then
                                let start, names = open'.Pop()

                                {
                                    StartLine = start
                                    EndLine = r.StartLine
                                    Names = names
                                }
                ]
        with _ -> // unreadable: no regions known; fsharpanalyzer: ignore-line FR0055
            None

    let _, regions =
        directiveRegionsCache.AddOrUpdate(
            path,
            (fun p -> stamp, read p),
            (fun p (cachedStamp, cached) ->
                if cachedStamp = stamp then
                    cachedStamp, cached
                else
                    stamp, read p)
        )

    regions

/// The names a directive tests when it branches on the build
/// CONFIGURATION. A framework region's other branch is a compilation of
/// its own, which the narrowest-first passes and the all-frameworks build
/// already answer for; these are the ones the parse tree never holds.
let private configurationNames = set [ "DEBUG"; "RELEASE"; "TRACE" ]

let private branchesOnConfiguration (region: DirectiveRegion) =
    region.Names |> List.exists configurationNames.Contains

/// Does `path` branch on the build configuration - `#if DEBUG`, `#if
/// !DEBUG`, `#if RELEASE`, `#if TRACE`? The analysis sees one
/// configuration's branch; the other is not in the parse tree at all. An
/// unreadable file is taken to.
let hasConfigurationConditional (path: string) =
    match directiveRegionsOf path with
    | Some regions -> regions |> List.exists branchesOnConfiguration
    | None -> true

/// Does any of `files` name `identifier` on a line inside an `#if` region
/// that branches on the build configuration? Such a line is in the parse
/// tree under one set of defines only, so a rewrite of the definition and
/// "every call site" reaches the calls of one branch and leaves the
/// other's behind — found by building the other configuration, which is
/// late. The regions come from the parser; the lines inside them are text
/// by nature (the untaken branch is in no parse tree), so the name is
/// matched as a word there, over-eagerly within that.
let namedInDirectiveRegion (files: string seq) (identifier: string) =
    let word = Regex($@"(?<![\w'`]){Regex.Escape identifier}(?![\w'`])")

    files
    |> Seq.exists (fun f ->
        match directiveRegionsOf f with
        | None -> true // unreadable: assume the worst, the migration waits
        | Some regions ->
            match regions |> List.filter branchesOnConfiguration with
            | [] -> false
            | configured ->
                try
                    File.ReadLines f
                    |> Seq.indexed
                    |> Seq.exists (fun (i, line) ->
                        let lineNumber = i + 1

                        configured
                        |> List.exists (fun r -> r.StartLine < lineNumber && lineNumber < r.EndLine)
                        && not (line.TrimStart().StartsWith "#")
                        && line.Contains identifier
                        && word.IsMatch line)
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    true)

/// Does a string literal in any of `files` name `identifier` as a whole
/// word? `Row.text` and `text` both count for `text`: a template spells
/// the call the way the code does.
let stringLiteralMentions (files: string seq) (identifier: string) =
    let word = Regex($@"(?<![\w'`]){Regex.Escape identifier}(?![\w'`])")

    files
    |> Seq.exists (fun f ->
        stringLiteralsOf f
        |> Array.exists (fun literal -> literal.Contains identifier && word.IsMatch literal))

/// The columns of `lineText` a line below may be anchored to: for every
/// context opener still open at the end of the line, the column of the
/// token that follows it. A bracket closed on the same line takes every
/// anchor inside it with it - nothing below can be aligned to text inside
/// `(Guid.NewGuid())`. An opener that ends the line anchors nothing here:
/// the next line's own first token sets that block's column. The line is
/// lexed on its own, so a line inside a multi-line string or comment lexes
/// as code; the caller edits code, so that is the line it asks about.
let offsideAnchors (lineText: string) : int list =
    let tokenizer = FSharpSourceTokenizer([], None, None, None)
    let lineTokenizer = tokenizer.CreateLineTokenizer lineText
    let tokens = ResizeArray<FSharpTokenInfo>()
    let mutable state = FSharpTokenizerLexState.Initial
    let mutable scanning = true

    while scanning do
        match lineTokenizer.ScanToken state with
        | Some token, next ->
            state <- next

            if
                token.TokenName <> "WHITESPACE"
                && token.ColorClass <> FSharpTokenColorKind.Comment
            then
                tokens.Add token
        | None, _ -> scanning <- false

    let anchors = ResizeArray<int>()
    // how many anchors were recorded when each still-open bracket opened:
    // closing it discards everything recorded since
    let openBrackets = Stack<int>()

    for i in 0 .. tokens.Count - 1 do
        let name = tokens.[i].TokenName

        if bracketClosers.Contains name then
            if openBrackets.Count > 0 then
                let mark = openBrackets.Pop()
                anchors.RemoveRange(mark, anchors.Count - mark)
        else
            if bracketOpeners.Contains name then
                openBrackets.Push anchors.Count

            if contextOpeners.Contains name && i + 1 < tokens.Count then
                anchors.Add tokens.[i + 1].LeftColumn

    List.ofSeq anchors

/// Would an edit on a single line, replacing a stretch ending at `endColumn`
/// with text `delta` characters longer (negative: shorter),
/// change how a line continuing it reads (see `continuationIndents`)? Those
/// lines do not move; the anchors after the edit do (see `offsideAnchors`),
/// and the hazard is a line whose standing against one of them - on it, to
/// its right, to its left - is not the same after the shift. fparsec's
/// CharParsers.fs:
///
///     && stream.SkipCaseFolded("inf") && (flags <- flags ||| NLF.IsInfinity
///                                         stream.SkipCaseFolded("inity") |> ignore
///
/// dropping the parens around `"inf"` moved `flags` two columns left, the
/// line under it stayed, and the block re-parsed as an application. The
/// earlier form of this check called ANY line indented past the edit's end
/// aligned - which is every arm body under a `| _ ->` it would have
/// expanded, every argument continued on the next line, and it silently
/// withheld whole files of FR0072 and FR0147 fixes (ClearBank.Net's tests,
/// management-portal's hubs). A line to the right of every anchor before
/// and after the shift is a continuation either way, and reads the same.
/// `lineAt` is 1-based, like a range's lines.
let alignmentHazard (lineAt: int -> string) (lineCount: int) (line: int) (endColumn: int) (delta: int) =
    delta <> 0
    && (match continuationIndents lineAt lineCount line with
        | [] -> false
        | indents ->
            // an anchor inside the edited stretch is replaced with it; one
            // before it does not move
            let moving =
                offsideAnchors (lineAt line) |> List.filter (fun anchor -> anchor >= endColumn)

            indents
            |> List.exists (fun indent ->
                moving
                |> List.exists (fun anchor -> compare indent anchor <> compare indent (anchor + delta))))

let alignmentHazardBelow (source: ISourceText) (line: int) (endColumn: int) (delta: int) =
    alignmentHazard (fun l -> source.GetLineString(l - 1)) (source.GetLineCount()) line endColumn delta

/// Does a directive open on the first non-blank line AFTER the range? The
/// parse tree ends at the last construct the ACTIVE defines leave visible,
/// so a `#if` block starting just below it can hold further match arms that
/// another configuration compiles. Rewriting only the visible arms strands
/// those, and the build check never sees it - it compiles the one
/// configuration in front of it, where the file is still valid.
let directiveFollows (source: ISourceText) (r: range) =
    let rec scan line =
        if line > source.GetLineCount() then
            false
        else
            let text = (source.GetLineString(line - 1)).TrimStart()

            if text = "" then scan (line + 1) else text.StartsWith '#'

    scan (r.EndLine + 1)

/// Total line accessor: a stale or synthetic FCS range can point outside the
/// current source snapshot. Out-of-bounds yields "" via a bounds check —
/// nothing is caught, so real failures still propagate.
let lineTextAt (source: ISourceText) (zeroBasedLine: int) =
    if zeroBasedLine < 0 || zeroBasedLine >= source.GetLineCount() then
        ""
    else
        source.GetLineString zeroBasedLine

/// Is the expression inside QUOTED code — a `query { }`-style builder (any
/// builder whose name ends in "query") or an `<@ @>` quotation? Code there
/// is data for a translator, not code that runs here: a LINQ provider
/// recognizes `y.IsNone` or the string Contains overload in a where clause
/// and turns them into SQL, while the "nicer" spelling — an Option-module
/// call wrapping a lambda, a char overload, an AsSpan — is a tree shape it
/// has never seen. Shape-changing rules stay quiet under either.
let insideQuotedCode (path: SyntaxNode list) =
    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.Quote _) -> true
        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.Ident id)) ->
            id.idText.EndsWith("query", StringComparison.OrdinalIgnoreCase)
        | _ -> false)

/// Does the file `open System` at any top-level line? Textual, cheap and
/// deliberately exact: `open System.IO` does not bring System.String into
/// scope, and a fix emitted without the open must spell `System.` out.
let opensSystemNamespace (source: ISourceText) =
    seq { 0 .. source.GetLineCount() - 1 }
    |> Seq.exists (fun l -> source.GetLineString(l).Trim() = "open System")

/// Does the file `open` this exact namespace at any top-level line? The
/// same textual, deliberately exact test as opensSystemNamespace.
let opensNamespace (source: ISourceText) (ns: string) =
    seq { 0 .. source.GetLineCount() - 1 }
    |> Seq.exists (fun l -> source.GetLineString(l).Trim() = "open " + ns)

/// A regex matching `name` as a WHOLE F# identifier. `\b<name>\b` is wrong
/// for this language: identifiers may end in primes (`visit'`), and after
/// a `'` the \b anchor finds no boundary — `\bvisit'\b` never matches
/// `visit' exp` at all, which let a recursive reference slip past a
/// membership check (caught adversarially on Linq.Expression.Optimizer).
let identifierPattern (name: string) =
    @"(?<![\w'])" + Regex.Escape name + @"(?![\w'])"

/// A char regex `\w` matches — `[\p{L}\p{Mn}\p{Nd}\p{Pc}]`, the nonspacing
/// marks included so a decomposed `naive` + combining acute reads as one
/// identifier rather than as a mention of `naive` — plus the `'` that
/// identifierPattern guards alongside it.
let private isIdentifierChar (c: char) =
    Char.IsLetterOrDigit c
    || c = '''
    || (match Char.GetUnicodeCategory c with
        | System.Globalization.UnicodeCategory.NonSpacingMark
        | System.Globalization.UnicodeCategory.ConnectorPunctuation -> true
        | _ -> false)

/// `text` names `name` as a whole identifier: the hand-rolled equal of
/// `Regex.IsMatch(text, identifierPattern name)`, for the callers that ask it
/// per AST node. A Regex there costs either a per-name instance cached for the
/// life of a process that outlives the sweep (Ionide and the VS extension host
/// these analyzers for days), or a pattern-cache lookup on every call; two
/// boundary checks around an ordinal IndexOf need neither.
let mentionsIdentifier (text: string) (name: string) =
    if String.IsNullOrEmpty name then
        false
    else
        let mutable i = text.IndexOf(name, StringComparison.Ordinal)
        let mutable found = false

        while not found && i >= 0 do
            let openedBefore = i = 0 || not (isIdentifierChar text.[i - 1])
            let ended = i + name.Length

            if openedBefore && (ended >= text.Length || not (isIdentifierChar text.[ended])) then
                found <- true
            else
                i <- text.IndexOf(name, i + 1, StringComparison.Ordinal)

        found

/// Every comment in a parse tree, as (range, text) — shared by the apply
/// layer's comment guard and its editor-side twin.
let commentsWithText (parseTree: ParsedInput) (source: ISourceText) =
    let ranges =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(trivia = trivia)) -> trivia.CodeComments
        | ParsedInput.SigFile(ParsedSigFileInput(trivia = trivia)) -> trivia.CodeComments
        |> List.map (fun c ->
            match c with
            | CommentTrivia.LineComment r
            | CommentTrivia.BlockComment r -> r)

    ranges |> List.map (fun r -> r, textOfRange source r)

/// Does a companion `.fsi` declare this file's contents?
///
/// A signature and its implementation must agree on more than types: field
/// NAMES, and attributes like `[<Literal>]`, are part of the contract. A rule
/// that reshapes a declaration in the .fs alone therefore stops the project
/// compiling — "The names differ", "The literal constant values and/or
/// attributes differ". Both were found on Fable's fcs-fable, which carries
/// 176 signature files.
///
/// Fixing such a rewrite properly means editing the .fsi in step, which is
/// the same reason the api pass skips projects carrying signatures. Until a
/// rule can do that, it stands down here.
let hasSignatureFile (fileName: string) =
    try
        not (String.IsNullOrEmpty fileName)
        && File.Exists(Path.ChangeExtension(fileName, ".fsi"))
    with _ -> // an unreadable path simply is not a signature; fsharpanalyzer: ignore-line FR0055
        false

/// Does the companion .fsi name this declaration?
///
/// The scope gate lets a PRIVATE declaration change shape even beside a
/// signature, on the reasoning that a signature declares every internal
/// and public name but never a private one. That reasoning is wrong: F#
/// signature files may write `val private`, and Deedle's vendored
/// FSharp.Data does —
///
///     val private ( |SubtypePrimitives|_| ) : ... -> (...) option
///
/// so FR0011 gave the implementation a `voption` return the signature
/// still declared as `option`, and the project stopped compiling. The
/// build check put it back; an editor's light bulb has no such check.
///
/// Deliberately TEXTUAL, and deliberately over-eager. Parsing the .fsi
/// needs the host's cross-file parser, which editors do not install — and
/// this has to hold in the editor, which is where the unverified fix
/// lands. A name that merely appears in the signature stands the rewrite
/// down; the cost of that is a fix not offered, against a project that
/// does not compile.
let signatureMentions (fileName: string) (name: string) =
    try
        if String.IsNullOrEmpty fileName || String.IsNullOrEmpty name then
            false
        else
            let signature = Path.ChangeExtension(fileName, ".fsi")

            File.Exists signature
            && (let text = File.ReadAllText signature
                // whole-word: `Value` must not match `ValueKind`
                let escaped = Regex.Escape name

                Regex.IsMatch(text, $@"(?<![\w'`]){escaped}(?![\w'])"))
    with _ -> // an unreadable signature is treated as declaring it; fsharpanalyzer: ignore-line FR0055
        true

/// Every name a pattern binds: `x`, the `a` and `b` of `(a, b)`, the `f`
/// and its parameters of `f (x: int) y`, the `v` of `Some v as v`.
[<TailCall>]
let rec private patNamesLoop (acc: string list) (pending: SynPat list) =
    match pending with
    | [] -> acc
    | p :: rest ->
        let acc, next =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText :: acc, rest
            | SynPat.As(lhsPat = lhs; rhsPat = rhs) -> acc, lhs :: rhs :: rest
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner)
            | SynPat.Paren(inner, _) -> acc, inner :: rest
            | SynPat.Tuple(elementPats = ps)
            | SynPat.ArrayOrList(elementPats = ps)
            | SynPat.Ands(pats = ps) -> acc, ps @ rest
            | SynPat.Or(lhsPat = lhs; rhsPat = rhs) -> acc, lhs :: rhs :: rest
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ head ]); argPats = SynArgPats.Pats ps) ->
                head.idText :: acc, ps @ rest
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> acc, ps @ rest
            // the four forms patBoundNames knows and this loop did not: a
            // `{ Id = id }` record pattern, a `(id, _) :: _` cons, an
            // optional `?id` and the named fields of `Case(Field = p)`. A
            // scope check that missed them (FR0095's shadowedAt) took a
            // match arm's `id` for FSharp.Core's
            | SynPat.Record(fieldPats = fields) ->
                acc, (fields |> List.map (fun (f: NamePatPairField) -> f.Pattern)) @ rest
            | SynPat.ListCons(lhsPat = lhs; rhsPat = rhs) -> acc, lhs :: rhs :: rest
            | SynPat.OptionalVal(ident = id) -> id.idText :: acc, rest
            | SynPat.LongIdent(argPats = SynArgPats.NamePatPairs(pats = ps)) ->
                acc, (ps |> List.map (fun (fieldPat: NamePatPairField) -> fieldPat.Pattern)) @ rest
            | _ -> acc, rest

        patNamesLoop acc next

let patNames (p: SynPat) : string list = patNamesLoop [] [ p ]

/// The `#if` condition a line sits under, innermost first: `Some "DEBUG"`
/// inside `#if DEBUG ... #endif`, `Some "!(DEBUG)"` under its `#else`,
/// None at top level.
let conditionAt (source: ISourceText) (line: int) : string option =
    let stack = Stack<string>()

    for l in 0 .. min (line - 2) (source.GetLineCount() - 1) do
        let text = source.GetLineString(l).Trim()

        if text.StartsWith "#if" then
            stack.Push(text.Substring(3).Trim())
        elif text.StartsWith "#else" then
            if stack.Count > 0 then
                let c = stack.Pop()
                stack.Push $"!({c})"
        elif text.StartsWith "#endif" then
            if stack.Count > 0 then
                stack.Pop() |> ignore

    if stack.Count = 0 then None else Some(stack.Peek())

/// A line a rule moves or generates from `originLine` to `targetLine` keeps
/// the `#if` it came from: the condition to wrap it in when the target sits
/// under a different one (or none). A rule that lifts a line to module
/// level must not free it from its condition, nor bind it to another — the
/// F# compiler's `open FSComp` landed inside `#if !NO_TYPEPROVIDERS` and
/// the Proto build stopped compiling.
let conditionToKeep (source: ISourceText) (originLine: int) (targetLine: int) : string option =
    match conditionAt source originLine with
    | Some c when conditionAt source targetLine <> Some c -> Some c
    | _ -> None

/// Re-indent a block of source text so it starts at `target`, moving every
/// continuation line by the same amount. `firstColumn` is the column the
/// block's first line began at — the text itself no longer carries it,
/// since a range's first line arrives already trimmed of its indentation.
///
/// None when the move cannot preserve the block: a continuation line with
/// less leading space than a leftward shift would remove (its structure
/// would collapse), or a line spanning string literal, whose content the
/// re-indent would silently edit. The caller then leaves the code alone.
///
/// Does a line break fall inside a string literal or a block comment? A
/// textual walk over the block, with no parse tree to ask: plain `"…"`
/// (with `\` escapes), verbatim `@"…"` (`""` escapes), triple-quoted
/// `"""…"""`, each with or without `$` prefixes, and `(* … *)`. Line
/// comments run to the end of their line; `'"'` is a char, not a string
/// start. The walk stays on the safe side: a mis-read only ever reports a
/// break INSIDE a literal, never hides one.
let private lineBreakInsideLiteral (text: string) =
    let n = text.Length
    let at i = if i < n then text.[i] else '\000'

    let startsAt i (s: string) =
        i + s.Length <= n && text.Substring(i, s.Length) = s

    // states: 0 code, 1 plain string, 2 verbatim string, 3 triple-quoted
    // string, 4 line comment, 5 block comment (nesting depth in `depth`)
    let mutable state = 0
    let mutable depth = 0
    let mutable i = 0
    let mutable found = false

    while not found && i < n do
        let c = at i

        match state with
        | 0 ->
            if startsAt i "(*)" then
                i <- i + 3
            elif startsAt i "(*" then
                state <- 5
                depth <- 1
                i <- i + 2
            elif startsAt i "//" then
                state <- 4
                i <- i + 2
            elif c = '\'' && at (i + 2) = '\'' then
                i <- i + 3
            elif c = '\'' && at (i + 1) = '\\' then
                let close = text.IndexOf('\'', i + 2)
                i <- (if close > 0 && close - i <= 8 then close + 1 else i + 1)
            elif startsAt i "\"\"\"" then
                state <- 3
                i <- i + 3
            elif c = '@' && at (i + 1) = '"' then
                state <- 2
                i <- i + 2
            elif c = '$' && (at (i + 1) = '@' || at (i + 1) = '"' || at (i + 1) = '$') then
                i <- i + 1
            elif c = '"' then
                state <- 1
                i <- i + 1
            else
                i <- i + 1
        | 1 ->
            if c = '\n' then
                found <- true
            // `\` before the break continues the literal on the next line
            elif c = '\\' then
                (if at (i + 1) = '\n' then found <- true else i <- i + 2)
            elif c = '"' then
                state <- 0
                i <- i + 1
            else
                i <- i + 1
        | 2 ->
            if c = '\n' then
                found <- true
            elif c = '"' && at (i + 1) = '"' then
                i <- i + 2
            elif c = '"' then
                state <- 0
                i <- i + 1
            else
                i <- i + 1
        | 3 ->
            if c = '\n' then
                found <- true
            elif startsAt i "\"\"\"" then
                state <- 0
                i <- i + 3
            else
                i <- i + 1
        | 4 ->
            if c = '\n' then
                state <- 0

            i <- i + 1
        | _ ->
            if c = '\n' then
                found <- true
            elif startsAt i "(*" then
                depth <- depth + 1
                i <- i + 2
            elif startsAt i "*)" then
                depth <- depth - 1

                if depth = 0 then
                    state <- 0

                i <- i + 2
            else
                i <- i + 1

    found

/// Three rules grew their own copy of this before it was extracted
/// (FR0034's match layout, FR0044's try removal, FR0142's task wrap); they
/// can migrate to it.
let reindentBlock (target: int) (firstColumn: int) (text: string) : string option =
    let lines = text.Replace("\r\n", "\n").Split '\n'

    if lines.Length = 1 then
        Some(String(' ', target) + lines.[0])
    else
        let shift = target - firstColumn
        let continuation = lines |> Array.skip 1
        let leading (l: string) = l.Length - l.TrimStart().Length

        if
            (shift < 0
             && continuation
                |> Array.exists (fun l -> not (String.IsNullOrWhiteSpace l) && leading l < -shift))
            // a continuation line that belongs to a string literal (or a
            // block comment) is content, not layout: moving it edits the
            // program's data
            || lineBreakInsideLiteral (String.concat "\n" lines)
        then
            None
        else
            let moved =
                continuation
                |> Array.map (fun l ->
                    if String.IsNullOrWhiteSpace l then ""
                    elif shift >= 0 then String(' ', shift) + l
                    else l.Substring(-shift))

            Some(String.concat "\n" (Array.append [| String(' ', target) + lines.[0] |] moved))
