/// Helpers for turning FCS ranges back into source text.
/// All refactorings emit minimal range-based edits, so extracting the exact
/// original text of a sub-expression is the core primitive.
module FSharp.Refactor.Text

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open System.Text.RegularExpressions

/// The exact source text covered by a range.
let textOfRange (source: ISourceText) (r: range) : string =
    if r.StartLine = r.EndLine then
        source.GetLineString(r.StartLine - 1).Substring(r.StartColumn, r.EndColumn - r.StartColumn)
    else
        [ for lineNumber in r.StartLine .. r.EndLine do
              let line = source.GetLineString(lineNumber - 1)

              if lineNumber = r.StartLine then
                  line.Substring r.StartColumn
              elif lineNumber = r.EndLine then
                  line.Substring(0, r.EndColumn)
              else
                  line ]
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

    let mutable line = declRange.StartLine

    while isDocLine line do
        line <- line + 1

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
    { FileName: string
      Source: ISourceText
      ParseTree: ParsedInput }

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
            r.FileName.Equals(other.FileName, System.StringComparison.OrdinalIgnoreCase)
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
            {| IsRecursive = isRecursive
               IsUse = isUse
               IsBang = isBang
               Bindings = bindings
               Body = body
               Range = e.Range |}
    | _ -> ValueNone
#else
    match e with
    | SynExpr.LetOrUse lou ->
        ValueSome
            {| IsRecursive = lou.IsRecursive
               IsUse = lou.IsUse
               IsBang = lou.IsBang
               Bindings = lou.Bindings
               Body = lou.Body
               Range = lou.Range |}
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
            // a no-argument lone identifier (the uppercase binder's parse
            // shape) BINDS the name — record it like Named
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) ->
                id.idText :: acc, rest
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> acc, ps @ rest
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
        [ "Bind"
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
          "BindReturn" ]

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
/// leave code that no longer compiles under the other defines.
let spansDirective (source: ISourceText) (r: range) =
    seq { r.StartLine .. r.EndLine }
    |> Seq.exists (fun line ->
        let text = (source.GetLineString(line - 1)).TrimStart()

        text.StartsWith "#if" || text.StartsWith "#else" || text.StartsWith "#endif")

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
            id.idText.EndsWith("query", System.StringComparison.OrdinalIgnoreCase)
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

/// Every comment in a parse tree, as (range, text) — shared by the apply
/// layer's comment guard and its editor-side twin.
let commentsWithText (parseTree: ParsedInput) (source: ISourceText) =
    let ranges =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(trivia = trivia)) -> trivia.CodeComments
        | ParsedInput.SigFile(ParsedSigFileInput(trivia = trivia)) -> trivia.CodeComments
        |> List.map (fun c ->
            match c with
            | FSharp.Compiler.SyntaxTrivia.CommentTrivia.LineComment r
            | FSharp.Compiler.SyntaxTrivia.CommentTrivia.BlockComment r -> r)

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
        not (System.String.IsNullOrEmpty fileName)
        && System.IO.File.Exists(System.IO.Path.ChangeExtension(fileName, ".fsi"))
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
        if System.String.IsNullOrEmpty fileName || System.String.IsNullOrEmpty name then
            false
        else
            let signature = System.IO.Path.ChangeExtension(fileName, ".fsi")

            System.IO.File.Exists signature
            && (let text = System.IO.File.ReadAllText signature
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
            | _ -> acc, rest

        patNamesLoop acc next

let patNames (p: SynPat) : string list = patNamesLoop [] [ p ]

/// The `#if` condition a line sits under, innermost first: `Some "DEBUG"`
/// inside `#if DEBUG ... #endif`, `Some "!(DEBUG)"` under its `#else`,
/// None at top level.
let conditionAt (source: ISourceText) (line: int) : string option =
    let stack = System.Collections.Generic.Stack<string>()

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
/// Three rules grew their own copy of this before it was extracted
/// (FR0034's match layout, FR0044's try removal, FR0142's task wrap); they
/// can migrate to it.
let reindentBlock (target: int) (firstColumn: int) (text: string) : string option =
    let lines = text.Replace("\r\n", "\n").Split '\n'

    if lines.Length = 1 then
        Some(System.String(' ', target) + lines.[0])
    else
        let shift = target - firstColumn
        let continuation = lines |> Array.skip 1
        let leading (l: string) = l.Length - l.TrimStart().Length

        if
            shift < 0
            && continuation |> Array.exists (fun l -> l.Trim() <> "" && leading l < -shift)
        then
            None
        else
            let moved =
                continuation
                |> Array.map (fun l ->
                    if l.Trim() = "" then ""
                    elif shift >= 0 then System.String(' ', shift) + l
                    else l.Substring(-shift))

            Some(String.concat "\n" (Array.append [| System.String(' ', target) + lines.[0] |] moved))
