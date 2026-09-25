/// Refactoring: pull a non-recursive member out of a `let rec ... and`
/// group (FR0116, fix).
///
///     let rec f1 x = f3 x + x         let f2 y = y + 1
///     and f2 y = y + 1           →
///     and f3 z = f1 z - z             let rec f1 x = f3 x + x
///                                     and f3 z = f1 z - z
///
/// A binding that references no member of its group takes part in no
/// recursion; carrying it in the `and` chain only widens the knot. It
/// moves to a plain `let` ABOVE the group — members may call it from
/// there, and it can call nothing in the group by construction.
///
/// A self-recursive member (calls itself, nobody else) leaves the same
/// way but keeps its own `let rec`. And when the HEAD is the one that
/// references nobody, nothing moves at all: `findHeadRecrowns` turns its
/// `let rec` into `let` and re-crowns the next binding — see below.
///
/// Safety rules (v1 keeps the surgery small):
///   - module-level groups only; the head is handled by re-crowning, the
///     rest by moving out
///   - the binding may carry no attributes, and nothing but whitespace may
///     sit between the previous binding's end and its `and` (a comment
///     there would be orphaned — and the comment guard would hold the fix
///     back anyway)
///   - group-membership is judged textually: any `\b<member>\b` inside the
///     binding block keeps it in the group, so a shadowed name errs toward
///     staying put
module FSharp.Refactor.RecGroup

open System
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The first leaving member's block - replaced with nothing; the
        /// hint's anchor.
        RemoveRange: range
        /// Every block that leaves, adjacent ones merged; `RemoveRange`
        /// is the head.
        Removes: range list
        /// Zero-width, at the group's start - the plain `let`s go here.
        InsertRange: range
        InsertText: string
        MemberName: string
        /// The member calls itself (but nobody else): it leaves the group
        /// as its own `let rec`, not a plain `let`.
        IsSelfRecursive: bool
        /// Every leaving member with its self-recursion, in the order they
        /// are inserted; `MemberName`/`IsSelfRecursive` are the head.
        Members: (string * bool) list
    }

/// One member ready to leave its group, before the group's leavers are
/// folded into a single suggestion.
type private Part =
    {
        Block: range
        Extracted: string
        HasComments: bool
        Condition: string option
        Name: string
        SelfRecursive: bool
    }

/// The HEAD of a group references no sibling: nothing needs to move at
/// all — the head's `let rec` becomes `let`, and the next binding's
/// `and` is re-crowned `let rec`. Two keyword rewrites, in place.
type HeadSuggestion =
    {
        /// The head's `let rec` keyword — becomes `let`.
        LetRecRange: range
        /// The second binding's `and` keyword — becomes `let rec`.
        AndRange: range
        MemberName: string
    }

let private bindingName (SynBinding(headPat = pat)) =
    match pat with
    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats _) -> Some id.idText
    | _ -> None

/// The identifiers a binding is USED by. An active pattern's definition
/// name is `|SqlColumnGet|_|`, but every use site says `SqlColumnGet` —
/// checking the decorated name finds nothing, which read as "references
/// no sibling" on SQLProvider's mutually recursive pattern grammar and
/// offered extractions that could not hold together.
let private referenceNames (name: string) =
    if name.Contains '|' then
        name.Split '|'
        |> Array.filter (fun part -> part <> "" && part <> "_")
        |> List.ofArray
    else
        [ name ]

let private isIdentifierChar (c: char) =
    Char.IsLetterOrDigit c || c = '_' || c = '''

/// The text with its string literals, char literals and comments blanked:
/// a name inside `failwith "StripToNominalTyconRef: ..."` is no reference
/// (the F# compiler's Optimizer.fs kept `let rec` on fifteen functions
/// whose only "self-call" was such a message). An interpolated string's
/// holes are CODE and stay visible — `$"size is {size n}"` calls `size` —
/// and a char literal `'"'` opens no string. A regex got both wrong: the
/// hole vanished with the text around it, and the quote inside the char
/// literal flipped the string phase for the rest of the block; either way
/// a reference went unseen, and a member left the group above a sibling
/// it still called. Anything this scanner cannot place stays visible: an
/// extra mention only keeps a member where it is.
let private codeOnly (text: string) =
    let chars = text.ToCharArray()
    let out = Array.copy chars
    let n = chars.Length

    let at i =
        if i >= 0 && i < n then chars.[i] else '\000'

    let blank i =
        if i >= 0 && i < n && chars.[i] <> '\n' && chars.[i] <> '\r' then
            out.[i] <- ' '

    let blankTo (a: int) (b: int) =
        for i in a .. b - 1 do
            blank i

    // a literal's end: from just after its opening quote(s) to just after
    // its closing quote(s); n when unterminated
    let closeOfString (start: int) (verbatim: bool) (triple: bool) =
        let mutable j = start
        let mutable close = -1

        while close < 0 && j < n do
            let c = chars.[j]

            if triple then
                if c = '"' && at (j + 1) = '"' && at (j + 2) = '"' then
                    close <- j + 3
                else
                    j <- j + 1
            elif verbatim then
                if c = '"' then
                    // a doubled quote is an escaped quote
                    if at (j + 1) = '"' then j <- j + 2 else close <- j + 1
                else
                    j <- j + 1
            elif c = '\\' then
                j <- j + 2
            elif c = '"' then
                close <- j + 1
            else
                j <- j + 1

        if close < 0 then n else close

    // code from `start`; inside a hole, up to and including the `}` that
    // closes it (braces within nest). Returns the index after the last
    // character consumed
    let rec scanCode (start: int) (inHole: bool) : int =
        let mutable j = start
        let mutable depth = 0
        let mutable fin = -1

        while fin < 0 && j < n do
            let c = chars.[j]
            let next = at (j + 1)

            if c = '/' && next = '/' then
                let mutable e = j

                while e < n && chars.[e] <> '\n' do
                    e <- e + 1

                blankTo j e
                j <- e
            elif c = '(' && next = '*' && at (j + 2) <> ')' then
                // block comments nest; `(*)` is the multiplication operator
                let mutable d = 1
                let mutable e = j + 2

                while d > 0 && e < n do
                    if chars.[e] = '(' && at (e + 1) = '*' then
                        d <- d + 1
                        e <- e + 2
                    elif chars.[e] = '*' && at (e + 1) = ')' then
                        d <- d - 1
                        e <- e + 2
                    else
                        e <- e + 1

                blankTo j e
                j <- e
            elif c = ''' && not (j > 0 && isIdentifierChar chars.[j - 1]) then
                // a char literal (`'"'`, `'\n'`, `'\''`) opens no string; a
                // type variable `'a` is one apostrophe and moves on; the
                // prime of `x'` is part of the identifier before it
                if next = '\\' then
                    let close = Array.IndexOf(chars, ''', min n (j + 2))

                    if close > 0 && close - j <= 12 then
                        blankTo j (close + 1)
                        j <- close + 1
                    else
                        j <- j + 1
                elif at (j + 2) = ''' then
                    blankTo j (j + 3)
                    j <- j + 3
                else
                    j <- j + 1
            elif c = '"' then
                let triple = next = '"' && at (j + 2) = '"'
                let close = closeOfString (if triple then j + 3 else j + 1) false triple
                blankTo j close
                j <- close
            elif c = '@' && next = '"' then
                let close = closeOfString (j + 2) true false
                blankTo j close
                j <- close
            elif c = '$' || (c = '@' && next = '$') then
                // interpolated: `$"`, `$@"`, `@$"`, `$"""`, `$$"""`
                let mutable e = j
                let mutable verbatim = false
                let mutable dollars = 0

                if chars.[e] = '@' then
                    verbatim <- true
                    e <- e + 1

                while at e = '$' do
                    dollars <- dollars + 1
                    e <- e + 1

                if at e = '@' then
                    verbatim <- true
                    e <- e + 1

                if at e = '"' && dollars > 0 then
                    let triple = at (e + 1) = '"' && at (e + 2) = '"'
                    let bodyStart = if triple then e + 3 else e + 1
                    blankTo j bodyStart
                    j <- scanInterpolated bodyStart dollars verbatim triple
                else
                    j <- j + 1
            elif inHole && c = '{' then
                depth <- depth + 1
                j <- j + 1
            elif inHole && c = '}' then
                if depth = 0 then
                    fin <- j + 1
                else
                    depth <- depth - 1
                    j <- j + 1
            else
                j <- j + 1

        if fin < 0 then n else fin

    // an interpolated string's text, blanked; its holes scanned as code.
    // Returns the index after the closing quote(s)
    and scanInterpolated (start: int) (dollars: int) (verbatim: bool) (triple: bool) : int =
        let mutable j = start
        let mutable fin = -1

        while fin < 0 && j < n do
            let c = chars.[j]

            if c = '{' then
                let rec advanceRun run =
                    if at (j + run) = '{' then advanceRun (run + 1) else run

                let run = advanceRun 0

                // `$"…"` opens a hole with one brace and escapes one with
                // two; `$$"""…"""` opens with two and takes one literally
                if (dollars = 1 && run = 1) || (dollars > 1 && run >= dollars) then
                    blankTo j (j + dollars)
                    let afterHole = scanCode (j + dollars) true
                    blank (afterHole - 1)
                    let mutable e = afterHole
                    let mutable k = 1

                    while k < dollars && at e = '}' do
                        blank e
                        e <- e + 1
                        k <- k + 1

                    j <- e
                else
                    blankTo j (j + run)
                    j <- j + run
            elif triple then
                if c = '"' && at (j + 1) = '"' && at (j + 2) = '"' then
                    blankTo j (j + 3)
                    fin <- j + 3
                else
                    blank j
                    j <- j + 1
            elif verbatim then
                if c = '"' then
                    if at (j + 1) = '"' then
                        blankTo j (j + 2)
                        j <- j + 2
                    else
                        blank j
                        fin <- j + 1
                else
                    blank j
                    j <- j + 1
            elif c = '\\' then
                blankTo j (j + 2)
                j <- j + 2
            elif c = '"' then
                blank j
                fin <- j + 1
            else
                blank j
                j <- j + 1

        if fin < 0 then n else fin

    scanCode 0 false |> ignore
    String out

/// Any use of `name` (by any of its reference identifiers) in the text.
let private mentions (text: string) (name: string) =
    let code = codeOnly text

    referenceNames name
    |> List.exists (fun part -> Regex.IsMatch(code, identifierPattern part))

let rec private declsOf (decls: SynModuleDecl list) : SynModuleDecl list =
    decls
    |> List.collect (fun d ->
        match d with
        | SynModuleDecl.NestedModule(decls = nested) -> d :: declsOf nested
        | _ -> [ d ])

/// Does the binding build or update a record? Inside the group a record
/// expression's type is pinned by the member's callers, all inferred
/// together; standing alone it has only its labels, and a label shared
/// between two records (`PendingConfirmation` in fedit's Model and
/// PickerState) no longer determines the type.
let private buildsRecord (index: AstIndex.Index) (bindingRange: range) =
    AstIndex.exprsWithin index bindingRange
    |> Seq.exists (fun (_, e) ->
        match e with
        | SynExpr.Record _ -> Range.rangeContainsRange bindingRange e.Range
        | _ -> false)

/// Does the member lean on the group's inference for a parameter it does
/// not annotate? A type test, a downcast, a member access or an indexer on
/// a bare parameter is typed by the group's callers; standing alone the
/// parameter is a bare 'a and the compiler refuses the test ("runtime
/// coercion from 'a involves an indeterminate type" — the TypeProviders
/// SDK's GetFieldInit). Such a member leaves only with its header written
/// out by the typed check, like a record builder.
let private leansOnParameters
    (check: FSharpCheckFileResults option)
    (source: ISourceText)
    (index: AstIndex.Index)
    (binding: SynBinding)
    =
    let (SynBinding(headPat = pat; expr = body)) = binding

    let bare =
        match pat with
        | SynPat.LongIdent(argPats = SynArgPats.Pats pats) ->
            pats
            |> List.choose (fun p ->
                match p with
                | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                | SynPat.Paren(SynPat.Named(ident = SynIdent(ident = id)), _) -> Some id.idText
                | _ -> None)
            |> Set.ofList
        | _ -> Set.empty

    let isInstClause (SynMatchClause(pat = p)) =
        match p with
        | SynPat.IsInst _
        | SynPat.As(SynPat.IsInst _, _, _) -> true
        | _ -> false

    // any dotted access on a bare parameter leans on the group. A record
    // label used to be exempt (`p.Index` names the record) — but standing
    // alone the compiler resolves the label to the LAST record in scope that
    // carries it, which is not necessarily the one the group inferred: the
    // F# compiler's Optimizer.fs has several records with `Info` and
    // `settings`, and a member pulled out with bare parameters failed with
    // "Lookup on object of indeterminate type". The annotated header names
    // the group's own type and costs nothing
    let memberLeans (id: Ident) (_: Ident) = bare.Contains id.idText

    not bare.IsEmpty
    && AstIndex.exprsWithin index body.Range
       |> Seq.exists (fun (_, e) ->
           Range.rangeContainsRange body.Range e.Range
           && (match e with
               | SynExpr.TypeTest(expr = SynExpr.Ident id)
               | SynExpr.Downcast(expr = SynExpr.Ident id)
               | SynExpr.DotIndexedGet(objectExpr = SynExpr.Ident id) -> bare.Contains id.idText
               | SynExpr.DotGet(expr = SynExpr.Ident id; longDotId = SynLongIdent(id = m :: _)) -> memberLeans id m
               | SynExpr.LongIdent(longDotId = SynLongIdent(id = id :: m :: _)) -> memberLeans id m
               | SynExpr.Match(expr = SynExpr.Ident id; clauses = clauses) ->
                   bare.Contains id.idText && clauses |> List.exists isInstClause
               | _ -> false))

/// The member's header line with every plain parameter annotated with the
/// type the group's inference found for it, and its return type added, so
/// the body's record expressions keep an expected type once the member
/// stands alone. None when a type cannot be written down (a generic), a
/// parameter is not a plain name or a unit, or the header spans lines.
let private annotatedHeaderLine
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (binding: SynBinding)
    (keywordRange: range)
    : string option =
    match binding with
    | SynBinding(
        headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats pats)
        returnInfo = returnInfo) when
        not pats.IsEmpty
        && pats
           |> List.forall (fun p ->
               p.Range.StartLine = keywordRange.StartLine
               && p.Range.EndLine = keywordRange.StartLine)
        ->
        let line = keywordRange.StartLine
        let lineText = source.GetLineString(line - 1)

        match OptionModule.symbolUseAt check (id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ]) with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                (try
                    let groups = v.CurriedParameterGroups
                    let writable (t: FSharpType) = t.Format symbolUse.DisplayContext

                    let isUnitPat (p: SynPat) =
                        match p with
                        | SynPat.Const(SynConst.Unit, _)
                        | SynPat.Paren(pat = SynPat.Const(SynConst.Unit, _)) -> true
                        | _ -> false

                    // one edit per parameter: (start column, end column, text)
                    let edits =
                        if groups.Count <> pats.Length then
                            None
                        else
                            List.zip pats (List.ofSeq groups)
                            |> List.map (fun (p, group) ->
                                match p with
                                | _ when isUnitPat p -> Some None
                                | SynPat.Paren(pat = SynPat.Typed _) -> Some None
                                | SynPat.Named(ident = SynIdent(ident = name)) when group.Count = 1 ->
                                    let t = writable group.[0].Type

                                    // the parameter as WRITTEN — a
                                    // backticked name keeps its backticks
                                    let written = textOfRange source p.Range

                                    if t.Contains '\'' || String.IsNullOrWhiteSpace written then
                                        None
                                    else
                                        Some(Some(p.Range.StartColumn, p.Range.EndColumn, $"({written}: {t})"))
                                | _ -> None)
                            |> List.fold
                                (fun acc e ->
                                    match acc, e with
                                    | Some acc, Some(Some edit) -> Some(edit :: acc)
                                    | Some acc, Some None -> Some acc
                                    | _ -> None)
                                (Some [])

                    let returnEdit =
                        match returnInfo with
                        | Some _ -> Some None
                        | None ->
                            let t = writable v.ReturnParameter.Type

                            if t.Contains '\'' then
                                None
                            else
                                let last = List.last pats
                                Some(Some(last.Range.EndColumn, last.Range.EndColumn, $" : {t}"))

                    match edits, returnEdit with
                    | Some edits, Some returnEdit ->
                        let all =
                            (Option.toList returnEdit @ edits) |> List.sortByDescending (fun (s, _, _) -> s)

                        let rewritten =
                            all
                            |> List.fold
                                (fun (text: string) (s, e, replacement) ->
                                    text.Substring(0, s) + replacement + text.Substring e)
                                lineText

                        Some(rewritten.Substring keywordRange.StartColumn)
                    | _ -> None
                 with _ -> // fsharpanalyzer: ignore-line FR0055
                     None)
            | _ -> None
        | None -> None
    | _ -> None

/// `check` is the typed tree when the host has one: a member that builds
/// a record leaves the group with its parameter and return types written
/// out (see `annotatedHeaderLine`), and without the typed tree such a
/// member stays where it is.
let find (check: FSharpCheckFileResults option) (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = lazy (AstIndex.ofTree parseTree)

    let decls =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
            modules |> List.collect (fun (SynModuleOrNamespace(decls = ds)) -> declsOf ds)
        | _ -> []

    [
        for decl in decls do
            match decl with
            | SynModuleDecl.Let(isRecursive = true; bindings = bindings) when bindings.Length >= 2 ->
                let names = bindings |> List.choose bindingName

                // every binding must have a recognizable name, or membership
                // is unknowable
                if names.Length = bindings.Length then
                    // each binding's text block runs from its leading keyword
                    // to the next binding's leading keyword (or the group end)
                    let keywordStarts =
                        bindings
                        |> List.map (fun (SynBinding(trivia = trivia)) -> trivia.LeadingKeyword.Range)

                    // comment lines directly above a binding's keyword belong
                    // to it and travel with it: a `///` doc, and equally a
                    // plain `//` note - left behind, the note re-attaches to
                    // whatever binding comes next (ProvidedTypes.fs's
                    // `// REVIEW: write into an accumuating buffer` headed an
                    // unrelated member once its own had moved out). A blank
                    // line ends the run, so a section banner above one stays
                    let commentStartOf i =
                        let keywordLine = (List.item i keywordStarts).StartLine
                        let mutable first = keywordLine
                        let mutable scanning = true

                        while scanning && first > 1 do
                            let above = source.GetLineString(first - 2).Trim()

                            if above.StartsWith "//" then
                                first <- first - 1
                            else
                                scanning <- false

                        first

                    // a binding's block runs from its leading keyword to the
                    // NEXT binding's own comments, not to its keyword: the doc
                    // comment above `and g` is g's, and moving f out with it
                    // orphaned five docs in the F# compiler's Optimizer.fs
                    let blockOf i =
                        let start = (List.item i keywordStarts).Start

                        let finish =
                            if i = bindings.Length - 1 then
                                decl.Range.End
                            else
                                let nextKeyword = (List.item (i + 1) keywordStarts).Start
                                let nextComments = commentStartOf (i + 1)

                                if nextComments < nextKeyword.Line then
                                    Position.mkPos nextComments 0
                                else
                                    nextKeyword

                        Range.mkRange decl.Range.FileName start finish

                    // `remaining`: the names still in the group once earlier
                    // leavers are out - membership is judged against those
                    let partFor (remaining: string list) i =
                        let keywordLine = (List.item i keywordStarts).StartLine
                        let name = List.item i names

                        let commentStartLine = commentStartOf i

                        let plainBlock = blockOf i
                        let binding = List.item i bindings

                        let rawText = textOfRange source plainBlock

                        // a record-building member leaves with its types
                        // written out, or not at all. So does any member of a
                        // file with a SIGNATURE: alone, a parameter the body
                        // never constrains (`accFreeInTupInfo _opts unt acc`,
                        // the F# compiler) generalises to 'a, and the .fsi's
                        // concrete type then fails FS0034 — inside the group
                        // the callers had pinned it
                        let signatureBeside =
                            let path = plainBlock.FileName

                            not (String.IsNullOrEmpty path)
                            && (try
                                    System.IO.File.Exists(System.IO.Path.ChangeExtension(path, ".fsi"))
                                with
                                | :? ArgumentException
                                | :? System.IO.IOException -> false)

                        let movableText =
                            if
                                buildsRecord index.Value binding.RangeOfBindingWithRhs
                                || leansOnParameters check source index.Value binding
                                || signatureBeside
                            then
                                match check with
                                | Some check ->
                                    annotatedHeaderLine check source binding (List.item i keywordStarts)
                                    |> Option.map (fun header ->
                                        let firstBreak = rawText.IndexOf '\n'

                                        if firstBreak < 0 then
                                            header
                                        else
                                            header + rawText.Substring firstBreak)
                                | None -> None
                            else
                                Some rawText

                        let bindingText = defaultArg movableText rawText

                        let companionComments =
                            [ for l in commentStartLine .. keywordLine - 1 -> source.GetLineString(l - 1) ]

                        // an INDENTED group's plain block runs keyword-to-
                        // keyword: removing it is column-symmetric and the
                        // next binding keeps its indentation. The comment-
                        // extended block starts at column 0, so it must END
                        // at column 0 too — ending at the next keyword's
                        // column ate the following `and`'s indent inside
                        // nested modules (VQC.fs, FSharp.Azure.Quantum) and
                        // left it orphaned at the margin
                        let block =
                            if commentStartLine < keywordLine then
                                let endPos =
                                    if i < bindings.Length - 1 && plainBlock.End.Column > 0 then
                                        Position.mkPos plainBlock.EndLine 0
                                    else
                                        plainBlock.End

                                Range.mkRange plainBlock.FileName (Position.mkPos commentStartLine 0) endPos
                            else
                                plainBlock

                        let (SynBinding(attributes = attrs)) = List.item i bindings

                        // membership judged on the BINDING text: a companion
                        // comment naming a sibling should not keep it in
                        let referencesGroup =
                            remaining
                            |> List.exists (fun other -> other <> name && mentions bindingText other)

                        // its own name beyond the header means self-recursion:
                        // the member still leaves, but as its own `let rec` —
                        // a plain `let` would not compile
                        let isSelfRecursive =
                            let code = codeOnly bindingText

                            referenceNames name
                            |> List.exists (fun part -> Regex.Matches(code, identifierPattern part).Count >= 2)

                        if
                            attrs.IsEmpty
                            && movableText.IsSome
                            && not referencesGroup
                            && not (spansDirective source block)
                            // the binding must start with its `and`, on its own
                            // line — mid-line groups are not worth the surgery
                            && bindingText.StartsWith "and"
                            && (source.GetLineString(plainBlock.StartLine - 1))
                                .Substring(0, plainBlock.StartColumn)
                                .Trim()
                                =
                                ""
                        then
                            let indent = String.replicate decl.Range.StartColumn " "

                            // `and f2 y = ...` becomes `let f2 y = ...`, its
                            // companion comments riding along above it
                            let commentPrefix =
                                match companionComments with
                                | [] -> ""
                                | lines -> (lines |> String.concat "\n") + $"\n{indent}"

                            let keyword = if isSelfRecursive then "let rec" else "let"
                            let extracted = commentPrefix + keyword + bindingText.Substring(3)

                            Some
                                {
                                    Block = block
                                    Extracted = extracted
                                    HasComments = commentPrefix <> ""
                                    Condition = conditionToKeep source keywordLine decl.Range.StartLine
                                    Name = name
                                    SelfRecursive = isSelfRecursive
                                }
                        else
                            None

                    let indent = String.replicate decl.Range.StartColumn " "

                    // a member under `#if` leaves under the same `#if`. A
                    // directive has to open its own line, so that form is
                    // inserted at column 0 of the group's line, ahead of its
                    // indentation - which the generated `let` line then
                    // carries itself (a raw comment line already does)
                    let conditioned (p: Part) (condition: string) =
                        let placed =
                            if p.HasComments then
                                p.Extracted.TrimEnd()
                            else
                                indent + p.Extracted.TrimEnd()

                        Range.mkRange
                            decl.Range.FileName
                            (Position.mkPos decl.Range.StartLine 0)
                            (Position.mkPos decl.Range.StartLine 0),
                        $"#if {condition}\n{placed}\n#endif\n\n"

                    // the LAST block of the group ends where the group ends,
                    // so a removal starting at its keyword leaves the line's
                    // indentation behind as a whitespace-only line
                    // (ProvidedTypes.fs:10841). Such a block starts at the end
                    // of the previous non-blank line instead - or, under a
                    // directive, at its own line's start
                    let trimmedTail (r: range) =
                        let startsOwnLine =
                            (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = ""

                        if startsOwnLine && Position.posEq r.End decl.Range.End then
                            let rec retreatL l =
                                if l > 1 && String.IsNullOrWhiteSpace(source.GetLineString(l - 1)) then
                                    retreatL (l - 1)
                                else
                                    l

                            let l = retreatL (r.StartLine - 1)

                            let previous = source.GetLineString(l - 1)

                            if previous.TrimStart().StartsWith '#' then
                                Range.mkRange r.FileName (Position.mkPos r.StartLine 0) r.End
                            else
                                Range.mkRange r.FileName (Position.mkPos l previous.Length) r.End
                        else
                            r

                    // members leave in WAVES: first those referencing no
                    // sibling, then those referencing only members already
                    // out - inserted after them, so the order still compiles.
                    // A member under its own `#if` leaves alone on a pass of
                    // its own, so it never counts as out for the members
                    // after it: the one that references it stays until then
                    let rec waves (remaining: string list) =
                        let wave =
                            [
                                for i in 1 .. bindings.Length - 1 do
                                    if List.contains (List.item i names) remaining then
                                        match partFor remaining i with
                                        | Some p -> p
                                        | None -> ()
                            ]

                        if wave.IsEmpty then
                            []
                        else
                            let gone =
                                wave |> List.filter (fun p -> p.Condition.IsNone) |> List.map (fun p -> p.Name)

                            if gone.IsEmpty then
                                [ wave ]
                            else
                                wave :: waves (remaining |> List.filter (fun n -> not (List.contains n gone)))

                    // ONE suggestion per group per pass, carrying EVERY member
                    // that can leave: they all insert at the group's start, so
                    // as separate messages only the first would apply and the
                    // rest be held back as un-appliable - and ProvidedTypes.fs's
                    // groups of twenty took a pass per member, which the
                    // divergence guard read as a fix feeding on its own
                    // output. A member under its own `#if` still leaves alone
                    match List.concat (waves names) with
                    | [] -> ()
                    | first :: _ when first.Condition.IsSome ->
                        let insertRange, insertText = conditioned first first.Condition.Value
                        let block = trimmedTail first.Block

                        {
                            RemoveRange = block
                            Removes = [ block ]
                            InsertRange = insertRange
                            InsertText = insertText
                            MemberName = first.Name
                            IsSelfRecursive = first.SelfRecursive
                            Members = [ first.Name, first.SelfRecursive ]
                        }
                    | parts ->
                        let plain = parts |> List.filter (fun p -> p.Condition.IsNone)

                        // adjacent blocks merge into one removal: an end at
                        // the next block's start, or at column 0 of the line
                        // the next block's keyword indents into (a comment-
                        // extended block ends there) - left as two, the
                        // second's tail trim would reach back into the first
                        let adjacent (prev: range) (r: range) =
                            Position.posEq prev.End r.Start
                            || (prev.EndLine = r.StartLine
                                && prev.EndColumn <= r.StartColumn
                                && (source.GetLineString(r.StartLine - 1))
                                    .Substring(prev.EndColumn, r.StartColumn - prev.EndColumn)
                                    .Trim()
                                    =
                                    "")

                        let removes =
                            plain
                            |> List.map (fun p -> p.Block)
                            |> List.sortBy (fun r -> r.StartLine, r.StartColumn)
                            |> List.fold
                                (fun (acc: range list) r ->
                                    match acc with
                                    | prev :: rest when adjacent prev r ->
                                        Range.mkRange r.FileName prev.Start r.End :: rest
                                    | _ -> r :: acc)
                                []
                            |> List.rev
                            // a merged block that starts at column 0 (a
                            // comment-extended head) must end at column 0
                            // too, as the head alone did: ending at the next
                            // keyword's column ate that `and`'s indentation
                            // and left it at the margin (ProvidedTypes.fs,
                            // "Unexpected keyword 'and'"), then
                            // the tail trimmed
                            |> List.map (fun r ->
                                let atMargin =
                                    r.StartColumn = 0
                                    && r.End.Column > 0
                                    && not (Position.posEq r.End decl.Range.End)
                                    && (source.GetLineString(r.EndLine - 1)).Substring(0, r.End.Column).Trim() = ""

                                trimmedTail (
                                    if atMargin then
                                        Range.mkRange r.FileName r.Start (Position.mkPos r.EndLine 0)
                                    else
                                        r
                                ))

                        let first = List.head plain

                        // the insert point sits AFTER the group's existing
                        // indentation: the first inserted line must not bring
                        // its own (raw comment lines carry it; inside a nested
                        // module that doubled up)
                        let insertText =
                            (plain
                             |> List.map (fun p -> p.Extracted.TrimStart().TrimEnd())
                             |> String.concat $"\n\n{indent}")
                            + $"\n\n{indent}"

                        {
                            RemoveRange = List.head removes
                            Removes = removes
                            InsertRange = Range.mkRange decl.Range.FileName decl.Range.Start decl.Range.Start
                            InsertText = insertText
                            MemberName = first.Name
                            IsSelfRecursive = first.SelfRecursive
                            Members = plain |> List.map (fun p -> p.Name, p.SelfRecursive)
                        }
            | _ -> ()
    ]

let private letRecKeywordRegex = Regex @"^let\s+rec$"

/// Head extraction: the FIRST binding of the group references no member
/// (itself included). Unlike an `and` extraction nothing moves — the
/// head already sits above the rest — so the fix is two keyword
/// rewrites: `let rec` → `let` on the head, `and` → `let rec` on the
/// next binding. Comments and attributes never enter into it.
let findHeadRecrowns
    (check: FSharpCheckFileResults option)
    (parseTree: ParsedInput)
    (source: ISourceText)
    : HeadSuggestion list =
    // an `and` extraction in the same group would overlap these keyword
    // edits; let it go first — the multi-pass loop revisits the group
    let takenGroups =
        find check parseTree source |> List.map (fun s -> s.RemoveRange.StartLine)

    let decls =
        match parseTree with
        | ParsedInput.ImplFile(ParsedImplFileInput(contents = modules)) ->
            modules |> List.collect (fun (SynModuleOrNamespace(decls = ds)) -> declsOf ds)
        | _ -> []

    [
        for decl in decls do
            match decl with
            | SynModuleDecl.Let(isRecursive = true; bindings = bindings) when bindings.Length >= 2 ->
                let names = bindings |> List.choose bindingName

                let groupHasExtraction =
                    takenGroups
                    |> List.exists (fun line -> line >= decl.Range.StartLine && line <= decl.Range.EndLine)

                if names.Length = bindings.Length && not groupHasExtraction then
                    let keywordRanges =
                        bindings
                        |> List.map (fun (SynBinding(trivia = trivia)) -> trivia.LeadingKeyword.Range)

                    let headKeyword = List.head keywordRanges
                    let andKeyword = List.item 1 keywordRanges
                    let headName = List.head names

                    // the head's text block: its keyword to the next keyword
                    let headText =
                        textOfRange source (Range.mkRange decl.Range.FileName headKeyword.Start andKeyword.Start)

                    let referencesAnyMember =
                        // itself included: a self-recursive head must keep its
                        // `rec`, and that variant is not worth the surgery.
                        // Names are checked by their USE identifiers — an
                        // active pattern is used by its case names, not its
                        // decorated `|A|_|` definition name
                        names
                        |> List.exists (fun other ->
                            let occurrencesBeyondHeader = if other = headName then 1 else 0

                            referenceNames other
                            |> List.exists (fun part ->
                                Regex.Matches(headText, identifierPattern part).Count > occurrencesBeyondHeader))

                    let startsOwnLine (r: range) =
                        (source.GetLineString(r.StartLine - 1)).Substring(0, r.StartColumn).Trim() = ""

                    if
                        not referencesAnyMember
                        && isSingleLine headKeyword
                        && letRecKeywordRegex.IsMatch(textOfRange source headKeyword)
                        && textOfRange source andKeyword = "and"
                        && startsOwnLine headKeyword
                        && startsOwnLine andKeyword
                        && not (spansDirective source decl.Range)
                    then
                        {
                            LetRecRange = headKeyword
                            AndRange = andKeyword
                            MemberName = headName
                        }
            | _ -> ()
    ]
