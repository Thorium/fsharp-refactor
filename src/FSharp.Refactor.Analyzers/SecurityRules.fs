/// Security notes:
///
/// 1. Weak cryptography (FR0065, CA5350/CA5351): MD5, SHA1, DES,
///    TripleDES and RC2 are broken for security purposes — collisions
///    and key sizes are within practical attack range. SHA-256+ and AES
///    are the drop-in families. (Non-security uses like legacy checksums
///    are a decision — this is a note, not a gate.) Also flags disabling
///    TLS certificate validation, which silently accepts any
///    man-in-the-middle.
///
/// 2. SQL built from strings (FR0066, CA2100): a command text assembled
///    by concatenation, interpolation holes, or sprintf invites
///    injection; parameters (`@name` + Parameters.AddWithValue) keep the
///    data out of the query language. The text is followed one hop: a
///    `let sql = "..." + x` bound just before `new SqlCommand(sql, con)` is
///    the same leak, and so is a dynamic string handed to `CreateCommand`
///    or to a helper whose name says it runs SQL (`executeSql`,
///    `runQuery`).
///
/// 3. Unparametrized SQL (FR0146): a command whose text is a plain
///    literal with no parameter marker at all — a full-table statement,
///    or values hard-coded into the text. Possible, but suspicious: the
///    parameters are where the values were supposed to go.
///
/// 4. Process execution from dynamic strings (FR0126).
module FSharp.Refactor.SecurityRules

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text
open System.Text.RegularExpressions

[<RequireQualifiedAccess>]
type WeakKind =
    | Hash of name: string
    | Cipher of name: string
    | CertificateBypass
    /// Ssl3/Tls/Tls11 protocol constants: broken or deprecated on the wire.
    | Protocol of name: string

type WeakCryptoSuggestion =
    {
        Range: range
        Kind: WeakKind
        /// The algorithm identifier itself, when a swap fix can target it.
        AlgoRange: range option
        /// The deprecated operand TOGETHER with the `|||` joining it to the
        /// rest — `Tls12 ||| Tls11` yields the ` ||| Tls11` span. Commenting
        /// that out retires the protocol while leaving the live one alone,
        /// and leaves the diff saying what was retired. None when the
        /// constant is not one operand of a flags-OR.
        ObsoleteOperand: range option
        /// The whole `X.SecurityProtocol <- ...` assignment, so the other
        /// offer can comment the setting out entirely and let the framework
        /// default (the OS negotiating the strongest protocol) stand.
        AssignmentRange: range option
    }

/// A dynamically built string reaching a process-execution sink — the
/// command-injection shape SonarQube's agentic-workflow rules target,
/// which matters doubly when the string carries LLM output.
type ProcessSinkSuggestion =
    {
        Range: range
        Sink: string
        /// The editor's alternative: the same arguments as a LIST —
        /// `Process.Start(file, [| "+x"; path |])`, or one
        /// `psi.ArgumentList.Add` per argument — for a template that
        /// splits into whole arguments. None when it does not.
        Fix: (range * string * string) option
    }

/// A piece of one argument: literal text, or a hole's expression text.
type private ArgumentPiece =
    | Literal of string
    | Hole of string

/// Split an interpolated template into the arguments a shell would see:
/// whitespace separates, a quote pair keeps its contents together and is
/// dropped (`+x \"{path}\"` is two arguments, the second the path itself).
/// None when a quote runs into a hole in a way this cannot follow.
let private argumentsOf (source: ISourceText) (parts: SynInterpolatedStringPart list) =
    let arguments = ResizeArray<ArgumentPiece list>()
    let current = ResizeArray<ArgumentPiece>()
    let literal = System.Text.StringBuilder()
    let mutable quoted = false
    let mutable sound = true

    let flushLiteral () =
        if literal.Length > 0 then
            current.Add(Literal(literal.ToString()))
            literal.Clear() |> ignore

    let flushArgument () =
        flushLiteral ()

        if current.Count > 0 then
            arguments.Add(List.ofSeq current)
            current.Clear()

    for part in parts do
        match part with
        | SynInterpolatedStringPart.String(text, _) ->
            for c in text do
                if c = '"' then
                    quoted <- not quoted
                elif System.Char.IsWhiteSpace c && not quoted then
                    flushArgument ()
                else
                    literal.Append c |> ignore
        | SynInterpolatedStringPart.FillExpr(expr, None) ->
            flushLiteral ()
            current.Add(Hole(textOfRange source expr.Range))
        // a format specifier (`{n:N2}`) would be lost on the way to a bare
        // hole: not worth following
        | SynInterpolatedStringPart.FillExpr(_, Some _) -> sound <- false

    flushArgument ()

    if quoted then
        sound <- false

    if sound && arguments.Count > 0 then
        Some(List.ofSeq arguments)
    else
        None

let private aZazwRegex = Regex @"^[A-Za-z_][\w'.]*$"

/// One argument as F# source: a literal, a bare hole, or an interpolated
/// string for a mix.
let private argumentText (pieces: ArgumentPiece list) =
    let escape (s: string) =
        s.Replace("\\", "\\\\").Replace("\"", "\\\"")

    match pieces with
    | [ Literal text ] -> "\"" + escape text + "\""
    | [ Hole expr ] -> if aZazwRegex.IsMatch expr then expr else $"({expr})"
    | mixed ->
        let body =
            mixed
            |> List.map (fun p ->
                match p with
                | Literal text -> escape(text).Replace("{", "{{").Replace("}", "}}")
                | Hole expr -> "{" + expr + "}")
            |> String.concat ""

        $"$\"{body}\""

/// Executables that take a COMMAND LINE by design — the string is the
/// program, not its arguments — where an argument list would change
/// what runs.
let private shells = set [ "cmd"; "cmd.exe"; "sh"; "bash"; "zsh" ]

type SqlStringSuggestion =
    {
        Range: range
        /// "CommandText", "CreateCommand", the constructor's type name, or
        /// the SQL-running helper's name.
        Sink: string
        /// The text is a plain literal with no parameter marker: not an
        /// injection, a statement that takes no values (FR0146).
        Unparametrized: bool
    }

let private weakHashes = set [ "MD5"; "SHA1" ]

let private weakHashTypes =
    set
        [
            "MD5CryptoServiceProvider"
            "SHA1CryptoServiceProvider"
            "SHA1Managed"
            "MD5Cng"
        ]

let private weakCiphers = set [ "DES"; "TripleDES"; "RC2" ]

let private weakCipherTypes =
    set
        [
            "DESCryptoServiceProvider"
            "TripleDESCryptoServiceProvider"
            "RC2CryptoServiceProvider"
        ]

let private commandTypes =
    set
        [
            "SqlCommand"
            "NpgsqlCommand"
            "MySqlCommand"
            "OracleCommand"
            "SqliteCommand"
            "SQLiteCommand"
        ]

/// A helper whose name says it runs SQL: `executeSql`, `runQuery`,
/// `ExecuteSql`, `sqlExec`, `queryDb`...
let private sqlHelperName =
    Regex(
        @"^(?i)(execute|exec|run|query|read|fetch|select)\w*(sql|query|db)\w*$|^(?i)sql\w*(execute|exec|run|query|read)\w*$",
        RegexOptions.Compiled
    )

/// SELECT/INSERT/UPDATE/DELETE text: a statement that takes values.
let private dmlStatement =
    Regex(@"^\s*(select|insert|update|delete|merge)\b", RegexOptions.Compiled ||| RegexOptions.IgnoreCase)

/// `@name`, `:name`, `?`, `$1` — a parameter marker in any dialect.
let private parameterMarker = Regex(@"@\w|:\w|\?|\$\d", RegexOptions.Compiled)

[<return: Struct>]
let private (|Addition|_|) (e: SynExpr) =
    match e with
    // infix + parses its operator as a one-segment LongIdent, not Ident
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Addition"; argExpr = l); argExpr = r) ->
        ValueSome(l, r)
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])); argExpr = l)
        argExpr = r) when op.idText = "op_Addition" -> ValueSome(l, r)
    | _ -> ValueNone

/// The curried arguments of an application, innermost first:
/// `sprintf fmt a b` gives `[sprintf; fmt; a; b]`.
let rec private appChain (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) -> appChain f @ [ a ]
    | other -> [ other ]

/// The pieces a string is assembled from: an interpolation's holes, a `+`
/// chain's operands, or a sprintf/String.Format call's arguments (the
/// format itself is a literal). None for any other expression.
let private assembledParts (e: SynExpr) =
    let rec operands (x: SynExpr) =
        match stripParens x with
        | Addition(l, r) -> operands l @ operands r
        | other -> [ other ]

    match stripParens e with
    | SynExpr.InterpolatedString(contents = parts) ->
        parts
        |> List.choose (fun p ->
            match p with
            | SynInterpolatedStringPart.FillExpr(expr, _) -> Some expr
            | SynInterpolatedStringPart.String _ -> None)
        |> Some
    | Addition _ as sum -> Some(operands sum)
    | SynExpr.App(isInfix = false) as app ->
        match appChain app with
        | SingleIdent f :: _format :: args when f.idText = "sprintf" -> Some args
        | [ SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); arg ] when
            ids.Length >= 2
            && (List.last ids).idText = "Format"
            && ids.[ids.Length - 2].idText = "String"
            ->
            match stripParens arg with
            | SynExpr.Tuple(exprs = _format :: args) -> Some args
            | _ -> None
        | _ -> None
    | _ -> None

/// A string expression assembled from VALUES: interpolation with holes,
/// a `+` chain, or a sprintf/String.Format call — where at least one hole,
/// operand or argument is not a compile-time constant. `isConstant` says
/// what counts as one (a literal, or a name bound immutably to one): a
/// `SET search_path = "{schema}"` whose schema is a module constant is a
/// statement the author wrote, not one the caller can bend, and there is
/// no parameter to move the name into anyway.
let private isDynamicStringWith (isConstant: SynExpr -> bool) (e: SynExpr) =
    match assembledParts e with
    | Some parts -> parts |> List.exists (isConstant >> not)
    | None -> false

/// The purely syntactic reading: every hole, operand and argument is a
/// value, literals apart.
let private isDynamicString (e: SynExpr) =
    isDynamicStringWith
        (fun x ->
            match stripParens x with
            | SynExpr.Const _ -> true
            | _ -> false)
        e

let private bindsName (name: string) (SynBinding(headPat = p)) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = name
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) -> id.idText = name
    | _ -> false

/// Protocol constants known to be broken or deprecated on the wire. A
/// CURATED list, because the framework marks its own inconsistently:
/// `SslProtocols.Tls11` carries [<Obsolete>] while
/// `SecurityProtocolType.Tls11` — the one real code actually sets — does not,
/// a decade after TLS 1.1 was deprecated. `isObsoleteProtocol` adds whatever
/// the framework HAS marked, so a release that retires more needs none of
/// ours; neither signal alone is enough.
let private legacyProtocols = set [ "Ssl2"; "Ssl3"; "Tls"; "Tls11" ]

/// Find weak cryptography, string-built SQL, and string-built process
/// execution.
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    (isObsoleteProtocol: range -> bool)
    : WeakCryptoSuggestion list * SqlStringSuggestion list * ProcessSinkSuggestion list =

    let index = AstIndex.ofTree parseTree
    let crypto = ResizeArray<WeakCryptoSuggestion>()
    let sql = ResizeArray<SqlStringSuggestion>()
    let processSinks = ResizeArray<ProcessSinkSuggestion>()

    let moduleBindingOf (name: string) =
        index.Decls
        |> Array.tryPick (fun (_, decl) ->
            match decl with
            | SynModuleDecl.Let(bindings = bindings) -> bindings |> List.tryFind (bindsName name)
            | _ -> None)

    let binderName (p: SynPat) =
        match p with
        | SynPat.Named(ident = SynIdent(ident = ident)) -> Some ident.idText
        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ ident ]); argPats = SynArgPats.Pats []) -> Some ident.idText
        | _ -> None

    // a lambda's arguments are not in the index's patterns: gather the
    // names they bind straight from the lambda
    let rec namesBoundBy (p: SynPat) : (string * range) list =
        let own = binderName p |> Option.map (fun n -> n, p.Range) |> Option.toList

        let children =
            match p with
            | SynPat.Paren(pat = inner)
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner) -> [ inner ]
            | SynPat.As(lhsPat = l; rhsPat = r)
            | SynPat.Or(lhsPat = l; rhsPat = r)
            | SynPat.ListCons(lhsPat = l; rhsPat = r) -> [ l; r ]
            | SynPat.Ands(pats = ps)
            | SynPat.Tuple(elementPats = ps)
            | SynPat.ArrayOrList(elementPats = ps) -> ps
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> ps
            | _ -> []

        own @ List.collect namesBoundBy children

    // the binders of each name in the file, with the range each one scopes
    // over: a pattern's first non-pattern ancestor - the function binding
    // whose parameter it is, the match arm, loop or `let!` that introduces
    // it - and a lambda for its arguments. A value `let` reaches past its own
    // binding, over the whole container it sits in: the `let ... in` block,
    // the class body (`type Repo(input) = let q = input`), the module (a
    // nested module's `let q = input` hides the file's `let q = "SELECT 1"`).
    // A primary constructor's parameters reach the whole type, not just the
    // constructor's argument list
    let bindersByName =
        lazy
            (let fromPatterns =
                index.Pats
                |> Array.choose (fun (patPath, p) ->
                    let container (outer: SyntaxNode list) =
                        match outer with
                        | SyntaxNode.SynExpr(LetOrUseE _ as letOrUse) :: _ -> Some letOrUse.Range
                        | SyntaxNode.SynMemberDefn(SynMemberDefn.LetBindings _) :: typeDefn :: _
                        | SyntaxNode.SynModule(SynModuleDecl.Let _) :: typeDefn :: _ -> Some typeDefn.Range
                        | _ -> None

                    let scope =
                        match
                            patPath
                            |> List.skipWhile (fun node ->
                                match node with
                                | SyntaxNode.SynPat _ -> true
                                | _ -> false)
                        with
                        | SyntaxNode.SynMemberDefn(SynMemberDefn.ImplicitCtor _) :: rest ->
                            rest |> List.tryHead |> Option.map (fun node -> node.Range)
                        // a value binding, not a function's parameter
                        | SyntaxNode.SynBinding(SynBinding(headPat = head)) as binding :: outer when
                            (match head with
                             | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> false
                             | _ -> true)
                            ->
                            container outer |> Option.orElse (Some binding.Range)
                        | node :: _ -> Some node.Range
                        | [] -> None

                    binderName p |> Option.map (fun n -> n, (p.Range, scope)))

             let fromLambdas =
                 index.Exprs
                 |> Array.collect (fun (_, e) ->
                     match e with
                     | SynExpr.Lambda(parsedData = Some(args, _)) ->
                         args
                         |> List.collect namesBoundBy
                         |> List.map (fun (n, r) -> n, (r, Some e.Range))
                         |> List.toArray
                     | _ -> [||])

             Array.append fromPatterns fromLambdas
             |> Array.groupBy fst
             |> Array.map (fun (n, binders) -> n, binders |> Array.map snd)
             |> Map.ofArray)

    // a use of `name` that `binding` does not reach: another binder of the
    // same name - a parameter, a lambda or match-arm argument (`let schema =
    // "app"` at module level and a `schema` parameter in the sink's
    // function) - scopes over the use, or the use sits in the binding's own
    // right-hand side, where a non-recursive `let` still reads the outer
    // name. A `let` of the same name in ANOTHER function scopes over
    // nothing here: SQLProvider binds `baseQuery` once per member
    let shadowed (SynBinding(headPat = own) as binding) (useRange: range) (name: string) =
        Range.rangeContainsRange binding.RangeOfBindingWithRhs useRange
        || (match bindersByName.Value.TryFind name with
            | None -> false
            | Some binders ->
                binders
                |> Array.exists (fun (patRange, scope) ->
                    not (Range.rangeContainsRange own.Range patRange)
                    && (match scope with
                        // between the binding and the use; a binder whose
                        // scope holds the binding too is an outer one it
                        // hides - unless it comes AFTER the binding and
                        // before the use, a script's top-level `let q =
                        // input` redefining the `let q = "SELECT 1"` above
                        | Some scopeRange ->
                            let bindingRange = binding.RangeOfBindingWithRhs

                            Range.rangeContainsRange scopeRange useRange
                            && (not (Range.rangeContainsRange scopeRange bindingRange)
                                || (Position.posGt patRange.Start bindingRange.End
                                    && Position.posLt patRange.Start useRange.Start))
                        | None -> true)))

    // where a binding's right-hand side reads its names: a local `let` from
    // its enclosing node outward (`let q = q + "x"` reads the outer q), a
    // module-level one at module level
    let bindingWithScope (path: SyntaxNode list) (name: string) =
        let rec local (nodes: SyntaxNode list) =
            match nodes with
            | [] -> None
            | (SyntaxNode.SynExpr(LetOrUseE lou) :: outer) ->
                match lou.Bindings |> List.tryFind (bindsName name) with
                | Some b -> Some(b, outer)
                | None -> local outer
            | _ :: outer -> local outer

        match local path with
        | Some found -> Some found
        | None -> moduleBindingOf name |> Option.map (fun b -> b, [])

    // the text expression one hop resolved, with the path its names are
    // read in: the binding's own scope, not the sink's - a `let table =
    // "users"` between `let sql = $"... {table} ..."` and the sink is not
    // the `table` the text read; a module-level definition's names are
    // module-level too, never the sink's locals
    let resolved (path: SyntaxNode list) (e: SynExpr) =
        match stripParens e with
        | SynExpr.Ident id ->
            match bindingWithScope path id.idText with
            | Some(SynBinding(expr = rhs) as b, rhsScope) when not (shadowed b id.idRange id.idText) ->
                stripParens rhs, rhsScope
            | _ -> e, path
        | other -> other, path

    // `Module.name`: a binding directly in this file's module (or a nested
    // module) of that name - not one in a module nested deeper, which
    // `Module.name` does not reach
    let qualifiedBindingOf (ids: Ident list) =
        match List.rev ids with
        | name :: owner :: _ ->
            let ownedBy (declPath: SyntaxNode list) =
                declPath
                |> List.tryPick (fun node ->
                    match node with
                    | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = lid))) ->
                        Some((List.last lid).idText = owner.idText)
                    | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(longId = lid; kind = kind)) ->
                        Some(kind.IsModule && not lid.IsEmpty && (List.last lid).idText = owner.idText)
                    | _ -> None)
                |> Option.defaultValue false

            index.Decls
            |> Array.tryPick (fun (declPath, decl) ->
                match decl with
                | SynModuleDecl.Let(bindings = bindings) when ownedBy declPath ->
                    bindings |> List.tryFind (bindsName name.idText)
                | _ -> None)
        | _ -> None

    // a compile-time constant, all the way down: a literal; an
    // interpolation, `+` chain, sprintf or String.Format whose every hole,
    // operand and argument is one; or a name bound IMMUTABLY to one - in
    // scope at the use, or `Module.name`. `let mutable schema = "public"`
    // is a value, because a later `schema <- input` makes it one; a
    // function parameter resolves to nothing and stays a value. `depth`
    // bounds the walk through names
    let rec constantAt depth path (e: SynExpr) =
        depth > 0
        && (match stripParens e with
            | SynExpr.Const(SynConst.Unit, _) -> false
            | SynExpr.Const _ -> true
            | SynExpr.Typed(expr = inner) -> constantAt depth path inner
            | SynExpr.Ident id ->
                match bindingWithScope path id.idText with
                | Some(SynBinding(isMutable = false; expr = rhs) as b, rhsScope) ->
                    not (shadowed b id.idRange id.idText) && constantAt (depth - 1) rhsScope rhs
                | _ -> false
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                match qualifiedBindingOf ids with
                | Some(SynBinding(isMutable = false; expr = rhs)) -> constantAt (depth - 1) [] rhs
                | _ -> false
            | other ->
                match assembledParts other with
                | Some parts -> parts |> List.forall (constantAt depth path)
                | None -> false)

    let dynamicText path e =
        let text, scope = resolved path e
        isDynamicStringWith (constantAt 6 scope) text

    // a plain-literal DML statement without a single parameter marker
    let unparametrizedText path e =
        match resolved path e with
        | SynExpr.Const(SynConst.String(text, _, _), _), _ ->
            dmlStatement.IsMatch text && not (parameterMarker.IsMatch text)
        | _ -> false

    let addSql path (range: range) (sink: string) (text: SynExpr) =
        if dynamicText path text then
            sql.Add
                {
                    Range = range
                    Sink = sink
                    Unparametrized = false
                }
        elif unparametrizedText path text then
            sql.Add
                {
                    Range = range
                    Sink = sink
                    Unparametrized = true
                }

    let firstArg (arg: SynExpr) =
        match stripParens arg with
        | SynExpr.Tuple(exprs = head :: _) -> head
        | single -> single

    // RFC 6455 mandates SHA-1 for the WebSocket handshake: Sec-WebSocket-
    // Accept is SHA-1 of the key and this GUID, and nothing else will do.
    // A file spelling the GUID is a WebSocket server, and its SHA1
    // is the protocol, not a choice
    let webSocketHandshake =
        lazy
            (index.Exprs
             |> Array.exists (fun (_, e) ->
                 match e with
                 | SynExpr.Const(SynConst.String(text = text), _) ->
                     text.Equals("258EAFA5-E914-47DA-95CA-C5AB0DC85B11", System.StringComparison.OrdinalIgnoreCase)
                 | _ -> false))

    // SHA1 constructed in one arm of a match whose sibling arm constructs
    // SHA256 or stronger: a format option the caller chose — a
    // `--checksumalgorithm` switch, say — with the strong algorithm already
    // on offer
    let strongerSibling (path: SyntaxNode list) =
        let strongHash (names: Ident list) =
            names
            |> List.exists (fun i ->
                match i.idText with
                | "SHA256"
                | "SHA384"
                | "SHA512" -> true
                | _ -> false)

        let constructsStrong (r: range) =
            AstIndex.exprsWithin index r
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (match e with
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> strongHash ids
                    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) -> strongHash ids
                    | _ -> false))

        let rec toMatch (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynMatchClause own :: SyntaxNode.SynExpr(SynExpr.Match(clauses = clauses)) :: _ ->
                Some(own, clauses)
            | SyntaxNode.SynMatchClause own :: SyntaxNode.SynExpr(SynExpr.MatchLambda(matchClauses = clauses)) :: _ ->
                Some(own, clauses)
            | SyntaxNode.SynMatchClause _ :: _
            | [] -> None
            | _ :: rest -> toMatch rest

        match toMatch path with
        | Some(own, clauses) ->
            clauses
            |> List.exists (fun sibling -> not (Range.equals sibling.Range own.Range) && constructsStrong sibling.Range)
        | None -> false

    let sha1Sanctioned (path: SyntaxNode list) =
        webSocketHandshake.Value || strongerSibling path

    for path, e in index.Exprs do
        match e with
        // MD5.Create() / SHA1.Create() / DES.Create() ...
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
            ids.Length >= 2 && (List.last ids).idText = "Create"
            ->
            match List.rev ids with
            | _create :: ownerId :: _ ->
                let owner = ownerId.idText

                if owner = "SHA1" && sha1Sanctioned path then
                    ()
                elif weakHashes.Contains owner then
                    crypto.Add
                        {
                            Range = e.Range
                            Kind = WeakKind.Hash owner
                            AlgoRange = Some ownerId.idRange
                            ObsoleteOperand = None
                            AssignmentRange = None
                        }
                elif weakCiphers.Contains owner then
                    crypto.Add
                        {
                            Range = e.Range
                            Kind = WeakKind.Cipher owner
                            AlgoRange = Some ownerId.idRange
                            ObsoleteOperand = None
                            AssignmentRange = None
                        }
            | _ -> ()
        // new MD5CryptoServiceProvider() and friends
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
            let name = (List.last ids).idText

            if name.StartsWith "SHA1" && sha1Sanctioned path then
                ()
            elif weakHashTypes.Contains name then
                crypto.Add
                    {
                        Range = e.Range
                        Kind = WeakKind.Hash name
                        AlgoRange = None
                        ObsoleteOperand = None
                        AssignmentRange = None
                    }
            elif weakCipherTypes.Contains name then
                crypto.Add
                    {
                        Range = e.Range
                        Kind = WeakKind.Cipher name
                        AlgoRange = None
                        ObsoleteOperand = None
                        AssignmentRange = None
                    }
            elif commandTypes.Contains name then
                // new SqlCommand(sql, ...)
                match e with
                | SynExpr.New(expr = arg) -> addSql path e.Range name (firstArg arg)
                | _ -> ()
            elif name = "ProcessStartInfo" then
                // new ProcessStartInfo(dynamicFile, dynamicArgs): the
                // command/argument-injection sink
                match e with
                | SynExpr.New(expr = arg) ->
                    let argsOf =
                        match stripParens arg with
                        | SynExpr.Tuple(exprs = es) -> es
                        | single -> [ single ]

                    if argsOf |> List.exists isDynamicString then
                        processSinks.Add
                            {
                                Range = e.Range
                                Sink = "ProcessStartInfo"
                                Fix = None
                            }
                | _ -> ()
        // SqlCommand(sql, ...) without `new`
        | SynExpr.App(isInfix = false; funcExpr = SingleIdent ctor; argExpr = arg) when
            commandTypes.Contains ctor.idText
            ->
            addSql path e.Range ctor.idText (firstArg arg)
        // con.CreateCommand(con, sql) — SQLProvider's spelling; the plain
        // BCL CreateCommand() takes no text and matches nothing here
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
            ids.Length >= 2 && (List.last ids).idText = "CreateCommand"
            ->
            match stripParens arg with
            | SynExpr.Tuple(exprs = [ _; text ]) -> addSql path e.Range "CreateCommand" text
            | _ -> ()
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = [ m ])); argExpr = arg) when
            m.idText = "CreateCommand"
            ->
            match stripParens arg with
            | SynExpr.Tuple(exprs = [ _; text ]) -> addSql path e.Range "CreateCommand" text
            | _ -> ()
        // executeSql (dynamic) / ExecuteSql (dynamic, ...): a helper that
        // says it runs SQL, judged by its name
        | SynExpr.App(isInfix = false; funcExpr = SingleIdent helper; argExpr = arg) when
            sqlHelperName.IsMatch helper.idText
            ->
            if dynamicText path (firstArg arg) then
                sql.Add
                    {
                        Range = e.Range
                        Sink = helper.idText
                        Unparametrized = false
                    }
            // `ReadSqlInteger "select max(id) from events" []`: a literal
            // statement and an EMPTY parameter list handed to the helper —
            // the same no-parameter command, one call further out
            elif unparametrizedText path (firstArg arg) then
                let emptyParameters =
                    match path with
                    | SyntaxNode.SynExpr(SynExpr.App(argExpr = SynExpr.ArrayOrList(exprs = []))) :: _ -> true
                    | SyntaxNode.SynExpr(SynExpr.App(
                        argExpr = SynExpr.ArrayOrListComputed(expr = SynExpr.Const(SynConst.Unit, _)))) :: _ -> true
                    | _ -> false

                if emptyParameters then
                    sql.Add
                        {
                            Range = e.Range
                            Sink = helper.idText
                            Unparametrized = true
                        }
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
            ids.Length >= 2
            && sqlHelperName.IsMatch (List.last ids).idText
            && dynamicText path (firstArg arg)
            ->
            sql.Add
                {
                    Range = e.Range
                    Sink = (List.last ids).idText
                    Unparametrized = false
                }
        // cmd.CommandText <- sql; cert validation bypass
        | SynExpr.LongIdentSet(SynLongIdent(id = ids), rhs, _) when not ids.IsEmpty ->
            match (List.last ids).idText with
            | "CommandText" -> addSql path e.Range "CommandText" rhs
            | "ServerCertificateValidationCallback"
            | "ServerCertificateCustomValidationCallback" ->
                crypto.Add
                    {
                        Range = e.Range
                        Kind = WeakKind.CertificateBypass
                        AlgoRange = None
                        ObsoleteOperand = None
                        AssignmentRange = None
                    }
            // psi.Arguments <- dynamic: the argument-injection sink;
            // FileName is any DTO's field and stays out
            | "Arguments" when isDynamicString rhs ->
                // the alternative: one ArgumentList.Add per argument. The
                // executable is not in view here, so a template carrying
                // quotes — a command line for a shell, most likely — is left
                let fix =
                    match stripParens rhs with
                    | SynExpr.InterpolatedString(contents = parts) when
                        parts
                        |> List.forall (fun p ->
                            match p with
                            | SynInterpolatedStringPart.String(text, _) -> not (text.Contains '"')
                            | SynInterpolatedStringPart.FillExpr _ -> true)
                        ->
                        argumentsOf source parts
                        |> Option.map (fun args ->
                            let receiver = ids |> List.take (ids.Length - 1) |> identText
                            let indent = String.replicate e.Range.StartColumn " "

                            let lines =
                                args
                                |> List.map (fun a -> $"{receiver}.ArgumentList.Add {argumentText a}")
                                |> String.concat ("\n" + indent)

                            e.Range, textOfRange source e.Range, lines)
                    | _ -> None

                processSinks.Add
                    {
                        Range = e.Range
                        Sink = "Arguments"
                        Fix = fix
                    }
            | _ -> ()
        | SynExpr.DotSet(_, SynLongIdent(id = ids), rhs, _) when not ids.IsEmpty ->
            match (List.last ids).idText with
            | "CommandText" -> addSql path e.Range "CommandText" rhs
            | "ServerCertificateValidationCallback"
            | "ServerCertificateCustomValidationCallback" ->
                crypto.Add
                    {
                        Range = e.Range
                        Kind = WeakKind.CertificateBypass
                        AlgoRange = None
                        ObsoleteOperand = None
                        AssignmentRange = None
                    }
            | "Arguments" when isDynamicString rhs ->
                processSinks.Add
                    {
                        Range = e.Range
                        Sink = "Arguments"
                        Fix = None
                    }
            | _ -> ()
        // Process.Start with a dynamically built command — the
        // command-injection sink; distinctive by name, so no typed gate
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = pids)); argExpr = parg) when
            pids.Length >= 2
            && (List.last pids).idText = "Start"
            && (pids |> List.item (pids.Length - 2)).idText = "Process"
            ->
            let argsOf =
                match stripParens parg with
                | SynExpr.Tuple(exprs = es) -> es
                | single -> [ single ]

            if argsOf |> List.exists isDynamicString then
                // the alternative: `Process.Start(file, [| ... |])` — for a
                // fixed executable that is not a shell (a shell takes a
                // command line by design, and a list would change what runs)
                let fix =
                    match argsOf with
                    | [ file; (SynExpr.InterpolatedString(contents = parts) as template) ] when
                        not (isDynamicString file)
                        ->
                        // a literal executable is known to be a shell or not; an
                        // executable bound elsewhere is unknown, and a template
                        // carrying quotes behind it reads like a shell's command
                        // line — left alone
                        let isShell, known =
                            match stripParens file with
                            | SynExpr.Const(SynConst.String(name, _, _), _) ->
                                shells.Contains(System.IO.Path.GetFileName(name).ToLowerInvariant()), true
                            | _ -> false, false

                        let quoted =
                            parts
                            |> List.exists (fun p ->
                                match p with
                                | SynInterpolatedStringPart.String(text, _) -> text.Contains '"'
                                | SynInterpolatedStringPart.FillExpr _ -> false)

                        if isShell || (not known && quoted) then
                            None
                        else
                            argumentsOf source parts
                            |> Option.map (fun args ->
                                template.Range,
                                textOfRange source template.Range,
                                "[| " + (args |> List.map argumentText |> String.concat "; ") + " |]")
                    | _ -> None

                processSinks.Add
                    {
                        Range = e.Range
                        Sink = "Process.Start"
                        Fix = fix
                    }
        // SecurityProtocolType.Ssl3 / SslProtocols.Tls11 and friends:
        // broken or deprecated on the wire. The modern default is to set
        // NOTHING and let the OS negotiate
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
            match (ids |> List.item (ids.Length - 2)).idText, (List.last ids).idText with
            | ("SecurityProtocolType" | "SslProtocols"), proto when
                legacyProtocols.Contains proto || isObsoleteProtocol (List.last ids).idRange
                ->
                // The `|||` joining this constant to the rest, taken from the
                // SOURCE: it sits immediately beside the constant by
                // definition, and reading the token beats guessing at how FCS
                // shapes an infix application. The span carries the operator
                // with it so commenting it out leaves valid F# either way:
                //     Tls12 (* ||| Tls11 *)      (* Tls11 ||| *) Tls12
                let obsoleteOperand =
                    let startLine = source.GetLineString(e.Range.StartLine - 1)
                    let endLine = source.GetLineString(e.Range.EndLine - 1)

                    let before =
                        if e.Range.StartColumn <= startLine.Length then
                            startLine.Substring(0, e.Range.StartColumn).TrimEnd()
                        else
                            ""

                    let after =
                        if e.Range.EndColumn <= endLine.Length then
                            endLine.Substring(e.Range.EndColumn).TrimStart()
                        else
                            ""

                    if before.EndsWith "|||" then
                        Some(
                            Range.mkRange
                                e.Range.FileName
                                (Position.mkPos e.Range.StartLine (before.Length - 3))
                                e.Range.End
                        )
                    elif after.StartsWith "|||" then
                        Some(
                            Range.mkRange
                                e.Range.FileName
                                e.Range.Start
                                (Position.mkPos e.Range.EndLine (endLine.Length - after.Length + 3))
                        )
                    else
                        None

                let assignmentRange =
                    index.Exprs
                    |> Array.choose (fun (_, candidate) ->
                        match candidate with
                        | SynExpr.LongIdentSet _
                        | SynExpr.DotSet _
                        | SynExpr.Set _ when Range.rangeContainsRange candidate.Range e.Range -> Some candidate.Range
                        | _ -> None)
                    |> Array.sortBy (fun r -> r.EndLine - r.StartLine, r.EndColumn)
                    |> Array.tryHead

                crypto.Add
                    {
                        Range = e.Range
                        Kind = WeakKind.Protocol proto
                        // the constant ident itself: the Tls12 swap's target
                        AlgoRange = Some (List.last ids).idRange
                        ObsoleteOperand = obsoleteOperand
                        AssignmentRange = assignmentRange
                    }
            | _ -> ()
        | _ -> ()

    List.ofSeq crypto, List.ofSeq sql, List.ofSeq processSinks
