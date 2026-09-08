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

/// One argument as F# source: a literal, a bare hole, or an interpolated
/// string for a mix.
let private argumentText (pieces: ArgumentPiece list) =
    let escape (s: string) =
        s.Replace("\\", "\\\\").Replace("\"", "\\\"")

    match pieces with
    | [ Literal text ] -> "\"" + escape text + "\""
    | [ Hole expr ] ->
        if Regex.IsMatch(expr, @"^[A-Za-z_][\w'.]*$") then
            expr
        else
            $"({expr})"
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
        [ "MD5CryptoServiceProvider"
          "SHA1CryptoServiceProvider"
          "SHA1Managed"
          "MD5Cng" ]

let private weakCiphers = set [ "DES"; "TripleDES"; "RC2" ]

let private weakCipherTypes =
    set
        [ "DESCryptoServiceProvider"
          "TripleDESCryptoServiceProvider"
          "RC2CryptoServiceProvider" ]

let private commandTypes =
    set
        [ "SqlCommand"
          "NpgsqlCommand"
          "MySqlCommand"
          "OracleCommand"
          "SqliteCommand"
          "SQLiteCommand" ]

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

/// A string expression assembled at runtime: interpolation with holes,
/// a `+` chain, or a sprintf/String.Format call.
let private isDynamicString (e: SynExpr) =
    match stripParens e with
    | SynExpr.InterpolatedString(contents = parts) ->
        parts
        |> List.exists (fun p ->
            match p with
            | SynInterpolatedStringPart.FillExpr _ -> true
            | SynInterpolatedStringPart.String _ -> false)
    // infix + parses its operator as a one-segment LongIdent, not Ident
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Addition")) -> true
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])))) when
        op.idText = "op_Addition"
        ->
        true
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent f)) when f.idText = "sprintf" -> true
    | SynExpr.App(funcExpr = SingleIdent f) when f.idText = "sprintf" -> true
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        ids.Length >= 2
        && (List.last ids).idText = "Format"
        && ids.[ids.Length - 2].idText = "String"
        ->
        true
    | _ -> false

let private bindsName (name: string) (SynBinding(headPat = p)) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText = name
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) -> id.idText = name
    | _ -> false

/// Find weak cryptography, string-built SQL, and string-built process
/// execution.
let find
    (parseTree: ParsedInput)
    (source: ISourceText)
    : WeakCryptoSuggestion list * SqlStringSuggestion list * ProcessSinkSuggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree
    let crypto = ResizeArray<WeakCryptoSuggestion>()
    let sql = ResizeArray<SqlStringSuggestion>()
    let processSinks = ResizeArray<ProcessSinkSuggestion>()

    // an identifier's right-hand side, one hop: the nearest enclosing
    // `let x = ...` on the path, else a module-level `let x = ...` of this
    // file. A function parameter resolves to nothing — the caller is
    // where the string was built, and the caller's site is the one
    // reported
    let definitionOf (path: SyntaxNode list) (name: string) =
        let local =
            path
            |> List.tryPick (fun node ->
                match node with
                | SyntaxNode.SynExpr(LetOrUseE lou) ->
                    lou.Bindings
                    |> List.tryPick (fun b ->
                        if bindsName name b then
                            let (SynBinding(expr = rhs)) = b
                            Some rhs
                        else
                            None)
                | _ -> None)

        match local with
        | Some rhs -> Some rhs
        | None ->
            index.Decls
            |> Array.tryPick (fun (_, decl) ->
                match decl with
                | SynModuleDecl.Let(bindings = bindings) ->
                    bindings
                    |> List.tryPick (fun b ->
                        if bindsName name b then
                            let (SynBinding(expr = rhs)) = b
                            Some rhs
                        else
                            None)
                | _ -> None)

    let resolved (path: SyntaxNode list) (e: SynExpr) =
        match stripParens e with
        | SynExpr.Ident id ->
            match definitionOf path id.idText with
            | Some rhs -> stripParens rhs
            | None -> e
        | other -> other

    let dynamicText path e = isDynamicString (resolved path e)

    // a plain-literal DML statement without a single parameter marker
    let unparametrizedText path e =
        match resolved path e with
        | SynExpr.Const(SynConst.String(text, _, _), _) ->
            dmlStatement.IsMatch text && not (parameterMarker.IsMatch text)
        | _ -> false

    let addSql path (range: range) (sink: string) (text: SynExpr) =
        if dynamicText path text then
            sql.Add
                { Range = range
                  Sink = sink
                  Unparametrized = false }
        elif unparametrizedText path text then
            sql.Add
                { Range = range
                  Sink = sink
                  Unparametrized = true }

    let firstArg (arg: SynExpr) =
        match stripParens arg with
        | SynExpr.Tuple(exprs = head :: _) -> head
        | single -> single

    // RFC 6455 mandates SHA-1 for the WebSocket handshake: Sec-WebSocket-
    // Accept is SHA-1 of the key and this GUID, and nothing else will do.
    // A file spelling the GUID is a WebSocket server (Suave), and its SHA1
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
    // SHA256 or stronger: a format option the caller chose — the F#
    // compiler's --checksumalgorithm — with the strong algorithm already
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
            index.Exprs
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
                        { Range = e.Range
                          Kind = WeakKind.Hash owner
                          AlgoRange = Some ownerId.idRange }
                elif weakCiphers.Contains owner then
                    crypto.Add
                        { Range = e.Range
                          Kind = WeakKind.Cipher owner
                          AlgoRange = Some ownerId.idRange }
            | _ -> ()
        // new MD5CryptoServiceProvider() and friends
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
            let name = (List.last ids).idText

            if name.StartsWith "SHA1" && sha1Sanctioned path then
                ()
            elif weakHashTypes.Contains name then
                crypto.Add
                    { Range = e.Range
                      Kind = WeakKind.Hash name
                      AlgoRange = None }
            elif weakCipherTypes.Contains name then
                crypto.Add
                    { Range = e.Range
                      Kind = WeakKind.Cipher name
                      AlgoRange = None }
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
                            { Range = e.Range
                              Sink = "ProcessStartInfo"
                              Fix = None }
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
                    { Range = e.Range
                      Sink = helper.idText
                      Unparametrized = false }
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
                        { Range = e.Range
                          Sink = helper.idText
                          Unparametrized = true }
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
            ids.Length >= 2
            && sqlHelperName.IsMatch (List.last ids).idText
            && dynamicText path (firstArg arg)
            ->
            sql.Add
                { Range = e.Range
                  Sink = (List.last ids).idText
                  Unparametrized = false }
        // cmd.CommandText <- sql; cert validation bypass
        | SynExpr.LongIdentSet(SynLongIdent(id = ids), rhs, _) when not ids.IsEmpty ->
            match (List.last ids).idText with
            | "CommandText" -> addSql path e.Range "CommandText" rhs
            | "ServerCertificateValidationCallback"
            | "ServerCertificateCustomValidationCallback" ->
                crypto.Add
                    { Range = e.Range
                      Kind = WeakKind.CertificateBypass
                      AlgoRange = None }
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
                    { Range = e.Range
                      Sink = "Arguments"
                      Fix = fix }
            | _ -> ()
        | SynExpr.DotSet(_, SynLongIdent(id = ids), rhs, _) when not ids.IsEmpty ->
            match (List.last ids).idText with
            | "CommandText" -> addSql path e.Range "CommandText" rhs
            | "ServerCertificateValidationCallback"
            | "ServerCertificateCustomValidationCallback" ->
                crypto.Add
                    { Range = e.Range
                      Kind = WeakKind.CertificateBypass
                      AlgoRange = None }
            | "Arguments" when isDynamicString rhs ->
                processSinks.Add
                    { Range = e.Range
                      Sink = "Arguments"
                      Fix = None }
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
                    { Range = e.Range
                      Sink = "Process.Start"
                      Fix = fix }
        // SecurityProtocolType.Ssl3 / SslProtocols.Tls11 and friends:
        // broken or deprecated on the wire. The modern default is to set
        // NOTHING and let the OS negotiate
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
            match (ids |> List.item (ids.Length - 2)).idText, (List.last ids).idText with
            | ("SecurityProtocolType" | "SslProtocols"), ("Ssl2" | "Ssl3" | "Tls" | "Tls11" as proto) ->
                crypto.Add
                    { Range = e.Range
                      Kind = WeakKind.Protocol proto
                      // the constant ident itself: the Tls12 swap's target
                      AlgoRange = Some (List.last ids).idRange }
            | _ -> ()
        | _ -> ()

    List.ofSeq crypto, List.ofSeq sql, List.ofSeq processSinks
