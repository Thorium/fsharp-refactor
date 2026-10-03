/// FR0127: provider-format API keys, credentials and private keys in
/// string literals.
///
/// Not entropy guessing — each pattern is a provider's DOCUMENTED key
/// format, anchored tightly enough that a match in source is a leaked
/// credential until proven otherwise:
///
///     "sk-ant-api03-..."          Anthropic
///     "sk-proj-..." / "sk-..."    OpenAI
///     "AIza..."                   Google API
///     "ghp_..." / "github_pat_"   GitHub
///     "AKIA..."                   AWS access key id
///     "xoxb-..."                  Slack
///     "sk_live_..." / "whsec_..." Stripe and Svix
///     "eyJ....eyJ....sig"         a signed JWT (three segments)
///     "Bearer eyJ..."             a bearer token spelled out
///     "Server=...;Password=..."   a connection string carrying its password
///     "AccountKey=..."            an Azure storage key
///     "-----BEGIN PRIVATE KEY"    PEM material
///
/// Placeholders stay quiet: a connection-string password of `password`,
/// `test`, `changeme`, `<...>`, `{...}`, `%...%` or `$(...)` is a sample,
/// not a secret. Interpolated strings' literal parts and type-provider
/// static arguments (`SqlDataProvider<ConnectionString = "...">`) are
/// scanned too — that is where connection strings live.
///
/// Notes only: the remedy (rotate the key, move to configuration or a
/// secret store) happens outside this file.
module FSharp.Refactor.SecretLiterals

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

type Suggestion =
    {
        Range: range
        Provider: string
        /// the value is a [<Literal>]: a compile-time constant a type provider
        /// reads before the program runs
        DesignTimeLiteral: bool
        /// The name the code gives the literal, for a finding made by name
        /// rather than by a provider's format; empty otherwise.
        Name: string
    }

let private patterns =
    [
        "Anthropic", Regex(@"\bsk-ant-[A-Za-z0-9_-]{12,}", RegexOptions.Compiled)
        "OpenAI", Regex(@"\bsk-(proj-)?[A-Za-z0-9_-]{32,}", RegexOptions.Compiled)
        "Google", Regex(@"\bAIza[0-9A-Za-z_-]{35}", RegexOptions.Compiled)
        "GitHub", Regex(@"\bgh[pousr]_[A-Za-z0-9]{36,}|github_pat_[A-Za-z0-9_]{22,}", RegexOptions.Compiled)
        "AWS", Regex(@"\bAKIA[0-9A-Z]{16}\b", RegexOptions.Compiled)
        "Slack", Regex(@"\bxox[baprs]-[A-Za-z0-9-]{10,}", RegexOptions.Compiled)
        "Stripe", Regex(@"\b(sk|rk)_(live|test)_[A-Za-z0-9]{24,}", RegexOptions.Compiled)
        "Svix webhook secret", Regex(@"\bwhsec_[A-Za-z0-9+/]{24,}", RegexOptions.Compiled)
        "JWT", Regex(@"\beyJ[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}\.[A-Za-z0-9_-]{10,}", RegexOptions.Compiled)
        "bearer token", Regex(@"\bBearer\s+[A-Za-z0-9._~+/-]{20,}", RegexOptions.Compiled)
        "Azure storage key", Regex(@"AccountKey=[A-Za-z0-9+/]{80,}={0,2}", RegexOptions.Compiled)
        "PEM private key", Regex(@"-----BEGIN [A-Z ]*PRIVATE KEY-----", RegexOptions.Compiled)
    ]

/// A connection string is one when another connection key sits beside the
/// password; the password itself must not read as a placeholder.
let private connectionKey =
    Regex(@"(?i)\b(Data Source|Server|Host|Initial Catalog|Database|User Id|Uid|Username)\s*=", RegexOptions.Compiled)

let private connectionPassword =
    Regex(@"(?i)\b(Password|Pwd)\s*=\s*([^;""\s]{4,})", RegexOptions.Compiled)

let private placeholderPassword =
    Regex(
        @"(?i)^(password|passw0rd|pass|secret|test|changeme|example|sample|yourpassword|xxx+|\*+|<.*>|\{.*\}|%.*%|\$\(.*\)|\$\{.*\})$",
        RegexOptions.Compiled
    )


/// A connection string whose SERVER is the loopback host is a development
/// one whatever its password looks like, and that is a far better signal
/// than guessing at the password's shape: `p4ssw0rd` reads as a sample and
/// `Hunter2Real9x` does not, yet both are equally local. Covers the spellings
/// a .NET connection string actually uses — `localhost`, `127.0.0.1`, `::1`,
/// `(local)`, `(localdb)\...`, and the bare `.` — each optionally followed by
/// an instance (`\SQLEXPRESS`) or a port (`,1433`).
let private loopbackServer =
    Regex(
        @"(?i)\b(?:Data Source|Server|Host|Address|Addr|Network Address)\s*=\s*(?:\(local(?:db)?\)|localhost|127\.0\.0\.1|::1|\.)(?=[;,\\""\s]|$)",
        RegexOptions.Compiled
    )

let private connectionStringLeak (text: string) =
    connectionKey.IsMatch text
    && not (loopbackServer.IsMatch text)
    && (let m = connectionPassword.Match text
        m.Success && not (placeholderPassword.IsMatch m.Groups.[2].Value))

/// A literal that says "test" anywhere is a test account's credential — a test
/// database, a test key, a test user. Good practice would keep those in a test
/// key vault too, but the practice is to keep them in source, so they are
/// not the leak this rule hunts. `123456` is the same signal: the standard
/// made-up key, and six specific digits do not occur by chance in real key
/// material (one in 64^6 per position of base64).
let private isTestFixture (text: string) =
    text.Contains("test", System.StringComparison.OrdinalIgnoreCase)
    || text.Contains "123456"

let private providerOf (text: string) =
    if isTestFixture text then
        ValueNone
    else
        match patterns |> List.tryFind (fun (_, rx) -> rx.IsMatch text) with
        | Some(provider, _) -> ValueSome provider
        | None when connectionStringLeak text -> ValueSome "connection-string password"
        | None -> ValueNone

/// A `[<Literal>]` binding's value is a compile-time constant, baked into
/// every use site and read by a type provider before the program runs. It
/// cannot move to configuration, so FR0127's remedy does not apply to it —
/// but the value still ships in source, and the provider only ever needs a
/// SCHEMA, so what belongs there is a development credential and never a
/// production one. Reported under its own lower-priority code because that
/// is a different thing to check.
let private isLiteralBinding (attrs: SynAttributeList list) =
    attrs
    |> List.exists (fun list ->
        list.Attributes
        |> List.exists (fun a ->
            match a.TypeName with
            | SynLongIdent(id = ids) when not ids.IsEmpty ->
                match (List.last ids).idText with
                | "Literal"
                | "LiteralAttribute" -> true
                | _ -> false
            | _ -> false))

let find (parseTree: ParsedInput) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let literalRanges =
        [
            for _, decl in index.Decls do
                match decl with
                | SynModuleDecl.Let(bindings = bindings) ->
                    for SynBinding(attributes = attrs; expr = rhs) in bindings do
                        if isLiteralBinding attrs then
                            yield rhs.Range
                | _ -> ()
        ]

    let designTime (r: range) =
        literalRanges |> List.exists (fun lr -> Range.rangeContainsRange lr r)

    let fromExprs =
        [
            for _, e in index.Exprs do
                match e with
                | SynExpr.Const(SynConst.String(text, _, _), r) ->
                    match providerOf text with
                    | ValueSome provider ->
                        {
                            Range = r
                            Provider = provider
                            DesignTimeLiteral = designTime r
                            Name = ""
                        }
                    | ValueNone -> ()
                // the literal parts of an interpolated string: a key with a
                // hole in its middle is still a key
                | SynExpr.InterpolatedString(contents = parts) ->
                    for part in parts do
                        match part with
                        | SynInterpolatedStringPart.String(text, r) ->
                            match providerOf text with
                            | ValueSome provider ->
                                {
                                    Range = r
                                    Provider = provider
                                    DesignTimeLiteral = designTime r
                                    Name = ""
                                }
                            | ValueNone -> ()
                        | SynInterpolatedStringPart.FillExpr _ -> ()
                | _ -> ()
        ]

    // type-provider static arguments: `SqlDataProvider<ConnectionString = "...">`
    let rec staticStrings (t: SynType) =
        match t with
        | SynType.StaticConstant(SynConst.String(text, _, _), r) -> [ text, r ]
        | SynType.StaticConstantNamed(_, inner, _) -> staticStrings inner
        | SynType.App(typeName = name; typeArgs = args) -> staticStrings name @ List.collect staticStrings args
        | _ -> []

    // a static argument is design-time by construction: it is spelled into
    // the type itself, so it is resolved before the program runs
    let fromTypes =
        [
            for _, t in index.Types do
                for text, r in staticStrings t do
                    match providerOf text with
                    | ValueSome provider ->
                        {
                            Range = r
                            Provider = provider
                            DesignTimeLiteral = true
                            Name = ""
                        }
                    | ValueNone -> ()
        ]

    fromExprs @ fromTypes |> List.distinctBy (fun s -> s.Range)

/// A name that says its value is a credential.
let private credentialName =
    Regex(@"(?i)(password|passwd|pwd|secret|api_?key|access_?key|private_?key|token|credential)", RegexOptions.Compiled)

/// ...unless the name is ABOUT the credential rather than the credential:
/// `passwordHeader`, `tokenEndpoint`, `secretName`, `passwordKey`.
let private describingName =
    Regex(
        @"(?i)((password|passwd|pwd|secret|key|token|credentials?)_?(name|field|header|param|parameter|path|file|label|prompt|message|format|regex|pattern|length|policy|hint|error|title|text|url|uri|type|kind|id|property|setting|option|claim|scheme|prefix|suffix|expiry|lifetime|timeout|endpoint|provider|validator|hash|salt|chars?|rules?|requirement|strength|mask|separator|delimiter|count|limit|size|budget)s?|(password|passwd|pwd|token|credentials?)_?keys?)$",
        RegexOptions.Compiled
    )

let private wordsOfRegex = Regex @"[A-Z]+(?![a-z])|[A-Z]?[a-z]+|\d+"

/// The words of a camelCase / snake_case name, lower-cased:
/// `servicePassword` -> service, password; `API_KEY` -> api, key.
let private wordsOf (name: string) =
    wordsOfRegex.Matches name
    |> Seq.map (fun m -> m.Value.ToLowerInvariant())
    |> List.ofSeq

let private credentialWords =
    set
        [
            "password"
            "passwd"
            "pwd"
            "secret"
            "token"
            "credential"
            "credentials"
            "apikey"
        ]

/// A credential word must be a WORD of the name: `apiToken` yes,
/// `tokenizer` no.
let private namesCredential (name: string) =
    let words = wordsOf name

    let asWord =
        words |> List.exists credentialWords.Contains
        || (words
            |> List.pairwise
            |> List.exists (fun (a, b) -> b = "key" && (a = "api" || a = "access" || a = "private" || a = "secret")))

    asWord && not (describingName.IsMatch name)

/// An environment variable or setting spelled in capitals: `GITHUB_TOKEN`.
let private settingName = Regex(@"^[A-Z][A-Z0-9_.:-]*$", RegexOptions.Compiled)

/// The literal reads as a value, not as a placeholder, a prompt, or the
/// NAME of the setting the credential comes from.
let private credentialValue (name: string) (text: string) =
    text.Length >= 6
    && not (text |> Seq.exists System.Char.IsWhiteSpace)
    && not (placeholderPassword.IsMatch text)
    && not (isTestFixture text)
    && not (credentialName.IsMatch text)
    && not (settingName.IsMatch text)
    && not (text.Equals(name, System.StringComparison.OrdinalIgnoreCase))
    && not (text.Contains '{' || text.Contains "%s" || text.Contains "://")

/// A string literal bound to a name that says it is a credential:
///
///     let servicePassword = "..."
///     { User = user; ApiKey = "..." }
///     client.Password <- "..."
///     if password = "..." then ...
///     Authenticate(user, "...")          // typed: the parameter is `password`
///
/// The key formats above are found by what the literal looks like; this is
/// found by what the code calls it. Quiet for a name that is ABOUT the
/// credential (`passwordHeader`, `tokenEndpoint`), and for a literal that
/// is a placeholder, a prompt, a test fixture, or the name of the setting
/// the credential is read from (`"GITHUB_TOKEN"`, `"Db:Password"`). The
/// positional-argument shape needs check results; the rest is parse-only.
let findNamed
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharp.Compiler.CodeAnalysis.FSharpCheckFileResults option)
    : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let literal (name: string) (e: SynExpr) : Suggestion option =
        match FSharp.Refactor.Text.stripParens e with
        | SynExpr.Const(SynConst.String(text, _, _), r) when namesCredential name && credentialValue name text ->
            Some
                {
                    Range = r
                    Provider = "credential name"
                    DesignTimeLiteral = false
                    Name = name
                }
        | _ -> None

    let ofBindings (bindings: SynBinding list) =
        bindings
        |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
            match p with
            | SynPat.Named(ident = SynIdent(ident = id))
            | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))) -> literal id.idText rhs
            | _ -> None)

    // the parameter names of a tupled call, in order
    let parameterNames (callee: Ident) =
        match check with
        | Some results when not (OptionModule.hasErrors results) ->
            match BlockingSites.valueAt results source callee with
            | Some value ->
                (try
                    match value.CurriedParameterGroups |> Seq.tryHead with
                    | Some group -> group |> Seq.map (fun p -> p.DisplayName) |> List.ofSeq
                    | None -> []
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     [])
            | None -> []
        | _ -> []

    let calleeOf (f: SynExpr) =
        match f with
        | SynExpr.Ident id -> Some id
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    [
        for _, decl in index.Decls do
            match decl with
            | SynModuleDecl.Let(bindings = bindings) -> yield! ofBindings bindings
            | _ -> ()
        for _, e in index.Exprs do
            match e with
            | FSharp.Refactor.Text.LetOrUseE lou when not lou.IsBang -> yield! ofBindings lou.Bindings
            // name = "literal": a named argument, a property initialiser, or
            // a comparison with the credential itself
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(
                    isInfix = true; funcExpr = FSharp.Refactor.Text.IdentName "op_Equality"; argExpr = lhs)
                argExpr = rhs) ->
                match FSharp.Refactor.Text.stripParens lhs with
                | SynExpr.Ident id -> yield! literal id.idText rhs |> Option.toList
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                    yield! literal (List.last ids).idText rhs |> Option.toList
                | _ -> ()
            | SynExpr.Record(recordFields = fields) ->
                for SynExprRecordField(fieldName = (SynLongIdent(id = ids), _); expr = value) in fields do
                    match List.tryLast ids, value with
                    | Some field, Some rhs -> yield! literal field.idText rhs |> Option.toList
                    | _ -> ()
            | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids); expr = rhs) when not ids.IsEmpty ->
                yield! literal (List.last ids).idText rhs |> Option.toList
            | SynExpr.DotSet(longDotId = SynLongIdent(id = ids); rhsExpr = rhs) when not ids.IsEmpty ->
                yield! literal (List.last ids).idText rhs |> Option.toList
            // f(user, "literal"): the parameter the literal lands on
            | SynExpr.App(isInfix = false; funcExpr = f; argExpr = SynExpr.Paren(expr = argument)) ->
                match calleeOf f with
                | Some callee ->
                    let arguments =
                        match argument with
                        | SynExpr.Tuple(exprs = items) -> items
                        | single -> [ single ]

                    if
                        arguments
                        |> List.exists (fun a ->
                            match a with
                            | SynExpr.Const(SynConst.String _, _) -> true
                            | _ -> false)
                    then
                        let names = parameterNames callee

                        if names.Length = arguments.Length then
                            for name, a in List.zip names arguments do
                                yield! literal name a |> Option.toList
                | None -> ()
            | _ -> ()
    ]
    |> List.distinctBy (fun s -> s.Range)
