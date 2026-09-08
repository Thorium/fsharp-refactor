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

type Suggestion = { Range: range; Provider: string }

let private patterns =
    [ "Anthropic", Regex(@"\bsk-ant-[A-Za-z0-9_-]{12,}", RegexOptions.Compiled)
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
      "PEM private key", Regex(@"-----BEGIN [A-Z ]*PRIVATE KEY-----", RegexOptions.Compiled) ]

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

let private connectionStringLeak (text: string) =
    connectionKey.IsMatch text
    && (let m = connectionPassword.Match text
        m.Success && not (placeholderPassword.IsMatch m.Groups.[2].Value))

/// A literal that says "test" anywhere is a test account's credential — a test
/// database, a test key, a test user. Good practice would keep those in a test
/// key vault too, but the practice is to keep them in source, so they are
/// not the leak this rule hunts.
let private isTestFixture (text: string) =
    text.Contains("test", System.StringComparison.OrdinalIgnoreCase)

let private providerOf (text: string) =
    if isTestFixture text then
        ValueNone
    else
        match patterns |> List.tryFind (fun (_, rx) -> rx.IsMatch text) with
        | Some(provider, _) -> ValueSome provider
        | None when connectionStringLeak text -> ValueSome "connection-string password"
        | None -> ValueNone

let find (parseTree: ParsedInput) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let fromExprs =
        [ for _, e in index.Exprs do
              match e with
              | SynExpr.Const(SynConst.String(text, _, _), r) ->
                  match providerOf text with
                  | ValueSome provider -> { Range = r; Provider = provider }
                  | ValueNone -> ()
              // the literal parts of an interpolated string: a key with a
              // hole in its middle is still a key
              | SynExpr.InterpolatedString(contents = parts) ->
                  for part in parts do
                      match part with
                      | SynInterpolatedStringPart.String(text, r) ->
                          match providerOf text with
                          | ValueSome provider -> { Range = r; Provider = provider }
                          | ValueNone -> ()
                      | SynInterpolatedStringPart.FillExpr _ -> ()
              | _ -> () ]

    // type-provider static arguments: `SqlDataProvider<ConnectionString = "...">`
    let rec staticStrings (t: SynType) =
        match t with
        | SynType.StaticConstant(SynConst.String(text, _, _), r) -> [ text, r ]
        | SynType.StaticConstantNamed(_, inner, _) -> staticStrings inner
        | SynType.App(typeName = name; typeArgs = args) -> staticStrings name @ List.collect staticStrings args
        | _ -> []

    let fromTypes =
        [ for _, t in index.Types do
              for text, r in staticStrings t do
                  match providerOf text with
                  | ValueSome provider -> { Range = r; Provider = provider }
                  | ValueNone -> () ]

    fromExprs @ fromTypes |> List.distinctBy (fun s -> s.Range)
