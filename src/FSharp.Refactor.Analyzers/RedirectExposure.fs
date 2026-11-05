/// Requests that go wherever a redirect points. .NET follows redirects by
/// default, on every runtime. It drops `Authorization` on the way, keeps every
/// other header, and on a 307 or 308 sends the body again; a host that
/// answers with a redirect therefore gets them. No fix: turning redirects off
/// turns a followed one into a failure the caller has to handle, and code that
/// fetches pages needs them.
///
/// FR0183 (correctness, note): a header that may hold a secret is added in a
/// file that never turns redirects off:
///
///     request.Headers.Add("PLAID-SECRET", secret)
///     client.DefaultRequestHeaders.Add("X-Auth-Token", token)
///     headers |> Seq.iter (fun (h, v) -> req.Headers.Add(h, v))    // any name at all
///
/// A constant name holding secret, token, password, api key, signature or
/// credential counts, or the word key on its own; so does a name not known
/// here, which a helper is passed. A local bound to a literal is read as that
/// literal. An enum of standard headers or `HeaderNames` isn't one. `Authorization` is dropped, an idempotency
/// key isn't a secret, and a response's headers go nowhere. A library handed its `HttpClient` can't
/// turn redirects off, so it still fires there: its docs have to ask callers to.
///
/// FR0184 (correctness, note, off by default): a request maker with redirects
/// on, in a file that never turns them off: `new HttpClient()`, a
/// `HttpClientHandler` or `SocketsHttpHandler`, `WebRequest.Create`,
/// `WebClient`, FSharp.Data's `Http.Request` family without
/// `customizeHttpRequest`. Downloads and public pages are fine as they are,
/// so this is for a code base that sends secrets or personal data.
///
/// `AllowAutoRedirect` set to false anywhere in the file's code, not in a
/// comment or string, quiets both: the question is whether the author has
/// considered redirects here. Test files are quiet.
module FSharp.Refactor.RedirectExposure

open System
open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type SecretHeader =
    {
        Range: range
        /// The header's name, when the code spells it.
        Name: string voption
    }

type FollowingClient =
    {
        Range: range
        /// What makes the requests, as the message names it.
        Maker: string
    }

let private mentionsRedirects =
    Regex(@"AllowAutoRedirect|customizeHttpRequest", RegexOptions.Compiled)

/// Does the code set `AllowAutoRedirect` to false, or pass `customizeHttpRequest`? A comparison
/// (`h.AllowAutoRedirect = false`) doesn't count: only a named argument's name stands alone.
let private redirectsOff (index: Lazy<AstIndex.Index>) (source: ISourceText) =
    let isFalse (e: SynExpr) =
        match stripParens e with
        | SynExpr.Const(SynConst.Bool false, _) -> true
        | _ -> false

    let namesAllow (ids: Ident list) =
        match List.tryLast ids with
        | Some last -> last.idText = "AllowAutoRedirect"
        | None -> false

    mentionsRedirects.IsMatch(source.GetSubTextString(0, source.Length))
    && index.Value.Exprs
       |> Array.exists (fun (_, e) ->
           match e with
           | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids); expr = value)
           | SynExpr.DotSet(longDotId = SynLongIdent(id = ids); rhsExpr = value) -> namesAllow ids && isFalse value
           | SynExpr.App(
               funcExpr = SynExpr.App(
                   isInfix = true
                   funcExpr = (SynExpr.Ident op | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])))
                   argExpr = SynExpr.Ident named)
               argExpr = value) when op.idText = "op_Equality" ->
               (named.idText = "AllowAutoRedirect" && isFalse value)
               || named.idText = "customizeHttpRequest"
           | _ -> false)

let private secretWords =
    [
        "secret"
        "token"
        "password"
        "passwd"
        "pwd"
        "apikey"
        "api-key"
        "api_key"
        "signature"
        "credential"
    ]

/// Does a header of this name hold a secret that a redirect would carry?
let holdsSecret (name: string) =
    let lower = name.ToLowerInvariant()

    if lower = "authorization" || lower.Contains "idempotency" then
        false
    else
        secretWords |> List.exists (fun (word: string) -> lower.Contains word)
        || lower.Split('-', '_') |> Array.contains "key"

let private sourceTextOf (source: ISourceText) =
    source.GetSubTextString(0, source.Length)

let private fullNameAt (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        (try
            match symbolUse.Symbol with
            | :? FSharpMemberOrFunctionOrValue as mfv -> mfv.DeclaringEntity |> Option.bind (fun e -> e.TryFullName)
            | :? FSharpEntity as e -> e.TryFullName
            | _ -> None
         with _ -> // an unreadable symbol isn't one of these types; fsharpanalyzer: ignore-line FR0055
             None)
    | None -> None

/// What declares the headers of something that sends a request. A response's go nowhere.
let private requestHeaderOwners =
    set
        [
            "System.Net.Http.HttpRequestMessage"
            "System.Net.Http.HttpClient"
            "System.Net.WebRequest"
            "System.Net.HttpWebRequest"
            "System.Net.WebClient"
        ]

/// The last two names of a call's function: what is called, and what it is called on.
let private calledNames (funcExpr: SynExpr) =
    match funcExpr with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
        let reversed = List.rev ids
        ValueSome(reversed[1], reversed[0])
    | _ -> ValueNone

/// What a call's name argument says of the header.
[<Struct; RequireQualifiedAccess>]
type private HeaderName =
    | Known of name: string
    /// A constant that isn't a string: `HttpRequestHeader.ContentType`.
    | Standard
    | Elsewhere

/// The expression naming the header, positional or `name = ...`.
let private nameArgument (arg: SynExpr) =
    let namedName (e: SynExpr) =
        match e with
        | SynExpr.App(
            funcExpr = SynExpr.App(
                isInfix = true
                funcExpr = (SynExpr.Ident op | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])))
                argExpr = SynExpr.Ident named)
            argExpr = value) when op.idText = "op_Equality" && named.idText = "name" -> Some value
        | _ -> None

    match stripParens arg with
    | SynExpr.Tuple(exprs = first :: _ :: _ as all) ->
        all |> List.tryPick namedName |> Option.defaultValue first |> ValueSome
    | _ -> ValueNone

let private headerName (check: FSharpCheckFileResults) (source: ISourceText) (index: AstIndex.Index) (name: SynExpr) =
    /// The literal an immutable value declared at this spot is bound to.
    let boundLiteral (declared: range) =
        index.Pats
        |> Array.tryPick (fun (path, pat) ->
            match pat, path with
            | SynPat.Named(ident = SynIdent(ident = bound)), SyntaxNode.SynBinding(SynBinding(expr = rhs)) :: _ when
                Range.equals bound.idRange declared
                ->
                match stripParens rhs with
                | SynExpr.Const(SynConst.String(text = text), _) -> Some text
                | _ -> None
            | _ -> None)

    let constantAt (ident: Ident) =
        let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
        | Some symbolUse ->
            (try
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value when
                    (value.DeclaringEntity
                     |> Option.bind (fun e -> e.TryFullName)
                     |> Option.exists (fun full -> full.EndsWith "HeaderNames"))
                    ->
                    Some(box 0)
                | :? FSharpMemberOrFunctionOrValue as value when not value.IsMutable && value.LiteralValue.IsNone ->
                    boundLiteral value.DeclarationLocation |> Option.map box
                | :? FSharpMemberOrFunctionOrValue as value -> value.LiteralValue
                | :? FSharpField as field when field.IsLiteral -> field.LiteralValue
                | _ -> None
             with _ -> // an unreadable symbol isn't a constant; fsharpanalyzer: ignore-line FR0055
                 None)
        | None -> None

    let ofConstant (ident: Ident) =
        match constantAt ident with
        | Some(:? string as text) -> HeaderName.Known text
        | Some _ -> HeaderName.Standard
        | None -> HeaderName.Elsewhere

    match stripParens name with
    | SynExpr.Const(SynConst.String(text = text), _) -> HeaderName.Known text
    | SynExpr.Ident ident -> ofConstant ident
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ofConstant (List.last ids)
    | _ -> HeaderName.Elsewhere

let findSecretHeaders
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : SecretHeader list =
    let lazyIndex = lazy (AstIndex.ofTree parseTree)

    if OptionModule.hasErrors check || redirectsOff lazyIndex source then
        []
    else
        let index = lazyIndex.Value

        if AstIndex.isTestFile index source then
            []
        else
            [
                for _, e in index.Exprs do
                    match e with
                    | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = arg) ->
                        match calledNames funcExpr, nameArgument arg with
                        | ValueSome(headers, called), ValueSome name when
                            (headers.idText = "Headers" || headers.idText = "DefaultRequestHeaders")
                            && (called.idText = "Add" || called.idText = "TryAddWithoutValidation")
                            && (match fullNameAt check source headers with
                                | Some full -> requestHeaderOwners.Contains full
                                | None -> false)
                            ->
                            match headerName check source index name with
                            | HeaderName.Known known when holdsSecret known ->
                                yield
                                    {
                                        Range = e.Range
                                        Name = ValueSome known
                                    }
                            | HeaderName.Elsewhere -> yield { Range = e.Range; Name = ValueNone }
                            | _ -> ()
                        | _ -> ()
                    | _ -> ()
            ]

let private makerNamesRegex = Regex @"\btype\s+(\w+)\s*=\s*(?:[\w.]+\.)?(?:HttpClient|HttpClientHandler|SocketsHttpHandler|WebClient)\b"
/// What a maker can be called in this file, its abbreviations included: resolving a symbol costs time
/// that grows with the file, so only these names are resolved.
let private makerNames (text: string) =
    let abbreviated =
        makerNamesRegex.Matches text
        |> Seq.map (fun found -> found.Groups[1].Value)

    set [ "HttpClient"; "HttpClientHandler"; "SocketsHttpHandler"; "WebClient" ]
    |> Set.union (set abbreviated)

let private constructedTypes =
    set
        [
            "System.Net.Http.HttpClientHandler"
            "System.Net.Http.SocketsHttpHandler"
            "System.Net.WebClient"
        ]

let private requestFunctions =
    set
        [
            "Request"
            "RequestString"
            "RequestStream"
            "AsyncRequest"
            "AsyncRequestString"
            "AsyncRequestStream"
        ]

let private isUnitArgument (arg: SynExpr) =
    match arg with
    | SynExpr.Const(SynConst.Unit, _) -> true
    | _ -> false

let findFollowingClients
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : FollowingClient list =
    let lazyIndex = lazy (AstIndex.ofTree parseTree)

    if OptionModule.hasErrors check || redirectsOff lazyIndex source then
        []
    else
        let index = lazyIndex.Value

        if AstIndex.isTestFile index source then
            []
        else
            let names = makerNames (sourceTextOf source)

            let constructed (typeId: Ident) (arg: SynExpr) =
                if names.Contains typeId.idText then
                    match fullNameAt check source typeId with
                    | Some "System.Net.Http.HttpClient" when isUnitArgument arg -> ValueSome "HttpClient"
                    | Some full when constructedTypes.Contains full -> ValueSome typeId.idText
                    | _ -> ValueNone
                else
                    ValueNone

            [
                for _, e in index.Exprs do
                    let maker =
                        match e with
                        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when
                            not ids.IsEmpty
                            ->
                            constructed (List.last ids) arg
                        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident typeId; argExpr = arg) ->
                            constructed typeId arg
                        | SynExpr.App(
                            isInfix = false
                            funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                            argExpr = arg) when ids.Length >= 2 ->
                            let called = List.last ids

                            match called.idText with
                            | "Create"
                            | "CreateHttp" when
                                (match fullNameAt check source called with
                                 | Some full -> full = "System.Net.WebRequest" || full = "System.Net.HttpWebRequest"
                                 | None -> false)
                                ->
                                ValueSome "WebRequest"
                            | name when requestFunctions.Contains name ->
                                match fullNameAt check source called with
                                | Some "FSharp.Data.Http" -> ValueSome "Http.Request"
                                | _ -> ValueNone
                            | _ -> constructed called arg
                        | _ -> ValueNone

                    match maker with
                    | ValueSome maker -> yield { Range = e.Range; Maker = maker }
                    | ValueNone -> ()
            ]
