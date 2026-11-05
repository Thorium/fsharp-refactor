module FSharp.Refactor.Tests.RedirectExposureTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private secretHeadersIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RedirectExposure.findSecretHeaders tree sourceText checkResults

let private followingClientsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RedirectExposure.findFollowingClients tree sourceText checkResults

// ---- FR0183 ----

[<Fact>]
let ``FR0183: names that hold secrets are told apart from those that don't`` () =
    for name in
        [
            "PLAID-SECRET"
            "X-Auth-Token"
            "x-api-key"
            "X-TM-Key"
            "CMG-AccessToken"
            "Signature"
            "DigitalSignature"
            "AuthenticationPwd"
            "Ocp-Apim-Subscription-Key"
        ] do
        Assert.True(RedirectExposure.holdsSecret name, name)

    for name in
        [
            "Authorization"
            "Idempotency-Key"
            "Stripe-Account"
            "Accept"
            "Plaid-Version"
            "X-Request-Id"
            "Monkey"
        ] do
        Assert.False(RedirectExposure.holdsSecret name, name)

[<Fact>]
let ``FR0183: a secret on a request or a client's defaults is noted, with the name it read`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            let send (client: HttpClient) (secret: string) =
                use request = new HttpRequestMessage(HttpMethod.Post, "https://example.com")
                request.Headers.Add("PLAID-SECRET", secret)
                client.DefaultRequestHeaders.Add("X-Auth-Token", secret)
                request.Headers.TryAddWithoutValidation("x-api-key", secret) |> ignore
                client.SendAsync request
            """

    let found = secretHeadersIn source

    Assert.Equal<string voption list>(
        [ ValueSome "PLAID-SECRET"; ValueSome "X-Auth-Token"; ValueSome "x-api-key" ],
        found |> List.map _.Name
    )

[<Fact>]
let ``FR0183: a header name a helper is passed may be a secret`` () =
    let source =
        fsharp
            """
            module M
            open System.Net
            let post (url: string) (headers: (string * string) seq) =
                let req = WebRequest.CreateHttp url
                headers |> Seq.iter (fun (h, v) -> req.Headers.Add(h, v))
                req
            """

    Assert.Equal<string voption list>([ ValueNone ], secretHeadersIn source |> List.map _.Name)

[<Fact>]
let ``FR0183: Authorization, plain headers and other collections stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Collections.Generic
            open System.Net.Http
            type Message = { Headers: Dictionary<string, string> }
            let send (m: Message) (request: HttpRequestMessage) (token: string) =
                request.Headers.Add("Authorization", token)
                request.Headers.Add("Idempotency-Key", token)
                request.Headers.Add("Accept", "application/json")
                m.Headers.Add("X-Api-Key", token)
            """

    Assert.Empty(secretHeadersIn source)

[<Fact>]
let ``FR0183: a response's headers go nowhere`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            let answer (signature: string) =
                let response = new HttpResponseMessage()
                response.Headers.Add("DigitalSignature", signature)
                response
            """

    Assert.Empty(secretHeadersIn source)

[<Fact>]
let ``FR0183: a file that turns redirects off is quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            let client = new HttpClient(new HttpClientHandler(AllowAutoRedirect = false))
            let send (secret: string) = client.DefaultRequestHeaders.Add("X-Auth-Token", secret)
            """

    Assert.Empty(secretHeadersIn source)

[<Fact>]
let ``FR0183: an HttpWebRequest set not to follow redirects is quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Net
            let post (url: string) (key: string) =
                let req = WebRequest.CreateHttp url
                req.AllowAutoRedirect <- false
                req.Headers.Add("X-TM-Key", key)
                req
            """

    Assert.Empty(secretHeadersIn source)

[<Fact>]
let ``FR0183: a test file is quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            type FactAttribute() = inherit System.Attribute()
            [<Fact>]
            let sends () =
                use request = new HttpRequestMessage()
                request.Headers.Add("X-Auth-Token", "t")
            """

    Assert.Empty(secretHeadersIn source)

// ---- FR0184 ----

[<Fact>]
let ``FR0184: every way to make a request that follows redirects is noted`` () =
    let source =
        fsharp
            """
            module M
            open System.Net
            open System.Net.Http
            let a = new HttpClient()
            let b = HttpClient()
            let c = new HttpClientHandler(UseCookies = false)
            let d = new SocketsHttpHandler()
            let e = WebRequest.Create "https://example.com"
            let f = WebRequest.CreateHttp "https://example.com"
            let g = new WebClient()
            """

    Assert.Equal<string list>(
        [
            "HttpClient"
            "HttpClient"
            "HttpClientHandler"
            "SocketsHttpHandler"
            "WebRequest"
            "WebRequest"
            "WebClient"
        ],
        followingClientsIn source |> List.map _.Maker
    )

[<Fact>]
let ``FR0184: a client over a handler answers for the handler, not twice`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            let make (handler: HttpMessageHandler) = new HttpClient(handler)
            """

    Assert.Empty(followingClientsIn source)

[<Fact>]
let ``FR0184: a file that turns redirects off is quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Net.Http
            let handler = new HttpClientHandler(AllowAutoRedirect = false)
            let other = new HttpClient()
            """

    Assert.Empty(followingClientsIn source)

[<Fact>]
let ``FR0184: it is off until asked for, and FR0183 is on`` () =
    Assert.False(Configuration.isEnabledIn Map.empty "FR0184" "RedirectFollowingClient")
    Assert.True(Configuration.isEnabledIn Map.empty "FR0183" "SecretHeaderRedirect")

[<Fact>]
let ``FR0183: a constant name is read, and a standard header's enum isn't a secret`` () =
    let source =
        fsharp
            """
            open System.Net
            open System.Net.Http
            [<Literal>]
            let Accept = "Accept"
            [<Literal>]
            let ApiKey = "X-Api-Key"
            let send (c: WebClient) (r: HttpRequestMessage) =
                c.Headers.Add(HttpRequestHeader.ContentType, "application/json")
                r.Headers.Add(Accept, "x")
                r.Headers.Add(name = "Accept", value = "x")
                r.Headers.Add(ApiKey, "y")
            """

    let found = Assert.Single(secretHeadersIn source)
    Assert.Equal(ValueSome "X-Api-Key", found.Name)

[<Fact>]
let ``FR0184: an abbreviation of a maker is still found`` () =
    let source =
        fsharp
            """
            open System.Net.Http
            type C = HttpClient
            let make () = C()
            """

    Assert.Single(followingClientsIn source) |> ignore

[<Fact>]
let ``FR0183: a local bound to a literal is read as that literal`` () =
    let source =
        fsharp
            """
            open System.Net.Http
            let send (r: HttpRequestMessage) =
                let plain = "Accept"
                r.Headers.Add(plain, "x")
                let key = "X-Api-Key"
                r.Headers.Add(key, "y")
            """

    let found = Assert.Single(secretHeadersIn source)
    Assert.Equal(ValueSome "X-Api-Key", found.Name)

[<Fact>]
let ``FR0183: a mention of AllowAutoRedirect that sets nothing doesn't quiet the file`` () =
    for quiet in
        [
            "// AllowAutoRedirect = false"
            "let note = \"AllowAutoRedirect = false\""
            "let check (h: HttpClientHandler) = h.AllowAutoRedirect = false"
        ] do
        let source =
            fsharp
                $"""
                open System.Net.Http
                {quiet}
                let send (r: HttpRequestMessage) (secret: string) = r.Headers.Add("X-Auth-Token", secret)
                """

        Assert.Single(secretHeadersIn source) |> ignore

[<Fact>]
let ``FR0183: a property set to false quiets the file`` () =
    let source =
        fsharp
            """
            open System.Net.Http
            let handler = new HttpClientHandler()
            handler.AllowAutoRedirect <- false
            let send (r: HttpRequestMessage) (secret: string) = r.Headers.Add("X-Auth-Token", secret)
            """

    Assert.Empty(secretHeadersIn source)
