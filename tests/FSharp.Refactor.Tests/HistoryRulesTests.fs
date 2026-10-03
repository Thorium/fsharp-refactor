/// FR0180 RandomShared, FR0181 WrappedCatch, and FR0127's credential-named literals.
module FSharp.Refactor.Tests.HistoryRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private patch (source: string) (edits: (FSharp.Compiler.Text.range * string) list) =
    edits
    |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, text) -> applyEdit acc r text) source

// ---- FR0180 RandomShared ----

let private randomsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    RandomShared.find tree sourceText checkResults

[<Fact>]
let ``FR0180: a Random built per call, unseeded or seeded from the clock, is Random.Shared`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading
            let a () = Random().Next 20
            let b () = (new Random(DateTime.Now.Millisecond)).Next 6
            let c () =
                let rnd = new Random(DateTime.Now.Second + DateTime.Now.Millisecond + Thread.CurrentThread.ManagedThreadId)
                700 + rnd.Next 20
            let d () = System.Random(Environment.TickCount).NextDouble()
            let e (xs: int list) = xs |> List.map (fun x -> x + Random(int DateTime.UtcNow.Ticks).Next 3)
            let f () = Random(Guid.NewGuid().GetHashCode()).Next 9
            """

    match randomsIn source with
    | [ a; b; c; d; e; f ] as all ->
        Assert.False a.ClockSeeded
        Assert.Equal(Some "Random.Shared", a.ReplacementText)
        Assert.True b.ClockSeeded
        Assert.Equal("new Random(DateTime.Now.Millisecond)", b.OriginalText)
        Assert.True c.ClockSeeded
        Assert.Equal(Some "System.Random.Shared", d.ReplacementText)
        Assert.True e.ClockSeeded
        Assert.True f.ClockSeeded

        let patched =
            patch source (all |> List.map (fun s -> s.Range, s.ReplacementText.Value))

        Assert.Contains("let a () = Random.Shared.Next 20", patched)
        Assert.Contains("let b () = (Random.Shared).Next 6", patched)
        Assert.Contains("let rnd = Random.Shared", patched)
        assertTypechecks "Patched source" patched
        Assert.Empty(randomsIn patched)
    | other -> failwithf "Expected six findings, got %A" other

[<Fact>]
let ``FR0180: a deliberate seed, a generator built once, and another Random stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System
            type Random2(seed: int) =
                member _.Next() = seed
            let shared = Random()
            let fixedSeed () = Random(42).Next 5
            let fromParameter (seed: int) = Random(seed).Next 5
            let mixed (seed: int) = Random(seed + DateTime.Now.Millisecond).Next 5
            let other () = Random2(DateTime.Now.Millisecond).Next()
            type Holder() =
                let rnd = Random()
                member _.Next() = rnd.Next()
            """

    Assert.Empty(randomsIn source)

// ---- FR0181 WrappedCatch ----

let private wrappedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    WrappedCatch.find tree sourceText checkResults

[<Fact>]
let ``FR0181: a specific handler around a blocking wait is noted, with both levels offered`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading.Tasks
            let register () = 1
            let a (work: Task) =
                try
                    work.Wait()
                    0
                with
                | :? InvalidOperationException -> register ()
            let b (work: Task<int>) =
                try
                    work.Result
                with
                | :? ArgumentException as e -> e.Message.Length
                | _ -> -1
            let c (x: Task) (y: Task) =
                try
                    Task.WaitAll(x, y)
                with
                | :? TimeoutException -> ()
            """

    match wrappedIn source with
    | [ a; b; c ] ->
        Assert.Equal(("InvalidOperationException", "Wait", false), (a.TypeText, a.Wait, a.HasCatchAll))
        Assert.Equal(("ArgumentException", "Result", true), (b.TypeText, b.Wait, b.HasCatchAll))
        // the handler uses its own exception value: the body cannot be
        // repeated under another pattern as written
        Assert.True(b.InnerOffer.IsNone && b.BaseOffer.IsNone)
        Assert.Equal("WaitAll", c.Wait)

        match a.InnerOffer, a.BaseOffer with
        | Some(at, inner), Some(_, deepest) ->
            Assert.Contains("when (aggregate.InnerException :? InvalidOperationException) -> register ()", inner)
            Assert.Contains("when (aggregate.GetBaseException() :? InvalidOperationException) -> register ()", deepest)
            assertTypechecks "Inner offer" (applyEdit source at inner)
            assertTypechecks "Base offer" (applyEdit source at deepest)

            Assert.Empty(
                wrappedIn (applyEdit source at inner)
                |> List.filter (fun s -> s.TypeText = "InvalidOperationException")
            )
        | other -> failwithf "Expected both offers, got %A" other
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0181: an aggregate handler, a general one, a wait under a lambda and no wait at all stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Threading.Tasks
            let a (work: Task) =
                try
                    work.Wait()
                with
                | :? AggregateException as ae -> printfn "%s" ae.Message
                | :? InvalidOperationException -> ()
            let b (work: Task) =
                try
                    work.Wait()
                with
                | :? Exception as e -> printfn "%s" e.Message
            let c (work: Task) =
                try
                    work.Wait()
                with
                | e -> printfn "%s" e.Message
            let d (work: Task) =
                try
                    let later = fun () -> work.Wait()
                    ignore later
                with
                | :? InvalidOperationException -> ()
            let e (compute: unit -> int) =
                try
                    compute ()
                with
                | :? InvalidOperationException -> 0
            type Slot() =
                member _.Result = 1
                member _.Wait() = ()
            let f (s: Slot) =
                try
                    s.Wait()
                    s.Result
                with
                | :? InvalidOperationException -> 0
            """

    Assert.Empty(wrappedIn source)

// ---- FR0127: a literal the code calls a credential ----

let private namedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    SecretLiterals.findNamed tree sourceText (Some checkResults)

[<Fact>]
let ``FR0127: a literal bound to a credential's name is a credential in source`` () =
    let source =
        fsharp
            """
            module M
            type Settings = { User: string; ApiKey: string }
            type Client() =
                member val Password = "" with get, set
                member _.Authenticate(user: string, password: string) = user.Length + password.Length
            let servicePassword = "Zx9q4SYqjNXa7Xw"
            let settings = { User = "svc"; ApiKey = "kq82hf01mmz9d1" }
            let connect (c: Client) =
                c.Password <- "pL0xx81nnQa"
                c.Authenticate("serviceuser", "Qw8zLm2pXy")
            let check (password: string) = password = "hunter2xyz"
            """

    match namedIn source with
    | [ a; b; c; d; e ] ->
        Assert.Equal<string list>(
            [ "servicePassword"; "ApiKey"; "Password"; "password"; "password" ],
            [ a.Name; b.Name; c.Name; d.Name; e.Name ]
        )
    | other -> failwithf "Expected five findings, got %A" other

[<Fact>]
let ``FR0127: names about a credential, placeholders, prompts and setting names stay quiet`` () =
    let source =
        fsharp
            """
            module M
            type Client() =
                member _.Authenticate(user: string, password: string) = user.Length + password.Length
                member _.Read(key: string) = key
            let passwordHeader = "X-Service-Auth"
            let tokenEndpoint = "https://example.org/connect"
            let secretName = "payments-prod"
            let passwordKey = "ServiceAccount"
            let tokenVariable = "GITHUB_TOKEN"
            let apiKey = "ApiKeyForPayments"
            let password = "changeme"
            let secret = ""
            let token = "test-token-000"
            let passwordPrompt = "Enter password:"
            let pwd = "short"
            let tokenizer = "cl100k_base"
            let tokens = "many-of-them"
            let connect (c: Client) (p: string) = c.Authenticate("serviceuser", p)
            let read (c: Client) = c.Read "anything-goes-here"
            let user = "serviceuser"
            """

    Assert.Empty(namedIn source)

[<Fact>]
let ``FR0127: without check results the named shapes still read, the positional one does not`` () =
    let source =
        "module M\ntype C() =\n    member _.Login(user: string, password: string) = 1\nlet secret = \"kq82hf01mmz9\"\nlet f (c: C) = c.Login(\"u\", \"Qw8zLm2pXy\")"

    let tree, sourceText = parse source

    match SecretLiterals.findNamed tree sourceText None with
    | [ only ] -> Assert.Equal("secret", only.Name)
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0180: a generator stored, returned or passed on is held state and stays`` () =
    let source =
        fsharp
            """
            module M
            open System
            type Game = { Rng: Random; Score: int }
            let start () = { Rng = Random(); Score = 0 }
            let league (teams: int) =
                let rng = Random()
                let first = rng.Next teams
                { Rng = rng; Score = first }
            let make () = Random()
            let shuffle (rng: Random) (xs: int[]) = xs |> Array.sortBy (fun _ -> rng.Next())
            let mixed (xs: int[]) =
                let rng = new Random(DateTime.Now.Millisecond)
                shuffle rng xs
            let drawn (xs: int[]) =
                let rng = Random()
                xs |> Array.sortBy (fun _ -> rng.Next())
            """

    match randomsIn source with
    | [ only ] -> Assert.Equal("Random()", only.OriginalText)
    | other -> failwithf "Expected the one local drawn from in place, got %A" other
