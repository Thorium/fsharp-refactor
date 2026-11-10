/// The MCP server's limits: it works inside the directory it was started
/// for, writes nowhere else, and a server started with --dry-run applies
/// nothing. In the "ProjectSources" collection: the server is `main`, and
/// it redirects the console.
[<Xunit.Collection("ProjectSources")>]
module FSharp.Refactor.Tests.McpServerTests

open System
open System.IO
open System.Text.Json
open Xunit
open FSharp.Refactor.Tool

let private tempRoot (prefix: string) =
    let root = Path.Combine(Path.GetTempPath(), prefix + Guid.NewGuid().ToString "N")
    Directory.CreateDirectory root |> ignore
    root

let private cleanup (root: string) =
    try
        Directory.Delete(root, true)
    with _ ->
        ()

/// One line with one FR0010 fix (`List.length xs = 0` to `List.isEmpty xs`).
let private fixable = "let isEmpty (xs: int list) = List.length xs = 0\n"

let private analyzeRequest (id: int) (target: string) (apply: bool) =
    JsonSerializer.Serialize(
        dict
            [
                "jsonrpc", box "2.0"
                "id", box id
                "method", box "tools/call"
                "params",
                box (
                    dict
                        [
                            "name", box "analyze"
                            "arguments", box (dict [ "target", box target; "apply", box apply; "codes", box "FR0010" ])
                        ]
                )
            ]
    )

/// The server run over `requests` as its stdin; returns its exit code, the
/// protocol lines it answered with and what it wrote to stderr.
let private serve (args: string list) (requests: string list) : int * string list * string =
    let oldIn, oldOut, oldErr = Console.In, Console.Out, Console.Error
    use input = new StringReader(String.concat "\n" requests)
    use output = new StringWriter()
    use errors = new StringWriter()
    Console.SetIn input
    Console.SetOut output
    Console.SetError errors

    try
        let code = Program.main (Array.ofList args)

        let answers =
            output.ToString().Split([| '\r'; '\n' |], StringSplitOptions.RemoveEmptyEntries)
            |> List.ofArray

        code, answers, errors.ToString()
    finally
        Console.SetIn oldIn
        Console.SetOut oldOut
        Console.SetError oldErr

/// An answer's error message, or the body of its tool result.
let private read (answer: string) : Result<JsonElement, string> =
    use doc = JsonDocument.Parse answer

    match doc.RootElement.TryGetProperty "error" with
    | true, error -> Error(error.GetProperty("message").GetString())
    | _ ->
        let text =
            doc.RootElement.GetProperty("result").GetProperty("content").[0].GetProperty("text").GetString()

        use body = JsonDocument.Parse text
        Ok(body.RootElement.Clone())

[<Fact>]
let ``a target outside the server's root is refused and left alone`` () =
    let root = tempRoot "fsref-mcp-root-"
    let elsewhere = tempRoot "fsref-mcp-elsewhere-"

    try
        let outside = Path.Combine(elsewhere, "probe.fsx")
        File.WriteAllText(outside, fixable)

        let code, answers, _ =
            serve
                [ root; "--mcp" ]
                [
                    analyzeRequest 1 outside true
                    analyzeRequest 2 (Path.Combine(root, "..", Path.GetFileName elsewhere, "probe.fsx")) true
                ]

        Assert.Equal(0, code)
        Assert.Equal(2, answers.Length)

        for answer in answers do
            match read answer with
            | Error message -> Assert.Contains("outside this server's root", message)
            | Ok body -> failwithf "answered %s" (body.GetRawText())

        Assert.Equal(fixable, File.ReadAllText outside)
    finally
        cleanup root
        cleanup elsewhere

[<Fact>]
let ``a target inside the root is analysed, a relative one from the root`` () =
    let root = tempRoot "fsref-mcp-root-"
    let before = Directory.GetCurrentDirectory()

    try
        File.WriteAllText(Path.Combine(root, "probe.fsx"), fixable)
        // the server's root is its argument, not where the process stands
        Directory.SetCurrentDirectory(Path.GetTempPath())

        let _, answers, _ =
            serve
                [ root; "--mcp" ]
                [
                    analyzeRequest 1 (Path.Combine(root, "probe.fsx")) false
                    analyzeRequest 2 "probe.fsx" false
                ]

        Assert.Equal(2, answers.Length)

        for answer in answers do
            match read answer with
            | Ok body ->
                Assert.Equal(1, body.GetProperty("findingCount").GetInt32())
                Assert.False(body.GetProperty("applied").GetBoolean())
            | Error message -> failwith message

        Assert.Equal(fixable, File.ReadAllText(Path.Combine(root, "probe.fsx")))
    finally
        Directory.SetCurrentDirectory before
        cleanup root

[<Fact>]
let ``a server started with --dry-run applies nothing`` () =
    let root = tempRoot "fsref-mcp-root-"

    try
        let script = Path.Combine(root, "probe.fsx")
        File.WriteAllText(script, fixable)

        let _, answers, _ =
            serve [ root; "--mcp"; "--dry-run" ] [ analyzeRequest 1 script true; analyzeRequest 2 script false ]

        match answers |> List.map read with
        | [ Error refusal; Ok report ] ->
            Assert.Contains("--dry-run", refusal)
            Assert.Equal(1, report.GetProperty("findingCount").GetInt32())
        | other -> failwithf "answered %A" other

        Assert.Equal(fixable, File.ReadAllText script)
    finally
        cleanup root

[<Fact>]
let ``an apply writes inside the root only: a compilation reaching a file outside it is put back whole`` () =
    let parent = tempRoot "fsref-mcp-parent-"

    try
        let root = Path.Combine(parent, "root")
        let shared = Path.Combine(parent, "shared")
        Directory.CreateDirectory root |> ignore
        Directory.CreateDirectory shared |> ignore
        let outside = Path.Combine(shared, "Lib.fsx")
        let script = Path.Combine(root, "main.fsx")
        File.WriteAllText(outside, fixable)

        let own =
            "#load \"../shared/Lib.fsx\"\nlet none (xs: string list) = List.length xs = 0\n"

        File.WriteAllText(script, own)

        let _, answers, _ = serve [ root; "--mcp" ] [ analyzeRequest 1 script true ]

        match answers |> List.map read with
        | [ Ok body ] ->
            Assert.Equal(1, body.GetProperty("exitCode").GetInt32())

            Assert.Contains(
                "outside",
                body.GetProperty("exitReasons").EnumerateArray()
                |> Seq.map _.GetString()
                |> String.concat "; "
            )
        | other -> failwithf "answered %A" other

        Assert.Equal(fixable, File.ReadAllText outside)
        Assert.Equal(own, File.ReadAllText script)
    finally
        cleanup parent

[<Fact>]
let ``a flag the server would ignore, or a root that is no directory, is a usage error`` () =
    let root = tempRoot "fsref-mcp-root-"

    try
        let file = Path.Combine(root, "probe.fsx")
        File.WriteAllText(file, fixable)

        let code, answers, said =
            serve [ root; "--mcp"; "--report"; Path.Combine(root, "x.sarif") ] []

        Assert.Equal(2, code)
        Assert.Empty answers
        Assert.Contains("--report", said)

        let code, _, said = serve [ root; "--mcp"; "--api-changes" ] []
        Assert.Equal(2, code)
        Assert.Contains("--api-changes", said)

        let code, _, said = serve [ file; "--mcp" ] []
        Assert.Equal(2, code)
        Assert.Contains("directory", said)

        // a server with nothing to answer ends cleanly
        let code, answers, _ = serve [ root; "--mcp"; "--define"; "LOCAL" ] []
        Assert.Equal(0, code)
        Assert.Empty answers
    finally
        cleanup root
