/// The slice of the Language Server Protocol this extension speaks with
/// its FsAutoComplete sidecar: Content-Length framing over stdio, and the
/// handful of message shapes we send or read. Hand-rolled on purpose —
/// the full client libraries drag in half an ecosystem for what is four
/// notifications and one request.
module FSharp.Refactor.Vsix.Lsp

open System
open System.Collections.Concurrent
open System.IO
open System.Text
open System.Threading
open System.Threading.Tasks
open Newtonsoft.Json.Linq

/// One JSON-RPC connection over a pair of streams (the sidecar's stdio).
/// `onError` receives handler failures: the listener runs on a raw
/// background thread where an escaped exception TERMINATES the host
/// process (it took Visual Studio down once), so nothing thrown by a
/// handler may leave this type.
type JsonRpc(input: Stream, output: Stream, onError: string -> unit) =
    let writeLock = obj ()
    let mutable nextId = 0
    let pending = ConcurrentDictionary<int, TaskCompletionSource<JToken>>()
    let notificationHandlers = ConcurrentDictionary<string, JToken -> unit>()

    let send (payload: JObject) =
        let json = payload.ToString Newtonsoft.Json.Formatting.None
        let bytes = Encoding.UTF8.GetBytes json
        let header = Encoding.ASCII.GetBytes $"Content-Length: {bytes.Length}\r\n\r\n"

        lock writeLock (fun () ->
            output.Write(header, 0, header.Length)
            output.Write(bytes, 0, bytes.Length)
            output.Flush())

    /// Blocking read loop; run it on a background thread.
    member _.Listen(ct: CancellationToken) =
        use reader = new BinaryReader(input)

        let readLine () =
            let sb = StringBuilder()

            let mutable c = reader.ReadByte()

            while c <> 10uy do
                if c <> 13uy then
                    sb.Append(char c) |> ignore

                c <- reader.ReadByte()

            sb.ToString()

        try
            while not ct.IsCancellationRequested do
                let mutable contentLength = 0
                let mutable line = readLine ()

                while line <> "" do
                    if line.StartsWith("Content-Length:", StringComparison.OrdinalIgnoreCase) then
                        contentLength <- int (line.Substring(15).Trim())

                    line <- readLine ()

                let body = reader.ReadBytes contentLength

                // a single bad message (or a throwing handler) must not
                // end the listener, and it must NEVER escape this thread
                try
                    let msg = JObject.Parse(Encoding.UTF8.GetString body)

                    match msg.TryGetValue "id", msg.TryGetValue "method" with
                    | (true, idTok), (false, _) ->
                        // response to one of our requests
                        match pending.TryRemove(idTok.Value<int>()) with
                        | true, tcs ->
                            match msg.TryGetValue "result" with
                            | true, result -> tcs.TrySetResult result |> ignore
                            | _ -> tcs.TrySetResult(JValue.CreateNull()) |> ignore
                        | _ -> ()
                    | _, (true, methodTok) ->
                        let name = methodTok.Value<string>()

                        match notificationHandlers.TryGetValue name with
                        | true, handler ->
                            match msg.TryGetValue "params" with
                            | true, p -> handler p
                            | _ -> handler (JValue.CreateNull())
                        | _ ->
                            // server-to-client REQUESTS we do not implement get an
                            // empty success so the sidecar never stalls on us
                            match msg.TryGetValue "id" with
                            | true, idTok ->
                                send (
                                    JObject(
                                        [
                                            JProperty("jsonrpc", "2.0")
                                            JProperty("id", idTok)
                                            JProperty("result", JValue.CreateNull())
                                        ]
                                    )
                                )
                            | _ -> ()
                    | _ -> ()
                with
                | :? EndOfStreamException
                | :? ObjectDisposedException
                | :? IOException -> reraise ()
                | ex -> onError $"listener: message handling failed: {ex}"
        with
        | :? EndOfStreamException
        | :? ObjectDisposedException
        | :? IOException ->
            // sidecar exited; pending requests fail fast
            for kv in pending do
                kv.Value.TrySetCanceled(ct) |> ignore

    member _.OnNotification(name: string, handler: JToken -> unit) = notificationHandlers[name] <- handler

    member _.Notify(name: string, parameters: JToken) =
        send (
            JObject(
                [
                    JProperty("jsonrpc", "2.0")
                    JProperty("method", name)
                    JProperty("params", parameters)
                ]
            )
        )

    member _.Request(name: string, parameters: JToken) : Task<JToken> =
        let id = Interlocked.Increment &nextId

        let tcs =
            TaskCompletionSource<JToken>(TaskCreationOptions.RunContinuationsAsynchronously)

        pending[id] <- tcs

        send (
            JObject(
                [
                    JProperty("jsonrpc", "2.0")
                    JProperty("id", id)
                    JProperty("method", name)
                    JProperty("params", parameters)
                ]
            )
        )

        tcs.Task

/// A diagnostic as published by the sidecar, kept in LSP coordinates
/// (0-based lines/columns) and mapped to editor spans at render time.
type Diag =
    {
        StartLine: int
        StartCol: int
        EndLine: int
        EndCol: int
        Code: string
        Message: string
        /// The raw LSP diagnostic, passed back verbatim in codeAction
        /// requests so the server can match fixes to it.
        Raw: JToken
    }

let parseDiagnostics (p: JToken) : string * Diag list =
    let uri = p["uri"].Value<string>()

    let diags =
        match p["diagnostics"] with
        | :? JArray as arr ->
            [
                for d in arr do
                    let range = d["range"]

                    let code =
                        match d["code"] with
                        | null -> ""
                        | c -> c.ToString()

                    {
                        StartLine = range["start"].["line"].Value<int>()
                        StartCol = range["start"].["character"].Value<int>()
                        EndLine = range["end"].["line"].Value<int>()
                        EndCol = range["end"].["character"].Value<int>()
                        Code = code
                        Message =
                            (match d["message"] with
                             | null -> ""
                             | m -> m.Value<string>())
                        Raw = d
                    }
            ]
        | _ -> []

    uri, diags

let uriOfPath (path: string) : string = Uri(path).AbsoluteUri

/// Total: a non-file or malformed URI comes back verbatim rather than
/// throwing on the listener thread.
let pathOfUri (uri: string) : string =
    try
        Uri(uri).LocalPath
    with _ -> // fsharpanalyzer: ignore-line FR0055
        uri
