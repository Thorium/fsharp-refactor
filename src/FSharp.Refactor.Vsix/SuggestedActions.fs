/// Light bulbs: one ISuggestedAction per code action the sidecar offers
/// for the FR diagnostics under the caret. The action titles come from
/// FsAutoComplete, the edits are applied straight to the ITextBuffer.
///
/// Visual Studio asks `HasSuggestedActionsAsync` first, off the UI
/// thread, and only then `GetSuggestedActions` on it. The sidecar round
/// trip happens in the first call and is cached for the second, keyed by
/// the snapshot version and the span asked about; the UI thread waits on
/// the sidecar only when the two calls disagree, which is the fallback.
module FSharp.Refactor.Vsix.SuggestedActions

open System
open System.Collections.Generic
open System.ComponentModel.Composition
open System.Threading.Tasks
open System.Windows
open System.Windows.Controls
open System.Windows.Media
open Microsoft.VisualStudio.Imaging.Interop
open Microsoft.VisualStudio.Language.Intellisense
open Microsoft.VisualStudio.Text
open Microsoft.VisualStudio.Text.Editor
open Microsoft.VisualStudio.Utilities
open FSharp.Refactor.Vsix

/// An LSP text edit: start line, start column, end line, end column, text.
type Edit = int * int * int * int * string

/// The span an edit addresses in a snapshot, clamped to the lines it
/// names; None past the end of the document.
let private spanOfEdit (snapshot: ITextSnapshot) ((sl, sc, el, ec, _): Edit) =
    if sl < snapshot.LineCount && el < snapshot.LineCount then
        let startLine = snapshot.GetLineFromLineNumber sl
        let endLine = snapshot.GetLineFromLineNumber el
        let startPos = startLine.Start.Position + min sc startLine.Length
        let endPos = endLine.Start.Position + min ec endLine.Length
        ValueSome(Span(startPos, max 0 (endPos - startPos)))
    else
        ValueNone

/// The preview pane: what each edit removes and what it puts there,
/// one monospace block per edit, long texts cut at a dozen lines.
let private previewOf (snapshot: ITextSnapshot) (edits: Edit list) : obj =
    let clip (text: string) =
        let lines = text.Replace("\r\n", "\n").Split '\n'

        if lines.Length > 12 then
            String.Join("\n", Array.append (Array.take 12 lines) [| "…" |])
        else
            text

    let block (prefix: string) (text: string) (brush: Brush) =
        let shown =
            String.Join("\n", (clip text).Split '\n' |> Array.map (fun l -> prefix + l))

        TextBlock(
            Text = shown,
            FontFamily = FontFamily "Consolas",
            Foreground = brush,
            TextWrapping = TextWrapping.NoWrap,
            Margin = Thickness(0., 0., 0., 2.)
        )

    let panel = StackPanel(Orientation = Orientation.Vertical, Margin = Thickness 4.)

    for edit in edits |> List.sortBy (fun (sl, sc, _, _, _) -> sl, sc) do
        let (_, _, _, _, newText) = edit

        let oldText =
            match spanOfEdit snapshot edit with
            | ValueSome span -> snapshot.GetText span
            | ValueNone -> ""

        if oldText <> "" then
            panel.Children.Add(block "- " oldText (SolidColorBrush(Color.FromRgb(180uy, 60uy, 60uy))))
            |> ignore

        if newText <> "" then
            panel.Children.Add(block "+ " newText (SolidColorBrush(Color.FromRgb(50uy, 140uy, 60uy))))
            |> ignore

    box panel

type FixAction(buffer: ITextBuffer, title: string, edits: Edit list) =
    interface ISuggestedAction with
        member _.DisplayText = title
        member _.IconMoniker = Unchecked.defaultof<ImageMoniker>
        member _.IconAutomationText = null
        member _.InputGestureText = null
        member _.HasActionSets = false

        member _.GetActionSetsAsync _ =
            Task.FromResult(Seq.empty: IEnumerable<SuggestedActionSet>)

        member _.HasPreview = not edits.IsEmpty

        member _.GetPreviewAsync _ =
            try
                Task.FromResult(previewOf buffer.CurrentSnapshot edits)
            with ex ->
                FsacClient.clientTrace $"preview '{title}' FAILED: {ex}"
                Task.FromResult<obj> null

        member _.Invoke(_ct) =
            try
                FsacClient.clientTrace $"invoke '{title}' with {List.length edits} edit(s)"
                let snapshot = buffer.CurrentSnapshot

                use edit = buffer.CreateEdit()

                // bottom-up, so earlier replacements never shift later spans
                for e in edits |> List.sortByDescending (fun (sl, sc, _, _, _) -> sl, sc) do
                    match spanOfEdit snapshot e with
                    | ValueSome span ->
                        let (_, _, _, _, newText) = e
                        edit.Replace(span, newText) |> ignore
                    | ValueNone -> ()

                edit.Apply() |> ignore
                FsacClient.clientTrace $"invoke '{title}' applied"
            with ex ->
                FsacClient.clientTrace $"invoke '{title}' FAILED: {ex}"
                reraise ()

        member _.TryGetTelemetryId(telemetryId: byref<Guid>) =
            telemetryId <- Guid.Empty
            false

    interface IDisposable with
        member _.Dispose() = ()

/// FsAutoComplete titles every analyzer fix "Fix <code>", so a primary
/// and its alternatives render as identical menu entries; the replacement
/// text is appended so the user can tell which fix is which (upstreaming
/// the title fix to FSAC is the durable version of this).
let private disambiguate (raw: (string * Edit list) list) =
    let duplicated =
        raw
        |> List.countBy fst
        |> List.filter (fun (_, n) -> n > 1)
        |> List.map fst
        |> Set.ofList

    raw
    |> List.map (fun (title, edits) ->
        match edits with
        | (_, _, _, _, newText) :: _ when duplicated.Contains title ->
            let firstLine =
                let t = newText.Trim()
                let i = t.IndexOfAny [| '\r'; '\n' |]
                let line = if i >= 0 then t.Substring(0, i) else t

                if line.Length > 50 then
                    line.Substring(0, 47) + "..."
                else
                    line

            $"{title} → {firstLine}", edits
        | _ -> title, edits)

type FrActionsSource(buffer: ITextBuffer, filePath: string) =
    let key = FsacClient.normalizePath filePath
    let changed = Event<EventHandler<EventArgs>, EventArgs>()
    let gate = obj ()

    /// The actions computed by the last `HasSuggestedActionsAsync`:
    /// snapshot version, the span asked about, and the actions for it.
    let mutable cached: (int * Span * ISuggestedAction list) option = None

    let subscription =
        FsacClient.diagnosticsChanged.Publish.Subscribe(fun changedPath ->
            if String.Equals(changedPath, key, StringComparison.OrdinalIgnoreCase) then
                lock gate (fun () -> cached <- None)
                changed.Trigger(null, EventArgs.Empty))

    let diagsAt (range: SnapshotSpan) =
        ErrorTagger.diagsFor filePath
        |> List.filter (fun d ->
            match ErrorTagger.spanOf range.Snapshot d with
            | Some span -> span.IntersectsWith range
            | None -> false)

    /// The sidecar round trip: the actions for the diagnostics in a span.
    let build (diags: Lsp.Diag list) =
        let raw = FsacClient.codeActions filePath diags

        FsacClient.clientTrace $"code actions: {List.length diags} diag(s) -> {List.length raw} action(s)"

        disambiguate raw
        |> List.map (fun (title, edits) -> FixAction(buffer, title, edits) :> ISuggestedAction)

    let cacheFor (range: SnapshotSpan) =
        lock gate (fun () ->
            match cached with
            | Some(version, span, actions) when version = range.Snapshot.Version.VersionNumber && span = range.Span ->
                Some actions
            | _ -> None)

    let toSets (actions: ISuggestedAction list) =
        if actions.IsEmpty then
            Seq.empty
        else
            [ SuggestedActionSet(PredefinedSuggestedActionCategoryNames.CodeFix, actions, "FSharp.Refactor") ] :> seq<_>

    do FsacClient.clientTrace $"actions source created for {filePath}"

    interface ISuggestedActionsSource with
        [<CLIEvent>]
        member _.SuggestedActionsChanged = changed.Publish

        member _.HasSuggestedActionsAsync(_categories, range, _ct) =
            match diagsAt range with
            | [] -> Task.FromResult false
            | diags ->
                // off the UI thread: fetch now, answer from the cache when
                // the light bulb opens
                Task.Run(fun () ->
                    let actions =
                        try
                            build diags
                        with ex ->
                            FsacClient.clientTrace $"prefetch FAILED: {ex.Message}"
                            []

                    lock gate (fun () -> cached <- Some(range.Snapshot.Version.VersionNumber, range.Span, actions))
                    not actions.IsEmpty)

        member _.GetSuggestedActions(_categories, range, _ct) =
            match cacheFor range with
            | Some actions -> toSets actions
            | None ->
                // the calls disagreed on the span or the buffer moved on:
                // the sidecar's 5s cap bounds this wait
                match diagsAt range with
                | [] -> Seq.empty
                | diags ->
                    FsacClient.clientTrace "code actions: cache miss, fetching on the UI thread"
                    toSets (build diags)

        member _.TryGetTelemetryId(telemetryId: byref<Guid>) =
            telemetryId <- Guid.Empty
            false

    interface IDisposable with
        member _.Dispose() = subscription.Dispose()

[<Export(typeof<ISuggestedActionsSourceProvider>)>]
[<Name "FSharp.Refactor Suggested Actions">]
[<ContentType "F#">]
type FrActionsSourceProvider() =
    interface ISuggestedActionsSourceProvider with
        member _.CreateSuggestedActionsSource(_view: ITextView, buffer: ITextBuffer) =
            match BufferSessions.ensureFor buffer with
            | Some session -> new FrActionsSource(buffer, session.FilePath) :> ISuggestedActionsSource
            | None -> null
