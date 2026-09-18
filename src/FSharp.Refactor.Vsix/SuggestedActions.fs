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

/// An edit pinned to the snapshot it was computed against: its span
/// there, the text that span held, and the text replacing it.
type PinnedEdit =
    {
        Span: SnapshotSpan
        OldText: string
        NewText: string
    }

/// The edits placed on the snapshot the light bulb was built from — the
/// text the sidecar's diagnostics describe. The same line and column on
/// a LATER snapshot is wherever the user's typing has since moved that
/// text, and applying there rewrote the wrong characters.
let private pin (snapshot: ITextSnapshot) (edits: Edit list) : PinnedEdit list =
    edits
    |> List.choose (fun e ->
        match spanOfEdit snapshot e with
        | ValueSome span ->
            let (_, _, _, _, newText) = e
            let pinned = SnapshotSpan(snapshot, span)

            Some
                {
                    Span = pinned
                    OldText = pinned.GetText()
                    NewText = newText
                }
        | ValueNone -> None)

/// The preview pane: what each edit removes and what it puts there,
/// one monospace block per edit, long texts cut at a dozen lines.
let private previewOf (edits: PinnedEdit list) : obj =
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

    for edit in edits |> List.sortBy (fun e -> e.Span.Start.Position) do
        if edit.OldText <> "" then
            panel.Children.Add(block "- " edit.OldText (SolidColorBrush(Color.FromRgb(180uy, 60uy, 60uy))))
            |> ignore

        if edit.NewText <> "" then
            panel.Children.Add(block "+ " edit.NewText (SolidColorBrush(Color.FromRgb(50uy, 140uy, 60uy))))
            |> ignore

    box panel

/// One light-bulb entry. `snapshot` is the buffer as it was when the
/// actions were built: the edits are pinned to it, and applied only where
/// the buffer's own edit history says that text now is.
type FixAction(buffer: ITextBuffer, snapshot: ITextSnapshot, title: string, edits: Edit list) =
    let pinned = pin snapshot edits

    interface ISuggestedAction with
        member _.DisplayText = title
        member _.IconMoniker = Unchecked.defaultof<ImageMoniker>
        member _.IconAutomationText = null
        member _.InputGestureText = null
        member _.HasActionSets = false

        member _.GetActionSetsAsync _ =
            Task.FromResult(Seq.empty: IEnumerable<SuggestedActionSet>)

        member _.HasPreview = not pinned.IsEmpty

        member _.GetPreviewAsync _ =
            try
                Task.FromResult(previewOf pinned)
            with ex ->
                FsacClient.clientTrace $"preview '{title}' FAILED: {ex}"
                Task.FromResult<obj> null

        member _.Invoke(_ct) =
            // nothing thrown leaves Invoke: it is called by the light-bulb
            // host, where an exception is Visual Studio's to crash on
            try
                FsacClient.clientTrace $"invoke '{title}' with {List.length pinned} edit(s)"
                let current = buffer.CurrentSnapshot

                // each span follows the buffer's edit history from the
                // snapshot it was pinned to; an edit whose text is no
                // longer what the fix was computed against is stale, and
                // the whole fix is skipped rather than half-applied
                let translated =
                    pinned
                    |> List.map (fun e -> e.Span.TranslateTo(current, SpanTrackingMode.EdgeExclusive), e)

                let drifted =
                    current.Version.VersionNumber <> snapshot.Version.VersionNumber
                    && translated |> List.exists (fun (span, e) -> span.GetText() <> e.OldText)

                if drifted then
                    FsacClient.clientTrace
                        $"invoke '{title}' skipped: the document changed under it (v{snapshot.Version.VersionNumber} -> v{current.Version.VersionNumber})"
                else
                    use edit = buffer.CreateEdit()

                    // bottom-up, so earlier replacements never shift later spans
                    for span, e in translated |> List.sortByDescending (fun (span, _) -> span.Start.Position) do
                        edit.Replace(span.Span, e.NewText) |> ignore

                    edit.Apply() |> ignore
                    FsacClient.clientTrace $"invoke '{title}' applied"
            with ex ->
                FsacClient.clientTrace $"invoke '{title}' FAILED: {ex}"

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

    /// The sidecar round trip: the actions for the diagnostics in a span,
    /// pinned to the snapshot the span was asked about on.
    let build (snapshot: ITextSnapshot) (diags: Lsp.Diag list) =
        let raw = FsacClient.codeActions filePath diags

        FsacClient.clientTrace $"code actions: {List.length diags} diag(s) -> {List.length raw} action(s)"

        disambiguate raw
        |> List.map (fun (title, edits) -> new FixAction(buffer, snapshot, title, edits) :> ISuggestedAction)

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
            [
                SuggestedActionSet(PredefinedSuggestedActionCategoryNames.CodeFix, actions, "FSharp.Refactor")
            ]
            :> seq<_>

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
                            build range.Snapshot diags
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

                    // on the UI thread, inside the light-bulb host: an
                    // exception here is MEF's, and Visual Studio's, to fail
                    // on — the bulb shows nothing instead
                    try
                        toSets (build range.Snapshot diags)
                    with ex ->
                        FsacClient.clientTrace
                            $"code actions on the UI thread FAILED: {ex.GetType().Name}: {ex.Message}"

                        Seq.empty

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
