/// Squiggles: an IErrorTag per FR diagnostic. The predefined
/// "suggestion" error types render as a few gray dots at the span start
/// — invisible in practice — so the extension registers its OWN error
/// type with a full-length squiggle in a distinct color (recolorable
/// under Fonts and Colors as "FSharp.Refactor Hint").
module FSharp.Refactor.Vsix.ErrorTagger

open System
open System.ComponentModel.Composition
open Microsoft.VisualStudio.Text
open Microsoft.VisualStudio.Text.Adornments
open Microsoft.VisualStudio.Text.Classification
open Microsoft.VisualStudio.Text.Editor
open Microsoft.VisualStudio.Text.Tagging
open Microsoft.VisualStudio.Utilities
open FSharp.Refactor.Vsix
open FSharp.Refactor.Vsix.Lsp

[<Literal>]
let FrHintErrorType = "fsharp-refactor-hint"

type FrErrorTypeExports() =
    [<Export(typeof<ErrorTypeDefinition>); Name(FrHintErrorType)>]
    member val FrHintDefinition: ErrorTypeDefinition = null with get, set

[<Export(typeof<EditorFormatDefinition>); Name(FrHintErrorType); UserVisible true>]
type FrHintFormat() as this =
    inherit EditorFormatDefinition()

    do
        this.DisplayName <- "FSharp.Refactor Hint"
        this.ForegroundColor <- Nullable(System.Windows.Media.Colors.MediumPurple)

/// LSP 0-based positions -> a span on the current snapshot; None when the
/// document has drifted past the diagnostic (a recheck is coming).
let spanOf (snapshot: ITextSnapshot) (d: Diag) : SnapshotSpan option =
    if d.StartLine >= snapshot.LineCount || d.EndLine >= snapshot.LineCount then
        None
    else
        let startLine = snapshot.GetLineFromLineNumber d.StartLine
        let endLine = snapshot.GetLineFromLineNumber d.EndLine
        let startPos = startLine.Start.Position + min d.StartCol startLine.Length
        let endPos = endLine.Start.Position + min d.EndCol endLine.Length

        if endPos > startPos && endPos <= snapshot.Length then
            Some(SnapshotSpan(snapshot, Span(startPos, endPos - startPos)))
        else
            None

/// The document's current FR diagnostics, by normalized path.
let diagsFor (filePath: string) =
    match FsacClient.diagnostics.TryGetValue(FsacClient.normalizePath filePath) with
    | true, ds -> ds
    | _ -> []

type FrTagger(buffer: ITextBuffer, filePath: string) as this =
    let key = FsacClient.normalizePath filePath

    let tagsChanged =
        Event<EventHandler<SnapshotSpanEventArgs>, SnapshotSpanEventArgs>()

    let mutable lastTraced = -1

    // GetTags runs on every scroll, edit and layout pass, so nothing in it may
    // be O(diagnostics) if it can be helped. The list from the client is
    // replaced wholesale when diagnostics change, so a reference check tells us
    // whether the array is stale - O(1) on the hot path, O(n) only on change.
    let mutable cachedSource: Diag list = []
    let mutable cached: Diag[] = [||]

    let currentDiags () =
        let ds = diagsFor filePath

        if not (obj.ReferenceEquals(ds, cachedSource)) then
            cachedSource <- ds
            cached <- List.toArray ds

        cached

    let subscription =
        FsacClient.diagnosticsChanged.Publish.Subscribe(fun changedPath ->
            if String.Equals(changedPath, key, StringComparison.OrdinalIgnoreCase) then
                let snapshot = buffer.CurrentSnapshot
                FsacClient.clientTrace $"tagger refresh: {List.length (diagsFor filePath)} diags for {filePath}"

                tagsChanged.Trigger(this, SnapshotSpanEventArgs(SnapshotSpan(snapshot, Span(0, snapshot.Length)))))

    do FsacClient.clientTrace $"tagger created for {filePath}"

    interface ITagger<IErrorTag> with
        [<CLIEvent>]
        member _.TagsChanged = tagsChanged.Publish

        member _.GetTags(spans: NormalizedSnapshotSpanCollection) =
            if spans.Count = 0 then
                Seq.empty
            else
                let snapshot = spans[0].Snapshot
                let diags = currentDiags ()

                if diags.Length <> lastTraced then
                    lastTraced <- diags.Length
                    FsacClient.clientTrace $"GetTags sees {lastTraced} diags for {filePath}"

                // A NormalizedSnapshotSpanCollection is sorted and
                // non-overlapping, so the whole requested region is bounded by
                // its first and last span. Two line lookups here replace two
                // per diagnostic: a diagnostic outside the window is rejected
                // by integer comparison, without touching the snapshot at all.
                let firstLine = snapshot.GetLineNumberFromPosition spans[0].Start.Position
                let lastLine = snapshot.GetLineNumberFromPosition spans[spans.Count - 1].End.Position

                let tags = ResizeArray<ITagSpan<IErrorTag>>()

                for i in 0 .. diags.Length - 1 do
                    let d = diags[i]

                    // spans an edge of the window, or sits inside it
                    if d.EndLine >= firstLine && d.StartLine <= lastLine then
                        match spanOf snapshot d with
                        | Some span ->
                            // indexed, to avoid an enumerator per diagnostic
                            let mutable hit = false
                            let mutable j = 0

                            while not hit && j < spans.Count do
                                if spans[j].IntersectsWith span then
                                    hit <- true

                                j <- j + 1

                            if hit then
                                tags.Add(
                                    TagSpan<IErrorTag>(span, ErrorTag(FrHintErrorType, $"{d.Code}: {d.Message}"))
                                    :> ITagSpan<IErrorTag>
                                )
                        | None -> ()

                tags :> seq<ITagSpan<IErrorTag>>

    interface IDisposable with
        member _.Dispose() = subscription.Dispose()

[<Export(typeof<IViewTaggerProvider>)>]
[<ContentType "F#">]
[<TagType(typeof<IErrorTag>)>]
[<TextViewRole(PredefinedTextViewRoles.Document)>]
type FrTaggerProvider() =
    interface IViewTaggerProvider with
        member _.CreateTagger<'T when 'T :> ITag>(_view: ITextView, buffer: ITextBuffer) : ITagger<'T> =
            match BufferSessions.ensureFor buffer with
            | Some session -> FrTagger(buffer, session.FilePath) |> box :?> ITagger<'T>
            | None -> null
