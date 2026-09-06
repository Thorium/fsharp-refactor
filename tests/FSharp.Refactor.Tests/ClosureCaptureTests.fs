module FSharp.Refactor.Tests.ClosureCaptureTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

let private capturesIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    ClosureCapture.find tree sourceText checkResults

[<Literal>]
let private sourcePrefix =
    "type Src() =\n    let fired = Event<int>()\n    member _.Fired = fired.Publish\n"

[<Fact>]
let ``this-capturing event handler is noted`` () =
    let suggestions =
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member this.Hook() = src.Fired.Add(fun n -> this.Bump n)\n    member this.Bump n = total <- total + n"
        )

    match suggestions with
    | [ s ] ->
        Assert.Equal("this", s.CapturedName)
        Assert.Equal("Add", s.SinkName)
    | other -> failwithf "Expected exactly one capture note, got %A" other

[<Fact>]
let ``instance field capture is an implicit this capture`` () =
    let suggestions =
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member _.Hook() = src.Fired.Add(fun n -> total <- total + n)\n    member _.Total = total"
        )

    match suggestions with
    | [ s ] -> Assert.Equal("total", s.CapturedName)
    | other -> failwithf "Expected exactly one field-capture note, got %A" other

[<Fact>]
let ``stateless handler is fine`` () =
    Assert.Empty(
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    member _.Hook() = src.Fired.Add(fun n -> printfn \"%d\" n)"
        )
    )

[<Fact>]
let ``a handler on an event created in the same member is not a leak`` () =
    // fsdocs' `let docsDependenciesChanged = Event<string>()` followed by
    // `docsDependenciesChanged.Publish.Add(fun ...)` in one member: the
    // publisher is born there and cannot outlive the object
    Assert.Empty(
        capturesIn
            "type Watcher() =\n    let mutable total = 0\n    member this.Run() =\n        let changed = Event<string>()\n        changed.Publish.Add(fun s -> this.Bump s.Length)\n        changed.Trigger \"x\"\n    member this.Bump n = total <- total + n"
    )

    Assert.Empty(
        capturesIn
            "type Watcher() =\n    let mutable total = 0\n    member this.Run() =\n        let changed = new Event<string>()\n        changed.Publish.Add(fun s -> this.Bump s.Length)\n        changed.Trigger \"x\"\n    member this.Bump n = total <- total + n"
    )

[<Fact>]
let ``a process-wide publisher is told apart from one handed in`` () =
    // fsi: `AppDomain.CurrentDomain.ProcessExit |> Event.add (fun _ -> ...)`
    // and `AppDomain.CurrentDomain.UnhandledException.Add(fun args -> ...)`
    // pin the object until the process exits
    let publisherOf (source: string) =
        match capturesIn source with
        | [ s ] -> s.Publisher
        | other -> failwithf "Expected exactly one capture note, got %A" other

    Assert.Equal(
        ClosureCapture.PublisherKind.ProcessWide,
        publisherOf
            "type Host() =\n    let mutable exits = 0\n    member this.Hook() = System.AppDomain.CurrentDomain.ProcessExit |> Event.add (fun _ -> this.Bump())\n    member this.Bump() = exits <- exits + 1"
    )

    Assert.Equal(
        ClosureCapture.PublisherKind.ProcessWide,
        publisherOf
            "type Host() =\n    let mutable exits = 0\n    member this.Hook() = System.AppDomain.CurrentDomain.UnhandledException.Add(fun _ -> this.Bump())\n    member this.Bump() = exits <- exits + 1"
    )

    // a publisher handed in lives as long as its owner does
    Assert.Equal(
        ClosureCapture.PublisherKind.External,
        publisherOf (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member this.Hook() = src.Fired.Add(fun n -> this.Bump n)\n    member this.Bump n = total <- total + n"
        )
    )

[<Fact>]
let ``Subscribe is also a sink`` () =
    let suggestions =
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member this.Hook() = src.Fired.Subscribe(fun n -> this.Bump n) |> ignore\n    member this.Bump n = total <- total + n"
        )

    match suggestions with
    | [ s ] -> Assert.Equal("Subscribe", s.SinkName)
    | other -> failwithf "Expected exactly one Subscribe note, got %A" other

[<Fact>]
let ``Observable module functions are sinks`` () =
    let suggestions =
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member this.Hook() = src.Fired |> Observable.add (fun n -> this.Bump n)\n    member this.Bump n = total <- total + n"
        )

    match suggestions with
    | [ s ] -> Assert.Equal("add", s.SinkName)
    | other -> failwithf "Expected exactly one Observable.add note, got %A" other

[<Fact>]
let ``ResizeArray Add is not a sink`` () =
    Assert.Empty(
        capturesIn
            "type Keeper() =\n    let handlers = ResizeArray<int -> unit>()\n    member this.Hook() = handlers.Add(fun n -> this.Bump n)\n    member _.Bump(n: int) = ignore n"
    )

[<Fact>]
let ``shadowing lambda parameter suppresses the note`` () =
    Assert.Empty(
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member _.Hook(f: int -> int) = src.Fired.Add(fun total -> ignore (total + 1))\n    member _.Total = total"
        )
    )

[<Fact>]
let ``module-level subscription has no this to capture`` () =
    Assert.Empty(
        capturesIn (
            sourcePrefix
            + "let src = Src()\nlet hook () = src.Fired.Add(fun n -> printfn \"%d\" n)"
        )
    )

[<Fact>]
let ``a method-group subscription pins this too`` () =
    // `src.Fired.Add this.Bump` holds `this` for the publisher's lifetime
    // just as hard as a lambda
    let suggestions =
        capturesIn (
            sourcePrefix
            + "type Sub(src: Src) =\n    let mutable total = 0\n    member this.Hook() = src.Fired.Add this.Bump\n    member this.Bump n = total <- total + n"
        )

    match suggestions with
    | [ s ] -> Assert.Equal("this", s.CapturedName)
    | other -> failwithf "Expected exactly one method-group note, got %A" other

[<Fact>]
let ``a handler on the object's own event is a cycle inside one lifetime`` () =
    // FSharp.Data's `x.Disposing.Add(fun _ -> ... x ...)`: the publisher IS
    // the captured object, so nothing outlives anything
    Assert.Empty(
        capturesIn (
            sourcePrefix
            + "type Sub() as x =\n    let fired = Event<int>()\n    let mutable total = 0\n    do x.Fired.Add(fun n -> x.Bump n)\n    member _.Fired = fired.Publish\n    member this.Bump n = total <- total + n"
        )
    )

[<Fact>]
let ``a handler on a publisher held in the object's own field is owned too`` () =
    Assert.Empty(
        capturesIn (
            sourcePrefix
            + "type Sub() =\n    let src = Src()\n    let mutable total = 0\n    member this.Hook() = src.Fired.Add(fun n -> this.Bump n)\n    member this.Bump n = total <- total + n"
        )
    )
