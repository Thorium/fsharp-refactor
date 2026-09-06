/// Refactoring note (GC lifetime): a lambda subscribed to an event or
/// observable captures `this`, and the publisher holds the handler — so the
/// whole subscriber object stays reachable until the handler is removed.
///
///     member this.Hook(src: Source) =
///         src.Changed.Add(fun n -> this.Bump n)
///         //                       ^^^^ pins `this` for the publisher's
///         //                            lifetime
///
/// The capture is also implicit: referencing an instance `let` field from a
/// lambda compiles to a field access through `this`, so it captures the
/// object just the same.
///
/// This is advice, not a fix: whether the coupling is intended (and whether
/// the object is large enough to matter) is the author's call. The usual
/// remedies are hoisting the needed values into locals before the lambda, or
/// keeping the subscription's IDisposable and disposing it.
///
/// Safety rules:
///   - only fires on sinks that provably store the handler: `.Add`,
///     `.AddHandler`, `.Subscribe` resolving (via typed check results) to
///     IObservable / IEvent / IDelegateEvent, and the `Observable.*` /
///     `Event.*` module functions — a `ResizeArray.Add` never matches
///   - lambda parameters shadowing the captured name suppress the note
///   - the file must have no type errors
module FSharp.Refactor.ClosureCapture

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type PublisherKind =
    /// AppDomain.CurrentDomain.*, Console.*, SystemEvents.*: a publisher
    /// that lives as long as the process, so the subscriber does too.
    | ProcessWide
    /// A publisher handed in from elsewhere: the subscriber lives as long
    /// as it does.
    | External

type Suggestion =
    {
        /// The subscribing lambda, where the hint anchors.
        Range: range
        /// The captured identifier (`this` or an instance field name).
        CapturedName: string
        /// The sink method or function name, for the message.
        SinkName: string
        /// How long the publisher holds the handler.
        Publisher: PublisherKind
    }

/// Receivers whose events are process-wide.
let private processWideRoots =
    set [ "AppDomain"; "Console"; "SystemEvents"; "Application" ]

/// The dotted names a publisher expression starts with: `System.AppDomain`
/// of `System.AppDomain.CurrentDomain.ProcessExit`, `src` of
/// `src.Fired`, `(x.Inner)` of `(x.Inner).Changed`.
let rec private leadingIds (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> [ id.idText ]
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> ids |> List.map (fun i -> i.idText)
    | SynExpr.DotGet(expr = inner)
    | SynExpr.Paren(expr = inner)
    | SynExpr.App(funcExpr = inner) -> leadingIds inner
    | _ -> []

/// Does the publisher live as long as the process? Its root, or the one
/// after a `System.` prefix, is AppDomain, Console or the like.
let private isProcessWide (ids: string list) =
    ids |> List.truncate 2 |> List.exists processWideRoots.Contains

/// A local `let e = Event<_>()` (or `new Event<_>()`) in a scope holding
/// the subscription: the publisher is born in the member and cannot
/// outlive the object (fsdocs' `docsDependenciesChanged`).
let private localEventNames (path: SyntaxNode list) =
    let constructsEvent (e: SynExpr) =
        let rec named (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = f) -> named f
            | SynExpr.TypeApp(expr = inner) -> named inner
            | SynExpr.Paren(expr = inner) -> named inner
            | SynExpr.Ident id -> id.idText = "Event"
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                (List.last ids).idText = "Event"
            | _ -> false

        match e with
        | SynExpr.New(targetType = SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)))) ->
            not ids.IsEmpty && (List.last ids).idText = "Event"
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids))) ->
            not ids.IsEmpty && (List.last ids).idText = "Event"
        | other -> named other

    path
    |> List.collect (fun node ->
        match node with
        | SyntaxNode.SynExpr(LetOrUseE lou) ->
            lou.Bindings
            |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
                match p with
                | SynPat.Named(ident = SynIdent(ident = id)) when constructsEvent rhs -> Some id.idText
                | _ -> None)
        | _ -> [])
    |> Set.ofList

/// Method names that store a handler on a long-lived publisher.
let private sinkMethods = set [ "Add"; "AddHandler"; "Subscribe" ]

/// Enclosing types whose Add/AddHandler/Subscribe members store handlers.
let private sinkEntityPrefixes =
    [ "System.IObservable"
      "Microsoft.FSharp.Control.IEvent"
      "Microsoft.FSharp.Control.IDelegateEvent"
      // the `.Add` extension on IObservable lives here
      "Microsoft.FSharp.Core.CommonExtensions" ]

/// Module functions that store a handler.
let private sinkFunctionPrefixes =
    [ "Microsoft.FSharp.Control.Observable."
      "Microsoft.FSharp.Control.Event."
      "Microsoft.FSharp.Core.CommonExtensions." ]

/// Does the method identifier resolve to an event/observable sink?
let private resolvesToSink (check: FSharpCheckFileResults) (source: ISourceText) (methodId: Ident) =
    let r = methodId.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ methodId.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            let enclosing = OptionModule.enclosingFullName value

            let fullName = OptionModule.fullNameOf value

            sinkEntityPrefixes |> List.exists enclosing.StartsWith
            || sinkFunctionPrefixes |> List.exists fullName.StartsWith
        | _ -> false
    | None -> false

/// The root identifier of a receiver expression — `x` in `x.Changed.Add`
/// or `(x.Inner).Changed.Add` — when it is a plain name.
[<TailCall>]
let rec private receiverRootLoop (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> Some id.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> Some first.idText
    | SynExpr.DotGet(expr = inner)
    | SynExpr.Paren(expr = inner) -> receiverRootLoop inner
    | _ -> None

/// A call storing a handler: the sink method, the handler, and the root
/// of the publisher's expression.
[<return: Struct>]
let private (|SinkCall|_|) (e: SynExpr) =
    let methodAndArg =
        match e with
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
            ids.Length >= 2
            ->
            ValueSome(List.last ids, arg, Some ids.Head.idText)
        | SynExpr.App(
            isInfix = false
            funcExpr = SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = ids))
            argExpr = arg) -> ValueSome(List.last ids, arg, receiverRootLoop receiver)
        | _ -> ValueNone

    match methodAndArg with
    | ValueSome(methodId, arg, receiver) when
        sinkMethods.Contains methodId.idText
        || ((methodId.idText = "add" || methodId.idText = "subscribe")
            && (match e with
                | SynExpr.App(funcExpr = SynExpr.LongIdent _) -> true
                | _ -> false))
        ->
        match stripParens arg with
        | SynExpr.Lambda _ as lambda -> ValueSome(methodId, lambda, receiver)
        // a method group — `src.Changed.Add this.OnChanged` — pins `this`
        // for the publisher's lifetime just as hard as a lambda; so does
        // one wrapped in a delegate constructor:
        // `w.Created.AddHandler(FileSystemEventHandler this.OnCreated)`
        | SynExpr.LongIdent _ as captured -> ValueSome(methodId, captured, receiver)
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident _; argExpr = inner) ->
            match stripParens inner with
            | SynExpr.LongIdent _ as captured -> ValueSome(methodId, captured, receiver)
            | _ -> ValueNone
        | _ -> ValueNone
    | _ -> ValueNone

/// Names bound by a lambda's own parameters (they shadow captures).
let private lambdaBoundNames (lambda: SynExpr) =
    match lambda with
    | SynExpr.Lambda(parsedData = Some(pats, _)) ->
        pats |> List.choose (fun p -> boundVar p |> Option.bind id) |> Set.ofList
    | _ -> Set.empty

/// Find `this`-capturing lambdas handed to event/observable sinks. Requires
/// typed check results for the sink gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // per type: (type range, instance let-bound names, member scopes)
        let typeContexts =
            [ for _, decl in index.Decls do
                  match decl with
                  | SynModuleDecl.Types(typeDefns = defns) ->
                      for typeDefn in defns do
                          match typeDefn with
                          | SynTypeDefn(typeRepr = SynTypeDefnRepr.ObjectModel(members = members)) ->
                              let ctorSelf =
                                  members
                                  |> List.tryPick (fun m ->
                                      match m with
                                      | SynMemberDefn.ImplicitCtor(selfIdentifier = Some selfId) -> Some selfId.idText
                                      | _ -> None)

                              let instanceLetNames =
                                  members
                                  |> List.collect (fun m ->
                                      match m with
                                      | SynMemberDefn.LetBindings(isStatic = false; bindings = bindings) ->
                                          bindings
                                          |> List.choose (fun (SynBinding(headPat = p)) ->
                                              match p with
                                              | SynPat.Named(ident = SynIdent(ident = var)) -> Some var.idText
                                              | SynPat.LongIdent(longDotId = SynLongIdent(id = [ f ])) ->
                                                  Some f.idText
                                              | _ -> None)
                                      | _ -> [])
                                  |> Set.ofList

                              let selfOf (SynBinding(headPat = p)) =
                                  match p with
                                  | SynPat.LongIdent(longDotId = SynLongIdent(id = [ self; _ ])) when self.idText <> "_" ->
                                      Some self.idText
                                  | _ -> None

                              let memberScopes =
                                  members
                                  |> List.collect (fun m ->
                                      match m with
                                      | SynMemberDefn.Member(memberDefn = binding) -> [ m.Range, selfOf binding ]
                                      | SynMemberDefn.GetSetMember(memberDefnForGet = g; memberDefnForSet = s) ->
                                          [ for b in List.choose id [ g; s ] -> m.Range, selfOf b ]
                                      | SynMemberDefn.LetBindings(isStatic = false) -> [ m.Range, ctorSelf ]
                                      | _ -> [])

                              typeDefn.Range, instanceLetNames, memberScopes
                          | _ -> ()
                  | _ -> () ]

        // does any expression inside `r` read or assign one of `names`?
        let mentioned (names: Set<string>) (r: range) =
            index.Exprs
            |> Array.tryPick (fun (_, e) ->
                match e with
                | SynExpr.Ident id when names.Contains id.idText && Range.rangeContainsRange r id.idRange ->
                    Some id.idText
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when
                    names.Contains firstId.idText && Range.rangeContainsRange r firstId.idRange
                    ->
                    Some firstId.idText
                | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) when
                    names.Contains firstId.idText && Range.rangeContainsRange r e.Range
                    ->
                    Some firstId.idText
                | _ -> None)

        [ for path, expr in index.Exprs do
              match expr with
              | SinkCall(methodId, lambda, receiver) ->
                  let enclosing =
                      typeContexts
                      |> List.tryPick (fun (typeRange, letNames, scopes) ->
                          if Range.rangeContainsRange typeRange expr.Range then
                              scopes
                              |> List.tryPick (fun (scopeRange, selfOpt) ->
                                  if Range.rangeContainsRange scopeRange expr.Range then
                                      Some(letNames, selfOpt)
                                  else
                                      None)
                          else
                              None)

                  match enclosing with
                  | Some(letNames, selfOpt) ->
                      let capturable =
                          Option.fold (fun names self -> Set.add self names) letNames selfOpt
                          - lambdaBoundNames lambda

                      // a publisher the object owns — its own event
                      // (`x.Disposing.Add(fun _ -> ... x ...)`), or one held
                      // in its own field — cannot outlive the object: the
                      // reference is a cycle inside one lifetime, not a leak
                      let ownPublisher =
                          match receiver with
                          | Some root -> capturable.Contains root || (localEventNames path).Contains root
                          | None -> false

                      // the publisher's own spelling — `AppDomain.CurrentDomain
                      // .UnhandledException.Add` — or, for `x |> Event.add f`,
                      // the left side of the pipe
                      let publisherIds =
                          match expr with
                          | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
                              ids |> List.map (fun i -> i.idText)
                          | SynExpr.App(funcExpr = SynExpr.DotGet(expr = receiverExpr)) -> leadingIds receiverExpr
                          | _ -> []

                      let pipedIds =
                          match path with
                          | SyntaxNode.SynExpr(SynExpr.App(
                              funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = lhs))) :: _ when
                              op.idText = "op_PipeRight"
                              ->
                              leadingIds lhs
                          | _ -> []

                      let publisher =
                          if isProcessWide publisherIds || isProcessWide pipedIds then
                              PublisherKind.ProcessWide
                          else
                              PublisherKind.External

                      match mentioned capturable lambda.Range with
                      | Some captured when not ownPublisher && resolvesToSink check source methodId ->
                          { Range = lambda.Range
                            CapturedName = captured
                            SinkName = methodId.idText
                            Publisher = publisher }
                      | _ -> ()
                  | None -> ()
              | _ -> () ]
