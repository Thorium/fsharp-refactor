/// Two type-design notes in the ReSharper tradition:
///
/// 1. Disposable field, no IDisposable (FR0032): a type that CREATES a
///    disposable (`let stream = new FileStream(...)`) but does not
///    implement IDisposable leaves the resource with no owner to dispose
///    it. Only `new`-constructed instance fields count — a field assigned
///    from a constructor parameter is injected, and the injector owns it.
///
/// 2. Could-be-static member (FR0033): an instance member whose body
///    touches no instance state — no self identifier, no instance let
///    field or function (whatever pattern the let binds), no
///    primary-constructor parameter, no `base` — can be a
///    `static member`. Advice only: call sites would change from
///    `obj.M(...)` to `Type.M(...)`, which is an API change on a public
///    member, so the note follows the Visibility gate: confined
///    (private/internal) members always, public ones under
///    --api-changes, and beside a signature file only private ones.
///    Protocol stubs stay quiet: a `()`-bodied or `inline` member mirrors
///    a shape rather than computing anything, and a type whose instances
///    are boxed to `obj` in the file is consumed by reflection or
///    dynamic dispatch, where a static member is invisible.
module FSharp.Refactor.ObjectDesign

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type DisposableFieldSuggestion =
    {
        TypeName: string
        FieldName: string
        Range: range
        /// The base class when it is disposable itself: the field then
        /// belongs in the base's Dispose, not in a second interface.
        DisposableBase: string option
        /// The editor's fix, carried by the type's FIRST such field only:
        /// an `interface System.IDisposable` appended to the type whose
        /// Dispose disposes every created field. Deliberately the plain
        /// form — no Dispose(bool), no finalizer, no GC.SuppressFinalize:
        /// a type holding managed disposables needs none of that.
        Fix: (range * string * string) option
    }

type StaticMemberSuggestion = { MemberName: string; Range: range }

/// FR0047 (CA2213): a disposable field the type's Dispose never releases.
type UndisposedFieldSuggestion =
    {
        TypeName: string
        FieldName: string
        Range: range
        /// The Dispose body DOES touch the field — it just never disposes
        /// it. `member this.Dispose() = cts.Cancel()` cancels the token
        /// and leaves the handle (fantomas's LSPFantomasService, and
        /// CloudAgent's connection factory both do exactly this): the
        /// author clearly meant to clean up, so the message says which
        /// half is missing rather than claiming nothing was done.
        MentionedOnly: bool
        /// The editor's fix: `field.Dispose()` as the first statement of
        /// the type's Dispose body.
        Fix: (range * string * string) option
    }

let private isDisposableName (name: string) = name = "System.IDisposable"

/// Is the type (after abbreviations) IDisposable or an implementation?
let private isDisposableType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.TryFullName |> Option.exists isDisposableName
            || t.TypeDefinition.AllInterfaces
               |> Seq.exists (fun i ->
                   i.HasTypeDefinition
                   && (i.TypeDefinition.TryFullName |> Option.exists isDisposableName)))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// Is the entity IDisposable or an implementation?
let entityIsDisposable (entity: FSharpEntity) =
    try
        entity.TryFullName |> Option.exists isDisposableName
        || entity.AllInterfaces
           |> Seq.exists (fun i ->
               i.HasTypeDefinition
               && (i.TypeDefinition.TryFullName |> Option.exists isDisposableName))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// Does the binder at this location resolve to an IDisposable-implementing
/// type? Shared with the use-binding rule.
let resolvesToDisposable (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> isDisposableType value.FullType
        | _ -> false
    | None -> false

let private symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
    |> Option.map (fun u -> u.Symbol)

/// Does the interface type name resolve to IDisposable or an interface
/// that inherits it (fantomas's `FantomasService`)? The name alone
/// suffices when it is IDisposable itself, in case resolution fails.
let private interfaceIsDisposable (check: FSharpCheckFileResults) (source: ISourceText) (t: SynType) =
    let ident =
        match t with
        | SynType.LongIdent(SynLongIdent(id = ids))
        | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty -> Some(List.last ids)
        | _ -> None

    match ident with
    | Some id ->
        id.idText = "IDisposable"
        || (match symbolAt check source id with
            | Some(:? FSharpEntity as entity) -> entityIsDisposable entity
            | _ -> false)
    | None -> false

/// A construction whose Dispose is a no-op because the object owns no
/// unmanaged resource: a MemoryStream over a buffer the caller owns
/// (suave's HPACK and Huffman codecs), a StringReader, a StringWriter
/// (fsharp.formatting's HTML writers). Leaving one undisposed leaks
/// nothing. A MemoryStream over its own buffer is not excluded: `use`
/// there is the idiom and costs nothing.
let ownsNoResource (check: FSharpCheckFileResults) (source: ISourceText) (rhs: SynExpr) =
    let isArray (id: Ident) =
        match symbolAt check source id with
        | Some(:? FSharpMemberOrFunctionOrValue as value) ->
            (try
                let t = OptionModule.stripAbbreviations value.FullType
                t.HasTypeDefinition && t.TypeDefinition.IsArrayType
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false

    let overCallersBuffer (args: SynExpr) =
        match stripParens args with
        | SynExpr.Const(SynConst.Unit, _) -> false
        // a capacity: its own buffer
        | SynExpr.Const(SynConst.Int32 _, _) -> false
        | SynExpr.Ident id -> isArray id
        | SynExpr.Tuple(exprs = _ :: _ :: _) -> true
        | _ -> true

    let typeName, args =
        match rhs with
        | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = args) when not ids.IsEmpty ->
            (List.last ids).idText, Some args
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id; argExpr = args) -> id.idText, Some args
        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = args) when
            not ids.IsEmpty
            ->
            (List.last ids).idText, Some args
        | _ -> "", None

    match typeName, args with
    | ("StringReader" | "StringWriter"), Some _ -> true
    | "MemoryStream", Some args -> overCallersBuffer args
    | _ -> false

/// All names bound by a pattern (primary-constructor parameters).
[<TailCall>]
let rec private patNamesLoop (acc: string list) (pending: SynPat list) =
    match pending with
    | [] -> acc
    | p :: rest ->
        let acc, next =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id)) -> id.idText :: acc, rest
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner)
            | SynPat.Paren(inner, _) -> acc, inner :: rest
            | SynPat.Tuple(elementPats = ps) -> acc, ps @ rest
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> acc, ps @ rest
            | _ -> acc, rest

        patNamesLoop acc next

let private patNames (p: SynPat) : string list = patNamesLoop [] [ p ]

/// Every name an instance `let` binds: the function name of `let f x =
/// ...`, and every binder of a destructuring pattern — `let a, b = ...`
/// (the compiler's GraphChecking `let sigToImpl, implToSig = ...`, whose
/// members read `implToSig`).
let private letBoundNames (p: SynPat) : string list =
    match p with
    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ head ])) -> [ head.idText ]
    | _ -> patBoundNames p

/// The type name a construction expression names: `T(...)`, `T<..>(...)`,
/// `new T(...)`, `M.T(...)`.
let private constructedTypeName (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(funcExpr = SynExpr.Ident id) -> Some id.idText
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when not ids.IsEmpty ->
        Some (List.last ids).idText
    | SynExpr.App(funcExpr = SynExpr.TypeApp(expr = SynExpr.Ident id)) -> Some id.idText
    | SynExpr.New(
        targetType = (SynType.LongIdent(SynLongIdent(id = ids)) | SynType.App(
            typeName = SynType.LongIdent(SynLongIdent(id = ids))))) when not ids.IsEmpty -> Some (List.last ids).idText
    | _ -> None

/// A member body that mirrors a protocol rather than computing: `()`,
/// `Unchecked.defaultof<_>`. Such stubs (fsharp.formatting's fake `fsi`
/// object, FCS's `_DebugKeyStoreNoop`) exist to be instances of a shape.
let private isProtocolStub (body: SynExpr) =
    match stripParens body with
    | UnitConst -> true
    | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when
        not ids.IsEmpty && (List.last ids).idText = "defaultof"
        ->
        true
    | _ -> false

/// Find both kinds of suggestion. Requires typed check results for the
/// disposable gate; the static-member analysis is purely syntactic.
/// `allowApiChanges` widens FR0033 to public members (see the module note).
let find
    (allowApiChanges: bool)
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : DisposableFieldSuggestion list * StaticMemberSuggestion list * UndisposedFieldSuggestion list =
    let index = AstIndex.ofTree parseTree
    let disposables = ResizeArray<DisposableFieldSuggestion>()
    let statics = ResizeArray<StaticMemberSuggestion>()
    let undisposed = ResizeArray<UndisposedFieldSuggestion>()

    // types whose instances are handed off as `obj` somewhere in this
    // file — `box (T())`, `T() :> obj`, or a let-bound instance boxed
    // later: the consumer is reflection (`BindingFlags.Instance`) or
    // dynamic dispatch, and a static member is invisible to it
    let boxedTypes =
        let constructedLocals =
            index.Exprs
            |> Array.collect (fun (_, e) ->
                match e with
                | LetOrUseE lou ->
                    lou.Bindings
                    |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
                        match p, constructedTypeName rhs with
                        | SynPat.Named(ident = SynIdent(ident = id)), Some t -> Some(id.idText, t)
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])
            |> Map.ofArray

        let handedOff (e: SynExpr) =
            match constructedTypeName e with
            | Some t -> Some t
            | None ->
                match stripParens e with
                | SynExpr.Ident id -> Map.tryFind id.idText constructedLocals
                | _ -> None

        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = arg) when fn.idText = "box" ->
                handedOff arg
            | SynExpr.Upcast(expr = inner; targetType = SynType.LongIdent(SynLongIdent(id = ids))) when
                not ids.IsEmpty && (List.last ids).idText = "obj"
                ->
                handedOff inner
            | _ -> None)
        |> Set.ofArray

    // does any expression inside `r` read or assign one of `names`?
    let mentions (names: Set<string>) (r: range) =
        // the walker does not descend into a record copy-and-update's source
        // (`{ state with ... }`), so read it off the Record node itself —
        // by TEXT, because the source can be any expression (FCS's
        // `{ denv g with ... }` applies a constructor parameter)
        let copySource (e: SynExpr) =
            match e with
            | SynExpr.Record(copyInfo = Some(copyExpr, _))
            | SynExpr.AnonRecd(copyInfo = Some(copyExpr, _)) -> Some copyExpr
            | _ -> None

        let textMentions (text: string) =
            names
            |> Set.exists (fun name -> System.Text.RegularExpressions.Regex.IsMatch(text, identifierPattern name))

        not names.IsEmpty
        && index.Exprs
           |> Array.exists (fun (_, e) ->
               match e with
               | SynExpr.Ident id when names.Contains id.idText -> Range.rangeContainsRange r id.idRange
               | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when names.Contains firstId.idText ->
                   Range.rangeContainsRange r firstId.idRange
               | SynExpr.LongIdentSet(SynLongIdent(id = firstId :: _), _, _) when names.Contains firstId.idText ->
                   Range.rangeContainsRange r e.Range
               | _ ->
                   match copySource e with
                   | Some copyExpr when Range.rangeContainsRange r copyExpr.Range ->
                       textMentions (textOfRange source copyExpr.Range)
                   | _ -> false)

    for path, decl in index.Decls do
        match decl with
        | SynModuleDecl.Types(typeDefns = defns) ->
            for typeDefn in defns do
                match typeDefn with
                | SynTypeDefn(
                    typeInfo = SynComponentInfo(longId = typeIds; accessibility = typeAccess)
                    typeRepr = SynTypeDefnRepr.ObjectModel(members = members)) ->
                    let typeName = typeIds |> List.map (fun i -> i.idText) |> String.concat "."
                    let declPath = SyntaxNode.SynModule decl :: path

                    // IDisposable itself, or an interface inheriting it
                    // (fantomas's FantomasService): its Dispose is the
                    // type's Dispose
                    let implementsDisposable =
                        members
                        |> List.exists (fun m ->
                            match m with
                            | SynMemberDefn.Interface(interfaceType = t) -> interfaceIsDisposable check source t
                            | _ -> false)

                    let instanceLetNames =
                        members
                        |> List.collect (fun m ->
                            match m with
                            | SynMemberDefn.LetBindings(isStatic = false; bindings = bindings) ->
                                bindings |> List.collect (fun (SynBinding(headPat = p)) -> letBoundNames p)
                            | _ -> [])
                        |> Set.ofList

                    let ctorParamNames =
                        members
                        |> List.collect (fun m ->
                            match m with
                            | SynMemberDefn.ImplicitCtor(ctorArgs = args) -> patNames args
                            | _ -> [])
                        |> Set.ofList

                    // new-constructed disposable instance fields
                    let newDisposableFields =
                        members
                        |> List.collect (fun m ->
                            match m with
                            | SynMemberDefn.LetBindings(isStatic = false; bindings = bindings) ->
                                bindings
                                |> List.choose (fun binding ->
                                    match binding with
                                    | SynBinding(
                                        headPat = SynPat.Named(ident = SynIdent(ident = var))
                                        expr = (SynExpr.New(expr = ctorArgs) as rhs)) when
                                        resolvesToDisposable check source var
                                        // a StringReader or a MemoryStream over the
                                        // caller's buffer has nothing to release
                                        && not (ownsNoResource check source rhs)
                                        // a disposable built WITH the object itself —
                                        // `new GraphicsDeviceManager(this)` (MonoGame) —
                                        // registers with it: the base or the framework
                                        // owns and disposes it
                                        && not (
                                            let self =
                                                members
                                                |> List.tryPick (fun m ->
                                                    match m with
                                                    | SynMemberDefn.ImplicitCtor(selfIdentifier = Some id) ->
                                                        Some id.idText
                                                    | _ -> None)
                                                |> Option.defaultValue "this"

                                            System.Text.RegularExpressions.Regex.IsMatch(
                                                textOfRange source ctorArgs.Range,
                                                $@"\b{System.Text.RegularExpressions.Regex.Escape self}\b"
                                            )
                                        )
                                        ->
                                        Some(var.idText, binding.RangeOfBindingWithRhs)
                                    | _ -> None)
                            | _ -> [])

                    // the bodies of Dispose members inside `interface ... with`
                    let disposeBodies =
                        members
                        |> List.collect (fun m ->
                            match m with
                            | SynMemberDefn.Interface(members = Some interfaceMembers) ->
                                interfaceMembers
                                |> List.choose (fun im ->
                                    match im with
                                    | SynMemberDefn.Member(
                                        memberDefn = SynBinding(
                                            headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids))
                                            expr = body)) when
                                        not ids.IsEmpty
                                        && (let name = (List.last ids).idText in
                                            name = "Dispose" || name = "DisposeAsync")
                                        ->
                                        // a Dispose that delegates to DisposeAsync
                                        // (FsAutoComplete's progress reporter)
                                        // disposes through the async body
                                        Some body.Range
                                    | _ -> None)
                            | _ -> [])

                    // one hop out of the interface Dispose: a body that calls
                    // `this.Dispose()` (the F# compiler's
                    // NativeDllResolveHandlerCoreClr) or a let-bound
                    // `dispose ()` (its TcImports) disposes through that
                    // member's or function's body
                    let delegatedBodies =
                        let called =
                            index.Exprs
                            |> Array.choose (fun (_, e) ->
                                if disposeBodies |> List.exists (fun r -> Range.rangeContainsRange r e.Range) then
                                    match e with
                                    | SynExpr.Ident id -> Some id.idText
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; m ])) -> Some m.idText
                                    | _ -> None
                                else
                                    None)
                            |> Set.ofArray

                        members
                        |> List.collect (fun m ->
                            match m with
                            | SynMemberDefn.Member(
                                memberDefn = SynBinding(
                                    headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids)); expr = body)) when
                                not ids.IsEmpty && called.Contains (List.last ids).idText
                                ->
                                [ body.Range ]
                            | SynMemberDefn.LetBindings(bindings = bindings) ->
                                bindings
                                |> List.choose (fun (SynBinding(headPat = p; expr = body)) ->
                                    match p with
                                    | SynPat.LongIdent(
                                        longDotId = SynLongIdent(id = [ f ]); argPats = SynArgPats.Pats(_ :: _)) when
                                        called.Contains f.idText
                                        ->
                                        Some body.Range
                                    | _ -> None)
                            | _ -> [])

                    let disposeBodies = disposeBodies @ delegatedBodies

                    // a member that calls `field.Dispose()` itself — a
                    // Close/Unsubscribe/ref-count protocol — is manual
                    // management, not an ownerless resource
                    let manuallyDisposed (fieldName: string) =
                        members
                        |> List.exists (fun m ->
                            match m with
                            | SynMemberDefn.Member(memberDefn = SynBinding(expr = body)) ->
                                (textOfRange source body.Range).Contains($"{fieldName}.Dispose")
                            | _ -> false)

                    // the members' indentation and the last member's end:
                    // where an appended interface implementation goes
                    let memberIndent =
                        members
                        |> List.tryFind (fun m ->
                            match m with
                            | SynMemberDefn.ImplicitCtor _ -> false
                            | _ -> true)
                        |> Option.map (fun m -> String.replicate m.Range.StartColumn " ")
                        |> Option.defaultValue "    "

                    let membersEnd = members |> List.tryLast |> Option.map (fun m -> m.Range.End)

                    if not implementsDisposable then
                        // FR0032: owns a disposable but is not disposable
                        let leaked =
                            newDisposableFields
                            |> List.filter (fun (fieldName, _) -> not (manuallyDisposed fieldName))

                        // the base class, when there is one: (name, Some
                        // disposable?) once resolved, None when it cannot be.
                        // A disposable base makes an added `interface
                        // IDisposable` a duplicate — the note then talks
                        // about the base's Dispose instead (Kasino's MonoGame
                        // Game subclass drew "does not implement IDisposable"
                        // while the base does); an unresolved base is not
                        // worth the guess
                        let bases =
                            members
                            |> List.choose (fun m ->
                                match m with
                                | SynMemberDefn.Inherit(baseType = Some(SynType.LongIdent(SynLongIdent(id = ids))))
                                | SynMemberDefn.ImplicitInherit(inheritType = SynType.LongIdent(SynLongIdent(id = ids))) when
                                    not ids.IsEmpty
                                    ->
                                    let id = List.last ids
                                    let r = id.idRange
                                    let lineText = source.GetLineString(r.EndLine - 1)

                                    let disposable =
                                        match
                                            check.GetSymbolUseAtLocation(
                                                r.EndLine,
                                                r.EndColumn,
                                                lineText,
                                                [ id.idText ]
                                            )
                                        with
                                        | Some symbolUse ->
                                            match symbolUse.Symbol with
                                            | :? FSharpEntity as e -> Some(entityIsDisposable e)
                                            | :? FSharpMemberOrFunctionOrValue as v ->
                                                (try
                                                    if v.IsConstructor then
                                                        v.DeclaringEntity |> Option.map entityIsDisposable
                                                    else
                                                        None
                                                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                                     None)
                                            | _ -> None
                                        | None -> None

                                    Some(id.idText, disposable)
                                | SynMemberDefn.Inherit _
                                | SynMemberDefn.ImplicitInherit _ -> Some("", None)
                                | _ -> None)

                        let disposableBase =
                            bases
                            |> List.tryPick (fun (name, disposable) ->
                                if disposable = Some true then Some name else None)

                        let baseAllowsInterface =
                            bases |> List.forall (fun (_, disposable) -> disposable = Some false)

                        // one fix for the type, carried by its first field:
                        // an IDisposable whose Dispose releases every one
                        let typeFix =
                            match membersEnd with
                            | Some at when not leaked.IsEmpty && baseAllowsInterface ->
                                let disposeLines =
                                    leaked
                                    |> List.map (fun (fieldName, _) -> $"{memberIndent}        {fieldName}.Dispose()")
                                    |> String.concat "\n"

                                let insertion =
                                    $"\n\n{memberIndent}interface System.IDisposable with\n{memberIndent}    member _.Dispose() =\n{disposeLines}"

                                Some(Range.mkRange typeDefn.Range.FileName at at, "", insertion)
                            | _ -> None

                        leaked
                        |> List.iteri (fun i (fieldName, fieldRange) ->
                            disposables.Add
                                { TypeName = typeName
                                  FieldName = fieldName
                                  Range = fieldRange
                                  DisposableBase = disposableBase
                                  Fix = if i = 0 then typeFix else None })
                    else
                        // FR0047 (CA2213): disposable, but the field is
                        // never touched by any Dispose body
                        // does a Dispose body RELEASE the field, rather than
                        // merely touch it? `cts.Cancel()` mentions the field
                        // and frees nothing
                        let releases (fieldName: string) =
                            let releaseNames = set [ "Dispose"; "DisposeAsync"; "Close" ]

                            // the field passed AS AN ARGUMENT leaves this
                            // body's sight — `cleanup cts`, `owned.Add cts`
                            // — and whatever received it may be what
                            // releases it. Being the RECEIVER is different:
                            // `cts.Cancel()` stays here and frees nothing
                            let handedOff (e: SynExpr) =
                                match e with
                                | SynExpr.App(isInfix = false; argExpr = arg) ->
                                    let operands =
                                        match stripParens arg with
                                        | SynExpr.Tuple(exprs = es) -> es
                                        | single -> [ single ]

                                    operands
                                    |> List.exists (fun operand ->
                                        match stripParens operand with
                                        | SynExpr.Ident id -> id.idText = fieldName
                                        | _ -> false)
                                | _ -> false

                            index.Exprs
                            |> Array.exists (fun (_, e) ->
                                disposeBodies |> List.exists (fun b -> Range.rangeContainsRange b e.Range)
                                && (handedOff e
                                    || (match e with
                                        // field.Dispose() / field.Close()
                                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                            (List.head ids).idText = fieldName
                                            && releaseNames.Contains (List.last ids).idText
                                        // (field :> IDisposable).Dispose()
                                        | SynExpr.DotGet(expr = recv; longDotId = SynLongIdent(id = [ m ])) when
                                            releaseNames.Contains m.idText
                                            ->
                                            mentions (Set.singleton fieldName) recv.Range
                                        | _ -> false)))

                        // a Dispose that hands off to its base has a
                        // disposal path this rule cannot follow
                        let delegatesToBase =
                            index.Exprs
                            |> Array.exists (fun (_, e) ->
                                disposeBodies |> List.exists (fun b -> Range.rangeContainsRange b e.Range)
                                && (match e with
                                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                                        (List.head ids).idText = "base" && (List.last ids).idText = "Dispose"
                                    | _ -> false))

                        for fieldName, fieldRange in newDisposableFields do
                            let touched =
                                disposeBodies
                                |> List.exists (fun body -> mentions (Set.singleton fieldName) body)

                            // Rx hands out disposables whose Dispose is an
                            // unsubscribe, and composes them deliberately —
                            // "this field is not disposed here" is the
                            // design there, not the defect
                            let reactive =
                                seq { 0 .. source.GetLineCount() - 1 }
                                |> Seq.exists (fun l ->
                                    let text = (source.GetLineString l).TrimStart()

                                    text.StartsWith "open System.Reactive"
                                    || text.StartsWith "open FSharp.Control.Reactive")

                            let mentionedOnly =
                                touched && not (releases fieldName) && not delegatesToBase && not reactive

                            if not (disposeBodies.IsEmpty || (touched && not mentionedOnly)) then
                                // `field.Dispose()` as the first statement of
                                // the Dispose body — replacing a `()` body,
                                // else a line above what is there, at its
                                // column
                                let fix =
                                    disposeBodies
                                    |> List.tryHead
                                    |> Option.map (fun body ->
                                        let bodyText = textOfRange source body

                                        if bodyText.Trim() = "()" then
                                            body, bodyText, $"{fieldName}.Dispose()"
                                        else
                                            let at = Range.mkRange body.FileName body.Start body.Start
                                            let indent = String.replicate body.StartColumn " "
                                            at, "", $"{fieldName}.Dispose()\n{indent}")

                                undisposed.Add
                                    { TypeName = typeName
                                      FieldName = fieldName
                                      Range = fieldRange
                                      MentionedOnly = mentionedOnly
                                      Fix = fix }

                    // FR0033: instance members touching no instance state —
                    // except where instance-ness is a contract (CE builders,
                    // framework-dispatched subclass members, instances
                    // boxed to obj for reflection)
                    let contract = instanceIsContract members || boxedTypes.Contains typeName

                    for m in (if contract then [] else members) do
                        match m with
                        | SynMemberDefn.Member(
                            memberDefn = SynBinding(
                                valData = SynValData(memberFlags = Some flags)
                                attributes = attrs
                                accessibility = bindingAccess
                                isInline = isInline
                                headPat = SynPat.LongIdent(
                                    longDotId = SynLongIdent(id = [ selfId; nameId ])
                                    argPats = SynArgPats.Pats args
                                    accessibility = patAccess)
                                expr = bodyExpr)) when
                            flags.IsInstance
                            && not flags.IsOverrideOrExplicitImpl
                            && not flags.IsDispatchSlot
                            && not args.IsEmpty
                            // an ATTRIBUTED member is framework-contract
                            // territory: [<Fact>] tests, [<Benchmark>]
                            // methods (BenchmarkDotNet REQUIRES instance),
                            // [<GlobalSetup>], controller actions — the
                            // framework dispatches reflectively and
                            // instance-ness is part of its protocol
                            && attrs.IsEmpty
                            // an inline member is a compile-time template
                            // (FCS's no-op key-store mirror); a stub body
                            // mirrors a protocol
                            && not isInline
                            && not (isProtocolStub bodyExpr)
                            // callers spell `x.M()` today: static is an API
                            // change on a public member
                            && Visibility.isInScope allowApiChanges declPath [ typeAccess; bindingAccess; patAccess ]
                            ->
                            let memberParamNames = args |> List.collect patNames |> Set.ofList

                            let instanceNames =
                                instanceLetNames + ctorParamNames
                                |> Set.add selfId.idText
                                |> Set.add "base"
                                |> fun names -> names - memberParamNames

                            if not (mentions instanceNames bodyExpr.Range) then
                                statics.Add
                                    { MemberName = nameId.idText
                                      Range = m.Range }
                        | _ -> ()
                | _ -> ()
        | _ -> ()

    List.ofSeq disposables, List.ofSeq statics, List.ofSeq undisposed

/// FR0148 (CA1063, note): a public `Dispose()` on a type that does not
/// implement IDisposable — nothing can `use` it, and only callers that
/// know the member by name release the resource.
type DisposeWithoutInterfaceSuggestion =
    {
        TypeName: string
        /// The Dispose member's range.
        Range: range
    }

/// Find public `member _.Dispose()` members on types that implement no
/// IDisposable — neither directly, nor through an interface inheriting
/// it, nor through a base type (typed: the entity's own interface list).
/// fsharp.formatting's FsiSession wraps an FCS evaluation session, a real
/// IDisposable, behind such a member: `use` cannot bind it, and FR0032
/// looked at the wrong field.
let disposeWithoutInterface
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : DisposeWithoutInterfaceSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let typeIsDisposable (typeId: Ident) =
            match symbolAt check source typeId with
            | Some(:? FSharpEntity as entity) -> entityIsDisposable entity
            | _ -> false

        [ for _, decl in index.Decls do
              match decl with
              | SynModuleDecl.Types(typeDefns = defns) ->
                  for SynTypeDefn(typeInfo = SynComponentInfo(longId = typeIds); typeRepr = repr; members = extra) in
                      defns do
                      let members =
                          match repr with
                          | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                          | _ -> extra

                      let publicDispose =
                          members
                          |> List.tryPick (fun m ->
                              match m with
                              | SynMemberDefn.Member(
                                  memberDefn = SynBinding(
                                      valData = SynValData(memberFlags = Some flags)
                                      accessibility = bindingAccess
                                      headPat = SynPat.LongIdent(
                                          longDotId = SynLongIdent(id = [ _; nameId ])
                                          argPats = SynArgPats.Pats [ arg ]
                                          accessibility = patAccess))) when
                                  nameId.idText = "Dispose"
                                  && flags.IsInstance
                                  && not flags.IsOverrideOrExplicitImpl
                                  && (let rec unparen (p: SynPat) =
                                          match p with
                                          | SynPat.Paren(pat = inner) -> unparen inner
                                          | p -> p

                                      match unparen arg with
                                      | SynPat.Const(SynConst.Unit, _) -> true
                                      | _ -> false)
                                  && (match bindingAccess, patAccess with
                                      | Some(SynAccess.Private _), _
                                      | _, Some(SynAccess.Private _) -> false
                                      | _ -> true)
                                  ->
                                  Some m.Range
                              | _ -> None)

                      match publicDispose, List.tryLast typeIds with
                      | Some memberRange, Some typeId when not (typeIsDisposable typeId) ->
                          { TypeName = typeIds |> List.map (fun i -> i.idText) |> String.concat "."
                            Range = memberRange }
                      | _ -> ()
              | _ -> () ]
