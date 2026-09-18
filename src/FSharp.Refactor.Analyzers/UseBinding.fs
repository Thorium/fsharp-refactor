/// Refactoring (correctness): a locally constructed disposable bound with
/// `let` has no owner — nothing ever disposes it.
///
///     let stream = new FileStream(path, FileMode.Open)     // leaked
///     use stream = new FileStream(path, FileMode.Open)     // disposed at
///                                                          // scope exit
///
/// The sibling of FR0032 (disposable FIELDS without IDisposable), for
/// expression-level bindings.
///
/// Three tiers, decided by where the bare mentions of the binder send it:
///   - FIX (`let` → `use`) when the value provably stays inside the scope:
///     every mention is an INVOKED member (`x.Read ...`) or a comparison
///     operand, never inside a lambda (which may outlive the scope), no
///     result position mentions it (a plain-valued call excepted), no
///     local bound to a value reached through it (`let cmd =
///     conn.CreateCommand()`) escapes either, the object does no work of
///     its own after the scope (a timer, a watcher, an event it raises),
///     and an enclosing computation expression's builder has a `Using`
///   - NOTHING when an escape is an ownership transfer: the value is the
///     scope's result (the caller owns it — the factory pattern; also
///     inside a tuple, a record, an upcast or a union case), an argument
///     to the constructor of another disposable, which disposes it in turn
///     (HttpClient its handler, StreamReader its stream), or stored where
///     a holder beyond the scope keeps it (a field or property, a
///     collection, a module-level value — FR0032/FR0047 judge that
///     holder). A `use` here would dispose it under the new owner
///   - NOTE ONLY when a mention could move the value somewhere whose
///     ownership is unknown — passed to an ordinary function, stored in a
///     local, captured by a lambda, read by a result that may outlive the
///     scope: the leak is worth pointing out, the rewrite is the author's
///     call, and the note says where the value went
///
/// Skips entirely when the scope already calls `x.Dispose()`, `x.Close()`
/// on a stream, writer or socket, or `(x :> IDisposable).Dispose()` — that
/// is manual management, not a leak. Skips disposables that own no
/// resource: a MemoryStream over the caller's buffer, a StringReader, a
/// StringWriter.
module FSharp.Refactor.UseBinding

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// A scope whose leaks weigh differently from an ordinary function's.
[<RequireQualifiedAccess>]
type ScopeContext =
    /// `[<EntryPoint>]`: nothing accumulates, but nothing flushes either —
    /// .NET runs no finalizers at process exit, so a writer's last buffer
    /// or a transaction's last work is lost. Only reported for such types.
    | EntryPoint
    /// an ASP.NET action or SignalR hub method: the scope runs once per
    /// request, so the leak repeats until the pool behind it runs dry
    | RequestHandler

/// Where an advisory's value goes.
[<RequireQualifiedAccess>]
type Destination =
    /// passed to a function by name; `inspected` when it is a function in
    /// this file whose body was read and does not dispose the parameter
    | Function of name: string * inspected: bool
    /// assigned to a mutable local or a local ref cell of the scope
    | StoredLocally of name: string
    /// captured by a lambda, a local function or an object expression that
    /// may run after the scope has exited
    | Captured
    /// the scope's result reads a member of it, so the value may still be
    /// needed after the scope exits (a task, a sequence, an object tied
    /// to it)
    | ReadInResult
    /// the object does work of its own after the scope returns — a timer,
    /// a watcher, a listener, an event it raises that the scope subscribed
    /// to, a callback it was constructed with — which `use` would stop
    | SelfActive
    /// a Task- or Async-returning member of it was called and the result
    /// dropped (`|> ignore`, a bare statement, `Async.Start`): that work
    /// may still be running when the scope exits, on a receiver `use`
    /// would have disposed
    | InFlight of memberName: string
    /// a CancellationTokenSource whose token (or the source itself) is
    /// handed as an argument to a call this rule cannot see finish — a
    /// user function, or a BCL/FSharp.Core operation whose result is not
    /// awaited in the scope — so work cancelled through it may outlive the
    /// scope, where disposing the source would abort it
    | TokenHanded of callee: string
    /// the binding sits in a computation expression whose builder defines
    /// no `Using`, so `use` cannot bind it there (FS0708)
    | NoBuilderUsing
    /// something this rule cannot read
    | Unknown

type Suggestion =
    {
        /// The `let` keyword's range (the fix rewrites it to `use`).
        Range: range
        Name: string
        /// None = advisory only (the value may escape the scope).
        Fix: (string * string) option
        /// Where an advisory's value goes; None for a fix.
        Destination: Destination option
        /// The kind of scope the binding sits in, when it is one whose
        /// leaks weigh differently: the program's entry point, a request
        /// handler.
        Context: ScopeContext option
    }

/// The advisory's account of where the value went, for the message: it
/// must say what actually happened (a value stored in a field used to be
/// reported as "handed to 'ValueSome'").
let describeEscape (s: Suggestion) =
    match s.Destination with
    | Some(Destination.Function(name, true)) -> $"it is handed to '%s{name}' in this file, which does not dispose it"
    | Some(Destination.Function(name, false)) -> $"it is handed to '%s{name}', which may or may not take ownership"
    | Some(Destination.StoredLocally name) ->
        $"it is stored in the local '%s{name}', whose later use this rule cannot follow"
    | Some Destination.Captured ->
        "a closure (a lambda, local function or object expression) captures it and may run after the scope has exited"
    | Some Destination.ReadInResult ->
        "the scope's result reads it, so it may still be needed after the scope exits (a task, a sequence, an object tied to it)"
    | Some Destination.SelfActive ->
        "it does work of its own after the scope returns (a timer, a watcher, a listener, an event it raises, a callback it was built with), which 'use' would stop"
    | Some(Destination.InFlight m) ->
        $"the result of its '%s{m}' call is dropped or handed on rather than awaited, so that work may still be running when the scope exits, and 'use' would dispose it underneath"
    | Some(Destination.TokenHanded callee) ->
        $"its token is handed to '%s{callee}', which may start work that outlives this scope (a background Async.Start, a stored task), and disposing the source under it would cancel or fault that work"
    | Some Destination.NoBuilderUsing ->
        "it sits in a computation expression whose builder defines no 'Using', so 'use' cannot bind it there"
    | Some Destination.Unknown
    | None -> "it also escapes this scope (passed, stored, or captured)"

/// BCL factories whose result the caller owns, by enclosing type.
let private bclFactories =
    [
        "System.IO.File",
        set
            [
                "Open"
                "OpenRead"
                "OpenWrite"
                "OpenText"
                "Create"
                "CreateText"
                "AppendText"
            ]
        "System.Xml.XmlReader", set [ "Create" ]
        "System.Xml.XmlWriter", set [ "Create" ]
        // the hash and cipher factories: `MD5.Create()` is THE way to get
        // one (the F# compiler's Hashing.fs, suave's WebSocket handshake)
        "System.Security.Cryptography.MD5", set [ "Create" ]
        "System.Security.Cryptography.SHA1", set [ "Create" ]
        "System.Security.Cryptography.SHA256", set [ "Create" ]
        "System.Security.Cryptography.SHA384", set [ "Create" ]
        "System.Security.Cryptography.SHA512", set [ "Create" ]
        "System.Security.Cryptography.HashAlgorithm", set [ "Create" ]
        "System.Security.Cryptography.Aes", set [ "Create" ]
        "System.Security.Cryptography.RandomNumberGenerator", set [ "Create" ]
    ]

/// The construction under the wrappers that leave it what it is: parens,
/// a type annotation, an upcast (`new StringWriter(sb) :> TextWriter`).
[<TailCall>]
let rec private unwrapped (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner)
    | SynExpr.Upcast(expr = inner)
    | SynExpr.InferredUpcast(expr = inner) -> unwrapped inner
    | _ -> e

/// The identifier an application's function position names, if it is a
/// plain (possibly dotted, possibly type-applied) name.
let private headIdent (f: SynExpr) =
    match f with
    | SynExpr.Ident id -> ValueSome id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.TypeApp(expr = SynExpr.Ident id) -> ValueSome id
    | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) when not ids.IsEmpty ->
        ValueSome(List.last ids)
    | _ -> ValueNone

let private symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ])
    |> Option.map (fun u -> u.Symbol)

/// Is the bound expression a construction the binder OWNS — `new T(...)`,
/// a constructor applied without `new` (`MemoryStream()`), or an
/// ownership-transferring BCL factory (`File.OpenRead path` is THE way to
/// open a file, and it leaks exactly like a bare constructor)?
let private locallyConstructed (check: FSharpCheckFileResults) (source: ISourceText) (rhs: SynExpr) =
    match rhs with
    | SynExpr.New _ -> true
    | SynExpr.App(isInfix = false; funcExpr = f) ->
        let headIdent = headIdent f

        // cheap prefilter before paying for symbol resolution: a
        // constructor-without-new is spelled with a type name and the BCL
        // factories are PascalCase, while ordinary calls (`let x = load y`)
        // are lowercase — resolving those for every let in a sweep put
        // this rule near the top of the slow-analyzer list
        let plausible =
            match headIdent with
            | ValueSome id -> id.idText.Length > 0 && System.Char.IsUpper id.idText.[0]
            | ValueNone -> false

        match (if plausible then headIdent else ValueNone) with
        | ValueSome id ->
            match symbolAt check source id with
            | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                (try
                    value.IsConstructor
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
                || (let enclosing = OptionModule.enclosingFullName value

                    bclFactories
                    |> List.exists (fun (entity, names) -> enclosing = entity && names.Contains id.idText))
            | _ -> false
        | ValueNone -> false
    | _ -> false

/// Is the type one of `bases` or derived from one, or does it implement
/// one of `interfaces`?
let private typeMatches (bases: Set<string>) (interfaces: Set<string>) (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        let rec baseChain (t: FSharpType) =
            if t.HasTypeDefinition then
                let entity = t.TypeDefinition

                (entity.TryFullName |> Option.exists bases.Contains)
                || (entity.BaseType |> Option.exists baseChain)
            else
                false

        baseChain t
        || (not interfaces.IsEmpty
            && t.HasTypeDefinition
            && t.TypeDefinition.AllInterfaces
               |> Seq.exists (fun i ->
                   i.HasTypeDefinition
                   && (i.TypeDefinition.TryFullName |> Option.exists interfaces.Contains)))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The type a symbol reads as: a value's own type, a member's or
/// property's return type, a field's type.
let private symbolType (symbol: FSharpSymbol) =
    try
        match symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            if value.IsProperty || value.IsMember then
                Some value.ReturnParameter.Type
            else
                Some value.FullType
        | :? FSharpField as field -> Some field.FieldType
        | _ -> None
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        None

/// Types a wrapper's constructor takes ownership of: its Dispose closes
/// the stream, reader, writer or handler too (leaveOpen and disposeHandler
/// default to owning).
let private adoptedResourceBases =
    set
        [
            "System.IO.Stream"
            "System.IO.TextReader"
            "System.IO.TextWriter"
            "System.Net.Http.HttpMessageHandler"
        ]

/// A wrapper built over a resource the scope did not create: its Dispose
/// closes that resource too (leaveOpen is false by default, HttpClient
/// disposes its handler). The F# compiler's ilnativeres.fs wraps a
/// caller-owned `resStream` in a BinaryWriter in a function that appends
/// to it — a `use` there closed the stream under the caller; a
/// `LineSource(stream: Stream)` wrapping its constructor parameter in a
/// StreamReader per call closed the shared stream after the first line.
/// Only a value the SAME scope constructed AND keeps (`ownedHere`) is the
/// scope's own: a parameter, a constructor parameter, a class `let` field,
/// a module-level value, an outer binding or a property read is foreign —
/// and so is a local that escapes the scope (Giraffe's tests build a
/// MemoryStream, wrap it in a StreamWriter, store it in
/// `ctx.Request.Body` and return a `task { }` that reads it: a `use` on
/// the writer closed the request body before the task ran). Such a
/// wrapper is not this scope's to dispose.
let private wrapsForeignResource
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (ownedHere: string -> bool)
    (rhs: SynExpr)
    =
    let arguments (args: SynExpr) =
        match stripParens args with
        | SynExpr.Tuple(exprs = elements) -> elements
        | SynExpr.Const(SynConst.Unit, _) -> []
        | single -> [ single ]

    // a stream, reader, writer or handler — not a path the wrapper opens
    // itself, nor a flag; unresolved, the name's suffix decides
    let resourceLike (id: Ident) =
        match symbolAt check source id |> Option.bind symbolType with
        | Some t -> typeMatches adoptedResourceBases Set.empty t
        | None ->
            let name = id.idText

            name.EndsWith "Stream"
            || name.EndsWith "Reader"
            || name.EndsWith "Writer"
            || name.EndsWith "Handler"

    let foreign (arg: SynExpr) =
        match unwrapped arg with
        | SynExpr.Ident id -> resourceLike id && not (ownedHere id.idText)
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> resourceLike (List.last ids)
        | _ -> false

    match rhs with
    | SynExpr.New(expr = args)
    | SynExpr.App(isInfix = false; argExpr = args) -> arguments args |> List.exists foreign
    | _ -> false

/// Does the identifier name a constructor of a disposable type — or, as
/// the type name of a `new T(...)`, a disposable type T?
let private constructsDisposable (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    match symbolAt check source id with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            value.IsConstructor
            && value.DeclaringEntity |> Option.exists ObjectDesign.entityIsDisposable
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | Some(:? FSharpEntity as entity) -> ObjectDesign.entityIsDisposable entity
    | _ -> false

let private typeIdent (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// Where a bare mention of the binder sends the value.
type private Escape =
    /// the scope's result: the caller owns it
    | Returned
    /// an argument to the constructor of another disposable, which
    /// disposes it in turn
    | Adopted
    /// stored where a holder beyond this scope keeps it — a field or
    /// property, a collection, a module-level value: the holder's type is
    /// where FR0032/FR0047 look for the Dispose, this scope is not the
    /// owner
    | Held
    /// an operand of a comparison: it goes nowhere
    | Kept
    /// passed to a function, stored, captured — owner unknown; the name
    /// of the destination when one can be read off the syntax
    | Handed of string option
    /// passed to a same-file function by bare name: the argument position
    /// (curried index, tuple element) lets the callee's body be read
    | HandedAt of callee: string * argument: int * element: int option
    /// assigned to a mutable local or a local ref cell of this scope
    | StoredLocally of string
    /// captured by a closure that may run after the scope
    | Captured
    /// a local bound to a value reached through the binder (a task, a
    /// command, a reader) is the scope's result: the caller still needs
    /// the binder behind it
    | ResultReads

/// Collection members that keep their argument.
let private collectionInserts = set [ "Add"; "TryAdd"; "Enqueue"; "Push"; "Insert" ]

/// Does the application head name a union case (`Some x`, `ValueSome x`,
/// `Ok x`)? The case wraps the value without taking it.
let private isUnionCase check source (f: SynExpr) =
    match headIdent f with
    | ValueSome id ->
        match symbolAt check source id with
        | Some(:? FSharpUnionCase) -> true
        | _ -> false
    | ValueNone -> false

let private nameOf (e: SynExpr) =
    match headIdent e with
    | ValueSome id -> Some id.idText
    | ValueNone -> None

/// The compiled name of an infix operator's function position
/// (`op_PipeRight` for `|>`), empty for anything else.
let private operatorName (op: SynExpr) =
    match headIdent op with
    | ValueSome id -> id.idText
    | ValueNone -> ""

/// The head of a curried application chain `f a b` = App(App(f, a), b):
/// the identifier, whether it was spelled bare (a single segment, so a
/// same-file binding of that name is the callee), and how many arguments
/// the chain has already applied.
[<TailCall>]
let rec private chainHead (f: SynExpr) (applied: int) =
    match f with
    | SynExpr.App(isInfix = false; funcExpr = g) -> chainHead g (applied + 1)
    | SynExpr.Ident id -> ValueSome id, true, applied
    | _ -> headIdent f, false, applied

let private handed (f: SynExpr) (element: int option) check source =
    match chainHead f 0 with
    | ValueSome id, _, _ when constructsDisposable check source id -> Adopted
    | ValueSome id, true, applied -> HandedAt(id.idText, applied, element)
    | ValueSome id, false, _ -> Handed(Some id.idText)
    | ValueNone, _, _ -> Handed None

/// Walk outward from a mention through the nodes that merely wrap an
/// argument (parens, tuples, annotations, upcasts, union cases,
/// named-argument `=`) to the construction, call or store that receives
/// it. `element` remembers which tuple element the mention sat in, for
/// reading the callee. `holds` tells whether a bare name assigned to keeps
/// values beyond the scope (a field of the enclosing type, a module-level
/// value) or is a local of it.
[<TailCall>]
let rec private classifyLoop
    check
    source
    (holds: string -> bool)
    (mention: range)
    (viaEquality: bool)
    (element: int option)
    (path: SyntaxNode list)
    =
    // `x <- v`, `x := v`: the type's field or the module's value holds it
    // from now on; a local of the scope is a place this rule cannot follow
    let storedIn (target: Ident) =
        if holds target.idText then
            Held
        else
            StoredLocally target.idText

    match path with
    | SyntaxNode.SynExpr(SynExpr.Tuple(exprs = elements)) :: rest ->
        let at =
            elements
            |> List.tryFindIndex (fun e -> Range.rangeContainsRange e.Range mention)

        classifyLoop check source holds mention viaEquality (if element.IsSome then element else at) rest
    | SyntaxNode.SynExpr(SynExpr.Paren _ | SynExpr.Typed _ | SynExpr.Upcast _ | SynExpr.InferredUpcast _) :: rest ->
        classifyLoop check source holds mention viaEquality element rest
    // `Some x`, `ValueSome x`: the case wraps the value, the next node
    // receives it (Mibo's `billboardEffect <- ValueSome e` was reported as
    // handed to 'ValueSome')
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a)) :: rest when
        Range.rangeContainsRange a.Range mention && isUnionCase check source f
        ->
        classifyLoop check source holds mention viaEquality element rest
    // `x |> f`: the infix node, then the outer application whose argument
    // is the callee (operators parse as LongIdents carrying their notation)
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op)) :: SyntaxNode.SynExpr(SynExpr.App(argExpr = callee)) :: _ when
        operatorName op = "op_PipeRight"
        ->
        handed callee element check source
    // the operator's own node of an infix application: keep climbing
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = true)) :: rest ->
        classifyLoop check source holds mention viaEquality element rest
    // `cell := x` (suave's RateLimit keeps its cleanup timer in a
    // module-level ref)
    | SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = op; argExpr = cell); argExpr = a)) :: _ when
        operatorName op = "op_ColonEquals" && Range.rangeContainsRange a.Range mention
        ->
        match stripParens cell with
        | SynExpr.Ident target -> storedIn target
        | _ -> Held
    // `Prop = x` is a named argument inside a construction and a plain
    // comparison anywhere else — the next node tells which
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = op))) :: rest when
        (let name = operatorName op in name = "op_Equality" || name = "op_Inequality")
        ->
        classifyLoop check source holds mention true element rest
    | SyntaxNode.SynExpr(SynExpr.New(targetType = t)) :: _ ->
        match typeIdent t with
        | ValueSome id when constructsDisposable check source id -> Adopted
        | ValueSome id -> Handed(Some id.idText)
        | ValueNone -> Handed None
    // `x <- v`: a field, a module value, or a local
    | SyntaxNode.SynExpr(SynExpr.LongIdentSet(longDotId = SynLongIdent(id = [ target ]))) :: _ -> storedIn target
    | SyntaxNode.SynExpr(SynExpr.Set(targetExpr = SynExpr.Ident target; rhsExpr = v)) :: _ when
        Range.rangeContainsRange v.Range mention
        ->
        storedIn target
    // `owner.Prop <- x`: a disposable owner disposes what it holds; any
    // other holder is where the Dispose belongs (Mibo's `res.Raster <- sr`)
    | SyntaxNode.SynExpr(SynExpr.LongIdentSet(longDotId = SynLongIdent(id = owner :: _ :: _))) :: _
    | SyntaxNode.SynExpr(SynExpr.Set(targetExpr = SynExpr.DotGet(expr = SynExpr.Ident owner))) :: _ ->
        if ObjectDesign.resolvesToDisposable check source owner then
            Adopted
        else
            Held
    // `xs.[i] <- x`, `o.Prop.[i] <- x`: the collection holds it (suave's
    // Tcp.fs fills its listen-socket array)
    | SyntaxNode.SynExpr(SynExpr.Set _ | SynExpr.DotIndexedSet _ | SynExpr.NamedIndexedPropertySet _ | SynExpr.DotNamedIndexedPropertySet _) :: _ ->
        Held
    // `owner.Add(x)`: a disposable collection owns its parts; any other
    // collection holds it for whoever holds the collection
    | SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.DotGet(expr = SynExpr.Ident owner; longDotId = SynLongIdent(id = path))
        argExpr = a)) :: _
    | SyntaxNode.SynExpr(SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = owner :: (_ :: _ as path)))
        argExpr = a)) :: _ when
        collectionInserts.Contains (List.last path).idText
        && Range.rangeContainsRange a.Range mention
        ->
        if ObjectDesign.resolvesToDisposable check source owner then
            Adopted
        else
            Held
    | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a)) :: _ when
        Range.rangeContainsRange a.Range mention
        ->
        handed f element check source
    | SyntaxNode.SynExpr(SynExpr.Lambda _) :: _ -> Captured
    | _ when viaEquality -> Kept
    | _ -> Handed None

/// The names the callee's parameter at (curried index, tuple element)
/// binds — `s` for `let save (s: Stream) =`, for `(name, s)` element 1.
let private parameterNames (pats: SynPat list) (argument: int) (element: int option) =
    let rec strip (p: SynPat) =
        match p with
        | SynPat.Paren(inner, _)
        | SynPat.Typed(pat = inner) -> strip inner
        | _ -> p

    match List.tryItem argument pats |> Option.map strip, element with
    | Some(SynPat.Tuple(elementPats = elements)), Some k ->
        List.tryItem k elements |> Option.map patNames |> Option.defaultValue []
    // a tuple handed to a non-tuple parameter: which element is which is
    // not readable here
    | Some _, Some _ -> []
    | Some p, None -> patNames p
    | None, _ -> []

/// ASP.NET action attributes, and the base types whose members run per
/// request or per message.
let private handlerAttributes =
    set
        [
            "HttpGet"
            "HttpPost"
            "HttpPut"
            "HttpDelete"
            "HttpPatch"
            "HttpHead"
            "HttpOptions"
            "Route"
        ]

let private handlerBases =
    set [ "Controller"; "ControllerBase"; "ApiController"; "Hub" ]

let private lastIdentOf (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids))
    | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
        Some (List.last ids).idText
    | _ -> None

/// The scope kind a binding at `at` sits in: read off the binding's own
/// attributes (`[<EntryPoint>]`, `[<HttpGet>]`) or the base type of the
/// type declaring it (a controller, a hub).
let private bindingContext (path: SyntaxNode list) (at: range) =
    let fromAttributes =
        path
        |> List.tryPick (fun node ->
            match node with
            | SyntaxNode.SynBinding(SynBinding(attributes = attributeLists)) ->
                attributeLists
                |> List.collect (fun l -> l.Attributes)
                |> List.tryPick (fun (a: SynAttribute) ->
                    match a.TypeName with
                    | SynLongIdent(id = ids) when not ids.IsEmpty ->
                        match (List.last ids).idText.Replace("Attribute", "") with
                        | "EntryPoint" -> Some ScopeContext.EntryPoint
                        | name when handlerAttributes.Contains name -> Some ScopeContext.RequestHandler
                        | _ -> None
                    | _ -> None)
            | _ -> None)

    let fromEnclosingType () =
        path
        |> List.tryPick (fun node ->
            match node with
            | SyntaxNode.SynModule(SynModuleDecl.Types(typeDefns = defns)) ->
                defns
                |> List.tryFind (fun (SynTypeDefn(range = r)) -> Range.rangeContainsRange r at)
                |> Option.bind (fun (SynTypeDefn(typeRepr = repr; members = extra)) ->
                    let members =
                        match repr with
                        | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                        | _ -> extra

                    members
                    |> List.tryPick (fun m ->
                        match m with
                        | SynMemberDefn.Inherit(baseType = Some t)
                        | SynMemberDefn.ImplicitInherit(inheritType = t) ->
                            lastIdentOf t
                            |> Option.filter handlerBases.Contains
                            |> Option.map (fun _ -> ScopeContext.RequestHandler)
                        | _ -> None))
            | _ -> None)

    match fromAttributes with
    | Some c -> Some c
    | None -> fromEnclosingType ()

/// Types whose undisposed instance loses work at process exit rather than
/// merely holding a handle the OS reclaims: buffered writers and streams,
/// and transactions.
let private flushSensitiveBases =
    set
        [
            "System.IO.Stream"
            "System.IO.TextWriter"
            "System.IO.BinaryWriter"
            "System.Data.Common.DbTransaction"
        ]

/// Is the binder's type one of `bases` or derived from one, or does it
/// implement one of `interfaces`?
let private typeIsA
    (bases: Set<string>)
    (interfaces: Set<string>)
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (binder: Ident)
    =
    match symbolAt check source binder with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            typeMatches bases interfaces value.FullType
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// Types that do work of their own after the scope returns — on a thread
/// pool callback, an OS notification, an accepted connection — so a `use`
/// stops them at scope exit: the timer never ticks, the watcher never
/// raises, the listener closes. Such an object is owned by whoever stops
/// it, never by the scope that started it.
let private selfActiveBases =
    set
        [
            "System.Timers.Timer"
            "System.Threading.Timer"
            "System.Threading.PeriodicTimer"
            "System.IO.FileSystemWatcher"
            "System.Diagnostics.Process"
            "System.Net.Sockets.TcpListener"
            "System.Net.Sockets.Socket"
            "System.Net.HttpListener"
        ]

let private selfActiveType check source binder =
    typeIsA selfActiveBases Set.empty check source binder

let private flushSensitive check source binder =
    typeIsA flushSensitiveBases (set [ "System.Data.IDbTransaction" ]) check source binder

/// Types whose `Close()` IS `Dispose()` (the F# compiler's ilwrite.fs
/// closes the MemoryStreams it writes into).
let private closeDisposesBases =
    set
        [
            "System.IO.Stream"
            "System.IO.TextWriter"
            "System.IO.TextReader"
            "System.IO.BinaryWriter"
            "System.IO.BinaryReader"
            "System.Net.Sockets.Socket"
            "System.Net.Sockets.TcpClient"
            "System.Net.Sockets.UdpClient"
            "System.Threading.WaitHandle"
        ]

let private closeDisposes check source binder =
    typeIsA closeDisposesBases Set.empty check source binder

/// Types a member can return while leaving nothing tied to the receiver:
/// primitives, strings, and arrays or tuples of those. `use x = ...; x.M ()`
/// evaluates such a result before disposing x, where a Task, a seq or a
/// Stream from x would still need it afterwards.
let private plainValueTypes =
    set
        [
            "System.String"
            "System.Boolean"
            "System.Char"
            "System.Byte"
            "System.SByte"
            "System.Int16"
            "System.UInt16"
            "System.Int32"
            "System.UInt32"
            "System.Int64"
            "System.UInt64"
            "System.Single"
            "System.Double"
            "System.Decimal"
            "System.Guid"
            "System.DateTime"
            "System.DateTimeOffset"
            "System.TimeSpan"
            "Microsoft.FSharp.Core.Unit"
            "Microsoft.FSharp.Core.unit"
        ]

/// Immutable containers that are fully evaluated when built: plain when
/// their contents are (a `string option`, an `int list`). A seq is not —
/// it runs when enumerated.
let private plainContainerTypes =
    set
        [
            "Microsoft.FSharp.Core.FSharpOption`1"
            "Microsoft.FSharp.Core.FSharpValueOption`1"
            "Microsoft.FSharp.Core.FSharpResult`2"
            "Microsoft.FSharp.Collections.FSharpList`1"
            "System.Nullable`1"
        ]

let rec private isPlainValue (t: FSharpType) =
    let t = OptionModule.stripAbbreviations t

    if t.IsTupleType || t.IsStructTupleType then
        t.GenericArguments |> Seq.forall isPlainValue
    elif t.HasTypeDefinition then
        let entity = t.TypeDefinition

        (entity.TryFullName |> Option.exists plainValueTypes.Contains)
        || entity.IsEnum
        || ((entity.IsArrayType
             || (entity.TryFullName |> Option.exists plainContainerTypes.Contains))
            && t.GenericArguments |> Seq.forall isPlainValue)
    else
        false

/// Does the member the identifier names return a plain value?
let private plainValued (check: FSharpCheckFileResults) (source: ISourceText) (memberId: Ident) =
    match symbolAt check source memberId with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            isPlainValue value.ReturnParameter.Type
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// Does the local the identifier names hold a plain value? A local bound
/// to anything else reached through a disposable (a task, a command, a
/// reader, a method group) is an alias of it. Unresolved counts as not
/// plain.
let private plainValuedLocal (check: FSharpCheckFileResults) (source: ISourceText) (local: Ident) =
    match symbolAt check source local with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            isPlainValue value.FullType
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// Is the member the identifier names a METHOD — one that, mentioned
/// without being applied, is a method group handed on as a function
/// (`Seq.map c.Convert xs`, `changed.Add c.Refresh`) rather than a value
/// read? A property, an event, a field or a value is read where it
/// stands; unresolved counts as a method.
let private isMethod (check: FSharpCheckFileResults) (source: ISourceText) (memberId: Ident) =
    match symbolAt check source memberId with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            value.IsMember
            && not (
                value.IsProperty
                || value.IsPropertyGetterMethod
                || value.IsPropertySetterMethod
                || value.IsEvent
            )
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             true)
    | Some _ -> false
    | None -> true

let private isEvent (check: FSharpCheckFileResults) (source: ISourceText) (memberId: Ident) =
    match symbolAt check source memberId with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            value.IsEvent
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | _ -> false

/// Is the mention at `mention` the function position of an application
/// (`x.Read buf`, `x.Read(buf, 0, n)`, `x.Get<int>()`)? Anything else —
/// an argument, a pipe operand, a bare value — is a method group when the
/// member is a method.
let private invokedAt (path: SyntaxNode list) (mention: range) =
    let rec applied (path: SyntaxNode list) (inner: range) =
        match path with
        | SyntaxNode.SynExpr(SynExpr.TypeApp(range = r)) :: rest -> applied rest r
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f)) :: _ -> Range.rangeContainsRange f.Range inner
        | _ -> false

    applied path mention

/// Members whose `unit` call starts self-driven work: `Start()`,
/// `BeginAccept`-style, `EnableRaisingEvents`.
let private startsWork (check: FSharpCheckFileResults) (source: ISourceText) (memberId: Ident) =
    let name = memberId.idText

    (name = "Start" || name.StartsWith "Begin" || name.StartsWith "Enable")
    && (match symbolAt check source memberId with
        | Some(:? FSharpMemberOrFunctionOrValue as value) ->
            (try
                let t = OptionModule.stripAbbreviations value.ReturnParameter.Type

                t.HasTypeDefinition
                && (t.TypeDefinition.TryFullName
                    |> Option.exists (fun n -> n = "Microsoft.FSharp.Core.Unit" || n = "Microsoft.FSharp.Core.unit"))
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 true)
        | _ -> true)

/// Builders whose `Using` the compiler knows without a symbol: the F#
/// core computations and `seq`, which is a language form.
let private usingBuilders = set [ "async"; "task"; "backgroundTask"; "seq" ]

/// Does the builder expression of a `builder { ... }` support `use`: one
/// of the known builders, or a value (a constructor, a property) whose
/// type defines a `Using` member, on itself or a base? `query { }` and a
/// hand-written `maybe { }` without one make `use` an FS0708.
let private builderDefinesUsing (check: FSharpCheckFileResults) (source: ISourceText) (builder: SynExpr) =
    let rec definesUsing (entity: FSharpEntity) =
        entity.MembersFunctionsAndValues
        |> Seq.exists (fun m -> m.DisplayName = "Using")
        || (entity.BaseType
            |> Option.exists (fun b -> b.HasTypeDefinition && definesUsing b.TypeDefinition))

    match headIdent builder with
    | ValueSome id when usingBuilders.Contains id.idText -> true
    | ValueSome id ->
        match symbolAt check source id with
        | Some(:? FSharpMemberOrFunctionOrValue as value) ->
            (try
                let entity =
                    if value.IsConstructor then
                        value.DeclaringEntity
                    else
                        symbolType value
                        |> Option.map OptionModule.stripAbbreviations
                        |> Option.filter (fun t -> t.HasTypeDefinition)
                        |> Option.map (fun t -> t.TypeDefinition)

                entity |> Option.exists definesUsing
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false
    | ValueNone -> false

/// The computation expression the binding at `path` sits DIRECTLY in —
/// its `use` binds to that builder's Using — and the builder expression,
/// when readable. None when a lambda, an object expression or a binding
/// intervenes: `use` there is the language's own.
let private enclosingComputation (path: SyntaxNode list) =
    let rec climb (path: SyntaxNode list) =
        match path with
        | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: SyntaxNode.SynExpr(SynExpr.App(
            isInfix = false; funcExpr = builder)) :: _ -> Some(Some builder)
        | SyntaxNode.SynExpr(SynExpr.ComputationExpr _) :: _ -> Some None
        | SyntaxNode.SynExpr(SynExpr.Lambda _ | SynExpr.ObjExpr _) :: _
        | SyntaxNode.SynBinding _ :: _
        | [] -> None
        | _ :: rest -> climb rest

    climb path

/// The names that hold values beyond a scope at `at`: the instance fields
/// and properties of the type declaring it, and the file's module-level
/// values. A store into one is a transfer to that holder.
let private holdersOn (index: AstIndex.Index) (path: SyntaxNode list) (at: range) =
    let typeMembers =
        path
        |> List.tryPick (fun node ->
            match node with
            | SyntaxNode.SynModule(SynModuleDecl.Types(typeDefns = defns)) ->
                defns
                |> List.tryFind (fun (SynTypeDefn(range = r)) -> Range.rangeContainsRange r at)
                |> Option.map (fun (SynTypeDefn(typeRepr = repr; members = extra)) ->
                    let members =
                        match repr with
                        | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                        | _ -> extra

                    members
                    |> List.collect (fun m ->
                        match m with
                        | SynMemberDefn.LetBindings(bindings = bindings) ->
                            bindings |> List.collect (fun (SynBinding(headPat = p)) -> patNames p)
                        | SynMemberDefn.AutoProperty(ident = id) -> [ id.idText ]
                        | SynMemberDefn.ValField(fieldInfo = SynField(idOpt = Some id)) -> [ id.idText ]
                        | _ -> []))
            | _ -> None)
        |> Option.defaultValue []

    let moduleValues =
        index.Decls
        |> Array.collect (fun (_, d) ->
            match d with
            | SynModuleDecl.Let(bindings = bindings) ->
                bindings
                |> List.collect (fun (SynBinding(headPat = p)) -> patNames p)
                |> Array.ofList
            | _ -> [||])

    Set.ofSeq (Seq.append typeMembers moduleValues)

/// The result-position expressions of a body: what the scope evaluates to.
[<TailCall>]
let rec private resultsLoop (acc: SynExpr list) (pending: SynExpr list) =
    match pending with
    | [] -> acc
    | e :: rest ->
        match e with
        | SynExpr.Sequential(expr2 = e2) -> resultsLoop acc (e2 :: rest)
        | LetOrUseE lou -> resultsLoop acc (lou.Body :: rest)
        | SynExpr.IfThenElse(thenExpr = t; elseExpr = els) ->
            let next =
                els
                |> Option.map (fun e2 -> t :: e2 :: rest)
                |> Option.defaultWith (fun () -> t :: rest)

            resultsLoop acc next
        | SynExpr.Match(clauses = clauses)
        | SynExpr.MatchBang(clauses = clauses) ->
            resultsLoop acc ((clauses |> List.map (fun (SynMatchClause(resultExpr = r)) -> r)) @ rest)
        | SynExpr.TryWith(tryExpr = t; withCases = clauses) ->
            resultsLoop acc (t :: (clauses |> List.map (fun (SynMatchClause(resultExpr = r)) -> r)) @ rest)
        | SynExpr.TryFinally(tryExpr = t) -> resultsLoop acc (t :: rest)
        | SynExpr.Paren(expr = inner)
        | SynExpr.Typed(expr = inner)
        | SynExpr.Upcast(expr = inner)
        | SynExpr.InferredUpcast(expr = inner)
        | SynExpr.YieldOrReturn(expr = inner)
        | SynExpr.YieldOrReturnFrom(expr = inner) -> resultsLoop acc (inner :: rest)
        | SynExpr.While _
        | SynExpr.For _
        | SynExpr.ForEach _ -> resultsLoop acc rest
        | other -> resultsLoop (other :: acc) rest

/// Is a mention at `path` one that runs LATER than the scope of the
/// binding at `binding` (whose body is `body`): inside a lambda, a local
/// function, an object expression, a `lazy`, or a computation expression
/// that starts after the binding (a `task { }` the function returns)?
/// suave's ConnectionHealthChecker kept its CancellationTokenSource in a
/// returned task's loop, and Proxy.fs its TcpListener in a `let rec loop
/// () = task { ... }`: a `use` there disposed the value before the
/// closure ran, and every health check died on its first cycle.
let private runsAfter (binding: range) (body: range) (path: SyntaxNode list) =
    path
    |> List.exists (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.Lambda _)
        | SyntaxNode.SynExpr(SynExpr.ObjExpr _)
        // a `lazy` body runs when the caller forces it
        | SyntaxNode.SynExpr(SynExpr.Lazy _) -> true
        | SyntaxNode.SynExpr(SynExpr.ComputationExpr(range = r)) ->
            // the scope's OWN computation contains the binding; one that
            // starts inside it is deferred
            not (Range.rangeContainsRange r binding)
        | SyntaxNode.SynBinding(SynBinding(headPat = headPat; range = r)) ->
            Range.rangeContainsRange body r
            && (match headPat with
                | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> true
                | _ -> false)
        | _ -> false)

/// Is a mention at `path` returned inside a tuple, a record, an upcast or
/// a union case that is the scope's result (`isResult`)? Still the
/// caller's (suave's `(port, cts)`, Mibo's `(node :> IDisposable, node :>
/// aset<'B>)` and `{ Vertices = vb; ... }`).
let private returnedThroughTo check source (isResult: range -> bool) (path: SyntaxNode list) =
    path
    |> Seq.map (fun node ->
        match node with
        | SyntaxNode.SynExpr(SynExpr.Paren _ | SynExpr.Typed _ | SynExpr.Upcast _ | SynExpr.InferredUpcast _ | SynExpr.Tuple _ | SynExpr.Record _ | SynExpr.AnonRecd _ as e) ->
            Some e
        | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f) as e) when isUnionCase check source f -> Some e
        | _ -> None)
    |> Seq.takeWhile Option.isSome
    |> Seq.exists (fun e -> isResult e.Value.Range)

/// Types whose value is work in progress: a Task or ValueTask is running
/// from the moment the member returns it; an Async runs once started.
let private pendingTypes =
    set
        [
            "System.Threading.Tasks.Task"
            "System.Threading.Tasks.Task`1"
            "System.Threading.Tasks.ValueTask"
            "System.Threading.Tasks.ValueTask`1"
            "Microsoft.FSharp.Control.FSharpAsync`1"
        ]

/// Does the member return pending work — and is it already running when
/// returned (a Task) or not until started (an Async)? ValueNone for any
/// other return type, or unresolved.
let private pendingKind (check: FSharpCheckFileResults) (source: ISourceText) (memberId: Ident) =
    match symbolAt check source memberId with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        (try
            let t = OptionModule.stripAbbreviations value.ReturnParameter.Type

            match
                (if t.HasTypeDefinition then
                     t.TypeDefinition.TryFullName
                 else
                     None)
            with
            | Some n when pendingTypes.Contains n -> ValueSome(not (n.StartsWith "Microsoft.FSharp.Control."))
            | _ -> ValueNone
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             ValueNone)
    | _ -> ValueNone

/// The last two segments of a callee's name (`Async.AwaitTask`, `ignore`),
/// through parens and type applications; empty for anything else.
[<TailCall>]
let rec private shortName (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.TypeApp(expr = inner) -> shortName inner
    | SynExpr.Ident id -> id.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
        ids
        |> List.map (fun i -> i.idText)
        |> List.rev
        |> List.truncate 2
        |> List.rev
        |> String.concat "."
    | _ -> ""

/// A `x.Member(...)` mention at `path` whose Task/ValueTask/Async result
/// is DROPPED while the work runs — `|> ignore`, `|> Async.AwaitTask |>
/// ignore`, a bare statement of Task type, `Async.Start` — is
/// fire-and-forget on the receiver: the work may still be running at
/// scope exit, where `use` would dispose it underneath (FsCheck's Runner
/// test calls `testCase.RunAsync(...) |> Async.AwaitTask |> ignore`). An
/// awaited, bound, `.Wait()`ed or `Async.RunSynchronously`'d result is
/// finished before the scope ends. The member's name, when so.
let private discardedPending
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (path: SyntaxNode list)
    (e: SynExpr)
    =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = _ :: (_ :: _ as members))) when invokedAt path e.Range ->
        let last = List.last members

        match pendingKind check source last with
        | ValueSome started ->
            // the application node the mention is the function of, and
            // the path above it
            let rec application (path: SyntaxNode list) (inner: range) =
                match path with
                | SyntaxNode.SynExpr(SynExpr.TypeApp(range = r)) :: rest -> application rest r
                | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; range = r)) :: rest when
                    Range.rangeContainsRange f.Range inner
                    ->
                    Some(r, rest)
                | _ -> None

            // where the value at `r` goes: dropped, or handed on still pending
            let rec dropped (started: bool) (r: range) (path: SyntaxNode list) =
                match path with
                | SyntaxNode.SynExpr(SynExpr.Paren(range = pr) | SynExpr.Typed(range = pr) | SynExpr.Tuple(range = pr)) :: rest ->
                    dropped started pr rest
                // a bare statement: only a running task is work in flight
                | SyntaxNode.SynExpr(SynExpr.Sequential(expr1 = a)) :: _ -> started && a.Range = r
                | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op; argExpr = a)) :: SyntaxNode.SynExpr(SynExpr.App(
                    isInfix = false; argExpr = callee; range = outer)) :: rest when
                    operatorName op = "op_PipeRight" && a.Range = r
                    ->
                    consumer started (shortName callee) outer rest
                | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a; range = outer)) :: rest when
                    Range.rangeContainsRange a.Range r
                    ->
                    consumer started (shortName f) outer rest
                | _ -> false

            and consumer (started: bool) (name: string) (outer: range) (rest: SyntaxNode list) =
                match name with
                | "ignore" -> started
                | "Async.Start"
                | "Async.StartImmediate" -> true
                // still pending, whatever happens next
                | "Async.AwaitTask"
                | "Async.Ignore"
                | "Async.Catch"
                | "Async.Parallel"
                | "Async.Sequential" -> dropped started outer rest
                | "Async.StartAsTask"
                | "Async.StartChild"
                | "Task.WhenAll"
                | "Task.WhenAny" -> dropped true outer rest
                // run to completion here: the work is over before the
                // scope ends
                | "Async.RunSynchronously"
                | "Task.WaitAll" -> false
                // handed on as an ARGUMENT to anything else — a collection
                // (`tasks.Add(client.GetStringAsync u)` then `Task.WhenAll
                // tasks` as the result), a constructor, a function this
                // rule cannot read — the work is in flight past this scope
                // and `use` would dispose the receiver under it; the
                // aliased spelling (`let t = client.GetStringAsync u` then
                // `tasks.Add t`) already stands down the same way
                | _ -> true

            match application path e.Range with
            | Some(r, rest) when dropped started r rest -> Some last.idText
            | _ -> None
        | ValueNone -> None
    | _ -> None

let private cancellationSource = set [ "System.Threading.CancellationTokenSource" ]

/// Is the callee a member or function of FSharp.Core or the BCL — one
/// whose behaviour with a token is known: it observes it while it runs,
/// and starts nothing of its own once its result is awaited?
let private bclOrCore (check: FSharpCheckFileResults) (source: ISourceText) (callee: Ident) =
    match symbolAt check source callee with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        let full = OptionModule.fullNameOf value
        let owner = OptionModule.enclosingFullName value

        // an extension member's owner is the BCL type it extends; its
        // body, and what it does with the token, is the user's
        not value.IsExtensionMember
        && (full.StartsWith "Microsoft.FSharp."
            || full.StartsWith "System."
            || owner.StartsWith "Microsoft.FSharp."
            || owner.StartsWith "System.")
    | _ -> false

/// FSharp.Core starters that return unit: the token goes to work that
/// runs on after the call has returned.
let private unitStarters =
    set [ "Async.Start"; "Async.StartImmediate"; "Async.StartWithContinuations" ]

/// The synchronous BCL and FSharp.Core members that are done with a token
/// when they return: the blocking waits. Every other synchronous callee
/// may store it — `tokens.Add ct`, `CancellationTokenSource.
/// CreateLinkedTokenSource ct` (the linked source registers on it) — and
/// so hands it on.
let private syncFinishers =
    set
        [
            "RunSynchronously"
            "WaitAll"
            "WaitAny"
            "Wait"
            "Take"
            "TryTake"
            "SignalAndWait"
            "ThrowIfCancellationRequested"
        ]

/// A CancellationTokenSource binder whose `.Token` (or the source itself,
/// or a local bound to its token) goes anywhere the scope does not see
/// finish. welendus: `let token = new CancellationTokenSource()` ...
/// `match! Loans.requestNewLoan ... token.Token false with` —
/// `requestNewLoan` hands the token to `Async.Start(work, token)` for a
/// background search that outlives the scope, and a `use` disposed the
/// source under it. The scope KEEPS the token in exactly these positions:
/// an argument of a BCL or FSharp.Core operation whose pending result
/// (`Task.Delay(ms, ct)`, `client.GetAsync(url, ct)`) is awaited on the
/// statement spine (`let!`, `do!`, `match!`, `return!`, `.Wait()`,
/// `.Result`, `.GetAwaiter().GetResult()`, `Async.RunSynchronously`,
/// `Task.WaitAll`); an argument of a synchronous blocking wait
/// (`syncFinishers`); and the right side of the local alias binding whose
/// uses this scan follows in turn. Every other position hands it on: a
/// user function (opaque), a starter (`Async.Start`), an unawaited pending
/// call, a synchronous BCL call that may store it (`tokens.Add`,
/// `CreateLinkedTokenSource`), a constructor argument (`new Worker(cts.
/// Token)`: the worker's timer dies with the source), a record field, a
/// property set (`w.Token <- cts.Token`), a tuple or option built from
/// it, a return, and anything this scan cannot name. The name of what
/// took it when the token is handed on; None when the scope keeps it.
let private tokenHandedOn
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (binder: Ident)
    (name: string)
    (aliases: Set<string>)
    (mentions: (SyntaxNode list * SynExpr)[])
    =
    if not (typeIsA cancellationSource Set.empty check source binder) then
        None
    else
        // the identifier the application's function position names, under
        // a curried chain, parens and type arguments; a receiver call's
        // member (`client.GetAsync(url, ct)` is `DotGet` when the receiver
        // is itself an expression)
        let rec calleeIdent (f: SynExpr) =
            match f with
            | SynExpr.App(isInfix = false; funcExpr = g) -> calleeIdent g
            | SynExpr.Paren(expr = inner)
            | SynExpr.TypeApp(expr = inner) -> calleeIdent inner
            | SynExpr.Ident id -> Some id
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
            | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
            | _ -> None

        // the whole curried application above `outer`: `f a b ct d` is
        // App(App(App(App(f, a), b), ct), d), and the token's App is the
        // function of the ones after it
        let rec whole (outer: range) (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; range = r)) :: rest when f.Range = outer ->
                whole r rest
            | _ -> outer, path

        // the application the mention is an argument of: through parens,
        // a tuple, an annotation and a named argument `cancellationToken =
        // ct`; a pipe `ct |> f` counts too
        let rec argumentOf (inner: range) (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren(range = r) | SynExpr.Tuple(range = r) | SynExpr.Typed(range = r)) :: rest ->
                argumentOf r rest
            | SyntaxNode.SynExpr(SynExpr.App(
                isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = op); range = r)) :: rest when
                operatorName op = "op_Equality"
                ->
                argumentOf r rest
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op; argExpr = a)) :: SyntaxNode.SynExpr(SynExpr.App(
                isInfix = false; argExpr = callee; range = outer)) :: rest when
                operatorName op = "op_PipeRight" && a.Range = inner
                ->
                Some(callee, outer, rest)
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a; range = outer)) :: rest when
                Range.rangeContainsRange a.Range inner
                ->
                let outer, rest = whole outer rest
                Some(f, outer, rest)
            | _ -> None

        // is the value at `r` finished on the statement spine before the
        // scope goes on?
        let rec awaited (r: range) (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren(range = pr) | SynExpr.Typed(range = pr)) :: rest -> awaited pr rest
            | SyntaxNode.SynBinding(SynBinding(expr = rhs)) :: SyntaxNode.SynExpr(LetOrUseE lou) :: _ when lou.IsBang ->
                rhs.Range = r
            | SyntaxNode.SynExpr(LetOrUseE lou) :: _ when lou.IsBang ->
                lou.Bindings |> List.exists (fun (SynBinding(expr = rhs)) -> rhs.Range = r)
            | SyntaxNode.SynExpr(SynExpr.DoBang(expr = e)) :: _
            | SyntaxNode.SynExpr(SynExpr.YieldOrReturnFrom(expr = e)) :: _
            | SyntaxNode.SynExpr(SynExpr.MatchBang(expr = e)) :: _ -> e.Range = r
            // `.Wait()`, `.Result`, `.GetAwaiter().GetResult()` on it
            | SyntaxNode.SynExpr(SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = ids)) as dg) :: rest when
                receiver.Range = r && not ids.IsEmpty
                ->
                match (List.last ids).idText with
                | "Wait"
                | "Result"
                | "GetResult" -> true
                | "GetAwaiter" -> awaited dg.Range rest
                | _ -> false
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; range = outer)) :: rest when f.Range = r ->
                awaited outer rest
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = op; argExpr = a)) :: SyntaxNode.SynExpr(SynExpr.App(
                isInfix = false; argExpr = callee; range = outer)) :: rest when
                operatorName op = "op_PipeRight" && a.Range = r
                ->
                finishes (shortName callee) outer rest
            | SyntaxNode.SynExpr(SynExpr.App(isInfix = false; funcExpr = f; argExpr = a; range = outer)) :: rest when
                Range.rangeContainsRange a.Range r
                ->
                finishes (shortName f) outer rest
            | _ -> false

        and finishes (consumerName: string) (outer: range) (rest: SyntaxNode list) =
            match consumerName with
            | "Async.RunSynchronously"
            | "Task.WaitAll" -> true
            // still pending: whatever wraps it must be awaited in turn
            | "Async.AwaitTask"
            | "Async.Ignore"
            | "Async.Catch" -> awaited outer rest
            | _ -> false

        // the right side of `let ct = cts.Token`, where every name the
        // pattern binds is an alias this scan follows: the token has not
        // left the scope yet
        let rec aliasBinding (inner: range) (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren(range = r) | SynExpr.Typed(range = r)) :: rest -> aliasBinding r rest
            | SyntaxNode.SynBinding(SynBinding(headPat = p; expr = rhs)) :: SyntaxNode.SynExpr(LetOrUseE _) :: _ ->
                rhs.Range = inner
                && (let bound = patBoundNames p in not bound.IsEmpty && bound |> List.forall aliases.Contains)
            | _ -> false

        // what a token that is no call's argument went into, for the
        // message: the type a constructor builds, the field or property
        // it is stored in, or the local it is bound to
        let rec positionName (path: SyntaxNode list) =
            match path with
            | SyntaxNode.SynExpr(SynExpr.Paren _ | SynExpr.Tuple _ | SynExpr.Typed _) :: rest -> positionName rest
            | SyntaxNode.SynExpr(SynExpr.New(targetType = t)) :: _ ->
                match t with
                | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> (List.last ids).idText
                | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
                    (List.last ids).idText
                | _ -> "a constructor this rule cannot name"
            | SyntaxNode.SynExpr(SynExpr.Record _) :: _
            | SyntaxNode.SynExpr(SynExpr.AnonRecd _) :: _ -> "a record"
            | SyntaxNode.SynExpr(SynExpr.LongIdentSet(SynLongIdent(id = ids), _, _)) :: _ when not ids.IsEmpty ->
                (List.last ids).idText
            | SyntaxNode.SynExpr(SynExpr.DotSet(longDotId = SynLongIdent(id = ids))) :: _ when not ids.IsEmpty ->
                (List.last ids).idText
            | SyntaxNode.SynBinding(SynBinding(headPat = p)) :: _ ->
                match patBoundNames p with
                | [ local ] -> $"the local '%s{local}'"
                | _ -> "a binding this rule cannot follow"
            | _ -> "a position this rule cannot name"

        mentions
        |> Array.tryPick (fun (path, e) ->
            let isToken =
                match e with
                | SynExpr.Ident id -> id.idText = name || aliases.Contains id.idText
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ root; t ])) ->
                    root.idText = name && t.idText = "Token"
                | _ -> false

            if not isToken then
                None
            else
                match argumentOf e.Range path with
                | None ->
                    if aliasBinding e.Range path then
                        None
                    else
                        Some(positionName path)
                | Some(f, outer, rest) ->
                    match calleeIdent f with
                    | None -> Some "a call this rule cannot name"
                    | Some callee ->
                        if not (bclOrCore check source callee) then
                            Some callee.idText
                        elif unitStarters.Contains(shortName f) then
                            Some callee.idText
                        else
                            match pendingKind check source callee with
                            | ValueSome _ -> if awaited outer rest then None else Some callee.idText
                            | ValueNone ->
                                if syncFinishers.Contains callee.idText then
                                    None
                                else
                                    Some callee.idText)

/// Find leaked local disposables. Requires typed check results for the
/// IDisposable gate.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // module-level functions of this file, by name: a disposable handed
        // to one of them can be followed one hop into its body
        let sameFileFunctions =
            index.Decls
            |> Array.collect (fun (_, d) ->
                match d with
                | SynModuleDecl.Let(bindings = bindings) ->
                    bindings
                    |> List.choose (fun (SynBinding(headPat = pat; expr = body)) ->
                        match pat with
                        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ fname ]); argPats = SynArgPats.Pats pats) when
                            not pats.IsEmpty
                            ->
                            Some(fname.idText, (pats, body))
                        | _ -> None)
                    |> Array.ofList
                | _ -> [||])
            |> Array.groupBy fst
            |> Array.choose (fun (name, defs) ->
                match defs with
                | [| _, def |] -> Some(name, def)
                | _ -> None)
            |> Map.ofArray

        // does the callee dispose the parameter the value arrives in:
        // `use`-bind it, call `.Dispose()` on it, or hand it to another
        // disposable's constructor?
        let calleeDisposes (pats: SynPat list, body: SynExpr) (argument: int) (element: int option) =
            let names = parameterNames pats argument element |> set

            let mentionsParameter (r: range) =
                index.Exprs
                |> Array.exists (fun (_, e) ->
                    match e with
                    | SynExpr.Ident id -> names.Contains id.idText && Range.rangeContainsRange r id.idRange
                    | _ -> false)

            not names.IsEmpty
            && index.Exprs
               |> Array.exists (fun (path, e) ->
                   Range.rangeContainsRange body.Range e.Range
                   && (match e with
                       | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ p; m ])) ->
                           names.Contains p.idText && m.idText = "Dispose"
                       | SynExpr.DotGet(expr = inner; longDotId = SynLongIdent(id = [ m ])) ->
                           m.idText = "Dispose" && mentionsParameter inner.Range
                       | SynExpr.Ident id when names.Contains id.idText ->
                           let usedDirectly =
                               path
                               |> List.truncate 2
                               |> List.exists (fun n ->
                                   match n with
                                   | SyntaxNode.SynExpr(LetOrUseE lou) when lou.IsUse ->
                                       lou.Bindings
                                       |> List.exists (fun (SynBinding(expr = rhs)) -> rhs.Range = id.idRange)
                                   | _ -> false)

                           usedDirectly
                           || (match classifyLoop check source (fun _ -> true) id.idRange false None path with
                               | Adopted
                               | Held -> true
                               | _ -> false)
                       | _ -> false))

        // the binding of `local` that the enclosing scope (a member, a
        // function, a lambda, a computation) constructs itself, in whose
        // body the wrapper binding at `wrapper` sits — the innermost such.
        // A construction outside the lambda is shared by every call of it,
        // so it counts as foreign there
        let localConstructionOf (declPath: SyntaxNode list) (wrapper: range) (local: string) =
            let scope =
                declPath
                |> List.tryPick (fun node ->
                    match node with
                    // a binding's own range stops at its `=`: take the rhs in
                    | SyntaxNode.SynBinding(SynBinding(expr = rhs; range = r)) -> Some(Range.unionRanges r rhs.Range)
                    | SyntaxNode.SynExpr(SynExpr.Lambda(range = r) | SynExpr.MatchLambda(range = r) | SynExpr.ObjExpr(
                        range = r) | SynExpr.ComputationExpr(range = r)) -> Some r
                    | _ -> None)

            index.Exprs
            |> Array.choose (fun (_, e) ->
                match e with
                | LetOrUseE inner when
                    not inner.IsBang
                    && Range.rangeContainsRange inner.Range wrapper
                    && inner.Range.Start <> wrapper.Start
                    && (scope |> Option.forall (fun r -> Range.rangeContainsRange r inner.Range))
                    && inner.Bindings
                       |> List.exists (fun (SynBinding(headPat = p; expr = rhs)) ->
                           locallyConstructed check source (unwrapped rhs)
                           && List.contains local (patNames p))
                    ->
                    Some inner
                | _ -> None)
            |> Array.sortByDescending (fun inner -> inner.Range.StartLine, inner.Range.StartColumn)
            |> Array.tryHead

        // does the local resource a wrapper is built over ESCAPE the scope
        // — stored beyond it, returned, handed to a function, captured by a
        // closure or a deferred computation, read by the result — so that
        // disposing the wrapper, which closes the resource, would pull it
        // out from under its new owner? The wrapper's own construction
        // (`construction`, its rhs) is the one mention that is expected; an
        // invoked member of the local (`stream.Position <- 0L`,
        // `ms.ToArray()` as a plain-valued result) keeps it here
        let localResourceEscapes
            (declPath: SyntaxNode list)
            (localRange: range)
            (body: SynExpr)
            (construction: range)
            (name: string)
            =
            let holders = holdersOn index declPath localRange
            let results = resultsLoop [] [ body ]

            let isResult (r: range) =
                results |> List.exists (fun x -> x.Range = r)

            let inLambda = runsAfter localRange body.Range
            let returnedThrough = returnedThroughTo check source isResult

            index.Exprs
            |> Array.exists (fun (path, e) ->
                Range.rangeContainsRange body.Range e.Range
                && not (Range.rangeContainsRange construction e.Range)
                && (match e with
                    | SynExpr.Ident id when id.idText = name ->
                        inLambda path
                        || isResult e.Range
                        || returnedThrough path
                        || classifyLoop check source holders.Contains e.Range false None path <> Kept
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: (_ :: _ as members))) when
                        first.idText = name
                        ->
                        let last = List.last members

                        inLambda path
                        || (not (invokedAt path e.Range) && isMethod check source last)
                        || (results |> List.exists (fun r -> Range.rangeContainsRange r.Range e.Range)
                            && not (
                                (invokedAt path e.Range || not (isMethod check source last))
                                && plainValued check source last
                            ))
                    | _ -> false))

        // is the name a resource this scope constructed and keeps: the
        // scope's own to dispose through the wrapper bound at `wrapper`
        // (its LetOrUse) and constructed by `construction` (its rhs)? One
        // already `use`-bound is disposed at scope exit whatever the
        // wrapper does
        let ownedHere (declPath: SyntaxNode list) (wrapper: range) (construction: range) (local: string) =
            match localConstructionOf declPath wrapper local with
            | Some inner ->
                inner.IsUse
                || not (localResourceEscapes declPath inner.Range inner.Body construction local)
            | None -> false

        // the identifiers a local binding's pattern names — the aliases
        // a value reached through the binder can be bound to
        let rec patIdents (p: SynPat) =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id)) -> [ id ]
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) -> [ id ]
            | SynPat.Paren(inner, _)
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner) -> patIdents inner
            | SynPat.Tuple(elementPats = ps) -> ps |> List.collect patIdents
            | SynPat.As(lhsPat = lhs; rhsPat = rhs) -> patIdents lhs @ patIdents rhs
            | _ -> []

        [
            for declPath, expr in index.Exprs do
                match expr with
                | LetOrUseE lou when not (lou.IsBang || lou.IsUse || lou.IsRecursive) ->
                    match lou.Bindings with
                    | [ SynBinding(
                            isMutable = false
                            headPat = (SynPat.Named(ident = SynIdent(ident = binder); accessibility = None) | SynPat.LongIdent(
                                longDotId = SynLongIdent(id = [ binder ])
                                argPats = SynArgPats.Pats []
                                accessibility = None))
                            expr = rhs) ] when
                        (let rhs = unwrapped rhs

                         locallyConstructed check source rhs
                         && not (wrapsForeignResource check source (ownedHere declPath expr.Range rhs.Range) rhs)
                         && not (ObjectDesign.ownsNoResource check source rhs))
                        && ObjectDesign.resolvesToDisposable check source binder
                        ->
                        let name = binder.idText
                        let body = lou.Body
                        let holders = holdersOn index declPath expr.Range

                        let mentionsOf (names: Set<string>) =
                            index.Exprs
                            |> Array.filter (fun (_, e) ->
                                match e with
                                | SynExpr.Ident id when names.Contains id.idText ->
                                    Range.rangeContainsRange body.Range id.idRange
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when
                                    names.Contains firstId.idText
                                    ->
                                    Range.rangeContainsRange body.Range firstId.idRange
                                | _ -> false)

                        // every mention of the binder itself in the scope
                        let binderMentions = mentionsOf (Set.singleton name)

                        // the locals bound to values reached THROUGH the
                        // binder — `let pending = client.GetStringAsync url`,
                        // `let cmd = conn.CreateCommand()`, `let f = c.Convert`
                        // — and through those in turn: a task, a command, a
                        // reader, a method group still needs the binder
                        // behind it, so where such an alias goes is where the
                        // binder goes. A plain-valued local (`let b =
                        // stream.ReadByte()`) is evaluated and done
                        let aliases =
                            let localBindings =
                                index.Exprs
                                |> Array.collect (fun (_, e) ->
                                    match e with
                                    | LetOrUseE inner when Range.rangeContainsRange body.Range inner.Range ->
                                        inner.Bindings
                                        |> List.choose (fun (SynBinding(headPat = p; expr = rhs)) ->
                                            match p with
                                            // a local function: its body's mentions
                                            // are captures already
                                            | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> None
                                            | _ -> Some(patIdents p, rhs.Range))
                                        |> Array.ofList
                                    | _ -> [||])

                            let rec grow (tracked: Set<string>) =
                                let mentioned = mentionsOf tracked

                                let more =
                                    localBindings
                                    |> Array.collect (fun (ids, rhsRange) ->
                                        if
                                            mentioned
                                            |> Array.exists (fun (_, m) -> Range.rangeContainsRange rhsRange m.Range)
                                        then
                                            ids
                                            |> List.filter (fun id ->
                                                not (tracked.Contains id.idText)
                                                && not (plainValuedLocal check source id))
                                            |> List.map (fun id -> id.idText)
                                            |> Array.ofList
                                        else
                                            [||])

                                if more.Length = 0 then
                                    tracked
                                else
                                    grow (Set.union tracked (Set.ofArray more))

                            grow (Set.singleton name) |> Set.remove name

                        // classify every mention of the binder and of its
                        // aliases in the scope
                        let mentions =
                            if aliases.IsEmpty then
                                binderMentions
                            else
                                mentionsOf (Set.add name aliases)

                        // `x.Dispose()`, `x.Close()` where Close is Dispose
                        // (streams, writers, sockets), and
                        // `(x :> IDisposable).Dispose()` (fantomas's daemon
                        // tests), whose upcast hides the receiver
                        let manuallyDisposed =
                            binderMentions
                            |> Array.exists (fun (_, e) ->
                                match e with
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ _; m ])) ->
                                    m.idText = "Dispose"
                                    || m.idText = "DisposeAsync"
                                    || (m.idText = "Close" && closeDisposes check source binder)
                                | _ -> false)
                            || index.Exprs
                               |> Array.exists (fun (_, e) ->
                                   match e with
                                   | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ m ])) when
                                       (m.idText = "Dispose" || m.idText = "DisposeAsync")
                                       && Range.rangeContainsRange body.Range e.Range
                                       ->
                                       binderMentions
                                       |> Array.exists (fun (_, mention) ->
                                           match mention with
                                           | SynExpr.Ident _ -> Range.rangeContainsRange receiver.Range mention.Range
                                           | _ -> false)
                                   | _ -> false)

                        if not manuallyDisposed then
                            let results = resultsLoop [] [ body ]

                            let isResult (r: range) =
                                results |> List.exists (fun x -> x.Range = r)

                            // returned inside a tuple, a record, an upcast or a
                            // union case: still the caller's
                            let returnedThrough = returnedThroughTo check source isResult

                            // a mention that runs LATER than the scope: inside a
                            // lambda, a local function, an object expression, or
                            // a computation expression that starts after the
                            // binding (a `task { }` the function returns)
                            let inLambda = runsAfter lou.Range body.Range

                            // a `x.Member` mention that is not the function
                            // of an application is a method group handed on
                            // (`Seq.map c.Convert xs`, `changed.Add c.Refresh`):
                            // it runs after the scope, on a disposed receiver
                            let methodGroup (path: SyntaxNode list) (e: SynExpr) =
                                match e with
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                    not (invokedAt path e.Range) && isMethod check source (List.last ids)
                                | _ -> false

                            // where each mention sends the value. An alias
                            // returned is the RESULT reading the binder, not
                            // an ownership transfer of it; an alias adopted or
                            // held goes somewhere this rule cannot follow
                            let escapes =
                                [
                                    for path, e in mentions do
                                        match e with
                                        | SynExpr.Ident id ->
                                            let escape =
                                                if inLambda path then
                                                    Captured
                                                elif isResult e.Range || returnedThrough path then
                                                    Returned
                                                else
                                                    classifyLoop check source holders.Contains e.Range false None path

                                            if id.idText = name then
                                                escape
                                            else
                                                match escape with
                                                | Returned -> ResultReads
                                                | Adopted
                                                | Held -> Handed None
                                                | other -> other
                                        | SynExpr.LongIdent _ when inLambda path || methodGroup path e -> Captured
                                        | _ -> ()
                                ]
                                // a same-file callee is read one hop: disposing
                                // the parameter is an ownership transfer, not
                                // disposing it is a leak this note can name
                                |> List.map (fun escape ->
                                    match escape with
                                    | HandedAt(callee, argument, element) ->
                                        match Map.tryFind callee sameFileFunctions with
                                        | Some target when calleeDisposes target argument element -> Adopted
                                        | Some _ -> escape
                                        | None -> Handed(Some callee)
                                    | other -> other)

                            // a member access in result position may hand out
                            // something still tied to the object (`client.GetAsync
                            // url` as the value: a task the scope's `use` would
                            // dispose the client under); a plain value
                            // (`md5.ComputeHash bytes`, `reader.ReadToEnd()`) is
                            // computed before the scope exits
                            // — and only when the member is a property read
                            // or INVOKED there: a method group's plain return
                            // type says nothing about when it runs
                            let inResult =
                                mentions
                                |> Array.exists (fun (path, e) ->
                                    inLambda path
                                    || (results |> List.exists (fun r -> Range.rangeContainsRange r.Range e.Range)
                                        && not (
                                            match e with
                                            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                                not ids.IsEmpty
                                                ->
                                                let last = List.last ids

                                                (invokedAt path e.Range || not (isMethod check source last))
                                                && plainValued check source last
                                            | _ -> false
                                        )))

                            // an object that does work of its own after the
                            // scope returns: a timer, a watcher, a listener by
                            // type; anything constructed with a callback; an
                            // event of it the scope subscribes to (`w.Changed.Add
                            // f`, `t.Elapsed |> Event.add f`, `x.Subscribe o`), a
                            // token registration, a `Start()`/`Enable...` call.
                            // `use` would stop it on the way out
                            let selfActive =
                                selfActiveType check source binder
                                || index.Exprs
                                   |> Array.exists (fun (_, e) ->
                                       match e with
                                       | SynExpr.Lambda _
                                       | SynExpr.MatchLambda _ -> Range.rangeContainsRange rhs.Range e.Range
                                       | _ -> false)
                                || binderMentions
                                   |> Array.exists (fun (path, e) ->
                                       match e with
                                       | SynExpr.LongIdent(longDotId = SynLongIdent(id = _ :: (_ :: _ as members))) ->
                                           let last = List.last members

                                           last.idText = "Subscribe"
                                           || last.idText = "AddHandler"
                                           || last.idText.StartsWith "add_"
                                           || (last.idText = "Register"
                                               && members |> List.exists (fun m -> m.idText = "Token"))
                                           || members |> List.exists (isEvent check source)
                                           || (invokedAt path e.Range && startsWork check source last)
                                       | _ -> false)
                                || index.Exprs
                                   |> Array.exists (fun (_, e) ->
                                       match e with
                                       | SynExpr.LongIdentSet(
                                           longDotId = SynLongIdent(id = first :: (_ :: _ as members))) ->
                                           first.idText = name
                                           && Range.rangeContainsRange body.Range e.Range
                                           && (List.last members).idText.StartsWith "Enable"
                                       | _ -> false)

                            // a Task/Async-returning member of the binder called
                            // and its result dropped (`|> ignore`, `|> Async.AwaitTask
                            // |> ignore`, a bare statement, `Async.Start`): work
                            // still running at scope exit, on a receiver `use`
                            // would dispose under it (FsCheck's Runner test:
                            // `testCase.RunAsync(...) |> Async.AwaitTask |> ignore`)
                            let inFlight =
                                binderMentions
                                |> Array.tryPick (fun (path, e) -> discardedPending check source path e)

                            // a CancellationTokenSource whose token is handed
                            // to a call the scope does not see finish: the
                            // work it cancels may outlive the scope, and
                            // `use` would dispose the source under it
                            // (welendus: `requestNewLoan ... token.Token`,
                            // which Async.Starts a background search)
                            let tokenHanded = tokenHandedOn check source binder name aliases mentions

                            // `use` inside a computation expression binds to
                            // the builder's Using: `query { }` and a hand-written
                            // builder without one make it an FS0708
                            let builderSupportsUse =
                                match enclosingComputation declPath with
                                | None -> true
                                | Some(Some builder) -> builderDefinesUsing check source builder
                                | Some None -> false

                            let destinations =
                                escapes
                                |> List.choose (fun e ->
                                    match e with
                                    | Handed(Some d) -> Some(Destination.Function(d, false))
                                    | Handed None -> Some Destination.Unknown
                                    | HandedAt(callee, _, _) -> Some(Destination.Function(callee, true))
                                    | StoredLocally name -> Some(Destination.StoredLocally name)
                                    | Captured -> Some Destination.Captured
                                    | ResultReads -> Some Destination.ReadInResult
                                    | Returned
                                    | Adopted
                                    | Held
                                    | Kept -> None)

                            // the first named destination, else the unnamed one
                            let handedTo =
                                destinations
                                |> List.tryFind (fun d -> d <> Destination.Unknown)
                                |> Option.orElse (List.tryHead destinations)

                            // an escape is an ownership transfer: the caller gets
                            // it back, another disposable adopts it, a holder beyond
                            // this scope keeps it. The owner is decided, whatever
                            // else the scope did with the value on the way (Activity.fs
                            // registers its listener and returns it) — a `use` here
                            // would be wrong, and there is nothing to say
                            let transferred =
                                escapes |> List.exists (fun e -> e = Returned || e = Adopted || e = Held)

                            // the `let` keyword: the LetOrUse node starts at it
                            let letRange =
                                Range.mkRange
                                    expr.Range.FileName
                                    expr.Range.Start
                                    (Position.mkPos expr.Range.StartLine (expr.Range.StartColumn + 3))

                            if textOfRange source letRange = "let" && not transferred then
                                let canFix =
                                    handedTo.IsNone
                                    && not inResult
                                    && not selfActive
                                    && inFlight.IsNone
                                    && tokenHanded.IsNone
                                    && builderSupportsUse

                                {
                                    Range = letRange
                                    Name = name
                                    Fix = if canFix then Some("let", "use") else None
                                    Destination =
                                        if canFix then
                                            None
                                        elif handedTo.IsSome then
                                            handedTo
                                        elif selfActive then
                                            Some Destination.SelfActive
                                        elif inFlight.IsSome then
                                            Some(Destination.InFlight inFlight.Value)
                                        elif tokenHanded.IsSome then
                                            Some(Destination.TokenHanded tokenHanded.Value)
                                        elif inResult then
                                            Some Destination.ReadInResult
                                        else
                                            Some Destination.NoBuilderUsing
                                    Context =
                                        match bindingContext declPath expr.Range with
                                        // a handle the OS reclaims at exit is no loss
                                        // in main; unflushed work is
                                        | Some ScopeContext.EntryPoint when not (flushSensitive check source binder) ->
                                            None
                                        | context -> context
                                }
                    | _ -> ()
                | _ -> ()
        ]

/// FR0150 (correctness): a `use`-bound disposable captured by a
/// computation that OUTLIVES the scope.
///
///     let startChecker () =
///         use cts = new CancellationTokenSource()   // disposed when THIS returns
///         task { while true do ... cts.Token ... }  // reads it long after
///
/// `use` disposes at the end of the enclosing scope, and a `task`/`async`
/// the scope RETURNS runs after that: suave's ConnectionHealthChecker
/// disposes its CancellationTokenSource and then reads `.Token` on every
/// interval, which throws ObjectDisposedException the first time round.
/// The computation, not the scope, owns the resource.
///
/// The fix moves the binding inside the computation, where the same `use`
/// disposes it when the work finishes — offered in editors, since
/// constructing later is a timing change only the author can sign off:
///
///     let startChecker () =
///         task {
///             use cts = new CancellationTokenSource()
///             while true do ... cts.Token ...
///         }
///
/// Gates: the computation is the scope's RESULT (returned directly, or
/// through a single binding of it), it mentions the binder, and nothing
/// between the `use` and the computation touches the binder — otherwise
/// the note stands without a fix.
///
/// Prior art: G-Research's `DisposedBeforeAsyncRunAnalyzer` finds the same
/// shape, and recommends the same repair. Two deliberate differences: it
/// flags the shape whether or not the workflow ever reads the disposable
/// (their example returns a constant), while this requires the mention,
/// so it fires only where a use-after-dispose can actually happen; and it
/// offers the move as an edit rather than prose. Anyone already running
/// their analyzers has this covered — `"FR0150": false` turns it off.
type EscapingUseSuggestion =
    {
        Range: range
        /// The bound name, for the message.
        Name: string
        /// The builder the computation uses, for the message.
        Builder: string
        /// (range, original, replacement) edits moving the binding inside
        /// the computation. Empty when anything between the two touches
        /// the binder, or the layout is not one this can rewrite.
        Edits: (range * string * string) list
    }

let private escapingBuilders = set [ "task"; "async"; "backgroundTask" ]

/// `task { body }` — the builder name and the body.
[<return: Struct>]
let private (|BuilderLiteral|_|) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident builder; argExpr = SynExpr.ComputationExpr(expr = body)) when
        escapingBuilders.Contains builder.idText
        ->
        ValueSome(builder.idText, body)
    | _ -> ValueNone

/// Find `use` bindings whose disposable escapes into a computation the
/// scope returns. Requires typed check results for the construction gate.
let findEscapingUse
    (parseTree: ParsedInput)
    (source: ISourceText)
    (check: FSharpCheckFileResults)
    : EscapingUseSuggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // every mention of `name` inside `r`
        let mentionsIn (name: string) (r: range) =
            index.Exprs
            |> Array.exists (fun (_, e) ->
                Range.rangeContainsRange r e.Range
                && (match e with
                    | SynExpr.Ident id -> id.idText = name
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> first.idText = name
                    | _ -> false))

        // the tail expression of a statement chain, and the statements
        // passed on the way — `let a = ... in let b = ... in tail`
        // acc is built REVERSED and turned once at the base case: appending
        // (`acc @ rhss`) copied the whole accumulator at every step, which is
        // O(n2) down a long statement chain
        let rec tailOf (acc: SynExpr list) (e: SynExpr) =
            match e with
            | LetOrUseE lou when not lou.IsBang ->
                let rhss = lou.Bindings |> List.map (fun (SynBinding(expr = rhs)) -> rhs)
                tailOf (List.rev rhss @ acc) lou.Body
            | SynExpr.Sequential(expr1 = a; expr2 = b) -> tailOf (a :: acc) b
            | tail -> List.rev acc, tail


        [
            for _, expr in index.Exprs do
                match expr with
                | LetOrUseE lou when lou.IsUse && not lou.IsBang ->
                    match lou.Bindings with
                    | [ SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = binder)); expr = rhs) ] when
                        locallyConstructed check source rhs
                        ->
                        let passed, tail = tailOf [] lou.Body

                        // the computation the scope hands back: the tail
                        // itself, or the one binding whose name it returns
                        let escaping =
                            match tail with
                            | BuilderLiteral(builder, body) -> Some(builder, body, tail)
                            | SynExpr.Ident named ->
                                index.Exprs
                                |> Array.tryPick (fun (_, outer) ->
                                    match outer with
                                    | LetOrUseE inner when
                                        not inner.IsBang && Range.rangeContainsRange lou.Range inner.Range
                                        ->
                                        inner.Bindings
                                        |> List.tryPick (fun (SynBinding(headPat = p; expr = r)) ->
                                            match p, r with
                                            | SynPat.Named(ident = SynIdent(ident = id)),
                                              BuilderLiteral(builder, body) when id.idText = named.idText ->
                                                Some(builder, body, r)
                                            | _ -> None)
                                    | _ -> None)
                            | _ -> None

                        match escaping with
                        | Some(builder, body, ceExpr) when mentionsIn binder.idText body.Range ->
                            // the binding moves only when nothing it passes
                            // on the way touches it, and it owns its line so
                            // the edit is a whole-line move
                            let untouchedBetween =
                                passed
                                |> List.forall (fun e ->
                                    Range.rangeContainsRange e.Range ceExpr.Range
                                    || not (mentionsIn binder.idText e.Range))

                            let useLine = lou.Range.StartLine
                            let useText = (source.GetLineString(useLine - 1)).TrimEnd()

                            let ownsItsLine =
                                useText.TrimStart().StartsWith "use " && rhs.Range.EndLine = useLine

                            // the computation's first statement: the binding
                            // slots in above it, at its indentation
                            let firstStatement =
                                let inner =
                                    match body with
                                    | LetOrUseE i -> i.Range.Start
                                    | SynExpr.Sequential(expr1 = a) -> a.Range.Start
                                    | other -> other.Range.Start

                                if
                                    inner.Line > ceExpr.Range.StartLine
                                    && inner.Column <= (source.GetLineString(inner.Line - 1)).Length
                                    && (source.GetLineString(inner.Line - 1)).Substring(0, inner.Column).Trim() = ""
                                then
                                    Some inner
                                else
                                    None

                            let edits =
                                match untouchedBetween && ownsItsLine, firstStatement with
                                | true, Some p ->
                                    let indent = System.String(' ', p.Column)

                                    let removeRange =
                                        Range.mkRange
                                            lou.Range.FileName
                                            (Position.mkPos useLine 0)
                                            (Position.mkPos (useLine + 1) 0)

                                    let insertAt = Range.mkRange lou.Range.FileName p p

                                    [
                                        insertAt, "", useText.TrimStart() + "\n" + indent
                                        removeRange, textOfRange source removeRange, ""
                                    ]
                                | _ -> []

                            {
                                Range = lou.Range
                                Name = binder.idText
                                Builder = builder
                                Edits =
                                    (if edits |> List.exists (fun (r, _, _) -> spansDirective source r) then
                                         []
                                     else
                                         edits)
                            }
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]
