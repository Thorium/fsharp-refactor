/// FR0140 (fix, idiom): a constructor immediately followed by property
/// assignments on the object it just made is F#'s named-property
/// construction spelled out the long way.
///
///     let h = Henkilo()              let h = Henkilo(Id = 1L, Etunimi = "x")
///     h.Id <- 1L              →
///     h.Etunimi <- "x"
///
/// This is not a constructor overload and it buys no speed: it is the
/// same calls in the same order. What it buys is that the object READS
/// as constructed rather than assembled — immutable-looking, even though
/// the mutation is still there underneath — and the half-built value
/// stops being nameable in between. That is why this is an idiom rule.
///
/// F# sets named properties in the order written, after the constructor
/// runs — checked against the sequential form with logging setters, the
/// two produce the identical order — so the rewrite is behaviour
/// preserving even when a setter has side effects.
///
/// Named properties are COMMA separated. A newline-separated list reads
/// as values and fails with FS0039, so the fix always emits commas.
///
/// Safety rules:
///   - the assignments must be the statements IMMEDIATELY after the
///     binding, uninterrupted: anything in between could observe the
///     half-built object, and moving code across it changes evaluation
///     order
///   - every target is `v.Prop` on the bound name itself, each property
///     distinct — a repeated property would collapse two writes into one
///   - no assigned expression may mention `v`: inside the constructor
///     call the object does not exist yet
///   - each property resolves (typed) to a SETTABLE property, so a
///     record field or a method never matches
///   - every assignment is single-line, since the values splice verbatim
module FSharp.Refactor.ObjectInitializer

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The whole region: the constructor call through the last
        /// assignment it absorbs.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// For the message — how many assignments moved in.
        Count: int
    }

/// `v.Prop <- rhs` on the given name, or None.
[<return: Struct>]
let private (|PropertySet|_|) (name: string) (e: SynExpr) =
    match e with
    | SynExpr.LongIdentSet(SynLongIdent(id = [ receiver; prop ]), rhs, _) when receiver.idText = name ->
        ValueSome(prop, rhs)
    | _ -> ValueNone

/// Peel the leading run of property sets off a statement sequence.
[<TailCall>]
let rec private leadingSets (name: string) (e: SynExpr) (acc: (Ident * SynExpr) list) =
    match e with
    | SynExpr.Sequential(expr1 = PropertySet name (prop, rhs); expr2 = rest) ->
        leadingSets name rest ((prop, rhs) :: acc)
    // the last statement of the block can be an assignment too
    | PropertySet name (prop, rhs) -> List.rev ((prop, rhs) :: acc), None
    | _ -> List.rev acc, Some e

/// The identifier naming what is being called, for a typed lookup.
[<TailCall>]
let rec private calleeIdent (e: SynExpr) =
    match e with
    | SynExpr.Ident i -> ValueSome i
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.App(funcExpr = inner) -> calleeIdent inner
    | SynExpr.New(targetType = t) ->
        match t with
        | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
        | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) when not ids.IsEmpty ->
            ValueSome(List.last ids)
        | _ -> ValueNone
    | _ -> ValueNone

/// Does this expression CONSTRUCT, as opposed to merely returning an
/// object? The distinction decides correctness, not tidiness: named
/// arguments on a constructor set properties, but on a method they bind
/// PARAMETERS. `Factory.Create()` followed by `h.Id <- 1L` would fold to
/// `Factory.Create(Id = 1L)`, and if Create happens to take an `Id` that
/// COMPILES while calling something else entirely — the one failure the
/// build check cannot catch. So the callee must resolve to a constructor.
let private isConstruction (check: FSharpCheckFileResults) (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.New _
    | SynExpr.App(isInfix = false) ->
        match calleeIdent e with
        | ValueSome ident ->
            let r = ident.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as value ->
                    (try
                        value.IsConstructor
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                // the type's own name resolves to the entity for `T()`
                | :? FSharpEntity as entity ->
                    (try
                        entity.IsClass || entity.IsValueType
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false
        | ValueNone -> false
    | _ -> false

/// Does any expression inside `r` mention `name`? Inside the constructor
/// call the object does not exist yet, so a value that reads it — even
/// `h.Count + 1` — cannot move in.
let private mentions (index: AstIndex.Index) (name: string) (r: range) =
    index.Exprs
    |> Array.exists (fun (_, e) ->
        match e with
        | SynExpr.Ident id when id.idText = name -> Range.rangeContainsRange r id.idRange
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = firstId :: _)) when firstId.idText = name ->
            Range.rangeContainsRange r firstId.idRange
        | _ -> false)

/// Is this identifier a settable property of the receiver's type — and
/// one that can actually be named in the construction?
///
/// A property sharing its name with a CONSTRUCTOR PARAMETER cannot:
/// `type B(Size: int)` with a settable `Size` makes `B(5, Size = 4)`
/// bind the named argument to the parameter, and the call is then one
/// unnamed plus one named argument for a one-argument constructor —
/// FS0500. The build check would catch it, but a pass spent to be told
/// so is a pass wasted.
let private isSettableProperty (check: FSharpCheckFileResults) (source: ISourceText) (prop: Ident) =
    let r = prop.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ prop.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value ->
            (try
                let clashesWithConstructorParameter =
                    match value.DeclaringEntity with
                    | Some entity ->
                        entity.MembersFunctionsAndValues
                        |> Seq.filter (fun m -> m.IsConstructor)
                        |> Seq.collect (fun m -> m.CurriedParameterGroups)
                        |> Seq.concat
                        |> Seq.exists (fun p ->
                            match p.Name with
                            | Some n -> n = prop.idText
                            | None -> false)
                    | None -> false

                value.IsProperty && value.HasSetterMethod && not clashesWithConstructorParameter
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 false)
        | _ -> false
    | None -> false

/// Does the construction already carry a TYPE-ANNOTATED argument?
///
/// `ChatResponse(assistantMsg: ChatMessage)` cannot take named properties
/// appended to it: after the `:` the parser is reading a TYPE, and the comma
/// that would introduce the first property ends it — "Unexpected symbol ','
/// in expression", then the rest of the file fails to parse. Verified
/// directly: `Resp(m: Msg, Model = "a")` does not compile, while
/// `Resp(m, Model = "a")` does. Found on Fuuga's McpToolRouting.
let private hasAnnotatedArgument (e: SynExpr) =
    let rec annotated (arg: SynExpr) =
        match arg with
        | SynExpr.Typed _ -> true
        | SynExpr.Paren(expr = inner) -> annotated inner
        | SynExpr.Tuple(exprs = items) -> items |> List.exists annotated
        | _ -> false

    match e with
    | SynExpr.App(argExpr = arg) -> annotated arg
    | SynExpr.New(expr = arg) -> annotated arg
    | _ -> false

/// Is the construction's argument list PARENTHESISED — `T(a)`, `T()`,
/// `new T(a, b)`? Named properties splice in before a closing paren, and
/// `ProcessStartInfo "dotnet"` — juxtaposed, no parens — has none: the
/// splice produced `ProcessStartInfo "dotnet"(Arguments = ...)`, "This value
/// is not a function and cannot be applied", and every later use of the
/// value lost its type (Fable's MSBuildCrackerResolver). Such a call is left
/// alone rather than re-shaped into a parenthesised one.
let private hasParenthesisedArguments (e: SynExpr) =
    let parenthesised (arg: SynExpr) =
        match arg with
        | SynExpr.Paren _
        | SynExpr.Const(SynConst.Unit, _) -> true
        | _ -> false

    match e with
    | SynExpr.App(argExpr = arg) -> parenthesised arg
    | SynExpr.New(expr = arg) -> parenthesised arg
    | _ -> false

/// Wrap once the one-line form would run past this column. Seven
/// properties spliced onto one line made a 380-character line on the
/// sample this rule was written for — correct, compiling, and unreadable.
[<Literal>]
let private WrapColumn = 100

/// The named-property layouts: the whole call on the construction's line,
/// or — when that line would run past WrapColumn — the fantomas shape,
/// whose text starts right after the binding's `=`:
///
///     let psi =
///         ProcessStartInfo(
///             FileName = "dotnet",
///             Arguments = args
///         )
///
/// The hanging form (`let psi = ProcessStartInfo(` with the properties
/// under the open paren, the `)` dangling) is what `fantomas --check`
/// rejected on the compiler's ShadowPass.fs.
type private Layout =
    | OneLine of string
    | Wrapped of string

/// Splice the named properties into the constructor call's argument list.
/// `T()` has a unit argument to replace; `T(a)` gets them appended.
/// `letColumn` is the column of the `let` whose binding the call is.
let private withNamedArgs (ctorText: string) (startColumn: int) (letColumn: int) (args: string list) =
    let trimmed = ctorText.TrimEnd()

    /// Index of the `(` matching the final `)`, or -1. Text matching is not
    /// enough here: `T( )` does not end with "()" and the naive branch
    /// emitted `T( , Age = 42)`, which does not compile.
    let openIndex =
        if not (trimmed.EndsWith ')') then
            -1
        else
            let mutable depth = 0
            let mutable i = trimmed.Length - 1
            let mutable found = -1

            while i >= 0 && found < 0 do
                if trimmed.[i] = ')' then
                    depth <- depth + 1
                elif trimmed.[i] = '(' then
                    depth <- depth - 1

                    if depth = 0 then
                        found <- i

                i <- i - 1

            found

    /// Whitespace between the parens means there are no arguments yet.
    let argsAreEmpty =
        openIndex >= 0
        && trimmed.Substring(openIndex + 1, trimmed.Length - openIndex - 2).Trim() = ""

    let splice (joined: string) =
        if openIndex < 0 then
            // no argument list at all (`T` alone is not a construction we match)
            $"{trimmed}({joined})"
        elif argsAreEmpty then
            trimmed.Substring(0, openIndex) + "(" + joined + ")"
        else
            trimmed.Substring(0, trimmed.Length - 1) + ", " + joined + ")"

    let oneLine = splice (String.concat ", " args)

    if startColumn + oneLine.Length <= WrapColumn then
        OneLine oneLine
    else
        let callIndent = System.String(' ', letColumn + 4)
        let inner = System.String(' ', letColumn + 8)

        let body = args |> List.map (fun a -> inner + a) |> String.concat ",\n"

        let head =
            if openIndex < 0 then trimmed + "("
            elif argsAreEmpty then trimmed.Substring(0, openIndex) + "("
            else trimmed.Substring(0, trimmed.Length - 1) + ","

        Wrapped("\n" + callIndent + head + "\n" + body + "\n" + callIndent + ")")

/// A named property's value: parenthesised unless atomic. `=` in a named
/// property binds tighter than a cast, so `Connection = con :?> SqlConnection`
/// parses as `(Connection = con) :?> SqlConnection` — an equality against an
/// undefined `Connection`, which is exactly the error SQLProvider reported.
/// `null` and literals — `-1` included — are atoms here and never gain the
/// parentheses the original did not have.
let private valueText (source: ISourceText) (rhs: SynExpr) =
    match rhs with
    | SynExpr.Null _
    | SynExpr.Const _ -> textOfRange source rhs.Range
    | _ -> argumentText source rhs

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for _, expr in index.Exprs do
              match expr with
              | LetOrUseE lou when not (lou.IsBang || lou.IsUse) ->
                  match lou.Bindings with
                  | [ SynBinding(
                          headPat = SynPat.Named(ident = SynIdent(ident = name)); expr = ctor; trivia = bindingTrivia) ] when
                      isSingleLine ctor.Range
                      && hasParenthesisedArguments ctor
                      && not (hasAnnotatedArgument ctor)
                      ->
                      // `rest` must exist: these are the statements of an
                      // expression body, so folding away every one of them
                      // would leave `let h = H(Id = 1L)` with nothing after
                      // it, which does not compile
                      let sets, rest = leadingSets name.idText lou.Body []

                      let distinct =
                          sets |> List.map (fun (p, _) -> p.idText) |> List.distinct |> List.length

                      if
                          rest.IsSome
                          && not sets.IsEmpty
                          && distinct = sets.Length
                          // the object cannot be mentioned in its own
                          // construction arguments
                          && sets
                             |> List.forall (fun (_, rhs) ->
                                 isSingleLine rhs.Range && not (mentions index name.idText rhs.Range))
                          // the typed lookups go LAST: each costs an FCS symbol
                          // resolution, and only a binding actually followed by
                          // property sets can reach them. From the `when` clause
                          // `isConstruction` charged that price for every
                          // single-line `let x = f a` in the file.
                          && isConstruction check source ctor
                          && sets |> List.forall (fun (p, _) -> isSettableProperty check source p)
                      then
                          let last = sets |> List.last |> snd

                          let args = sets |> List.map (fun (p, rhs) -> $"{p.idText} = {valueText source rhs}")

                          // a greedy last argument — `T(fun _ -> false)` — would
                          // swallow the named properties appended after it
                          // (`fun _ -> false, Hosted = true` is a lambda returning
                          // a tuple: the TypeProviders SDK's
                          // TypeProviderConfig); it gets its own parentheses
                          let ctorText =
                              let lastArgument =
                                  match ctor with
                                  | SynExpr.New(expr = SynExpr.Paren(expr = inner))
                                  | SynExpr.App(argExpr = SynExpr.Paren(expr = inner)) ->
                                      match inner with
                                      | SynExpr.Tuple(exprs = es) -> Some(List.last es)
                                      | e -> Some e
                                  | _ -> None

                              let greedy (e: SynExpr) =
                                  match e with
                                  | SynExpr.Lambda _
                                  | SynExpr.MatchLambda _
                                  | SynExpr.Match _
                                  | SynExpr.IfThenElse _
                                  | SynExpr.TryWith _
                                  | SynExpr.TryFinally _
                                  | SynExpr.Sequential _
                                  | SynExpr.LetOrUse _ -> true
                                  | _ -> false

                              match lastArgument with
                              | Some e when greedy e ->
                                  let before =
                                      textOfRange
                                          source
                                          (Range.mkRange ctor.Range.FileName ctor.Range.Start e.Range.Start)

                                  let after =
                                      textOfRange source (Range.mkRange ctor.Range.FileName e.Range.End ctor.Range.End)

                                  before + "(" + textOfRange source e.Range + ")" + after
                              | _ -> textOfRange source ctor.Range

                          // the wrapped layout starts on the binding's `=`
                          // line and needs the `let` column; the region then
                          // runs from just after the `=` (the space before
                          // the call goes with it)
                          let letColumn = expr.Range.StartColumn

                          let ctorRegion = Range.mkRange ctor.Range.FileName ctor.Range.Start last.Range.End

                          let region, replacement =
                              match
                                  withNamedArgs ctorText ctor.Range.StartColumn letColumn args,
                                  bindingTrivia.EqualsRange
                              with
                              | OneLine text, _ -> ctorRegion, text
                              | Wrapped text, Some equals ->
                                  Range.mkRange ctor.Range.FileName equals.End last.Range.End, text
                              // no `=` to hang from (never for a let; kept total)
                              | Wrapped text, None -> ctorRegion, text.TrimStart()

                          { Range = region
                            OriginalText = textOfRange source region
                            ReplacementText = replacement
                            Count = sets.Length }
                  | _ -> ()
              | _ -> () ]
