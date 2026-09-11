/// FR0151: an exception handler that reads only `.Message` (or
/// `.ToString()`) from an exception whose ACTUAL diagnosis lives somewhere
/// else on the type.
///
///     with :? ReflectionTypeLoadException as e ->
///         log e.Message        // "Unable to load one or more of the
///                              //  requested types." and nothing else.
///
/// For that one the first question is not how to report the failure but
/// whether it IS one. .NET loads every referenced assembly, so what failed
/// is routinely a dependency the caller never touches - a localization
/// satellite, an optional plugin - while `e.Types` already holds the types
/// that loaded, with nulls where the others would be. Filtering those and
/// carrying on is usually the whole repair, which is why the editor offers
/// it FIRST and the LoaderExceptions join second.
///
///     with :? WebException as wex ->
///         log wex.Message      // the server's error body is in
///                              //  wex.Response.GetResponseStream(),
///                              //  never in the message
///
/// Deliberately NOT the same rule as FR0120, and deliberately narrower.
/// FR0120 treats `ex.Message` as a handled exception ON PURPOSE, because
/// logging only the message can be a GDPR/PII decision. This rule fires
/// only for types whose message is provably uninformative - a fixed string
/// naming no cause - so it escalates nothing that was ever a choice.
///
/// Note-only for WebException: reading the body needs two `use` bindings
/// placed inside the handler, and `Response` can be null, which is why the
/// idiomatic handler guards `when wex.Response <> null`. A fix IS offered
/// for ReflectionTypeLoadException, where the replacement is a single
/// type-preserving expression - and it filters nulls, because on .NET
/// Framework the elements of LoaderExceptions genuinely can be null.
module FSharp.Refactor.ExceptionDetail

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `.Message` / `.ToString()` site: where the information is
        /// thrown away, which is what the reader needs to be shown.
        Range: range
        ExceptionType: string
        /// The member carrying the real diagnosis.
        Carrier: string
        Advice: string
        Fix: (range * string * string) option
        /// The other repair, when the handler throws the partial result away:
        /// carry on with the types that DID load. Offered only where the try
        /// body is a GetTypes() call, so both branches are provably Type[].
        AlternativeFix: (range * string * string) option
    }

/// The types worth reporting, and where their diagnosis actually lives. A
/// table on purpose: AggregateException (InnerExceptions), SqlException
/// (Errors/Number) and FileNotFoundException (FusionLog) slot straight in
/// once each has a real site to verify against.
let private carriers =
    Map.ofList
        [ "ReflectionTypeLoadException",
          ("System.Reflection.ReflectionTypeLoadException",
           [ "Types"; "LoaderExceptions" ],
           "A ReflectionTypeLoadException's .Message is a fixed string naming no cause - reach for Types, which already holds the types that DID load. .NET loads every referenced assembly, so what failed is routinely a dependency this code never uses - a localization satellite, an optional plugin - and Types carries nulls where those would be. Filter them and carry on; LoaderExceptions is for when the failure genuinely has to be reported.")

          "WebException",
          ("System.Net.WebException",
           [ "Response" ],
           "A WebException's .Message never carries the server's error body - that is only in Response.GetResponseStream(). Read it with a StreamReader inside the handler, guarded by a Response null check, which is how the idiomatic handler spells it.") ]

/// `:? T as name` - the type tested for, and the name it binds.
[<TailCall>]
let rec private typedHandler (p: SynPat) =
    match p with
    | SynPat.Paren(pat = inner) -> typedHandler inner
    | SynPat.As(
        lhsPat = SynPat.IsInst(SynType.LongIdent(SynLongIdent(id = ids)), _)
        rhsPat = SynPat.Named(ident = SynIdent(ident = bound))) when not ids.IsEmpty -> ValueSome(List.last ids, bound)
    | _ -> ValueNone

/// `<something>.GetTypes()` - the call whose partial result is worth keeping.
let private getTypesIdent (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f) ->
        match f with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty && (List.last ids).idText = "GetTypes" ->
            ValueSome(List.last ids)
        | _ -> ValueNone
    | _ -> ValueNone

/// `reraise ()` or `raise <the handler's own binder>` - throwing away what
/// already loaded. NOT `raise (Wrap("...", e))`: a deliberate wrap changes
/// the thrown type, and a carry-on in its place would silently drop it.
let private isRethrow (bound: string) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident f; argExpr = arg) ->
        match f.idText, stripParens arg with
        | "reraise", UnitConst -> true
        | "raise", SynExpr.Ident raised -> raised.idText = bound
        | _ -> false
    | _ -> false

/// The expressions a handler body can EVALUATE TO: the tail of its
/// statement chain, through parentheses, a let's body, both branches of
/// an if/else and every arm of a match. Only a rethrow in one of these can
/// be replaced by a value - `if strict then reraise ()` followed by more
/// statements is a unit `if`, and a Type[] in its branch is FS0001.
let rec private tailExprs (e: SynExpr) : SynExpr list =
    match e with
    | SynExpr.Sequential(expr2 = e2) -> tailExprs e2
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> tailExprs inner
    | LetOrUseE lou -> tailExprs lou.Body
    | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some els) -> tailExprs t @ tailExprs els
    | SynExpr.Match(clauses = cs) -> cs |> List.collect (fun (SynMatchClause(resultExpr = r)) -> tailExprs r)
    | _ -> [ e ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the entity behind the tested type name, so a user type of the same
        // short name never matches
        let entityFullName (id: Ident) =
            try
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpEntity as entity -> entity.TryFullName |> Option.defaultValue ""
                    | _ -> ""
                | None -> ""
            with _ -> // an unresolvable type is not one of ours; fsharpanalyzer: ignore-line FR0055
                ""

        // Ranges of try/with expressions nested INSIDE a clause. A nested
        // handler is free to bind the same name to a different exception, and
        // a fix aimed at that read would rewrite `e.Message` into
        // `e.LoaderExceptions ...` for a type that has no such member - a fix
        // that does not compile, which is the one outcome never acceptable.
        let nestedTryRanges (outer: range) =
            index.Exprs
            |> Array.choose (fun (_, inner) ->
                match inner with
                | SynExpr.TryWith _ when Range.rangeContainsRange outer inner.Range -> Some inner.Range
                | _ -> None)

        // Ranges of `$"..."` literals inside a clause. A `.Message` in a
        // hole is a read like any other, but the replacement carries a
        // quoted `"; "`, which a single-quote interpolated string may not
        // hold inside a hole (FS3373) - such a read is reported, never fixed.
        let interpolatedRanges (outer: range) =
            index.Exprs
            |> Array.choose (fun (_, inner) ->
                match inner with
                | SynExpr.InterpolatedString(range = r) when Range.rangeContainsRange outer r -> Some r
                | _ -> None)

        // the type that declares a called member
        let entityMemberOwner (id: Ident) =
            try
                let r = id.idRange
                let lineText = source.GetLineString(r.EndLine - 1)

                match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as m -> OptionModule.enclosingFullName m
                    | _ -> ""
                | None -> ""
            with _ -> // fsharpanalyzer: ignore-line FR0055
                ""

        // Every `<name>.<member>` read inside a range. BOTH spellings: with a
        // plain identifier receiver F# parses `e.Message` as a LongIdent of
        // [e; Message], and only a non-trivial receiver produces a DotGet.
        // Matching just the latter finds nothing, which is exactly what the
        // first version of this rule did.
        let readsIn (name: string) (body: range) =
            index.Exprs
            |> Array.choose (fun (_, inner) ->
                if Range.rangeContainsRange body inner.Range then
                    match inner with
                    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                        ids.Length >= 2 && (List.head ids).idText = name
                        ->
                        // the DIRECT member: `e.LoaderExceptions.Length` counts
                        // as a LoaderExceptions read, not a Length one. The flag
                        // says whether the chain STOPS there: the range of
                        // `e.Message.Length` covers the whole chain, so replacing
                        // it would drop the `.Length` and the result would not
                        // compile - such a read may be reported but never fixed.
                        Some((List.item 1 ids).idText, inner.Range, ids.Length = 2)
                    | SynExpr.DotGet(expr = SynExpr.Ident receiver; longDotId = SynLongIdent(id = ids)) when
                        receiver.idText = name && not ids.IsEmpty
                        ->
                        Some((List.head ids).idText, inner.Range, ids.Length = 1)
                    | _ -> None
                else
                    None)

        [ for _, e in index.Exprs do
              match e with
              | SynExpr.TryWith(tryExpr = tried; withCases = cases) ->
                  for SynMatchClause(pat = p; resultExpr = body; range = clauseRange) in cases do
                      match typedHandler p with
                      | ValueSome(typeId, bound) ->
                          match Map.tryFind typeId.idText carriers with
                          | Some(fullName, memberNames, advice) when entityFullName typeId = fullName ->
                              // the whole clause, guard included - a handler
                              // that tests `wex.Response` in its `when` has
                              // already shown it knows where the body is
                              let nested = nestedTryRanges clauseRange

                              let reads =
                                  readsIn bound.idText clauseRange
                                  |> Array.filter (fun (_, r, _) ->
                                      not (nested |> Array.exists (fun n -> Range.rangeContainsRange n r)))

                              // ANY of them is awareness: a handler reading
                              // LoaderExceptions to report the failure is as
                              // informed as one reading Types to carry on
                              let mentionsCarrier =
                                  reads |> Array.exists (fun (n, _, _) -> List.contains n memberNames)

                              let carrier = List.head memberNames

                              // `ToString()` parses as a DotGet of ToString
                              // under the unit application, so both spellings
                              // land here
                              let thrownAway =
                                  reads |> Array.tryFind (fun (n, _, _) -> n = "Message" || n = "ToString")

                              // only a read that ENDS at .Message, outside any
                              // `$"..."` hole, can be rewritten in place; a
                              // longer chain or an interpolated one is
                              // reported and left alone
                              let interpolated = interpolatedRanges clauseRange

                              let fixable =
                                  reads
                                  |> Array.tryFind (fun (n, r, exact) ->
                                      n = "Message"
                                      && exact
                                      && not (interpolated |> Array.exists (fun i -> Range.rangeContainsRange i r)))

                              match mentionsCarrier, thrownAway with
                              | false, Some(_, r, _) ->
                                  yield
                                      { Range = r
                                        ExceptionType = typeId.idText
                                        Carrier = carrier
                                        Advice = advice
                                        Fix =
                                          // one type-preserving expression, and
                                          // only for the shape that has one
                                          match fixable with
                                          | Some(_, fixRange, _) when typeId.idText = "ReflectionTypeLoadException" ->
                                              Some(
                                                  fixRange,
                                                  textOfRange source fixRange,
                                                  "("
                                                  + bound.idText
                                                  + ".LoaderExceptions |> Seq.filter (isNull >> not) |> Seq.map (fun x -> x.Message) |> String.concat \"; \")"
                                              )
                                          | _ -> None
                                        AlternativeFix =
                                          // the partial result is only worth
                                          // keeping when the call that failed
                                          // was GetTypes, which is what makes
                                          // both branches Type[]
                                          if
                                              typeId.idText = "ReflectionTypeLoadException"
                                              && (match getTypesIdent (stripParens tried) with
                                                  | ValueSome id ->
                                                      // Assembly.GetTypes, not a
                                                      // user method of that name:
                                                      // the fix only typechecks
                                                      // because the result is
                                                      // Type[]
                                                      (entityMemberOwner id).StartsWith "System.Reflection.Assembly"
                                                  | ValueNone -> false)
                                          then
                                              // only a rethrow the handler EVALUATES
                                              // TO: the replacement is a Type[], so
                                              // a statement-position `if strict then
                                              // reraise ()` mid-body stays as it is
                                              tailExprs body
                                              |> List.tryPick (fun inner ->
                                                  if
                                                      isRethrow bound.idText inner
                                                      // a nested handler's rethrow
                                                      // belongs to ITS exception,
                                                      // not ours
                                                      && not (
                                                          nested
                                                          |> Array.exists (fun n ->
                                                              Range.rangeContainsRange n inner.Range)
                                                      )
                                                  then
                                                      // A TRAILING comment is only
                                                      // safe when the rethrow ends
                                                      // its line. In `if c then
                                                      // reraise() else fallback`
                                                      // it would comment the `else`
                                                      // out, which compiles as
                                                      // something else entirely or
                                                      // not at all.
                                                      let endsTheLine =
                                                          try
                                                              let line = source.GetLineString(inner.Range.EndLine - 1)

                                                              inner.Range.EndColumn >= line.Length
                                                              || System.String.IsNullOrWhiteSpace(
                                                                  line.Substring inner.Range.EndColumn
                                                              )
                                                          with _ -> // unknown reads as unsafe; fsharpanalyzer: ignore-line FR0055
                                                              false

                                                      Some(
                                                          inner.Range,
                                                          textOfRange source inner.Range,
                                                          "(let loaded = (if isNull "
                                                          + bound.idText
                                                          + ".Types then [||] else "
                                                          + bound.idText
                                                          + ".Types |> Array.filter (isNull >> not)) in if Array.isEmpty loaded then reraise () else loaded)"
                                                          + (if endsTheLine then
                                                                 " // TODO: log "
                                                                 + bound.idText
                                                                 + ".LoaderExceptions as a warning - these did not load"
                                                             else
                                                                 "")
                                                      )
                                                  else
                                                      None)
                                          else
                                              None }
                              | _ -> ()
                          | _ -> ()
                      | ValueNone -> ()
              | _ -> () ]
