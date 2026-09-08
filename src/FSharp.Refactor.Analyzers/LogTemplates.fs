/// FR0124: structured-log templates that lie (notes, correctness).
///
///     logger.LogInformation("user {User} did {Action}", user)
///                                       // 2 placeholders, 1 argument
///     logger.LogError($"failed for {user}")
///                                       // interpolation destroys the
///                                       // template: every message is a
///                                       // distinct event to the sink
///     logger.LogWarning("{Id} then {Id} again", a, b)
///                                       // duplicate placeholder name
///
/// The template sibling of FR0048 (String.Format). Placeholder syntax:
/// `{Name}`, `{@Name}`, `{$Name}`, `{Name:format}`, `{Name,align}`;
/// `{{`/`}}` are literal braces. A leading exception argument (FR0120's
/// output included) is skipped — the template is the first string
/// literal. Typed-gated to Microsoft.Extensions.Logging and Serilog.
///
/// Logary fills placeholders by NAME along a pipeline:
///
///     Message.eventInfo "Executing {sql}" |> Message.setField "sql" q |> writeLog
///
/// so a placeholder no `setField` of the same chain fills is reported, and
/// an interpolated template is the same mistake as above. Chains that fill
/// no field at all are left alone: the message may be filled by a helper.
module FSharp.Refactor.LogTemplates

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type TemplateProblem =
    | CountMismatch of placeholders: int * arguments: int
    | DuplicateName of name: string
    | Interpolated
    /// Logary: placeholders no `Message.setField` in the pipeline fills.
    | MissingFields of names: string list

type Suggestion =
    { Range: range
      Problem: TemplateProblem
      LogMethod: string }

/// Microsoft.Extensions.Logging's extension methods, plus the raw
/// `Log(LogLevel, ...)` they wrap.
let private logMethods =
    set
        [ "LogTrace"
          "LogDebug"
          "LogInformation"
          "LogWarning"
          "LogError"
          "LogCritical"
          "Log" ]

/// Serilog's static `Log.X` and `ILogger.X` — the same template syntax.
let private serilogMethods =
    set [ "Verbose"; "Debug"; "Information"; "Warning"; "Error"; "Fatal" ]

/// A template spelled as `"..." + "..."` chains: the pieces, joined — or
/// None when any operand is not a literal.
let rec private literalChain (e: SynExpr) : string option =
    match e with
    | SynExpr.Paren(expr = inner) -> literalChain inner
    | SynExpr.Const(SynConst.String(text, _, _), _) -> Some text
    | SynExpr.App(
        funcExpr = SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ op ])); argExpr = l)
        argExpr = r) when op.idText = "op_Addition" ->
        match literalChain l, literalChain r with
        | Some a, Some b -> Some(a + b)
        | _ -> None
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SynExpr.Ident op; argExpr = l); argExpr = r) when
        op.idText = "op_Addition"
        ->
        match literalChain l, literalChain r with
        | Some a, Some b -> Some(a + b)
        | _ -> None
    | _ -> None

/// Placeholder names of a message template, `{{`-escapes skipped.
let internal placeholdersOf (template: string) =
    let names = ResizeArray<string>()
    let mutable i = 0

    while i < template.Length do
        if i + 1 < template.Length && template.[i] = '{' && template.[i + 1] = '{' then
            i <- i + 2
        elif template.[i] = '{' then
            let close = template.IndexOf('}', i + 1)

            if close > i then
                let raw = template.Substring(i + 1, close - i - 1)
                let name = raw.TrimStart('@', '$')

                let name =
                    match name.IndexOfAny [| ':'; ',' |] with
                    | -1 -> name
                    | cut -> name.Substring(0, cut)

                if name.Length > 0 then
                    names.Add name

                i <- close + 1
            else
                i <- template.Length
        else
            i <- i + 1

    List.ofSeq names

[<return: Struct>]
let private (|CallIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // the library the method belongs to — Microsoft.Extensions.Logging
        // or Serilog — via the typed check; a user's own `Log.Information`
        // is neither
        let loggerFamily (logId: Ident) =
            let r = logId.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ logId.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.bind (fun n ->
                            if n.StartsWith "Microsoft.Extensions.Logging" then
                                Some "MEL"
                            elif n.StartsWith "Serilog" then
                                Some "Serilog"
                            else
                                None)
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         None)
                | _ -> None
            | None -> None

        let isLoggerExtension (logId: Ident) =
            match loggerFamily logId with
            | Some "MEL" -> logMethods.Contains logId.idText
            | Some "Serilog" -> serilogMethods.Contains logId.idText
            | _ -> false

        // ---- Logary: `Message.eventX "..{name}.." |> Message.setField "name" v |> ...` ----
        //
        // the template's placeholders are filled by name, by setField
        // stages of the same pipeline; a placeholder no stage fills reaches
        // the sink as literal braces. Only pipelines that fill at least one
        // field are judged: a message handed to a helper may be filled there
        let isPipe (e: SynExpr) =
            match e with
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) ->
                op.idText = "op_PipeRight"
            | _ -> false

        let rec stages (e: SynExpr) =
            match e with
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)
                argExpr = right) when op.idText = "op_PipeRight" -> stages left @ [ right ]
            | SynExpr.Paren(expr = inner) -> stages inner
            | other -> [ other ]

        let logaryEvent (e: SynExpr) =
            match e with
            | SynExpr.App(
                isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                ids.Length >= 2
                && ids.[ids.Length - 2].idText = "Message"
                && (List.last ids).idText.StartsWith "event"
                ->
                Some(List.last ids, stripParens arg)
            | _ -> None

        let setFieldName (e: SynExpr) =
            match e with
            | SynExpr.App(
                funcExpr = SynExpr.App(
                    funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                    argExpr = SynExpr.Const(SynConst.String(name, _, _), _))) when
                ids.Length >= 2
                && ((List.last ids).idText = "setField" || (List.last ids).idText = "setFieldValue")
                ->
                Some name
            | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
                ids.Length >= 2
                && ((List.last ids).idText = "setField" || (List.last ids).idText = "setFieldValue")
                ->
                match stripParens arg with
                | SynExpr.Const(SynConst.String(name, _, _), _) -> Some name
                | SynExpr.Tuple(exprs = SynExpr.Const(SynConst.String(name, _, _), _) :: _) -> Some name
                | _ -> None
            | _ -> None

        // a field-setting stage whose names this rule cannot read:
        // `setFields`, `setFieldsFromObject`, `setFieldFromObject`,
        // `addFields`, `setContext`, or a `setField` with a computed name
        let fillsUnreadably (e: SynExpr) =
            let rec headName (e: SynExpr) =
                match e with
                | SynExpr.App(funcExpr = f) -> headName f
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when ids.Length >= 2 ->
                    Some (List.last ids).idText
                | _ -> None

            match headName e with
            | Some name ->
                (name.StartsWith "setField"
                 || name.StartsWith "addField"
                 || name.StartsWith "setContext"
                 || name.StartsWith "addContext")
                && (setFieldName e).IsNone
            | None -> false

        let isLogary (logId: Ident) =
            let r = logId.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ logId.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpMemberOrFunctionOrValue as mfv ->
                    (try
                        mfv.DeclaringEntity
                        |> Option.bind (fun e -> e.TryFullName)
                        |> Option.exists (fun n -> n.StartsWith "Logary")
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         false)
                | _ -> false
            | None -> false

        let logary =
            [ for path, expr in index.Exprs do
                  // the outermost pipe of its chain only
                  let outermost =
                      isPipe expr
                      && not (
                          path
                          |> List.exists (fun node ->
                              match node with
                              | SyntaxNode.SynExpr(SynExpr.App(isInfix = true; funcExpr = SingleIdent op)) ->
                                  op.idText = "op_PipeRight"
                              | SyntaxNode.SynExpr(SynExpr.Paren _) -> false
                              | SyntaxNode.SynExpr(SynExpr.App(
                                  isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op))) ->
                                  op.idText = "op_PipeRight"
                              | _ -> false)
                      )

                  if outermost then
                      let chain = stages expr

                      // the event stage: `Message.eventX "..."` applied, or
                      // `"..." |> Message.eventX` point-free
                      let event =
                          chain
                          |> List.tryPick logaryEvent
                          |> Option.orElse (
                              match chain with
                              | template :: SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) :: _ when
                                  ids.Length >= 2
                                  && ids.[ids.Length - 2].idText = "Message"
                                  && (List.last ids).idText.StartsWith "event"
                                  ->
                                  Some(List.last ids, stripParens template)
                              | _ -> None
                          )

                      match event with
                      | Some(eventId, template) when isLogary eventId ->
                          let filled = chain |> List.choose setFieldName |> Set.ofList
                          let unreadable = chain |> List.exists fillsUnreadably

                          match template with
                          | SynExpr.InterpolatedString(contents = parts; range = r) when
                              parts
                              |> List.exists (fun p ->
                                  match p with
                                  | SynInterpolatedStringPart.FillExpr _ -> true
                                  | SynInterpolatedStringPart.String _ -> false)
                              ->
                              { Range = r
                                Problem = TemplateProblem.Interpolated
                                LogMethod = eventId.idText }
                          | SynExpr.Const(SynConst.String(text, _, _), r) when not (filled.IsEmpty || unreadable) ->
                              let names = placeholdersOf text

                              let missing =
                                  names |> List.distinct |> List.filter (fun n -> not (filled.Contains n))

                              if not missing.IsEmpty then
                                  { Range = r
                                    Problem = TemplateProblem.MissingFields missing
                                    LogMethod = eventId.idText }
                          | _ -> ()
                      | _ -> () ]

        logary
        @ [ for _, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = CallIdent logId; argExpr = SynExpr.Paren(expr = inner)) when
                    logMethods.Contains logId.idText || serilogMethods.Contains logId.idText
                    ->
                    let args =
                        match inner with
                        | SynExpr.Tuple(exprs = es) -> es
                        | single -> [ single ]

                    // the template is the first STRING argument — a literal, a
                    // `"..." + "..."` chain of literals, or an interpolation;
                    // anything before it (the exception, the level) is
                    // skipped, anything after it feeds the placeholders
                    let templateIndex =
                        args
                        |> List.tryFindIndex (fun a ->
                            match a with
                            | SynExpr.Const(SynConst.String _, _)
                            | SynExpr.InterpolatedString _ -> true
                            | other -> (literalChain other).IsSome)

                    // a trailing array LITERAL is the params array spelled
                    // out: its elements are the arguments
                    let trailingCount (trailing: SynExpr list) =
                        match trailing with
                        | [ SynExpr.ArrayOrList(exprs = es) ] -> Some es.Length
                        | [ SynExpr.ArrayOrListComputed(expr = SynExpr.Sequential _ as seq) ] ->
                            let rec count (e: SynExpr) =
                                match e with
                                | SynExpr.Sequential(expr1 = a; expr2 = b) -> count a + count b
                                | _ -> 1

                            Some(count seq)
                        | [ SynExpr.ArrayOrListComputed(expr = SynExpr.Const(SynConst.Unit, _)) ] -> Some 0
                        | [ SynExpr.ArrayOrListComputed(expr = single) ] ->
                            match single with
                            | SynExpr.ForEach _
                            | SynExpr.For _
                            | SynExpr.YieldOrReturn _
                            | SynExpr.YieldOrReturnFrom _ -> None
                            | _ -> Some 1
                        | _ -> Some trailing.Length

                    // one trailing IDENT argument may be the params ARRAY
                    // passed whole — its element count is invisible here, so
                    // any arity claim would be a guess
                    let isParamsArrayPassThrough (trailing: SynExpr list) =
                        match trailing with
                        | [ SynExpr.Ident argId ] ->
                            let r = argId.idRange
                            let lineText = source.GetLineString(r.EndLine - 1)

                            (match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ argId.idText ]) with
                             | Some symbolUse ->
                                 match symbolUse.Symbol with
                                 | :? FSharpMemberOrFunctionOrValue as v ->
                                     (try
                                         let t = v.FullType.Format symbolUse.DisplayContext
                                         t.EndsWith "[]" || t.EndsWith "array"
                                      with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                          true)
                                 | _ -> false
                             | None -> false)
                        | _ -> false

                    match templateIndex with
                    | Some ti when isLoggerExtension logId ->
                        match List.item ti args with
                        | SynExpr.InterpolatedString(contents = parts; range = r) when
                            parts
                            |> List.exists (fun p ->
                                match p with
                                | SynInterpolatedStringPart.FillExpr _ -> true
                                | SynInterpolatedStringPart.String _ -> false)
                            ->
                            // hole-free $"..." compiles to a constant — only
                            // actual interpolation destroys the template
                            { Range = r
                              Problem = TemplateProblem.Interpolated
                              LogMethod = logId.idText }
                        | templateExpr ->
                            let template =
                                match templateExpr with
                                | SynExpr.Const(SynConst.String(template, _, _), _) -> Some template
                                | other -> literalChain other

                            match template with
                            | Some template ->
                                let r = templateExpr.Range
                                let names = placeholdersOf template
                                let trailing = List.skip (ti + 1) args

                                let duplicate =
                                    names
                                    |> List.groupBy id
                                    |> List.tryPick (fun (name, hits) -> if hits.Length > 1 then Some name else None)

                                match duplicate, trailingCount trailing with
                                | Some name, _ ->
                                    { Range = r
                                      Problem = TemplateProblem.DuplicateName name
                                      LogMethod = logId.idText }
                                | None, Some argCount ->
                                    if names.Length <> argCount && not (isParamsArrayPassThrough trailing) then
                                        { Range = r
                                          Problem = TemplateProblem.CountMismatch(names.Length, argCount)
                                          LogMethod = logId.idText }
                                | None, None -> ()
                            | None -> ()
                    | _ -> ()
                | _ -> () ]
