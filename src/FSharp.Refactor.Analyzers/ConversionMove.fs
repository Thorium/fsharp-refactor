/// Refactoring: move a List/Seq/Array conversion past the next operation in a
/// pipeline, or drop it when the operation consumes the collection.
///
///     xs |> Seq.toList |> List.map f      →  xs |> Seq.map f |> Seq.toList
///     xs |> Array.toList |> List.filter f →  xs |> Array.filter f |> Array.toList
///     xs |> Seq.toList |> List.length     →  xs |> Seq.length
///     xs |> Seq.toList |> List.iter f     →  xs |> Seq.iter f
///
/// The rewrite avoids building an intermediate collection and is
/// type-correct by construction: the conversion's input type tells us which
/// module's operation accepts the original value, and the trailing conversion
/// (or consuming operation) keeps the overall evaluation eager. Conversions
/// *toward* seq are never moved — that would turn eager code lazy — and an
/// operation is never moved INTO the List module (see worthMovingInto).
///
/// An operation that MUTATES is refused outright, and this is the rule's
/// sharpest edge rather than a footnote. `Seq.toList |> List.iter (fun k ->
/// dict[k] <- v)` materialises before the writes begin; `Seq.iter` interleaves
/// them, and where the sequence reads what the body writes the enumeration
/// throws "Collection was modified". SQLProvider lost 19 tests to exactly
/// this shape, on a sequence built from the very dictionary its body
/// assigned into. Nothing downstream can catch it either: the rewrite
/// compiles, so only a test run ever finds out.
///
/// Safety rules: both pipeline stages single-line; the conversion must be a
/// bare `Module.function`; the operation's head must be exactly the
/// conversion's target module + a whitelisted operation; argument text is
/// preserved verbatim.
module FSharp.Refactor.ConversionMove

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range spanning the conversion stage through the operation stage.
        Range: range
        OriginalText: string
        ReplacementText: string
        /// True when the conversion was dropped entirely (consuming operation).
        Eliminated: bool
    }

/// conversion function → (module whose ops accept the conversion's input,
///                        module the conversion produces)
let private conversions =
    dict
        [ "Seq.toList", ("Seq", "List")
          "List.ofSeq", ("Seq", "List")
          "Seq.toArray", ("Seq", "Array")
          "Array.ofSeq", ("Seq", "Array")
          "List.toArray", ("List", "Array")
          "Array.ofList", ("List", "Array")
          "Array.toList", ("Array", "List")
          "List.ofArray", ("Array", "List") ]

/// Operations after which the conversion is still needed (it moves). All are
/// order-preserving element transforms whose Seq/List/Array variants agree
/// once the trailing conversion forces evaluation. `groupBy` is deliberately
/// absent: Seq.groupBy yields seq-valued groups, so the element type changes.
let private movableOps =
    set
        [ "map"
          "mapi"
          "filter"
          "choose"
          "collect"
          "rev"
          "sort"
          "sortBy"
          "sortDescending"
          "sortByDescending"
          "sortWith"
          "distinct"
          "distinctBy"
          "indexed"
          "countBy" ]

/// Operations that consume the collection (the conversion is dropped). The
/// moved form may short-circuit source enumeration (exists/find/head/...),
/// which is the point of the rewrite; results are identical for pure sources.
/// `skip`/`take` are absent: their List and Seq variants throw different
/// exception types on short inputs.
let private consumingOps =
    set
        [ "length"
          "iter"
          "iteri"
          "sum"
          "sumBy"
          "average"
          "averageBy"
          "max"
          "min"
          "maxBy"
          "minBy"
          "exists"
          "forall"
          "isEmpty"
          "fold"
          "reduce"
          "contains"
          "find"
          "tryFind"
          "findIndex"
          "tryFindIndex"
          "pick"
          "tryPick"
          "head"
          "tryHead"
          "last"
          "tryLast"
          // `item` is absent: Array.item throws IndexOutOfRangeException while
          // List.item/Seq.item throw ArgumentException
          "exactlyOne"
          "tryExactlyOne" ]

/// The Array sorts are unstable while the Seq/List sorts are stable, so the
/// sort family must not be moved across an Array boundary.
let private sortFamily =
    set [ "sort"; "sortBy"; "sortDescending"; "sortByDescending"; "sortWith" ]

/// Per-operation restrictions on top of the whitelists: `collect`'s mapper
/// return type differs between modules (only Seq.collect accepts any #seq),
/// and sorting stability differs on Array.
let private opAllowedForModules (opFunc: string) (sourceModule: string) (targetModule: string) =
    if opFunc = "collect" then
        sourceModule = "Seq"
    elif sortFamily.Contains opFunc then
        sourceModule <> "Array" && targetModule <> "Array"
    else
        true

/// Is MOVING an operation into `sourceModule` actually cheaper?
///
/// Into Seq, yes: the pipeline goes lazy and the intermediate collection
/// stops existing until the trailing conversion forces it. Into Array, yes:
/// a contiguous block replaces a chain of cons cells.
///
/// Into List, no. `xs |> List.toArray |> Array.filter f` builds one array
/// and filters it in a tight loop; `xs |> List.filter f |> List.toArray`
/// allocates a cons cell per surviving element — around 32 bytes each
/// against 8 for an array slot — and then chases those pointers to build
/// the array anyway. That only breaks even if the filter discards most of
/// its input, and for the length-preserving operations (map, rev, indexed)
/// it is always a loss, so the move is not offered at all.
///
/// Into Seq, only when the operation SHRINKS its input — and this took
/// measuring, because the reasoning above was written for List and is just
/// as true here. `Seq.toList |> List.map f` → `Seq.map f |> Seq.toList`
/// runs 35% SLOWER (46k → 62k ns/op at n=1000) for 12% less allocation:
/// the intermediate list does disappear, but `Seq.toList` then builds the
/// result through an enumerator with a virtual call per element, where
/// `List.map` walked cons cells in a tight loop. With `filter` the output
/// is smaller than the input, and that saving pays for the indirection
/// (−4% time, −13% allocation); with `map`, `rev` or `indexed` there is
/// nothing to pay with. Into Array the same pair is a rout either way —
/// map −39% time and −44% allocation, filter −53% and −62% — because a
/// contiguous block replaces the cons chain rather than adding to it.
///
/// Dropping a conversion outright (a consuming operation) stays worthwhile
/// in every direction: there the intermediate really does disappear, so
/// this gate does not apply to it.
let private lengthPreserving =
    set
        [ "map"
          "mapi"
          "rev"
          "indexed"
          "sort"
          "sortBy"
          "sortDescending"
          "sortByDescending"
          "sortWith" ]

let private worthMovingInto (sourceModule: string) (operation: string) =
    match sourceModule with
    | "List" -> false
    | "Seq" -> not (lengthPreserving.Contains operation)
    | _ -> true

[<return: Struct>]
let private (|ModuleFunc|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])) -> ValueSome(m.idText, f.idText, e.Range)
    | _ -> ValueNone

/// The leading `Module.function` of a (possibly curried, non-infix)
/// application, e.g. `List.map` in `List.map f`.
[<TailCall>]
let rec private headModuleFunc (e: SynExpr) =
    match e with
    | ModuleFunc(m, f, r) -> ValueSome(m, f, r)
    | SynExpr.App(isInfix = false; funcExpr = funcExpr) -> headModuleFunc funcExpr
    | SynExpr.TypeApp(expr = inner) -> headModuleFunc inner
    | _ -> ValueNone

/// Does this text write to anything? The eager conversion this rule removes
/// is what keeps enumeration and mutation apart, so code that assigns
/// cannot have it taken away.
///
/// Read off the source text deliberately: it over-approximates, and it does
/// so in the SAFE direction — a `<-` inside a string or a comment costs a
/// fix that was available, never a rewrite that breaks at run time.
let private mutatesSomething (text: string) = text.Contains "<-"

/// The arguments of the operation that could RUN during the walk: the
/// `register` of `List.iter register`, the lambda of `List.map (fun k ->
/// ...)`. `List.length`, `List.rev` and `List.take 3` carry none, and cannot
/// write to the collection they are reading.
let private callbackArguments (opStage: SynExpr) =
    let rec arguments (e: SynExpr) =
        match e with
        | SynExpr.App(isInfix = false; funcExpr = funcExpr; argExpr = argExpr) -> argExpr :: arguments funcExpr
        | SynExpr.TypeApp(expr = inner) -> arguments inner
        | _ -> []

    arguments opStage
    |> List.filter (fun arg ->
        match stripParens arg with
        | SynExpr.Const _ -> false
        | _ -> true)

/// The identifier a pipeline source ultimately reads from: `d` in `d.Keys`,
/// `xs` in `xs |> h`, `getItems` in `getItems ()`.
[<TailCall>]
let rec private sourceRoot (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome id.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> ValueSome first.idText
    | SynExpr.DotGet(expr = inner)
    | SynExpr.Paren(expr = inner)
    | SynExpr.TypeApp(expr = inner) -> sourceRoot inner
    | PipeApp(inner, _) -> sourceRoot inner
    | SynExpr.App(funcExpr = funcExpr) -> sourceRoot funcExpr
    | _ -> ValueNone

/// Is the source collection OWNED by the function this pipeline sits in?
///
/// Under a callback, the eager copy can only matter where the callback can
/// reach the collection being read. A collection the function itself binds
/// — a local `let`, a parameter, a loop or match variable — is reachable
/// only through the function's own text, which `mutatesSomething` reads in
/// full. A module-level collection, or one captured from further out, can
/// be written by any function the callback names (SQLProvider's shape: the
/// sequence was built from a dictionary a helper assigned into), and
/// nothing in this file can tell — so those are gated out, and only those.
/// A list or array literal is already materialised and reads from nothing.
let private sourceIsOwned (path: SyntaxNode list) (sourceExpr: SynExpr) =
    match stripParens sourceExpr with
    | SynExpr.ArrayOrList _
    | SynExpr.ArrayOrListComputed _ -> true
    | _ ->
        match sourceRoot sourceExpr with
        | ValueNone -> false
        | ValueSome name ->
            let bindingNames (bindings: SynBinding list) =
                bindings
                |> List.collect (fun (SynBinding(headPat = headPat)) -> patNames headPat)

            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(LetOrUseE lou) -> bindingNames lou.Bindings |> List.contains name
                | SyntaxNode.SynBinding(SynBinding(headPat = headPat)) -> patNames headPat |> List.contains name
                | SyntaxNode.SynExpr(SynExpr.Lambda(parsedData = Some(parameters, _))) ->
                    parameters |> List.collect patNames |> List.contains name
                | SyntaxNode.SynMatchClause(SynMatchClause(pat = pat)) -> patNames pat |> List.contains name
                | SyntaxNode.SynExpr(SynExpr.ForEach(pat = pat)) -> patNames pat |> List.contains name
                | SyntaxNode.SynExpr(SynExpr.For(ident = ident)) -> ident.idText = name
                | _ -> false)

/// Could this callback write to the OWNED collection while the walk reads?
///
/// Only what runs DURING the enumeration matters. A function that assigns
/// into its array earlier and then filters it — FsRocket's checkTrooperHits
/// writes `es[ti] <- ...` in a loop and ends with `es |> Array.toList |>
/// List.filter (fun e -> ...)` — is the ordinary case, and reading the whole
/// function for `<-` refused it. So the callback is what is read:
///
///   - a lambda: its own text must not assign, and must not call a LOCAL
///     function that does (`let killTrooper ti = es[ti] <- ...` is exactly
///     the closure that can reach the collection; a module-level function
///     cannot, unless the collection is handed to it, which is the next
///     case)
///   - anything else — a named function, a partial application: it must
///     not be a local that assigns, and must not mention the collection
///     itself, since `List.iter (register es)` hands it over
let private callbackMayWrite (source: ISourceText) (path: SyntaxNode list) (sourceName: string option) (arg: SynExpr) =
    let text = textOfRange source arg.Range

    let mentions (name: string) =
        System.Text.RegularExpressions.Regex.IsMatch(text, $@"\b{System.Text.RegularExpressions.Regex.Escape name}\b")

    // local bindings on the path whose body assigns: the closures that can
    // reach a collection this function owns
    let assigningLocals =
        path
        |> List.collect (fun node ->
            match node with
            | SyntaxNode.SynExpr(LetOrUseE lou) ->
                lou.Bindings
                |> List.filter (fun binding -> mutatesSomething (textOfRange source binding.RangeOfBindingWithRhs))
                |> List.collect (fun (SynBinding(headPat = headPat)) -> patNames headPat)
            | _ -> [])

    mutatesSomething text
    || assigningLocals |> List.exists mentions
    || (match stripParens arg with
        | SynExpr.Lambda _
        | SynExpr.MatchLambda _ -> false
        | _ -> sourceName |> Option.exists mentions)

/// Is the pipeline's source ALREADY the collection the conversion
/// produces? Then the conversion is at most a copy, and moving the
/// operation in front of it trades a tight Array/List pass for a lazy Seq
/// walk: fsharplint's `identifier.idText.Split('|') |> Seq.toArray |>
/// Array.filter ..` became `.. |> Seq.filter .. |> Seq.toArray`, a
/// pessimisation on an input that was an array all along. The rule is
/// syntactic, so the shapes are read off the text: an array/list literal
/// of the target kind, a .NET method that returns an array (Split,
/// ToArray, ToCharArray, GetFiles, GetDirectories) or a List (ToList),
/// or the target module's own function feeding the conversion.
let private alreadyMaterialised (targetModule: string) (sourceExpr: SynExpr) =
    let arrayMethods =
        set [ "Split"; "ToArray"; "ToCharArray"; "GetFiles"; "GetDirectories" ]

    let listMethods = set [ "ToList" ]

    let rec calleeName (e: SynExpr) =
        match e with
        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome (List.last ids).idText
        | SynExpr.TypeApp(expr = inner) -> calleeName inner
        | _ -> ValueNone

    let producesTarget (e: SynExpr) =
        match e with
        | SynExpr.ArrayOrList(isArray = isArray)
        | SynExpr.ArrayOrListComputed(isArray = isArray) -> (if isArray then "Array" else "List") = targetModule
        | SynExpr.App(isInfix = false; funcExpr = callee) ->
            let byMethod =
                match calleeName callee with
                | ValueSome name ->
                    (targetModule = "Array" && arrayMethods.Contains name)
                    || (targetModule = "List" && listMethods.Contains name)
                | ValueNone -> false

            let byModule =
                match headModuleFunc e with
                | ValueSome(m, _, _) -> m = targetModule
                | ValueNone -> false

            byMethod || byModule
        | _ -> false

    match stripParens sourceExpr with
    // `xs |> Array.map f |> Seq.toArray |> ..`: the last stage decides
    | PipeApp(_, lastStage) -> producesTarget (stripParens lastStage)
    | e -> producesTarget e

/// Find pipeline segments `conv |> Module.op args` that can be rewritten.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | PipeApp(PipeApp(sourceExpr, (ModuleFunc(convModule, convFunc, _) as convStage)), opStage) when
                    isSingleLine convStage.Range && isSingleLine opStage.Range
                    ->
                    let convKey = $"{convModule}.{convFunc}"

                    match conversions.TryGetValue convKey with
                    | true, (sourceModule, targetModule) ->
                        match headModuleFunc opStage with
                        | ValueSome(opModule, opFunc, headRange) when opModule = targetModule ->
                            let movable = movableOps.Contains opFunc && worthMovingInto sourceModule opFunc

                            let consuming = consumingOps.Contains opFunc

                            // a callback can write while the walk reads:
                            // the collection must be the function's own,
                            // and nothing in the function may assign
                            let safeUnderCallback =
                                match callbackArguments opStage with
                                | [] -> true
                                | callbacks ->
                                    sourceIsOwned path sourceExpr
                                    && (let sourceName =
                                            match sourceRoot sourceExpr with
                                            | ValueSome name -> Some name
                                            | ValueNone -> None

                                        callbacks |> List.forall (callbackMayWrite source path sourceName >> not))

                            if
                                (movable || consuming)
                                && opAllowedForModules opFunc sourceModule targetModule
                                && safeUnderCallback
                                // a source that already IS the target kind
                                // gains nothing from a lazy detour — not
                                // even for a consuming drop, where
                                // `Seq.length` over the array would walk
                                // what `Array.length` reads in O(1)
                                && not (alreadyMaterialised targetModule sourceExpr)
                            then
                                let argsText =
                                    textOfRange
                                        source
                                        (Range.mkRange opStage.Range.FileName headRange.End opStage.Range.End)

                                let rewrittenOp = $"{sourceModule}.{opFunc}{argsText}"

                                let replacement =
                                    if consuming then
                                        rewrittenOp
                                    else
                                        // the two stages keep the layout they had: a
                                        // one-op-per-line pipeline stays that way
                                        // (fsharp.formatting's fantomas check rejected
                                        // the joined line), a one-liner stays one
                                        let glue =
                                            textOfRange
                                                source
                                                (Range.mkRange
                                                    convStage.Range.FileName
                                                    convStage.Range.End
                                                    opStage.Range.Start)

                                        let glue = if glue.Contains "|>" then glue else " |> "

                                        rewrittenOp + glue + textOfRange source convStage.Range

                                let fullRange =
                                    Range.mkRange convStage.Range.FileName convStage.Range.Start opStage.Range.End

                                suggestions.Add
                                    { Range = fullRange
                                      OriginalText = textOfRange source fullRange
                                      ReplacementText = replacement
                                      Eliminated = consuming }
                        | _ -> ()
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
