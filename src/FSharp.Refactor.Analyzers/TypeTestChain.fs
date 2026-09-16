/// Refactoring: the Python isinstance ladder, in F# clothing.
///
///     if (shape :? Circle) then                 match shape with
///         area (shape :?> Circle)               | :? Circle as v -> area v
///     elif (shape :? Rect) then           →     | :? Rect as v -> width v
///         width (shape :?> Rect)                | _ -> failwith "unknown"
///     else failwith "unknown"
///
/// Each branch currently tests the type twice (the `:?` and the `:?>`);
/// the match tests once and binds. It also retires the unsafe casts — an
/// `InvalidCastException` waiting for the next edit to reorder branches —
/// and reads like F#. (Still a runtime type dispatch: a DU would beat it,
/// but that is a design change, not a rewrite.)
///
/// Safety rules (all syntactic):
///   - the subject is one plain identifier, textually identical in every
///     test and every cast; at least two type-tests; a plain `else` closes
///     the chain (or its absence makes every branch unit → `| _ -> ()`)
///   - conditions are BARE type-tests — an extra `&&` would need a when
///     guard, the author's call
///   - every `:?>` of the subject inside a branch casts to THAT branch's
///     tested type: a cast to something else means the author knows more
///     than the test says, and the chain stays
///   - branch bodies are single-line (cast substitution is column-based)
///     and never assign the subject
module FSharp.Refactor.TypeTestChain

open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// `subj :? Ty` with a plain identifier subject → (subject, type text).
[<return: Struct>]
let private (|SubjectTypeTest|_|) (source: ISourceText) (e: SynExpr) =
    match stripParens e with
    | SynExpr.TypeTest(expr = SynExpr.Ident subj; targetType = ty) -> ValueSome(subj, textOfRange source ty.Range)
    | _ -> ValueNone

/// The if/elif chain: (subject, type text, body) per branch plus the final
/// else body, or None when any link breaks the shape.
[<TailCall>]
let rec private chain
    (source: ISourceText)
    (acc: (Ident * string * SynExpr) list)
    (e: SynExpr)
    : ((Ident * string * SynExpr) list * SynExpr option) option =
    match e with
    | SynExpr.IfThenElse(ifExpr = SubjectTypeTest source (subj, tyText); thenExpr = body; elseExpr = els) ->
        let acc = (subj, tyText, body) :: acc

        match els with
        | Some(SynExpr.IfThenElse _ as nested) -> chain source acc nested
        | Some final -> Some(List.rev acc, Some final)
        | None -> Some(List.rev acc, None)
    | _ -> None

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    // only the OUTERMOST if of a chain; the elifs are visited separately
    // and must not each produce a (nested, garbled) suggestion
    let isElifItself (e: SynExpr) =
        match e with
        | SynExpr.IfThenElse(trivia = trivia) -> trivia.IsElif
        | _ -> false

    for _, expr in index.Exprs do
        match expr with
        | SynExpr.IfThenElse _ when not ((isElifItself expr) || (spansDirective source expr.Range)) ->
            match chain source [] expr with
            | Some((_ :: _ :: _ as branches), finalElse) ->
                let subject = let (s, _, _) = List.head branches in s

                let sameSubject =
                    branches |> List.forall (fun (s, _, _) -> s.idText = subject.idText)

                let distinctTypes =
                    branches |> List.map (fun (_, ty, _) -> ty) |> List.distinct |> List.length = branches.Length

                let bodies =
                    branches
                    |> List.map (fun (_, _, b) -> b)
                    |> List.append (Option.toList finalElse)

                let bodiesInline =
                    bodies |> List.forall (fun b -> isSingleLine b.Range && isSafeInline b)

                // casts of the subject inside each branch, and proof that
                // each targets that branch's own type
                let castsOf (body: SynExpr) =
                    index.Exprs
                    |> Array.choose (fun (_, e) ->
                        match e with
                        | SynExpr.Downcast(expr = SynExpr.Ident castSubj; targetType = ty) when
                            castSubj.idText = subject.idText && Range.rangeContainsRange body.Range e.Range
                            ->
                            Some(e, textOfRange source ty.Range)
                        | _ -> None)

                let castsAgree =
                    branches
                    |> List.forall (fun (_, tyText, body) ->
                        castsOf body |> Array.forall (fun (_, castTy) -> castTy = tyText))

                let subjectAssigned =
                    index.Exprs
                    |> Array.exists (fun (_, e) ->
                        match e with
                        | SynExpr.LongIdentSet(SynLongIdent(id = first :: _), _, _) when
                            first.idText = subject.idText && Range.rangeContainsRange expr.Range e.Range
                            ->
                            true
                        | _ -> false)

                if
                    sameSubject
                    && distinctTypes
                    && bodiesInline
                    && castsAgree
                    && not subjectAssigned
                then
                    let wholeText = textOfRange source expr.Range

                    let binder =
                        [ "v"; $"{subject.idText}Value" ]
                        |> List.tryFind (fun name -> not (Regex.IsMatch(wholeText, @"\b" + Regex.Escape name + @"\b")))

                    match binder with
                    | Some binder ->
                        // substitute each `(subj :?> Ty)`-shaped cast (the
                        // parens included when present) with the binder,
                        // right-to-left per body
                        let substituted (body: SynExpr) =
                            let casts =
                                castsOf body
                                |> Array.map (fun (castExpr, _) ->
                                    // widen to the enclosing parens when the
                                    // cast is parenthesized
                                    index.Exprs
                                    |> Array.tryPick (fun (_, e) ->
                                        match e with
                                        | SynExpr.Paren(expr = inner) when Range.equals inner.Range castExpr.Range ->
                                            Some e.Range
                                        | _ -> None)
                                    |> Option.defaultValue castExpr.Range)

                            casts
                            |> Array.sortByDescending (fun r -> r.StartColumn)
                            |> Array.fold
                                (fun (text: string) (r: range) ->
                                    let start = r.StartColumn - body.Range.StartColumn
                                    let length = r.EndColumn - r.StartColumn
                                    text.Remove(start, length).Insert(start, binder))
                                (textOfRange source body.Range)

                        let arms =
                            branches
                            |> List.map (fun (_, tyText, body) ->
                                if castsOf body |> Array.isEmpty then
                                    $"| :? {tyText} -> {substituted body}"
                                else
                                    $"| :? {tyText} as {binder} -> {substituted body}")

                        let finalArm =
                            match finalElse with
                            | Some e -> $"| _ -> {textOfRange source e.Range}"
                            | None -> "| _ -> ()"

                        let replacement =
                            $"match {subject.idText} with " + String.concat " " arms + " " + finalArm

                        suggestions.Add
                            {
                                Range = expr.Range
                                OriginalText = wholeText
                                ReplacementText = replacement
                            }
                    | None -> ()
            | _ -> ()
        | _ -> ()

    List.ofSeq suggestions
