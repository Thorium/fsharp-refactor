/// FR0158 (idiom): a `while` that walks a mutable index while a condition
/// holds is a tail-recursive local function - the `while` member of the
/// loop family FR0050 (accumulate) and FR0107 (flag) cover for `for`.
///
///     let mutable line = 0                          let rec advanceLine line =
///                                                       if line < max && blank line then advanceLine (line + 1) else line
///     while line < max && blank line do
///         line <- line + 1                          let line = advanceLine 0
///
/// and the countdown `line <- line - 1` the same way, as `retreatLine`.
/// The condition is evaluated once per step in the same order, the value
/// the loop leaves behind is the function's result, and the recursion is
/// a tail call the compiler turns back into a loop. Measured in
/// PerfClaims: level with the loop (26 against 30 ns for 37 steps); the
/// `Seq.tryFind` spelling over a range doubled the time and allocated
/// 104 bytes per call, so it is not what the rule writes.
///
/// Safety rules:
///   - `let mutable v = init` is immediately followed (blank lines aside)
///     by the `while`, in the same block
///   - the loop body is exactly `v <- v + e` or `v <- v - e`, `e` a
///     single-line expression that does not mention `v`
///   - `v` is assigned nowhere else: after the loop it is an immutable
///     `let`, and a later assignment would not compile
///   - `init` and `e` are single-line; the condition spans no `#if` and no
///     multi-line literal; nothing but blank lines stands between the
///     `let` and the `while`
///   - the function's name (`advanceV` / `retreatV`) is not in use
module FSharp.Refactor.IndexScan

open System
open System.Text.RegularExpressions
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The mutable's name.
        Name: string
        /// The `let mutable` through the end of the `while`.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

let private pascal (name: string) =
    if name = "" then
        name
    else
        string (Char.ToUpperInvariant name.[0]) + name.Substring 1

/// `v <- v + e` / `v <- v - e`: the operator and the step.
[<return: Struct>]
let private (|Step|_|) (name: string) (body: SynExpr) =
    let assigned =
        match body with
        | SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), rhs, _)
        | SynExpr.Set(SynExpr.Ident target, rhs, _) when target.idText = name -> ValueSome rhs
        | _ -> ValueNone

    match assigned with
    | ValueSome(SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName op; argExpr = SynExpr.Ident left)
        argExpr = step)) when
        left.idText = name
        && (op = "op_Addition" || op = "op_Subtraction")
        && isSingleLine step.Range
        ->
        ValueSome((if op = "op_Addition" then "+" else "-"), step)
    | _ -> ValueNone

/// Find index-scan loops. Parse-only.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree
    let text = source.GetSubTextString(0, source.Length)

    let mentions (name: string) (r: range) =
        Regex.IsMatch(textOfRange source r, identifierPattern name)

    // every assignment to a name in the file, by target
    let assignments =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | SynExpr.LongIdentSet(SynLongIdent(id = [ target ]), _, _)
            | SynExpr.Set(SynExpr.Ident target, _, _) -> Some(target.idText, e.Range)
            | _ -> None)

    [
        for _, expr in index.Exprs do
            match expr with
            | LetOrUseE lou when not (lou.IsRecursive || lou.IsBang || lou.IsUse) ->
                match lou.Bindings, lou.Body with
                | [ SynBinding(
                        isMutable = true
                        headPat = SynPat.Named(ident = SynIdent(ident = v))
                        expr = init
                        attributes = []) as binding ],
                  SynExpr.Sequential(expr1 = SynExpr.While(whileExpr = cond; doExpr = body) as loop; expr2 = rest) when
                    isSingleLine init.Range
                    && not (mentions v.idText init.Range)
                    && mentions v.idText cond.Range
                    // the while right after the let, blank lines apart
                    && (seq { binding.RangeOfBindingWithRhs.EndLine + 1 .. loop.Range.StartLine - 1 }
                        |> Seq.forall (fun l -> String.IsNullOrWhiteSpace(source.GetLineString(l - 1))))
                    && loop.Range.StartColumn = binding.RangeOfBindingWithRhs.StartColumn - 12
                    ->
                    match body with
                    | Step v.idText (op, step) when not (mentions v.idText step.Range) ->
                        let name = (if op = "+" then "advance" else "retreat") + pascal v.idText

                        // the mutable is assigned in the loop and nowhere else, and
                        // the function's name is free
                        let onlyThisAssignment =
                            assignments
                            |> Array.forall (fun (target, r) ->
                                target <> v.idText || Range.rangeContainsRange body.Range r)

                        let whole =
                            Range.mkRange
                                loop.Range.FileName
                                (Position.mkPos
                                    binding.RangeOfBindingWithRhs.StartLine
                                    (binding.RangeOfBindingWithRhs.StartColumn - 12))
                                loop.Range.End

                        if
                            onlyThisAssignment
                            && not (Regex.IsMatch(text, identifierPattern name))
                            && not (spansDirective source whole)
                            && Range.rangeContainsRange lou.Range rest.Range
                        then
                            let column = whole.StartColumn
                            let pad n = String(' ', n)
                            let v = v.idText
                            let stepText = textOfRange source step.Range
                            let call = $"{name} ({v} {op} {stepText})"
                            let condText = textOfRange source cond.Range

                            let shape =
                                if isSingleLine cond.Range && column + 8 + condText.Length + call.Length < 100 then
                                    Some
                                        [
                                            $"let rec {name} {v} ="
                                            $"{pad (column + 4)}if {condText} then {call} else {v}"
                                        ]
                                else
                                    reindentBlock (column + 8) cond.Range.StartColumn condText
                                    |> Option.map (fun moved ->
                                        [
                                            $"let rec {name} {v} ="
                                            $"{pad (column + 4)}if"
                                            moved
                                            $"{pad (column + 4)}then"
                                            $"{pad (column + 8)}{call}"
                                            $"{pad (column + 4)}else"
                                            $"{pad (column + 8)}{v}"
                                        ])

                            match shape with
                            | Some lines ->
                                let replacement =
                                    String.concat
                                        "\n"
                                        (lines @ [ ""; $"{pad column}let {v} = {name} {argumentText source init}" ])

                                {
                                    Name = v
                                    Range = whole
                                    OriginalText = textOfRange source whole
                                    ReplacementText = replacement
                                }
                            | None -> ()
                    | _ -> ()
                | _ -> ()
            | _ -> ()
    ]
