/// Diagnostic (performance): a singleton append to an accumulator in a
/// RECURSIVE call — FR0051's blind spot, with no `<-` and no loop.
///
///     let rec collect acc = function
///         | [] -> acc
///         | x :: rest when keep x -> collect (acc @ [x]) rest   // O(n²)
///         | _ :: rest -> collect acc rest
///
/// `acc @ [x]` copies the whole accumulator on every step. Ironically this
/// is the shape LLMs produce MORE when told to avoid mutation. Advice
/// only, because the right repair varies: cons and reverse once
/// (`collect (x :: acc) rest` … `| [] -> List.rev acc`), or an array /
/// ResizeArray when the result is consumed positionally — the base case
/// changes either way.
///
/// Only a SINGLETON literal appended in a self-call argument counts: a
/// general `a @ b` merge runs once per call over |a|, which may be exactly
/// what the author wants.
module FSharp.Refactor.RecursiveAppend

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// The recursive function's name, for the message.
        FunctionName: string
        /// The accumulator parameter's name, for the message.
        AccumulatorName: string
    }

/// A one-element list or array literal.
let private isSingletonLiteral (e: SynExpr) =
    match stripParens e with
    | SynExpr.ArrayOrList(exprs = [ _ ]) -> true
    | SynExpr.ArrayOrListComputed(expr = inner) ->
        match inner with
        | SynExpr.Sequential _ -> false
        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op)) when op.idText = "op_Range" -> false
        | _ -> true
    | _ -> false

/// `p @ [x]` / `List.append p [x]` / `Array.append p [|x|]` where p is one
/// of `paramNames` — the appended-to parameter.
[<return: Struct>]
let private (|SingletonAppendTo|_|) (paramNames: Set<string>) (e: SynExpr) =
    match stripParens e with
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent op; argExpr = SynExpr.Ident p); argExpr = appended) when
        op.idText = "op_Append"
        && paramNames.Contains p.idText
        && isSingletonLiteral appended
        ->
        ValueSome p
    | SynExpr.App(
        funcExpr = SynExpr.App(
            funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ m; f ])); argExpr = SynExpr.Ident p)
        argExpr = appended) when
        (m.idText = "List" || m.idText = "Array")
        && f.idText = "append"
        && paramNames.Contains p.idText
        && isSingletonLiteral appended
        ->
        ValueSome p
    | _ -> ValueNone

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree

    // (name, parameter names, body range) of every recursive binding
    let recBindings =
        let ofBindings isRec bindings =
            if isRec then
                bindings
                |> List.choose (fun (SynBinding(headPat = headPat; expr = body)) ->
                    match headPat with
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ f ]); argPats = SynArgPats.Pats args) ->
                        let parameters = args |> List.collect patBoundNames |> Set.ofList
                        Some(f.idText, parameters, body.Range)
                    | _ -> None)
            else
                []

        [
            yield!
                index.Decls
                |> Array.toList
                |> List.collect (fun (_, decl) ->
                    match decl with
                    | SynModuleDecl.Let(isRecursive = isRec; bindings = bindings) -> ofBindings isRec bindings
                    | _ -> [])
            yield!
                index.Exprs
                |> Array.toList
                |> List.collect (fun (_, e) ->
                    match e with
                    | LetOrUseE lou when lou.IsRecursive && not lou.IsBang -> ofBindings true lou.Bindings
                    | _ -> [])
        ]

    let suggestions: Suggestion list =
        [
            for name, parameters, bodyRange in recBindings do
                if not parameters.IsEmpty then
                    // self-call application spines inside the body whose arguments
                    // include a singleton append to a parameter
                    for _, e in index.Exprs do
                        match e with
                        | SynExpr.App(isInfix = false; argExpr = SingletonAppendTo parameters accParam) when
                            Range.rangeContainsRange bodyRange e.Range
                            ->
                            // walk to the spine head: is this an application of the
                            // recursive function itself?
                            let rec headOf (f: SynExpr) =
                                match f with
                                | SynExpr.App(isInfix = false; funcExpr = inner) -> headOf inner
                                | SynExpr.Ident id -> Some id
                                | _ -> None

                            match e with
                            | SynExpr.App(funcExpr = f) ->
                                match headOf f with
                                | Some head when head.idText = name ->
                                    {
                                        Range = e.Range
                                        FunctionName = name
                                        AccumulatorName = accParam.idText
                                    }
                                | _ -> ()
                            | _ -> ()
                        | _ -> ()
        ]

    suggestions
