/// Refactoring note (correctness, CA2208): the parameter name handed to an
/// argument exception must name a real parameter.
///
///     let scale (value: int) (factor: int) =
///         if factor = 0 then invalidArg "facotr" "zero factor"   // typo
///         ...
///
/// The name string drifts on renames exactly like doc comments do; a wrong
/// name sends the caller debugging the wrong argument. Covers `invalidArg`
/// and `nullArg`, plus `ArgumentException("msg", "param")`,
/// `ArgumentNullException("param")` and `ArgumentOutOfRangeException`
/// constructions inside the function.
module FSharp.Refactor.ArgNames

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The offending name literal.
        Range: range
        /// The name the code used.
        UsedName: string
        /// The enclosing function's real parameter names.
        ParameterNames: string list
    }

/// (param-name literal, its range) from an argument-exception shape.
[<return: Struct>]
let private (|ParamNameArg|_|) (e: SynExpr) =
    match e with
    // invalidArg "name" msg / nullArg "name"
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = nameArg)
        argExpr = _) when fn.idText = "invalidArg" ->
        match stripParens nameArg with
        | SynExpr.Const(SynConst.String(name, _, _), _) as c -> ValueSome(name, c.Range)
        | _ -> ValueNone
    | SynExpr.App(isInfix = false; funcExpr = SingleIdent fn; argExpr = nameArg) when fn.idText = "nullArg" ->
        match stripParens nameArg with
        | SynExpr.Const(SynConst.String(name, _, _), _) as c -> ValueSome(name, c.Range)
        | _ -> ValueNone
    // ArgumentException("msg", "name") / ArgumentNullException("name") /
    // ArgumentOutOfRangeException("name", ...)
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg)
    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) ->
        let typeName = if ids.IsEmpty then "" else (List.last ids).idText

        let nameExpr =
            match typeName, stripParens arg with
            | "ArgumentException", SynExpr.Tuple(exprs = [ _; name ]) -> Some name
            | ("ArgumentNullException" | "ArgumentOutOfRangeException"), SynExpr.Tuple(exprs = name :: _) -> Some name
            | ("ArgumentNullException" | "ArgumentOutOfRangeException"), single -> Some single
            | _ -> None

        match nameExpr |> Option.map stripParens with
        | Some(SynExpr.Const(SynConst.String(name, _, _), _) as c) -> ValueSome(name, c.Range)
        | _ -> ValueNone
    | _ -> ValueNone

/// Parameter names of a binding's head pattern.
let private paramsOf (SynBinding(headPat = headPat)) =
    match headPat with
    | SynPat.LongIdent(argPats = SynArgPats.Pats args) -> args |> List.collect patBoundNames
    | _ -> []

/// A literal that could plausibly BE a parameter name. `"--mode"` or
/// `"input file"` name a CLI flag or an external concept, not an F#
/// parameter — the drift argument does not apply to those.
let private isIdentifierShaped (name: string) =
    name.Length > 0
    && (System.Char.IsLetter name.[0] || name.[0] = '_')
    && name
       |> Seq.forall (fun c -> System.Char.IsLetterOrDigit c || c = '_' || c = '\'')

/// Find wrong argument names. `nameof` uses never match (not literals).
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    ignore source
    let index = AstIndex.ofTree parseTree
    let suggestions = ResizeArray<Suggestion>()

    // the argument-exception sites FIRST, once: they are rare, and the
    // previous shape scanned every expression per binding — O(bindings ×
    // expressions) — which put this rule at the top of the slow-analyzer
    // list for files containing no argument exception at all
    let paramNameSites =
        index.Exprs
        |> Array.choose (fun (_, e) ->
            match e with
            | ParamNameArg(used, litRange) when isIdentifierShaped used -> Some(used, litRange, e.Range)
            | _ -> None)

    let checkBinding (SynBinding(attributes = attrs; expr = body) as binding) =
        let parameters = paramsOf binding

        // a [<CustomOperation>] member's "argument" is the DSL keyword's
        // operand; its name deliberately follows the DSL, not the F# signature
        if not (hasAttributeNamed "CustomOperation" attrs || parameters.IsEmpty) then
            let names = Set.ofList parameters

            for used, litRange, siteRange in paramNameSites do
                if Range.rangeContainsRange body.Range siteRange && not (names.Contains used) then
                    suggestions.Add
                        {
                            Range = litRange
                            UsedName = used
                            ParameterNames = parameters
                        }

    if not (Array.isEmpty paramNameSites) then
        for _, decl in index.Decls do
            match decl with
            | SynModuleDecl.Let(bindings = bindings) -> bindings |> List.iter checkBinding
            | SynModuleDecl.Types(typeDefns = defns) ->
                for SynTypeDefn(typeRepr = repr; members = extra) in defns do
                    let members =
                        match repr with
                        | SynTypeDefnRepr.ObjectModel(members = ms) -> ms @ extra
                        | _ -> extra

                    // in a CE builder, name literals follow the DSL's keywords
                    // (a builder's Run validating "vpc"), not the F# signature
                    for m in (if instanceIsContract members then [] else members) do
                        match m with
                        | SynMemberDefn.Member(memberDefn = binding) -> checkBinding binding
                        | _ -> ()
            | _ -> ()

    List.ofSeq suggestions
