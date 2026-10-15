/// FR0182 (idiom, fix): a local binding named `id` hides FSharp.Core's
/// identity function for the rest of its scope:
///
///     match tokens.TryGetValue text with      match tokens.TryGetValue text with
///     | true, id -> id                        | true, pid -> pid
///     | _ -> failwith "missing"               | _ -> failwith "missing"
///
/// Only the binding just written: one bound in an expression (a match or
/// `function` pattern, a `let`/`use`/`let!`, a lambda or `for` variable, a
/// local function's parameter) and read exactly once. A name read in
/// several places is settled code, and renaming it is churn; a module
/// value, a member, a constructor's or a module function's parameter is a
/// name callers see, and so is the parameter of a lambda a module-level or
/// member binding is (`let f = fun id -> ...` compiles to a method). A
/// binding that is itself a function (`let id = fun x -> x`) is the
/// identity on purpose and stays. An or-pattern binding the name in each
/// branch reads as more than one occurrence and stays too.
///
/// The new name is `pid`, and only where nothing in the binding's scope
/// spells `pid` already, so no other `pid` is shadowed or captured; a
/// `let`'s right-hand side is outside that scope unless the `let` is
/// recursive. A read through `nameof` keeps the rule quiet, since the
/// rename would change the string.
module FSharp.Refactor.ShadowedId

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// The new name, when one is free in the scope.
        NewName: string option
        /// The definition and the one read.
        Edits: (range * string * string) list
    }

[<Literal>]
let private Shadowed = "id"

[<Literal>]
let private Replacement = "pid"

let private nameofBeforeRegex = Regex @"\bnameof\s*\(?\s*$"

/// The identifiers a pattern binds under the name, with their ranges.
[<TailCall>]
let rec private bindersLoop (acc: Ident list) (pending: SynPat list) =
    match pending with
    | [] -> acc
    | p :: rest ->
        let acc, next =
            match p with
            | SynPat.Named(ident = SynIdent(ident = id)) when id.idText = Shadowed -> id :: acc, rest
            | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) when
                id.idText = Shadowed
                ->
                id :: acc, rest
            | SynPat.Typed(pat = inner)
            | SynPat.Attrib(pat = inner)
            | SynPat.Paren(inner, _) -> acc, inner :: rest
            | SynPat.Tuple(elementPats = ps)
            | SynPat.ArrayOrList(elementPats = ps)
            | SynPat.Ands(pats = ps) -> acc, ps @ rest
            | SynPat.As(lhsPat = l; rhsPat = r)
            | SynPat.Or(lhsPat = l; rhsPat = r)
            | SynPat.ListCons(lhsPat = l; rhsPat = r) -> acc, l :: r :: rest
            | SynPat.Record(fieldPats = fields) ->
                acc, (fields |> List.map (fun (f: NamePatPairField) -> f.Pattern)) @ rest
            | SynPat.LongIdent(argPats = SynArgPats.Pats ps) -> acc, ps @ rest
            | SynPat.LongIdent(argPats = SynArgPats.NamePatPairs(pats = ps)) ->
                acc, (ps |> List.map (fun (f: NamePatPairField) -> f.Pattern)) @ rest
            | _ -> acc, rest

        bindersLoop acc next

/// Where a pattern the index lists binds its names, as the ranges a new
/// name must be free in: the match clause or expression it sits in; for a
/// `let` value, every head pattern of that `let` (a sibling may bind the new
/// name) and the body, but not a right-hand side the name does not reach;
/// for a local function's parameter, the whole `let`. A pattern of a
/// module-level or member binding, or of a constructor, has none: its
/// names are seen by callers.
[<TailCall>]
let rec private patternScope (path: SyntaxNode list) =
    match path with
    | SyntaxNode.SynPat _ :: rest -> patternScope rest
    // the clause's result is in scope too: a lambda's pattern parameter
    // (`fun (KeyValue(k, id)) -> ...`) is parsed as a match clause whose
    // range is the pattern alone, the lambda's body its result
    | SyntaxNode.SynMatchClause(SynMatchClause(resultExpr = result) as clause) :: _ ->
        ValueSome [ Range.unionRanges clause.Range result.Range ]
    | SyntaxNode.SynBinding(SynBinding(headPat = headPat)) :: SyntaxNode.SynExpr(LetOrUseE lou as e) :: _ ->
        match headPat with
        | SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)) -> ValueSome [ e.Range ]
        | _ when lou.IsRecursive -> ValueSome [ e.Range ]
        | _ -> ValueSome([ for SynBinding(headPat = p) in lou.Bindings -> p.Range ] @ [ lou.Body.Range ])
    | SyntaxNode.SynBinding _ :: SyntaxNode.SynExpr e :: _ -> ValueSome [ e.Range ]
    | SyntaxNode.SynExpr e :: _ -> ValueSome [ e.Range ]
    | _ -> ValueNone

/// Is the lambda the body of a module-level or member binding (`let f =
/// fun id -> ...`, `member _.M = fun id -> ...`)? Its parameters then
/// compile to the method's, a name callers see.
[<TailCall>]
let rec private lambdaIsSignature (path: SyntaxNode list) =
    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren _ | SynExpr.Typed _ | SynExpr.Lambda _) :: rest -> lambdaIsSignature rest
    | SyntaxNode.SynBinding _ :: SyntaxNode.SynExpr _ :: _ -> false
    | SyntaxNode.SynBinding _ :: _ -> true
    | _ -> false

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // (binder, its scope)
        let binders =
            [
                for path, p in index.Pats do
                    match p with
                    | SynPat.Named(ident = SynIdent(ident = id))
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats []) when
                        id.idText = Shadowed
                        ->
                        match patternScope path with
                        | ValueSome scope -> yield id, scope
                        | ValueNone -> ()
                    | _ -> ()

                // a lambda's parameters are not among the index's patterns
                for path, e in index.Exprs do
                    match e with
                    | SynExpr.Lambda(parsedData = Some(pats, _)) when not (lambdaIsSignature path) ->
                        for id in bindersLoop [] pats do
                            yield id, [ e.Range ]
                    | SynExpr.For(ident = id) when id.idText = Shadowed -> yield id, [ e.Range ]
                    | _ -> ()
            ]
            |> List.distinctBy (fun (id, _) -> id.idRange.StartLine, id.idRange.StartColumn)

        [
            for id, scope in binders do
                let lineText = source.GetLineString(id.idRange.EndLine - 1)

                match
                    OptionModule.symbolUseAt check (id.idRange.EndLine, id.idRange.EndColumn, lineText, [ id.idText ])
                with
                | Some symbolUse ->
                    match symbolUse.Symbol with
                    | :? FSharpMemberOrFunctionOrValue as value when
                        not value.IsModuleValueOrMember
                        && not (
                            try
                                value.FullType.IsFunctionType
                            with _ -> // an unresolved type reads as a function: stand down; fsharpanalyzer: ignore-line FR0055
                                true
                        )
                        ->
                        let uses =
                            check.GetUsesOfSymbolInFile value
                            |> Array.distinctBy (fun u -> u.Range.StartLine, u.Range.StartColumn)

                        // the binding is this symbol's occurrence at the binder (a
                        // pattern's binder is not flagged as a definition); the
                        // rest are its reads
                        let isBinder (u: FSharpSymbolUse) = Range.equals u.Range id.idRange
                        let bindsHere = uses |> Array.exists isBinder
                        let reads = uses |> Array.filter (isBinder >> not)

                        // every occurrence is the bare name on one line, and
                        // none is the argument of `nameof`
                        let editable =
                            uses
                            |> Array.forall (fun u ->
                                u.Range.StartLine = u.Range.EndLine
                                && textOfRange source u.Range = Shadowed
                                && not (
                                    nameofBeforeRegex.IsMatch(
                                        source.GetLineString(u.Range.StartLine - 1).Substring(0, u.Range.StartColumn)
                                    )
                                ))

                        // a read under an `#if` branch the parse left out is in no
                        // symbol use: a scope spanning a directive proves no
                        // single read
                        if
                            bindsHere
                            && reads.Length = 1
                            && editable
                            && not (scope |> List.exists (spansDirective source))
                        then
                            let newName =
                                if
                                    scope
                                    |> List.exists (fun r -> mentionsIdentifier (textOfRange source r) Replacement)
                                then
                                    None
                                else
                                    Some Replacement

                            {
                                Range = id.idRange
                                NewName = newName
                                Edits =
                                    match newName with
                                    | Some name -> [ for u in uses -> u.Range, Shadowed, name ]
                                    | None -> []
                            }
                    | _ -> ()
                | None -> ()
        ]
