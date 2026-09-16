/// Refactoring: rewrite a boolean match expression as an if-else expression.
///
///     match x with            →     if x then a else b
///     | true -> a
///     | false -> b
///
/// Safety rules (a suggestion that does not appear is stable; one that appears
/// and mangles code is not):
///   - exactly two clauses, no `when` guards
///   - patterns are `true`/`false` (or one of them plus `_`)
///   - scrutinee and both branch bodies are single-line
///   - no expression is offered whose text would re-parse differently when
///     inlined into `if _ then _ else _` (lambdas, nested if/match, `let ... in`,
///     sequential `;` expressions, try-blocks, loops)
module FSharp.Refactor.MatchToIf

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole match expression, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

[<return: Struct>]
let private (|BoolPat|_|) (p: SynPat) =
    match p with
    | SynPat.Const(SynConst.Bool b, _) -> ValueSome b
    | _ -> ValueNone

[<return: Struct>]
let private (|WildPat|_|) (p: SynPat) =
    match p with
    | SynPat.Wild _ -> ValueSome()
    | _ -> ValueNone

/// Given the two clauses, return (thenBody, elseBody) if this is a boolean match
/// we can rewrite.
let private boolBranches (clauses: SynMatchClause list) : (SynExpr * SynExpr) option =
    match clauses |> List.map simpleClause with
    | [ Some(BoolPat true, thenBody); Some(BoolPat false, elseBody) ]
    | [ Some(BoolPat true, thenBody); Some(WildPat, elseBody) ]
    | [ Some(BoolPat false, elseBody); Some(BoolPat true, thenBody) ]
    | [ Some(BoolPat false, elseBody); Some(WildPat, thenBody) ] -> Some(thenBody, elseBody)
    | _ -> None

/// Find all boolean match expressions in the file that can be safely rewritten
/// as single-line if-else expressions.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.Match(expr = scrutinee; clauses = clauses; range = m) ->
                    match boolBranches clauses with
                    | Some(thenBody, elseBody) when
                        isSingleLine scrutinee.Range
                        && isSingleLine thenBody.Range
                        && isSingleLine elseBody.Range
                        && isSafeInline scrutinee
                        && isSafeInline thenBody
                        && isSafeInline elseBody
                        && not (spansDirective source m)
                        ->
                        let replacement =
                            sprintf
                                "if %s then %s else %s"
                                (textOfRange source scrutinee.Range)
                                (textOfRange source thenBody.Range)
                                (textOfRange source elseBody.Range)

                        suggestions.Add
                            {
                                Range = m
                                OriginalText = textOfRange source m
                                ReplacementText = replacement
                            }
                    | _ -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
