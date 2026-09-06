/// Refactoring: drop redundant parentheses around a single atomic argument.
///
///     List.max([4; 3])       →  List.max [4; 3]
///     String.length(s)       →  String.length s
///     f("literal")           →  f "literal"
///
/// Safety rules:
///   - the argument must be a single atom: an identifier, a dotted path, a
///     non-negative constant, or a collection literal — never a tuple (those
///     parens are a method-call argument list) and never an application
///   - the callee must be an F# function — a lowercase identifier, a core
///     Option/Result case, or a module-qualified lowercase path; method and
///     constructor calls (uppercase-final: `File.ReadAllText(path)`,
///     `StringValues("x")`) keep their parens per the F# style guide
///   - calls continued by a projection (`f(x).Length`, `f(x).[0]`) are left
///     alone — the parens make the application atomic there
module FSharp.Refactor.RedundantParens

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the parenthesized argument, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// Option/Result cases whose parenthesized payload is idiomatically bare.
let private coreCaseNames =
    set
        [ "Some"
          "ValueSome"
          "Ok"
          "Error"
          "Choice1Of2"
          "Choice2Of2"
          "Choice1Of3"
          "Choice2Of3"
          "Choice3Of3" ]

/// A callee we are confident is an F# function (or core wrapper case), not a
/// .NET method or constructor: a lowercase bare identifier, a core Option or
/// Result case, or a dotted path headed by an uppercase module whose LAST
/// segment is lowercase (module functions). Uppercase-final paths —
/// `File.ReadAllText(path)`, `StringValues("x")`, constructors — keep their
/// parens per the F# style guide for method calls.
[<return: Struct>]
let private (|FunctionCallee|_|) (e: SynExpr) =
    let lowercaseInitial (id: Ident) =
        id.idText.Length > 0
        && not (Char.IsUpper id.idText.[0])
        // op_Implicit and friends are .NET operator methods, not functions
        && not (id.idText.StartsWith "op_")

    match e with
    | SynExpr.Ident id when lowercaseInitial id || coreCaseNames.Contains id.idText -> ValueSome()
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = head :: (_ :: _ as rest))) when
        head.idText.Length > 0
        && Char.IsUpper head.idText.[0]
        && lowercaseInitial (List.last rest)
        ->
        ValueSome()
    | _ -> ValueNone

/// An argument that stays unambiguous without its parens. Shared with
/// FR0094, which applies the same test to instance method calls.
let isBareableArgument (source: ISourceText) (inner: SynExpr) =
    match inner with
    // operator references parse as idents whose range includes their own
    // parens (`(+)`), which splice fine; only a bare operator token would not
    | SynExpr.Ident _ ->
        let text = textOfRange source inner.Range

        text.StartsWith '('
        || (text.Length > 0 && (Char.IsLetter text.[0] || text.[0] = '_'))
    | SynExpr.LongIdent _ -> true
    // `m (())` passes unit as a VALUE — to a generic `'t` parameter, say;
    // bare, `m ()` is a call with no arguments, and a method with a
    // required parameter stops compiling
    | SynExpr.Const(SynConst.Unit, _) -> false
    | SynExpr.Const _ ->
        // a leading sign would re-parse as a binary operator: `f(-1)` / `f(+1)`
        let text = textOfRange source inner.Range
        not (text.StartsWith '-' || text.StartsWith '+')
    | SynExpr.ArrayOrList _
    | SynExpr.ArrayOrListComputed _ -> true
    // an interpolated string is one token to the parser, as a literal is:
    // `f ($"..")` left by a sprintf-to-interpolation rewrite (FR0042)
    | SynExpr.InterpolatedString _ -> true
    | _ -> false

/// Find single-argument calls whose parenthesized argument is a bare atom.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.App(
                    isInfix = false
                    funcExpr = (FunctionCallee as callee)
                    argExpr = (SynExpr.Paren(expr = inner; rightParenRange = Some _) as argExpr)) when
                    isSingleLine argExpr.Range && isBareableArgument source inner
                    ->
                    // `f(x).Length` needs the atomic application: skip under
                    // projections, and under the dynamic `?` for the same
                    // reason — `f(x)?y` bare would bind the argument to `?`
                    let projected =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.DotGet _) :: _
                        | SyntaxNode.SynExpr(SynExpr.DotIndexedGet _) :: _
                        | SyntaxNode.SynExpr(SynExpr.Dynamic _) :: _ -> true
                        // the `_.` shorthand lambda demands an ATOMIC body:
                        // `_.reshape([| n |])` is legal and `_.reshape [| n |]`
                        // is not, so dropping these parens turns compiling
                        // code into "Shorthand lambda syntax is only supported
                        // for atomic expressions". Found on toro, where six
                        // FR0013 fixes were applied, broke the build and were
                        // rolled back — correct, but a whole pass spent to
                        // learn what the parse tree already said
                        | SyntaxNode.SynExpr(SynExpr.DotLambda _) :: _ -> true
                        // a direct tuple element keeps its parens:
                        // `ValueSome(x), y` bare is the same parse, but the
                        // comma next to a spaced application makes the
                        // reader run the precedence table to see which side
                        // owns it
                        | SyntaxNode.SynExpr(SynExpr.Tuple _) :: _ -> true
                        | _ -> false

                    if not projected then
                        let innerText = textOfRange source inner.Range

                        let replacement =
                            // `f(x)` has no space between callee and argument
                            if callee.Range.End = argExpr.Range.Start then
                                " " + innerText
                            else
                                innerText

                        suggestions.Add
                            { Range = argExpr.Range
                              OriginalText = textOfRange source argExpr.Range
                              ReplacementText = replacement }
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
