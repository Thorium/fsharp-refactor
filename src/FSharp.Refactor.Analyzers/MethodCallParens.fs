/// Refactoring: drop redundant parentheses around the single atomic argument
/// of an INSTANCE method call.
///
///     s.Contains("x")        →  s.Contains "x"
///     builder.Append(c)      →  builder.Append c
///     xs.Head.Trim(' ')      →  xs.Head.Trim ' '
///
/// Separate from FR0013 rather than folded into it, because method-call
/// parens are a matter of taste: the F# style guide keeps them and plenty of
/// codebases drop them. Its own code means either preference can be switched
/// off without losing the other.
///
/// Safety rules, beyond FR0013's requirement that the argument be a single
/// bare atom:
///
///   - the receiver must be a VALUE, never a type. `s.Contains(...)` on a
///     lowercase `s`, or `.Method(...)` on any expression, is a member
///     access and nothing else. A path headed by an uppercase name is
///     ambiguous without type information — `System.Uri("x")` is a
///     CONSTRUCTOR, whose parens are load-bearing (`new Uri "x"` does not
///     compile) — so uppercase-headed paths are left alone entirely.
///
///   - nothing may continue the call on its own line. `x.y(4) <> ""` keeps
///     its parens, because `x.y 4 <> ""` reads as though the argument were
///     `4 <> ""`. A continuation on a LATER line is clear and allowed:
///     `x.y(4)` followed by `|> ignore` becomes `x.y 4`.
///
///   - a projection still blocks the fix (`s.Trim(' ').Length`), exactly as
///     it does for FR0013: there the parens make the application atomic.
///
///   - the next line must not stand aligned past the argument: dropping
///     two characters shifts everything after them on the line, and a
///     block aligned under that text (`&& (flags <- ...` continued on the
///     lines below, fparsec) would end up offside.
module FSharp.Refactor.MethodCallParens

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the parenthesized argument, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// A callee that is certainly a member access on a value, so certainly not a
/// constructor: either a dotted path whose HEAD is lowercase (`s.Contains`,
/// and equally a lowercase module's function), or a `.Method` projected off
/// an arbitrary expression (`(f x).Trim`, `xs.[0].Trim`).
[<return: Struct>]
let private (|MethodCallee|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = head :: _ :: _)) when
        head.idText.Length > 0
        && not (Char.IsUpper head.idText.[0])
        && not (head.idText.StartsWith "op_")
        ->
        ValueSome()
    | SynExpr.DotGet _ -> ValueSome()
    | _ -> ValueNone

/// Is the call continued by something else on its own line?
///
/// Only an enclosing APPLICATION counts — an infix operator or an outer call,
/// the cases where dropping the parens changes how the line reads. Structural
/// parents do not: `if s.Contains("x") then`, `match s.Trim(' ') with`,
/// `[ s.Trim(' ') ]` and a plain binding all read fine bare.
let private continuedOnItsLine (path: SyntaxNode list) (callRange: range) =
    match path with
    | SyntaxNode.SynExpr(SynExpr.App _ as parent) :: _ ->
        let r = parent.Range

        (r.EndLine = callRange.EndLine && r.EndColumn > callRange.EndColumn)
        || (r.StartLine = callRange.StartLine && r.StartColumn < callRange.StartColumn)
    | _ -> false

/// Find single-argument instance method calls whose parenthesized argument is
/// a bare atom and whose line holds nothing else.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                | SynExpr.App(
                    isInfix = false
                    funcExpr = (MethodCallee as callee)
                    argExpr = (SynExpr.Paren(expr = inner; rightParenRange = Some _) as argExpr)) when
                    isSingleLine argExpr.Range
                    && RedundantParens.isBareableArgument source inner
                    && not (continuedOnItsLine path expr.Range)
                    // shorter by the parens, the line no longer anchors a
                    // block aligned under text after the argument
                    && not (
                        alignmentHazardBelow
                            source
                            argExpr.Range.EndLine
                            argExpr.Range.EndColumn
                            (RedundantParens.bareDelta callee argExpr inner)
                    )
                    ->
                    // `s.Trim(' ').Length` needs the atomic application, and
                    // so does the dynamic operator: bare, the argument of
                    // `hub.Clients.Group(roomId)?notify(user)` binds to the
                    // `?` instead and the file stops parsing
                    let projected =
                        match path with
                        | SyntaxNode.SynExpr(SynExpr.DotGet _) :: _
                        | SyntaxNode.SynExpr(SynExpr.DotIndexedGet _) :: _
                        | SyntaxNode.SynExpr(SynExpr.Dynamic _) :: _ -> true
                        // a direct tuple element keeps its parens:
                        // `M(x), y` bare is the same parse, but the comma
                        // next to a spaced application makes the reader run
                        // the precedence table to see which side owns it
                        | SyntaxNode.SynExpr(SynExpr.Tuple _) :: _ -> true
                        // the `_.` shorthand lambda demands an ATOMIC body,
                        // as FR0013 already knows: welendus's
                        // `configureEndpoint _.WithName("x").WithGroupName(g)`
                        // bare became `(fun e -> e.WithName("x").WithGroupName) g`
                        | SyntaxNode.SynExpr(SynExpr.DotLambda _) :: _ -> true
                        | _ -> false

                    if not projected then
                        let innerText = textOfRange source inner.Range

                        let replacement =
                            // `s.Contains("x")` has no space before the argument
                            if callee.Range.End = argExpr.Range.Start then
                                " " + innerText
                            else
                                innerText

                        suggestions.Add
                            {
                                Range = argExpr.Range
                                OriginalText = textOfRange source argExpr.Range
                                ReplacementText = separated source argExpr.Range replacement
                            }
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
