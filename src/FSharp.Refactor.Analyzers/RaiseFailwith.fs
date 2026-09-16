/// Refactoring: `raise (Exception msg)` is exactly what `failwith` does.
///
///     raise (Exception "boom")           →  failwith "boom"
///     raise (new Exception(msg))         →  failwith msg
///     raise (Exception(sprintf "%d" n))  →  failwith (sprintf "%d" n)
///
/// Only the plain `System.Exception` type qualifies — `failwith` constructs
/// exactly that, so the raised exception's type and message are unchanged.
/// Subclasses (`ArgumentException`, ...), the no-argument constructor, and
/// the `(message, innerException)` overload are left alone.
module FSharp.Refactor.RaiseFailwith

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
    }

let private isExceptionPath (ids: Ident list) =
    match ids |> List.map (fun i -> i.idText) with
    | [ "Exception" ]
    | [ "System"; "Exception" ] -> true
    | _ -> false

/// `Exception arg` / `Exception(arg)` / `new Exception(arg)`, returning the
/// constructor argument.
[<return: Struct>]
let private (|ExceptionCtor|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id; argExpr = arg) when isExceptionPath [ id ] ->
        ValueSome arg
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        isExceptionPath ids
        ->
        ValueSome arg
    | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when isExceptionPath ids ->
        ValueSome arg
    | _ -> ValueNone

/// The message argument's text as a `failwith` argument.
let private messageText (source: ISourceText) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.String _, _)
    | SynExpr.InterpolatedString _ -> textOfRange source e.Range
    | _ -> argumentText source e

/// Find `raise (Exception message)` applications.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(_path, expr) =
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = IdentName "raise"; argExpr = arg) when isSingleLine expr.Range ->
                    match stripParens arg with
                    | ExceptionCtor ctorArg ->
                        match stripParens ctorArg with
                        | SynExpr.Tuple _ -> () // (message, innerException) overload
                        | UnitConst -> () // no-argument constructor
                        // a single NAMED argument parses as an op_Equality
                        // application — `Exception(message = "boom")` must
                        // not become `failwith (message = "boom")`
                        | SynExpr.App(funcExpr = SynExpr.App(funcExpr = SingleIdent eq)) when eq.idText = "op_Equality" ->
                            ()
                        | message ->
                            suggestions.Add
                                {
                                    Range = expr.Range
                                    OriginalText = textOfRange source expr.Range
                                    ReplacementText = "failwith " + messageText source message
                                }
                    | _ -> ()
                | _ -> ()
        }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
