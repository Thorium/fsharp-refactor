/// An interpreter for the F# the rules leave behind: the boolean and
/// integer operators of BoolExpr, `not`, parentheses, literals and the
/// three variables. Anything else is a loud failure — a rewrite into a
/// shape this cannot read is worth a look, not a silent pass.
module FSharp.Refactor.PropertyTests.Interpreter

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text

/// The name an operator or function is applied by: `op_BooleanAnd`,
/// `not`, ... Operators parse as a single-identifier long ident carrying
/// their notation as trivia; plain functions as an ident.
[<return: Struct>]
let private (|Callee|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome id.idText
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> ValueSome id.idText
    | _ -> ValueNone

/// `lhs OP rhs`: an application of the flagged-infix application of OP
/// to lhs, to rhs.
[<return: Struct>]
let private (|Infix|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.App(isInfix = true; funcExpr = Callee op; argExpr = lhs); argExpr = rhs) ->
        ValueSome(op, lhs, rhs)
    | _ -> ValueNone

let rec evalInt (env: string -> int) (e: SynExpr) : int =
    match e with
    | SynExpr.Paren(expr = inner) -> evalInt env inner
    | SynExpr.Const(SynConst.Int32 n, _) -> n
    | SynExpr.Ident id -> env id.idText
    | Infix("op_Addition", a, b) -> evalInt env a + evalInt env b
    | Infix("op_Subtraction", a, b) -> evalInt env a - evalInt env b
    | Infix("op_Multiply", a, b) -> evalInt env a * evalInt env b
    | SynExpr.App(isInfix = false; funcExpr = Callee "op_UnaryNegation"; argExpr = a) -> -(evalInt env a)
    | other -> failwithf "not an integer expression this interpreter reads: %A" other

let rec evalBool (env: string -> int) (e: SynExpr) : bool =
    match e with
    | SynExpr.Paren(expr = inner) -> evalBool env inner
    | SynExpr.Const(SynConst.Bool b, _) -> b
    | Infix("op_BooleanAnd", a, b) -> evalBool env a && evalBool env b
    | Infix("op_BooleanOr", a, b) -> evalBool env a || evalBool env b
    | Infix("op_Equality", a, b) -> evalInt env a = evalInt env b
    | Infix("op_Inequality", a, b) -> evalInt env a <> evalInt env b
    | Infix("op_LessThan", a, b) -> evalInt env a < evalInt env b
    | Infix("op_LessThanOrEqual", a, b) -> evalInt env a <= evalInt env b
    | Infix("op_GreaterThan", a, b) -> evalInt env a > evalInt env b
    | Infix("op_GreaterThanOrEqual", a, b) -> evalInt env a >= evalInt env b
    | SynExpr.App(isInfix = false; funcExpr = Callee "not"; argExpr = a) -> not (evalBool env a)
    | other -> failwithf "not a boolean expression this interpreter reads: %A" other

/// The body of the single `let f ... = body` a BoolExpr program declares.
let bodyOf (tree: ParsedInput) : SynExpr =
    match tree with
    | ParsedInput.ImplFile(ParsedImplFileInput(contents = [ SynModuleOrNamespace(decls = decls) ])) ->
        decls
        |> List.tryPick (function
            | SynModuleDecl.Let(bindings = [ SynBinding(expr = body) ]) -> Some body
            | _ -> None)
        |> Option.defaultWith (fun () -> failwithf "no let binding in %A" decls)
    | other -> failwithf "not a one-module implementation file: %A" other

/// Run the program's function at one environment, through the tree.
let run (tree: ParsedInput) (env: int[]) : bool =
    let lookup (name: string) =
        match Array.tryFindIndex ((=) name) BoolExpr.variables with
        | Some i -> env.[i]
        | None -> failwithf "unbound variable %s" name

    evalBool lookup (bodyOf tree)

/// `range` as `(line,col)-(line,col)`, for messages.
let rangeText (r: range) =
    $"({r.StartLine},{r.StartColumn})-({r.EndLine},{r.EndColumn})"
