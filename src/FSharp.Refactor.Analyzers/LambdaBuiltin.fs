/// Refactoring: a lambda that only reproduces a built-in function.
///
///     fun x -> x           →  id
///     fun (a, b) -> a      →  fst
///     fun (a, b) -> b      →  snd
///
/// Safety rules:
///   - one parameter only. `fun x y -> x` is not `fst`: it takes its
///     arguments curried, where `fst` takes one tuple.
///   - the pattern must be plain names, unannotated. `fun (a: int, b) -> a`
///     carries a type annotation that the call site may be relying on, and
///     `fst` cannot carry it.
///   - not as a direct argument to a .NET method. `xs.Select(fun x -> x)`
///     relies on F# converting a lambda EXPRESSION to a delegate; a function
///     value does not convert the same way, so `xs.Select(id)` need not
///     compile. Arguments to F# functions (`List.map id`) are unaffected.
module FSharp.Refactor.LambdaBuiltin

open System
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the whole lambda, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// A pattern that is exactly one unannotated name, yielding that name.
[<return: Struct>]
let private (|PlainName|_|) (pat: SynPat) =
    match pat with
    | SynPat.Named(ident = SynIdent(ident = id)) -> ValueSome id.idText
    | _ -> ValueNone

/// `(a, b)` — a two-element tuple of plain names, in either paren style.
[<return: Struct>]
let private (|PlainNamePair|_|) (pat: SynPat) =
    let unwrapped =
        match pat with
        | SynPat.Paren(pat = inner) -> inner
        | other -> other

    match unwrapped with
    | SynPat.Tuple(elementPats = [ PlainName first; PlainName second ]) -> ValueSome(first, second)
    | _ -> ValueNone

/// The identifier an expression is, if it is nothing more than one.
[<return: Struct>]
let private (|JustIdent|_|) (e: SynExpr) =
    match e with
    | SynExpr.Ident id -> ValueSome id.idText
    | _ -> ValueNone

/// The callee of the application this node sits in, seen through the call's
/// own parentheses: `xs.Select(fun x -> x)` wraps the lambda in a `Paren`
/// before the `App` that decides anything.
[<TailCall>]
let rec private enclosingCallee (path: SyntaxNode list) =
    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren _) :: rest -> enclosingCallee rest
    | SyntaxNode.SynExpr(SynExpr.App(funcExpr = funcExpr)) :: _ -> Some funcExpr
    | _ -> None

/// Does this callee name a .NET method rather than an F# function?
let private isMethod (funcExpr: SynExpr) =
    match funcExpr with
    | SynExpr.DotGet _ -> true
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
        let last = (List.last ids).idText
        last.Length > 0 && Char.IsUpper last.[0]
    | SynExpr.Ident id -> id.idText.Length > 0 && Char.IsUpper id.idText.[0]
    | _ -> false

/// Is this lambda a direct argument to a .NET method call, where the
/// lambda-to-delegate conversion may be doing the work?
let private argumentToMethod (path: SyntaxNode list) =
    enclosingCallee path |> Option.exists isMethod

/// Names in scope at a position that the file itself binds. `id`, `fst` and
/// `snd` are only the builtins while nothing nearer shadows them, and `let
/// id bhvr = returnB bhvr` in a module (nu's Behavior does exactly this for
/// all three) makes `id` mean something else for the rest of it — so `fun x
/// -> x` becoming `id` would call the wrong function. Verified: FR0095
/// rewrote a lambda inside such a module, broke the build and was rolled
/// back.
///
/// Scope is read off the tree, because this rule carries no typed results
/// and is worth keeping usable under --parse-only: the enclosing `let`s,
/// parameters, lambda arguments, match and loop patterns on the path, and
/// the module-level bindings declared ABOVE the position. The far more
/// common `let id = 42` in some unrelated function stays where it is and
/// costs nothing here. A module opened from another file that rebinds the
/// name is the one case this cannot see; the verification build catches it.
let private shadowedAt (path: SyntaxNode list) (at: range) =
    let bindingNames (bindings: SynBinding list) =
        bindings
        |> List.collect (fun (SynBinding(headPat = headPat)) -> patNames headPat)

    let declaredAbove (decls: SynModuleDecl list) =
        decls
        |> List.collect (fun decl ->
            match decl with
            | SynModuleDecl.Let(bindings = bindings; range = r) when Position.posLt r.Start at.Start ->
                bindingNames bindings
            | _ -> [])

    path
    |> List.collect (fun node ->
        match node with
        | SyntaxNode.SynExpr(LetOrUseE lou) -> bindingNames lou.Bindings
        | SyntaxNode.SynBinding(SynBinding(headPat = headPat)) -> patNames headPat
        | SyntaxNode.SynExpr(SynExpr.Lambda(parsedData = Some(parameters, _))) -> parameters |> List.collect patNames
        | SyntaxNode.SynMatchClause(SynMatchClause(pat = pat)) -> patNames pat
        | SyntaxNode.SynExpr(SynExpr.ForEach(pat = pat)) -> patNames pat
        | SyntaxNode.SynExpr(SynExpr.For(ident = ident)) -> [ ident.idText ]
        | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(decls = decls))
        | SyntaxNode.SynModule(SynModuleDecl.NestedModule(decls = decls)) -> declaredAbove decls
        | _ -> [])
    |> Set.ofList

/// The lambda's own parentheses, when it has them and dropping them is
/// safe: a bare identifier needs none, and `Array.init this.Count (id)`,
/// `ListReduceNode(list, (id), reduction)` — nine sites on Mibo — read as
/// a leftover. `f (id)` and `f id` are the same application; the one
/// place the parentheses still do work is when they touch a neighbouring
/// token (`List.map(fun x -> x)` would fuse into `List.mapid`), so a
/// glued character on either side keeps them.
let private droppableParens (source: ISourceText) (path: SyntaxNode list) (lambda: SynExpr) =
    match path with
    | SyntaxNode.SynExpr(SynExpr.Paren(expr = inner; range = pr)) :: _ when Range.equals inner.Range lambda.Range ->
        let glued (c: char) =
            Char.IsLetterOrDigit c || "_'.()[]{}".Contains c

        let startLine = source.GetLineString(pr.StartLine - 1)
        let endLine = source.GetLineString(pr.EndLine - 1)

        let before =
            if pr.StartColumn = 0 then
                ' '
            else
                startLine.[pr.StartColumn - 1]

        let after =
            if pr.EndColumn >= endLine.Length then
                ' '
            else
                endLine.[pr.EndColumn]

        if glued before || glued after then
            ValueNone
        else
            ValueSome pr
    | _ -> ValueNone

/// Find lambdas that are just `id`, `fst` or `snd`.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let suggestions = ResizeArray<Suggestion>()

    let collector =
        { new SyntaxCollectorBase() with
            override _.WalkExpr(path, expr) =
                match expr with
                // `parsedData` carries the patterns as written, before the
                // compiler lowers them into SynSimplePats
                | SynExpr.Lambda(parsedData = Some([ parameter ], body)) when not (argumentToMethod path) ->
                    let builtin =
                        match parameter, body with
                        | PlainName only, JustIdent returned when only = returned -> Some "id"
                        | PlainNamePair(first, second), JustIdent returned when returned = first -> Some "fst"
                        | PlainNamePair(first, second), JustIdent returned when returned = second -> Some "snd"
                        | _ -> None

                    match builtin with
                    | Some replacement when not ((shadowedAt path expr.Range).Contains replacement) ->
                        // the edit covers the lambda's parentheses too:
                        // the replacement is a bare identifier
                        let range =
                            match droppableParens source path expr with
                            | ValueSome parenRange -> parenRange
                            | ValueNone -> expr.Range

                        suggestions.Add
                            { Range = range
                              OriginalText = textOfRange source range
                              ReplacementText = replacement }
                    | _ -> ()
                | _ -> () }

    AstIndex.replay collector parseTree
    List.ofSeq suggestions
