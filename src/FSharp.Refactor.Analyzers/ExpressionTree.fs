/// Arguments the compiler turns into System.Linq.Expressions trees.
///
/// A lambda (or, for a `[<ProjectionParameter>]` custom operation, the
/// bare operation argument) handed to a parameter of type
/// `Expression<Func<...>>` is not code that runs here: F# auto-quotes it
/// into a LINQ expression tree, and whoever receives the tree walks it BY
/// SHAPE. SqlHydra's `select { for a in t do where (a.Line2 <> None) }`
/// turns `<> None` into `IS NOT NULL`; the "nicer" spelling
/// `a.Line2 |> Option.isSome` is a tree its visitor has never seen and the
/// query throws at runtime. So the shape-changing rules (FR0010, FR0012,
/// FR0034) stay quiet inside such an argument.
///
/// Only the typed callee decides: the path is walked outward to every
/// enclosing application whose ARGUMENT side holds the range, the callee's
/// last identifier is resolved (`GetSymbolUseAtLocation` resolves a custom
/// operation keyword to its builder method too), and the gate closes when
/// any of its parameters is a `System.Linq.Expressions.Expression`. An
/// unresolved callee keeps the rules' behaviour as it was; F# quotations
/// `<@ @>` and `query { }` are not this module's business.
module FSharp.Refactor.ExpressionTree

open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK

/// Is the parameter's type `System.Linq.Expressions.Expression<_>` (or the
/// non-generic base)? Abbreviations are followed first.
let private isExpressionType (t: FSharpType) =
    try
        let t = OptionModule.stripAbbreviations t

        t.HasTypeDefinition
        && (t.TypeDefinition.TryFullName
            |> Option.exists (fun name -> name.StartsWith "System.Linq.Expressions.Expression"))
    with OptionModule.FcsSymbolFailure ->
        false

/// The identifier that names the callee of an application spine: the `f`
/// of `f a b`, the `Where` of `xs.Where(...)` and `(...).Where(...)`, the
/// `where` of a computation expression's custom operation `where (...)`.
[<TailCall>]
let rec private calleeIdent (e: SynExpr) : Ident voption =
    match e with
    | SynExpr.App(funcExpr = f) -> calleeIdent f
    | SynExpr.Paren(expr = inner)
    | SynExpr.TypeApp(expr = inner) -> calleeIdent inner
    | SynExpr.Ident id -> ValueSome id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// Does the callee named by this identifier take an expression tree in any
/// parameter position? The typed symbol answers; anything unresolved is a
/// plain call.
let private takesExpressionTree (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as callee ->
            try
                callee.CurriedParameterGroups
                |> Seq.exists (Seq.exists (fun (p: FSharpParameter) -> isExpressionType p.Type))
            with OptionModule.FcsSymbolFailure ->
                false
        | _ -> false
    | None -> false

/// A gate for one file: `gate path range` is true when the range sits
/// inside an argument the compiler will turn into a LINQ expression tree.
/// Callee lookups are memoized per callee identifier, so a rule asking
/// about several expressions under one `where (...)` resolves it once.
let gate (check: FSharpCheckFileResults) (source: ISourceText) : SyntaxNode list -> range -> bool =
    let known = Dictionary<range, bool>()

    let calleeTakesTree (id: Ident) =
        match known.TryGetValue id.idRange with
        | true, answer -> answer
        | false, _ ->
            let answer = takesExpressionTree check source id
            known.[id.idRange] <- answer
            answer

    fun path r ->
        path
        |> List.exists (fun node ->
            match node with
            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f; argExpr = arg)) when Range.rangeContainsRange arg.Range r ->
                match calleeIdent f with
                // an operator application (`x |> f`, `a && b`) is never
                // the auto-quoting call; the call is further out
                | ValueSome id when not (id.idText.StartsWith "op_") -> calleeTakesTree id
                | _ -> false
            | _ -> false)
