/// FR0136 (fix): the zero-argument Guid constructor — the classic .NET
/// trap where `new Guid()` reads like "a new guid" but produces
/// 00000000-0000-0000-0000-000000000000:
///
///     let id = Guid()             let id = Guid.Empty      (CLI fix —
///     let id = new System.Guid()  System.Guid.Empty         identical value,
///                                                           stated intent)
///     editor alternative:         Guid.NewGuid()           (the LIKELY
///                                                           intent — but a
///                                                           behavior change,
///                                                           never auto)
///
/// The Empty spelling is value- and type-identical, so the CLI applies it
/// freely; if the code MEANT a fresh guid, the bug becomes visible at the
/// call site instead of hiding behind constructor syntax. Typed-gated to
/// System.Guid; the qualification prefix is preserved.
module FSharp.Refactor.EmptyGuid

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        /// `{prefix}Guid.Empty` — the behavior-preserving spelling.
        EmptyText: string
        /// `{prefix}Guid.NewGuid()` — the likely intent, editor-only.
        NewGuidText: string
    }

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let isSystemGuid (ids: Ident list) =
        let guidId = List.last ids
        let lineText = source.GetLineString(guidId.idRange.EndLine - 1)

        match
            check.GetSymbolUseAtLocation(
                guidId.idRange.EndLine,
                guidId.idRange.EndColumn,
                lineText,
                ids |> List.map _.idText
            )
        with
        | Some symbolUse ->
            match symbolUse.Symbol with
            | :? FSharpEntity as e ->
                (try
                    e.TryFullName = Some "System.Guid"
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | :? FSharpMemberOrFunctionOrValue as m ->
                (try
                    m.DeclaringEntity
                    |> Option.bind (fun e -> e.TryFullName)
                    |> Option.map ((=) "System.Guid")
                    |> Option.defaultValue false
                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false
        | None -> false

    let suggest (e: SynExpr) (ids: Ident list) =
        if isSystemGuid ids then
            let prefix =
                ids
                |> List.take (ids.Length - 1)
                |> List.map (fun i -> i.idText + ".")
                |> String.concat ""

            Some
                {
                    Range = e.Range
                    EmptyText = $"{prefix}Guid.Empty"
                    NewGuidText = $"{prefix}Guid.NewGuid()"
                }
        else
            None

    [
        for _, e in index.Exprs do
            match e with
            // new Guid() / new System.Guid()
            | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when
                not ids.IsEmpty
                && (List.last ids).idText = "Guid"
                && (match stripParens arg with
                    | SynExpr.Const(SynConst.Unit, _) -> true
                    | _ -> false)
                ->
                match suggest e ids with
                | Some s -> s
                | None -> ()
            // Guid() / System.Guid() without new
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                argExpr = SynExpr.Const(SynConst.Unit, _)) when not ids.IsEmpty && (List.last ids).idText = "Guid" ->
                match suggest e ids with
                | Some s -> s
                | None -> ()
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident ctor; argExpr = SynExpr.Const(SynConst.Unit, _)) when
                ctor.idText = "Guid"
                ->
                match suggest e [ ctor ] with
                | Some s -> s
                | None -> ()
            | _ -> ()
    ]
