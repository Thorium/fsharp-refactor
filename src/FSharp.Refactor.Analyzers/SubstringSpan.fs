/// Refactoring (performance): a Substring handed straight to a parser
/// allocates a copy the parser immediately discards.
///
///     Int32.Parse(s.Substring(6, 5))   →   Int32.Parse(s.AsSpan(6, 5))
///
/// Measured: 19.2ns/32B → 7.3ns/0B — 2.6x, allocation-free. The
/// framework's own methods (StartsWith, Contains, IndexOf) already run
/// on spans internally and need no help; the copy above is made by USER
/// code before the framework ever sees it, which is why this is the one
/// span rewrite that earns a rule.
///
/// The fix is a single-identifier swap — `Substring` becomes `AsSpan`,
/// receiver and arguments untouched.
///
/// Safety rules:
///   - the Substring call is DIRECTLY the parser's only argument, parens
///     aside — no binding, no escape, nothing else sees the value
///   - the receiver's Substring resolves (typed) to System.String's
///   - the parser resolves to a method whose enclosing type ALSO offers
///     an overload taking ReadOnlySpan<char> first. This is the
///     availability gate: span Parse overloads arrived with .NET Core /
///     net6+, and a compilation without them (netstandard2.0, net4x)
///     simply never proves the overload — no TFM sniffing needed, and
///     the multi-framework build check backstops shared-source siblings
///   - byref TryParse spellings (`TryParse(sub, &r)`) are left alone:
///     the tuple argument shape does not match, deliberately
module FSharp.Refactor.SubstringSpan

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The `Substring` identifier — the fix replaces exactly this.
        Range: range
        /// The parser's name, for the message.
        ParserName: string
    }

let private parserNames = set [ "Parse"; "TryParse" ]

let private resolveValue (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as value -> ValueSome value
        | _ -> ValueNone
    | None -> ValueNone

/// Is this System.String's Substring?
let private isStringSubstring (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match resolveValue check source ident with
    | ValueSome value -> OptionModule.enclosingFullName value = "System.String"
    | ValueNone -> false

let private isReadOnlySpanOfChar (t: FSharpType) =
    // instance-level stripping keeps the generic instantiation
    let rec strip (t: FSharpType) =
        if t.IsAbbreviation then strip t.AbbreviatedType else t

    try
        let t = strip t

        t.HasTypeDefinition
        && t.TypeDefinition.TryFullName = Some "System.ReadOnlySpan`1"
        && t.GenericArguments.Count = 1
        && (let g = strip t.GenericArguments.[0]
            g.HasTypeDefinition && g.TypeDefinition.TryFullName = Some "System.Char")
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// Does the parser's enclosing type offer a ReadOnlySpan<char> overload of
/// the same method? THE availability gate: a netstandard2.0 or net4x
/// compilation has no such overload to find, so the rule stays silent
/// there without any target-framework sniffing.
let private hasSpanOverload (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match resolveValue check source ident with
    | ValueSome value ->
        (try
            match value.ApparentEnclosingEntity with
            | Some entity ->
                entity.MembersFunctionsAndValues
                |> Seq.exists (fun m ->
                    m.LogicalName = ident.idText
                    && m.CurriedParameterGroups.Count >= 1
                    && m.CurriedParameterGroups.[0].Count >= 1
                    && isReadOnlySpanOfChar m.CurriedParameterGroups.[0].[0].Type)
            | None -> false
         with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
             false)
    | ValueNone -> false

/// The trailing `Substring` ident of a member-call function expression.
[<return: Struct>]
let private (|MethodNamed|_|) (name: string) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty && (List.last ids).idText = name ->
        ValueSome(List.last ids)
    | _ -> ValueNone

/// Find Substring calls whose only consumer is a span-capable parser.
/// Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = MethodNamed "Parse" parserIdent; argExpr = parserArg)
                | SynExpr.App(isInfix = false; funcExpr = MethodNamed "TryParse" parserIdent; argExpr = parserArg) when
                    parserNames.Contains parserIdent.idText
                    // a quotation translator knows Substring, not AsSpan
                    && not (insideQuotedCode path)
                    ->
                    match stripParens parserArg with
                    | SynExpr.App(isInfix = false; funcExpr = MethodNamed "Substring" substringIdent; argExpr = _) when
                        isSingleLine expr.Range
                        && isStringSubstring check source substringIdent
                        && hasSpanOverload check source parserIdent
                        ->
                        {
                            Range = substringIdent.idRange
                            ParserName = parserIdent.idText
                        }
                    | _ -> ()
                | _ -> ()
        ]
