/// Refactoring (performance): a Substring handed straight to a consumer
/// that only READS it allocates a copy the consumer immediately discards.
///
///     Int32.Parse(s.Substring(6, 5))   →   Int32.Parse(s.AsSpan(6, 5))
///     sb.Append(s.Substring(6, 5))     →   sb.Append(s.AsSpan(6, 5))
///     writer.Write(s.Substring 6)      →   writer.Write(s.AsSpan 6)
///
/// Measured: Parse 19.2ns/32B → 7.3ns/0B — 2.6x, allocation-free;
/// StringBuilder.Append 136B → 104B per call at time parity (the 32 B
/// copy gone, the builder's own buffer remaining). The framework's own
/// methods (StartsWith, Contains, IndexOf) already run on spans internally
/// and need no help; the copy above is made by USER code before the
/// framework ever sees it, which is why this is the one span rewrite that
/// earns a rule.
///
/// The consumers are the ones whose span overload is the SAME operation
/// to the character: the numeric parsers, StringBuilder.Append, and
/// TextWriter.Write/WriteLine. StartsWith/Equals/IndexOf stay out — their
/// string overloads compare by culture, their span twins ordinally.
///
/// The fix is a single-identifier swap — `Substring` becomes `AsSpan`,
/// receiver and arguments untouched. Substring and AsSpan check their
/// bounds identically, so the exception path is the same too. (An F#
/// slice `s[a..]` is NOT the same: it clamps where AsSpan throws, so
/// slices are left alone.)
///
/// Safety rules:
///   - the Substring call is DIRECTLY the consumer's only argument, parens
///     aside — no binding, no escape, nothing else sees the value
///   - the receiver's Substring resolves (typed) to System.String's
///   - the consumer resolves to a method whose enclosing type ALSO offers
///     an overload of the same name taking ReadOnlySpan<char> first. This
///     is the availability gate: the span overloads arrived with
///     netstandard2.1 / .NET Core, and a compilation without them
///     (netstandard2.0, net4x) simply never proves the overload — no TFM
///     sniffing needed, and the multi-framework build check backstops
///     shared-source siblings. Append and Write are further pinned to
///     System.Text.StringBuilder and System.IO.TextWriter (or a subclass
///     that re-declares the span overload), so a user type's `Append`
///     with a span overload of its own devising is not assumed identical
///   - byref TryParse spellings (`TryParse(sub, &r)`) are left alone:
///     the tuple argument shape does not match, deliberately
///   - the file opens `System`: `AsSpan` is an extension method of
///     `System.MemoryExtensions`, and a file that opens only
///     `System.Text.RegularExpressions` cannot see it (the tool's own
///     SprintfInterpolation.fs, rolled back when the rule swept it)
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
        /// The consumer's name, for the message.
        ParserName: string
        /// What the consumer does with the characters, for the message:
        /// "parses", "appends", "writes".
        Verb: string
    }

/// Consumer method name → the verb for the message and the enclosing type
/// it must resolve to (None: a System type that proves the span overload —
/// the parsers are many, and each BCL type's Parse is its own).
let private consumers =
    dict
        [
            "Parse", ("parses", None)
            "TryParse", ("parses", None)
            "Append", ("appends", Some "System.Text.StringBuilder")
            "Write", ("writes", Some "System.IO.TextWriter")
            "WriteLine", ("writes", Some "System.IO.TextWriter")
        ]

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
    // is `entity` the named type, or does it derive from it? StreamWriter
    // and StringWriter re-declare the span Write overrides, and their
    // Append/Write must still be TextWriter's operation, not a lookalike's
    let rec isOrDerivesFrom (fullName: string) (entity: FSharpEntity) =
        entity.TryFullName = Some fullName
        || (match entity.BaseType with
            | Some b when b.HasTypeDefinition -> isOrDerivesFrom fullName b.TypeDefinition
            | _ -> false)

    match resolveValue check source ident with
    | ValueSome value ->
        (try
            match value.ApparentEnclosingEntity, consumers.TryGetValue ident.idText with
            | Some entity, (true, (_, requiredType)) ->
                (match requiredType with
                 | Some t -> isOrDerivesFrom t entity
                 // the parsers: the BCL's own (`System.Int32`, `System.Guid`,
                 // `System.DateTime`, `System.Numerics.BigInteger`), whose
                 // string and span overloads are one implementation. A user
                 // type's `Parse(string)` and `Parse(ReadOnlySpan<char>)` are
                 // the author's two methods, and nothing says they agree
                 | None -> entity.Namespace = Some "System" || entity.Namespace = Some "System.Numerics")
                && entity.MembersFunctionsAndValues
                   |> Seq.exists (fun m ->
                       m.LogicalName = ident.idText
                       && m.CurriedParameterGroups.Count >= 1
                       && m.CurriedParameterGroups.[0].Count >= 1
                       && isReadOnlySpanOfChar m.CurriedParameterGroups.[0].[0].Type)
            | _ -> false
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

/// The trailing method ident of a member-call function expression, when
/// it names one of the consumers.
[<return: Struct>]
let private (|ConsumerCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when
        not ids.IsEmpty && consumers.ContainsKey (List.last ids).idText
        ->
        ValueSome(List.last ids)
    | _ -> ValueNone

/// Find Substring calls whose only consumer is a span-capable reader.
/// Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    // `AsSpan` is MemoryExtensions': without `open System` it does not resolve
    if OptionModule.hasErrors check || not (opensNamespace source "System") then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for path, expr in index.Exprs do
                match expr with
                | SynExpr.App(isInfix = false; funcExpr = ConsumerCall consumerIdent; argExpr = consumerArg) when
                    // a quotation translator knows Substring, not AsSpan
                    not (insideQuotedCode path)
                    ->
                    match stripParens consumerArg with
                    | SynExpr.App(isInfix = false; funcExpr = MethodNamed "Substring" substringIdent; argExpr = _) when
                        isSingleLine expr.Range
                        && isStringSubstring check source substringIdent
                        && hasSpanOverload check source consumerIdent
                        ->
                        {
                            Range = substringIdent.idRange
                            ParserName = consumerIdent.idText
                            Verb = fst consumers.[consumerIdent.idText]
                        }
                    | _ -> ()
                | _ -> ()
        ]
