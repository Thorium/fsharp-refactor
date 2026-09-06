/// Refactoring (FR0092): give a static `failwith` message the context of
/// the call that produced it.
///
///     let mymethod (x: int) =          let mymethod (x: int) =
///         failwith "Error"        →        failwith $"Error, calling mymethod with x: {x}"
///
/// A constant error string is the anti-pattern: every occurrence in the log
/// reads the same, so it says which line threw but nothing about why. The
/// enclosing function's arguments are the cheapest context available, and
/// they are in scope right there.
///
/// Only STATIC strings are rewritten. A message that is already
/// interpolated has had thought put into it, and amending it would fight
/// the author rather than help them.
///
/// Safety rules:
///   - `failwith` must resolve to FSharp.Core (not a local shadow)
///   - the argument is a single-line regular string literal: no verbatim or
///     triple-quoted strings (different escaping), and no `{`, `}` or `%`,
///     which change meaning once the string becomes interpolated
///   - the enclosing binding is a function with 1-4 parameters; only the
///     plain-named ones (`x`, `(x: int)`) are quoted, and only those whose
///     TYPE prints something a reader can use: primitives, strings, enums,
///     unions without fields, small records of those, and options or lists
///     of them. A metadata reader, a byte array, a socket, a function, a
///     generic `'a` or a compiler-tree node prints its type name or worse
///     (ilread's `sigptrGetTy ctxt numTypars bytes sigptr`, Suave's
///     acceptor over sockets and pools), so a function with no such
///     parameter gets no note at all. `let f = function ... | _ ->
///     failwith "..."` has one argument with no name: when its type
///     prints, the wildcard arm is named (`value`) and quoted
///   - the message must not already mention a parameter by name — that is
///     a hand-written contextual message
///   - the message must not state an invariant: "unreachable", "not
///     possible", "NYI", "internal error", "invalid case" — no call context
///     explains a branch that was never meant to run
///   - the message must not be the enclosing function's own name (fslex
///     writes `failwith "<rule>"` as its fallthrough arm)
///   - the enclosing function, its type or module, or a parameter must not
///     smell of secrets — auth, session, crypt, token, password, secret,
///     credential: Suave's `parseData textBlob` throws on freshly decrypted
///     session data, and interpolating it would log the secret
///   - the file must not be a test file: a test's failwith is an assertion,
///     and the runner already names the test and its inputs
///
/// The rewrite only changes the text of the exception; the exception type
/// and control flow are untouched. It does put argument VALUES into the
/// message, so the hint says so: on a parameter holding personal data that
/// is a logging decision, not a mechanical one.
///
/// The text is still observable behaviour — tests assert on messages, and
/// callers match on them — so the fix is offered only under
/// `--api-changes`; a plain sweep reports it as an advisory note.
module FSharp.Refactor.FailwithContext

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        OriginalText: string
        ReplacementText: string
        /// The enclosing function, for the message.
        FunctionName: string
        /// For a `let f = function ... | _ -> failwith "..."` the wildcard
        /// arm has to be named before it can be quoted: the edit that
        /// names it, applied together with the message edit.
        PatternEdit: (range * string * string) option
    }

/// A function binding: its whole range, its name, its plain-named
/// parameters, and — for `let f = function ...` — the binding's name
/// ident and body, through which the one implicit argument is typed and
/// found.
type private Function =
    {
        BindingRange: range
        Name: string
        Parameters: Ident list
        /// `let f = function ...`: the name ident (whose type's domain is
        /// the argument's type) and the `function` body.
        Implicit: (Ident * SynExpr) option
    }

/// A parameter that can be reported by name.
let private paramIdent (p: SynPat) =
    match p with
    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id
    | SynPat.Paren(pat = SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id)))) -> Some id
    | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))) -> Some id
    | _ -> None

/// A function binding we could name and quote parameters from. A tuple
/// or wildcard parameter carries no name to report and is simply left
/// out. `let f = function ...` (Suave's `toOpcode`) has one argument with
/// no name at all; its fallthrough arm can be named on the way.
let private describeBinding (binding: SynBinding) =
    match binding with
    | SynBinding(headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = ids); argPats = SynArgPats.Pats pats)) when
        not (ids.IsEmpty || pats.IsEmpty) && pats.Length <= 4
        ->
        Some
            { BindingRange = binding.RangeOfBindingWithRhs
              Name = (List.last ids).idText
              Parameters = pats |> List.choose paramIdent
              Implicit = None }
    | SynBinding(headPat = SynPat.Named(ident = SynIdent(ident = id)); expr = SynExpr.MatchLambda _ as body)
    | SynBinding(
        headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ]); argPats = SynArgPats.Pats [])
        expr = SynExpr.MatchLambda _ as body) ->
        Some
            { BindingRange = binding.RangeOfBindingWithRhs
              Name = id.idText
              Parameters = []
              Implicit = Some(id, body) }
    | _ -> None

/// A message that states an invariant: the branch was never meant to run,
/// and no argument explains why it did.
let private invariantMessage =
    Regex(
        @"(?i)\b(unreachable|not possible|impossible|NYI|not (yet )?implemented|internal error|invalid (case|state)|should (not|never) (happen|be reached|get here|reach)|can(not|'t) happen|never happens?)\b",
        RegexOptions.Compiled
    )

/// A name that says the values in scope are secrets.
let private sensitiveName =
    Regex(@"(?i)auth(?!or)|session|crypt|token(?!i[sz])|passw|secret|credential|api_?key", RegexOptions.Compiled)

/// Does the message name the parameter as a WORD? `x` inside "no text
/// property" is not a mention (ParsePynb), nor is `ty` inside "open
/// generic type" (fsi).
let private mentionsParameter (text: string) (name: string) =
    Regex.IsMatch(text, @"(?<![A-Za-z0-9_'])" + Regex.Escape name + @"(?![A-Za-z0-9_'])")

/// Does a value of this type print something a reader can use? Primitives,
/// strings, enums, unions without fields, small records of those, and
/// options or lists of them do; a class, an array, a function, a tuple, a
/// generic parameter or a compiler-tree node prints its type name.
let rec private printsUsefully (depth: int) (t: FSharpType) =
    try
        // FCS's own stripping keeps the instantiation: `Point option` is
        // FSharpOption<Point>, not FSharpOption<'T>
        let t = t.StripAbbreviations()

        if
            t.IsGenericParameter
            || t.IsFunctionType
            || t.IsTupleType
            || not t.HasTypeDefinition
        then
            false
        else
            let d = t.TypeDefinition

            match d.TryFullName with
            | Some("System.String" | "System.Boolean" | "System.Char" | "System.Guid" | "System.Uri" | "System.Version") ->
                true
            | Some("System.Int32" | "System.Int64" | "System.Int16" | "System.Byte" | "System.SByte") -> true
            | Some("System.UInt32" | "System.UInt64" | "System.UInt16" | "System.IntPtr" | "System.UIntPtr") -> true
            | Some("System.Double" | "System.Single" | "System.Decimal") -> true
            | Some("System.DateTime" | "System.DateTimeOffset" | "System.TimeSpan" | "System.DateOnly" | "System.TimeOnly") ->
                true
            | Some fullName when
                fullName.StartsWith "Microsoft.FSharp.Core.FSharpOption`"
                || fullName.StartsWith "Microsoft.FSharp.Core.FSharpValueOption`"
                || fullName.StartsWith "Microsoft.FSharp.Collections.FSharpList`"
                ->
                depth < 2 && t.GenericArguments |> Seq.forall (printsUsefully (depth + 1))
            | _ ->
                if d.IsEnum then
                    true
                elif d.IsFSharpUnion then
                    d.UnionCases |> Seq.forall (fun c -> c.Fields.Count = 0)
                elif d.IsFSharpRecord then
                    depth < 2
                    && d.FSharpFields.Count <= 4
                    && d.FSharpFields |> Seq.forall (fun f -> printsUsefully (depth + 1) f.FieldType)
                else
                    false
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The declared or inferred type of the value an ident binds, from the
/// typed tree.
let private typeOfBound (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    let r = id.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ id.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpMemberOrFunctionOrValue as v ->
            (try
                Some v.FullType
             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                 None)
        | _ -> None
    | None -> None

/// The parameter's type.
let private parameterType (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    typeOfBound check source id

/// The type of the one argument of `let f = function ...`: the domain of
/// f's own function type.
let private implicitArgType (check: FSharpCheckFileResults) (source: ISourceText) (id: Ident) =
    typeOfBound check source id
    |> Option.bind (fun t ->
        try
            let t = t.StripAbbreviations()

            if t.IsFunctionType && t.GenericArguments.Count = 2 then
                Some t.GenericArguments.[0]
            else
                None
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            None)

/// The wildcard arm of a `function` body whose result is this throw:
/// `| _ -> failwith "..."` directly under the binding's own `function`,
/// not inside a nested match.
let private wildcardArmOf (path: SyntaxNode list) (body: SynExpr) (throwRange: range) =
    match path with
    | SyntaxNode.SynMatchClause(SynMatchClause(pat = SynPat.Wild _ as wild; resultExpr = result)) :: SyntaxNode.SynExpr(SynExpr.MatchLambda(
        range = bodyRange)) :: _ when
        Range.equals bodyRange body.Range
        && Range.rangeContainsRange (stripParens result).Range throwRange
        ->
        Some wild.Range
    | _ -> None

/// The names of the modules and types enclosing an expression.
let private enclosingNames (path: SyntaxNode list) =
    path
    |> List.collect (fun node ->
        match node with
        | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(longId = ids)) -> ids |> List.map (fun i -> i.idText)
        | SyntaxNode.SynModule(SynModuleDecl.NestedModule(moduleInfo = SynComponentInfo(longId = ids))) ->
            ids |> List.map (fun i -> i.idText)
        | SyntaxNode.SynTypeDefn(SynTypeDefn(typeInfo = SynComponentInfo(longId = ids))) ->
            ids |> List.map (fun i -> i.idText)
        | _ -> [])

/// The static `failwith "..."` shape this rule rewrites.
[<return: Struct>]
let private (|StaticFailwith|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.Ident failwithIdent
        argExpr = SynExpr.Const(SynConst.String(text = text; synStringKind = SynStringKind.Regular), literalRange)) when
        failwithIdent.idText = "failwith"
        ->
        ValueSome(failwithIdent, text, literalRange)
    | _ -> ValueNone

/// Find static failwith messages that can carry their caller's arguments.
/// Requires typed check results for the shadowing gate and the parameter
/// types.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    if OptionModule.hasErrors check || SwallowedException.isTestFile index source then
        []
    else
        // every function binding in the file, module-level and nested
        let functions = ResizeArray<Function>()

        for _, decl in index.Decls do
            match decl with
            | SynModuleDecl.Let(bindings = bindings) ->
                for binding in bindings do
                    describeBinding binding |> Option.iter functions.Add
            | _ -> ()

        for _, expr in index.Exprs do
            match expr with
            | LetOrUseE lou ->
                for binding in lou.Bindings do
                    describeBinding binding |> Option.iter functions.Add
            | _ -> ()

        if functions.Count = 0 then
            []
        else
            let all = source.GetSubTextString(0, source.Length)

            // every static failwith literal of the file, by text: two
            // throws sharing a message (Suave's `failwith "Index overrun."`
            // twice in one function) are not one reading the other back
            let thrownCounts =
                index.Exprs
                |> Array.choose (fun (_, e) ->
                    match e with
                    | StaticFailwith(_, _, r) -> Some(textOfRange source r)
                    | _ -> None)
                |> Array.countBy id
                |> Map.ofArray

            // parameter types resolve once per parameter, not per throw
            let usefulParameter =
                let cache = System.Collections.Generic.Dictionary<range, bool>()

                fun (id: Ident) ->
                    match cache.TryGetValue id.idRange with
                    | true, known -> known
                    | false, _ ->
                        let useful = parameterType check source id |> Option.exists (printsUsefully 0)

                        cache.[id.idRange] <- useful
                        useful

            // a name for the wildcard arm of a `function` that nothing in
            // the binding already spells
            let freshNameIn (r: range) =
                let taken =
                    Seq.append
                        (index.Exprs
                         |> Seq.choose (fun (_, e) ->
                             match e with
                             | SynExpr.Ident id when Range.rangeContainsRange r id.idRange -> Some id.idText
                             | _ -> None))
                        (index.Pats
                         |> Seq.choose (fun (_, p) ->
                             match p with
                             | SynPat.Named(ident = SynIdent(ident = id)) when Range.rangeContainsRange r id.idRange ->
                                 Some id.idText
                             | _ -> None))
                    |> Set.ofSeq

                [ "value"; "input"; "arg" ] |> List.tryFind (fun n -> not (taken.Contains n))

            [ for path, expr in index.Exprs do
                  match expr with
                  | StaticFailwith(failwithIdent, text, literalRange) when
                      isSingleLine literalRange
                      && not (text.Contains '{' || text.Contains '}' || text.Contains '%')
                      && not (invariantMessage.IsMatch text)
                      ->
                      // the innermost enclosing function wins: it is the one
                      // whose arguments explain this particular throw
                      let enclosing =
                          functions
                          |> Seq.filter (fun f -> Range.rangeContainsRange f.BindingRange literalRange)
                          |> Seq.sortBy (fun f -> f.BindingRange.EndLine - f.BindingRange.StartLine)
                          |> Seq.tryHead

                      match enclosing with
                      | Some f when
                          text.Trim() <> f.Name
                          // a message already naming an argument was written
                          // deliberately
                          && not (f.Parameters |> List.exists (fun p -> mentionsParameter text p.idText))
                          // secrets in scope are not for the log
                          && not (sensitiveName.IsMatch f.Name)
                          && not (f.Parameters |> List.exists (fun p -> sensitiveName.IsMatch p.idText))
                          && not (enclosingNames path |> List.exists sensitiveName.IsMatch)
                          && OptionModule.resolvesToCoreOperator check source failwithIdent
                          ->
                          let functionName = f.Name

                          // the `function` shape: its one argument is quoted
                          // by naming the wildcard arm that throws
                          let implicitArm =
                              match f.Implicit with
                              | Some(nameId, body) ->
                                  match wildcardArmOf path body expr.Range with
                                  | Some wildRange when
                                      implicitArgType check source nameId |> Option.exists (printsUsefully 0)
                                      ->
                                      freshNameIn f.BindingRange
                                      |> Option.map (fun fresh -> fresh, (wildRange, "_", fresh))
                                  | _ -> None
                              | None -> None

                          let reportable =
                              (f.Parameters |> List.filter usefulParameter |> List.map (fun p -> p.idText))
                              @ (implicitArm |> Option.map fst |> Option.toList)

                          let literalText = textOfRange source literalRange

                          // the same text elsewhere in the file is somebody
                          // reading it back — a test's `should equal "..."`
                          // (Fuuga), a caller matching on the message
                          let quotedElsewhere =
                              let thrown = thrownCounts |> Map.tryFind literalText |> Option.defaultValue 1

                              let rec count (from: int) (acc: int) =
                                  let next = all.IndexOf(literalText, from, System.StringComparison.Ordinal)
                                  if next < 0 then acc else count (next + 1) (acc + 1)

                              count 0 0 > thrown

                          if
                              not reportable.IsEmpty
                              && literalText.StartsWith '"'
                              && literalText.EndsWith '"'
                              && not (literalText.StartsWith "\"\"\"")
                              && literalText.Length >= 2
                              && not quotedElsewhere
                          then
                              let reported =
                                  reportable |> List.map (fun p -> p + ": {" + p + "}") |> String.concat ", "

                              let suffix = $", calling {functionName} with {reported}"

                              { Range = literalRange
                                OriginalText = literalText
                                ReplacementText = "$" + literalText.Insert(literalText.Length - 1, suffix)
                                FunctionName = functionName
                                PatternEdit = implicitArm |> Option.map snd }
                      | _ -> ()
                  | _ -> () ]
