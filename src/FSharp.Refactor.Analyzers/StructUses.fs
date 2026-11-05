/// What makes a struct WORSE than the class it would replace — shared by
/// FR0016 (unions) and FR0070 (records), the F# reading of CSharp.Refactor's
/// CR0081 `structHostile` and its 32-byte cap.
///
/// A `[<Struct>]` saves one allocation per instance and pays for it with a
/// copy per pass. Two things turn that trade around:
///
///   - SIZE: a record of four `decimal`s is 64 bytes, copied on every
///     assignment and argument; the allocation it saved was one 80-byte
///     object. The cap is 32 bytes inline, CR0081's.
///   - a use that BOXES the value back: `box x`, `x :> obj`, an interface
///     cast, `Object.ReferenceEquals`, an `isNull` / `= null` test
///     (meaningless on a struct, and FS0043 once it is one), a `lock x`
///     (FS0001 on a struct: `lock` wants a reference type). Each such site
///     allocates the very object the attribute removed, or stops compiling.
///     The typed check reads the operand's type where the operand is a
///     name or a dotted path, and follows the implicit boxing too: a value
///     handed to a parameter typed `obj` (`Console.WriteLine p`), to
///     `string`/`hash`, or to a `%A`/`%O` hole of the printf family. A
///     `Unchecked.defaultof<T>` names the type. So does anything that takes
///     reference types only (`where T : class`, F#'s `not struct`), as
///     `AddSingleton`, `IOptions<T>` and `Volatile.Write` do, whether it is
///     given a value or named a type argument: the call stops compiling.
///     The same scan reads the project's other files and, under
///     `--api-changes`, the sibling projects (see ProjectSources).
///
/// Without check results only the size cap and the type-named shapes apply;
/// the parse-only callers (the property suite) see exactly that.
module FSharp.Refactor.StructUses

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

/// Bytes a small value type occupies inline, by its F# or BCL name. The
/// names are the two rules' whitelists; anything else is not a candidate
/// field and answers nothing.
let private sizes =
    Map.ofList
        [
            "bool", 1
            "byte", 1
            "sbyte", 1
            "int8", 1
            "uint8", 1
            "char", 2
            "int16", 2
            "uint16", 2
            "int", 4
            "int32", 4
            "uint", 4
            "uint32", 4
            "float32", 4
            "single", 4
            "int64", 8
            "uint64", 8
            "float", 8
            "double", 8
            "nativeint", 8
            "unativeint", 8
            "DateTime", 8
            "TimeSpan", 8
            "decimal", 16
            "Guid", 16
            "DateTimeOffset", 16
        ]

let private lastName (t: SynType) =
    match t with
    | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> Some (List.last ids).idText
    | _ -> None

/// The inline size of a field type: a known value type, or a `voption` of
/// one (its payload beside an `int` tag).
let private sizeOf (t: SynType) =
    match t with
    | SynType.App(typeName = name; typeArgs = [ elem ]) when
        (lastName name = Some "voption" || lastName name = Some "ValueOption")
        ->
        lastName elem |> Option.bind sizes.TryFind |> Option.map (fun s -> s + 4)
    | _ -> lastName t |> Option.bind sizes.TryFind

/// CR0081's cap: a struct bigger than this copies slower than it allocates.
[<Literal>]
let inlineByteCap = 32

/// Do these field types fit the cap? A type the table does not know
/// (the caller's whitelist should have refused it already) does not.
let fitsInline (fieldTypes: SynType list) =
    let known = fieldTypes |> List.choose sizeOf

    known.Length = fieldTypes.Length && List.sum known <= inlineByteCap

/// The identifier an operand ultimately reads: `x` in `x`, `p.Point` in
/// `p.Point`, through parentheses and annotations.
[<TailCall>]
let rec private operandIdent (e: SynExpr) =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> operandIdent inner
    | SynExpr.Ident pid -> ValueSome pid
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// The operands the hostile shapes put a value in: `box e`, `lock e`,
/// `isNull e`, `e :> T`, `e = null`, `null = e`, `ReferenceEquals(a, b)`.
let private hostileOperands (e: SynExpr) : SynExpr list =
    match e with
    | SynExpr.Upcast(expr = inner) -> [ inner ]
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident f; argExpr = arg) when
        f.idText = "box" || f.idText = "lock" || f.idText = "isNull"
        ->
        [ arg ]
    | SynExpr.App(
        isInfix = false
        funcExpr = SynExpr.App(isInfix = true; funcExpr = IdentName "op_Equality"; argExpr = lhs)
        argExpr = rhs) ->
        match stripParens lhs, stripParens rhs with
        | SynExpr.Null _, other
        | other, SynExpr.Null _ -> [ other ]
        | _ -> []
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = arg) when
        not ids.IsEmpty && (List.last ids).idText = "ReferenceEquals"
        ->
        match stripParens arg with
        | SynExpr.Tuple(exprs = es) -> es
        | single -> [ single ]
    | _ -> []

/// The `printf` family: a `%A`/`%O` hole boxes its argument.
let private printfFamily =
    set
        [
            "printf"
            "printfn"
            "eprintf"
            "eprintfn"
            "sprintf"
            "failwithf"
            "fprintf"
            "fprintfn"
            "bprintf"
            "kprintf"
        ]

/// The application chain's head and its arguments, outermost application
/// last: `f a b` → (f, [a; b]); `x.M(a, b)` → (x.M, [(a, b)]).
let private applicationOf (e: SynExpr) =
    let rec unwind (e: SynExpr) (args: SynExpr list) =
        match e with
        | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) -> unwind f (a :: args)
        | SynExpr.TypeApp(expr = inner) -> unwind inner args
        | head -> head, args

    unwind e []

/// The identifier a callee spells: `f`, `x.M`, `Console.WriteLine`.
let private calleeIdent (head: SynExpr) =
    match head with
    | SynExpr.Ident pid -> ValueSome pid
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> ValueSome(List.last ids)
    | _ -> ValueNone

/// The type names a `Unchecked.defaultof<T>` spells anywhere in the file:
/// null for the class, a zeroed value for the struct - a sentinel the code
/// compares against.
let private defaultofNames (index: AstIndex.Index) : Set<string> =
    index.Exprs
    |> Array.choose (fun (_, e) ->
        match e with
        | SynExpr.TypeApp(
            expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
            typeArgs = [ SynType.LongIdent(SynLongIdent(id = tids)) ]) when
            not ids.IsEmpty && (List.last ids).idText = "defaultof" && not tids.IsEmpty
            ->
            Some (List.last tids).idText
        | _ -> None)
    |> Set.ofArray

/// Does this generic parameter take reference types only (`where T : class`, F#'s `not struct`)?
let private takesReferenceTypesOnly (parameter: FSharpGenericParameter) =
    parameter.Constraints |> Seq.exists _.IsReferenceTypeConstraint

/// The full names of every type whose value a file boxes, locks, null-tests or hands to an `obj` parameter, or that goes
/// where reference types only are taken: given as an argument, or named as a type argument. `symbolsAt` answers what an
/// identifier resolved to, so this reads a file of this compilation and one of a sibling project alike.
let hostileNamesIn (symbolsAt: Ident -> FSharpSymbol list) (index: AstIndex.Index) : Set<string> =
    let methodAt (pid: Ident) =
        symbolsAt pid
        |> List.tryPick (fun symbol ->
            match symbol with
            | :? FSharpMemberOrFunctionOrValue as mfv -> Some mfv
            | _ -> None)

    let rec typeOfOperand (operand: SynExpr) =
        match stripParens operand with
        | SynExpr.Typed(expr = inner) -> typeOfOperand inner
        | SynExpr.Record(copyInfo = Some(copied, _)) -> typeOfOperand copied
        // a record literal names its type through its fields
        | SynExpr.Record(recordFields = SynExprRecordField(fieldName = (SynLongIdent(id = ids), _)) :: _) when
            not ids.IsEmpty
            ->
            symbolsAt (List.last ids)
            |> List.tryPick (fun symbol ->
                match symbol with
                | :? FSharpField as field -> field.DeclaringEntity |> Option.bind _.TryFullName
                | _ -> None)
        | plain ->
            match operandIdent plain with
            | ValueSome pid ->
                match methodAt pid with
                | Some value ->
                    (try
                        let t = OptionModule.stripAbbreviations value.FullType

                        if t.HasTypeDefinition then
                            t.TypeDefinition.TryFullName
                        else
                            None
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         None)
                | None -> None
            | ValueNone -> None

    /// Can `typeOfOperand` read this at all? Without one, the callee's typed lookup finds nothing to report.
    let readable (operand: SynExpr) =
        match stripParens operand with
        | SynExpr.Record _ -> true
        | plain -> (operandIdent plain).IsSome

    let entityNameOf (t: SynType) =
        match t with
        | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty ->
            symbolsAt (List.last ids)
            |> List.tryPick (fun symbol ->
                match symbol with
                | :? FSharpEntity as entity -> entity.TryFullName
                | _ -> None)
        | _ -> None

    /// The type arguments that sit where reference types only are taken. A type's own parameters can come before a method's,
    /// so the two lists line up from the end.
    let namedInReferenceOnly (parameters: FSharpGenericParameter list) (arguments: SynType list) =
        if parameters.Length < arguments.Length then
            []
        else
            List.zip (List.skip (parameters.Length - arguments.Length) parameters) arguments
            |> List.choose (fun (parameter, argument) ->
                if takesReferenceTypesOnly parameter then
                    entityNameOf argument
                else
                    None)

    let namedInExpression (e: SynExpr) =
        match e with
        | SynExpr.TypeApp(expr = callee; typeArgs = arguments) ->
            match calleeIdent callee with
            | ValueSome pid ->
                match methodAt pid with
                | Some mfv ->
                    (try
                        namedInReferenceOnly (List.ofSeq mfv.GenericParameters) arguments
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         [])
                | None -> []
            | ValueNone -> []
        | _ -> []

    let namedInType (t: SynType) =
        match t with
        | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)); typeArgs = arguments) when not ids.IsEmpty ->
            symbolsAt (List.last ids)
            |> List.collect (fun symbol ->
                match symbol with
                | :? FSharpEntity as entity ->
                    (try
                        namedInReferenceOnly (List.ofSeq entity.GenericParameters) arguments
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         [])
                | _ -> [])
        | _ -> []

    // the implicit boxing: a value handed to a parameter typed `obj`
    // (`Console.WriteLine p`, `String.Format("{0}", p)`, `x.Equals p`), to
    // `string`/`hash`, or to a `%A`/`%O` hole of the printf family
    let objParameter (t: FSharpType) =
        try
            let t = OptionModule.stripAbbreviations t
            t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Object"
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    let referenceTypesOnly (t: FSharpType) =
        try
            t.IsGenericParameter
            && t.GenericParameter.Constraints |> Seq.exists _.IsReferenceTypeConstraint
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false

    let boxedAtCall (e: SynExpr) : SynExpr list =
        match e with
        | SynExpr.App _ ->
            let head, args = applicationOf e

            match calleeIdent head with
            | ValueSome callee when
                printfFamily.Contains callee.idText
                && (match args with
                    | SynExpr.Const(SynConst.String(text = fmt), _) :: _ -> fmt.Contains "%A" || fmt.Contains "%O"
                    | _ -> false)
                ->
                List.tail args
            | ValueSome callee when callee.idText = "string" || callee.idText = "hash" -> args
            // a name or a record literal among the arguments (or a tuple's
            // elements) has a type `typeOfOperand` reads: without one, the
            // callee's typed lookup - one per application of the file - finds nothing
            | ValueSome _ when
                not (
                    args
                    |> List.exists (fun a ->
                        readable a
                        || (match stripParens a with
                            | SynExpr.Tuple(exprs = es) -> es |> List.exists readable
                            | _ -> false))
                )
                ->
                []
            | ValueSome callee ->
                match methodAt callee with
                | Some mfv ->
                    (try
                        let groups = mfv.CurriedParameterGroups |> Seq.map List.ofSeq |> List.ofSeq

                        // one tupled group: the arguments by position;
                        // curried groups: one argument each
                        let pairs =
                            match groups, args with
                            | [ group ], [ single ] ->
                                let actuals =
                                    match stripParens single with
                                    | SynExpr.Tuple(exprs = es) -> es
                                    | other -> [ other ]

                                List.zip (List.truncate actuals.Length group) (List.truncate group.Length actuals)
                            | _ ->
                                List.zip
                                    (groups |> List.truncate args.Length |> List.map List.tryHead)
                                    (List.truncate groups.Length args)
                                |> List.choose (fun (p, a) -> p |> Option.map (fun p -> p, a))

                        pairs
                        |> List.choose (fun (parameter, actual) ->
                            if objParameter parameter.Type || referenceTypesOnly parameter.Type then
                                Some actual
                            else
                                None)
                     with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                         [])
                | None -> []
            | ValueNone -> []
        | _ -> []

    Set.unionMany
        [
            index.Exprs
            |> Seq.collect (fun (_, e) -> hostileOperands e @ boxedAtCall e)
            |> Seq.choose typeOfOperand
            |> Set.ofSeq

            index.Exprs |> Seq.collect (snd >> namedInExpression) |> Set.ofSeq
            index.Types |> Seq.collect (snd >> namedInType) |> Set.ofSeq
        ]

let private defaultofCache =
    System.Runtime.CompilerServices.ConditionalWeakTable<AstIndex.Index, Set<string>>()

let private hostileCache =
    System.Runtime.CompilerServices.ConditionalWeakTable<FSharpCheckFileResults, Set<string>>()

/// How the type declared by `typeIdent` is used outside this file, as far as the host can tell.
let outsideUse (check: FSharpCheckFileResults option) (source: ISourceText) (typeIdent: Ident) =
    match check with
    | None -> ProjectSources.OutsideStructUse.Clear
    | Some check ->
        match OptionModule.symbolOfIdent check source typeIdent with
        | Some(:? FSharpEntity as entity) when not entity.Accessibility.IsPrivate ->
            match entity.TryFullName with
            | Some fullName -> ProjectSources.outsideStructUse typeIdent.idText fullName entity.Accessibility.IsPublic
            | None -> ProjectSources.OutsideStructUse.Clear
        | _ -> ProjectSources.OutsideStructUse.Clear

/// Is a value of the type declared by `typeIdent` boxed, locked,
/// null-tested or defaulted anywhere in the file, or used in a way
/// a struct can't take outside it?
let hostileUse
    (check: FSharpCheckFileResults option)
    (index: AstIndex.Index)
    (source: ISourceText)
    (typeIdent: Ident)
    : bool =
    (defaultofCache.GetValue(index, defaultofNames)).Contains typeIdent.idText
    || (match check with
        | None -> false
        | Some check ->
            match OptionModule.symbolOfIdent check source typeIdent with
            | Some(:? FSharpEntity as entity) ->
                match entity.TryFullName with
                | Some fullName ->
                    hostileCache
                        .GetValue(
                            check,
                            fun check ->
                                hostileNamesIn
                                    (fun pid -> OptionModule.symbolOfIdent check source pid |> Option.toList)
                                    index
                        )
                        .Contains
                        fullName
                | None -> false
            | _ -> false)
    || outsideUse check source typeIdent = ProjectSources.OutsideStructUse.Hostile
