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
///     `Unchecked.defaultof<T>` names the type.
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
    | SynExpr.Ident id -> Some id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
    | _ -> None

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
    | SynExpr.Ident id -> Some id
    | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
    | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
    | _ -> None

/// Is a value of the type declared by `typeIdent` boxed, locked,
/// null-tested or defaulted anywhere in the file?
let hostileUse
    (check: FSharpCheckFileResults option)
    (index: AstIndex.Index)
    (source: ISourceText)
    (typeIdent: Ident)
    : bool =
    let byName =
        index.Exprs
        |> Array.exists (fun (_, e) ->
            match e with
            // `Unchecked.defaultof<T>`: null for the class, a zeroed value
            // for the struct - a sentinel the code compares against
            | SynExpr.TypeApp(
                expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                typeArgs = [ SynType.LongIdent(SynLongIdent(id = tids)) ]) when
                not ids.IsEmpty
                && (List.last ids).idText = "defaultof"
                && not tids.IsEmpty
                && (List.last tids).idText = typeIdent.idText
                ->
                true
            | _ -> false)

    byName
    || (match check with
        | None -> false
        | Some check ->
            let typeFullName =
                match OptionModule.symbolOfIdent check source typeIdent with
                | Some(:? FSharpEntity as entity) -> entity.TryFullName
                | _ -> None

            match typeFullName with
            | None -> false
            | Some fullName ->
                let isOfType (operand: SynExpr) =
                    match operandIdent operand with
                    | Some id ->
                        match OptionModule.symbolOfIdent check source id with
                        | Some(:? FSharpMemberOrFunctionOrValue as value) ->
                            (try
                                let t = OptionModule.stripAbbreviations value.FullType
                                t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some fullName
                             with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                 false)
                        | _ -> false
                    | None -> false

                // the implicit boxing: a value of the type handed to a
                // parameter typed `obj` (`Console.WriteLine p`,
                // `String.Format("{0}", p)`, `x.Equals p`), to `string`/`hash`,
                // or to a `%A`/`%O` hole of the printf family
                let objParameter (t: FSharpType) =
                    try
                        let t = OptionModule.stripAbbreviations t
                        t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.Object"
                    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                        false

                let boxedAtCall (e: SynExpr) =
                    match e with
                    | SynExpr.App _ ->
                        let head, args = applicationOf e

                        match calleeIdent head with
                        | Some callee when
                            printfFamily.Contains callee.idText
                            && (match args with
                                | SynExpr.Const(SynConst.String(text = fmt), _) :: _ ->
                                    fmt.Contains "%A" || fmt.Contains "%O"
                                | _ -> false)
                            ->
                            args |> List.tail |> List.exists isOfType
                        | Some callee when callee.idText = "string" || callee.idText = "hash" ->
                            args |> List.exists isOfType
                        | Some callee ->
                            match OptionModule.symbolOfIdent check source callee with
                            | Some(:? FSharpMemberOrFunctionOrValue as mfv) ->
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

                                            List.zip
                                                (List.truncate actuals.Length group)
                                                (List.truncate group.Length actuals)
                                        | _ ->
                                            List.zip
                                                (groups |> List.truncate args.Length |> List.map List.tryHead)
                                                (List.truncate groups.Length args)
                                            |> List.choose (fun (p, a) -> p |> Option.map (fun p -> p, a))

                                    pairs
                                    |> List.exists (fun (parameter, actual) ->
                                        objParameter parameter.Type && isOfType actual)
                                 with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
                                     false)
                            | _ -> false
                        | None -> false
                    | _ -> false

                index.Exprs
                |> Array.exists (fun (_, e) -> (hostileOperands e |> List.exists isOfType) || boxedAtCall e))
