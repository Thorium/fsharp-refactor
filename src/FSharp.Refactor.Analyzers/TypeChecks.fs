/// Refactoring notes for runtime type comparisons (advice only):
///
///     x.GetType().Name = "Customer"        // fragile string comparison:
///                                          // renames, namespaces, generics
///                                          // all break it silently
///     x.GetType() = typeof<Customer>       // exact-type equality; often a
///                                          // type test `x :? Customer` was
///                                          // meant (which matches subtypes)
///
/// The first shape gets a "compare types, not names" note. The second gets
/// a note offering `:?` with the exact-vs-subtype caveat spelled out — the
/// two are NOT equivalent, so there is no automatic fix.
module FSharp.Refactor.TypeChecks

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type TypeCheckKind =
    /// `x.GetType().Name = "..."` / `.FullName = "..."`.
    | NameComparison of property: string
    /// `x.GetType() = typeof<T>`.
    | TypeofEquality of receiverText: string * typeText: string

type Suggestion = { Range: range; Kind: TypeCheckKind }

/// `<receiver>.GetType()` — the receiver expression.
[<return: Struct>]
let private (|GetTypeCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = UnitConst) when
        ids.Length >= 2 && (List.last ids).idText = "GetType"
        ->
        ValueSome()
    | SynExpr.App(
        isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = [ getTypeId ])); argExpr = UnitConst) when
        getTypeId.idText = "GetType"
        ->
        ValueSome()
    | _ -> ValueNone

/// `<receiver>.GetType().Name` / `.FullName` — the property name.
[<return: Struct>]
let private (|TypeNameAccess|_|) (e: SynExpr) =
    match e with
    | SynExpr.DotGet(expr = GetTypeCall; longDotId = SynLongIdent(id = [ propId ])) when
        propId.idText = "Name" || propId.idText = "FullName"
        ->
        ValueSome propId.idText
    | _ -> ValueNone

[<return: Struct>]
let private (|StringLiteral|_|) (e: SynExpr) =
    match e with
    | SynExpr.Const(SynConst.String _, _) -> ValueSome()
    | _ -> ValueNone

/// `typeof<T>` — the type argument's source text.
[<return: Struct>]
let private (|TypeofExpr|_|) (e: SynExpr) =
    match e with
    | SynExpr.TypeApp(expr = IdentName "typeof"; typeArgs = [ t ]) -> ValueSome t.Range
    | _ -> ValueNone

/// The receiver identifier of `<receiver>.GetType()` when the receiver is
/// a bare name.
let private getTypeReceiver (e: SynExpr) =
    match e with
    | SynExpr.App(funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = [ receiver; _ ]))) -> Some receiver.idText
    | SynExpr.App(funcExpr = SynExpr.DotGet(expr = SynExpr.Ident receiver)) -> Some receiver.idText
    | _ -> None

let private lastSegment (typeText: string) =
    typeText.Trim().Substring(typeText.Trim().LastIndexOf '.' + 1)

/// Find fragile runtime type comparisons.
let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // `| :? T as x when x.GetType() = typeof<T>` — the guard narrows a
    // type test to EXACTLY T, excluding subtypes on purpose: the `:?` the
    // note would offer is the very test it refines (FCS FileSystem.fs
    // retries a locked file only on a plain IOException, never on
    // FileNotFound or PathTooLong). Any clause with a `when` counts: the
    // guard may sit deeper than the top-level comparison.
    let exactTypeGuards =
        let clausesOf (e: SynExpr) =
            match e with
            | SynExpr.Match(clauses = cs)
            | SynExpr.MatchBang(clauses = cs)
            | SynExpr.MatchLambda(matchClauses = cs)
            | SynExpr.TryWith(withCases = cs) -> cs
            | _ -> []

        index.Exprs
        |> Array.collect (fun (_, e) ->
            clausesOf e
            |> List.choose (fun (SynMatchClause(pat = p; whenExpr = w)) ->
                match p, w with
                | SynPat.As(
                    lhsPat = SynPat.IsInst(pat = testedType); rhsPat = SynPat.Named(ident = SynIdent(ident = x))),
                  Some guard -> Some(x.idText, lastSegment (textOfRange source testedType.Range), guard.Range)
                | _ -> None)
            |> Array.ofList)

    let refinesTypeTest (r: range) (receiver: string option) (typeText: string) =
        match receiver with
        | Some x ->
            exactTypeGuards
            |> Array.exists (fun (bound, testedType, guardRange) ->
                bound = x
                && testedType = lastSegment typeText
                && Range.rangeContainsRange guardRange r)
        | None -> false

    [ for _, expr in index.Exprs do
          match expr with
          | SynExpr.App(funcExpr = SynExpr.App(funcExpr = IdentName "op_Equality"; argExpr = lhs); argExpr = rhs) ->
              match lhs, rhs with
              | TypeNameAccess prop, StringLiteral
              | StringLiteral, TypeNameAccess prop ->
                  { Range = expr.Range
                    Kind = TypeCheckKind.NameComparison prop }
              | (GetTypeCall as getTypeSide), TypeofExpr typeRange
              | TypeofExpr typeRange, (GetTypeCall as getTypeSide) ->
                  let typeText = textOfRange source typeRange

                  if not (refinesTypeTest expr.Range (getTypeReceiver getTypeSide) typeText) then
                      let receiverText =
                          // strip the trailing `.GetType()` for the message
                          let text = textOfRange source getTypeSide.Range
                          let cut = text.LastIndexOf ".GetType"
                          if cut > 0 then text.Substring(0, cut) else text

                      { Range = expr.Range
                        Kind = TypeCheckKind.TypeofEquality(receiverText, typeText) }
              | _ -> ()
          | _ -> () ]
