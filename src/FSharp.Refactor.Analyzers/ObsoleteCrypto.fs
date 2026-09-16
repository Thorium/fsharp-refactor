/// FR0128 (fix): the obsolete *Managed / *CryptoServiceProvider crypto
/// constructors become the static factories — SAME algorithm, so the
/// rewrite is behavior-preserving:
///
///     new SHA256Managed()              SHA256.Create()
///     new AesCryptoServiceProvider()   Aes.Create()
///     new RNGCryptoServiceProvider()   RandomNumberGenerator.Create()
///
/// .NET marked the whole family [<Obsolete>] (SYSLIB0021/0023): the
/// factories pick the platform implementation. Weak algorithms (MD5,
/// DES...) still get their FR0065 note — this rule only modernizes the
/// spelling, it does not bless the algorithm.
module FSharp.Refactor.ObsoleteCrypto

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        ObsoleteName: string
        Replacement: string
    }

let private factories =
    dict
        [
            "MD5CryptoServiceProvider", "MD5"
            "SHA1CryptoServiceProvider", "SHA1"
            "SHA1Managed", "SHA1"
            "SHA256CryptoServiceProvider", "SHA256"
            "SHA256Managed", "SHA256"
            "SHA384CryptoServiceProvider", "SHA384"
            "SHA384Managed", "SHA384"
            "SHA512CryptoServiceProvider", "SHA512"
            "SHA512Managed", "SHA512"
            "AesCryptoServiceProvider", "Aes"
            "AesManaged", "Aes"
            "TripleDESCryptoServiceProvider", "TripleDES"
            "DESCryptoServiceProvider", "DES"
            "RC2CryptoServiceProvider", "RC2"
            "RNGCryptoServiceProvider", "RandomNumberGenerator"
        ]

let private replacementFor (ids: Ident list) =
    match factories.TryGetValue (List.last ids).idText with
    | true, factory ->
        let prefix =
            ids
            |> List.take (ids.Length - 1)
            |> List.map (fun i -> i.idText + ".")
            |> String.concat ""

        ValueSome((List.last ids).idText, $"{prefix}{factory}.Create()")
    | _ -> ValueNone

let private sites (parseTree: ParsedInput) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    [
        for _, e in index.Exprs do
            match e with
            // new SHA256Managed()
            | SynExpr.New(targetType = SynType.LongIdent(SynLongIdent(id = ids)); expr = arg) when
                not ids.IsEmpty
                && (match stripParens arg with
                    | SynExpr.Const(SynConst.Unit, _) -> true
                    | _ -> false)
                ->
                match replacementFor ids with
                | ValueSome(name, replacement) ->
                    {
                        Range = e.Range
                        ObsoleteName = name
                        Replacement = replacement
                    }
                | ValueNone -> ()
            // SHA256Managed() without new
            | SynExpr.App(
                isInfix = false
                funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                argExpr = SynExpr.Const(SynConst.Unit, _)) when not ids.IsEmpty ->
                match replacementFor ids with
                | ValueSome(name, replacement) ->
                    {
                        Range = e.Range
                        ObsoleteName = name
                        Replacement = replacement
                    }
                | ValueNone -> ()
            | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident ctor; argExpr = SynExpr.Const(SynConst.Unit, _)) ->
                match replacementFor [ ctor ] with
                | ValueSome(name, replacement) ->
                    {
                        Range = e.Range
                        ObsoleteName = name
                        Replacement = replacement
                    }
                | ValueNone -> ()
            | _ -> ()
    ]

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    // The factories return the BASE type (SHA256.Create() : SHA256, not
    // SHA256Managed), so any OTHER mention of the obsolete name — a type
    // annotation, a `:?` test, typeof<>, a generic argument — can break the
    // build or change a type test's meaning. Each rewrite site mentions the
    // name exactly once; any surplus textual mention vetoes that name.
    let candidates = sites parseTree

    match candidates with
    | [] -> []
    | _ ->
        let text =
            System.String.Join("\n", [| for i in 0 .. source.GetLineCount() - 1 -> source.GetLineString i |])

        let mentions name =
            System.Text.RegularExpressions.Regex.Matches(text, $@"\b{name}\b").Count

        candidates
        |> List.groupBy (fun s -> s.ObsoleteName)
        |> List.collect (fun (name, group) -> if mentions name = group.Length then group else [])
