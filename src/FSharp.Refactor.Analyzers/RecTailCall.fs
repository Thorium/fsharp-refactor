/// FR0131 (fix): a module-level `let rec` whose every self-call provably
/// sits in tail position gains [<TailCall>]:
///
///     let rec sum acc = function       [<TailCall>]
///                               →      let rec sum acc = function
///
/// The attribute changes no codegen — it makes the compiler emit FS3569
/// whenever a later edit pushes a recursive call OUT of tail position, so
/// it is a regression guard the function earns by construction. Because a
/// wrongly-placed attribute manufactures warnings (and breaks builds under
/// TreatWarningsAsErrors), the verification is deliberately conservative:
///
///   - tail position is tracked through parens, type ascriptions, `match`
///     arms, if/elif/else branches, `let` bodies and sequencing — nothing
///     else. A mention of the function's name inside anything unverified
///     (a lambda, try/with, a computation expression, `use` scope, a
///     `while` body, an argument, a string...) vetoes the binding.
///   - a self-call must be FULLY applied (partial application returns a
///     closure and cannot be verified) and may not carry the name in its
///     arguments. `x |> f args` counts, pipes being inlined.
///   - single non-mutual bindings only: `and`-groups need whole-group
///     analysis, so they stay untouched.
///   - no byref/inref/outref parameter and no self-call passing `&x`: the
///     compiler's tail-call checker refuses those (FS3569), so the
///     attribute would create the warning it exists to prevent.
///   - the attribute exists from FSharp.Core 8 on — a typed gate on the
///     referenced FSharp.Core version keeps the editor fix sound where
///     the CLI's verify build could not catch a missing type.
///
/// No --api-changes gate: unlike [<Literal>] the attribute is additive
/// metadata and leaves the compiled shape of a public function unchanged.
module FSharp.Refactor.RecTailCall

open System.Text.RegularExpressions
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        Range: range
        Name: string
        /// Zero-width insert point (line start of the `let`) and the
        /// attribute line.
        Fix: range * string
    }

/// [<TailCall>] ships in FSharp.Core 8.0.
let private coreHasAttribute (check: FSharpCheckFileResults) =
    try
        check.ProjectContext.GetReferencedAssemblies()
        |> List.exists (fun a ->
            a.SimpleName = "FSharp.Core"
            && (let m = Regex.Match(a.QualifiedName, @"Version=(\d+)\.")
                m.Success && int m.Groups.[1].Value >= 8))
    with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
        false

/// The application spine: `f a b c` unrolled to its head and arguments.
[<TailCall>]
let rec private spine (args: SynExpr list) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = f; argExpr = a) -> spine (a :: args) f
    | head -> head, args

/// A parameter typed `byref<_>`, `inref<_>` or `outref<_>` (any spelling:
/// prefix, postfix, qualified). The compiler's own tail-call checker
/// refuses a recursive call that passes a byref along, so [<TailCall>] on
/// such a function manufactures the very FS3569 it is meant to guard
/// against — the F# compiler's TaggedCollections.fs `tryGetValue ... (v:
/// byref<'Value>)` was attributed that way. Read from the source text so
/// no type-syntax shape slips past.
let private byrefPattern = Regex(@"\b(byref|inref|outref)\b")

let private hasByrefParameter (source: ISourceText) (pats: SynPat list) =
    pats |> List.exists (fun p -> byrefPattern.IsMatch(textOfRange source p.Range))

/// An argument spelled `&x` — the address-of the self-call hands over.
[<TailCall>]
let rec private passesAddress (arg: SynExpr) =
    match arg with
    | SynExpr.AddressOf _ -> true
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> passesAddress inner
    | _ -> false

/// What one `let rec` binding's verification needs: the source it reads
/// spans from, the function's own name, the arity a self-call must reach,
/// and the accumulator counting the qualifying self-calls found so far.
type private Ctx =
    { Source: ISourceText
      Fid: Ident
      Arity: int
      SelfCalls: int ref }

/// No mention of the function's own name anywhere in `r`. This runs on nearly
/// every subexpression of the body, which is why it goes through
/// mentionsIdentifier and not a Regex — see there.
let private mentionFree (c: Ctx) (r: range) =
    not (mentionsIdentifier (textOfRange c.Source r) c.Fid.idText)

/// One application in the body: a fully-applied self-call in tail position
/// (which the accumulator counts), or any other application, which is
/// verified only by never naming the function. `e` is the whole application
/// the head and args came from.
let private selfCall (c: Ctx) (isTail: bool) (e: SynExpr) (head: SynExpr) (args: SynExpr list) =
    match head with
    | SynExpr.Ident id when id.idText = c.Fid.idText ->
        if
            isTail
            && args.Length = c.Arity
            && args |> List.forall (fun a -> mentionFree c a.Range)
            // a self-call handing over an address
            // (`f key t &v`) is one the compiler's own
            // tail-call checker refuses (FS3569)
            && not (args |> List.exists passesAddress)
        then
            c.SelfCalls.Value <- c.SelfCalls.Value + 1
            true
        else
            false
    | _ -> mentionFree c e.Range

let rec private ok (c: Ctx) (isTail: bool) (e: SynExpr) : bool =
    match e with
    | SynExpr.Paren(expr = inner)
    | SynExpr.Typed(expr = inner) -> ok c isTail inner
    | SynExpr.Match(expr = scrut; clauses = cs) ->
        mentionFree c scrut.Range
        && cs
           |> List.forall (fun (SynMatchClause(whenExpr = w; resultExpr = r)) ->
               (match w with
                | Some g -> mentionFree c g.Range
                | None -> true)
               && ok c isTail r)
    | SynExpr.IfThenElse(ifExpr = cond; thenExpr = t; elseExpr = els) ->
        mentionFree c cond.Range
        && ok c isTail t
        && (match els with
            | Some e2 -> ok c isTail e2
            | None -> true)
    | LetOrUseE lou when not (lou.IsUse || lou.IsBang) ->
        lou.Bindings
        |> List.forall (fun (SynBinding _ as inner) -> mentionFree c inner.RangeOfBindingWithRhs)
        && ok c isTail lou.Body
    | SynExpr.Sequential(expr1 = e1; expr2 = e2) -> mentionFree c e1.Range && ok c isTail e2
    // `x |> f args` is `f args x` — pipes are inlined
    // (the operator parses as a one-segment LongIdent)
    | SynExpr.App(funcExpr = SynExpr.App(funcExpr = opE; argExpr = lhs); argExpr = rhs) when
        (match opE with
         | SynExpr.Ident i -> i.idText = "op_PipeRight"
         | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ i ])) -> i.idText = "op_PipeRight"
         | _ -> false)
        && mentionFree c lhs.Range
        ->
        let head, args = spine [] rhs
        selfCall c isTail e head (args @ [ lhs ])
    | SynExpr.App(isInfix = false) ->
        let head, args = spine [] e
        selfCall c isTail e head args
    // anything unverified — lambdas, try/with, CEs,
    // `use` scopes, loops, arguments — passes only by
    // never naming the function
    | _ -> mentionFree c e.Range

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if not (coreHasAttribute check) then
        []
    else
        let index = AstIndex.ofTree parseTree

        [ for _, decl in index.Decls do
              match decl with
              | SynModuleDecl.Let(isRecursive = true; bindings = [ binding ]) ->
                  match binding with
                  | SynBinding(
                      attributes = []
                      isInline = false
                      headPat = SynPat.LongIdent(longDotId = SynLongIdent(id = [ fid ]); argPats = SynArgPats.Pats pats)
                      expr = body
                      trivia = trivia) when not (pats.IsEmpty || hasByrefParameter source pats) ->
                      // `let rec f acc = function ...` compiles as one more
                      // curried parameter; its clause bodies ARE the tail
                      let arity, tailBodies, guardsAndScrutinees =
                          match body with
                          | SynExpr.MatchLambda(matchClauses = cs) ->
                              pats.Length + 1,
                              [ for SynMatchClause(resultExpr = r) in cs -> r ],
                              [ for SynMatchClause(whenExpr = w) in cs do
                                    match w with
                                    | Some g -> g.Range
                                    | None -> () ]
                          | _ -> pats.Length, [ body ], []

                      let c =
                          { Source = source
                            Fid = fid
                            Arity = arity
                            SelfCalls = ref 0 }

                      let allTail =
                          guardsAndScrutinees |> List.forall (mentionFree c)
                          && tailBodies |> List.forall (ok c true)

                      if allTail && c.SelfCalls.Value > 0 then
                          let kw = trivia.LeadingKeyword.Range

                          let ownLine =
                              kw.StartColumn = 0
                              || (source.GetLineString(kw.StartLine - 1)).Substring(0, kw.StartColumn).Trim() = ""

                          if ownLine then
                              let indent = String.replicate kw.StartColumn " "
                              let at = Position.mkPos kw.StartLine 0

                              { Range = fid.idRange
                                Name = fid.idText
                                Fix = Range.mkRange decl.Range.FileName at at, $"{indent}[<TailCall>]\n" }
                  | _ -> ()
              | _ -> () ]
