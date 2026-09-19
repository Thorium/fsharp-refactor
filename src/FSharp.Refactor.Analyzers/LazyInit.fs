/// FR0162 (correctness): check-then-assign on a shared mutable — the
/// hand-rolled lazy that races.
///
///     let mutable private cache: Index option = None
///     let index () =
///         if cache.IsNone then cache <- Some (build ())
///         cache.Value
///
/// A module-level (or `static let`) mutable is one slot for the whole
/// process. Two threads that both find it empty both run the factory, and
/// whichever stores last wins; a reader in between can see the other's
/// half-built value when the store is not the last thing the factory does.
/// `Lazy<T>` is the answer — `let private cache = lazy (build ())`, read
/// as `cache.Value` — thread-safe by default (ExecutionAndPublication),
/// the factory run once. FR0154 is the dictionary twin of the same race.
///
/// The shape: a module-level or static `let mutable` initialised empty
/// (`None`, `ValueNone`, `null`, `Unchecked.defaultof`) whose every
/// assignment sits under a test of its own emptiness — an `if` on
/// `x.IsNone`/`isNull x`/`x = null`/`Option.isNone x`, or the `None` arm of
/// a `match x with`. An assignment inside `lock` is guarded and stands
/// the note down for that mutable. Note only: the reads move too, and
/// where the value is reset elsewhere `Lazy` is the wrong tool.
module FSharp.Refactor.LazyInit

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The mutable's binding.
        Range: range
        Name: string
        /// The first guarded assignment, for the message.
        AssignmentRange: range
    }

[<TailCall>]
let rec private isEmpty (e: SynExpr) =
    match stripParens e with
    // `let mutable x: T = None` carries the annotation on the expression too
    | SynExpr.Typed(expr = inner) -> isEmpty inner
    | SynExpr.Null _ -> true
    | IdentName("None" | "ValueNone") -> true
    | SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))) ->
        not ids.IsEmpty && (List.last ids).idText = "defaultof"
    | _ -> false

let find (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    // a mutable born empty: its name and binding
    let emptyMutable (b: SynBinding) =
        match b with
        | SynBinding(isMutable = true; headPat = pat; expr = init) when isEmpty init ->
            match pat with
            | SynPat.Named(ident = SynIdent(ident = id))
            | SynPat.Typed(pat = SynPat.Named(ident = SynIdent(ident = id))) -> Some(id.idText, b.RangeOfBindingWithRhs)
            | _ -> None
        | _ -> None

    // module-level and static mutables born empty
    let candidates =
        [
            for _, d in index.Decls do
                match d with
                | SynModuleDecl.Let(bindings = bindings) -> yield! bindings |> List.choose emptyMutable
                | SynModuleDecl.Types(typeDefns = defns) ->
                    for SynTypeDefn(typeRepr = repr) in defns do
                        match repr with
                        | SynTypeDefnRepr.ObjectModel(members = members) ->
                            for m in members do
                                match m with
                                | SynMemberDefn.LetBindings(bindings = bindings; isStatic = true) ->
                                    yield! bindings |> List.choose emptyMutable
                                | _ -> ()
                        | _ -> ()
                | _ -> ()
        ]

    // the condition IS the emptiness test and nothing more. A compound one
    // (`isNull holder || not holder.IsValueCreated || isNull holder.Value`,
    // management-portal's reconnecting context holders) re-creates the
    // value on other grounds too, and `lazy` is not the tool for it
    let emptinessTest (name: string) (cond: SynExpr) =
        let text = (textOfRange source (stripParens cond).Range).Trim()
        let n = identifierPattern name

        System.Text.RegularExpressions.Regex.IsMatch(
            text,
            "^("
            + $@"isNull\s*\(?\s*(box\s+)?{n}\s*\)?"
            + $@"|{n}\s*\.\s*IsNone"
            + $@"|{n}\s*=\s*null"
            + $@"|null\s*=\s*{n}"
            + $@"|Option\.isNone\s+{n}"
            + $@"|{n}\s*\|>\s*Option\.isNone"
            + $@"|(obj|Object)\.ReferenceEquals\s*\(\s*{n}\s*,\s*null\s*\)"
            + ")$"
        )

    // the `None`/`null` arm of a match on the mutable
    let emptyArmOf (name: string) (e: SynExpr) (assignment: range) =
        match e with
        | SynExpr.Match(expr = SynExpr.Ident id; clauses = clauses) when id.idText = name ->
            clauses
            |> List.exists (fun (SynMatchClause(pat = pat; resultExpr = result)) ->
                Range.rangeContainsRange result.Range assignment
                && (match pat with
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = [ c ])) ->
                        c.idText = "None" || c.idText = "ValueNone"
                    | SynPat.Null _ -> true
                    | _ -> false))
        | _ -> false

    // an assignment under a test of the mutable's emptiness, or under a
    // lock (guarded, no race)
    let classify (name: string) (path: SyntaxNode list) (assignment: range) =
        // `lock gate (fun () -> ...)` and `lock gate <| fun () -> ...` alike
        let rec headIsLock (e: SynExpr) =
            match e with
            | SynExpr.App(funcExpr = SynExpr.App(isInfix = true; funcExpr = SingleIdent op; argExpr = left)) when
                op.idText = "op_PipeLeft"
                ->
                headIsLock left
            | SynExpr.App(funcExpr = f) -> headIsLock f
            | SynExpr.Ident lock' -> lock'.idText = "lock"
            | _ -> false

        let guardedByLock =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.App _ as app) -> headIsLock app
                | _ -> false)

        let underTest =
            path
            |> List.exists (fun node ->
                match node with
                | SyntaxNode.SynExpr(SynExpr.IfThenElse(ifExpr = cond; thenExpr = thenE)) ->
                    Range.rangeContainsRange thenE.Range assignment && emptinessTest name cond
                | SyntaxNode.SynExpr m -> emptyArmOf name m assignment
                | _ -> false)

        guardedByLock, underTest

    // a test file's fixtures are one thread's; nothing races there
    let candidates = if AstIndex.isTestFile index source then [] else candidates

    [
        for name, bindingRange in candidates do
            // every store, qualified (`M.cache <- ...`) or not
            let assignments =
                index.Exprs
                |> Array.choose (fun (path, e) ->
                    match e with
                    | SynExpr.LongIdentSet(SynLongIdent(id = ids), _, _) when
                        not ids.IsEmpty && (List.last ids).idText = name
                        ->
                        Some(path, e.Range)
                    | _ -> None)

            if not (Array.isEmpty assignments) then
                let classified = assignments |> Array.map (fun (path, r) -> r, classify name path r)

                let anyLocked = classified |> Array.exists (fun (_, (locked, _)) -> locked)
                let allTested = classified |> Array.forall (fun (_, (_, tested)) -> tested)

                if allTested && not anyLocked then
                    {
                        Range = bindingRange
                        Name = name
                        AssignmentRange = fst classified.[0]
                    }
    ]
