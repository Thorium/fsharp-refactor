/// FR0170 (performance): a loop over a dictionary's keys that looks every
/// key up again.
///
///     for k in d.Keys do                 for KeyValue(k, v) in d do
///         use k d.[k]              →         use k v
///
/// `d.[k]` hashes the key and probes the table once per iteration for a
/// value the enumerator already had in hand: `KeyValue` reads the pair.
/// CSharp.Refactor's CR0032 (`foreach (var (k, v) in d)`).
///
/// Guards: `d` is a name or a dotted read typed `Dictionary<K,V>`,
/// `IDictionary<K,V>` or `IReadOnlyDictionary<K,V>` (never a concurrent
/// one: its `Keys` is a snapshot where its enumerator is live, and the
/// two disagree under a writer); the loop variable is a plain name; the
/// body reads `d.[k]` / `d[k]` at least once and never stores through the
/// indexer, and never rebinds `k` (a `d.[k]` under a `let k = ...` reads
/// another key), and no read sits under a lambda, `lazy`, computation
/// expression or object expression inside the body (it runs later, against
/// the dictionary as it is then, where `v` is a snapshot); `k` read as a
/// plain value is fine, `KeyValue(k, v)` binds it;
/// the value name is `value`, else `v`, else `v1`, unused in the enclosing
/// binding. Every read converts together with the header.
///
/// `v` is the value when the iteration STARTED; `d.[k]` is the value when
/// the read runs. Since .NET Core 3.0 an overwrite or a `Remove` no longer
/// breaks the enumeration, so a write to the dictionary before a read in
/// the same iteration makes the two differ. The rule fixes by default and
/// stands down only on what it positively sees write, or hand out, the
/// dictionary before a read: the receiver named other than by a read or a
/// read-only member (`bump d k`, `d.Remove k`, `let m = d`), the receiver's
/// name rebound or reassigned, a store through a value of this file bound
/// to the receiver (`let view = d` then `view.[k] <- 0`), and a function,
/// member, getter, active pattern or forced value (a `seq { }`, an async, a
/// lazy, a function value) DEFINED IN THIS FILE whose body touches a
/// dictionary - names a dictionary-typed value or parameter, stores through
/// one, or calls or forces another such definition, a few levels deep. A
/// call the analysis cannot see into - a helper defined elsewhere, an
/// interface, a delegate, an event, a virtual, the BCL - is taken as
/// harmless: that is the accepted residual, user code behind such a call
/// writing the very dictionary the loop walks. In a `seq { }` or `task { }`
/// the consumer or another task runs at each `yield`, `let!`, `do!` and
/// `match!`, and an else-less `if` or a loop with a value is an implicit
/// yield; a unit statement is not, and a list comprehension runs nothing
/// between. Only what runs BEFORE a read counts: a call's arguments run
/// before the call (`use k d.[k]` converts), while a getter runs where it
/// is read, argument or not. Inside a loop nested around a read, at any
/// depth, every such write counts, since the next round runs it first; a
/// read inside a local function runs when it is called and keeps the loop.
/// A dotted receiver whose getter, defined in this file, builds a
/// dictionary hands each read another one and keeps the loop.
module FSharp.Refactor.DictKeysLoop

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    {
        /// The loop header's `k in d.Keys` span, for the message.
        Range: range
        KeyName: string
        ValueName: string
        /// The header edit and one per indexer read: (range, original, replacement).
        Edits: (range * string * string) list
    }

/// When a name in the loop body may run code that writes the dictionary.
type private Effect =
    /// Never.
    | Safe
    /// Where it is evaluated: a user getter, a constructor.
    | InPlace
    /// When the call it heads, or is handed to, runs.
    | Called

let private dictionaryTypes =
    set
        [
            "System.Collections.Generic.Dictionary`2"
            "System.Collections.Generic.IDictionary`2"
            "System.Collections.Generic.IReadOnlyDictionary`2"
            "System.Collections.Generic.SortedDictionary`2"
        ]

let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        let symbolOf (id: Ident) =
            let r = id.idRange
            let lineText = source.GetLineString(r.EndLine - 1)

            OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ id.idText ])
            |> Option.map (fun u -> u.Symbol)

        // the dictionary's type, from the last identifier of its spelling
        let isDictionary (id: Ident) =
            match symbolOf id with
            | Some(:? FSharpMemberOrFunctionOrValue as mfv) ->
                (try
                    let t = OptionModule.stripAbbreviations mfv.FullType

                    t.HasTypeDefinition
                    && (t.TypeDefinition.TryFullName |> Option.exists dictionaryTypes.Contains)
                 with _ -> // an unreadable type is no dictionary of ours; fsharpanalyzer: ignore-line FR0055
                     false)
            | Some(:? FSharpField as f) ->
                (try
                    let t = OptionModule.stripAbbreviations f.FieldType

                    t.HasTypeDefinition
                    && (t.TypeDefinition.TryFullName |> Option.exists dictionaryTypes.Contains)
                 with _ -> // fsharpanalyzer: ignore-line FR0055
                     false)
            | _ -> false

        // `d.Keys` where `d` is a name or a dotted read: the receiver's
        // identifiers and its text
        let keysOf (e: SynExpr) =
            match stripParens e with
            | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when
                ids.Length >= 2 && (List.last ids).idText = "Keys"
                ->
                let receiver = ids |> List.take (ids.Length - 1)
                Some(receiver, identText receiver)
            | SynExpr.DotGet(expr = receiver; longDotId = SynLongIdent(id = [ keys ])) when keys.idText = "Keys" ->
                match receiver with
                | SynExpr.Ident id -> Some([ id ], id.idText)
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(ids, identText ids)
                | _ -> None
            | _ -> None

        // `d.[k]` / `d[k]` with the same receiver text and the loop key
        let indexerRead (receiverText: string) (key: string) (e: SynExpr) =
            let keyIs (arg: SynExpr) =
                match stripParens arg with
                | SynExpr.Ident id -> id.idText = key
                | _ -> false

            match e with
            | SynExpr.DotIndexedGet(objectExpr = obj; indexArgs = arg) ->
                textOfRange source obj.Range = receiverText && keyIs arg
            // F# 6 `d[k]`: an application of the receiver to a list literal
            | SynExpr.App(
                isInfix = false; funcExpr = obj; argExpr = SynExpr.ArrayOrListComputed(isArray = false; expr = arg)) ->
                textOfRange source obj.Range = receiverText && keyIs arg
            | _ -> false

        // every symbol use of the file, by where it ends, collected once: a
        // loop body's names resolved one lookup each cost ~100 ms a loop
        let usesByEnd =
            lazy
                (let table =
                    System.Collections.Generic.Dictionary<struct (int * int), ResizeArray<FSharpSymbol>>()

                 try
                     for u in check.GetAllUsesOfAllSymbolsInFile() do
                         let key = struct (u.Range.EndLine, u.Range.EndColumn)

                         match table.TryGetValue key with
                         | true, l -> l.Add u.Symbol
                         | false, _ -> table.[key] <- ResizeArray [ u.Symbol ]
                 with _ -> // the per-name lookup below answers instead; fsharpanalyzer: ignore-line FR0055
                     ()

                 table)

        let resolve (ids: Ident list) =
            let last = List.last ids
            let r = last.idRange

            let tabled =
                match usesByEnd.Value.TryGetValue(struct (r.EndLine, r.EndColumn)) with
                | true, symbols ->
                    // an operator's ident is `op_Addition`, its display `(+)`
                    symbols
                    |> Seq.tryFind (fun s ->
                        s.DisplayName = last.idText
                        || (match s with
                            | :? FSharpMemberOrFunctionOrValue as v -> v.LogicalName = last.idText
                            | _ -> false))
                | false, _ -> None

            match tabled with
            | Some _ -> tabled
            | None ->
                let lineText = source.GetLineString(r.EndLine - 1)

                OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, ids |> List.map (fun i -> i.idText))
                |> Option.map (fun u -> u.Symbol)

        // the members of a dictionary that only read it
        let readOnlyMembers =
            set
                [
                    "Count"
                    "ContainsKey"
                    "ContainsValue"
                    "Contains"
                    "TryGetValue"
                    "Keys"
                    "Values"
                    "Comparer"
                    "CopyTo"
                    "GetEnumerator"
                    "GetValueOrDefault"
                ]

        // the types another name for this dictionary may have: a write
        // through one of them may be a write to it
        let aliasTypes =
            set
                [
                    "System.Collections.Generic.Dictionary`2"
                    "System.Collections.Generic.IDictionary`2"
                    "System.Collections.Generic.SortedDictionary`2"
                    "System.Collections.Generic.ICollection`1"
                    "System.Collections.IDictionary"
                ]

        // signed by the framework, not a package that merely keeps the
        // System namespace (System.Reactive's `Subject.OnNext` runs its
        // subscribers). The key, not the path: netstandard and the .NET
        // Framework reference assemblies come from the NuGet cache too
        let frameworkKeys =
            [
                "b77a5c561934e089"
                "b03f5f7f11d50a3a"
                "cc7b13ffcd2ddd51"
                "31bf3856ad364e35"
                "7cec85d7bea7798e"
            ]

        let fromFramework (symbol: FSharpSymbol) =
            try
                let name = symbol.Assembly.QualifiedName
                frameworkKeys |> List.exists (fun key -> name.Contains("PublicKeyToken=" + key))
            with _ -> // an unreadable assembly is no proof; fsharpanalyzer: ignore-line FR0055
                false

        // WHEN a name may write the dictionary: never, or when the call it
        // heads or is handed to runs (`Called`). Only what the analysis
        // positively sees counts - the receiver itself named other than by a
        // read, and a function, value, member or active pattern of THIS FILE
        // whose definition touches a dictionary (names a dictionary-typed
        // value or parameter, stores through one, forces a sequence or calls
        // a function that does, a few levels deep). Everything else - a
        // helper defined elsewhere, an interface call, a delegate, an event,
        // the BCL - is harmless by default: a fix, with a note only on a
        // detected edge. The residual is user code behind a call the analysis
        // cannot see into that writes the very dictionary the loop walks
        let isStore (e: SynExpr) =
            match e with
            | SynExpr.LongIdentSet _
            | SynExpr.DotSet _
            | SynExpr.Set _
            | SynExpr.DotIndexedSet _
            | SynExpr.NamedIndexedPropertySet _
            | SynExpr.DotNamedIndexedPropertySet _ -> true
            | _ -> false

        // a dictionary type by name - never its nested key or value
        // collection or enumerator, which cannot write it
        let dictionaryName (n: string) =
            aliasTypes.Contains n
            || (n.Contains "Dictionary"
                && not (n.EndsWith "Collection" || n.EndsWith "Enumerator" || n.Contains '+'))

        let dictionaryTyped (t: FSharpType) =
            try
                let t = OptionModule.stripAbbreviations t

                t.HasTypeDefinition
                && (t.TypeDefinition.TryFullName |> Option.exists dictionaryName)
            with _ -> // fsharpanalyzer: ignore-line FR0055
                true

        let fromCore (x: FSharpSymbol) =
            (OptionModule.fullNameOf x).StartsWith "Microsoft.FSharp."

        // the body of this file a symbol names - a `let` value or function,
        // a member, a class `let`, an active pattern - to read what a call
        // visibly does
        let bodiesDeclaredAt (symbol: FSharpSymbol) =
            OptionModule.bodiesBoundAt index parseTree.FileName symbol |> List.map fst

        // the bodies a use of a symbol runs: a property's getter when read,
        // its setter when stored to; anything else all of them
        let bodiesRunBy (store: bool) (symbol: FSharpSymbol) =
            let bodies = OptionModule.bodiesBoundAt index parseTree.FileName symbol

            match symbol with
            | :? FSharpMemberOrFunctionOrValue as v when v.IsProperty ->
                bodies
                |> List.choose (fun (body, setter) -> if setter = store then Some body else None)
            | _ -> bodies |> List.map fst

        // does a definition of this file touch a dictionary? Decided once per
        // symbol and access; a cycle reads as no
        let touches = System.Collections.Generic.Dictionary<string, bool>()

        let rec touchesDictionary (depth: int) (store: bool) (symbol: FSharpSymbol) : bool =
            let key =
                try
                    match symbol.DeclarationLocation with
                    | Some l -> $"{symbol.FullName}@{l.FileName}:{l.StartLine}:{l.StartColumn}:{store}"
                    | None -> ""
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    ""

            if key = "" then
                false
            else
                match touches.TryGetValue key with
                | true, known -> known
                | false, _ ->
                    touches.[key] <- false

                    // a dictionary read through a read-only member
                    // (`table.ContainsKey k`) is no touch: what follows
                    // reads its value
                    let bodyTouches (body: SynExpr) =
                        AstIndex.exprsWithin index body.Range
                        |> Array.exists (fun (_, e) ->
                            Range.rangeContainsRange body.Range e.Range
                            && (match e with
                                | SynExpr.Ident id -> touchesName depth [ id ]
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                    [ 1 .. ids.Length ]
                                    |> List.exists (fun n ->
                                        not (n < ids.Length && readOnlyMembers.Contains (List.item n ids).idText)
                                        && touchesName depth (List.take n ids))
                                | _ -> false))

                    let answer =
                        (bodiesRunBy store symbol |> List.exists bodyTouches)
                        || (assignedBodies symbol |> Array.exists bodyTouches)

                    touches.[key] <- answer
                    answer

        // what a `let mutable` hook is assigned anywhere in this file: `hook
        // <- fun () -> d.Clear()` two lines above the loop runs that body
        // when `hook ()` does, whatever the definition said
        and assignedBodies (symbol: FSharpSymbol) : SynExpr[] =
            match symbol with
            | :? FSharpMemberOrFunctionOrValue as v when v.IsMutable ->
                let declared =
                    try
                        symbol.DeclarationLocation
                    with _ -> // fsharpanalyzer: ignore-line FR0055
                        None

                let same (id: Ident) =
                    id.idText = v.DisplayName
                    && (match resolve [ id ] with
                        | Some target ->
                            (try
                                target.DeclarationLocation = declared
                             with _ -> // fsharpanalyzer: ignore-line FR0055
                                 false)
                        | None -> false)

                index.Exprs
                |> Array.choose (fun (_, e) ->
                    match e with
                    | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids); expr = rhs) when
                        not ids.IsEmpty && same (List.last ids)
                        ->
                        Some rhs
                    | SynExpr.Set(targetExpr = SynExpr.Ident id; rhsExpr = rhs) when same id -> Some rhs
                    | _ -> None)
            | _ -> [||]

        // a definition worth following: one that runs code when used - a
        // function or member, a sequence, an async, a task, a lazy, a
        // delegate. A plain value bound from a lookup (`let a = d.[k]`) is
        // inert
        and runsWhenUsed (x: FSharpMemberOrFunctionOrValue) =
            x.IsMember
            || (try
                    let t = OptionModule.stripAbbreviations x.FullType

                    t.IsFunctionType
                    || (t.HasTypeDefinition
                        && (t.TypeDefinition.IsDelegate
                            || (match t.TypeDefinition.TryFullName with
                                | Some n ->
                                    n.StartsWith "System.Collections.Generic.IEnumerable"
                                    || n = "System.Collections.IEnumerable"
                                    || n.StartsWith "Microsoft.FSharp.Control."
                                    || n.StartsWith "System.Threading.Tasks."
                                    || n.StartsWith "System.Lazy"
                                | None -> false)))
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    true)

        // a dictionary-typed value, field or property - `member val D =
        // Dictionary()` included - is a dictionary touched
        and touchesName (depth: int) (ids: Ident list) =
            match resolve ids with
            | Some(:? FSharpMemberOrFunctionOrValue as x) ->
                (not x.IsMember && dictionaryTyped x.FullType)
                || (x.IsProperty
                    && (try
                            dictionaryTyped x.ReturnParameter.Type
                        with _ -> // fsharpanalyzer: ignore-line FR0055
                            false))
                || (not (fromCore x)
                    && depth > 0
                    && runsWhenUsed x
                    && touchesDictionary (depth - 1) false x)
            | Some(:? FSharpField as f) -> dictionaryTyped f.FieldType
            | Some(:? FSharpActivePatternCase as c) -> depth > 0 && touchesDictionary (depth - 1) false c
            | _ -> false

        // a getter runs where it is read, an argument included, a setter
        // where it is stored to; a function or method when the call it heads
        // or is handed to runs
        let effectOfWith (store: bool) (symbol: FSharpSymbol) =
            try
                match symbol with
                | :? FSharpMemberOrFunctionOrValue as v when
                    not (fromCore v) && runsWhenUsed v && touchesDictionary 3 store v
                    ->
                    if v.IsProperty || v.IsPropertyGetterMethod || v.IsPropertySetterMethod then
                        InPlace
                    else
                        Called
                | _ -> Safe
            with _ -> // an unreadable symbol is taken as harmless; fsharpanalyzer: ignore-line FR0055
                Safe

        let effectOf (symbol: FSharpSymbol) = effectOfWith false symbol

        // the symbol's value is a dictionary: a field or property of that
        // type, a value of it
        let dictionaryValued (symbol: FSharpSymbol) =
            match symbol with
            | :? FSharpMemberOrFunctionOrValue as v ->
                if v.IsProperty || v.IsPropertyGetterMethod then
                    dictionaryTyped v.ReturnParameter.Type
                else
                    dictionaryTyped v.FullType
            | :? FSharpField as f -> dictionaryTyped f.FieldType
            | _ -> false

        // the type a statement's value has, for the implicit yields of a
        // `seq { }`: a unit statement (a printf, a store, a loop, a call of a
        // unit function or void method) yields nothing
        let returnsUnit (e: SynExpr) =
            let unitType (t: FSharpType) =
                try
                    let rec result (t: FSharpType) =
                        if t.IsFunctionType then
                            result t.GenericArguments.[1]
                        else
                            t

                    let t = OptionModule.stripAbbreviations (result t)

                    t.HasTypeDefinition
                    && t.TypeDefinition.TryFullName = Some "Microsoft.FSharp.Core.Unit"
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false

            let unitFunctions =
                set
                    [
                        "printf"
                        "printfn"
                        "eprintf"
                        "eprintfn"
                        "failwith"
                        "failwithf"
                        "raise"
                        "invalidArg"
                        "invalidOp"
                        "nullArg"
                    ]

            let rec headIds (e: SynExpr) =
                match stripParens e with
                | SynExpr.App(isInfix = false; funcExpr = f) -> headIds f
                | SynExpr.TypeApp(expr = f) -> headIds f
                | SynExpr.Ident id -> Some [ id ]
                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some ids
                | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty -> Some [ List.last ids ]
                | _ -> None

            let rec unit (e: SynExpr) =
                match stripParens e with
                | SynExpr.Const(SynConst.Unit, _)
                | SynExpr.Do _ -> true
                // in a `seq { }` a loop or an else-less `if` whose body has
                // a value yields it
                | SynExpr.For(doBody = b)
                | SynExpr.ForEach(bodyExpr = b)
                | SynExpr.While(doExpr = b)
                | SynExpr.IfThenElse(thenExpr = b; elseExpr = None) -> unit b
                | e when isStore e -> true
                | SynExpr.IfThenElse(thenExpr = t; elseExpr = Some el) -> unit t && unit el
                | SynExpr.Match(clauses = cs) -> cs |> List.forall (fun (SynMatchClause(resultExpr = r)) -> unit r)
                | SynExpr.Sequential(expr2 = e2) -> unit e2
                | LetOrUseE lou -> unit lou.Body
                | SynExpr.TryWith(tryExpr = t) -> unit t
                | PipeApp(_, fn) -> unit fn
                | other ->
                    match headIds other with
                    | Some ids when unitFunctions.Contains (List.last ids).idText -> true
                    | Some ids ->
                        match resolve ids with
                        | Some(:? FSharpMemberOrFunctionOrValue as v) ->
                            (v.IsMember
                             && (try
                                     unitType v.ReturnParameter.Type
                                 with _ -> // fsharpanalyzer: ignore-line FR0055
                                     false))
                            || unitType v.FullType
                        | _ -> false
                    | None -> false

            unit e

        // a store elsewhere is harmless - into a variable, a field, an array,
        // another collection - unless its target is visibly another name
        // for the receiver: a value of this file whose definition names the
        // receiver (`let view = d`, `let m = d :> IDictionary<_, _>`). The
        // receiver's own stores are `stores` above
        let aliasOfReceiver (receiverRoot: string) (id: Ident) =
            let mentionsRoot (body: SynExpr) =
                AstIndex.exprsWithin index body.Range
                |> Array.exists (fun (_, x) ->
                    Range.rangeContainsRange body.Range x.Range
                    && (match x with
                        | SynExpr.Ident id -> id.idText = receiverRoot
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> first.idText = receiverRoot
                        | _ -> false))

            id.idText <> receiverRoot
            && (match resolve [ id ] with
                | Some symbol ->
                    (try
                        bodiesDeclaredAt symbol |> List.exists mentionsRoot
                     with _ -> // fsharpanalyzer: ignore-line FR0055
                         false)
                | None -> false)

        let harmlessStore (receiverRoot: string) (e: SynExpr) =
            // a dictionary reached through a value bound to the receiver:
            // `env.Table.[k] <- 0`
            let throughAlias (ids: Ident list) =
                aliasOfReceiver receiverRoot (List.head ids)
                && (match resolve ids with
                    | Some symbol -> dictionaryValued symbol
                    | None -> true)

            match e with
            | SynExpr.DotIndexedSet(objectExpr = SynExpr.Ident id)
            | SynExpr.Set(targetExpr = SynExpr.App(funcExpr = SynExpr.Ident id; argExpr = SynExpr.ArrayOrListComputed _)) ->
                not (aliasOfReceiver receiverRoot id)
            | SynExpr.DotIndexedSet(objectExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))
            | SynExpr.Set(
                targetExpr = SynExpr.App(
                    funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids))
                    argExpr = SynExpr.ArrayOrListComputed _)) when not ids.IsEmpty -> not (throughAlias ids)
            | _ -> true

        // WHEN a node takes effect: a function or method at the end of the
        // application it heads, an argument when the call it is handed to
        // runs, anything else where it stands. Arguments run before the
        // call, so `use k d.[k]` reads before `use` runs
        let rec climbHead (nodes: SyntaxNode list) (r: range) =
            match nodes with
            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f) as app) :: rest when Range.equals f.Range r ->
                climbHead rest app.Range
            | SyntaxNode.SynExpr(SynExpr.TypeApp(expr = inner) as t) :: rest when Range.equals inner.Range r ->
                climbHead rest t.Range
            | _ -> r

        let rec throughArgument (nodes: SyntaxNode list) (r: range) =
            match nodes with
            | SyntaxNode.SynExpr(SynExpr.Paren _ | SynExpr.Tuple _ as wrap) :: rest -> throughArgument rest wrap.Range
            | SyntaxNode.SynExpr(SynExpr.App(argExpr = a) as app) :: rest when Range.equals a.Range r ->
                Some(climbHead rest app.Range)
            | _ -> None

        let effectEnd (path: SyntaxNode list) (node: SynExpr) =
            let applied = climbHead path node.Range

            if not (Range.equals applied node.Range) then
                applied.End
            else
                match throughArgument path node.Range with
                | Some call -> call.End
                | None -> node.Range.End

        // `member val` properties of this file, by name and declaring line
        let autoProperties =
            lazy
                (index.Decls
                 |> Array.collect (fun (_, decl) ->
                     match decl with
                     | SynModuleDecl.Types(typeDefns = types) ->
                         [|
                             for SynTypeDefn(typeRepr = repr; members = members) in types do
                                 let inner =
                                     match repr with
                                     | SynTypeDefnRepr.ObjectModel(members = inner) -> inner
                                     | _ -> []

                                 for m in members @ inner do
                                     match m with
                                     | SynMemberDefn.AutoProperty(ident = id) -> id.idText, id.idRange.StartLine
                                     | _ -> ()
                         |]
                     | _ -> [||])
                 |> Set.ofArray)

        // every segment after the receiver's root is taken to read the SAME
        // dictionary each time, unless a getter of this file visibly builds
        // one - `member _.Table = Dictionary()` hands each read another
        // dictionary than the header walked
        let receiverStable (receiverIds: Ident list) =
            // a dictionary's constructor call, or a call of a function of
            // this file that makes one (`member _.Table = make ()`), three
            // calls deep; a StringBuilder built on the way is no new dictionary
            let dictionaryEntity (e: FSharpEntity) =
                try
                    e.TryFullName |> Option.exists dictionaryName
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    true

            let rec constructs (depth: int) (body: SynExpr) =
                let constructing (ids: Ident list) =
                    match resolve ids with
                    | Some(:? FSharpMemberOrFunctionOrValue as c) ->
                        (c.IsConstructor && dictionaryName (OptionModule.enclosingFullName c))
                        || (not c.IsConstructor
                            && depth > 0
                            && not (fromCore c)
                            && (bodiesDeclaredAt c |> List.exists (constructs (depth - 1))))
                    | Some(:? FSharpEntity as e) -> dictionaryEntity e
                    | _ -> false

                let rec typeIds (t: SynType) =
                    match t with
                    | SynType.App(typeName = inner) -> typeIds inner
                    | SynType.LongIdent(SynLongIdent(id = ids)) -> Some ids
                    | _ -> None

                AstIndex.exprsWithin index body.Range
                |> Array.exists (fun (_, x) ->
                    Range.rangeContainsRange body.Range x.Range
                    && (match x with
                        | SynExpr.New(targetType = t) ->
                            (match typeIds t with
                             | Some ids ->
                                 (match resolve ids with
                                  | Some(:? FSharpEntity as e) -> dictionaryEntity e
                                  | Some(:? FSharpMemberOrFunctionOrValue as c) -> constructing ids
                                  | _ -> (List.last ids).idText.Contains "Dictionary")
                             | None -> false)
                        | SynExpr.App(isInfix = false; funcExpr = SynExpr.Ident id)
                        | SynExpr.App(isInfix = false; funcExpr = SynExpr.TypeApp(expr = SynExpr.Ident id)) ->
                            constructing [ id ]
                        | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))
                        | SynExpr.App(
                            isInfix = false
                            funcExpr = SynExpr.TypeApp(expr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)))) ->
                            constructing ids
                        | _ -> false))

            [ 2 .. receiverIds.Length ]
            |> List.forall (fun n ->
                match resolve (List.take n receiverIds) with
                | Some(:? FSharpMemberOrFunctionOrValue as v) when
                    v.IsProperty
                    && not (autoProperties.Value.Contains((v.DisplayName, v.DeclarationLocation.StartLine)))
                    ->
                    (try
                        not (bodiesDeclaredAt v |> List.exists (constructs 3))
                     with _ -> // an unreadable property is taken as stable; fsharpanalyzer: ignore-line FR0055
                         true)
                | _ -> true)

        // the receiver is a local the function built itself - `let d =
        // Dictionary<_, _>()` - and no other name can reach: every mention of
        // it in the function is its own member access, index or store, none
        // hands it on (an argument, a tuple, a return, another binding) and
        // none sits in a closure. Then nothing but those mentions can write
        // it, and a user call, an interface call or a suspension before a
        // read is harmless
        let unescapedLocal (receiverIds: Ident list) (loopPath: SyntaxNode list) =
            match receiverIds with
            | [ receiver ] ->
                match resolve [ receiver ] with
                | Some(:? FSharpMemberOrFunctionOrValue as v) when not v.IsModuleValueOrMember ->
                    let constructed =
                        match OptionModule.bindingDeclaredAt index v with
                        | Some(_, rhs) ->
                            let rec head (e: SynExpr) =
                                match stripParens e with
                                | SynExpr.App(funcExpr = f; isInfix = false) -> head f
                                | SynExpr.TypeApp(expr = f) -> head f
                                | SynExpr.Ident id -> Some [ id ]
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) -> Some ids
                                | _ -> None

                            // a lookup also runs the key's hashing and the
                            // comparer's: a key type or comparer of the user's
                            // own may change what `d.[k]` finds without
                            // writing the dictionary
                            let frameworkType (t: FSharpType) =
                                let t = OptionModule.stripAbbreviations t

                                t.HasTypeDefinition
                                && (fromFramework t.TypeDefinition
                                    || t.TypeDefinition.TryFullName
                                       |> Option.exists (fun n -> n.StartsWith "Microsoft.FSharp."))

                            let frameworkKey =
                                try
                                    let t = OptionModule.stripAbbreviations v.FullType
                                    t.GenericArguments.Count >= 1 && frameworkType t.GenericArguments.[0]
                                with _ -> // fsharpanalyzer: ignore-line FR0055
                                    false

                            let rec arguments (e: SynExpr) =
                                match stripParens e with
                                | SynExpr.App(funcExpr = f; argExpr = a; isInfix = false) -> a :: arguments f
                                | SynExpr.New(expr = a) -> [ a ]
                                | _ -> []

                            // no comparer, a constant, or the framework's
                            let frameworkArgument (a: SynExpr) =
                                match stripParens a with
                                | SynExpr.Const _ -> true
                                | SynExpr.Tuple(exprs = parts) ->
                                    parts
                                    |> List.forall (fun p ->
                                        match stripParens p with
                                        | SynExpr.Const _ -> true
                                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                            match resolve ids with
                                            | Some s ->
                                                fromFramework s
                                                || (OptionModule.fullNameOf s).StartsWith "Microsoft.FSharp."
                                            | None -> false
                                        | _ -> false)
                                | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                    match resolve ids with
                                    | Some s ->
                                        fromFramework s || (OptionModule.fullNameOf s).StartsWith "Microsoft.FSharp."
                                    | None -> false
                                | _ -> false

                            frameworkKey
                            && arguments rhs |> List.forall frameworkArgument
                            && match stripParens rhs with
                               | SynExpr.New _ -> true
                               | other ->
                                   match head other with
                                   | Some ids ->
                                       match resolve ids with
                                       | Some(:? FSharpMemberOrFunctionOrValue as c) ->
                                           c.IsConstructor
                                           && (OptionModule.enclosingFullName c).StartsWith
                                               "System.Collections.Generic."
                                       | Some(:? FSharpEntity as t) ->
                                           t.TryFullName
                                           |> Option.exists (fun n -> n.StartsWith "System.Collections.Generic.")
                                       | _ -> false
                                   | None -> false
                        | None -> false

                    // the function the local lives in: the innermost binding
                    // around the loop that also holds the declaration
                    let scope =
                        loopPath
                        |> List.tryPick (fun node ->
                            match node with
                            | SyntaxNode.SynBinding(SynBinding _ as b) when
                                Range.rangeContainsRange b.RangeOfBindingWithRhs v.DeclarationLocation
                                ->
                                Some b.RangeOfBindingWithRhs
                            | _ -> None)

                    // a `seq { }` or `async { }` holds its mentions for later,
                    // as a lambda does
                    let closure (node: SyntaxNode) =
                        match node with
                        | SyntaxNode.SynExpr(SynExpr.Lambda _)
                        | SyntaxNode.SynExpr(SynExpr.MatchLambda _)
                        | SyntaxNode.SynExpr(SynExpr.ObjExpr _)
                        | SyntaxNode.SynExpr(SynExpr.Lazy _)
                        | SyntaxNode.SynExpr(SynExpr.ComputationExpr _)
                        | SyntaxNode.SynBinding(SynBinding(headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _)))) ->
                            true
                        | _ -> false

                    // the dictionary's own members: its reads whichever way
                    // they are used (a key collection writes nothing), its
                    // writes only when called - `let reset = d.Clear` hands
                    // the writer on, an extension of the user's own may keep
                    // the dictionary, a lookup handed out writes through it
                    let ownReads = set [ "Keys"; "Values"; "Count"; "Comparer" ]

                    let ownCalls =
                        set
                            [
                                "Add"
                                "Remove"
                                "Clear"
                                "TryAdd"
                                "TryGetValue"
                                "ContainsKey"
                                "ContainsValue"
                                "GetValueOrDefault"
                                "EnsureCapacity"
                                "TrimExcess"
                            ]

                    let ownMember (memberId: Ident) (applied: bool) =
                        ownReads.Contains memberId.idText
                        || (applied
                            && ownCalls.Contains memberId.idText
                            && (match resolve [ receiver; memberId ] with
                                | Some(:? FSharpMemberOrFunctionOrValue as m) ->
                                    not m.IsExtensionMember || fromFramework m
                                | _ -> false))

                    let appliedAt (node: range) (parents: SyntaxNode list) =
                        match parents with
                        | SyntaxNode.SynExpr(SynExpr.App(funcExpr = f)) :: _ -> Range.equals f.Range node
                        | _ -> false

                    let mentioned (e: SynExpr) =
                        match e with
                        | SynExpr.Ident id -> id.idText = receiver.idText
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = first :: _)) -> first.idText = receiver.idText
                        | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = first :: _)) ->
                            first.idText = receiver.idText
                        | _ -> false

                    // a mention is its own only as the object of an index, an
                    // F# 6 index, a store, a reassignment, or one of its own
                    // members
                    let ownUse (mentionPath: SyntaxNode list) (e: SynExpr) =
                        match e with
                        | SynExpr.LongIdentSet _ -> true
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = _ :: m :: _)) ->
                            ownMember m (appliedAt e.Range mentionPath)
                        | SynExpr.LongIdent _ -> false
                        | _ ->
                            match mentionPath with
                            | SyntaxNode.SynExpr(SynExpr.DotIndexedGet(objectExpr = o)) :: _
                            | SyntaxNode.SynExpr(SynExpr.DotIndexedSet(objectExpr = o)) :: _ ->
                                Range.equals o.Range e.Range
                            | SyntaxNode.SynExpr(SynExpr.DotGet(expr = o; longDotId = SynLongIdent(id = m :: _)) as dot) :: parents ->
                                Range.equals o.Range e.Range && ownMember m (appliedAt dot.Range parents)
                            | SyntaxNode.SynExpr(SynExpr.App(funcExpr = o; argExpr = SynExpr.ArrayOrListComputed _)) :: _ ->
                                Range.equals o.Range e.Range
                            | _ -> false

                    constructed
                    && (match scope with
                        | Some scope ->
                            AstIndex.exprsWithin index scope
                            |> Array.forall (fun (mentionPath, e) ->
                                not (mentioned e)
                                || (ownUse mentionPath e
                                    && not (
                                        mentionPath
                                        |> List.exists (fun node ->
                                            closure node
                                            && (match node with
                                                | SyntaxNode.SynExpr inner ->
                                                    Range.rangeContainsRange scope inner.Range
                                                    && not (Range.equals scope inner.Range)
                                                | SyntaxNode.SynBinding b ->
                                                    Range.rangeContainsRange scope b.RangeOfBindingWithRhs
                                                    && not (Range.equals scope b.RangeOfBindingWithRhs)
                                                | _ -> false))
                                    )))
                        | None -> false)
                | _ -> false
            | _ -> false

        [
            for path, e in index.Exprs do
                match e with
                | SynExpr.ForEach(
                    pat = SynPat.Named(ident = SynIdent(ident = key)); enumExpr = enumExpr; bodyExpr = body) ->
                    match keysOf enumExpr with
                    | Some(receiverIds, receiverText) when isDictionary (List.last receiverIds) ->
                        let readsWithPaths =
                            AstIndex.exprsWithin index body.Range
                            |> Array.filter (fun (_, inner) ->
                                Range.rangeContainsRange body.Range inner.Range
                                && indexerRead receiverText key.idText inner)

                        let reads = readsWithPaths |> Array.map snd

                        // a read under a lambda, `lazy`, computation
                        // expression or object expression inside the body
                        // runs LATER, against the dictionary as it is then;
                        // the pair's value is what it held during the loop
                        let deferredRead =
                            readsWithPaths
                            |> Array.exists (fun (readPath, _) ->
                                readPath
                                |> List.exists (fun node ->
                                    match node with
                                    | SyntaxNode.SynExpr(SynExpr.Lambda _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.MatchLambda _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.Lazy _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.ComputationExpr _ as deferring)
                                    | SyntaxNode.SynExpr(SynExpr.ObjExpr _ as deferring) ->
                                        Range.rangeContainsRange body.Range deferring.Range
                                    // a local function: `let get () = d.[k]`
                                    // reads when it is called
                                    | SyntaxNode.SynBinding(SynBinding(
                                        headPat = SynPat.LongIdent(argPats = SynArgPats.Pats(_ :: _))) as b) ->
                                        Range.rangeContainsRange body.Range b.RangeOfBindingWithRhs
                                    | _ -> false))

                        // a store through the indexer, or a key used anywhere
                        // but as the lookup, keeps the loop
                        let stores =
                            AstIndex.exprsWithin index body.Range
                            |> Array.exists (fun (_, inner) ->
                                Range.rangeContainsRange body.Range inner.Range
                                && (match inner with
                                    | SynExpr.DotIndexedSet(objectExpr = obj) ->
                                        textOfRange source obj.Range = receiverText
                                    | SynExpr.Set(targetExpr = SynExpr.App(funcExpr = obj)) ->
                                        textOfRange source obj.Range = receiverText
                                    | _ -> false))

                        let enclosing =
                            path
                            |> List.tryPick (fun node ->
                                match node with
                                | SyntaxNode.SynBinding(SynBinding _ as b) ->
                                    Some(textOfRange source b.RangeOfBindingWithRhs)
                                | _ -> None)
                            |> Option.defaultValue (source.GetSubTextString(0, source.Length))

                        let valueName =
                            [ "value"; "v"; "v1" ] |> List.tryFind (mentionsIdentifier enclosing >> not)

                        // a `let k = ...`, a lambda or a match arm rebinding
                        // the key inside the body: a `d.[k]` under it reads
                        // ANOTHER key, which the pair's value is not
                        let keyRebound =
                            (AstIndex.patsWithin index body.Range
                             |> Array.exists (fun (_, p) ->
                                 Range.rangeContainsRange body.Range p.Range
                                 && List.contains key.idText (patBoundNames p)))
                            // a lambda's parameters are simple patterns the
                            // index does not list
                            || (AstIndex.exprsWithin index body.Range
                                |> Array.exists (fun (_, inner) ->
                                    Range.rangeContainsRange body.Range inner.Range
                                    && (match inner with
                                        | SynExpr.Lambda(parsedData = Some(pats, _)) ->
                                            pats |> List.collect patBoundNames |> List.contains key.idText
                                        | _ -> false)))

                        // the receiver's own name rebound in the body: a
                        // `d.[k]` under `let d = other` reads ANOTHER
                        // dictionary with the same text
                        let receiverRoot = (List.head receiverIds).idText

                        let receiverRebound =
                            (AstIndex.patsWithin index body.Range
                             |> Array.exists (fun (_, p) ->
                                 Range.rangeContainsRange body.Range p.Range
                                 && List.contains receiverRoot (patBoundNames p)))
                            || (AstIndex.exprsWithin index body.Range
                                |> Array.exists (fun (_, inner) ->
                                    Range.rangeContainsRange body.Range inner.Range
                                    && (match inner with
                                        | SynExpr.Lambda(parsedData = Some(pats, _)) ->
                                            pats |> List.collect patBoundNames |> List.contains receiverRoot
                                        | _ -> false)))

                        let insideRead (r: range) =
                            reads |> Array.exists (fun read -> Range.rangeContainsRange read.Range r)

                        let isReceiverPrefix (ids: Ident list) =
                            ids.Length >= receiverIds.Length
                            && identText (List.take receiverIds.Length ids) = receiverText

                        // the loop sits in a `seq { }`, `task { }` or `async { }`:
                        // at each `yield`, `let!`, `do!` or `match!` other code
                        // runs - the consumer, another task - before the next
                        // statement. A list or array comprehension runs none
                        let computation =
                            path
                            |> List.pairwise
                            |> List.tryPick (fun (node, parent) ->
                                match node, parent with
                                // `seq { }`: an implicit yield has no node
                                | SyntaxNode.SynExpr(SynExpr.ComputationExpr _),
                                  SyntaxNode.SynExpr(SynExpr.App(funcExpr = SynExpr.Ident builder)) when
                                    builder.idText = "seq"
                                    ->
                                    Some(Some true)
                                | SyntaxNode.SynExpr(SynExpr.ComputationExpr _), _ -> Some(Some false)
                                | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed _), _
                                | SyntaxNode.SynExpr(SynExpr.Lambda _), _ -> Some None
                                | _ -> None)
                            |> Option.flatten

                        let inComputation = computation.IsSome
                        let inSeq = computation = Some true

                        // the loop's own suspension points, not a nested
                        // computation's or closure's
                        let ownStatement (nodePath: SyntaxNode list) =
                            nodePath
                            |> List.forall (fun node ->
                                match node with
                                | SyntaxNode.SynExpr(SynExpr.ComputationExpr _ as inner)
                                | SyntaxNode.SynExpr(SynExpr.Lambda _ as inner)
                                | SyntaxNode.SynExpr(SynExpr.ArrayOrListComputed _ as inner) ->
                                    not (Range.rangeContainsRange body.Range inner.Range)
                                | _ -> true)

                        // a loop inside a computation shares the dictionary
                        // with whatever runs at its suspensions: no local is
                        // proven unreached there
                        let escapeFree = lazy (not inComputation && unescapedLocal receiverIds path)

                        let suspensions () =
                            if not inComputation then
                                [||]
                            else
                                AstIndex.exprsWithin index body.Range
                                |> Array.choose (fun (nodePath, inner) ->
                                    if
                                        not (Range.rangeContainsRange body.Range inner.Range)
                                        || not (ownStatement nodePath)
                                    then
                                        None
                                    else
                                        match inner with
                                        | SynExpr.YieldOrReturn _
                                        | SynExpr.YieldOrReturnFrom _ -> Some(inner.Range, inner.Range.End)
                                        | SynExpr.DoBang(expr = awaited)
                                        | SynExpr.MatchBang(expr = awaited) -> Some(inner.Range, awaited.Range.End)
                                        | LetOrUseE lou when lou.IsBang -> Some(inner.Range, lou.Body.Range.Start)
                                        // in a `seq { }` a statement with a value
                                        // is an implicit yield; a unit one is not
                                        | SynExpr.Sequential(expr1 = statement) when
                                            inSeq && not (returnsUnit statement)
                                            ->
                                            Some(statement.Range, statement.Range.End)
                                        | _ -> None)

                        // an active pattern of the user's own runs when the
                        // arm is tried: `| Touch -> ...` before the read
                        let patternCalls () =
                            AstIndex.patsWithin index body.Range
                            |> Array.choose (fun (_, p) ->
                                match p with
                                | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when
                                    Range.rangeContainsRange body.Range p.Range
                                    ->
                                    match resolve ids with
                                    | Some(:? FSharpActivePatternCase as case) when
                                        not (fromCore case) && touchesDictionary 3 false case
                                        ->
                                        Some(p.Range, p.Range.End)
                                    | _ -> None
                                | _ -> None)

                        // everything in the body that may write the
                        // dictionary, with WHEN it takes effect
                        let hazards () =
                            AstIndex.exprsWithin index body.Range
                            |> Array.choose (fun (hazardPath, inner) ->
                                if not (Range.rangeContainsRange body.Range inner.Range) || insideRead inner.Range then
                                    None
                                else
                                    let names =
                                        match inner with
                                        | SynExpr.Ident id -> Some [ id ]
                                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                                            Some ids
                                        | _ -> None

                                    // the segments' effects together: a getter
                                    // on the way runs where the chain is read
                                    let combined (effects: Effect list) =
                                        if List.contains InPlace effects then InPlace
                                        elif List.contains Called effects then Called
                                        else Safe

                                    // a member of another dictionary that a
                                    // value of this file names as the receiver
                                    // (`let view = d`) writes this one
                                    // the member must be able to write: a
                                    // dictionary's own, or a member of this
                                    // file whose body touches one - never a
                                    // counter field of the holder (`env.Counter
                                    // <- env.Counter + 1`), nor a member of one
                                    let throughAlias (store: bool) (ids: Ident list) =
                                        ids.Length >= 2
                                        && not (readOnlyMembers.Contains (List.last ids).idText)
                                        && aliasOfReceiver receiverRoot (List.head ids)
                                        && (ids.Length = 2
                                            || (match resolve (List.take (ids.Length - 1) ids) with
                                                | Some owner -> dictionaryValued owner
                                                | None -> true))
                                        && (match resolve ids with
                                            | Some(:? FSharpField) -> false
                                            | Some(:? FSharpMemberOrFunctionOrValue as v) when
                                                not (bodiesDeclaredAt v).IsEmpty
                                                ->
                                                effectOfWith store v <> Safe
                                            | _ -> true)

                                    // the last segment read, or stored to
                                    let effectOfIdsFor (store: bool) (ids: Ident list) =
                                        if throughAlias store ids then
                                            Called
                                        else
                                            [ 1 .. ids.Length ]
                                            |> List.map (fun n ->
                                                match resolve (List.take n ids) with
                                                | Some symbol -> effectOfWith (store && n = ids.Length) symbol
                                                | None -> Safe)
                                            |> combined

                                    let effectOfIds (ids: Ident list) = effectOfIdsFor false ids

                                    let effect =
                                        match inner, names with
                                        | _, Some ids when isReceiverPrefix ids ->
                                            // the receiver itself: a read-only
                                            // member - whatever follows one
                                            // reads its value, `d.Count.ToString()`
                                            // - or handed to something
                                            if
                                                ids.Length > receiverIds.Length
                                                && readOnlyMembers.Contains (List.item receiverIds.Length ids).idText
                                            then
                                                Safe
                                            else
                                                Called
                                        // a local no other name reaches: only
                                        // its own mentions, above and below
                                        | _, Some _ when escapeFree.Value -> Safe
                                        | _, Some ids -> effectOfIds ids
                                        | (SynExpr.DotGet _ | SynExpr.New _), _ when escapeFree.Value -> Safe
                                        | SynExpr.DotGet(longDotId = SynLongIdent(id = ids)), _ ->
                                            ids
                                            |> List.map (fun id ->
                                                match resolve [ id ] with
                                                | Some symbol -> effectOf symbol
                                                | None -> Safe)
                                            |> combined
                                        // the receiver reassigned: `d <- other`,
                                        // `this.d <- other`
                                        | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)), _ when
                                            isReceiverPrefix ids
                                            || (ids.Length < receiverIds.Length
                                                && identText ids = identText (List.take ids.Length receiverIds))
                                            ->
                                            InPlace
                                        // a store through a setter of this file
                                        // runs the setter: `h.Bump <- 99`
                                        | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)), _
                                        | SynExpr.DotSet(longDotId = SynLongIdent(id = ids)), _
                                        | SynExpr.NamedIndexedPropertySet(longDotId = SynLongIdent(id = ids)), _
                                        | SynExpr.DotNamedIndexedPropertySet(longDotId = SynLongIdent(id = ids)), _ when
                                            not (escapeFree.Value || ids.IsEmpty) && effectOfIdsFor true ids <> Safe
                                            ->
                                            InPlace
                                        | (SynExpr.LongIdentSet _ | SynExpr.DotSet _ | SynExpr.Set _ | SynExpr.DotIndexedSet _ | SynExpr.NamedIndexedPropertySet _ | SynExpr.DotNamedIndexedPropertySet _),
                                          _ ->
                                            if escapeFree.Value || harmlessStore receiverRoot inner then
                                                Safe
                                            else
                                                InPlace
                                        | _ -> Safe

                                    match effect with
                                    | Safe -> None
                                    | InPlace -> Some(inner.Range, inner.Range.End)
                                    | Called -> Some(inner.Range, effectEnd hazardPath inner))
                            |> fun fromBody -> Array.concat [ patternCalls (); suspensions (); fromBody ]

                        // a hazard runs before the read when it takes effect
                        // at or before the read's start - or anywhere in a
                        // loop nested around the read, at any depth, whose
                        // next round runs it first
                        let hazardBeforeRead () =
                            let hazards = hazards ()

                            readsWithPaths
                            |> Array.exists (fun (readPath, read) ->
                                let innerLoops =
                                    readPath
                                    |> List.choose (fun node ->
                                        match node with
                                        | SyntaxNode.SynExpr(SynExpr.While _ as loop)
                                        | SyntaxNode.SynExpr(SynExpr.WhileBang _ as loop)
                                        | SyntaxNode.SynExpr(SynExpr.For _ as loop)
                                        | SyntaxNode.SynExpr(SynExpr.ForEach _ as loop) when
                                            Range.rangeContainsRange body.Range loop.Range
                                            ->
                                            Some loop.Range
                                        | _ -> None)

                                hazards
                                |> Array.exists (fun (hazard, effect) ->
                                    Position.posGeq read.Range.Start effect
                                    || innerLoops |> List.exists (fun loop -> Range.rangeContainsRange loop hazard)))

                        match valueName with
                        | Some valueName when
                            reads.Length > 0
                            && not stores
                            && not keyRebound
                            && not receiverRebound
                            && not deferredRead
                            && isSingleLine enumExpr.Range
                            && receiverStable receiverIds
                            // the costly one last: it resolves every name in
                            // the body, so only a loop that passed the rest pays
                            && not (hazardBeforeRead ())
                            ->
                            let headerRange =
                                Range.mkRange enumExpr.Range.FileName key.idRange.Start enumExpr.Range.End

                            {
                                Range = headerRange
                                KeyName = key.idText
                                ValueName = valueName
                                Edits =
                                    (headerRange,
                                     textOfRange source headerRange,
                                     $"KeyValue({key.idText}, {valueName}) in {receiverText}")
                                    :: [ for r in reads -> r.Range, textOfRange source r.Range, valueName ]
                            }
                        | _ -> ()
                    | _ -> ()
                | _ -> ()
        ]
