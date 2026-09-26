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
/// breaks the enumeration, so anything that may write the dictionary
/// before a read in the same iteration stands the rule down: the receiver
/// named other than by a read or a read-only member (`bump d k`, `d.Remove
/// k`, `let m = d`), the receiver's name rebound or reassigned, a writing
/// member of another dictionary that may be this one (an alias made before
/// the loop; one of other type arguments cannot be), and any call not
/// proven harmless - a user function or method, a user getter or setter, a
/// delegate, a user constructor, a call through an interface (whatever
/// implements it runs), a sequence or a collection of the user's own
/// forced by a `for` or a consumer, FSharp.Core's entry points into user
/// code (an event's Trigger, Async's runners), a member of a package that
/// merely shares the System namespace - which may reach the dictionary
/// through a field or a closure. In a `seq { }` or `task { }` the consumer
/// or another task runs at each `yield`, `let!`, `do!` and `match!`, which
/// count the same way; a list comprehension runs nothing between. A local
/// the function built itself (`let d = Dictionary<_, _>()`) that no other
/// name reaches - only indexed, stored, asked for its members, never handed
/// on or captured - can be written by nothing but its own mentions, so
/// only those count. Only what runs BEFORE a read counts: a
/// call's arguments run before the call (`use k d.[k]` converts), while a
/// getter runs where it is read, argument or not. Inside a loop nested
/// around a read, at any depth, every such call counts, since the next
/// round runs it first; a read inside a local function runs when it is
/// called and keeps the loop. A dotted receiver reads a field, a BCL
/// getter or a `member val` at every segment: a computed property may hand
/// each read another dictionary.
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

        let enumerableInterface (t: FSharpType) =
            t.HasTypeDefinition
            && (match t.TypeDefinition.TryFullName with
                | Some "System.Collections.Generic.IEnumerable`1"
                | Some "System.Collections.IEnumerable" -> true
                | _ -> false)

        // a value the code that consumes it may run user code through: a
        // function, a delegate, a sequence (`seq { }`, a user iterator), a
        // collection of the user's own (its enumerator is user code), a task
        let runsCodeWhenUsed (t: FSharpType) =
            let t = OptionModule.stripAbbreviations t

            t.IsFunctionType
            || enumerableInterface t
            || (t.HasTypeDefinition
                && (let e = t.TypeDefinition

                    e.IsDelegate
                    || (match e.TryFullName with
                        | Some n ->
                            n.StartsWith "System.Threading.Tasks.Task"
                            || n.StartsWith "System.Threading.Tasks.ValueTask"
                        | None -> false)
                    || (not e.IsArrayType
                        && not (e.TryFullName |> Option.exists (fun n -> n.StartsWith "Microsoft.FSharp."))
                        && not (fromFramework e)
                        && e.AllInterfaces |> Seq.exists enumerableInterface)))

        // WHEN a name may write the dictionary through a field, a closure or
        // an alias: never (`Safe`: FSharp.Core's operators and collection
        // functions, the BCL's members and getters, a union case, a plain
        // value or field); where it is evaluated (`InPlace`: a user getter,
        // which runs even as an argument); or when the call it heads or is
        // handed to runs (`Called`: a user function or method, a delegate, a
        // sequence, a call through an interface, FSharp.Core's entry points
        // into user code - an event's Trigger, Async's runners - and a
        // mutating member of ANOTHER dictionary, which may be this one under
        // another name). The sequence a Seq function forces is a value
        // checked where it stands, so `Seq.sum xs` over an array is Safe
        // a function of this file whose body only computes - FSharp.Core and
        // String calls, no store, no dictionary named - cannot reach the
        // dictionary: `label k` before a read is harmless. Decided once per
        // function
        let pureHelpers = System.Collections.Generic.Dictionary<string, bool>()

        let isStore (e: SynExpr) =
            match e with
            | SynExpr.LongIdentSet _
            | SynExpr.DotSet _
            | SynExpr.Set _
            | SynExpr.DotIndexedSet _
            | SynExpr.NamedIndexedPropertySet _
            | SynExpr.DotNamedIndexedPropertySet _ -> true
            | _ -> false

        let dictionaryTyped (t: FSharpType) =
            try
                let t = OptionModule.stripAbbreviations t

                t.HasTypeDefinition
                && (t.TypeDefinition.TryFullName
                    |> Option.exists (fun n -> aliasTypes.Contains n || n.Contains "Dictionary"))
            with _ -> // fsharpanalyzer: ignore-line FR0055
                true

        // a value a pure body may name: no dictionary, and nothing that runs
        // code when used (a `seq { }` forced by `Seq.length`, a delegate)
        let plainValue (t: FSharpType) =
            not (dictionaryTyped t)
            && not (
                try
                    runsCodeWhenUsed t
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    true
            )

        // FSharp.Core's operators and functions are function-typed values the
        // call check above has already vetted
        let fromCore (x: FSharpMemberOrFunctionOrValue) =
            (OptionModule.fullNameOf x).StartsWith "Microsoft.FSharp."

        let pureHelper (v: FSharpMemberOrFunctionOrValue) =
            let key =
                try
                    $"{v.FullName}@{v.DeclarationLocation.FileName}:{v.DeclarationLocation.StartLine}:{v.DeclarationLocation.StartColumn}"
                with _ -> // no declaration to read: no proof; fsharpanalyzer: ignore-line FR0055
                    ""

            if key = "" then
                false
            else
                match pureHelpers.TryGetValue key with
                | true, known -> known
                | false, _ ->
                    let pure =
                        match OptionModule.bindingDeclaredAt index v with
                        | Some(_, body) ->
                            OptionModule.callsOnlyCore check source index body.Range
                            && AstIndex.exprsWithin index body.Range
                               |> Array.forall (fun (_, e) ->
                                   not (Range.rangeContainsRange body.Range e.Range)
                                   || (not (isStore e)
                                       && (match e with
                                           | SynExpr.Ident id ->
                                               match resolve [ id ] with
                                               // a member is a call, vetted above
                                               | Some(:? FSharpMemberOrFunctionOrValue as x) when
                                                   not x.IsMember && not (fromCore x)
                                                   ->
                                                   plainValue x.FullType
                                               | Some(:? FSharpField as f) -> plainValue f.FieldType
                                               | _ -> true
                                           | SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)) ->
                                               [ 1 .. ids.Length ]
                                               |> List.forall (fun n ->
                                                   match resolve (List.take n ids) with
                                                   | Some(:? FSharpMemberOrFunctionOrValue as x) when
                                                       not x.IsMember && not (fromCore x)
                                                       ->
                                                       plainValue x.FullType
                                                   | Some(:? FSharpField as f) -> plainValue f.FieldType
                                                   | _ -> true)
                                           | _ -> true)))
                        | None -> false

                    pureHelpers.[key] <- pure
                    pure

        let effectOf (symbol: FSharpSymbol) =
            try
                match symbol with
                | :? FSharpUnionCase
                | :? FSharpEntity -> Safe
                | :? FSharpField as f -> if runsCodeWhenUsed f.FieldType then Called else Safe
                | :? FSharpMemberOrFunctionOrValue as v ->
                    let fullName = OptionModule.fullNameOf v
                    let enclosing = OptionModule.enclosingFullName v
                    let getter = v.IsProperty || v.IsPropertyGetterMethod
                    let framework = enclosing.StartsWith "System." && fromFramework v

                    if enclosing = "System.Lazy`1" then
                        if getter then InPlace else Called
                    elif v.IsExtensionMember then
                        // LINQ's operators consume a receiver and arguments
                        // that are checked where they stand; the framework's
                        // dictionary extensions (`other.Remove(k, &old)`,
                        // `TryAdd`) write whatever `other` names
                        if
                            framework
                            && v.DeclaringEntity
                               |> Option.bind (fun e -> e.TryFullName)
                               |> Option.exists ((=) "System.Collections.Generic.CollectionExtensions")
                            && not (readOnlyMembers.Contains v.DisplayName)
                        then
                            Called
                        elif framework then
                            Safe
                        elif getter then
                            InPlace
                        else
                            Called
                    elif fullName.StartsWith "Microsoft.FSharp.Control." then
                        Called
                    elif fullName.StartsWith "Microsoft.FSharp." then
                        if v.DisplayName = "force" || v.DisplayName = "Force" then
                            Called
                        else
                            Safe
                    elif getter then
                        if framework then Safe else InPlace
                    elif v.IsMember || v.IsConstructor then
                        // a local has no enclosing entity to ask (FCS throws)
                        let owner = v.ApparentEnclosingEntity

                        if not framework then
                            Called
                        elif owner |> Option.exists (fun e -> e.IsDelegate) then
                            Called
                        elif aliasTypes.Contains enclosing then
                            if readOnlyMembers.Contains v.DisplayName then
                                Safe
                            else
                                Called
                        // a lookup through `IReadOnlyDictionary` and kin reads
                        elif
                            enclosing.StartsWith "System.Collections."
                            && readOnlyMembers.Contains v.DisplayName
                        then
                            Safe
                        // `o.OnNext k`, `x.Dispose()`: whatever implements it
                        elif owner |> Option.exists (fun e -> e.IsInterface) then
                            Called
                        else
                            Safe
                    elif runsCodeWhenUsed v.FullType then
                        if v.FullType.IsFunctionType && pureHelper v then
                            Safe
                        else
                            Called
                    else
                        Safe
                | _ -> InPlace
            with _ -> // an unreadable symbol may be anything; fsharpanalyzer: ignore-line FR0055
                InPlace

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

        // a store is harmless into a local mutable, or into an array or a
        // System.Collections.Generic collection named other than the
        // receiver (its own stores are `stores` above) that is no dictionary:
        // another dictionary may be this one under another name
        let harmlessStore (receiverText: string) (distinctDictionary: FSharpType -> bool) (e: SynExpr) =
            let bclTarget (obj: SynExpr) =
                match obj with
                | SynExpr.Ident id when id.idText <> receiverText ->
                    match resolve [ id ] with
                    | Some(:? FSharpMemberOrFunctionOrValue as v) ->
                        (try
                            let t = OptionModule.stripAbbreviations v.FullType

                            t.HasTypeDefinition
                            && (t.TypeDefinition.IsArrayType
                                || (t.TypeDefinition.TryFullName
                                    |> Option.exists (fun n ->
                                        n.StartsWith "System.Collections.Generic."
                                        && ((not (aliasTypes.Contains n) && not (n.Contains "Dictionary"))
                                            || distinctDictionary t))))
                         with _ -> // fsharpanalyzer: ignore-line FR0055
                             false)
                    | _ -> false
                | _ -> false

            match e with
            // a variable store rebinds a name, it writes no dictionary (the
            // receiver's own reassignment is counted before this)
            | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = [ id ])) ->
                match resolve [ id ] with
                | Some(:? FSharpMemberOrFunctionOrValue as v) -> v.IsMutable
                | Some(:? FSharpField) -> true
                | _ -> false
            // a field store runs no code: `acc.Count <- acc.Count + 1`
            | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)) ->
                match resolve ids with
                | Some(:? FSharpField) -> true
                | _ -> false
            | SynExpr.DotSet(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                match resolve [ List.last ids ] with
                | Some(:? FSharpField) -> true
                | _ -> false
            | SynExpr.DotIndexedSet(objectExpr = obj) -> bclTarget obj
            | SynExpr.Set(targetExpr = SynExpr.App(funcExpr = obj; argExpr = SynExpr.ArrayOrListComputed _)) ->
                bclTarget obj
            | _ -> false

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

        // every segment after the receiver's root reads the SAME dictionary
        // each time: a field, a BCL getter, or a `member val` (backed by a
        // field). A computed property - `member _.Table = Dictionary()` -
        // may hand the reads another dictionary than the header walked
        let receiverStable (receiverIds: Ident list) =
            [ 2 .. receiverIds.Length ]
            |> List.forall (fun n ->
                match resolve (List.take n receiverIds) with
                | Some(:? FSharpField) -> true
                | Some(:? FSharpMemberOrFunctionOrValue as v) when v.IsProperty ->
                    (try
                        (OptionModule.enclosingFullName v).StartsWith "System."
                        || (v.HasGetterMethod
                            && v.GetterMethod.Attributes
                               |> Seq.exists (fun a -> a.AttributeType.DisplayName = "CompilerGeneratedAttribute"))
                        || autoProperties.Value.Contains((v.DisplayName, v.DeclarationLocation.StartLine))
                     with _ -> // an unreadable property is no proof; fsharpanalyzer: ignore-line FR0055
                         false)
                | Some(:? FSharpMemberOrFunctionOrValue as v) -> not v.IsMember
                | _ -> false)

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

                        // a dictionary that cannot be this one: its type
                        // arguments differ (`Dictionary<string, bool>` is no
                        // `IDictionary<string, int>`), or both are classes of
                        // different types
                        let receiverType =
                            match resolve receiverIds with
                            | Some(:? FSharpMemberOrFunctionOrValue as v) -> Some v.FullType
                            | Some(:? FSharpField as f) -> Some f.FieldType
                            | _ -> None

                        let distinctDictionary (other: FSharpType) =
                            try
                                match receiverType with
                                | Some mine ->
                                    let mine = OptionModule.stripAbbreviations mine
                                    let other = OptionModule.stripAbbreviations other

                                    let name (t: FSharpType) =
                                        if t.HasTypeDefinition then
                                            t.TypeDefinition.TryFullName |> Option.defaultValue ""
                                        else
                                            ""

                                    let arguments (t: FSharpType) =
                                        t.GenericArguments
                                        |> Seq.map (fun a -> a.Format FSharpDisplayContext.Empty)
                                        |> List.ofSeq

                                    let keyed (t: FSharpType) = (name t).EndsWith "Dictionary`2"

                                    (keyed mine && keyed other && arguments mine <> arguments other)
                                    || (mine.HasTypeDefinition
                                        && other.HasTypeDefinition
                                        && not mine.TypeDefinition.IsInterface
                                        && not other.TypeDefinition.IsInterface
                                        && name mine <> name other)
                                | None -> false
                            with _ -> // fsharpanalyzer: ignore-line FR0055
                                false

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
                                        not ((OptionModule.fullNameOf case).StartsWith "Microsoft.FSharp.")
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

                                    // a writing member of a dictionary that
                                    // cannot be this one: `seen.Add(k, true)`
                                    let onDistinctDictionary (ids: Ident list) (symbol: FSharpSymbol) =
                                        ids.Length >= 2
                                        && (match symbol with
                                            | :? FSharpMemberOrFunctionOrValue as v ->
                                                aliasTypes.Contains(OptionModule.enclosingFullName v)
                                            | _ -> false)
                                        && (match resolve (List.take (ids.Length - 1) ids) with
                                            | Some(:? FSharpMemberOrFunctionOrValue as owner) ->
                                                distinctDictionary owner.FullType
                                            | Some(:? FSharpField as owner) -> distinctDictionary owner.FieldType
                                            | _ -> false)

                                    // a value of an interface type handed on:
                                    // `Array.Sort(arr, cmp)` calls into it
                                    let interfaceValue (symbol: FSharpSymbol) =
                                        try
                                            let t =
                                                match symbol with
                                                | :? FSharpMemberOrFunctionOrValue as v when not v.IsMember ->
                                                    Some v.FullType
                                                | :? FSharpField as f -> Some f.FieldType
                                                | _ -> None

                                            t
                                            |> Option.map OptionModule.stripAbbreviations
                                            |> Option.exists (fun t ->
                                                t.HasTypeDefinition && t.TypeDefinition.IsInterface)
                                        with _ -> // fsharpanalyzer: ignore-line FR0055
                                            false

                                    let effectOfIds (ids: Ident list) =
                                        [ 1 .. ids.Length ]
                                        |> List.map (fun n ->
                                            match resolve (List.take n ids) with
                                            | Some symbol when n = ids.Length && onDistinctDictionary ids symbol ->
                                                Safe
                                            | Some symbol when n = ids.Length && interfaceValue symbol -> Called
                                            | Some symbol -> effectOf symbol
                                            | None -> InPlace)
                                        |> combined

                                    let effect =
                                        match inner, names with
                                        | _, Some ids when isReceiverPrefix ids ->
                                            // the receiver itself: a read-only
                                            // member, or handed to something
                                            if
                                                ids.Length = receiverIds.Length + 1
                                                && readOnlyMembers.Contains (List.last ids).idText
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
                                                | None -> InPlace)
                                            |> combined
                                        | SynExpr.New(targetType = t), _ ->
                                            let typeIds =
                                                match t with
                                                | SynType.LongIdent(SynLongIdent(id = ids))
                                                | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids))) ->
                                                    ids
                                                | _ -> []

                                            match typeIds with
                                            | [] -> InPlace
                                            | ids ->
                                                match resolve ids with
                                                | Some(:? FSharpEntity as entity) when
                                                    entity.TryFullName
                                                    |> Option.exists (fun n -> n.StartsWith "System.")
                                                    ->
                                                    Safe
                                                | _ -> InPlace
                                        // the receiver reassigned: `d <- other`,
                                        // `this.d <- other`
                                        | SynExpr.LongIdentSet(longDotId = SynLongIdent(id = ids)), _ when
                                            isReceiverPrefix ids
                                            || (ids.Length < receiverIds.Length
                                                && identText ids = identText (List.take ids.Length receiverIds))
                                            ->
                                            InPlace
                                        | (SynExpr.LongIdentSet _ | SynExpr.DotSet _ | SynExpr.Set _ | SynExpr.DotIndexedSet _ | SynExpr.NamedIndexedPropertySet _ | SynExpr.DotNamedIndexedPropertySet _),
                                          _ ->
                                            if
                                                escapeFree.Value || harmlessStore receiverText distinctDictionary inner
                                            then
                                                Safe
                                            else
                                                InPlace
                                        | _ -> Safe

                                    match effect with
                                    | Safe -> None
                                    | InPlace -> Some(inner.Range, inner.Range.End)
                                    | Called -> Some(inner.Range, effectEnd hazardPath inner))
                            |> Array.append (suspensions ())
                            |> Array.append (patternCalls ())

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
