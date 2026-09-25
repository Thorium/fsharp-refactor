/// Refactoring note (correctness, CA2002): locking on an object with weak
/// identity synchronizes with strangers.
///
///     lock "cache" (fun () -> ...)      // interned strings are shared
///     lock typeof<T> (fun () -> ...)    // runtime Type objects are shared
///     lock (x.GetType()) (fun () -> ...)
///     lock this (fun () -> ...)         // any holder of the reference
///     lock stdout (fun () -> ...)       // a process-wide singleton
///
/// Interned strings and runtime Type objects are process-wide singletons:
/// any other code locking the same string content or the same type takes
/// the same monitor, inviting contention and deadlocks that no local
/// reasoning can rule out. `this` is the same story with a public object,
/// and `stdout`/`Console.Out` belong to the whole process.
///
/// The remedy is a dedicated private lock object. When what is locked
/// belongs to this file by nature — a literal, a type object, `this`, or a
/// value this file defines — the editor offers it: `let private xLock =
/// obj ()` next to the locked value's definition (or before the enclosing
/// binding), and the lock taken on that. A shared object from another
/// module (`stdout`) gets the note alone: its other lockers are not here to
/// be fixed.
///
/// The `lock` function is typed-gated to FSharp.Core; identifiers resolve
/// via the check results.
module FSharp.Refactor.WeakLock

open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

[<RequireQualifiedAccess>]
type WeakKind =
    | StringValue
    | TypeObject
    /// `this`/`self`: the object itself, reachable by every holder.
    | SelfObject
    /// `stdout`, `stderr`, `Console.Out`...: a process-wide singleton.
    | SharedSingleton of name: string

type Suggestion =
    {
        Range: range
        Kind: WeakKind
        /// The locked expression's text, for the message.
        TargetText: string
        /// The editor's fix: (range, original, replacement) edits that
        /// declare a private lock object and lock on it. Empty when the
        /// locked value belongs to another module.
        Fix: (range * string * string) list
    }

let private symbolAt (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    OptionModule.symbolUseAt check (r.EndLine, r.EndColumn, lineText, [ ident.idText ])
    |> Option.map (fun u -> u.Symbol)

let private resolvesToString (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match symbolAt check source ident with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        try
            let t = OptionModule.stripAbbreviations value.FullType
            t.HasTypeDefinition && t.TypeDefinition.TryFullName = Some "System.String"
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false
    | _ -> false

let private resolvesToSelf (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    match symbolAt check source ident with
    | Some(:? FSharpMemberOrFunctionOrValue as value) ->
        try
            value.IsMemberThisValue || value.IsConstructorThisValue
        with _ -> // deliberate fail-safe probe; fsharpanalyzer: ignore-line FR0055
            false
    | _ -> false

/// The process-wide writers FSharp.Core and the BCL hand out.
let private sharedSingletons = set [ "stdout"; "stderr"; "stdin" ]

/// `x.GetType()` in either parse shape.
[<return: Struct>]
let private (|GetTypeCall|_|) (e: SynExpr) =
    match e with
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.LongIdent(longDotId = SynLongIdent(id = ids)); argExpr = UnitConst) when
        ids.Length >= 2 && (List.last ids).idText = "GetType"
        ->
        ValueSome()
    | SynExpr.App(isInfix = false; funcExpr = SynExpr.DotGet(longDotId = SynLongIdent(id = [ id ])); argExpr = UnitConst) when
        id.idText = "GetType"
        ->
        ValueSome()
    | _ -> ValueNone

/// The range of the module (nested or top-level) a path sits in directly.
let private enclosingModuleRange (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynModule(SynModuleDecl.NestedModule(range = r)) -> Some r
        | SyntaxNode.SynModuleOrNamespace(SynModuleOrNamespace(range = r)) -> Some r
        | _ -> None)

/// A `let` of the SAME module binding this name: its declaration's range,
/// for placing the lock object next to it. A binding of another module
/// would leave the lock object out of scope at the lock.
let private moduleBindingOf (index: AstIndex.Index) (moduleRange: range option) (name: string) =
    index.Decls
    |> Array.tryPick (fun (path, decl) ->
        match decl with
        | SynModuleDecl.Let(bindings = bindings) when enclosingModuleRange path = moduleRange ->
            bindings
            |> List.tryPick (fun (SynBinding(headPat = p)) ->
                match p with
                | SynPat.Named(ident = SynIdent(ident = id)) when id.idText = name -> Some decl.Range
                | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])) when id.idText = name -> Some decl.Range
                | _ -> None)
        | _ -> None)

/// The module-level declaration a path sits in, when it is a `let` (a
/// member of a type has no module-level slot for a lock object).
let private enclosingModuleLet (path: SyntaxNode list) =
    path
    |> List.tryPick (fun node ->
        match node with
        | SyntaxNode.SynModule(SynModuleDecl.Let(bindings = bindings) as decl) ->
            let name =
                bindings
                |> List.tryPick (fun (SynBinding(headPat = p)) ->
                    match p with
                    | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
                    | SynPat.LongIdent(longDotId = SynLongIdent(id = ids)) when not ids.IsEmpty ->
                        Some (List.last ids).idText
                    | _ -> None)

            Some(decl.Range, name)
        | SyntaxNode.SynModule(SynModuleDecl.Types _) -> Some(Range.range0, None)
        | _ -> None)

/// Find locks on weak-identity objects. Requires typed check results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        [
            for path, expr in index.Exprs do
                match expr with
                // the `lock x` application itself — the same node whether the
                // body follows directly or through `<|`
                | SynExpr.App(isInfix = false; funcExpr = SingleIdent lockId; argExpr = lockObj) when
                    lockId.idText = "lock"
                    ->
                    let target = stripParens lockObj

                    let weak =
                        match target with
                        | SynExpr.Const(SynConst.String _, _) -> Some WeakKind.StringValue
                        | SynExpr.TypeApp(expr = IdentName "typeof") -> Some WeakKind.TypeObject
                        | GetTypeCall -> Some WeakKind.TypeObject
                        | SynExpr.Ident id when sharedSingletons.Contains id.idText ->
                            Some(WeakKind.SharedSingleton id.idText)
                        | SynExpr.LongIdent(longDotId = SynLongIdent(id = [ c; m ])) when
                            c.idText = "Console"
                            && (m.idText = "Out" || m.idText = "Error" || m.idText = "In")
                            ->
                            Some(WeakKind.SharedSingleton $"Console.{m.idText}")
                        | SynExpr.Ident id when resolvesToString check source id -> Some WeakKind.StringValue
                        | SynExpr.Ident id when resolvesToSelf check source id -> Some WeakKind.SelfObject
                        | _ -> None

                    match weak with
                    | Some kind when OptionModule.resolvesToCoreOperator check source lockId ->
                        let targetText = textOfRange source target.Range

                        // the fix: a private lock object declared next to the
                        // locked value when this file defines it, else before
                        // the enclosing module-level binding; nothing for a
                        // singleton another module owns
                        let fix =
                            match kind with
                            | WeakKind.SharedSingleton _ -> []
                            | _ ->
                                let moduleRange = enclosingModuleRange path

                                let lockName, insertAfter =
                                    match target with
                                    | SynExpr.Ident id when (moduleBindingOf index moduleRange id.idText).IsSome ->
                                        $"{id.idText}Lock", moduleBindingOf index moduleRange id.idText
                                    | _ -> "lockObj", None

                                match insertAfter, enclosingModuleLet path with
                                | Some declRange, _ ->
                                    // after the value's own declaration, at its
                                    // indentation
                                    let indent = String.replicate declRange.StartColumn " "

                                    let at =
                                        Range.mkRange
                                            declRange.FileName
                                            (Position.mkPos (declRange.EndLine + 1) 0)
                                            (Position.mkPos (declRange.EndLine + 1) 0)

                                    [
                                        at, "", $"{indent}let private {lockName} = obj ()\n"
                                        target.Range, targetText, lockName
                                    ]
                                | None, Some(declRange, Some name) when declRange <> Range.range0 ->
                                    // before the enclosing binding, at its
                                    // indentation
                                    let lockName = $"{name}Lock"
                                    let indent = String.replicate declRange.StartColumn " "

                                    let at =
                                        Range.mkRange
                                            declRange.FileName
                                            (Position.mkPos declRange.StartLine 0)
                                            (Position.mkPos declRange.StartLine 0)

                                    [
                                        at, "", $"{indent}let private {lockName} = obj ()\n\n"
                                        target.Range, targetText, lockName
                                    ]
                                | _ -> []

                        {
                            Range = expr.Range
                            Kind = kind
                            TargetText = targetText
                            Fix = fix
                        }
                    | _ -> ()
                | _ -> ()
        ]
