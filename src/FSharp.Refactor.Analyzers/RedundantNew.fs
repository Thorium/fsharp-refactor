/// Refactoring (FR0085, the ReSharper redundant-`new`): F# convention
/// reserves the `new` keyword for constructions the code must dispose —
/// the compiler itself warns the other way around (FS0760) when an
/// IDisposable is constructed WITHOUT `new`.
///
///     let sb = new StringBuilder()     →  let sb = StringBuilder()
///     use fs = new FileStream(...)     // stays: disposable, new belongs
///
/// Typed-gated: the constructed type must resolve and NOT implement
/// IDisposable; unresolved types stay untouched.
module FSharp.Refactor.RedundantNew

open System.Collections.Generic
open FSharp.Compiler.CodeAnalysis
open FSharp.Compiler.Symbols
open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Refactor.Text

type Suggestion =
    { Range: range
      OriginalText: string
      TypeName: string }

let private disposableNames =
    set [ "System.IDisposable"; "System.IAsyncDisposable" ]

let private isDisposableEntity (entity: FSharpEntity) =
    try
        // a PROVIDED type's disposability lives in what it erases to —
        // FSharp.Data's CsvProvider erases to a CsvFile that implements
        // IDisposable, and the provided entity itself reports no interface;
        // unknown, so the `new` stays
        entity.IsProvided
        || (entity.TryFullName |> Option.exists disposableNames.Contains)
        || entity.AllInterfaces
           |> Seq.exists (fun i ->
               i.HasTypeDefinition
               && (i.TypeDefinition.TryFullName |> Option.exists disposableNames.Contains))
    with OptionModule.FcsSymbolFailure ->
        true // unknown: assume disposable, keep the `new`

let private resolvesToNonDisposable (check: FSharpCheckFileResults) (source: ISourceText) (ident: Ident) =
    let r = ident.idRange
    let lineText = source.GetLineString(r.EndLine - 1)

    match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
    | Some symbolUse ->
        match symbolUse.Symbol with
        | :? FSharpEntity as entity -> not (isDisposableEntity entity)
        | :? FSharpMemberOrFunctionOrValue as value when value.IsConstructor ->
            try
                value.ApparentEnclosingEntity |> Option.exists (isDisposableEntity >> not)
            with OptionModule.FcsSymbolFailure ->
                false
        | _ -> false
    | None -> false

/// Union-case names that would CAPTURE a bare `TypeName (args)` here.
///
/// In expression position a union case wins over a type name, and `new` is
/// the only thing forcing resolution down the constructor path. Nu's
/// OpenGL.Texture declares a `LazyTexture` class and a `Texture.LazyTexture`
/// union case in the same module: dropping `new` turned a six-argument
/// construction into a one-argument case application, and the tuple was then
/// checked against the case's payload — "The type 'obj * obj * obj * obj *
/// obj * obj' is not compatible with the type 'LazyTexture'".
///
/// The disposability gate this sits beside asks whether `new` is needed for
/// DISPOSAL. This asks the other question the rule never asked: whether it is
/// needed for NAME RESOLUTION.
///
/// Collected once per file — resolving symbols per `new` expression is how
/// FR0140 came to cost 77% of a sweep's analyzer time.
let private capturingUnionCases (check: FSharpCheckFileResults) =
    try
        check.GetAllUsesOfAllSymbolsInFile()
        |> Seq.choose (fun u ->
            match u.Symbol with
            | :? FSharpUnionCase as case ->
                (try
                    Some case.DisplayName
                 with _ -> // fsharpanalyzer: ignore-line FR0055
                     None)
            | _ -> None)
        |> Set.ofSeq
    with _ -> // a file whose symbols we cannot enumerate contributes no names; fsharpanalyzer: ignore-line FR0055
        Set.empty

/// Every assembly this file can see, the project's own first. Each may carry
/// its own fragment of any namespace.
let private assemblySignatures (check: FSharpCheckFileResults) =
    try
        check.PartialAssemblySignature
        :: [ for assembly in check.ProjectContext.GetReferencedAssemblies() -> assembly.Contents ]
    with _ -> // fsharpanalyzer: ignore-line FR0055
        []

/// Names declared in MORE THAN ONE fragment of a namespace.
///
/// .NET overloads type names by generic arity, and F# `DisplayName` carries
/// no arity — `ChatResponse` and `ChatResponse<'T>` are two entities with one
/// name. A namespace is not one thing either: each assembly contributes a
/// fragment, and `DeclaringEntity` shows only the fragment the resolved type
/// lives in. Microsoft.Extensions.AI.Abstractions declares `ChatResponse`;
/// Microsoft.Extensions.AI declares `ChatResponse<'T>` in the same namespace.
///
/// `new ChatResponse()` resolves by arity across every fragment and finds
/// the right one. The bare `ChatResponse()` searches the fragments in turn
/// and stops at the FIRST that carries the name at all, choosing by arity
/// only within it: with Abstractions referenced first — the natural
/// dependency order — dropping `new` gave "The object constructor
/// 'ChatResponse`1' takes 2 argument(s) but is here given 0" (Fuuga's Eval),
/// and with the order flipped the same code compiles. The guard cannot know
/// the order a build will use, so a name split across fragments keeps its
/// `new`.
///
/// Siblings in ONE fragment are not the hazard: `TaskCompletionSource` and
/// `TaskCompletionSource<'T>`, `Lazy` and `Lazy<'T>`, or an F# `Resp` beside
/// `Resp<'a>` all sit in one assembly, where the arity choice works, and the
/// bare form compiles. Counting declarations rather than fragments would
/// have declined every one of them.
///
/// Memoised per namespace: the walk touches every referenced assembly (some
/// 50ms across 160 of them), and a file rarely constructs from more than a
/// few namespaces.
let private ambiguousNames
    (signatures: Lazy<FSharpAssemblySignature list>)
    (memo: Dictionary<string, Set<string>>)
    (ns: string)
    =
    match memo.TryGetValue ns with
    | true, names -> names
    | _ ->
        let path = ns.Split '.' |> List.ofArray

        let names =
            signatures.Value
            |> List.choose (fun signature ->
                try
                    signature.FindEntityByPath path
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    None)
            |> Seq.collect (fun fragment ->
                // each fragment contributes a name ONCE, however many
                // arities it declares it at
                try
                    fragment.NestedEntities |> Seq.map (fun e -> e.DisplayName) |> Set.ofSeq
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    Set.empty)
            |> Seq.countBy id
            |> Seq.filter (fun (_, fragments) -> fragments > 1)
            |> Seq.map fst
            |> Set.ofSeq

        memo.[ns] <- names
        names

/// Is this type's name split across fragments of its namespace? A type
/// declared in a module, or nested in another type, has one fragment only.
let private hasSameNamedSibling
    (signatures: Lazy<FSharpAssemblySignature list>)
    (memo: Dictionary<string, Set<string>>)
    (entity: FSharpEntity)
    =
    try
        match entity.DeclaringEntity, entity.Namespace with
        | Some parent, _ when not parent.IsNamespace -> false
        | _, Some ns -> (ambiguousNames signatures memo ns).Contains entity.DisplayName
        | _, None -> false
    with _ -> // fsharpanalyzer: ignore-line FR0055
        false

/// The cases of any union declared BESIDE the constructed type. Catches the
/// sibling declaration even where the case is never mentioned in this file,
/// which the use-scan above cannot see.
let private siblingUnionCases (entity: FSharpEntity) =
    try
        match entity.DeclaringEntity with
        | Some parent ->
            parent.NestedEntities
            |> Seq.filter (fun nested ->
                try
                    nested.IsFSharpUnion
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    false)
            |> Seq.collect (fun union ->
                try
                    union.UnionCases |> Seq.map (fun c -> c.DisplayName)
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    Seq.empty)
            |> Set.ofSeq
        | None -> Set.empty
    with _ -> // fsharpanalyzer: ignore-line FR0055
        Set.empty

/// A function or value declared BESIDE the type and spelled like it. The
/// same-file check below cannot see one that lives in another file, and the
/// two hazards differ sharply: a same-named function of an incompatible
/// signature makes the bare form a TYPE ERROR, which the build check catches
/// and puts back, while one that swallows any argument — generic, like
/// `let Widget (_: 'a) = Widget(0, 0)` — typechecks and silently calls the
/// function instead of the constructor. Nothing downstream sees that, so the
/// name is refused here whatever the signature.
let private siblingValues (entity: FSharpEntity) =
    try
        match entity.DeclaringEntity with
        | Some parent ->
            parent.MembersFunctionsAndValues
            |> Seq.choose (fun value ->
                try
                    if value.IsConstructor then None else Some value.DisplayName
                with _ -> // fsharpanalyzer: ignore-line FR0055
                    None)
            |> Set.ofSeq
        | None -> Set.empty
    with _ -> // fsharpanalyzer: ignore-line FR0055
        Set.empty

/// Function and value names the file's `open` declarations bring into scope.
///
/// `siblingValues` sees only the module DECLARING the type; a same-named
/// function in ANOTHER module, opened here, captures the bare name just as
/// surely. `type Parse` in one module, `let Parse (_: 'a)` in a second, both
/// opened: `new Parse()` builds the class, `Parse()` calls the function —
/// measured, the tag went from "ctor" to "function", compiling cleanly at
/// every step.
///
/// Only F# modules carry values, so opening a namespace contributes nothing
/// and costs one lookup. Collected once per file, lazily.
let private openedValueNames (signatures: Lazy<FSharpAssemblySignature list>) (index: AstIndex.Index) =
    [ for _, decl in index.Decls do
          match decl with
          | SynModuleDecl.Open(target = SynOpenDeclTarget.ModuleOrNamespace(longId = SynLongIdent(id = ids))) ->
              let path = ids |> List.map (fun i -> i.idText)

              for signature in signatures.Value do
                  let entity =
                      try
                          signature.FindEntityByPath path
                      with _ -> // fsharpanalyzer: ignore-line FR0055
                          None

                  match entity with
                  | Some entity ->
                      yield!
                          (try
                              entity.MembersFunctionsAndValues
                              |> Seq.choose (fun v -> if v.IsConstructor then None else Some v.DisplayName)
                              |> List.ofSeq
                           with _ -> // fsharpanalyzer: ignore-line FR0055
                               [])
                  | None -> ()
          | _ -> () ]
    |> Set.ofList

/// Values and functions this file binds by name, at any level: a `let`
/// spelled like a type takes the bare name over the constructor.
let private boundValueNames (index: AstIndex.Index) =
    let ofBinding (SynBinding(headPat = pat)) =
        match pat with
        | SynPat.Named(ident = SynIdent(ident = id)) -> Some id.idText
        | SynPat.LongIdent(longDotId = SynLongIdent(id = [ id ])) -> Some id.idText
        | _ -> None

    [ for _, decl in index.Decls do
          match decl with
          | SynModuleDecl.Let(bindings = bindings) -> yield! bindings |> List.choose ofBinding
          | _ -> ()
      for _, e in index.Exprs do
          match e with
          | LetOrUseE lou -> yield! lou.Bindings |> List.choose ofBinding
          | _ -> () ]
    |> Set.ofList

/// Names FSharp.Core binds as CONVERSION FUNCTIONS in every scope, where a
/// type abbreviation of the same name also lives. In expression position the
/// function wins, and it takes ONE argument — so a multi-argument
/// construction silently becomes the function applied to a TUPLE:
///
///     new string (output, index + 1, 12 - index)   →  "bcd"
///         string (output, index + 1, 12 - index)   →  "(System.Char[], 1, 3)"
///
/// Both are `string`, so this typechecks and no build check can see it.
/// management-portal's id generator was rewritten this way and every id it
/// handed out became that literal; its uniqueness test failed. `new` is the
/// only thing forcing the constructor. Written-case sensitive on purpose:
/// `new String(...)` names the type, not the function, and still drops.
let private conversionFunctions =
    set
        [ "string"
          "decimal"
          "nativeint"
          "unativeint"
          "int"
          "int8"
          "uint8"
          "int16"
          "uint16"
          "int32"
          "uint32"
          "int64"
          "uint64"
          "byte"
          "sbyte"
          "char"
          "float"
          "float32"
          "single"
          "double"
          "enum" ]

/// Would the bare name mean something else — a conversion function, a union
/// case, a value bound here, or a type of another arity — once `new` no
/// longer forces the constructor path?
let private bareNameCaptured
    (check: FSharpCheckFileResults)
    (source: ISourceText)
    (fileCases: Lazy<Set<string>>)
    (fileValues: Lazy<Set<string>>)
    (openedValues: Lazy<Set<string>>)
    (signatures: Lazy<FSharpAssemblySignature list>)
    (memo: Dictionary<string, Set<string>>)
    (ident: Ident)
    =
    conversionFunctions.Contains ident.idText
    || fileCases.Value.Contains ident.idText
    || fileValues.Value.Contains ident.idText
    || openedValues.Value.Contains ident.idText
    || (let r = ident.idRange
        let lineText = source.GetLineString(r.EndLine - 1)

        // an F#-declared type resolves to its CONSTRUCTOR here, a .NET one to
        // the entity itself
        let constructed =
            match check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ ident.idText ]) with
            | Some symbolUse ->
                match symbolUse.Symbol with
                | :? FSharpEntity as entity -> Some entity
                | :? FSharpMemberOrFunctionOrValue as value when value.IsConstructor ->
                    (try
                        value.DeclaringEntity
                     with _ -> // fsharpanalyzer: ignore-line FR0055
                         None)
                | _ -> None
            | None -> None

        match constructed with
        | Some entity ->
            (siblingUnionCases entity).Contains ident.idText
            || (siblingValues entity).Contains ident.idText
            || hasSameNamedSibling signatures memo entity
        | None -> false)

/// Find `new` on non-disposable constructions. Requires typed check
/// results.
let find (parseTree: ParsedInput) (source: ISourceText) (check: FSharpCheckFileResults) : Suggestion list =
    if OptionModule.hasErrors check then
        []
    else
        let index = AstIndex.ofTree parseTree

        // once per file, not once per `new` — and LAZILY, so a file with no
        // non-disposable construction never pays for the symbol scan at all
        let fileUnionCases = lazy (capturingUnionCases check)
        let fileValues = lazy (boundValueNames index)
        let signatures = lazy (assemblySignatures check)
        let openedValues = lazy (openedValueNames signatures index)
        let ambiguousByNamespace = Dictionary<string, Set<string>>()

        [ for _, expr in index.Exprs do
              match expr with
              | SynExpr.New(targetType = targetType) ->
                  // a type application carrying STATIC arguments — a type
                  // provider's `CsvProvider<"Data/GDP.csv", SkipRows=3>()` —
                  // needs `new`: in expression position the bare form parses
                  // `CsvProvider < "Data/GDP.csv"` as a comparison, "Invalid
                  // module/expression/type" (FSharp.Data's tests)
                  let staticArgument (t: SynType) =
                      match t with
                      | SynType.StaticConstant _
                      | SynType.StaticConstantExpr _
                      | SynType.StaticConstantNamed _ -> true
                      | _ -> false

                  let typeIdent =
                      match targetType with
                      | SynType.LongIdent(SynLongIdent(id = ids)) when not ids.IsEmpty -> Some(List.last ids)
                      | SynType.App(typeName = SynType.LongIdent(SynLongIdent(id = ids)); typeArgs = args) when
                          not (ids.IsEmpty || args |> List.exists staticArgument)
                          ->
                          Some(List.last ids)
                      | _ -> None

                  match typeIdent with
                  | Some typeIdent when
                      resolvesToNonDisposable check source typeIdent
                      && not (
                          bareNameCaptured
                              check
                              source
                              fileUnionCases
                              fileValues
                              openedValues
                              signatures
                              ambiguousByNamespace
                              typeIdent
                      )
                      ->
                      // the `new ` keyword: from the expression start to the
                      // type's start
                      let newRange =
                          Range.mkRange expr.Range.FileName expr.Range.Start targetType.Range.Start

                      let newText = textOfRange source newRange

                      if newText.TrimEnd() = "new" then
                          { Range = newRange
                            OriginalText = newText
                            TypeName = typeIdent.idText }
                  | _ -> ()
              | _ -> () ]
