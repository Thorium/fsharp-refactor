/// The object-programming rules and the function-shape rules around them:
/// FR0019 / FR0020 / FR0054 ObjectRules, FR0026 AutoProperty,
/// FR0032 / FR0033 / FR0047 / FR0148 ObjectDesign, FR0005 CeStrip,
/// FR0006 ActivePattern, FR0011 StructActivePattern, FR0008 TupleParams,
/// FR0023 ParamOrder, FR0057 XmlDocParams, FR0061 ArgNames, FR0161
/// StructPropertyMutation.
///
/// FR0077 ImplementMissing is called but cannot be reached from a program
/// the properties accept: it fires only on a file WITH type errors (the
/// missing members are the error), and a generated program must have
/// none. It stays wired in so the damaged-program property still runs it.
/// FR0155 SealedClass reads the project's typed results, which the
/// harness computes on first use (`Checked.Project`).
module FSharp.Refactor.PropertyTests.Families.Objects

open FsCheck.FSharp
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

/// A one-digit positive divisor, so a `%`-shaped body never divides by zero.
let private genDivisor = Gen.choose (1, 9)

let private shapes =
    [
        // FR0155: an internal class nothing inherits, stored in an array of its type
        withFree "InternalClassInArray" [ "FR0155" ] (Gen.choose (1, 8)) (fun n i ->
            $"module N{i} =\n    type internal Node{i}(v: int) =\n        member _.Value = v\n\n    let internal slots{i}: Node{i}[] = Array.zeroCreate {n}\n\n    let internal fill{i} () =\n        for k in 0 .. {n - 1} do\n            slots{i}.[k] <- Node{i} k")
        // FR0155: the type test is the other trigger
        fixed' "InternalClassTypeTested" [ "FR0155" ] (fun i ->
            $"module N{i} =\n    type internal Node{i}(v: int) =\n        member _.Value = v\n\n    let internal value{i} (o: obj) =\n        match o with\n        | :? Node{i} as n -> n.Value\n        | _ -> 0")
        // FR0161: a mutating struct member called through a property's copy
        withFree "StructPropertyBump" [ "FR0161" ] genSmall (fun n i ->
            $"module S{i} =\n    [<Struct>]\n    type Counter{i} =\n        val mutable N: int\n        member this.Bump() = this.N <- this.N + {n}\n\n    type Holder{i}() =\n        member val Counter = Counter{i}() with get, set\n\n    let bump{i} (h: Holder{i}) =\n        h.Counter.Bump()\n        h.Counter.N")
        // FR0019: Equals overridden, GetHashCode not
        withFree "EqualsWithoutHashCode" [ "FR0019" ] genWord (fun w i ->
            $"type C{i}(v: int) =\n    member _.V{w} = v\n    override this.Equals(o) =\n        match o with\n        | :? C{i} as c -> c.V{w} = v\n        | _ -> false")
        // FR0020: an abstract member read while the constructor runs
        withFree "AbstractCallInCtor" [ "FR0020" ] (Gen.elements [ "call"; "property" ]) (fun form i ->
            match form with
            | "call" ->
                $"[<AbstractClass>]\ntype B{i}() as this =\n    let initial = this.Compute()\n    member _.Initial = initial\n    abstract Compute: unit -> int"
            | _ ->
                $"[<AbstractClass>]\ntype B{i}() as this =\n    do printfn \"%%d\" this.Size\n    abstract Size: int")
        // FR0054: a raise inside GetHashCode or Dispose
        withFree
            "RaiseInSpecialMember"
            [ "FR0054" ]
            (Gen.zip (Gen.elements [ "hash"; "dispose"; "pipe" ]) genWord)
            (fun (form, w) i ->
                match form with
                | "hash" ->
                    $"type T{i}() =\n    override _.Equals(o) = false\n    override _.GetHashCode() = failwith \"{w}\""
                | "dispose" ->
                    $"type T{i}() =\n    interface System.IDisposable with\n        member _.Dispose() = failwith \"{w}\""
                | _ ->
                    $"type T{i}() =\n    override _.Equals(o) = false\n    override _.GetHashCode() = raise <| System.InvalidOperationException \"{w}\"")
        // FR0026: a mutable backing field behind a trivial get/set
        withFree "BackingFieldProperty" [ "FR0026" ] genSmall (fun n i ->
            $"type P{i}() =\n    let mutable age = {n}\n    member this.Age\n        with get () = age\n        and set v = age <- v")
        // FR0026: the string-initialised form with another member around it
        withFree "BackingFieldPropertyString" [ "FR0026" ] genWord (fun w i ->
            $"type P{i}() =\n    let mutable name = \"{w}\"\n    member _.Greet() = \"hi\"\n    member this.Name\n        with get () = name\n        and set v = name <- v")
        // FR0032: a type creating a disposable it never owns
        withFree "DisposableFieldNoInterface" [ "FR0032" ] genSmall (fun n i ->
            $"type H{i}() =\n    let stream = new MemoryStream({n})\n    member _.Size = stream.Length")
        // FR0032: two created fields; the fix rides on the first
        fixed' "TwoDisposableFields" [ "FR0032" ] (fun i ->
            $"type H{i}() =\n    let stream = new MemoryStream()\n    let reader = new StreamReader(stream)\n    member _.Read() = reader.ReadLine()")
        // FR0033: a confined member touching no instance state
        withFree "StaticCandidate" [ "FR0033" ] genSmall (fun n i ->
            $"type private Calc{i}() =\n    member _.Twice(x: int) = x * 2 + {n}")
        // FR0033: an internal member of a public type
        withFree "StaticCandidateInternalMember" [ "FR0033" ] genSmall (fun n i ->
            $"type Calc{i}(seed: int) =\n    let offset = seed * 2\n    member internal _.Twice(x: int) = x * {n}\n    member _.WithOffset(x: int) = x + offset")
        // FR0047: Dispose releases one created field and forgets the other
        fixed' "UndisposedField" [ "FR0047" ] (fun i ->
            $"type H{i}() =\n    let stream = new MemoryStream()\n    let reader = new StreamReader(stream)\n    interface IDisposable with\n        member _.Dispose() =\n            reader.Dispose()")
        // FR0047: Dispose cancels the field instead of disposing it
        fixed' "CancelledNotDisposed" [ "FR0047" ] (fun i ->
            $"type H{i}() =\n    let cts = new CancellationTokenSource()\n    member _.Token = cts.Token\n    interface IDisposable with\n        member _.Dispose() = cts.Cancel()")
        // FR0148: a public Dispose on a type that is not IDisposable
        fixed' "DisposeWithoutInterface" [ "FR0148" ] (fun i ->
            $"type S{i}(inner: MemoryStream) =\n    member _.Dispose() = inner.Dispose()")
        // FR0005: `async { return! comp }`
        fixed' "ReturnBangForward" [ "FR0005" ] (fun i -> $"let f{i} (comp: Async<int>) = async {{ return! comp }}")
        // FR0005: `async { let! v = comp in return v }`, both layouts
        withFree "LetBangForward" [ "FR0005" ] (Gen.elements [ true; false ]) (fun oneLine i ->
            if oneLine then
                $"let f{i} (comp: Async<int>) = async {{ let! v = comp in return v }}"
            else
                $"let f{i} (comp: Async<int>) =\n    async {{\n        let! v = comp\n        return v\n    }}")
        // FR0005: a wrap run at once
        withFree "WrapThenRun" [ "FR0005" ] (Gen.zip genSmall (Gen.elements [ true; false ])) (fun (n, piped) i ->
            if piped then
                $"let f{i} x = async {{ return x + {n} }} |> Async.RunSynchronously"
            else
                $"let f{i} x = Async.RunSynchronously (async {{ return x + {n} }})")
        // FR0005: `task { return x }` under the Tasks open
        withFree "TaskOfConstant" [ "FR0005" ] genSmall (fun n i -> $"let f{i} () = task {{ return {n} }}")
        // FR0006: a `when` guard that is one .NET predicate on the bound value
        withFree
            "GuardToActivePattern"
            [ "FR0006" ]
            (Gen.zip
                (Gen.elements
                    [
                        "string", "System.String.IsNullOrEmpty"
                        "string", "System.String.IsNullOrWhiteSpace"
                        "char", "System.Char.IsDigit"
                    ])
                genSmall)
            (fun ((ty, guard), n) i ->
                $"let f{i} (s: {ty}) =\n    match s with\n    | s when {guard} s -> {n}\n    | _ -> 0")
        // FR0006: the guarded variable is read by the arm
        fixed' "GuardToActivePatternReadsVar" [ "FR0006" ] (fun i ->
            $"let g{i} (s: string) =\n    match s with\n    | s when System.String.IsNullOrEmpty s -> s.Length\n    | s -> 0")
        // FR0011: a private partial active pattern returning a literal option
        withFree
            "OptionActivePattern"
            [ "FR0011" ]
            (Gen.zip (Gen.elements [ true; false ]) genDivisor)
            (fun (ifForm, d) i ->
                if ifForm then
                    $"let private (|Even{i}|_|) (n: int) = if n %% {d} = 0 then Some n else None"
                else
                    $"let private (|Positive{i}|_|) (n: int) =\n    match n with\n    | n when n > {d} -> Some n\n    | _ -> None")
        // FR0008: a private tupled function nothing calls yet
        fixed' "TupledPrivate" [ "FR0008" ] (fun i -> $"let private add{i} (a, b) = a + b")
        // FR0008: the recursive form carries its own call site
        withFree "TupledPrivateRec" [ "FR0008" ] genSmall (fun n i ->
            $"let rec private count{i} (n, acc) =\n    if n = 0 then acc else count{i} (n - 1, acc + {n})")
        // FR0008: annotated elements, and a call from the same module
        withFree "TupledPrivateCalled" [ "FR0008" ] genWord (fun w i ->
            $"module M{i} =\n    let private describe{i} (name: string, count: int) = sprintf \"%%s: %%d\" name count\n    let d{i} = describe{i} (\"{w}\", 3)")
        // FR0023: data-first private function with an eta-blocking lambda site
        withFree "DataFirstWithLambda" [ "FR0023" ] genSmall (fun n i ->
            $"module P{i} =\n    let private scale{i} (x: float) (k: int) = x * float k\n    let doubled{i} (xs: float list) = xs |> List.map (fun x -> scale{i} x {n})")
        // FR0057: a doc comment documenting one of two parameters
        withFree "HalfDocumentedParams" [ "FR0057" ] genWord (fun w i ->
            $"/// <summary>Scales {w}.</summary>\n/// <param name=\"v{i}\">The value.</param>\nlet f{i} (v{i}: int) (k{i}: int) = v{i} * k{i}")
        // FR0061: invalidArg naming no parameter, two parameters (note only)
        withFree "WrongInvalidArgName" [ "FR0061" ] genWord (fun w i ->
            $"let f{i} (v{i}: int) (k{i}: int) =\n    if k{i} = 0 then invalidArg \"{w}\" \"zero\"\n    v{i} * k{i}")
        // FR0061: one parameter, so the editor offers the rename
        withFree "WrongArgumentNullName" [ "FR0061" ] genWord (fun w i ->
            $"let g{i} (input{i}: string) =\n    if isNull input{i} then raise (System.ArgumentNullException \"{w}\")\n    input{i}.Length")
    ]

let family: Family =
    {
        Name = "Objects"
        Shapes = shapes
        Edits =
            fun c ->
                let scope = Visibility.apiChangesAllowed ()

                [
                    for s in AutoProperty.find c.Tree c.Source ->
                        "FR0026", [ for r, _, replacement in s.Edits -> edit "FR0026" r replacement ]
                    let disposables, _, undisposed = ObjectDesign.find scope c.Tree c.Source c.Check

                    for s in disposables do
                        match s.Fix with
                        | Some(r, _, replacement) -> yield "FR0032", [ edit "FR0032" r replacement ]
                        | None -> ()

                    for s in undisposed do
                        match s.Fix with
                        | Some(r, _, replacement) -> yield "FR0047", [ edit "FR0047" r replacement ]
                        | None -> ()

                    for s in SealedClass.find scope c.Tree c.Source c.Check (Some c.Project.Value) do
                        match s.Fix with
                        | Some(r, text) -> yield "FR0155", [ edit "FR0155" r text ]
                        | None -> ()

                    for s in ImplementMissing.find c.Tree c.Source c.Check ->
                        "FR0077", [ edit "FR0077" s.Range s.InsertText ]

                    for s in CeStrip.find c.Tree c.Source -> "FR0005", [ edit "FR0005" s.Range s.ReplacementText ]

                    for s in ActivePattern.find true c.Tree c.Source c.Check ->
                        "FR0006",
                        [
                            edit "FR0006" s.ClauseRange s.ClauseText
                            edit "FR0006" s.InsertRange s.InsertText
                        ]

                    for s in StructActivePattern.findWith (fun _ -> false) scope c.Tree c.Source c.Check ->
                        "FR0011", [ for e in s.Edits -> edit "FR0011" e.Range e.Replacement ]

                    for s in TupleParams.find c.Tree c.Source c.Check ->
                        "FR0008", [ for e in s.Edits -> edit "FR0008" e.Range e.Replacement ]

                    for s in ParamOrder.find c.Tree c.Source c.Check ->
                        "FR0023", [ for r, _, replacement in s.Edits -> edit "FR0023" r replacement ]

                    for s in XmlDocParams.find c.Tree c.Source do
                        match s.Insertion with
                        | Some(at, text) -> yield "FR0057", [ edit "FR0057" at text ]
                        | None -> ()

                    for s in ArgNames.find c.Tree c.Source do
                        match s.ParameterNames with
                        | [ only ] -> yield "FR0061", [ edit "FR0061" s.Range $"\"{only}\"" ]
                        | _ -> ()
                ]
        Notes =
            fun c ->
                let scope = Visibility.apiChangesAllowed ()
                let equals, ctorCalls, raises = ObjectRules.find c.Tree c.Source

                let disposables, statics, undisposed =
                    ObjectDesign.find scope c.Tree c.Source c.Check

                [
                    for s in equals -> "FR0019", s.Range
                    for s in ctorCalls -> "FR0020", s.Range
                    for s in raises -> "FR0054", s.Range
                    for s in disposables -> "FR0032", s.Range
                    for s in statics -> "FR0033", s.Range
                    for s in undisposed -> "FR0047", s.Range
                    for s in ObjectDesign.disposeWithoutInterface c.Tree c.Source c.Check -> "FR0148", s.Range
                    for s in SealedClass.find scope c.Tree c.Source c.Check (Some c.Project.Value) -> "FR0155", s.Range
                    for s in StructPropertyMutation.find c.Tree c.Source c.Check -> "FR0161", s.Range
                    for s in XmlDocParams.find c.Tree c.Source -> "FR0057", s.Range
                    for s in ArgNames.find c.Tree c.Source -> "FR0061", s.Range
                ]
    }
