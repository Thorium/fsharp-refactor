/// Generated F# programs: a module of independent declarations, each one a
/// shape some parse-only rule is written for, with the free parts (names,
/// literals, the boolean term) drawn at random. A program never refers
/// across its declarations, so a shrunk program is any sub-list of the
/// original and still parses.
module FSharp.Refactor.PropertyTests.Programs

open FsCheck
open FsCheck.FSharp
open FSharp.Refactor.PropertyTests.BoolExpr

/// One declaration. The comment names the rule the shape is for; the
/// generator's coverage test checks that every one of them still fires.
type Shape =
    /// FR0001: `match c with | true -> .. | false -> ..`
    | BoolMatch of BoolExpr
    /// FR0024: `raise (Exception "msg")`
    | RaiseMessage of string
    /// FR0094: `s.Contains("x")`
    | MethodParens of string
    /// FR0099: `let x = 1;`
    | TrailingSemi of int
    /// FR0096: `let f (x) = x`
    | PatternParens
    /// FR0097: `(x: (int))`
    | TypeParens
    /// FR0098: `(x: System.Int32)`
    | TypeAbbrev
    /// FR0060: `[<A>] [<B>]`; FR0082 `[<ObsoleteAttribute>]`; FR0083 `[<Obsolete()>]`
    | Attributes of int
    /// FR0095: `fun x -> x`
    | IdLambda
    /// FR0010: `if c then true else false`
    | IfBool of BoolExpr
    /// FR0010: `List.length xs = 0`
    | LengthZero
    /// FR0004: `xs |> Seq.toList |> List.filter f`
    | ConversionPipe
    /// FR0086: `$"no holes"`
    | HoleFree of string
    /// FR0073: `let! r = g () \n match r with`
    | MatchBang
    /// FR0101: `for i in 0 .. xs.Length - 1 do .. xs.[i]`
    | IndexedFor
    /// FR0103: `if o :? A then .. elif o :? B then ..`
    | TypeTestLadder
    /// FR0013: `List.length(xs)`
    | RedundantArgParens
    /// FR0011/FR0012: `not (a = b)`, De Morgan
    | Negated of BoolExpr
    /// FR0108/FR0109: a boolean term as it comes
    | BoolFn of BoolExpr
    /// FR0084: ``` ``name`` ```
    | Backticks

let private parameters =
    variables |> Array.map (fun v -> $"({v}: int)") |> String.concat " "

/// The declaration for a shape, at position `i` in the module.
let print (i: int) (shape: Shape) : string =
    match shape with
    | BoolMatch e -> $"let f{i} {parameters} =\n    match {printBool e} with\n    | true -> 1\n    | false -> 2"
    | RaiseMessage s -> $"let f{i} () = raise (Exception \"{s}\")"
    | MethodParens s -> $"let f{i} (s: string) = s.Contains(\"{s}\")"
    | TrailingSemi n -> $"let f{i} () =\n    let x = {n};\n    x + 1"
    | PatternParens -> $"let f{i} (x) = x"
    | TypeParens -> $"let f{i} (x: (int)) = x"
    | TypeAbbrev -> $"let f{i} (x: System.Int32) = x"
    | Attributes n ->
        // two or three bracket groups, the first with its suffix, the
        // second with empty parens: three rules on one declaration
        let extra = if n % 2 = 0 then "" else " [<Sealed>]"
        $"[<ObsoleteAttribute>] [<AllowNullLiteral()>]{extra}\ntype T{i}() =\n    member _.Value = {n}"
    | IdLambda -> $"let f{i} (xs: int list) = xs |> List.map (fun x -> x)"
    | IfBool e -> $"let f{i} {parameters} = if {printBool e} then true else false"
    | LengthZero -> $"let f{i} (xs: int list) = List.length xs = 0"
    | ConversionPipe -> $"let f{i} (xs: seq<int>) = xs |> Seq.toList |> List.filter (fun x -> x > 1)"
    | HoleFree s -> $"let v{i} = $\"{s}\""
    | MatchBang ->
        $"let f{i} (g: unit -> Async<int option>) =\n    async {{\n        let! r = g ()\n\n        match r with\n        | Some v -> return v\n        | None -> return 0\n    }}"
    | IndexedFor -> $"let f{i} (xs: int[]) =\n    for i in 0 .. xs.Length - 1 do\n        printfn \"%%d\" xs.[i]"
    | TypeTestLadder ->
        $"let f{i} (o: obj) =\n    if (o :? string) then (o :?> string).Length\n    elif (o :? int) then (o :?> int)\n    else 0"
    | RedundantArgParens -> $"let f{i} (xs: int list) = List.length(xs)"
    | Negated e -> $"let f{i} {parameters} = not ({printBool e})"
    | BoolFn e -> $"let f{i} {parameters} = {printBool e}"
    | Backticks -> $"let ``v{i}`` = {i}"

/// The module: every shape as one declaration, in order.
let program (shapes: Shape list) : string =
    let decls = shapes |> List.mapi print |> String.concat "\n\n"
    $"module Test\n\nopen System\n\n{decls}\n"

// ---- generation ----

/// Letters only: safe inside a string literal and an interpolated one.
let private genWord =
    Gen.choose (1, 8)
    |> Gen.bind (fun n -> Gen.elements [ 'a' .. 'z' ] |> List.replicate n |> Gen.sequenceToList)
    |> Gen.map (Array.ofList >> System.String)

let genShape (size: int) : Gen<Shape> =
    let term = genBool (size / 2)

    Gen.frequency
        [
            3, Gen.map BoolMatch term
            2, Gen.map RaiseMessage genWord
            2, Gen.map MethodParens genWord
            2, Gen.map TrailingSemi (Gen.choose (0, 99))
            1, Gen.constant PatternParens
            1, Gen.constant TypeParens
            1, Gen.constant TypeAbbrev
            2, Gen.map Attributes (Gen.choose (0, 9))
            1, Gen.constant IdLambda
            3, Gen.map IfBool term
            1, Gen.constant LengthZero
            1, Gen.constant ConversionPipe
            2, Gen.map HoleFree genWord
            1, Gen.constant MatchBang
            1, Gen.constant IndexedFor
            1, Gen.constant TypeTestLadder
            1, Gen.constant RedundantArgParens
            3, Gen.map Negated term
            4, Gen.map BoolFn term
            1, Gen.constant Backticks
        ]

let genProgram: Gen<Shape list> =
    Gen.sized (fun size ->
        gen {
            let! count = Gen.choose (1, max 1 (size / 4))
            return! List.replicate count (genShape size) |> Gen.sequenceToList
        })

/// A shape's own smaller versions: its boolean term shrunk.
let shrinkShape (shape: Shape) : seq<Shape> =
    let inner make e = shrinkBool e |> Seq.map make

    match shape with
    | BoolMatch e -> inner BoolMatch e
    | IfBool e -> inner IfBool e
    | Negated e -> inner Negated e
    | BoolFn e -> inner BoolFn e
    | _ -> Seq.empty

/// Drop one declaration, or shrink one in place.
let shrinkProgram (shapes: Shape list) : seq<Shape list> =
    seq {
        for i in 0 .. shapes.Length - 1 do
            yield List.removeAt i shapes

        for i in 0 .. shapes.Length - 1 do
            for smaller in shrinkShape shapes.[i] -> List.updateAt i smaller shapes
    }

let arbitrary: Arbitrary<Shape list> = Arb.fromGenShrink (genProgram, shrinkProgram)
