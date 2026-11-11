/// Random damage to a program's text: what an editor hands the analyzers
/// mid-keystroke. The parser recovers into a partial tree, and every rule
/// must read that tree without throwing.
module FSharp.Refactor.PropertyTests.Mutation

open FsCheck
open FsCheck.FSharp

type Mutation =
    | DeleteAt of int
    | InsertAt of i: int * token: string
    | Truncate of int
    | DuplicateLine of int
    /// The n-th space beside a bracket goes: `f (x) with` is `f (x)with`,
    /// still legal, and a fix that drops the brackets must not glue tokens.
    | DeleteSpaceAtBracket of int

/// Fragments that unbalance, re-nest or reinterpret what follows them.
let private tokens =
    [
        "("
        ")"
        "["
        "]"
        "{"
        "}"
        "let "
        "match "
        "| "
        "->"
        "\n"
        "    "
        "\""
        "//"
        "(*"
        "*)"
        "fun "
        "<-"
        ":"
        "#if X\n"
        "#endif\n"
        "then "
        "else "
        ";"
        ","
        "."
        "!"
        "<@"
        "@>"
        "async {"
        "\t"
        "``"
        "$\""
        "with"
        "in "
    ]

let genMutation: Gen<Mutation> =
    Gen.frequency
        [
            3, Gen.map DeleteAt (Gen.choose (0, 999))
            3, Gen.map InsertAt (Gen.zip (Gen.choose (0, 999)) (Gen.elements tokens))
            1, Gen.map Truncate (Gen.choose (0, 999))
            1, Gen.map DuplicateLine (Gen.choose (0, 99))
            3, Gen.map DeleteSpaceAtBracket (Gen.choose (0, 999))
        ]

/// One to five mutations.
let genMutations: Gen<Mutation list> =
    Gen.choose (1, 5)
    |> Gen.bind (fun n -> List.replicate n genMutation |> Gen.sequenceToList)

/// The position itself, or the start of the surrogate pair it falls inside.
let private onCharacter (source: string) (i: int) =
    if
        i > 0
        && i < source.Length
        && System.Char.IsLowSurrogate source.[i]
        && System.Char.IsHighSurrogate source.[i - 1]
    then
        i - 1
    else
        i

/// Positions wrap around the text, so a mutation drawn blind still lands.
/// They never split a surrogate pair: half of one is no text.
let apply (source: string) (mutation: Mutation) : string =
    if source.Length = 0 then
        source
    else
        match mutation with
        | DeleteAt i ->
            let at = onCharacter source (i % source.Length)

            source.Remove(at, (if System.Char.IsSurrogatePair(source, at) then 2 else 1))
        | InsertAt(i, token) -> source.Insert(onCharacter source (i % (source.Length + 1)), token)
        | Truncate i -> source.Substring(0, onCharacter source (i % source.Length))
        | DuplicateLine i ->
            let lines = source.Split '\n'
            let line = lines.[i % lines.Length]
            String.concat "\n" (List.ofArray lines |> List.insertAt (i % lines.Length) line)
        | DeleteSpaceAtBracket n ->
            let beside (i: int) =
                source.[i] = ' '
                && (i > 0 && (source.[i - 1] = ')' || source.[i - 1] = ']')
                    || i + 1 < source.Length && (source.[i + 1] = '(' || source.[i + 1] = '['))

            match
                [|
                    for i in 0 .. source.Length - 1 do
                        if beside i then
                            i
                |]
            with
            | [||] -> source
            | spaces -> source.Remove(spaces.[n % spaces.Length], 1)

let applyAll (source: string) (mutations: Mutation list) : string = List.fold apply source mutations
