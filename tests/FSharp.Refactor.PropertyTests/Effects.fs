/// Programs that DO something, for the execution property.
///
/// The other generators draw from a list of hand-written shapes, one per
/// rule, with only the leaves free — a number, a module name, a loop
/// header. That finds a rule that stopped firing; it cannot find a rule
/// that fires on a shape nobody thought to write down. FR0071's array
/// hole was exactly that: its shape was `let c = a + 3`, so no generated
/// program ever bound an array inside a loop.
///
/// So this generator draws the STRUCTURE instead, from a grammar of
/// statements over three types (`int`, `int[]`, `int list`) and the
/// things that go wrong around loops: a binding, a mutable, an array
/// element written, a list grown, a nested loop, a branch. Every program
/// is closed (names are only ever read in scope, so it typechecks),
/// bounded (`for` over a literal range, nesting at most two, so it
/// terminates) and deterministic (every value is a literal, so two runs
/// of the same program agree).
///
/// Generation is driven by a TAPE of integers: each choice consumes one,
/// and a tape that has run out chooses 0 every time. A shorter tape is
/// therefore a smaller program, and FsCheck's list shrinker shrinks the
/// counterexample without a shrinker of our own.
module FSharp.Refactor.PropertyTests.Effects

open FsCheck
open FsCheck.FSharp

/// How many elements a generated array or list may hold. The count is
/// free because it changes the SHAPE of the tree: a one-element literal
/// is `ArrayOrListComputed` over the element, two or more is one over a
/// `Sequential`, and a rule walking the first and not the second (as
/// FR0071 did) behaves differently on the two.
/// Every index is drawn below its own collection's length, so no
/// generated program throws.
let private maxElements = 3

type private Tape(choices: int list) =
    let mutable rest = choices

    /// The next choice in [0, n).
    member _.Next(n: int) =
        if n <= 1 then
            0
        else
            match rest with
            | x :: tail ->
                rest <- tail
                ((x % n) + n) % n
            | [] -> 0

/// The names in scope, by what they hold. A collection carries its own
/// length, so every index written over it is in range.
type private Scope =
    {
        Ints: string list
        Mutables: string list
        Arrays: (string * int) list
        Lists: (string * int) list
    }

let private empty =
    {
        Ints = []
        Mutables = []
        Arrays = []
        Lists = []
    }

/// An `int`-valued expression over the names in scope. Division is left
/// out (no divisor is provably non-zero here) and so is anything that can
/// throw; `+`, `-` and `*` overflow silently and agree between runs.
let rec private expr (t: Tape) (s: Scope) (depth: int) : string =
    let leaf () =
        let readable = s.Ints @ s.Mutables
        // two slots for a literal, so a scope full of names still produces
        // constants
        let choices = 2 + readable.Length + s.Arrays.Length + s.Lists.Length
        let pick = t.Next choices

        if pick < 2 then
            string (t.Next 10)
        elif pick - 2 < readable.Length then
            readable.[pick - 2]
        else
            let k = pick - 2 - readable.Length

            let name, length =
                if k < s.Arrays.Length then
                    s.Arrays.[k]
                else
                    s.Lists.[k - s.Arrays.Length]

            $"{name}.[{t.Next length}]"

    if depth <= 0 then
        leaf ()
    else
        match t.Next 5 with
        | 0
        | 1 -> leaf ()
        | 2 -> $"({expr t s (depth - 1)} + {expr t s (depth - 1)})"
        | 3 -> $"({expr t s (depth - 1)} - {expr t s (depth - 1)})"
        | _ -> $"({expr t s (depth - 1)} * {t.Next 4})"

/// A `bool`-valued expression, for a branch condition.
let private condition (t: Tape) (s: Scope) =
    let op = [| ">"; "<"; ">="; "<>" |].[t.Next 4]
    $"{expr t s 1} {op} {t.Next 6}"

/// Emit `count` statements at `indent` into `out`, threading the scope.
/// `depth` is how many more levels of loop or branch may still be opened;
/// a nested block sees the names in scope but its own do not escape, as
/// F# scoping has it.
let rec private block
    (t: Tape)
    (fresh: unit -> string)
    (out: ResizeArray<string>)
    (indent: string)
    (depth: int)
    (count: int)
    (scope: Scope)
    : Scope =
    let mutable s = scope
    let before = out.Count
    // a block is an expression: it may not end in a binding
    let mutable endsInBinding = false

    for _ in 1..count do
        let kinds =
            [|
                yield! [| 0; 1; 2; 3; 4 |]
                if not s.Mutables.IsEmpty then
                    yield! [| 5; 12 |]

                if not s.Arrays.IsEmpty then
                    yield! [| 6; 7; 13 |]

                if not s.Lists.IsEmpty then
                    yield 8

                // loops carry most of what these rules are about, so they
                // are drawn more often than a statement that is not one
                if depth > 0 then
                    yield! [| 9; 9; 9; 10 |]

                    if not s.Lists.IsEmpty then
                        yield! [| 11; 11 |]
            |]

        // a nested block gets what is in scope here and keeps its own
        let nested (header: string) (body: Scope) =
            out.Add $"{indent}{header}"
            block t fresh out (indent + "    ") (depth - 1) (1 + t.Next 3) body |> ignore

        let kind = kinds.[t.Next kinds.Length]
        endsInBinding <- kind <= 3

        match kind with
        | 0 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = {expr t s 2}"
            s <- { s with Ints = n :: s.Ints }
        | 1 ->
            let n = fresh ()
            out.Add $"{indent}let mutable {n} = {expr t s 1}"
            s <- { s with Mutables = n :: s.Mutables }
        | 2 ->
            let n = fresh ()
            let length = 1 + t.Next maxElements
            let elements = [ for _ in 1..length -> expr t s 1 ] |> String.concat "; "
            out.Add $"{indent}let {n} = [| {elements} |]"
            s <- { s with Arrays = (n, length) :: s.Arrays }
        | 3 ->
            let n = fresh ()
            let length = 1 + t.Next maxElements
            let elements = [ for _ in 1..length -> expr t s 1 ] |> String.concat "; "
            out.Add $"{indent}let {n} = [ {elements} ]"
            s <- { s with Lists = (n, length) :: s.Lists }
        | 4 -> out.Add $"{indent}sink ({expr t s 2})"
        | 5 ->
            let m = s.Mutables.[t.Next s.Mutables.Length]
            out.Add $"{indent}{m} <- {expr t s 1}"
        | 6 ->
            let a, length = s.Arrays.[t.Next s.Arrays.Length]
            out.Add $"{indent}{a}.[{t.Next length}] <- {expr t s 1}"
        | 7 ->
            let a, length = s.Arrays.[t.Next s.Arrays.Length]
            out.Add $"{indent}sink {a}.[{t.Next length}]"
        | 8 ->
            let l, _ = s.Lists.[t.Next s.Lists.Length]
            out.Add $"{indent}sink (List.length {l})"
        | 9 ->
            let v = fresh ()
            nested $"for {v} = 0 to {t.Next 3} do" { s with Ints = v :: s.Ints }
        | 10 ->
            let c = condition t s
            nested $"if {c} then" s
            nested "else" s
        | 11 ->
            let v = fresh ()
            let l, _ = s.Lists.[t.Next s.Lists.Length]
            nested $"for {v} in {l} do" { s with Ints = v :: s.Ints }
        // the accumulating forms: what the value becomes depends on what
        // it already was, so a rewrite that changes how often a statement
        // runs, or what it runs over, shows up in the trace
        | 12 ->
            let m = s.Mutables.[t.Next s.Mutables.Length]
            out.Add $"{indent}{m} <- {m} + {expr t s 1}"
        | _ ->
            let a, length = s.Arrays.[t.Next s.Arrays.Length]
            let i = t.Next length
            out.Add $"{indent}{a}.[{i}] <- {a}.[{i}] + {expr t s 1}"

    if out.Count = before || endsInBinding then
        out.Add $"{indent}()"

    s

/// A generated program and the lines its body occupies (1-based,
/// inclusive). Only edits inside that span are applied: the log, `sink`
/// and `trace` around it are the measuring apparatus, and a rule adding
/// `private` to `trace` would break the run without saying anything about
/// the rule.
type Program =
    {
        Source: string
        BodyStart: int
        BodyEnd: int
    }

/// The fixture every program carries: a log, the `sink` that appends to
/// it, and a `trace` that clears it first, so the same program traced
/// twice answers the same.
let private prologue =
    [
        "let log = System.Text.StringBuilder()"
        ""
        "let sink (n: int) =" // fsharpanalyzer: ignore-line
        "    log.Append(n).Append(';') |> ignore"
        ""
        "let go () ="
    ]

let private epilogue =
    [
        ""
        "let trace () ="
        "    log.Clear() |> ignore"
        "    go ()"
        "    log.ToString()"
    ]

/// Read back everything the body still holds. Without this the trace
/// only sees what a `sink` inside a loop happened to report, and a
/// rewrite that leaves an array or a mutable in a different state — the
/// shape of the FR0071 hole — runs to the end unnoticed.
let private observe (indent: string) (s: Scope) =
    [
        for n in List.rev (s.Ints @ s.Mutables) -> $"{indent}sink {n}"
        for a, length in List.rev s.Arrays do
            for i in 0 .. length - 1 -> $"{indent}sink {a}.[{i}]"
        for l, length in List.rev s.Lists do
            $"{indent}sink (List.length {l})"

            for i in 0 .. length - 1 -> $"{indent}sink {l}.[{i}]"
    ]

let program (choices: int list) : Program =
    let t = Tape choices
    let mutable counter = 0

    let fresh () =
        counter <- counter + 1
        $"v{counter}"

    let body = ResizeArray()
    let final = block t fresh body "    " 2 (2 + t.Next 6) empty
    body.AddRange(observe "    " final)

    {
        Source = String.concat "\n" (prologue @ List.ofSeq body @ epilogue)
        BodyStart = prologue.Length + 1
        BodyEnd = prologue.Length + body.Count
    }

/// Drop a choice, or flatten one to 0. Both make the program smaller: a
/// tape that has run out chooses 0, and 0 is the first alternative of
/// every choice, so a flattened tape takes the simplest branch there.
let private shrinkTape (choices: int list) : seq<int list> =
    seq {
        // flattening first: it keeps every later choice where it was, so
        // the program shrinks in one place instead of being redrawn
        for i in 0 .. choices.Length - 1 do
            if choices.[i] <> 0 then
                List.updateAt i 0 choices

        for i in 0 .. choices.Length - 1 do
            List.removeAt i choices
    }

/// The tape is drawn long enough that a program of this size never runs
/// it out: an exhausted tape chooses 0 for every remaining decision, and
/// a program whose every expression is the literal `0` exercises nothing.
let arbitrary: Arbitrary<int list> =
    let generator =
        Gen.sized (fun size -> Gen.listOfLength (40 + 8 * size) (Gen.choose (0, 255)))

    Arb.fromGenShrink (generator, shrinkTape)
