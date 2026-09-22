/// Programs that DO something, for the execution property.
///
/// The other generators draw from a list of hand-written shapes, one per
/// rule, with only the leaves free — a number, a module name, a loop
/// header. That finds a rule that stopped firing; it cannot find a rule
/// that fires on a shape nobody thought to write down. FR0071's array
/// hole was exactly that: its shape was `let c = a + 3`, so no generated
/// program ever bound an array inside a loop.
///
/// So this generator draws the STRUCTURE instead, from a grammar over
/// ints, arrays, lists, strings, a `ResizeArray`, a mutable list
/// accumulator, an option, a `Dictionary`, a `DateTime` and a flag, with
/// nested loops, branches, `printfn`, comments, `try`/`with`, `Regex`,
/// `String.Format` and `async`/`task`/`query` blocks, and — where the
/// program drew the declaration — a record with a member, a union matched
/// by `function`, a `match` with `when` guards, a recursive function, an
/// active pattern, a small struct-candidate record and a private function
/// answering with an option.
///
/// What fires is a VOCABULARY question, not a sampling one: a rule
/// written over `SqlCommand` cannot fire on a program that never says
/// `SqlCommand`, however many programs are drawn. Widening the grammar
/// along one axis brings a whole cluster of rules into reach at once —
/// adding `try`/`with` alone reached FR0024, FR0055 and FR0168.
///
/// Three invariants make a generated program usable as a test:
///   - CLOSED: a name is only ever read where it is in scope, so every
///     program typechecks. A generator that emits programs the compiler
///     rejects tests nothing, so the property fails loudly on one.
///   - BOUNDED: `for` runs over a literal range, nesting stops at two,
///     and every index is drawn below its own collection's length, so a
///     program terminates and throws nothing.
///   - DETERMINISTIC: every value is a literal, the computation
///     expressions are run to completion rather than left concurrent, and
///     `stdout` is captured — so the same program traced twice agrees,
///     and a difference between two traces is the rewrite's doing.
///
/// Generation is driven by a TAPE of integers: each choice consumes one,
/// and a tape that has run out chooses 0 — the first alternative of every
/// choice — so zeroing or truncating the tape shrinks the program.
module FSharp.Refactor.PropertyTests.Effects

open FsCheck
open FsCheck.FSharp

/// How many elements a generated array or list may hold. The count is
/// free because it changes the SHAPE of the tree: a one-element literal
/// is `ArrayOrListComputed` over the element, two or more is one over a
/// `Sequential`, and a rule walking the first and not the second (as
/// FR0071 did) behaves differently on the two. Every index is drawn
/// below its own collection's length, so no generated program throws.
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
        Strings: string list
        /// `ResizeArray<int>`, grown by `Add`.
        Buffers: string list
        /// `let mutable _ : int list = []`, grown by `@` or `::`.
        Accumulators: string list
        /// `int option`.
        Options: string list
        /// Values of the generated record type.
        People: string list
        /// Values of the generated union type.
        Shapes: string list
        /// `Dictionary<string, int>`.
        Dicts: string list
        /// `DateTime`, always built from literal parts so the trace is the
        /// same every run.
        Dates: string list
        /// `let mutable _ = false`, the flag a loop sets.
        Flags: string list
        /// Which of the module's declarations this program drew, and so
        /// which names the body may use.
        Vocabulary: Set<string>
    }

let private empty =
    {
        Ints = []
        Mutables = []
        Arrays = []
        Lists = []
        Strings = []
        Buffers = []
        Accumulators = []
        Options = []
        People = []
        Shapes = []
        Dicts = []
        Dates = []
        Flags = []
        Vocabulary = Set.empty
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

/// A small vocabulary, so a generated string is short and prints plainly.
let private words = [| "a"; "ab"; "key"; "x1"; "-"; "" |]

/// Spliced rather than written inline: a `%` in an interpolated string is
/// a format specifier, and `% 2` does not compile.
let private percent = "%"

/// A `string`-valued expression. `string` of an int and `+` of two
/// strings are the two ways one is built here, plus an interpolation —
/// the shapes several of the string rules are written over.
let rec private text (t: Tape) (s: Scope) (depth: int) : string =
    let leaf () =
        let pick = t.Next(2 + s.Strings.Length)

        if pick < 2 then
            "\"" + words.[t.Next words.Length] + "\""
        else
            s.Strings.[pick - 2]

    if depth <= 0 then
        leaf ()
    else
        match t.Next 5 with
        | 0
        | 1 -> leaf ()
        | 2 -> $"({leaf ()} + {text t s (depth - 1)})"
        | 3 -> $"(string {expr t s 1})"
        | _ -> $"$\"{{{expr t s 0}}}{words.[t.Next words.Length]}\""

/// A `bool`-valued expression. Compound and negated forms are drawn too:
/// the boolean rules (the hint engine's De Morgan and negation rewrites,
/// the identity and duplicate simplifications, the redundant parentheses)
/// have nothing to work on in a bare comparison.
let rec private condition (t: Tape) (s: Scope) (depth: int) : string =
    let leaf () =
        if not s.Strings.IsEmpty && t.Next 4 = 0 then
            let op = [| "="; "<>" |].[t.Next 2]
            $"{s.Strings.[t.Next s.Strings.Length]} {op} \"{words.[t.Next words.Length]}\""
        elif not s.Flags.IsEmpty && t.Next 3 = 0 then
            s.Flags.[t.Next s.Flags.Length]
        else
            let op = [| ">"; "<"; ">="; "<>"; "=" |].[t.Next 5]
            $"{expr t s 1} {op} {t.Next 6}"

    if depth <= 0 then
        leaf ()
    else
        match t.Next 6 with
        | 0
        | 1
        | 2 -> leaf ()
        | 3 -> $"({condition t s (depth - 1)} && {condition t s (depth - 1)})"
        | 4 -> $"({condition t s (depth - 1)} || {condition t s (depth - 1)})"
        | _ -> $"(not ({condition t s (depth - 1)}))"

/// Read back every value a block bound, at the end of that block.
///
/// Without this the trace sees only what a `sink` happened to report, and
/// a rewrite that leaves an array or a mutable holding something else —
/// the shape of the FR0071 hole, where the hoisted buffer accumulated
/// across iterations instead of starting fresh — runs to the end
/// unnoticed. Reading everything back makes every value the program
/// computes part of what the property compares.
let private observe (indent: string) (bound: Scope) =
    [
        for n in List.rev (bound.Ints @ bound.Mutables) -> $"{indent}sink {n}"
        for a, length in List.rev bound.Arrays do
            for i in 0 .. length - 1 -> $"{indent}sink {a}.[{i}]"
        for l, length in List.rev bound.Lists do
            yield $"{indent}sink (List.length {l})"

            for i in 0 .. length - 1 -> $"{indent}sink {l}.[{i}]"
        for n in List.rev bound.Strings -> $"{indent}sinkText {n}"
        // a buffer and an accumulator are read whole: their length is part
        // of what a rewrite can get wrong
        for n in List.rev (bound.Buffers @ bound.Accumulators) do
            yield $"{indent}sink (Seq.length {n})"
            yield $"{indent}{n} |> Seq.iter sink"
        // the parentheses matter: `defaultArg o -1` reads as a subtraction
        for n in List.rev bound.Options -> $"{indent}sink (defaultArg {n} (-1))"
        for n in List.rev bound.People do
            yield $"{indent}sinkText {n}.Name"
            yield $"{indent}sink {n}.Age"
            yield $"{indent}sinkText {n}.Greeting"
        for n in List.rev bound.Shapes -> $"{indent}sink (area {n})"
        // a dictionary is read back in KEY ORDER: its own enumeration order
        // is an implementation detail, and a trace must not depend on one
        for n in List.rev bound.Dicts do
            yield $"{indent}sink {n}.Count"

            yield $"{indent}{n} |> Seq.sortBy (fun kv -> kv.Key) |> Seq.iter (fun kv -> sinkText kv.Key; sink kv.Value)"
        for n in List.rev bound.Dates -> $"{indent}sinkText ({n}.ToString(\"yyyy-MM-dd\"))"
        for n in List.rev bound.Flags -> $"{indent}sink (if {n} then 1 else 0)"
    ]

/// What `s` holds that `scope` did not: the names this block itself bound.
let private bound (scope: Scope) (s: Scope) =
    {
        Ints = s.Ints |> List.filter (fun n -> not (List.contains n scope.Ints))
        Mutables = s.Mutables |> List.filter (fun n -> not (List.contains n scope.Mutables))
        Arrays = s.Arrays |> List.filter (fun a -> not (List.contains a scope.Arrays))
        Lists = s.Lists |> List.filter (fun l -> not (List.contains l scope.Lists))
        Strings = s.Strings |> List.filter (fun n -> not (List.contains n scope.Strings))
        Buffers = s.Buffers |> List.filter (fun n -> not (List.contains n scope.Buffers))
        Accumulators =
            s.Accumulators
            |> List.filter (fun n -> not (List.contains n scope.Accumulators))
        Options = s.Options |> List.filter (fun n -> not (List.contains n scope.Options))
        People = s.People |> List.filter (fun n -> not (List.contains n scope.People))
        Shapes = s.Shapes |> List.filter (fun n -> not (List.contains n scope.Shapes))
        Dicts = s.Dicts |> List.filter (fun n -> not (List.contains n scope.Dicts))
        Dates = s.Dates |> List.filter (fun n -> not (List.contains n scope.Dates))
        Flags = s.Flags |> List.filter (fun n -> not (List.contains n scope.Flags))
        Vocabulary = Set.empty
    }

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

                // the accumulating write (13) is drawn more often than the
                // plain one: a plain write stores the same value on every
                // iteration, so a value left over from the iteration
                // before is invisible in the trace — which is exactly the
                // state a hoisting rule can get wrong
                if not s.Arrays.IsEmpty then
                    yield! [| 6; 7; 13; 13 |]

                if not s.Lists.IsEmpty then
                    yield! [| 8; 19 |]

                // the wider vocabulary: strings, a ResizeArray, a mutable
                // list accumulator, an option. Each brings a cluster of
                // rules into reach that an int-only program never touches.
                yield! [| 14; 16; 20; 22 |]

                if not s.Strings.IsEmpty then
                    yield! [| 15; 23 |]

                if not s.Buffers.IsEmpty then
                    yield 17

                if not s.Accumulators.IsEmpty then
                    yield! [| 21; 21 |]

                if not s.Options.IsEmpty then
                    yield 18

                // the module's own declarations, where the program drew
                // them: a record with a member, a union matched by
                // `function`, a match with `when` guards, a recursive
                // function over a list, an active pattern
                if s.Vocabulary.Contains "Person" then
                    yield 24

                if s.Vocabulary.Contains "Shape" then
                    yield 25

                if not s.People.IsEmpty then
                    yield 26

                if s.Vocabulary.Contains "describe" then
                    yield 27

                if s.Vocabulary.Contains "total" && not s.Lists.IsEmpty then
                    yield 28

                if s.Vocabulary.Contains "EvenOdd" then
                    yield 29

                if s.Vocabulary.Contains "Point" then
                    yield 48

                if s.Vocabulary.Contains "tryNumber" && not s.Strings.IsEmpty then
                    yield 49

                // computation expressions, run to completion so the trace
                // is the same every time; `printfn`, whose output the
                // fixture captures into the log as well
                yield! [| 30; 31; 32 |]

                if not s.Lists.IsEmpty then
                    yield! [| 33; 43 |]

                // a dictionary, a regex, a `try`/`with`, a DateTime, a
                // String.Format and a flag a loop sets: each the surface a
                // cluster of rules is written over
                yield! [| 34; 38; 40; 42; 44 |]

                if not s.Dicts.IsEmpty then
                    yield! [| 35; 35; 36 |]

                if not s.Strings.IsEmpty then
                    yield! [| 37; 39; 41 |]

                if not s.Dates.IsEmpty then
                    yield 45

                if not s.Flags.IsEmpty && depth < 2 then
                    yield! [| 46; 46 |]

                if not s.Arrays.IsEmpty && depth > 0 then
                    yield 47

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
            block t fresh out (indent + "    ") (depth - 1) (1 + t.Next 4) body |> ignore

        let kind = kinds.[t.Next kinds.Length]

        endsInBinding <-
            kind <= 3
            || List.contains kind [ 14; 16; 19; 20; 22; 24; 25; 30; 32; 33; 34; 38; 39; 40; 41; 42 ]

        // a comment now and then: it rides on the statement below, and a
        // rewrite that loses it or re-attaches it elsewhere is a defect
        // these rules have had before
        if t.Next 8 = 0 then
            out.Add $"{indent}// {words.[t.Next words.Length]} {words.[t.Next words.Length]}"

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

            s <-
                { s with
                    Arrays = (n, length) :: s.Arrays
                }
        | 3 ->
            let n = fresh ()
            let length = 1 + t.Next maxElements
            let elements = [ for _ in 1..length -> expr t s 1 ] |> String.concat "; "
            out.Add $"{indent}let {n} = [ {elements} ]"

            s <-
                { s with
                    Lists = (n, length) :: s.Lists
                }
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
            let c = condition t s 2
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
        | 13 ->
            let a, length = s.Arrays.[t.Next s.Arrays.Length]
            let i = t.Next length
            out.Add $"{indent}{a}.[{i}] <- {a}.[{i}] + {expr t s 1}"
        | 14 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = {text t s 2}"
            s <- { s with Strings = n :: s.Strings }
        | 15 -> out.Add $"{indent}sinkText {text t s 2}"
        | 16 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = ResizeArray<int>()"
            s <- { s with Buffers = n :: s.Buffers }
        | 17 ->
            let b = s.Buffers.[t.Next s.Buffers.Length]
            out.Add $"{indent}{b}.Add({expr t s 1})"
        | 18 ->
            let o = s.Options.[t.Next s.Options.Length]

            match t.Next 2 with
            | 0 -> out.Add $"{indent}sink (if {o}.IsSome then {o}.Value else 0)"
            | _ -> out.Add $"{indent}{o} |> Option.iter sink"
        | 19 ->
            let n = fresh ()
            let v = fresh ()
            let l, length = s.Lists.[t.Next s.Lists.Length]
            let inner = { s with Ints = v :: s.Ints }
            out.Add $"{indent}let {n} = {l} |> List.map (fun {v} -> {expr t inner 1})"

            s <-
                { s with
                    Lists = (n, length) :: s.Lists
                }
        | 20 ->
            let n = fresh ()
            out.Add $"{indent}let mutable {n} : int list = []"

            s <-
                { s with
                    Accumulators = n :: s.Accumulators
                }
        | 21 ->
            let a = s.Accumulators.[t.Next s.Accumulators.Length]

            match t.Next 3 with
            | 0 -> out.Add $"{indent}{a} <- {a} @ [ {expr t s 1} ]"
            | 1 -> out.Add $"{indent}{a} <- List.append {a} [ {expr t s 1} ]"
            | _ -> out.Add $"{indent}{a} <- {expr t s 1} :: {a}"
        | 22 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = if {condition t s 1} then Some({expr t s 1}) else None"
            s <- { s with Options = n :: s.Options }
        | 23 ->
            let str = s.Strings.[t.Next s.Strings.Length]

            match t.Next 3 with
            | 0 -> out.Add $"{indent}sink {str}.Length"
            | 1 -> out.Add $"{indent}sink (if {str}.Contains \"{words.[t.Next words.Length]}\" then 1 else 0)"
            | _ -> out.Add $"{indent}sinkText ({str}.ToUpper())"
        | 24 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = {{ Name = {text t s 1}; Age = {expr t s 1} }}"
            s <- { s with People = n :: s.People }
        | 25 ->
            let n = fresh ()

            match t.Next 2 with
            | 0 -> out.Add $"{indent}let {n} = Circle({expr t s 1})"
            | _ -> out.Add $"{indent}let {n} = Rect({expr t s 1}, {expr t s 1})"

            s <- { s with Shapes = n :: s.Shapes }
        | 26 ->
            let p = s.People.[t.Next s.People.Length]

            match t.Next 2 with
            | 0 -> out.Add $"{indent}sinkText {p}.Greeting"
            | _ -> out.Add $"{indent}sink (if {p}.Age >= Threshold then 1 else 0)"
        | 27 -> out.Add $"{indent}sinkText (describe {expr t s 1})"
        | 28 ->
            let l, _ = s.Lists.[t.Next s.Lists.Length]
            out.Add $"{indent}sink (total 0 {l})"
        | 29 -> out.Add $"{indent}sink (match {expr t s 1} with | Even -> 0 | Odd -> 1)"
        | 30 ->
            let n = fresh ()

            match t.Next 3 with
            | 0 -> out.Add $"{indent}let {n} = async {{ return {expr t s 1} }} |> Async.RunSynchronously"
            | 1 ->
                out.Add
                    $"{indent}let {n} = [| async {{ return {expr t s 1} }}; async {{ return {expr t s 1} }} |] |> Async.Parallel |> Async.RunSynchronously |> Array.sum"
            | _ -> out.Add $"{indent}let {n} = (task {{ return {expr t s 1} }}).Result"

            s <- { s with Ints = n :: s.Ints }
        | 31 ->
            match t.Next 2 with
            | 0 -> out.Add($"{indent}printfn \"" + percent + "d\" (" + expr t s 1 + ")")
            | _ -> out.Add($"{indent}printfn \"" + percent + "s\" (" + text t s 1 + ")")
        | 32 ->
            let n = fresh ()
            let v = fresh ()

            if s.Lists.IsEmpty then
                // no list to query over: a plain range serves
                out.Add $"{indent}let {n} = ResizeArray<int>([ 0 .. {t.Next 4} ])"
            else
                let l, _ = s.Lists.[t.Next s.Lists.Length]
                out.Add $"{indent}let {n} ="
                out.Add $"{indent}    query {{"
                out.Add $"{indent}        for {v} in {l} do"
                out.Add($"{indent}        where (" + v + " " + percent + " 2 = 0)")
                out.Add $"{indent}        select ({v} * {v})"
                out.Add $"{indent}    }}"
                out.Add $"{indent}    |> ResizeArray"

            s <- { s with Buffers = n :: s.Buffers }
        | 33 ->
            let n = fresh ()
            let v = fresh ()
            let l, _ = s.Lists.[t.Next s.Lists.Length]
            let inner = { s with Ints = v :: s.Ints }

            match t.Next 3 with
            | 0 -> out.Add $"{indent}let {n} = {l} |> List.filter (fun {v} -> {condition t inner 1}) |> ResizeArray"
            | 1 -> out.Add $"{indent}let {n} = {l} |> List.sortBy (fun {v} -> {expr t inner 1}) |> ResizeArray"
            | _ -> out.Add $"{indent}let {n} = {l} |> List.map (fun {v} -> {expr t inner 1}) |> ResizeArray"

            s <- { s with Buffers = n :: s.Buffers }
        | 34 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = Dictionary<string, int>()"
            s <- { s with Dicts = n :: s.Dicts }
        | 35 ->
            let d = s.Dicts.[t.Next s.Dicts.Length]
            out.Add $"{indent}{d}.[{text t s 0}] <- {expr t s 1}"
        | 36 ->
            let d = s.Dicts.[t.Next s.Dicts.Length]
            let k = text t s 0

            // the four ContainsKey shapes the dictionary rules rewrite:
            // read-with-else, add-if-absent, remove-if-present, and the
            // walk over Keys that indexes straight back
            match t.Next 5 with
            | 0 -> out.Add $"{indent}if {d}.ContainsKey {k} then sink {d}.[{k}] else sink {t.Next 9}"
            | 1 -> out.Add $"{indent}if not ({d}.ContainsKey {k}) then {d}.[{k}] <- {expr t s 1}"
            | 2 -> out.Add $"{indent}if {d}.ContainsKey {k} then {d}.Remove {k} |> ignore"
            | 3 ->
                let v = fresh ()
                out.Add $"{indent}for {v} in {d}.Keys do"
                out.Add $"{indent}    sink {d}.[{v}]"
            | _ -> out.Add $"{indent}sink (if {d}.ContainsKey {k} then 1 else 0)"
        | 37 ->
            let str = s.Strings.[t.Next s.Strings.Length]
            let pattern = words.[t.Next words.Length]

            match t.Next 3 with
            | 0 -> out.Add $"{indent}sink (if Regex.IsMatch({str}, \"{pattern}\") then 1 else 0)"
            | 1 -> out.Add $"{indent}sinkText (Regex.Replace({str}, \"{pattern}\", \"z\"))"
            | _ -> out.Add $"{indent}sink (Regex.Matches({str}, \"{pattern}\").Count)"
        | 38 ->
            let n = fresh ()
            // a literal that does not parse, so the handler is the path taken
            out.Add $"{indent}let {n} = try Int32.Parse \"nan\" with _ -> {expr t s 1}"
            s <- { s with Ints = n :: s.Ints }
        | 39 ->
            let n = fresh ()
            let str = s.Strings.[t.Next s.Strings.Length]
            out.Add $"{indent}let {n} ="
            out.Add $"{indent}    try"
            out.Add $"{indent}        Int32.Parse {str}"
            out.Add $"{indent}    with"
            out.Add $"{indent}    | :? FormatException -> {expr t s 1}"
            out.Add $"{indent}    | :? OverflowException -> {expr t s 1}"
            s <- { s with Ints = n :: s.Ints }
        | 40 ->
            let n = fresh ()
            out.Add $"{indent}let {n} = DateTime(2020, {1 + t.Next 9}, {1 + t.Next 20})"
            s <- { s with Dates = n :: s.Dates }
        | 41 ->
            let n = fresh ()
            let str = s.Strings.[t.Next s.Strings.Length]

            out.Add(
                $"{indent}let {n} = String.Format(\"{{0}}-{{1}}\", "
                + expr t s 1
                + ", "
                + str
                + ")"
            )

            s <- { s with Strings = n :: s.Strings }
        | 42 ->
            let n = fresh ()
            out.Add $"{indent}let mutable {n} = false"
            s <- { s with Flags = n :: s.Flags }
        | 43 ->
            let v = fresh ()
            let l, _ = s.Lists.[t.Next s.Lists.Length]
            out.Add $"{indent}{l} |> List.map (fun {v} -> {v} + {t.Next 5}) |> ignore"
        | 44 -> out.Add $"{indent}sink (try raise (Exception \"boom\") with _ -> {t.Next 9})"
        | 45 ->
            let d = s.Dates.[t.Next s.Dates.Length]

            match t.Next 3 with
            | 0 -> out.Add $"{indent}sink {d}.Year"
            // true for any date this generator builds, so the trace does
            // not depend on the clock — but the rules still see the shape
            | 1 -> out.Add $"{indent}sink (if DateTime.UtcNow > {d} then 1 else 0)"
            | _ -> out.Add $"{indent}sink ({d}.AddDays(1.0).Day)"
        | 46 ->
            let f = s.Flags.[t.Next s.Flags.Length]
            out.Add $"{indent}if {condition t s 1} then {f} <- true"
        | 48 ->
            match t.Next 2 with
            | 0 -> out.Add $"{indent}sink ((shift {{ X = {expr t s 1}; Y = {expr t s 1} }}).X)"
            | _ -> out.Add $"{indent}sink (unwrap (Wrap {expr t s 1}))"
        | 49 ->
            let str = s.Strings.[t.Next s.Strings.Length]
            out.Add $"{indent}sink (defaultArg (tryNumber {str}) (-1))"
        | _ ->
            // the index-based walk over a collection it only indexes
            let v = fresh ()
            let a, _ = s.Arrays.[t.Next s.Arrays.Length]
            out.Add $"{indent}for {v} in 0 .. {a}.Length - 1 do"
            out.Add $"{indent}    sink {a}.[{v}]"

    let observations = observe indent (bound scope s)
    out.AddRange observations

    // a block is an expression: an empty one, or one whose last statement
    // is a binding with nothing to read back, needs a result
    if out.Count = before || (endsInBinding && observations.IsEmpty) then
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
/// The measuring apparatus, which no fix is applied to: the log, the two
/// sinks, and `trace`, which clears the log, captures `stdout` (so a
/// `printfn` is part of what the property compares) and runs the body.
let private prologue =
    [
        "open System"
        "open System.Collections.Generic"
        "open System.Linq"
        "open System.Text.RegularExpressions"
        ""
        "let log = System.Text.StringBuilder()"
        ""
        "let sink (n: int) =" // fsharpanalyzer: ignore-line
        "    log.Append(n).Append(';') |> ignore"
        ""
        "let sinkText (s: string) =" // fsharpanalyzer: ignore-line
        "    log.Append(s).Append(';') |> ignore"
    ]

let private epilogue =
    [
        ""
        "let trace () ="
        "    log.Clear() |> ignore"
        // the writer writes INTO the log, so a printfn lands between the
        // sinks around it: a rewrite that moves one past a sink shows up
        "    let previous = System.Console.Out"
        "    System.Console.SetOut(new System.IO.StringWriter(log))"
        ""
        "    try"
        "        go ()"
        "    finally"
        "        System.Console.SetOut previous"
        ""
        "    log.ToString()"
    ]

/// The declarations a program may draw on, each with the name the body
/// gates on. They are fixed text: the variety the property needs is in
/// the statements that USE them, and a generated type declaration would
/// only make every program slower to typecheck.
let private declarations =
    [
        "Threshold", [ "[<Literal>]"; "let Threshold = 18" ]
        "Person",
        [
            "/// A record with a member."
            "type Person ="
            "    {"
            "        Name: string"
            "        Age: int"
            "    }"
            ""
            "    member this.Greeting = $\"Hello, {this.Name}!\""
        ]
        "Shape",
        [
            "type Shape ="
            "    | Circle of radius: int"
            "    | Rect of width: int * height: int"
            ""
            "let area ="
            "    function"
            "    | Circle r -> r * r * 3"
            "    | Rect(w, h) -> w * h"
        ]
        "describe",
        [
            "let describe age ="
            "    match age with"
            "    | n when n < 13 -> \"child\""
            "    | n when n < Threshold -> \"teen\""
            "    | _ -> \"adult\""
        ]
        "total",
        [
            "let rec total acc xs ="
            "    match xs with"
            "    | [] -> acc"
            "    | x :: rest -> total (acc + x) rest"
        ]
        "EvenOdd", [ "let (|Even|Odd|) n = if n % 2 = 0 then Even else Odd" ]
        // a small record of two ints and a single-case union: what the
        // struct rules are written over, left without the attribute on
        // purpose so they have something to say
        "Point",
        [
            "type private Point = { X: int; Y: int }"
            ""
            "type private Wrapper = Wrap of int"
            ""
            "let private shift (p: Point) = { p with X = p.X + 1 }"
            ""
            "let private unwrap (Wrap n) = n"
        ]
        // a private function answering with an option, which the
        // ValueOption migration reads
        "tryNumber",
        [
            "let private tryNumber (s: string) ="
            "    match Int32.TryParse s with"
            "    | true, v -> Some v"
            "    | _ -> None"
        ]
    ]

let program (choices: int list) : Program =
    let t = Tape choices
    let mutable counter = 0

    let fresh () =
        counter <- counter + 1
        $"v{counter}"

    // `describe` reads Threshold, `Person` is what `Threshold` is
    // compared against: draw Threshold whenever either is in
    let drawn =
        declarations
        |> List.filter (fun (name, _) -> name = "Threshold" || t.Next 2 = 0)
        |> List.map fst
        |> Set.ofList

    let vocabulary =
        if drawn.Contains "describe" then
            drawn.Add "Threshold"
        else
            drawn

    let declared =
        [
            for name, lines in declarations do
                if vocabulary.Contains name then
                    yield! lines
                    yield ""
        ]

    let body = ResizeArray()
    body.Add "let go () ="

    block t fresh body "    " 2 (2 + t.Next 6) { empty with Vocabulary = vocabulary }
    |> ignore

    let middle = declared @ List.ofSeq body

    {
        Source = String.concat "\n" (prologue @ [ "" ] @ middle @ epilogue)
        BodyStart = prologue.Length + 2
        BodyEnd = prologue.Length + 1 + middle.Length
    }

/// Shrink COARSELY, and only a handful of candidates per step.
///
/// Every candidate costs a typecheck and several evaluations, so the
/// obvious shrinker — one candidate per tape position — turns a failure
/// into twenty minutes of shrinking over a tape of three hundred. These
/// four cut the tape in half, in quarters, and flatten a half to zero (an
/// exhausted or zeroed tape takes the first alternative of every choice,
/// which is the smallest program). The counterexample that comes out is
/// not minimal, and the failure message prints the whole program anyway.
let private shrinkTape (choices: int list) : seq<int list> =
    let n = choices.Length

    seq {
        if n > 8 then
            List.truncate (n / 2) choices
            List.truncate (n * 3 / 4) choices
            List.mapi (fun i x -> if i >= n / 2 then 0 else x) choices
            List.mapi (fun i x -> if i % 2 = 1 then 0 else x) choices
    }

/// The tape is drawn long enough that a program of this size never runs
/// it out: an exhausted tape chooses 0 for every remaining decision, and
/// a program whose every expression is the literal `0` exercises nothing.
let arbitrary: Arbitrary<int list> =
    let generator =
        Gen.sized (fun size -> Gen.listOfLength (40 + 8 * size) (Gen.choose (0, 255)))

    Arb.fromGenShrink (generator, shrinkTape)
