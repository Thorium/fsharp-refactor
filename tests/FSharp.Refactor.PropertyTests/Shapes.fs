/// The contract a rule family fulfils to join the generated-program
/// properties: the declarations its rules are written for, drawn at
/// random, and the rules' own output over a checked program, as edit sets
/// and notes. The properties in TypedTests are written once over this and
/// hold for every family in Families.all.
module FSharp.Refactor.PropertyTests.Shapes

open FsCheck
open FsCheck.FSharp
open FSharp.Compiler.Text

/// One edit of a fix: the text at `Range` becomes `Replacement`.
type Edit =
    {
        Code: string
        Range: range
        Replacement: string
    }

let edit (code: string) (range: range) (replacement: string) : Edit =
    {
        Code = code
        Range = range
        Replacement = replacement
    }

/// One declaration of the generated module. `Text i` prints it with `i`
/// in every name it binds (`f{i}`, `T{i}`), so any list of shapes is a
/// module of independent declarations, and a shrunk program is any
/// sub-list of the original.
type Shape =
    {
        /// For the counterexample: which shape this was.
        Name: string
        /// The rules the shape is written for, as the coverage test counts
        /// them. A code spelled `!FR0162` is the opposite: a shape written
        /// to stay QUIET under that rule (a guarded store, an edit through an
        /// interface), and the coverage test fails when the rule fires on it.
        Codes: string list
        Text: int -> string
    }

/// The rules a shape must reach, and the rules it must not.
let expectations (shape: Shape) =
    shape.Codes
    |> List.partition (fun c -> not (c.StartsWith "!"))
    |> fun (fires, quiet) -> fires, quiet |> List.map (fun c -> c.Substring 1)

/// A rule family: its shapes, and its rules' findings over a checked
/// program. `Edits` returns every fix as the set of edits that apply
/// together (a single-edit fix is a set of one), tagged with its code;
/// `Notes` returns every advisory finding.
type Family =
    {
        Name: string
        Shapes: Gen<Shape> list
        Edits: Typed.Checked -> (string * Edit list) list
        Notes: Typed.Checked -> (string * range) list
    }

/// A shape with no free parts.
let fixed' (name: string) (codes: string list) (text: int -> string) : Gen<Shape> =
    Gen.constant
        {
            Name = name
            Codes = codes
            Text = text
        }

/// A shape with a free part drawn from `gen`.
let withFree (name: string) (codes: string list) (gen: Gen<'a>) (text: 'a -> int -> string) : Gen<Shape> =
    gen
    |> Gen.map (fun a ->
        {
            Name = $"%s{name} %A{a}"
            Codes = codes
            Text = text a
        })

/// Lowercase letters only, one to eight of them: safe in a string literal,
/// an interpolated string, an identifier tail and a comment.
let genWord: Gen<string> =
    Gen.choose (1, 8)
    |> Gen.bind (fun n -> Gen.elements [ 'a' .. 'z' ] |> List.replicate n |> Gen.sequenceToList)
    |> Gen.map (Array.ofList >> System.String)

/// A small non-negative integer literal.
let genSmall: Gen<int> = Gen.choose (0, 99)

/// The opens every generated module starts with; a shape may rely on them.
let opens =
    [
        "System"
        "System.IO"
        "System.Text"
        "System.Collections.Generic"
        "System.Threading"
        "System.Threading.Tasks"
        "System.Text.RegularExpressions"
        // the harness's stub namespace (Typed.stubs): a logger whose methods are extensions
        "Microsoft.Extensions.Logging"
    ]

/// The module: every shape as one declaration, in order.
let program (shapes: Shape list) : string =
    let header = opens |> List.map (fun o -> $"open {o}") |> String.concat "\n"
    let decls = shapes |> List.mapi (fun i s -> s.Text i) |> String.concat "\n\n"
    $"module Test\n\n{header}\n\n{decls}\n"

/// Apply one set of edits bottom-up, so earlier ranges stay valid.
let applyEdits (source: string) (edits: Edit list) : string =
    edits
    |> List.sortByDescending (fun e -> e.Range.StartLine, e.Range.StartColumn)
    |> List.fold (fun acc e -> FSharp.Refactor.Tests.Parsing.applyEdit acc e.Range e.Replacement) source

/// A program of the given families' shapes.
let genProgram (families: Family list) : Gen<Shape list> =
    let shapes = families |> List.collect (fun f -> f.Shapes)

    Gen.sized (fun size ->
        gen {
            let! count = Gen.choose (1, max 1 (size / 4))
            return! List.replicate count (Gen.oneof shapes) |> Gen.sequenceToList
        })

/// Drop one declaration.
let shrinkProgram (shapes: Shape list) : seq<Shape list> =
    seq { for i in 0 .. shapes.Length - 1 -> List.removeAt i shapes }

let arbitrary (families: Family list) : Arbitrary<Shape list> =
    Arb.fromGenShrink (genProgram families, shrinkProgram)
