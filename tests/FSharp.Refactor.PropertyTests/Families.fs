/// Every rule family the generated-program properties run over. A family
/// joins by being listed here; the properties in TypedTests need nothing
/// else, and the coverage test holds every family's shapes to their codes.
module FSharp.Refactor.PropertyTests.Families.All

open FSharp.Refactor.PropertyTests.Shapes
open FSharp.Refactor.PropertyTests.Families

let all: Family list =
    [
        Dictionaries.family
        Collections.family
        Matching.family
        Correctness.family
        Objects.family
        Async.family
        Loops.family
        Security.family
        Branching.family
        Strings.family
        Declarations.family
    ]
