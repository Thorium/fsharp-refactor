namespace FSharp.Refactor.Tests

open Xunit

/// Tests that change state the whole process reads - an environment
/// variable a rule's gate consults - run with no other test beside them:
/// xUnit runs a collection defined this way after the parallel ones, one
/// test at a time. A module joins with `[<Collection("ProcessState")>]`.
[<CollectionDefinition("ProcessState", DisableParallelization = true)>]
type ProcessStateCollection() = class end
