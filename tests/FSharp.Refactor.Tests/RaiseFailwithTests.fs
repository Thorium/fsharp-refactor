module FSharp.Refactor.Tests.RaiseFailwithTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0024 RaiseFailwith ----

let private raiseIn (source: string) =
    let tree, sourceText = parse source
    RaiseFailwith.find tree sourceText

let private assertRaiseFix (source: string) (expectedReplacement: string) =
    match raiseIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one raise suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``literal message becomes failwith`` () =
    assertRaiseFix "module Test\nlet f () = raise (System.Exception \"boom\")" "failwith \"boom\""

[<Fact>]
let ``open System constructor call becomes failwith`` () =
    assertRaiseFix "module Test\nopen System\nlet f () = raise (Exception(\"boom\"))" "failwith \"boom\""

[<Fact>]
let ``new keyword form becomes failwith`` () =
    assertRaiseFix "module Test\nopen System\nlet f (msg: string) = raise (new Exception(msg))" "failwith msg"

[<Fact>]
let ``computed message is parenthesized`` () =
    assertRaiseFix
        "module Test\nopen System\nlet f (n: int) = raise (Exception(sprintf \"bad %d\" n))"
        "failwith (sprintf \"bad %d\" n)"

[<Fact>]
let ``interpolated message stays bare`` () =
    assertRaiseFix "module Test\nopen System\nlet f (n: int) = raise (Exception $\"bad {n}\")" "failwith $\"bad {n}\""

[<Fact>]
let ``property on a method-call result is parenthesized`` () =
    assertRaiseFix
        "module Test\nopen System\nlet f (ex: exn) = raise (Exception(ex.GetType().Name))"
        "failwith (ex.GetType().Name)"

[<Fact>]
let ``exception subclasses are left alone`` () =
    Assert.Empty(raiseIn "module Test\nopen System\nlet f () = raise (ArgumentException \"boom\")")

[<Fact>]
let ``no-argument constructor is left alone`` () =
    Assert.Empty(raiseIn "module Test\nopen System\nlet f () = raise (Exception())")

[<Fact>]
let ``inner-exception overload is left alone`` () =
    Assert.Empty(raiseIn "module Test\nopen System\nlet f (inner: exn) = raise (Exception(\"boom\", inner))")

// ---- FR0025 OptionOfObj ----

let private ofObjIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    OptionOfObj.find tree sourceText checkResults

let private assertOfObj (source: string) (expectedReplacement: string) =
    match ofObjIn source with
    | [ s ] ->
        Assert.Equal(expectedReplacement, s.ReplacementText)
        let patched = applyEdit source s.Range s.ReplacementText
        Assert.True(typechecksCleanly patched, $"Patched source does not typecheck:\n%s{patched}")
    | other -> failwithf "Expected exactly one ofObj suggestion, got %d: %A" (List.length other) other

[<Fact>]
let ``isNull test becomes ofObj`` () =
    assertOfObj "let f (s: string) = if isNull s then None else Some s" "Option.ofObj s"

[<Fact>]
let ``negated isNull test becomes ofObj`` () =
    assertOfObj "let f (s: string) = if not (isNull s) then Some s else None" "Option.ofObj s"

[<Fact>]
let ``null equality test becomes ofObj`` () =
    assertOfObj "let f (s: string) = if s = null then None else Some s" "Option.ofObj s"

[<Fact>]
let ``null inequality test becomes ofObj`` () =
    assertOfObj "let f (s: string) = if s <> null then Some s else None" "Option.ofObj s"

[<Fact>]
let ``null match becomes ofObj`` () =
    assertOfObj "let f (s: string) =\n    match s with\n    | null -> None\n    | v -> Some v" "Option.ofObj s"

[<Fact>]
let ``value option variant uses ValueOption`` () =
    assertOfObj "let f (s: string) = if isNull s then ValueNone else ValueSome s" "ValueOption.ofObj s"

[<Fact>]
let ``shadowing union suppresses the suggestion`` () =
    Assert.Empty(
        ofObjIn "type Maybe = Some of string | None\nlet f (s: string) : Maybe = if isNull s then None else Some s"
    )

[<Fact>]
let ``wrapping a different value is left alone`` () =
    Assert.Empty(ofObjIn "let f (s: string) (t: string) = if isNull s then None else Some t")

[<Fact>]
let ``property access is left alone`` () =
    Assert.Empty(ofObjIn "let f (s: string) = if isNull s then None else Some (s.Trim())")

[<Fact>]
let ``a named-argument constructor keeps its raise`` () =
    // `Exception(message = "boom")` parses its argument as an op_Equality
    // application — `failwith (message = "boom")` would not compile
    Assert.Empty(raiseIn "module Test\nlet f () = raise (System.Exception(message = \"boom\"))")
