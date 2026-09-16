/// FR0147 against the two attributes that change what an `open` means:
/// `[<AutoOpen>]`, which makes an open bring a module's contents with the
/// namespace, and `[<RequireQualifiedAccess>]`, which keeps a module's or
/// union's names behind their qualifier whatever is open.
module FSharp.Refactor.Tests.QualifiedNamesScopeTests

open Xunit
open FSharp.Compiler.Diagnostics
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

/// FR0147's suggestions for B, compiled after A.
let private qualifiedIn (sourceA: string) (sourceB: string) =
    let tree, sourceText, checkResults = parseAndCheckSecond sourceA sourceB
    QualifiedNames.find 3 2 tree sourceText checkResults

/// Apply a suggestion's edits to B and typecheck the result after A.
let private patched (sourceB: string) (s: QualifiedNames.Suggestion) =
    s.Edits
    |> List.sortByDescending (fun (r, _, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, _, replacement) -> applyEdit acc r replacement) sourceB

let private errorsAfter (sourceA: string) (patchedB: string) =
    let _, _, check = parseAndCheckSecond sourceA patchedB

    check.Diagnostics
    |> Array.filter (fun d -> d.Severity = FSharpDiagnosticSeverity.Error)
    |> Array.map (fun d -> d.Message)

// ---- [<AutoOpen>] ----

[<Literal>]
let private libWithAutoOpen =
    "namespace Lib\n[<AutoOpen>]\nmodule Auto =\n    let helper (x: int) = x + 1\nmodule Util =\n    let f (x: int) = x\nnamespace Other\nmodule Z =\n    let helper (x: int) = x * 2\n"

[<Fact>]
let ``an open whose AutoOpen module would capture a name the file uses from elsewhere is only noted`` () =
    // `open Lib` brings Lib.Auto's `helper` with it, and the file's bare
    // `helper` comes from Other.Z: the open would rebind it
    let source =
        "module Test\nopen Other.Z\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\nlet d = helper 4\n"

    match qualifiedIn libWithAutoOpen source with
    | [ s ] ->
        Assert.Empty s.Edits
        Assert.Contains("helper", defaultArg s.Reason "")
    | other -> failwithf "Expected one noted suggestion, got %A" other

[<Fact>]
let ``an AutoOpen module's names that the file does not use are no obstacle`` () =
    let source =
        "module Test\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\n"

    match qualifiedIn libWithAutoOpen source with
    | [ s ] ->
        let result = patched source s
        Assert.Contains("open Lib", result)
        Assert.Contains("let a = Util.f 1", result)
        Assert.Empty(errorsAfter libWithAutoOpen result)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``an assembly-level AutoOpen re-applied by the open still counts`` () =
    // `[<assembly: AutoOpen("Lib.Auto")>]` puts `helper` in scope everywhere;
    // `open Other.Z` then shadows it, and an `open Lib` placed after that
    // open would bring Lib.Auto's `helper` back on top
    let lib = "[<assembly: AutoOpen(\"Lib.Auto\")>]\ndo ()\n" + libWithAutoOpen

    let source =
        "module Test\nopen Other.Z\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\nlet d = helper 4\n"

    match qualifiedIn lib source with
    | [ s ] -> Assert.Empty s.Edits
    | [] -> ()
    | other -> failwithf "Expected the open withheld, got %A" other

[<Fact>]
let ``uses inside the file's own AutoOpen module are shortened under an open placed at the top`` () =
    // ClearBank.Net's tests: the uses sit in a nested [<AutoOpen>] module
    // that has an open of its own; the namespace open still goes at the top
    let source =
        "namespace Tests\n[<AutoOpen>]\nmodule Helpers =\n    open Other.Z\n    let a = Lib.Util.f 1\n    let b = Lib.Util.f 2\nmodule More =\n    let c = Lib.Util.f 3\n"

    match qualifiedIn libWithAutoOpen source with
    | [ s ] ->
        let result = patched source s
        Assert.StartsWith("namespace Tests\nopen Lib\n", result)
        Assert.Contains("let c = Util.f 3", result)
        Assert.Empty(errorsAfter libWithAutoOpen result)
    | other -> failwithf "Expected one suggestion, got %A" other

// ---- [<RequireQualifiedAccess>] ----

[<Fact>]
let ``a RequireQualifiedAccess module keeps its own qualifier under the open`` () =
    let lib =
        "namespace Lib\n[<RequireQualifiedAccess>]\nmodule Util =\n    let f (x: int) = x\n"

    let source =
        "module Test\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\n"

    match qualifiedIn lib source with
    | [ s ] ->
        let result = patched source s
        Assert.Contains("let a = Util.f 1", result)
        Assert.Empty(errorsAfter lib result)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a RequireQualifiedAccess union's cases keep the type under the open`` () =
    let lib =
        "namespace Lib\n[<RequireQualifiedAccess>]\ntype Kind =\n    | A\n    | B\n"

    let source =
        "module Test\nlet a = Lib.Kind.A\nlet b = Lib.Kind.B\nlet c = Lib.Kind.A\nlet d (k: Lib.Kind) = match k with | Lib.Kind.A -> 1 | Lib.Kind.B -> 2\n"

    match qualifiedIn lib source with
    | [ s ] ->
        let result = patched source s
        Assert.Contains("let a = Kind.A", result)
        Assert.DoesNotContain("Lib.Kind", result)
        Assert.Empty(errorsAfter lib result)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a RequireQualifiedAccess union's case does not block an open that a same-named local uses`` () =
    // `open Lib` brings no `A`: the union demands its qualifier, so the
    // file's own `A` from Other.Names is untouched
    let lib =
        "namespace Lib\n[<RequireQualifiedAccess>]\ntype Kind =\n    | A\n    | B\nmodule Util =\n    let f (x: int) = x\nnamespace Other\nmodule Names =\n    let A = 1\n"

    let source =
        "module Test\nopen Other.Names\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\nlet d = A + 1\n"

    match qualifiedIn lib source with
    | [ s ] ->
        Assert.NotEmpty s.Edits
        let result = patched source s
        Assert.Empty(errorsAfter lib result)
    | other -> failwithf "Expected one suggestion, got %A" other

[<Fact>]
let ``a union without the attribute whose case the file already uses from elsewhere holds the open`` () =
    // the same shape without RequireQualifiedAccess: `open Lib` would bring
    // the case `A` on top of Other.Names.A
    let lib =
        "namespace Lib\ntype Kind =\n    | A\n    | B\nmodule Util =\n    let f (x: int) = x\nnamespace Other\nmodule Names =\n    let A = 1\n"

    let source =
        "module Test\nopen Other.Names\nlet a = Lib.Util.f 1\nlet b = Lib.Util.f 2\nlet c = Lib.Util.f 3\nlet d = A + 1\n"

    match qualifiedIn lib source with
    | [ s ] -> Assert.Empty s.Edits
    | [] -> ()
    | other -> failwithf "Expected the open withheld, got %A" other
