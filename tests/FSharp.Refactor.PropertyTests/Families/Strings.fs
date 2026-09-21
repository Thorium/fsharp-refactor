/// The string rules: FR0031 StringConcat, FR0038 CharOverload, FR0039
/// CaseInsensitive, FR0042 SprintfInterpolation, FR0043 TypedHoles, FR0048
/// FormatArgs, FR0053 HexString, FR0106 SubstringSpan, FR0166 PrefixCompare, FR0167 CharArrayCopy, FR0138
/// StringEmptiness, FR0021 InterpToString, FR0015 RegexUsage, FR0122
/// RegexValidity, FR0125 UnicodeHygiene, FR0157 StringUnion.
///
/// FR0124 LogTemplates fires only on a call whose declaring entity's full
/// name starts with Microsoft.Extensions.Logging, Serilog or Logary, which
/// a script cannot declare; the harness's stub file (Typed.stubs) declares
/// the MEL logger and its extension methods ahead of the script for it.
module FSharp.Refactor.PropertyTests.Families.Strings

open FsCheck
open FsCheck.FSharp
open FSharp.Compiler.Symbols
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

/// A single lowercase letter, for the single-character string literals.
let private genLetter: Gen<char> = Gen.elements [ 'a' .. 'z' ]

/// Two distinct words, for a closed set of two literals.
let private genTwoWords: Gen<string * string> =
    Gen.two genWord |> Gen.filter (fun (a, b) -> a <> b)

/// The invisible characters FR0125 hunts, built from their code points so
/// this file holds none of them itself.
let private zeroWidthSpace = string (char 0x200B)

let private rightToLeftOverride = string (char 0x202E)

let private tagLatinA = System.Char.ConvertFromUtf32 0xE0041

/// Three distinct words, for a set of two arms and a third literal.
let private genThreeWords: Gen<string * string * string> =
    Gen.three genWord |> Gen.filter (fun (a, b, c) -> a <> b && b <> c && a <> c)

let private shapes =
    [
        // FR0124: a template with more placeholders than arguments, or an interpolated one
        withFree
            "LogTemplateLie"
            [ "FR0124" ]
            (Gen.zip
                (Gen.elements [ "LogError"; "LogWarning"; "LogInformation" ])
                (Gen.elements
                    [
                        "\"user {User} did {Action}\", user"
                        "$\"user {user} did something\""
                        "\"user {User} did {User}\", user, user"
                    ]))
            (fun (method, args) i -> $"let f{i} (logger: ILogger) (user: string) =\n    logger.{method}({args})")
        // FR0031: a literal-and-identifier chain
        withFree "ConcatChain" [ "FR0031" ] genWord (fun w i -> $"let f{i} (name: string) = \"{w} \" + name + \"!\"")
        // FR0031: two holes around one literal
        withFree "ConcatTwoHoles" [ "FR0031" ] genWord (fun w i ->
            $"let f{i} (prefix: string) (label: string) = prefix + \"{w}: \" + label")
        // FR0038: Contains with a single-character string, the ordinal-safe fix
        withFree "ContainsChar" [ "FR0038" ] genLetter (fun c i -> $"let f{i} (s: string) = s.Contains \"{c}\"")
        // FR0038: StringBuilder.Append of one character
        withFree "AppendChar" [ "FR0038" ] genLetter (fun c i ->
            $"let f{i} (sb: StringBuilder) = sb.Append(\"{c}\") |> ignore")
        // FR0038: an ordinal StartsWith collapses to the char overload
        withFree "OrdinalStartsWithChar" [ "FR0038" ] genLetter (fun c i ->
            $"let f{i} (s: string) = s.StartsWith(\"{c}\", StringComparison.Ordinal)")
        // FR0038: a culture-sensitive method stays advisory
        withFree "EndsWithChar" [ "FR0038" ] genLetter (fun c i -> $"let f{i} (s: string) = s.EndsWith \"{c}\"")
        // FR0038: IndexOf is culture-sensitive too
        withFree "IndexOfChar" [ "FR0038" ] genLetter (fun c i -> $"let f{i} (s: string) = s.IndexOf \"{c}\"")
        // FR0039: an invariant lowering compared with an ASCII literal
        withFree "LowerEqualsLiteral" [ "FR0039" ] genWord (fun w i ->
            $"let f{i} (role: string) = role.ToLowerInvariant() = \"{w}\"")
        // FR0039: a lowered StartsWith against an ASCII literal
        withFree "LowerStartsWith" [ "FR0039" ] genWord (fun w i ->
            $"let f{i} (path: string) = path.ToLowerInvariant().StartsWith \"{w}\"")
        // FR0039: an inequality against an upper-cased literal, wrapped in not
        withFree "UpperNotEquals" [ "FR0039" ] genWord (fun w i ->
            $"let f{i} (role: string) = role.ToUpperInvariant() <> \"{w.ToUpperInvariant()}\"")
        // FR0039: a lowered Contains, the StringComparison overload
        withFree "LowerContains" [ "FR0039" ] genWord (fun w i ->
            $"let f{i} (s: string) = s.ToLowerInvariant().Contains \"{w}\"")
        // FR0039: an upper-cased EndsWith in parentheses
        withFree "UpperEndsWith" [ "FR0039" ] genWord (fun w i ->
            $"let f{i} (path: string) = path.ToUpperInvariant().EndsWith(\".{w.ToUpperInvariant()}\")")
        // FR0039: two lowered operands, advice only
        fixed' "LowerBothSides" [ "FR0039" ] (fun i -> $"let f{i} (a: string) (b: string) = a.ToLower() = b.ToLower()")
        // FR0042: a fully applied sprintf with one hole
        withFree "SprintfOne" [ "FR0042" ] genWord (fun w i ->
            "let f" + string i + " (x: string) = sprintf \"" + w + " %s\" x")
        // FR0042: two holes of different types
        withFree "SprintfTwo" [ "FR0042" ] genWord (fun w i ->
            "let f"
            + string i
            + " (name: string) (count: int) = sprintf \"%s has %d "
            + w
            + "\" name count")
        // FR0042: an escaped percent stays escaped
        withFree "SprintfPercent" [ "FR0042" ] genWord (fun w i ->
            "let f" + string i + " (n: int) = sprintf \"%d%% " + w + "\" n")
        // FR0043: a typed hole beside an untyped one
        withFree "TypedHoleBeside" [ "FR0043" ] genWord (fun w i ->
            "let f"
            + string i
            + " (name: string) (age: int) = $\"%s{name} "
            + w
            + " {age}\"")
        // FR0043: the untyped hole is a string
        withFree "TypedHoleString" [ "FR0043" ] genWord (fun w i ->
            "let f"
            + string i
            + " (name: string) (age: int) = $\"%d{age} "
            + w
            + " {name}\"")
        // FR0048: a placeholder with no argument
        withFree "FormatMissingArg" [ "FR0048" ] genWord (fun w i ->
            "let f" + string i + " (x: int) = String.Format(\"{0} " + w + " {1}\", x)")
        // FR0048: two arguments for three placeholders
        withFree "FormatMissingThird" [ "FR0048" ] genWord (fun w i ->
            "let f"
            + string i
            + " (a: int) (b: int) = String.Format(\"{0}"
            + w
            + "{1}{2}\", a, b)")
        // FR0053: BitConverter.ToString with the dashes stripped
        fixed' "HexDashes" [ "FR0053" ] (fun i ->
            $"let f{i} (bytes: byte[]) = BitConverter.ToString(bytes).Replace(\"-\", \"\")")
        // FR0106: a Substring handed straight to Int32.Parse
        withFree "SubstringParse" [ "FR0106" ] genSmall (fun n i ->
            $"let f{i} (s: string) = Int32.Parse(s.Substring({n}, 2))")
        // FR0106: a one-argument Substring handed to Int64.Parse
        withFree "SubstringTailParse" [ "FR0106" ] genSmall (fun n i ->
            $"let f{i} (s: string) = Int64.Parse(s.Substring {n})")
        // FR0106: a Substring handed to StringBuilder.Append and to a TextWriter
        withFree "SubstringAppend" [ "FR0106" ] genSmall (fun n i ->
            $"let f{i} (s: string) (sb: System.Text.StringBuilder) (w: System.IO.TextWriter) =\n    w.Write(s.Substring {n})\n    sb.Append(s.Substring({n}, 2)).Length")
        // FR0166: a slice compared with a literal of the slice's length — exact
        withFree "SliceEqualsLiteral" [ "FR0166" ] genWord (fun w i ->
            $"let f{i} (s: string) = s[..{w.Length - 1}] = \"{w}\" || s[s.Length - {w.Length} ..] <> \"{w}\"")
        // FR0166: a Substring compared with a literal under a length guard — exact
        withFree "GuardedSubstringEqualsLiteral" [ "FR0166" ] genWord (fun w i ->
            $"let f{i} (s: string) = s.Length >= {w.Length} && s.Substring(0, {w.Length}) = \"{w}\"")
        // FR0166: a bare Substring compared with a literal — a note in a sweep
        withFree "BareSubstringEqualsLiteral" [ "FR0166" ] genWord (fun w i ->
            $"let f{i} (s: string) = s.Substring(s.Length - {w.Length}) = \"{w}\"")
        // FR0167: a ToCharArray copy read once by a loop and by Array functions
        withFree "CharArrayCopy" [ "FR0167" ] genLetter (fun ch i ->
            $"let f{i} (s: string) =\n    let mutable n = 0\n    for c in s.ToCharArray() do n <- n + int c\n    n, Array.exists (fun c -> c = '{ch}') (s.ToCharArray()), (s.ToCharArray() |> Array.forall (fun c -> c <> '{ch}'))")
        // FR0167 decoy: a Seq consumer and a bound copy stay as they are
        fixed' "CharArrayCopyKept" [ "!FR0167" ] (fun i ->
            $"let f{i} (s: string) =\n    let chars = s.ToCharArray()\n    Seq.length (Seq.filter Char.IsDigit (s.ToCharArray())) + chars.Length")
        // FR0171: an ASCII literal encoded at run time is a byte string literal
        withFree "AsciiGetBytes" [ "FR0171" ] genWord (fun w i ->
            $"let f{i} () = Encoding.UTF8.GetBytes \"{w}\" |> Array.length")
        // FR0171 must stay quiet: a variable, and a non-ASCII literal
        fixed' "GetBytesKept" [ "!FR0171" ] (fun i ->
            $"let f{i} (s: string) = Encoding.UTF8.GetBytes s |> Array.length")
        // FR0138: the guarded emptiness test, an exact rewrite
        withFree "NullOrEmptyGuarded" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if isNull x || x = \"\" then {n} else 1")
        // FR0138: the null comparison spelled with = null, and a Trim
        withFree "NullOrWhiteSpaceGuarded" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if x = null || x.Trim() = \"\" then {n} else 1")
        // FR0138: IsNullOrEmpty over a trimmed copy, advice only in a sweep
        withFree "IsNullOrEmptyTrimmed" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if String.IsNullOrEmpty(x.Trim()) then {n} else 1")
        // FR0138: the negated guarded form
        withFree "NotNullAndNotEmpty" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if not (isNull x) && x <> \"\" then {n} else 1")
        // FR0138: the bare Trim form, advice only in a sweep
        withFree "TrimEquals" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if x.Trim() = \"\" then {n} else 1")
        // FR0138: the trimmed Length form, advice only in a sweep
        withFree "TrimLengthZero" [ "FR0138" ] genSmall (fun n i ->
            $"let f{i} (x: string) = if x.Trim().Length = 0 then {n} else 1")
        // FR0021: a ToString inside an interpolated string
        withFree "InterpToString" [ "FR0021" ] genWord (fun w i -> $"let f{i} (x: int) = $\"{{x.ToString()}} {w}\"")
        // FR0021: a dotted receiver keeps its path
        withFree "InterpDottedToString" [ "FR0021" ] genWord (fun w i ->
            $"let f{i} (x: string) = $\"{w} {{x.Length.ToString()}}\"")
        // FR0021: a parenthesised receiver
        withFree "InterpParenToString" [ "FR0021" ] genSmall (fun n i ->
            $"let f{i} (a: int) = $\"{{(a + {n}).ToString()}}\"")
        // FR0015: a literal IsMatch is a Contains
        withFree "RegexContains" [ "FR0015" ] genWord (fun w i -> $"let f{i} (s: string) = Regex.IsMatch(s, \"{w}\")")
        // FR0015: an anchored literal IsMatch is a StartsWith
        withFree "RegexStartsWith" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.IsMatch(s, \"^{w}\")")
        // FR0015: a literal Replace is a string Replace
        withFree "RegexReplaceLiteral" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.Replace(s, \"{w}\", \"x\")")
        // FR0015: Match(...).Success and the Matches(...).Count tests are Contains
        withFree "RegexMatchSuccess" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.Match(s, \"{w}\").Success, Regex.Matches(s, \"{w}\").Count > 0, 0 = Regex.Matches(s, \"^{w}\").Count")
        // FR0015: a literal Split is a String.Split with that separator
        withFree "RegexSplitLiteral" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.Split(s, \"{w}\").Length")
        // FR0015: a static call with a real pattern inside a loop is hoisted
        withFree "RegexInLoop" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (xs: string list) =\n    for s in xs do\n        if Regex.IsMatch(s, \"{w}+\") then Console.WriteLine s")
        // FR0015: a static Replace with a real pattern inside a loop is hoisted
        withFree "RegexReplaceInLoop" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (xs: string list) =\n    for s in xs do\n        Console.WriteLine(Regex.Replace(s, \"{w}.\", \"-\"))")
        // FR0015: a static call inside a collection lambda runs once per element
        withFree "RegexInLambda" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (xs: string list) =\n    xs |> List.filter (fun s -> Regex.IsMatch(s, \"{w}.\"))")
        // FR0015: a Regex constructed inside a loop is hoisted
        withFree "RegexBuiltInLoop" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (xs: string list) =\n    for x in xs do\n        let r = Regex \"{w}+\"\n        r.IsMatch x |> ignore")
        // FR0015: a construction with constant options inside a lambda
        withFree "RegexOptionsInLambda" [ "FR0015" ] genWord (fun w i ->
            $"let f{i} (xs: string list) =\n    xs |> List.map (fun x -> Regex(\"{w}+\", RegexOptions.IgnoreCase).IsMatch x)")
        // FR0122: a pattern that does not compile
        withFree "RegexUnclosedGroup" [ "FR0122" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.IsMatch(s, \"({w}\")")
        // FR0122: a verbatim pattern ending in a lone backslash
        withFree "RegexTrailingBackslash" [ "FR0122" ] genWord (fun w i ->
            $"let f{i} (s: string) = Regex.IsMatch(s, @\"{w}\\\")")
        // FR0122: an invalid pattern in a constructor
        withFree "RegexBadClass" [ "FR0122" ] genWord (fun w i -> $"let r{i} = Regex(\"[{w}-\")")
        // FR0125: a zero-width space inside a literal, escaped by the fix
        withFree "ZeroWidthSpace" [ "FR0125" ] genWord (fun w i -> $"let v{i} = \"{w}{zeroWidthSpace}{w}\"")
        // FR0125: a tag-block character, an astral code point
        withFree "TagCharacter" [ "FR0125" ] genWord (fun w i -> $"let v{i} = \"{w} {tagLatinA}\"")
        // FR0125: a bidi override in a comment, advice only
        withFree "BidiComment" [ "FR0125" ] genWord (fun w i -> $"// {w} {rightToLeftOverride}{w}\nlet v{i} = 1")
        // FR0157: a parameter every call passes a literal for, the wildcard dropped
        withFree "StringUnionParam" [ "FR0157" ] genTwoWords (fun (a, b) i ->
            $"let private f{i} () =\n    let describe (mode{i}: string) =\n        match mode{i} with\n        | \"{a}\" -> 1\n        | \"{b}\" -> 2\n        | _ -> failwith \"unsupported\"\n\n    describe \"{a}\" + describe \"{b}\"")
        // FR0157: a literal no arm names keeps the wildcard and gains a case
        withFree "StringUnionExtraLiteral" [ "FR0157" ] genThreeWords (fun (a, b, c) i ->
            $"let private f{i} () =\n    let describe (mode{i}: string) =\n        match mode{i} with\n        | \"{a}\" -> 1\n        | \"{b}\" -> 2\n        | _ -> -1\n\n    describe \"{a}\" + describe \"{b}\" + describe \"{c}\"")
        // FR0157: an interpolated print and a comparison ride along
        withFree "StringUnionPrinted" [ "FR0157" ] genTwoWords (fun (a, b) i ->
            $"let private f{i} () =\n    let describe (mode{i}: string) =\n        printfn $\"mode {{mode{i}}}\"\n        let quiet = mode{i} = \"{b}\"\n\n        match mode{i} with\n        | \"{a}\" -> 1\n        | \"{b}\" -> 2\n        | _ -> -1\n\n    describe \"{a}\" + describe \"{b}\"")
        // FR0157: a Result whose every Error is a literal
        withFree "StringUnionResult" [ "FR0157" ] genTwoWords (fun (a, b) i ->
            $"let private f{i} (n: int) =\n    let load{i} (k: int) : Result<int, string> =\n        if k = 0 then Error \"{a}\"\n        elif k = 1 then Error \"{b}\"\n        else Ok k\n\n    match load{i} n with\n    | Ok v -> v\n    | Error \"{a}\" -> -1\n    | Error \"{b}\" -> -2\n    | Error _ -> 0")
    ]

/// The world FR0157 sees from one script: this file's uses, symbols and
/// types alone, as StringUnionTests builds it. The scope is open because a
/// script is a leaf compilation with no consumer.
let private stringUnionWorld (c: Typed.Checked) : StringUnion.World =
    let rec names (entities: FSharpEntity seq) =
        seq {
            for e in entities do
                yield e.DisplayName
                yield! names e.NestedEntities
        }

    {
        StringUnion.UsesOf = c.Check.GetUsesOfSymbolInFile
        StringUnion.File = (fun _ -> Some(c.Tree, c.Source))
        StringUnion.SymbolAt =
            (fun _ id ->
                let r = id.idRange

                c.Check.GetSymbolUseAtLocation(
                    r.EndLine,
                    r.EndColumn,
                    c.Source.GetLineString(r.EndLine - 1),
                    [ id.idText ]
                ))
        StringUnion.FileOrder = (fun _ -> 0)
        StringUnion.ScopeOpen = true
        StringUnion.TypeNames = names c.Check.PartialAssemblySignature.Entities |> Set.ofSeq
        StringUnion.InternalsVisible = false
        StringUnion.SourceFiles = [ "Test.fsx" ]
    }

let private stringUnions (c: Typed.Checked) =
    if StringUnion.hasCandidates c.Tree then
        StringUnion.find (stringUnionWorld c) c.Tree c.Source
    else
        []

/// A capability fix as the CLI emits it, plain in this single-framework
/// run.
let private capability (code: string) (c: Typed.Checked) r (original: string) (replacement: string) =
    let f = CapabilityFix.make c.Source r original replacement
    edit code f.FromRange f.ToText

let family: Family =
    {
        Name = "Strings"
        Shapes = shapes
        Edits =
            fun c ->
                [
                    for s in StringConcat.find c.Tree c.Source c.Check do
                        yield "FR0031", [ edit "FR0031" s.Range s.ReplacementText ]
                    for s in CharOverload.find c.Tree c.Source c.Check do
                        match s.ReplacementText with
                        | Some replacement when not (CapabilityFix.guardUnavailable ()) ->
                            yield "FR0038", [ capability "FR0038" c s.Range s.OriginalText replacement ]
                        | _ -> ()
                    for s in CaseInsensitive.find c.Tree c.Source c.Check do
                        match s.Replacement with
                        | Some replacement when not (CapabilityFix.guardUnavailable ()) ->
                            yield
                                "FR0039",
                                [
                                    capability "FR0039" c s.Range (Text.textOfRange c.Source s.Range) replacement
                                ]
                        | _ -> ()
                    for s in SprintfInterpolation.find c.Tree c.Source c.Check do
                        yield "FR0042", [ edit "FR0042" s.Range s.ReplacementText ]
                    for s in TypedHoles.find c.Tree c.Source c.Check do
                        yield "FR0043", [ edit "FR0043" s.Range s.Specifier ]
                    for s in HexString.find c.Tree c.Source c.Check do
                        yield "FR0053", [ edit "FR0053" s.Range s.ReplacementText ]
                    if not (CapabilityFix.guardUnavailable ()) then
                        for s in SubstringSpan.find c.Tree c.Source c.Check do
                            yield "FR0106", [ capability "FR0106" c s.Range "Substring" "AsSpan" ]
                        // a sweep applies the exact ones only; the bare
                        // Substring is the editor's offer and a note here
                        for s in PrefixCompare.find true c.Tree c.Source c.Check do
                            if s.Exact then
                                yield "FR0166", [ capability "FR0166" c s.Range s.OriginalText s.ReplacementText ]

                        for s in CharArrayCopy.find c.Tree c.Source c.Check do
                            if s.Exact then
                                yield "FR0167", [ capability "FR0167" c s.Range s.OriginalText s.ReplacementText ]
                    for s in StringEmptiness.find c.Tree c.Source do
                        if s.Guarded then
                            yield "FR0138", [ edit "FR0138" s.Range s.ReplacementText ]
                    for s in ByteStringLiteral.find c.Tree c.Source do
                        yield "FR0171", [ edit "FR0171" s.Range s.ReplacementText ]
                    for s in InterpToString.find c.Tree c.Source do
                        yield "FR0021", [ edit "FR0021" s.Range s.ReplacementText ]
                    for s in RegexUsage.find c.Tree c.Source do
                        if not s.Edits.IsEmpty then
                            yield "FR0015", [ for r, _, t in s.Edits -> edit "FR0015" r t ]
                    for s in UnicodeHygiene.find c.Tree c.Source do
                        match s.Fix with
                        | Some(r, _, replacement) -> yield "FR0125", [ edit "FR0125" r replacement ]
                        | None -> ()
                    for s in stringUnions c do
                        yield "FR0157", [ for e in s.Edits -> edit "FR0157" e.Range e.Replacement ]
                ]
        Notes =
            fun c ->
                [
                    for s in CharOverload.find c.Tree c.Source c.Check do
                        if s.ReplacementText.IsNone then
                            yield "FR0038", s.Range
                    for s in CaseInsensitive.find c.Tree c.Source c.Check do
                        if s.Replacement.IsNone then
                            yield "FR0039", s.Range
                    for s in FormatArgs.find c.Tree c.Source do
                        yield "FR0048", s.Range
                    for s in StringEmptiness.find c.Tree c.Source do
                        if not s.Guarded then
                            yield "FR0138", s.Range
                    for s in RegexUsage.find c.Tree c.Source do
                        if s.Edits.IsEmpty then
                            yield "FR0015", s.Range
                    for r, _, _ in RegexUsage.findInvalidPatterns c.Tree do
                        yield "FR0122", r
                    for s in LogTemplates.find c.Tree c.Source c.Check do
                        yield "FR0124", s.Range
                    for s in UnicodeHygiene.find c.Tree c.Source do
                        if s.Fix.IsNone then
                            yield "FR0125", s.Range
                    for s in PrefixCompare.find true c.Tree c.Source c.Check do
                        if not s.Exact then
                            yield "FR0166", s.Range
                    for s in CharArrayCopy.find c.Tree c.Source c.Check do
                        if not s.Exact then
                            yield "FR0167", s.Range
                ]
    }
