/// What kind of change each rule proposes.
///
/// The distinction that matters in practice is whether a fix is worth another
/// person's review time. Running the whole rule set over a repository you do
/// not maintain and opening a pull request from the result is a good way to
/// waste everyone's afternoon: nobody wants "removed an empty attribute
/// argument list" across two hundred files. A disposable that is never
/// disposed is a different conversation.
///
///     fsharp-refactor Their.fsproj --categories correctness,performance
///
/// is the run for someone else's codebase. Everything is the run for your own.
///
/// The four categories:
///
///   correctness — a defect. The code does something other than what it
///                 looks like it does: a race, a swallowed exception, a
///                 disposable that leaks, a comparison that never holds.
///   performance — measurably wasteful, but correct. Allocations that need
///                 not happen, repeated work, a scan where a lookup would do.
///   idiom       — the same behaviour written the way F# writes it. Worth
///                 doing, and worth agreeing on first: it is a matter of
///                 house style as much as anything.
///   cosmetic    — punctuation and spelling of code. Real cleanups, and
///                 nobody's idea of a welcome pull request from a stranger.
module FSharp.Refactor.RuleCatalog

open System

[<RequireQualifiedAccess>]
type Category =
    | Correctness
    | Performance
    | Idiom
    | Cosmetic

let name (category: Category) =
    match category with
    | Category.Correctness -> "correctness"
    | Category.Performance -> "performance"
    | Category.Idiom -> "idiom"
    | Category.Cosmetic -> "cosmetic"

let all =
    [
        Category.Correctness
        Category.Performance
        Category.Idiom
        Category.Cosmetic
    ]

let parse (text: string) =
    let wanted = text.Trim()

    all
    |> List.tryFind (fun c -> String.Equals(name c, wanted, StringComparison.OrdinalIgnoreCase))

/// The categories a stranger's repository is worth a pull request over.
let substantive = set [ Category.Correctness; Category.Performance ]

/// Every rule, by code. A rule absent here reads as `idiom`, which keeps a
/// newly added rule out of `--categories correctness` until someone has
/// decided where it belongs.
let private categories =
    [ // --- correctness: the code does not do what it looks like it does
        "FR0017", Category.Correctness, "Async discarded with ignore never runs"
        "FR0018", Category.Correctness, "check-then-add races"
        "FR0019", Category.Correctness, "Equals without GetHashCode"
        "FR0020", Category.Correctness, "abstract member called during construction"
        "FR0027", Category.Correctness, "lambda capturing this holds the object alive"
        "FR0032", Category.Correctness, "disposable field, no IDisposable"
        "FR0036", Category.Correctness, "runtime type comparison breaks on a rename"
        "FR0044", Category.Correctness, "raise ex resets the stack trace"
        "FR0045", Category.Correctness, "x = nan never holds"
        "FR0046", Category.Correctness, "locking a process-wide singleton"
        "FR0047", Category.Correctness, "Dispose that misses a field"
        "FR0048", Category.Correctness, "String.Format placeholder without an argument"
        "FR0049", Category.Correctness, "sync-over-async deadlocks"
        "FR0054", Category.Correctness, "raise inside Equals/GetHashCode/Dispose"
        "FR0055", Category.Correctness, "swallowing every exception"
        "FR0061", Category.Correctness, "invalidArg naming a parameter that does not exist"
        "FR0062", Category.Correctness, "public module-level mutable state"
        "FR0063", Category.Correctness, "raise in finally discards the exception in flight"
        "FR0064", Category.Correctness, "raising runtime-reserved exceptions"
        "FR0065", Category.Correctness, "weak cryptography"
        "FR0066", Category.Correctness, "SQL assembled from strings"
        "FR0067", Category.Correctness, "culture-sensitive parsing"
        "FR0068", Category.Correctness, "duplicate enum values conflate cases"
        "FR0072", Category.Correctness, "a wildcard hiding one or two real cases"
        "FR0075", Category.Correctness, "a disposable bound with let is never disposed"
        "FR0077", Category.Correctness, "object expression missing interface members (FS0366)"
        "FR0080", Category.Correctness, "leading TABs (FS1161)"
        "FR0089", Category.Correctness, "[ 1, 2 ] is a one-element list of a tuple"
        "FR0100", Category.Correctness, "an unfinished branch returning a plausible value"
        "FR0105", Category.Correctness, "unchecked arithmetic on near-limit constants wraps silently"
        "FR0110", Category.Correctness, "incomplete DU match gains explicit raising arms (FS0025 made loud)"

        // --- performance: correct, but doing work it need not
        "FR0004",
        Category.Performance,
        "Move List/Seq/Array conversion past the next pipeline operation (or drop it before consuming ops)"
        "FR0014",
        Category.Performance,
        "ContainsKey + indexer: two lookups (measured 1.26x); the ConcurrentDictionary race is called out in the message"
        "FR0011",
        Category.Performance,
        "Trivial partial active patterns => [<return: Struct>] ValueSome/ValueNone (perf: no allocation per match attemp..."
        "FR0015",
        Category.Performance,
        "Literal regex patterns => StartsWith/Contains/Replace/Split, the Match.Success and Matches.Count tests included"
        "FR0016",
        Category.Performance,
        "Small value-type-only unions => [<Struct>] (perf: no heap allocation per value) Edits the companion .fsi in ste..."
        "FR0021", Category.Performance, "Redundant .ToString() inside interpolated strings"
        "FR0028", Category.Performance, "N+1 queries"
        "FR0029", Category.Performance, "task state machine"
        "FR0030",
        Category.Performance,
        "A loop whose whole body is a single ResizeArray.Add becomes one AddRange call (for x in xs do acc.Add(x * 2) =>..."
        "FR0035", Category.Performance, "List/Array/Seq.contains x ys inside a loop"
        "FR0037",
        Category.Performance,
        "Build-once types constructed inside a loop: ConcurrentDictionary, HttpClient, JsonSerializerOptions (CA1869), ..."
        "FR0038",
        Category.Performance,
        "Char overloads for single-character strings (CA1834/1847/1865-67): s.Contains 'x' => s.Contains 'x' and sb.Appe..."
        "FR0039",
        Category.Performance,
        "Allocating case-insensitive comparisons (CA1862): x.ToLower() = 'literal' gets a FIX to String.Equals(x, 'lite..."
        "FR0040",
        Category.Performance,
        "Redundant membership guards (CA1853/1868, fix): if d.ContainsKey k then d.Remove k |> ignore => d.Remove k |> i..."
        "FR0041", Category.Performance, "Array.sum/average/min/max/contains on int[]/int64[] is a scalar loop"
        "FR0051",
        Category.Performance,
        "acc <- acc @ [x] / acc <- Array.append acc [|x|] inside a loop copies the accumulator per iteration"
        "FR0052",
        Category.Performance,
        "q.Count = 0 on ConcurrentQueue/Stack/Bag => q.IsEmpty (CA1836, fix): their Count walks segments, IsEmpty peeks"
        "FR0053",
        Category.Performance,
        "BitConverter.ToString(bytes).Replace('-', '') => System.Convert.ToHexString bytes (CA1872, fix)"
        "FR0058",
        Category.Performance,
        "A let rec re-entering itself through seq/taskSeq/asyncSeq { } builds a fresh enumerator per recursion level"
        "FR0059", Category.Performance, "A private function returning Some/None moves to ValueSome/ValueNone"
        "FR0069",
        Category.Performance,
        "A private/internal record field X: int option / DateTime option / Guid option boxes the struct payload"
        "FR0070", Category.Performance, "A private/internal record of at most four small struct fields gains [<Struct>]"
        "FR0071",
        Category.Performance,
        "A pure binding inside a for/while/collection lambda that depends on nothing the loop changes is re-evaluated e..."
        "FR0076", Category.Performance, "List/Array.map f |> ignore allocates a discarded list"
        "FR0079",
        Category.Performance,
        "Task.WhenAll [| t |] / Task.WaitAll / Async.Parallel [ c ] over a single-element literal adds indirection for ..."
        "FR0093", Category.Performance, "A private/internal record field X: int * int is a reference tuple"
        "FR0102", Category.Performance, "list indexing in a loop is O(i) per access"
        "FR0106",
        Category.Performance,
        "Substring copy fed to a parser, StringBuilder.Append or TextWriter.Write; AsSpan reads in place (Parse 2.6x, allocation-free)"
        "FR0104", Category.Performance, "singleton append per recursive call is O(n^2)"
        "FR0166",
        Category.Performance,
        "a prefix or suffix cut out to compare with a literal is StartsWith/EndsWith Ordinal; 4.5 => 1.9 ns, allocation-free"
        "FR0167",
        Category.Performance,
        "a ToCharArray copy read once by a for loop or Array.iter/exists/forall walks the string itself; 72 => 0 B"
        "FR0168",
        Category.Performance,
        "try T.Parse with a parse-failure or catch-all handler is T.TryParse; a failed parse costs a bool, not a throw"
        "FR0170",
        Category.Performance,
        "a loop over d.Keys reading d.[k] looks every key up again; KeyValue(k, v) reads the pair"
        "FR0171",
        Category.Performance,
        "Encoding.UTF8.GetBytes of an ASCII literal encodes at run time; the byte string literal is compiled data"
        "FR0173",
        Category.Performance,
        "a range built only to be mapped over allocates a second collection the size of the result; init builds the result alone"
        "FR0174",
        Category.Performance,
        "a query copied before Where/Select (or filter/map) loads every row; the query runs them and the copy follows"

        // --- idiom: same behaviour, written the way F# writes it
        "FR0001", Category.Idiom, "Boolean match => if-else"
        "FR0002",
        Category.Idiom,
        "Manual Some/None (and ValueSome/ValueNone) match => Option/ValueOption map/bind/flatten/defaultValue/defaultWit..."
        "FR0003", Category.Idiom, "Extract function composition (f >> g) from pipeline/nested-application lambdas"
        "FR0005",
        Category.Idiom,
        "Strip do-nothing CE wrapping (async { return! c }, rewrap identity, immediately-run wraps, task { return x } =>..."
        "FR0006", Category.Idiom, "Extract a when guard into an active pattern"
        "FR0007",
        Category.Idiom,
        "Remove mutable from never-mutated local bindings and type-level let mutable fields (class lets are private to ..."
        "FR0008", Category.Idiom, "Tupled => curried parameters for private functions (definition + all call sites)"
        "FR0009",
        Category.Idiom,
        "Manual Ok/Error match => Result.map/bind/mapError/isOk/isError/defaultValue/defaultWith/iter"
        "FR0010", Category.Idiom, "Simplifications: if c then true else false => c"
        "FR0012",
        Category.Idiom,
        "Term-rewriting hints (fsharplint-style lhs ===> rhs rules): comparison flips, x = true, null checks via isNull..."
        "FR0022",
        Category.Idiom,
        "Non-public union cases with unnamed tuple fields take the field names the code already spells, from the strong..."
        "FR0023",
        Category.Idiom,
        "Private two-parameter functions called as fun x -> f x k are reordered data-last, all in one fix: the definiti..."
        "FR0024", Category.Idiom, "raise (Exception msg) => failwith msg (plain System.Exception only"
        "FR0025",
        Category.Idiom,
        "Null test wrapping a value into an option => Option.ofObj / ValueOption.ofObj (if isNull x then None else Some ..."
        "FR0026",
        Category.Idiom,
        "Mutable backing field + trivial get/set member => member val X = init with get, set (field must be untouched el..."
        "FR0031",
        Category.Idiom,
        "String + chains mixing literals and string values => interpolated string ('Hello ' + name + '!' => $'Hello {name..."
        "FR0033", Category.Idiom, "An instance member touching no instance state"
        "FR0034",
        Category.Idiom,
        "if x.IsSome then x.Value + 1 else e => match x with | Some v -> v + 1 | None -> e (.Value throws when misused"
        "FR0042",
        Category.Idiom,
        "Fully applied sprintf => typed interpolated string (sprintf 'asdf %s' x => $'asdf %s{x}')"
        "FR0043",
        Category.Idiom,
        "In an interpolated string that *already* has a typed hole, the remaining plain holes gain specifiers ($'%s{nam..."
        "FR0050", Category.Idiom, "measured: List/Array.sum run LEVEL with the loop, not faster"
        "FR0107", Category.Idiom, "exists/forall short-circuit where the flag loop kept iterating"
        "FR0108", Category.Idiom, "&& true contributes nothing; the expression is the other operand"
        "FR0109", Category.Idiom, "a || a is a, when a is visibly call-free; often a copy-paste worth a look"
        "FR0112", Category.Idiom, "if/elif over one ident vs literals is a match spelled longhand"
        "FR0113", Category.Idiom, "nested ifs with the same else (or none) merge into one &&"
        "FR0114", Category.Idiom, "pyramid flip: short exit first (default off - house style)"
        "FR0115", Category.Idiom, "base case first behind a compound guard: advice on arm order"
        "FR0116", Category.Idiom, "a non-recursive member leaves its let rec group"
        "FR0117", Category.Idiom, "adjacent same-result match arms fold into an or-pattern"
        "FR0118", Category.Correctness, "a CancellationToken in scope should reach the calls that take one"
        "FR0119", Category.Correctness, "inside task/async, the awaitable twin should be used"
        "FR0120", Category.Correctness, "a catch-clause log should mention the caught exception"
        "FR0121", Category.Correctness, "UtcNow.Date/Today are timezone-random; Now->UtcNow opt-in"
        "FR0122", Category.Correctness, "literal regex patterns must compile"
        "FR0123", Category.Correctness, "Monitor.Enter/Exit is the lock function spelled dangerously"
        "FR0124", Category.Correctness, "structured-log templates that lie"
        "FR0125", Category.Correctness, "invisible and bidirectional Unicode in source"
        "FR0126", Category.Correctness, "dynamic strings into process-execution sinks"
        "FR0127", Category.Correctness, "provider-format API keys in literals"
        "FR0128", Category.Idiom, "obsolete crypto constructors become static factories"
        "FR0129", Category.Idiom, "a guard that only equality-tests the binder is the literal pattern"
        "FR0130", Category.Idiom, "module-level constants gain Literal"
        "FR0131", Category.Idiom, "provably tail-recursive functions gain TailCall"
        "FR0132", Category.Idiom, "trailing comment promoted to XML doc position"
        "FR0133", Category.Cosmetic, "five-word names become double-backtick names (tests by default)"
        "FR0134", Category.Idiom, "DateTime record fields migrate to DateTimeOffset (default off)"
        "FR0135", Category.Cosmetic, "markdown-bearing block comments in scripts become literate cells"
        "FR0136", Category.Correctness, "zero-argument Guid constructor: Guid.Empty stated, NewGuid offered"
        "FR0137", Category.Performance, "consecutive same-module map passes fuse via composition"
        "FR0138", Category.Idiom, "hand-rolled emptiness tests become String.IsNullOrEmpty/IsNullOrWhiteSpace"
        "FR0139", Category.Performance, "Seq.* on a proven array goes through IEnumerable"
        "FR0140", Category.Idiom, "constructor then property sets is named-property construction spelled out"
        "FR0141", Category.Idiom, "a state-carrying while loop is tail recursion written inside out"
        "FR0142", Category.Performance, "a test that blocks on async work returns the work as a Task instead"
        "FR0143", Category.Correctness, "a script #load chain missing a file of the project it loads from"
        "FR0144", Category.Correctness, "a script #r or #I path the package no longer has, re-pointed at what it has"
        "FR0145", Category.Correctness, "a record expression leaving fields unassigned gets them, by type"

        "FR0146", Category.Correctness, "a SQL command with no parameter at all"

        "FR0147", Category.Idiom, "a namespace spelled out at every use becomes an open"
        "FR0148", Category.Correctness, "a public Dispose() on a type that is not IDisposable"
        "FR0149", Category.Correctness, "a computation started with nobody to observe its failure"
        "FR0150", Category.Correctness, "a use-bound disposable captured by a computation that outlives the scope"

        "FR0151",
        Category.Correctness,
        "an exception handler reading only .Message from a type whose diagnosis is elsewhere"
        "FR0152",
        Category.Correctness,
        "GetOrAdd caching a Task or Lazy, so one failure is cached for every later reader"
        "FR0153", Category.Correctness, "a credential in a [<Literal>], which should be a development one"
        "FR0154",
        Category.Correctness,
        "a store after a TryGetValue miss on a ConcurrentDictionary races other callers; the miss arm becomes GetOrAdd"
        "FR0155",
        Category.Performance,
        "an internal class nothing inherits, stored in arrays or type-tested, gains [<Sealed>]"
        "FR0159",
        Category.Correctness,
        "a float/decimal conversion of an integer division truncates first: float (a / b) => float a / float b"
        "FR0160",
        Category.Correctness,
        "a handler raising a new exception drops the one it caught; the constructor's trailing inner-exception argument"
        "FR0161", Category.Correctness, "a mutating method on the struct a property returns mutates a copy"
        "FR0162", Category.Correctness, "check-then-assign on a module-level mutable races; lazy runs the factory once"
        "FR0163", Category.Correctness, "a System.Threading.Timer constructed and dropped is collected mid-flight"
        "FR0164",
        Category.Correctness,
        "a collection edited inside a for loop over itself throws; the loop walks a snapshot"
        "FR0165",
        Category.Correctness,
        "a local DateTime compared with or subtracted from a UTC one flips with the timezone"
        "FR0169",
        Category.Correctness,
        "a seq parameter or local enumerated twice on one path runs a query or a generator again"
        "FR0073",
        Category.Idiom,
        "let! x = comp whose binder exists only to be matched collapses to match! comp with (F# 4.5+)"
        "FR0074",
        Category.Idiom,
        "Nested record copy-and-update flattens to F# 8 path syntax: { r with X = { r.X with Y = v } } => { r with X.Y =..."
        "FR0078",
        Category.Idiom,
        "The three-part mutable-condition loop idiom (let! first / let mutable go / rebind at loop end) collapses to F#..."
        "FR0081", Category.Idiom, "Path fragments joined with a hard-coded / or \ separator => Path.Combine advice"
        "FR0087", Category.Idiom, "The pattern x :: [] => [ x ]"
        "FR0090",
        Category.Idiom,
        "Tupled => curried for internal/public functions with every project call site rewritten (cross-file"
        "FR0091",
        Category.Idiom,
        "Data-last parameter reorder for internal/public functions with every project call site rewritten (cross-file"
        "FR0092", Category.Idiom, "A constant failwith 'Error' gains the enclosing function's arguments"
        "FR0095",
        Category.Idiom,
        "A lambda that restates a built-in: fun x -> x => id, fun (a, b) -> a => fst, fun (a, b) -> b => snd"
        "FR0101", Category.Idiom, "index-based loop over a collection it only indexes"
        "FR0103", Category.Idiom, "isinstance-style type-test ladders as match"
        "FR0156",
        Category.Idiom,
        "a ResizeArray filled one Add at a time by loops, or a mutable list appended one element at a time, and only read after is a list expression"
        "FR0157",
        Category.Idiom,
        "a closed set of string literals matched by name becomes a union with a ToString returning the text"
        "FR0158",
        Category.Idiom,
        "a while loop walking a mutable index while a condition holds is a tail-recursive local function"
        "FR0172",
        Category.Idiom,
        "a match arm binding a whole list and reading only itms.[0] / .[1] / .Tail is a cons pattern; an earlier [] arm makes it exact"

        // --- cosmetic: punctuation and spelling of code
        "FR0013", Category.Cosmetic, "Redundant parentheses around single atomic arguments to a *function*: List.max([4"
        "FR0057", Category.Cosmetic, "XML doc drift"
        "FR0060",
        Category.Cosmetic,
        "Consecutive attribute brackets merge: [<Attr1>] [<Attr2>] (stacked or same-line) => [<Attr1"
        "FR0082", Category.Cosmetic, "[<FooAttribute>] => [<Foo>]"
        "FR0083", Category.Cosmetic, "[<Foo()>] => [<Foo>]"
        "FR0084", Category.Cosmetic, " name  backticks around a plain non-keyword identifier do nothing"
        "FR0085", Category.Cosmetic, "new on a non-IDisposable construction is noise"
        "FR0086", Category.Cosmetic, "$'no holes' => 'no holes'"
        "FR0088",
        Category.Cosmetic,
        "Case(_, _) => Case _ when every field is a wildcard (typed-gated to real union cases"
        "FR0094",
        Category.Cosmetic,
        "Redundant parentheses around a single atomic argument to an instance *method*: s.Contains('x') => s.Contains 'x..."
        "FR0096",
        Category.Cosmetic,
        "Redundant parentheses around a pattern: | (Some y) -> => | Some y ->, let f (x) = x => let f x = x"
        "FR0097",
        Category.Cosmetic,
        "Redundant parentheses around a type: (x: (int)) => (x: int), (string) list => string list"
        "FR0098",
        Category.Cosmetic,
        "The BCL name of a type F# abbreviates: System.Int32 => int, System.String => string, System.Object => obj"
        "FR0111", Category.Cosmetic, "else-holding-an-if is elif spelled tall"
        "FR0099", Category.Cosmetic, "A ; ending a line does nothing in light syntax: let x = 1; => let x = 1"
    ]
    |> List.map (fun (code, category, description) -> code, (category, description))
    |> Map.ofList

/// The category of a rule; anything unlisted reads as `idiom`.
let categoryOf (code: string) =
    categories.TryFind(code.ToUpperInvariant())
    |> Option.map fst
    |> Option.defaultValue Category.Idiom

/// A one-line description of a rule for reports; a generic line when the
/// catalog has none.
let describe (code: string) =
    let code = code.ToUpperInvariant()

    categories.TryFind code
    |> Option.map snd
    |> Option.filter (fun d -> d <> "")
    |> Option.defaultValue $"{name (categoryOf code)} rule {code}"

/// The rule table on GitHub.
[<Literal>]
let RulesUrl = "https://github.com/Thorium/fsharp-refactor/blob/main/Rules.md"

/// The GitHub anchor of a rule's section in Rules.md. Every section heads
/// `### FRnnnn — category`, and GitHub slugs a heading by lowercasing it,
/// dropping every character that is neither letter, digit, space nor
/// hyphen, and turning each space into a hyphen: the em dash vanishes and
/// the two spaces around it leave a double hyphen, `fr0103--idiom`. A link
/// to `#fr0103` alone lands on nothing, so the anchor carries the whole
/// heading.
let anchor (code: string) =
    $"{code.ToLowerInvariant()}--{name (categoryOf code)}"

/// Where Rules.md documents the rule — the link a report or an editor hover
/// can send the reader to.
let helpUri (code: string) = $"{RulesUrl}#{anchor code}"

/// Every known code in the given categories.
let codesIn (wanted: Set<Category>) =
    categories
    |> Map.toSeq
    |> Seq.filter (fun (_, (category, _)) -> wanted.Contains category)
    |> Seq.map fst
    |> Set.ofSeq

/// Every code the catalog knows, for tests that check nothing was forgotten.
let known = categories |> Map.toSeq |> Seq.map fst |> Set.ofSeq

/// Every rule as (code, category) — the machine-readable catalog.
let allRules =
    categories
    |> Map.toList
    |> List.map (fun (code, (category, _)) -> code, category)

/// The rules that never offer a fix — their finding is the whole product.
/// Rules.md marks them with an em dash in its "Offered fix" column, and a
/// test keeps the two in step.
let advisory =
    set
        [
            "FR0146"
            "FR0017"
            "FR0019"
            "FR0020"
            "FR0027"
            "FR0028"
            "FR0033"
            "FR0036"
            "FR0037"
            "FR0041"
            "FR0048"
            "FR0051"
            "FR0054"
            "FR0058"
            "FR0061"
            "FR0063"
            "FR0064"
            "FR0065"
            "FR0066"
            "FR0068"
            "FR0081"
            "FR0102"
            "FR0104"
            "FR0115"
            "FR0122"
            "FR0124"
            "FR0126"
            "FR0127"
            "FR0141"
            "FR0153"
            "FR0161"
            "FR0162"
            "FR0163"
            "FR0165"
            "FR0169"
        ]

/// The rules worth looking at first — a likely defect too costly to hold
/// back: an N+1 query loop, SQL built from strings, a raise inside finally,
/// a regex that cannot compile. Orthogonal to the category: their notes
/// print without --notes, editors show them as warnings, SARIF carries
/// them at warning level. Rules.md marks them in its "Priority" column.
let priority =
    set
        [
            "FR0032"
            "FR0047"
            "FR0065"
            "FR0020"
            "FR0028"
            "FR0046"
            "FR0048"
            "FR0061"
            "FR0063"
            "FR0066"
            "FR0122"
            "FR0126"
            "FR0127"
        ]

let isPriority (code: string) =
    priority.Contains(code.ToUpperInvariant())

/// One tunable a rule reads from its own config entry, beside `enabled`.
type Knob =
    {
        Name: string
        /// This build's default, as the JSON the generated config writes.
        Default: string
        /// One line, for the comment above the entry.
        Summary: string
    }

let private flag name value summary =
    {
        Name = name
        Default = (if value then "true" else "false")
        Summary = summary
    }

let private number name (value: int) summary =
    {
        Name = name
        Default = string value
        Summary = summary
    }

/// The tunables, by rule. `--create-config` writes each rule that has one
/// as an object (`{ "enabled": true, "perCall": true }`) rather than a
/// bare bool, so the knob is discoverable from the generated file instead
/// of only from the README — a config listing every rule but none of
/// their parameters reads as though there are none.
///
/// A default here is the SAME value the rule passes to
/// `Configuration.parameterBool`/`parameterInt`; ConfigKnobTests holds the
/// two together, so a rule whose default moves fails a test rather than
/// writing a config that lies.
let knobs: (string * Knob list) list =
    [
        "FR0015",
        [
            flag "perCall" true "hoist a Regex out of a plain function body too, not only out of a loop"
        ]
        "FR0029",
        [
            number "tailLines" 40 "non-awaiting lines after the last await that earn a tail extraction"
            flag "hoistReturnOnAsync" false "extend the return hoist (not the FS3511 advice) to async { }"
        ]
        "FR0049",
        [
            flag "syncSwap" false "let a sweep swap an awaited call for its synchronous sibling"
        ]
        "FR0060",
        [
            number "maxAttributes" 4 "how many attributes may share one [<A; B>] bracket"
            number "wrapColumn" 110 "how wide the merged attribute line may get"
        ]
        "FR0065",
        [
            flag "dropLegacyProtocols" false "let a sweep comment a dead TLS protocol out of the flags"
        ]
        "FR0067",
        [
            flag "invariant" false "let a sweep apply CultureInfo.InvariantCulture to an uncultured parse"
        ]
        "FR0114",
        [
            number "thenAtLeast" 20 "how long the then-branch must be before flipping is suggested"
            number "elseAtMost" 3 "how short the else-branch must stay"
        ]
        "FR0121", [ flag "utcNow" false "let a sweep rewrite DateTime.Now to UtcNow" ]
        "FR0133",
        [
            flag "locals" false "rename local and file-private names too, not only test-attributed ones"
        ]
        "FR0147",
        [
            number "uses" 6 "how many spellings of a namespace earn an open"
            number "deepUses" 4 "the same, for a namespace three segments deep"
        ]
        "FR0156",
        [
            flag "arrays" false "write an array expression too, at the measured cost of a slower collector"
            flag "explicitYield" false "spell the collected element `yield x` rather than bare `x`"
        ]
        "FR0159",
        [
            flag "all" false "note the literal-operand and product-dividend divisions on a sweep too"
        ]
        "FR0174",
        [
            flag
                "pipelines"
                false
                "take the `q |> Seq.toList |> List.filter f` pipeline too, not only the LINQ method chain"
        ]
    ]

/// The tunables of one rule, empty when it has none.
let knobsOf (code: string) =
    knobs
    |> List.tryFind (fun (c, _) -> String.Equals(c, code, StringComparison.OrdinalIgnoreCase))
    |> Option.map snd
    |> Option.defaultValue []
