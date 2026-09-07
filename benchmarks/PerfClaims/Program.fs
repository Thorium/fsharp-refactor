/// Before/after gate for every performance and idiom rule.
///
///     dotnet run -c Release --project benchmarks/PerfClaims            # all
///     dotnet run -c Release --project benchmarks/PerfClaims -- FR0050  # one
///
/// Each case runs the code a rule REWRITES (before) and the code it
/// EMITS (after), measured on both axes — wall clock and allocation,
/// because GC pressure is performance too. The gates:
///
///   performance — the rewrite may not be worse on EITHER axis (small
///                 jitter tolerances only). It exists to make code
///                 faster; a regression on any axis fails.
///   idiom       — a tiny cost is tolerated (factor 3, generous against
///                 measurement noise), an order of magnitude is not.
///                 FR0050 once emitted `Seq.sum` for a list, ~50% slower
///                 than the loop it replaced; that escape is why this
///                 file exists.
///
/// Rules with no measurable runtime pair (advice about IO, scheduler
/// behavior, pure syntax, or API shape) are listed as N/A with a reason,
/// so the accounting covers the full category lists and a new rule
/// missing from BOTH lists is visible.
///
/// Stopwatch loops, not BenchmarkDotNet — its generated host executables
/// tend to be blocked by application control on locked-down machines.
/// Both sides of a pair pay the same delegate-invocation overhead, so
/// the RATIOS the gates test are fair even where absolute ns are not.
/// Exit code = number of failed gates.
module FSharp.Refactor.Benchmarks.PerfClaims

open System
open System.Diagnostics
open System.Text.RegularExpressions

type Category =
    | Perf
    | Idiom

type Case =
    { Code: string
      Name: string
      Cat: Category
      Iters: int
      Before: unit -> int
      After: unit -> int }

let private measure iters (f: unit -> int) =
    // real warmup: two calls do not get past JIT tiering, and tier-0
    // noise flaked gates at the single-digit-ns scale
    let mutable warm = 0L

    for _ in 1 .. min 1000 iters do
        warm <- warm + int64 (f ())

    let mutable sink = warm
    let mutable best = infinity
    let mutable bytesPerOp = 0.0

    for _ in 1..5 do
        let allocBefore = GC.GetAllocatedBytesForCurrentThread()
        let sw = Stopwatch.StartNew()

        for _ in 1..iters do
            sink <- sink + int64 (f ())

        sw.Stop()
        let allocAfter = GC.GetAllocatedBytesForCurrentThread()
        bytesPerOp <- float (allocAfter - allocBefore) / float iters
        best <- min best (float sw.Elapsed.TotalMilliseconds * 1e6 / float iters)

    best, bytesPerOp, sink

/// Performance rules whose CLAIM is the allocation axis: their time sits
/// at single-digit nanoseconds where run-to-run JIT jitter exceeds any
/// honest tolerance, while their B/op is deterministic. These keep the
/// strict allocation gate and take the idiom-grade time gate instead —
/// judged on what they promise, held loosely on what they don't.
///
/// FR0004 was briefly here, when its gate still measured a `map` moving
/// into Seq — 35% slower for 12% less allocation. The right answer turned
/// out to be that the rule should not offer that move at all, so it does
/// not, and the gate follows the rule to `filter`, where the strict Perf
/// tolerance is met honestly.
let private allocIsTheClaim = set [ "FR0011"; "FR0106" ]

/// The symmetric set: advice that TRADES a stated one-time allocation
/// for time (FR0035's build-a-HashSet note). Allocation cannot gate a
/// trade whose before-side allocates nothing; instead the time win must
/// be DECISIVE — at least 2x — or naming the trade isn't worth it.
let private timeIsTheClaim = set [ "FR0035" ]

/// The gates. Time tolerances are generous because stopwatch loops
/// jitter; the allocation axis is nearly deterministic, so its
/// tolerances are tight.
let private gate cat (relaxedTime: bool) (timeTrade: bool) (bNs: float, bB: float) (aNs: float, aB: float) =
    if timeTrade then
        // an explicit time-for-allocation trade: the advice names its
        // price, so only the promised axis gates — and it must win BIG
        if aNs <= bNs * 0.5 then
            Ok()
        else
            Error $"the traded time win is not decisive: {bNs:F0} -> {aNs:F0} ns/op"
    else

        match cat with
        | Perf ->
            let timeOk =
                if relaxedTime then
                    aNs <= bNs * 3.0 + 10.0
                else
                    aNs <= bNs * 1.25 + 2.0

            let allocOk = aB <= bB * 1.15 + 16.0

            if timeOk && allocOk then
                Ok()
            elif not allocOk then
                Error $"allocation regressed: {bB:F0} -> {aB:F0} B/op"
            else
                Error $"time regressed: {bNs:F0} -> {aNs:F0} ns/op"
        | Idiom ->
            let timeOk = aNs <= bNs * 3.0 + 10.0
            let allocOk = aB <= bB * 3.0 + 64.0

            if timeOk && allocOk then
                Ok()
            elif not allocOk then
                Error $"allocation order-of-magnitude worse: {bB:F0} -> {aB:F0} B/op"
            else
                Error $"time order-of-magnitude worse: {bNs:F0} -> {aNs:F0} ns/op"

// ---- fixture types --------------------------------------------------------

type RefShape =
    | RefCircle of float
    | RefUnit

[<Struct>]
type StructShape =
    | StructCircle of r: float
    | StructUnit

type RefPoint = { RX: int; RY: int }

[<Struct>]
type StructPoint = { SX: int; SY: int }

[<return: Struct>]
let (|EvenStruct|_|) (n: int) =
    if n % 2 = 0 then ValueSome n else ValueNone

let (|EvenRef|_|) (n: int) = if n % 2 = 0 then Some n else None

let tryHalfRef (n: int) = if n % 2 = 0 then Some(n / 2) else None

let tryHalfStruct (n: int) =
    if n % 2 = 0 then ValueSome(n / 2) else ValueNone

type Calc() =
    member _.AddInst(a: int, b: int) = a + b
    static member AddStat(a: int, b: int) = a + b

let rec descendRefSeq (d: int) : int seq =
    seq {
        yield d

        if d > 0 then
            yield! descendRefSeq (d - 1)
    }

// ---- fixtures --------------------------------------------------------------

let xsList = List.init 1000 id

// FR0090's pair: a saturated curried call compiles to the same direct
// static invocation as the tupled call — no intermediate partial
// applications exist unless a partial ESCAPES (and even a
// constant-capturing escapee is cached as a static singleton)
let private tupled8 (a: int, b: int, c: int, d: int, e: int, f: int, g: int, h: int) = a + b + c + d + e + f + g + h

let private curried8 (a: int) (b: int) (c: int) (d: int) (e: int) (f: int) (g: int) (h: int) =
    a + b + c + d + e + f + g + h

let xsArr = Array.init 1000 id
let bigArr = Array.init 100_000 (fun i -> i % 100)
let sq = Seq.init 1000 id
let pairArr = Array.init 1000 (fun i -> i, string i)
let idSet = Set.ofList xsList
let queue = System.Collections.Concurrent.ConcurrentQueue<int>(Seq.init 1000 id)
let opt = Some 42
let vopt = ValueSome 42
let sName = "wintermute"
let sCity = "chiba"
let sHello = "hello world, hello again"
// padded but NOT blank: the Trim() = "" test does its full work and the
// trimmed copy still allocates
let sPadded = "  hello  "
let sMixed = "Hello World"
let sMixed2 = "hELLO wORLD"
let mutable maybeNull: string = "present"
let bytes64 = Array.init 64 byte
let cachedRegex = Regex @"\d+-\d+"
let shapeObj: obj = box (RefCircle 2.0)

let guardDict =
    System.Collections.Generic.Dictionary<int, int>(
        Seq.init 100 id
        |> Seq.map (fun i -> System.Collections.Generic.KeyValuePair(i, i))
    )

let calc = Calc()
let oneItem = [ 42 ]
let pieces200 = List.init 200 (fun i -> string (i % 10))
let orderId = "ORDER-12345-CONFIRMED"

// keys 100..199, evens present, odds absent — the FR0018 workload
let halfDict =
    System.Collections.Generic.Dictionary<int, int>(
        seq {
            for k in 100..199 do
                if k % 2 = 0 then
                    System.Collections.Generic.KeyValuePair(k, k)
        }
    )

let compAsync = async { return 1 }

// ---- the cases -------------------------------------------------------------

let cases =
    [
      // ================= performance rules =================
      // the map form is no longer emitted — measuring it was what showed
      // the move into Seq is only worth it for an operation that SHRINKS
      // its input, so the gate follows the rule to `filter`
      { Code = "FR0004"
        Name = "Seq.toList|>List.filter -> Seq.filter|>Seq.toList"
        Cat = Perf
        Iters = 10_000
        Before = fun () -> (sq |> Seq.toList |> List.filter (fun x -> x % 2 = 0)).Length
        After = fun () -> (sq |> Seq.filter (fun x -> x % 2 = 0) |> Seq.toList).Length }

      { Code = "FR0137"
        Name = "Array.map fst|>Array.map f -> Array.map (fst >> f)"
        Cat = Perf
        Iters = 10_000
        Before = fun () -> (pairArr |> Array.map fst |> Array.map (fun x -> x + 1)).Length
        After = fun () -> (pairArr |> Array.map (fst >> fun x -> x + 1)).Length }

      { Code = "FR0011"
        Name = "active pattern -> [<return: Struct>]"
        Cat = Perf
        Iters = 100_000
        Before =
          fun () ->
              let mutable n = 0

              for i in 0..999 do
                  match i with
                  | EvenRef _ -> n <- n + 1
                  | _ -> ()

              n
        After =
          fun () ->
              let mutable n = 0

              for i in 0..999 do
                  match i with
                  | EvenStruct _ -> n <- n + 1
                  | _ -> ()

              n }

      { Code = "FR0015"
        Name = "Regex.IsMatch(s, pat) -> cached instance"
        Cat = Perf
        Iters = 500_000
        Before = fun () -> if Regex.IsMatch(sHello, @"\d+-\d+") then 1 else 0
        After = fun () -> if cachedRegex.IsMatch sHello then 1 else 0 }

      { Code = "FR0016"
        Name = "small DU -> [<Struct>] DU"
        Cat = Perf
        Iters = 200_000
        Before =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let s = if i % 2 = 0 then RefCircle(float i) else RefUnit

                  acc <-
                      acc
                      + (match s with
                         | RefCircle r -> int r
                         | RefUnit -> 0)

              acc
        After =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let s = if i % 2 = 0 then StructCircle(float i) else StructUnit

                  acc <-
                      acc
                      + (match s with
                         | StructCircle r -> int r
                         | StructUnit -> 0)

              acc }

      { Code = "FR0021"
        Name = "$\"{x}\" of one value -> string x"
        Cat = Perf
        Iters = 2_000_000
        Before = fun () -> ($"{42}").Length
        After = fun () -> (string 42).Length }

      { Code = "FR0139"
        Name = "Seq.length on an array -> Array.length"
        Cat = Perf
        Iters = 200_000
        Before = fun () -> Seq.length xsArr
        After = fun () -> Array.length xsArr }

      { Code = "FR0139"
        Name = "Seq.head on an array -> Array.head"
        Cat = Perf
        Iters = 200_000
        Before = fun () -> Seq.head xsArr
        After = fun () -> Array.head xsArr }

      { Code = "FR0139"
        Name = "Seq.tryFind on an array -> Array.tryFind"
        Cat = Perf
        Iters = 50_000
        Before =
          fun () ->
              match Seq.tryFind (fun x -> x = 999) xsArr with
              | Some v -> v
              | None -> 0
        After =
          fun () ->
              match Array.tryFind (fun x -> x = 999) xsArr with
              | Some v -> v
              | None -> 0 }

      // contains has TWO better answers: the CLI applies the idiomatic
      // one, an editor also offers the vectorised one. Both are gated, so
      // neither claim can drift
      { Code = "FR0139"
        Name = "Seq.contains on int[] -> Array.contains (editor alternative)"
        Cat = Perf
        Iters = 50_000
        Before = fun () -> if Seq.contains 999 xsArr then 1 else 0
        After = fun () -> if Array.contains 999 xsArr then 1 else 0 }

      { Code = "FR0139"
        Name = "Seq.contains on int[] -> vectorised LINQ (CLI default)"
        Cat = Perf
        Iters = 50_000
        Before = fun () -> if Seq.contains 999 xsArr then 1 else 0
        After = fun () -> if System.Linq.Enumerable.Contains(xsArr, 999) then 1 else 0 }

      { Code = "FR0139"
        Name = "Seq.exists on an array -> Array.exists"
        Cat = Perf
        Iters = 50_000
        Before = fun () -> if Seq.exists (fun x -> x = 999) xsArr then 1 else 0
        After = fun () -> if Array.exists (fun x -> x = 999) xsArr then 1 else 0 }

      { Code = "FR0030"
        Name = "Add loop over a RANGE -> AddRange [| a .. b |]"
        Cat = Perf
        Iters = 20_000
        Before =
          fun () ->
              let r = ResizeArray<int>()

              for x in 1..1000 do
                  r.Add x

              r.Count
        After =
          fun () ->
              let r = ResizeArray<int>()
              r.AddRange [| 1..1000 |]
              r.Count }

      { Code = "FR0030"
        Name = "Add loop -> AddRange"
        Cat = Perf
        Iters = 20_000
        Before =
          fun () ->
              let r = ResizeArray<int>()

              for x in xsArr do
                  r.Add x

              r.Count
        After =
          fun () ->
              let r = ResizeArray<int>()
              r.AddRange xsArr
              r.Count }

      { Code = "FR0035"
        Name = "List.contains probes -> binding converted to Set in place"
        Cat = Perf
        Iters = 1_000
        Before =
          fun () ->
              let mutable n = 0

              for i in 0..999 do
                  if List.contains i xsList then
                      n <- n + 1

              n
        After =
          // build charged, same honesty rule as the HashSet companion:
          // Set.Contains is O(log n) not O(1), but even a five-element
          // set beats the list scan measured 2.5x — and the in-place
          // form keeps the module value immutable
          fun () ->
              let probes = Set.ofList xsList
              let mutable n = 0

              for i in 0..999 do
                  if probes.Contains i then
                      n <- n + 1

              n }

      { Code = "FR0035"
        Name = "List.contains probes -> HashSet built once, probed per iteration"
        Cat = Perf
        Iters = 1_000
        Before =
          fun () ->
              let mutable n = 0

              for i in 0..999 do
                  if List.contains i xsList then
                      n <- n + 1

              n
        After =
          // the build is CHARGED to the rewrite — the advice is only
          // honest if the one-time construction plus O(1) probes beats
          // the repeated linear scans, build cost included
          fun () ->
              let probes = System.Collections.Generic.HashSet<int>(xsList)
              let mutable n = 0

              for i in 0..999 do
                  if probes.Contains i then
                      n <- n + 1

              n }

      { Code = "FR0037"
        Name = "Regex ctor in loop -> hoisted"
        Cat = Perf
        Iters = 5_000
        Before =
          fun () ->
              let mutable n = 0

              for _ in 0..9 do
                  let re = Regex @"\d+-\d+"

                  if re.IsMatch sHello then
                      n <- n + 1

              n
        After =
          fun () ->
              let re = Regex @"\d+-\d+"
              let mutable n = 0

              for _ in 0..9 do
                  if re.IsMatch sHello then
                      n <- n + 1

              n }

      { Code = "FR0038"
        Name = "Contains \"o\" -> Contains 'o'"
        Cat = Perf
        Iters = 2_000_000
        Before = fun () -> if sHello.Contains "o" then 1 else 0
        After = fun () -> if sHello.Contains 'o' then 1 else 0 }

      { Code = "FR0039"
        Name = "ToLower() = ToLower() -> Equals OrdinalIgnoreCase"
        Cat = Perf
        Iters = 500_000
        Before =
          fun () ->
              if sMixed.ToLowerInvariant() = sMixed2.ToLowerInvariant() then
                  1
              else
                  0
        After =
          fun () ->
              if String.Equals(sMixed, sMixed2, StringComparison.OrdinalIgnoreCase) then
                  1
              else
                  0 }

      { Code = "FR0040"
        Name = "ContainsKey guard before Remove -> bare Remove"
        Cat = Perf
        Iters = 100_000
        Before =
          fun () ->
              let mutable n = 0

              for k in 0..99 do
                  if guardDict.ContainsKey k then
                      guardDict.Remove k |> ignore

                  guardDict.[k] <- k // restore, identically on both sides
                  n <- n + 1

              n
        After =
          fun () ->
              let mutable n = 0

              for k in 0..99 do
                  guardDict.Remove k |> ignore
                  guardDict.[k] <- k // restore, identically on both sides
                  n <- n + 1

              n }

      { Code = "FR0041"
        Name = "Array.sum int[100k] -> Enumerable.Sum (SIMD)"
        Cat = Perf
        Iters = 2_000
        Before = fun () -> Array.sum bigArr
        After = fun () -> System.Linq.Enumerable.Sum bigArr }

      { Code = "FR0051"
        Name = "acc <- acc @ [x] loop -> cons + List.rev"
        Cat = Perf
        Iters = 2_000
        Before =
          fun () ->
              let mutable acc: int list = []

              for i in 0..199 do
                  acc <- acc @ [ i ]

              acc.Length
        After =
          fun () ->
              let mutable acc: int list = []

              for i in 0..199 do
                  acc <- i :: acc

              (List.rev acc).Length }

      { Code = "FR0051"
        Name = "string acc <- acc + s loop -> StringBuilder"
        Cat = Perf
        Iters = 5_000
        Before =
          fun () ->
              let mutable acc = ""

              for p in pieces200 do
                  acc <- acc + p

              acc.Length
        After =
          fun () ->
              let sb = System.Text.StringBuilder()

              for p in pieces200 do
                  sb.Append p |> ignore

              sb.ToString().Length }

      { Code = "FR0052"
        Name = "ConcurrentQueue Count = 0 -> IsEmpty"
        Cat = Perf
        Iters = 1_000_000
        Before = fun () -> if queue.Count = 0 then 1 else 0
        After = fun () -> if queue.IsEmpty then 1 else 0 }

      { Code = "FR0053"
        Name = "BitConverter+Replace -> Convert.ToHexString"
        Cat = Perf
        Iters = 200_000
        Before = fun () -> BitConverter.ToString(bytes64).Replace("-", "").Length
        After = fun () -> (Convert.ToHexString bytes64).Length }

      { Code = "FR0058"
        Name = "recursive seq yield! -> flat generation"
        Cat = Perf
        Iters = 5_000
        Before = fun () -> descendRefSeq 100 |> Seq.sum
        After = fun () -> seq { for d in 100..-1..0 -> d } |> Seq.sum }

      { Code = "FR0059"
        Name = "Option-returning try-function -> ValueOption"
        Cat = Perf
        Iters = 100_000
        Before =
          fun () ->
              let mutable n = 0

              for i in 0..99 do
                  match tryHalfRef i with
                  | Some h -> n <- n + h
                  | None -> ()

              n
        After =
          fun () ->
              let mutable n = 0

              for i in 0..99 do
                  match tryHalfStruct i with
                  | ValueSome h -> n <- n + h
                  | ValueNone -> ()

              n }

      { Code = "FR0069"
        Name = "Option in a pipeline -> ValueOption"
        Cat = Perf
        Iters = 500_000
        Before = fun () -> opt |> Option.map (fun v -> v * 2) |> Option.defaultValue 0
        After = fun () -> vopt |> ValueOption.map (fun v -> v * 2) |> ValueOption.defaultValue 0 }

      { Code = "FR0070"
        Name = "small record -> [<Struct>] record"
        Cat = Perf
        Iters = 200_000
        Before =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let p = { RX = i; RY = i + 1 }
                  acc <- acc + p.RX + p.RY

              acc
        After =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let p = { SX = i; SY = i + 1 }
                  acc <- acc + p.SX + p.SY

              acc }

      { Code = "FR0071"
        Name = "loop-invariant call inside loop -> hoisted"
        Cat = Perf
        Iters = 100_000
        Before =
          fun () ->
              let mutable n = 0

              for _ in 0..9 do
                  n <- n + (sHello.ToUpperInvariant()).Length

              n
        After =
          fun () ->
              let upper = sHello.ToUpperInvariant()
              let mutable n = 0

              for _ in 0..9 do
                  n <- n + upper.Length

              n }

      { Code = "FR0076"
        Name = "List.map f |> ignore -> List.iter"
        Cat = Perf
        Iters = 50_000
        Before =
          fun () ->
              xsList |> List.map (fun x -> x + 1) |> ignore
              xsList.Length
        After =
          fun () ->
              xsList |> List.iter (fun x -> (x + 1) |> ignore)
              xsList.Length }

      { Code = "FR0093"
        Name = "reference tuple result -> struct tuple"
        Cat = Perf
        Iters = 200_000
        Before =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let (a, b) = (i, i + 1)
                  acc <- acc + a + b

              acc
        After =
          fun () ->
              let mutable acc = 0

              for i in 0..99 do
                  let struct (a, b) = struct (i, i + 1)
                  acc <- acc + a + b

              acc }

      { Code = "FR0102"
        Name = "list.[i] per index -> direct iteration"
        Cat = Perf
        Iters = 1_000
        Before =
          fun () ->
              let mutable t = 0

              for i in 0..999 do
                  t <- t + xsList.[i]

              t
        After =
          fun () ->
              let mutable t = 0

              for x in xsList do
                  t <- t + x

              t }

      { Code = "FR0106"
        Name = "Parse of a Substring copy -> Parse of AsSpan"
        Cat = Perf
        Iters = 2_000_000
        Before = fun () -> System.Int32.Parse(orderId.Substring(6, 5))
        After = fun () -> System.Int32.Parse(orderId.AsSpan(6, 5)) }

      { Code = "FR0104"
        Name = "recursive acc @ [x] -> cons + rev at the end"
        Cat = Perf
        Iters = 2_000
        Before =
          fun () ->
              let rec go acc i =
                  if i = 200 then acc else go (acc @ [ i ]) (i + 1)

              (go [] 0: int list).Length
        After =
          fun () ->
              let rec go acc i =
                  if i = 200 then List.rev acc else go (i :: acc) (i + 1)

              (go [] 0: int list).Length }

      // ================= idiom rules (parity gates) =================
      { Code = "FR0001"
        Name = "match bool -> if"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              match sHello.Length > 10 with
              | true -> 1
              | false -> 0
        After = fun () -> if sHello.Length > 10 then 1 else 0 }

      { Code = "FR0138"
        Name = "isNull x || x = \"\" -> String.IsNullOrEmpty"
        Cat = Idiom
        Iters = 5_000_000
        Before = fun () -> if isNull sHello || sHello = "" then 1 else 0
        After = fun () -> if System.String.IsNullOrEmpty sHello then 1 else 0 }

      { Code = "FR0138"
        Name = "x.Trim() = \"\" -> String.IsNullOrWhiteSpace"
        Cat = Perf
        Iters = 1_000_000
        Before = fun () -> if sPadded.Trim() = "" then 1 else 0
        After = fun () -> if System.String.IsNullOrWhiteSpace sPadded then 1 else 0 }

      { Code = "FR0002"
        Name = "match option -> Option.map |> defaultValue"
        Cat = Idiom
        Iters = 2_000_000
        Before =
          fun () ->
              match opt with
              | Some v -> v + 1
              | None -> 0
        After = fun () -> opt |> Option.map (fun v -> v + 1) |> Option.defaultValue 0 }

      { Code = "FR0003"
        Name = "fun x -> g (f x) -> f >> g in map"
        Cat = Idiom
        Iters = 20_000
        Before = fun () -> (xsList |> List.map (fun x -> string (abs x))).Length
        After = fun () -> (xsList |> List.map (abs >> string)).Length }

      { Code = "FR0007"
        Name = "mutable max loop -> List.fold"
        Cat = Idiom
        Iters = 50_000
        Before =
          fun () ->
              let mutable best = 0

              for x in xsList do
                  best <- max best (x % 7)

              best
        After = fun () -> xsList |> List.fold (fun best x -> max best (x % 7)) 0 }

      { Code = "FR0009"
        Name = "match result -> Result.map"
        Cat = Idiom
        Iters = 2_000_000
        Before =
          fun () ->
              let r: Result<int, string> = Ok 41

              match r with
              | Ok v -> v + 1
              | Error _ -> 0
        After =
          fun () ->
              let r: Result<int, string> = Ok 41

              r
              |> Result.map (fun v -> v + 1)
              |> function
                  | Ok v -> v
                  | Error _ -> 0 }

      { Code = "FR0010"
        Name = "if b then true else false -> b"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              if (if sHello.Length > 10 then true else false) then
                  1
              else
                  0
        After = fun () -> if sHello.Length > 10 then 1 else 0 }

      { Code = "FR0012"
        Name = "not (a = b) -> a <> b"
        Cat = Idiom
        Iters = 5_000_000
        Before = fun () -> if not (sHello.Length = 11) then 1 else 0
        After = fun () -> if sHello.Length <> 11 then 1 else 0 }

      { Code = "FR0012"
        Name = "List.head (List.sort xs) -> List.min xs"
        Cat = Idiom
        Iters = 20_000
        Before = fun () -> List.head (List.sort xsList)
        After = fun () -> List.min xsList }

      { Code = "FR0025"
        Name = "if isNull then None else Some -> Option.ofObj"
        Cat = Idiom
        Iters = 2_000_000
        Before =
          fun () ->
              match (if isNull maybeNull then None else Some maybeNull) with
              | Some s -> s.Length
              | None -> 0
        After =
          fun () ->
              match Option.ofObj maybeNull with
              | Some s -> s.Length
              | None -> 0 }

      // STRING holes only, mirroring the rule's own typed guard. That
      // guard is measured, not stylistic: an interpolation hole holding a
      // non-string (`$"id-{42}"`) boxes through String.Format — ~4x the
      // time and ~6x the allocation of concatenating `string 42` — while
      // string holes run level with concat. Widening the rule past
      // strings would fail this gate.
      // And at most TWO of them: a 3-hole interpolation falls off the
      // compiler's String.Concat optimization onto String.Format — 4.9x
      // slower, 2.3x the allocation — so the rule caps the hole count.
      { Code = "FR0031"
        Name = "string + chain -> interpolation"
        Cat = Idiom
        Iters = 500_000
        Before = fun () -> ("id-" + sName + "-of-" + sCity).Length
        After = fun () -> ($"id-{sName}-of-{sCity}").Length }

      { Code = "FR0034"
        Name = "IsSome/.Value -> match"
        Cat = Idiom
        Iters = 2_000_000
        Before = fun () -> if opt.IsSome then opt.Value + 1 else 0
        After =
          fun () ->
              match opt with
              | Some v -> v + 1
              | None -> 0 }

      { Code = "FR0042"
        Name = "sprintf -> interpolated string"
        Cat = Idiom
        Iters = 200_000
        Before = fun () -> (sprintf "v=%d, w=%d" 42 99).Length
        After = fun () -> ($"v=%d{42}, w=%d{99}").Length }

      { Code = "FR0050"
        Name = "mutable sum loop -> List.sum"
        Cat = Idiom
        Iters = 50_000
        Before =
          fun () ->
              let mutable t = 0

              for x in xsList do
                  t <- t + x

              t
        After = fun () -> List.sum xsList }

      { Code = "FR0108"
        Name = "x && true -> x"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              let x = xsArr

              if x.[0] < x.[1] && true then 1 else 0
        After =
          fun () ->
              let x = xsArr

              if x.[0] < x.[1] then 1 else 0 }

      { Code = "FR0109"
        Name = "a || a -> a"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              let x = xsArr

              if x.[0] > x.[1] || x.[0] > x.[1] then 1 else 0
        After =
          fun () ->
              let x = xsArr

              if x.[0] > x.[1] then 1 else 0 }

      { Code = "FR0112"
        Name = "if/elif equality chain -> match"
        Cat = Idiom
        Iters = 1_000_000
        // sum over varied inputs so neither side constant-folds and every
        // arm is exercised — the first fixture compared a folded chain
        // against a live match and passed on gate slack alone
        Before =
          fun () ->
              let mutable acc = 0

              for i in 0..7 do
                  let x = xsArr.[i]

                  acc <-
                      acc
                      + (if x = 1 then 10
                         elif x = 2 then 20
                         elif x = 3 then 30
                         else 0)

              acc
        After =
          fun () ->
              let mutable acc = 0

              for i in 0..7 do
                  let x = xsArr.[i]

                  acc <-
                      acc
                      + (match x with
                         | 1 -> 10
                         | 2 -> 20
                         | 3 -> 30
                         | _ -> 0)

              acc }

      { Code = "FR0113"
        Name = "nested ifs, same else -> one &&"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              let x = xsArr

              if x.[0] < x.[1] then
                  if x.[1] < x.[2] then 1 else 3
              else
                  3
        After =
          fun () ->
              let x = xsArr

              if x.[0] < x.[1] && x.[1] < x.[2] then 1 else 3 }

      { Code = "FR0090"
        Name = "tupled f(a,..,h) -> curried f a .. h (saturated)"
        Cat = Idiom
        Iters = 2_000_000
        // arguments read from the array so neither side constant-folds
        Before =
          fun () ->
              let x = xsArr

              tupled8 (x.[0], x.[1], x.[2], x.[3], x.[4], x.[5], x.[6], x.[7])
        After =
          fun () ->
              let x = xsArr

              curried8 x.[0] x.[1] x.[2] x.[3] x.[4] x.[5] x.[6] x.[7] }

      // the predicate never hits, so exists gets NO short-circuit help:
      // this is the rewrite's worst case, a full scan against a full scan.
      // Any real match only widens the gap in exists's favor
      { Code = "FR0107"
        Name = "mutable flag loop -> List.exists (no-hit worst case)"
        Cat = Idiom
        Iters = 50_000
        Before =
          fun () ->
              let mutable found = false

              for x in xsList do
                  if x > 1_000_000 then
                      found <- true

              if found then 1 else 0
        After = fun () -> if List.exists (fun x -> x > 1_000_000) xsList then 1 else 0 }

      { Code = "FR0095"
        Name = "map (fun x -> x) -> map id"
        Cat = Idiom
        Iters = 20_000
        Before = fun () -> (xsList |> List.map (fun x -> x)).Length
        After = fun () -> (xsList |> List.map id).Length }

      { Code = "FR0101"
        Name = "for i in 0..len-1 xs.[i] -> for x in xs"
        Cat = Idiom
        Iters = 100_000
        Before =
          fun () ->
              let mutable t = 0

              for i in 0 .. xsArr.Length - 1 do
                  t <- t + xsArr.[i]

              t
        After =
          fun () ->
              let mutable t = 0

              for x in xsArr do
                  t <- t + x

              t }

      { Code = "FR0103"
        Name = "if :? plus casts -> match with type tests"
        Cat = Idiom
        Iters = 2_000_000
        Before =
          fun () ->
              if (shapeObj :? StructShape) then
                  1
              elif (shapeObj :? RefShape) then
                  int (
                      match shapeObj :?> RefShape with
                      | RefCircle r -> r
                      | RefUnit -> 0.0
                  )
              else
                  0
        After =
          fun () ->
              match shapeObj with
              | :? StructShape -> 1
              | :? RefShape as s ->
                  int (
                      match s with
                      | RefCircle r -> r
                      | RefUnit -> 0.0
                  )
              | _ -> 0 }

      { Code = "FR0005"
        Name = "async { return! comp } -> comp (construction)"
        Cat = Idiom
        Iters = 1_000_000
        Before =
          fun () ->
              let wrapped = async { return! compAsync }
              if obj.ReferenceEquals(wrapped, null) then 0 else 1
        After =
          fun () ->
              let bare = compAsync
              if obj.ReferenceEquals(bare, null) then 0 else 1 }

      { Code = "FR0033"
        Name = "stateless instance member -> static member"
        Cat = Idiom
        Iters = 200_000
        Before =
          fun () ->
              let mutable n = 0

              for i in 0..99 do
                  n <- n + calc.AddInst(i, 1)

              n
        After =
          fun () ->
              let mutable n = 0

              for i in 0..99 do
                  n <- n + Calc.AddStat(i, 1)

              n }

      { Code = "FR0087"
        Name = "pattern x :: [] -> [ x ]"
        Cat = Idiom
        Iters = 5_000_000
        Before =
          fun () ->
              match oneItem with
              | x :: [] -> x
              | _ -> 0
        After =
          fun () ->
              match oneItem with
              | [ x ] -> x
              | _ -> 0 }

      { Code = "FR0014"
        Name = "ContainsKey + indexer -> TryGetValue"
        Cat = Perf
        Iters = 100_000
        Before =
          fun () ->
              let mutable n = 0

              for k in 0..99 do
                  if guardDict.ContainsKey k then
                      n <- n + guardDict.[k]

              n
        After =
          fun () ->
              let mutable n = 0

              for k in 0..99 do
                  match guardDict.TryGetValue k with
                  | true, v -> n <- n + v
                  | _ -> ()

              n }

      // ---- a correctness rule whose rewrite also claims a lookup saved ----
      // half the keys are absent: check-then-add only exists in code where
      // insertion sometimes happens — an all-present fixture measures the
      // one workload nobody writes the pattern for (and TryAdd loses it by
      // ~40%, for the record). Both sides restore identically.
      { Code = "FR0018"
        Name = "check-then-add -> TryAdd (half absent)"
        Cat = Perf
        Iters = 50_000
        Before =
          fun () ->
              let mutable n = 0

              for k in 100..199 do
                  if not (halfDict.ContainsKey k) then
                      halfDict.[k] <- k

                  n <- n + 1

              for k in 100..199 do
                  if k % 2 = 1 then
                      halfDict.Remove k |> ignore

              n
        After =
          fun () ->
              let mutable n = 0

              for k in 100..199 do
                  halfDict.TryAdd(k, k) |> ignore
                  n <- n + 1

              for k in 100..199 do
                  if k % 2 = 1 then
                      halfDict.Remove k |> ignore

              n } ]


/// Rules with no measurable in-process runtime pair, and why. Every
/// performance/idiom rule must appear either here or in `cases`.
let notApplicable =
    [ // performance
      "FR0028", "N+1 query batching: the cost is in the database round trips"
      "FR0029", "state-machine size at codegen; fixes verified by typecheck, not stopwatch"
      "FR0079", "awaiting one awaitable: scheduler-bound"
      // idiom
      "FR0006", "extracting an active pattern: same code, new name"
      "FR0008", "tupled-to-curried signature: call shape, not runtime"
      "FR0022", "naming DU fields: syntax only"
      "FR0023", "parameter order: signature, not runtime"
      "FR0024", "raise-vs-failwith: the exceptional path is not a hot path"
      "FR0026", "auto-property rewrite: same compiled accessor"
      "FR0043", "typed holes: placeholder advice"
      "FR0073", "match! sugar: identical desugaring"
      "FR0074", "nested record update: identical construction"
      "FR0078", "while! sugar: identical desugaring"
      "FR0081", "path separators: correctness of behavior, not speed"
      "FR0091", "cross-file signature change: data-last is idiom, not speed"
      "FR0092", "failwith message content: diagnostic quality"
      "FR0114", "branch reorder: identical branches, swapped positions"
      "FR0115", "advice on match arm order: no fix to measure"
      "FR0116", "rec-group membership: same compiled calls either way"
      "FR0142", "test returns Task: the claim is thread occupancy while the work is in flight, not throughput"
      "FR0117", "or-pattern fold: identical decision tree after compilation"
      "FR0118", "cancellation plumbing: correctness of propagation, not speed"
      "FR0119", "sync-to-async twin: thread-pool behavior, scheduler-bound in-process"
      "FR0120", "log completeness: diagnostic quality, not speed"
      "FR0121", "wall-clock semantics: correctness, not speed"
      "FR0122", "pattern validity: correctness, not speed"
      "FR0123", "lock shape: release-on-all-paths correctness, not speed"
      "FR0124", "template arity: diagnostic quality, not speed"
      "FR0125", "invisible characters: review integrity, not speed"
      "FR0126", "injection sink: security, not speed"
      "FR0127", "credential formats: security, not speed"
      "FR0128", "same algorithm behind a factory: spelling, not speed"
      "FR0129", "guard removal: identical decision, one fewer test"
      "FR0130", "Literal const-folds at use sites; no in-process pair isolates it"
      "FR0131", "TailCall is metadata only — it changes no codegen to measure"
      "FR0132", "moving a comment to the doc position changes no executed code"
      "FR0133", "a rename is spelling only — nothing to measure"
      "FR0134", "DateTimeOffset carries the offset the DateTime dropped; no perf claim"
      "FR0135", "one star in a comment; nothing executes differently"
      "FR0136", "Guid.Empty is the same value the constructor made; no perf claim"

      "FR0147", "an open changes name resolution at compile time and nothing at runtime; no perf claim"
      "FR0140",
      "named-property construction is the same calls in the same order; it reads better, it does not run faster"
      "FR0141", "a note; nothing is rewritten, so there is nothing to measure" ]

[<EntryPoint>]
let main argv =
    let wanted = argv |> Array.map (fun a -> a.ToUpperInvariant()) |> Set.ofArray

    let selected =
        if wanted.IsEmpty then
            cases
        else
            cases |> List.filter (fun c -> wanted.Contains(c.Code.ToUpperInvariant()))

    let mutable failures = 0
    let mutable sink = 0L

    printfn "%-8s %-50s %11s %11s %10s %10s  %s" "rule" "rewrite" "before ns" "after ns" "before B" "after B" "verdict"

    for case in selected do
        let bNs, bB, s1 = measure case.Iters case.Before
        let aNs, aB, s2 = measure case.Iters case.After
        sink <- sink + s1 + s2

        match
            gate case.Cat (allocIsTheClaim.Contains case.Code) (timeIsTheClaim.Contains case.Code) (bNs, bB) (aNs, aB)
        with
        | Ok() -> printfn "%-8s %-50s %11.1f %11.1f %10.1f %10.1f  PASS" case.Code case.Name bNs aNs bB aB
        | Error why ->
            failures <- failures + 1
            printfn "%-8s %-50s %11.1f %11.1f %10.1f %10.1f  FAIL: %s" case.Code case.Name bNs aNs bB aB why

    if wanted.IsEmpty then
        printfn ""
        printfn "not applicable (no in-process runtime pair):"

        for code, reason in notApplicable do
            printfn "  %-8s %s" code reason

        // self-enforcing accounting: every performance and idiom rule in
        // the catalog must be measured or excused. FR0040 sat in neither
        // list for one revision while the doc claimed omissions would be
        // "visible" — visible requires checked.
        let covered =
            Set.union (cases |> List.map (fun c -> c.Code) |> Set.ofList) (notApplicable |> List.map fst |> Set.ofList)

        let expected =
            FSharp.Refactor.RuleCatalog.codesIn (
                set
                    [ FSharp.Refactor.RuleCatalog.Category.Performance
                      FSharp.Refactor.RuleCatalog.Category.Idiom ]
            )

        for code in Set.difference expected covered do
            failures <- failures + 1
            printfn "  %-8s FAIL: in the catalog but neither measured nor excused" code

    printfn ""

    if failures = 0 then
        printfn "all %d gates passed (sink %d)" selected.Length (sink % 7L)
    else
        printfn "%d of %d gates FAILED (sink %d)" failures selected.Length (sink % 7L)

    failures
