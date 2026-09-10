# Rules

Every rule fsharp-refactor knows. The table is the quick reference — one
line each: an example of the source it fires on and the fix it offers for
it — and [Rule details](#rule-details) below it explains each one in prose.
The README covers the safety model behind them. The tool's own tests keep
this file complete: every code in the rule catalog has a row and a section,
and its category and default state match the code.

| ID | Category | Enabled * | API ** | Priority *** | Fires on | Offered fix |
| -- | -- | -- | -- | -- | -- | -- |
| FR0001 | Idiom | v | | | `match x with true -> a \| false -> b` | `if x then a else b` |
| FR0002 | Idiom | | | | `match x with Some v -> f v \| None -> None` | `x \|> Option.bind (fun v -> f v)` |
| FR0003 | Idiom | v | | | `xs \|> List.map (fun x -> g (f x))` | `xs \|> List.map (f >> g)` |
| FR0004 | Performance | v | | | `xs \|> Seq.toList \|> List.filter f` | `xs \|> Seq.filter f \|> Seq.toList` |
| FR0005 | Idiom | v | | | `async { return! comp }` | `comp` |
| FR0006 | Idiom | v | | | `match n with n when isEven n -> f n \| _ -> g n` | `let private (\|IsEven\|_\|) input = if isEven input then Some input else None` then `match n with IsEven n -> f n \| _ -> g n` |
| FR0007 | Idiom | v | | | `let mutable x = 0 in printfn "%d" x` | `let x = 0 in printfn "%d" x` |
| FR0008 | Idiom | v | | | `let add (a, b) = a + b in add (1, 2)` | `let add a b = a + b in add 1 2` |
| FR0009 | Idiom | v | | | `match r with Ok v -> Ok (f v) \| Error e -> Error e` | `r \|> Result.map (fun v -> f v)` |
| FR0010 | Idiom | v | | | `if c then true else false` | `c` |
| FR0011 | Performance | v | v | | `let private (\|Even\|_\|) n = if n % 2 = 0 then Some n else None` | `[<return: Struct>] let private (\|Even\|_\|) n = if n % 2 = 0 then ValueSome n else ValueNone` |
| FR0012 | Idiom | v | | | `not (a = b)` | `a <> b` |
| FR0013 | Cosmetic | v | | | `List.max([4; 3])` | `List.max [4; 3]` |
| FR0014 | Performance | v | | | `if d.ContainsKey k then f d.[k] else e` | `match d.TryGetValue k with true, value -> f value \| _ -> e` |
| FR0015 | Performance | v | | | `Regex.IsMatch(s, "^abc")` | `s.StartsWith "abc"` |
| FR0016 | Performance | v | v | | `type private Shape = \| Circle of radius: float \| Square of side: float` | `[<Struct>] type private Shape = \| Circle of radius: float \| Square of side: float` |
| FR0017 | Correctness | v | | | `comp \|> ignore` | — |
| FR0018 | Correctness | v | | | `if not (d.ContainsKey k) then d.[k] <- v` | `d.TryAdd(k, v) \|> ignore` |
| FR0019 | Correctness | | | | `override _.Equals(o) = ...` | — |
| FR0020 | Correctness | v | | v | `type B() as this =<br>    do this.Init()<br>    abstract Init: unit -> unit` | — |
| FR0021 | Performance | v | | | `$"{x.ToString()} items"` | `$"{x} items"` |
| FR0022 | Idiom | v | v | | `type private Order = \| Line of int * decimal` then `\| Line(qty, price) -> total qty price` | `type private Order = \| Line of qty: int * price: decimal` |
| FR0023 | Idiom | v | | | `let scale x k = x * k in xs \|> List.map (fun x -> scale x 2)` | `let scale k x = x * k in xs \|> List.map (scale 2)` |
| FR0024 | Idiom | v | | | `raise (Exception "boom")` | `failwith "boom"` |
| FR0025 | Idiom | v | | | `if isNull x then None else Some x` | `Option.ofObj x` |
| FR0026 | Idiom | v | | | `let mutable name = ""<br>member this.Name with get () = name and set v = name <- v` | `member val Name = "" with get, set` |
| FR0027 | Correctness | v | | | `src.Changed.Add(fun n -> this.Bump n)` | — |
| FR0028 | Performance | v | | v | `for c in customers do for o in db.Orders do use c o` | — |
| FR0029 | Performance | v | | | `task { let cfg = load () in let! x = fetch cfg in use x }` | `let cfg = load () in task { let! x = fetch cfg in use x }` |
| FR0030 | Performance | v | | | `for x in xs do acc.Add x` | `acc.AddRange xs` |
| FR0031 | Idiom | v | | | `"Hello " + name + "!"` | `$"Hello {name}!"` |
| FR0032 | Correctness | v | | v | `type T() =<br>    let stream = new FileStream(...)` | `interface System.IDisposable with member _.Dispose() = stream.Dispose()` (editor) |
| FR0033 | Idiom | v | | | `member this.Add a b = a + b` | — |
| FR0034 | Idiom | v | | | `if x.IsSome then x.Value + 1 else 0` | `match x with Some v -> v + 1 \| None -> 0` |
| FR0035 | Performance | v | | | `let private ys = [1; 2; 3]<br>xs \|> List.filter (fun x -> List.contains x ys)` | `let private ys = [1; 2; 3] \|> Set.ofList<br>xs \|> List.filter (fun x -> ys.Contains x)` |
| FR0036 | Correctness | v | | | `x.GetType().Name = "Customer"` | — |
| FR0037 | Performance | v | | | `for url in urls do let client = new HttpClient() in fetch client url` | — |
| FR0038 | Performance | v | | | `s.Contains "x"` | `s.Contains 'x'` |
| FR0039 | Performance | v | | | `x.ToLower() = "abc"` | `String.Equals(x, "abc", StringComparison.OrdinalIgnoreCase)` |
| FR0040 | Performance | v | | | `if d.ContainsKey k then d.Remove k \|> ignore` | `d.Remove k \|> ignore` |
| FR0041 | Performance | v | | | `values \|> Array.sum` | — |
| FR0042 | Idiom | v | | | `sprintf "asdf %s: %d" name count` | `$"asdf %s{name}: %d{count}"` |
| FR0043 | Idiom | v | | | `$"%s{name} is {age}"` | `$"%s{name} is %d{age}"` |
| FR0044 | Correctness | v | | | `try f () with ex -> log ex; raise ex` | `try f () with ex -> log ex; reraise ()` |
| FR0045 | Correctness | v | | | `x = nan` | `System.Double.IsNaN x` |
| FR0046 | Correctness | v | | v | `lock "cache" (fun () -> ...)` | `let private bumpLock = obj ()` then `lock bumpLock (fun () -> ...)` (editor) |
| FR0047 | Correctness | v | | v | `let s = new FileStream(...)<br>interface IDisposable with<br>    member _.Dispose() = ()` | `member _.Dispose() = s.Dispose()` (editor) |
| FR0048 | Correctness | v | | v | `String.Format("{0} of {1}", x)` | — |
| FR0049 | Correctness | v | | | `task { let x = t.Result in use x }`, `task { t.Wait() }`, `task { Task.WaitAll(a, b) }`, `task { let! x = Task.Run(fun () -> c \|> Async.RunSynchronously) }` | `task { let! x = t in use x }`, `do! t`, `do! Task.WhenAll(a, b)`, `task { let! x = c \|> Async.StartAsTask }` |
| FR0050 | Idiom | v | | | `let mutable total = 0 in for x in xs do total <- total + x` | `let total = xs \|> List.sum` |
| FR0051 | Performance | v | | | `for x in xs do acc <- acc @ [x]` | — |
| FR0052 | Performance | v | | | `q.Count = 0` | `q.IsEmpty` |
| FR0053 | Performance | v | | | `BitConverter.ToString(bytes).Replace("-", "")` | `Convert.ToHexString bytes` |
| FR0054 | Correctness | v | | | `override _.GetHashCode() = failwith "no hash"` | — |
| FR0055 | Correctness | v | | | `try work () with _ -> ()` | `if x = 0 then 0 else a / x`, `match Int32.TryParse s with ...`, an IO-only catch, or a log line in the file's idiom (editor) |
| FR0057 | Cosmetic | v | | | `/// <param name="value">The value.</param><br>let scale value factor = ...` | `/// <param name="factor"></param>` (editor scaffold) |
| FR0058 | Performance | v | | | `let rec walk n = seq { for c in n.Children do yield! walk c }` | — |
| FR0059 | Performance | v | | | `let private tryParse s = if ok s then Some (conv s) else None` | `let private tryParse s = if ok s then ValueSome (conv s) else ValueNone` |
| FR0060 | Cosmetic | v | | | `[<Attr1>] [<Attr2>]` | `[<Attr1; Attr2>]` |
| FR0061 | Correctness | v | | v | `let scale value factor = invalidArg "facotr" "zero factor"` | — |
| FR0062 | Correctness | v | | | `let mutable counter = 0<br>let bump () = counter <- counter + 1` | `let mutable private counter = 0` (editor) |
| FR0063 | Correctness | v | | v | `try work () finally failwith "cleanup"` | — |
| FR0064 | Correctness | v | | | `raise (NullReferenceException())` | — |
| FR0065 | Correctness | v | | v | `use md5 = MD5.Create()` | — |
| FR0066 | Correctness | v | | v | `cmd.CommandText <- $"SELECT * FROM t WHERE id={id}"` | — |
| FR0067 | Correctness | v | | | `DateTime.Parse s` | `DateTime.Parse(s, CultureInfo.InvariantCulture)` |
| FR0068 | Correctness | v | | | `type Color = Red = 1 \| Crimson = 1` | — |
| FR0069 | Performance | v | v | | `type private Row = { Seen: DateTime option }` | `type private Row = { Seen: DateTime voption }` |
| FR0070 | Performance | v | v | | `type private P = { X: int; Y: int }` | `[<Struct>] type private P = { X: int; Y: int }` |
| FR0071 | Performance | v | | | `for x = 0 to 100 do let c = a + 3 in sink (x + c)` | `let c = a + 3 in for x = 0 to 100 do sink (x + c)` |
| FR0072 | Correctness | v | | | `\| A -> .. \| B -> .. \| C -> .. \| _ -> d` | `\| A -> .. \| B -> .. \| C -> .. \| D -> d` |
| FR0073 | Idiom | v | | | `let! x = fetch () in match x with Some v -> f v \| None -> g ()` | `match! fetch () with Some v -> f v \| None -> g ()` |
| FR0074 | Idiom | v | | | `{ r with X = { r.X with Y = v } }` | `{ r with X.Y = v }` |
| FR0075 | Correctness | v | | | `let s = new FileStream(path, mode)` | `use s = new FileStream(path, mode)` |
| FR0076 | Performance | v | | | `xs \|> List.map f \|> ignore` | `xs \|> List.iter (f >> ignore)` |
| FR0077 | Correctness | v | | | `{ new IDbConnection with member _.Open() = open () }` | `{ new IDbConnection with member _.Open() = open ()<br>  member _.Close() = raise (NotImplementedException()) }` |
| FR0078 | Idiom | v | | | `let! first = check ()<br>let mutable go = first<br>while go do ...; let! next = check () in go <- next` | `while! check () do ...` |
| FR0079 | Performance | v | | | `Task.WhenAll [\| t \|]` | `t` (editor) |
| FR0080 | Correctness | v | | | `<TAB>let x = 1` | `    let x = 1` |
| FR0081 | Idiom | v | | | `dir + "\\" + file` | — |
| FR0082 | Cosmetic | v | | | `[<SerializableAttribute>]` | `[<Serializable>]` |
| FR0083 | Cosmetic | v | | | `[<Foo()>]` | `[<Foo>]` |
| FR0084 | Cosmetic | v | | | ```let ``name`` = 1``` | `let name = 1` |
| FR0085 | Cosmetic | v | | | `let sb = new StringBuilder()` | `let sb = StringBuilder()` |
| FR0086 | Cosmetic | v | | | `$"no holes"` | `"no holes"` |
| FR0087 | Idiom | v | | | `\| x :: [] -> ...` | `\| [ x ] -> ...` |
| FR0088 | Cosmetic | v | | | `\| Case(_, _) -> ...` | `\| Case _ -> ...` |
| FR0089 | Correctness | v | | | `[ 1, 2 ]` | `[ 1; 2 ]` (editor) |
| FR0090 | Idiom | v | v | | `let add (a, b) = a + b in add (1, 2)` | `let add a b = a + b in add 1 2` |
| FR0091 | Idiom | v | v | | `let pad (s: string) (n: int) = s.PadLeft n in xs \|> List.map (fun s -> pad s 2)` | `let pad (n: int) (s: string) = s.PadLeft n in xs \|> List.map (pad 2)` |
| FR0092 | Idiom | v | v | | `let f x = failwith "Error"` | `let f x = failwith $"Error, calling f with x: {x}"` |
| FR0093 | Performance | v | v | | `type private P = { A: int * int }` | `type private P = { A: struct (int * int) }` |
| FR0094 | Cosmetic | v | | | `s.Contains("x")` | `s.Contains "x"` |
| FR0095 | Idiom | v | | | `fun x -> x` | `id` |
| FR0096 | Cosmetic | v | | | `\| (Some y) -> ...` | `\| Some y -> ...` |
| FR0097 | Cosmetic | v | | | `let f (x: (int)) = x` | `let f (x: int) = x` |
| FR0098 | Cosmetic | v | | | `let f (x: System.Int32) = x` | `let f (x: int) = x` |
| FR0099 | Cosmetic | | | | `let x = 1;` | `let x = 1` |
| FR0100 | Correctness | v | | | `\| Jordan -> (* not supported yet *) None` | `\| Jordan -> (* not supported yet *) raise (NotImplementedException())` |
| FR0101 | Idiom | v | | | `for i in 0 .. xs.Length - 1 do handle xs.[i]` | `for item in xs do handle item` |
| FR0102 | Performance | v | | | `for i in 0 .. n - 1 do printfn "%s" names.[i] (* names: string list *)` | — |
| FR0103 | Idiom | v | | | `if (shape :? Circle) then area (shape :?> Circle) elif (shape :? Rect) then width (shape :?> Rect) else failwith "unknown"` | `match shape with :? Circle as v -> area v \| :? Rect as v -> width v \| _ -> failwith "unknown"` |
| FR0104 | Performance | v | | | `\| x :: rest -> collect (acc @ [x]) rest` | — |
| FR0105 | Correctness | v | | | `let due = balance + 2_000_000_000` | `int64 balance + 2_000_000_000L` (editor; `Checked.(+) balance 2_000_000_000` second) |
| FR0106 | Performance | v | | | `Int32.Parse(s.Substring(6, 5))` | `Int32.Parse(s.AsSpan(6, 5))` |
| FR0107 | Idiom | v | | | `let mutable found = false in for x in xs do if p x then found <- true` | `let found = xs \|> List.exists (fun x -> p x)` |
| FR0108 | Idiom | v | | | `x && true` | `x` |
| FR0109 | Idiom | v | | | `a \|\| a` | `a` |
| FR0110 | Correctness | v | | | `match color with Red -> "r" \| Green -> "g"` | `match color with Red -> "r" \| Green -> "g" \| Blue -> raise (System.NotImplementedException())` |
| FR0111 | Cosmetic | v | | | `if a then x else if b then y else z` | `if a then x elif b then y else z` |
| FR0112 | Idiom | v | | | `if x = 1 then a elif x = 2 then b else c` | `match x with 1 -> a \| 2 -> b \| _ -> c` |
| FR0113 | Idiom | v | | | `if a then (if b then X else E) else E` | `if a && b then X else E` |
| FR0114 | Idiom | | | | `if ok then (twenty lines) else fail ()` | `if not ok then fail () else (twenty lines)` |
| FR0115 | Idiom | v | | | `match v with x when a && b -> base \| _ -> err` | — |
| FR0116 | Idiom | v | | | `let rec f1 x = f3 x + x and f2 y = y + 1 and f3 z = f1 z - z` | `let f2 y = y + 1` then `let rec f1 x = f3 x + x and f3 z = f1 z - z` |
| FR0117 | Idiom | v | | | `\| 1 -> true \| 2 -> true \| _ -> false` | `\| 1 \| 2 -> true \| _ -> false` |
| FR0118 | Correctness | v | | | `let! s = client.GetStringAsync(url) // ct in scope` | `let! s = client.GetStringAsync(url, ct)` |
| FR0119 | Correctness | v | | | `task { let line = reader.ReadLine() ... }` | `task { let! line = reader.ReadLineAsync() ... }` |
| FR0120 | Correctness | v | | | `with ex -> logger.LogError("sync failed {Id}", id)` | `with ex -> logger.LogError(ex, "sync failed {Id}", id)` |
| FR0121 | Correctness | v | | | `DateTime.UtcNow.Date` (note) / `DateTime.Now` | `DateTime.UtcNow` (opt-in: `{ "FR0121": { "utcNow": 1 } }`) |
| FR0122 | Correctness | v | | v | `Regex("(unclosed")` | — |
| FR0123 | Correctness | v | | | `Monitor.Enter gate; try body () finally Monitor.Exit gate` | `lock gate (fun () -> body ())` |
| FR0124 | Correctness | v | | | `logger.LogInformation("user {User} did {Action}", user)` | — |
| FR0125 | Correctness | v | | | `"foo<U+200B>bar"` (invisible char in a string literal) | `"foo\u200Bbar"` |
| FR0126 | Correctness | v | | v | `Process.Start("cmd", $"/c {input}")` | — |
| FR0127 | Correctness | v | | v | `let key = "sk-ant-api03-..."` | — |
| FR0128 | Idiom | v | | | `new SHA256Managed()` | `SHA256.Create()` |
| FR0129 | Idiom | v | | | `\| x when x = "A" -> 1` | `\| "A" -> 1` |
| FR0130 | Idiom | v | v | | `let ConnectionName = "orders"` | `[<Literal>] let ConnectionName = "orders"` |
| FR0131 | Idiom | v | | | `let rec sum acc = function [] -> acc \| x :: xs -> sum (acc + x) xs` | `[<TailCall>] let rec sum acc = function [] -> acc \| x :: xs -> sum (acc + x) xs` |
| FR0132 | Idiom | v | | | `let interestRate r n = r * n // monthly, non-compounding` | `/// monthly, non-compounding<br>let interestRate r n = r * n` |
| FR0133 | Cosmetic | v | | | `let thisIsMyVeryComplexMethod x =` | ``` let ``this is my very complex method`` x = ``` |
| FR0134 | Idiom | | | | `type private Row = { Seen: DateTime }<br>{ Seen = DateTime.UtcNow }` | `type private Row = { Seen: DateTimeOffset }<br>{ Seen = DateTimeOffset.UtcNow }` |
| FR0135 | Cosmetic | v | | | `(* ### Setup *)` (in .fsx) | `(** ### Setup *)` |
| FR0136 | Correctness | v | | | `let id = Guid()` | `let id = Guid.Empty` |
| FR0137 | Performance | v | | | `xs \|> Array.map fst \|> Array.map f` | `xs \|> Array.map (fst >> f)` |
| FR0138 | Idiom | v | | | `isNull x \|\| x = ""` | `String.IsNullOrEmpty x` |
| FR0139 | Performance | v | | | `arr \|> Seq.length` | `arr \|> Array.length` |
| FR0140 | Idiom | v | | | `let h = Henkilo() in h.Id <- 1L; h.Etunimi <- "x"` | `let h = Henkilo(Id = 1L, Etunimi = "x")` |
| FR0141 | Idiom | | | | `let mutable stopped = false in while not stopped && n < limit do (if next = stop then stopped <- true)` | — |
| FR0142 | Performance | v | | | ``` [<Fact>] let ``reads`` () = let res = load () \|> Async.RunSynchronously in check res ```, `Task.WaitAll(a, b)`, `Assert.Throws<E>(fun () -> t.Wait())` | ``` [<Fact>] let ``reads`` () = task { let! res = load () \|> Async.StartImmediateAsTask in check res } :> Task ```, `do! Task.WhenAll(a, b)`, `let! ex = Assert.ThrowsAsync<E>(fun () -> t :> Task)` |
| FR0143 | Correctness | v | | | `#load "../src/Lib/Braiding.fs"` (Braiding.fs needs `FMatrix`, defined in the project's FMatrix.fs) | `#load "../src/Lib/FMatrix.fs"` inserted before it |
| FR0144 | Correctness | v | | | `#r @"../packages/Sql.1.2.3/lib/net451/Sql.dll"` (net451 gone, net461 present) | `#r @"../packages/Sql.1.2.3/lib/net461/Sql.dll"` |
| FR0145 | Correctness | v | | | `{ Name = "x"; Retries = 3 }` (Tags and Timeout unassigned) | `{ Name = "x"; Retries = 3; Tags = []; Timeout = None }` |
| FR0146 | Correctness | v | | | `cmd.CommandText <- "SELECT * FROM users"` | — |
| FR0147 | Idiom | v | | | `System.Threading.Tasks.Task.Delay 10` (four times in the file, or six for a two-segment namespace) | `open System.Threading.Tasks` then `Task.Delay 10` |
| FR0148 | Correctness | v | | | `type Session() =<br>    member _.Dispose() = inner.Dispose()` | note: implement `IDisposable` (nothing can `use` it otherwise) |
| FR0149 | Correctness | v | | | `try<br>    async { f () } \|> Async.Start<br>with e -> g e` | `async {<br>    try<br>        f ()<br>    with e -> g e<br>}<br>\|> Async.Start` (editor); otherwise a note — unhandled on a pool thread kills the process |
| FR0150 | Correctness | v | | | `use cts = new CancellationTokenSource()<br>task { ... cts.Token ... }` | `task {<br>    use cts = ...<br>    ... }` (editor) |
| FR0151 | Correctness | v | | | `with :? ReflectionTypeLoadException as e -> log e.Message`, `with :? WebException as wex -> log wex.Message` | in place of a `reraise()` under a `GetTypes()` try: `let loaded = ... e.Types filtered of nulls ... in if Array.isEmpty loaded then reraise () else loaded`, plus a `// TODO: log e.LoaderExceptions` where it ends the line (editor, offered FIRST); then the `e.LoaderExceptions \|> ... \|> String.concat "; "` join. Reading EITHER member, in the body or the `when` guard, already counts as handled; WebException note-only |
| FR0152 | Correctness | v | | | `cache.GetOrAdd(args, addCache)` where the value type is `Task`/`ValueTask`/`Lazy` | note only - a faulted value stays cached and every later reader gets it; remove the entry when it faults |
| FR0153 | Correctness | v | | | `[<Literal>] let cs = "Server=...;Password=..."` on a non-loopback server | — |

\*) Enabled by default. A blank cell means the rule is off until
`fsharprefactor.json` turns it on (`"FR0099": true`) or a run asks for it
with `--codes`.

\*\*) The fix changes a public API — a signature, a type's shape, a field
name, an exception's text that callers may read — and is applied only with
`--api-changes`; without it the rule reports and, where a declaration is
private or internal, fixes that. An assembly nothing links against is the
exception: an executable or a script has no external consumer, so the
in-place shape changes among these apply to its public declarations
anyway — in editors too. A library says the same with `"publicApi": false`
in `fsharprefactor.json`, and an executable takes it back with `true`. See
the README's `--api-changes` section.

\*\*\*) Priority: a likely defect too costly to hold back — an N+1 query
loop, SQL built from strings, a raise inside finally, a regex that cannot
compile. Orthogonal to the category: these notes print without `--notes`,
editors show them as warnings, and SARIF carries them at warning level.

A `—` under Offered fix means the rule only reports: it points at the
shape and leaves the rewrite to you, either because there is no single
safe rewrite or because the right one is a design decision.
### FR0001 — idiom

Boolean `match` → `if-else`

### FR0002 — idiom

Manual `Some/None` (and `ValueSome/ValueNone`) match → `Option`/`ValueOption` `map`/`bind`/`flatten`/`defaultValue`/`defaultWith`/`isSome`/`isNone` (spelled `x.IsSome`/`x.IsNone` where the receiver's type is settled, as FR0010 does)/`iter`/`exists`/`forall` + map-then-default combos. OFF BY DEFAULT: the measured board's one rewrite that slows the rewritten code (+53%, one closure per call) — enable via `"FR0002": true` or `--codes FR0002` when the readability trade suits

### FR0003 — idiom

Extract function composition (`f >> g`) from pipeline/nested-application lambdas

### FR0004 — performance

Move `List`/`Seq`/`Array` conversion past the next pipeline operation (or drop it before consuming ops). Moving INTO Seq is offered only for operations that SHRINK their input: measured, `Seq.toList |> List.map f` → `Seq.map f |> Seq.toList` runs 35% slower for 12% less allocation, because `Seq.toList` rebuilds the result through an enumerator where `List.map` walked cons cells, and a length-preserving operation has no smaller output to pay for that. `filter` does (−4% time, −13% allocation), and moving into Array wins outright (map −39% time, −44% allocation). Moving into List is never offered

### FR0005 — idiom

Strip do-nothing CE wrapping (`async { return! c }`, rewrap identity, immediately-run wraps, `task { return x }` → `Task.FromResult`)

### FR0006 — idiom

Extract a `when` guard into an active pattern

### FR0007 — idiom

Remove `mutable` from never-mutated local bindings and type-level `let mutable` fields (class lets are private to the type, so the whole mutation scope is visible)

### FR0008 — idiom

Tupled → curried parameters for `private` functions (definition + all call sites)

### FR0009 — idiom

Manual `Ok/Error` match → `Result.map`/`bind`/`mapError`/`isOk`/`isError`/`defaultValue`/`defaultWith`/`iter`

### FR0010 — idiom

Simplifications: `if c then true else false` → `c`; `x = None` → `x.IsNone` (`<> None` → `IsSome`; `Option.isSome x` and `x |> Option.isNone` → the property too; the module form stays on an unannotated parameter, whose type is not settled where it is read; withheld when the branch reads `x.Value` or `Option.get x`, where FR0034 binds the payload instead); `List.length xs = 0` → `List.isEmpty xs` (List/Seq/Array/Set/Map)

### FR0011 — performance

Trivial partial active patterns → `[<return: Struct>]` `ValueSome`/`ValueNone` (perf: no allocation per match attempt)

### FR0012 — idiom

Term-rewriting hints (fsharplint-style `lhs ===> rhs` rules): comparison flips, `x = true`, null checks via `isNull`, map fusion, `isEmpty (filter ...)` → `exists`, `sum (map ...)` → `sumBy`, `map id`, `id >>`, `compare ... = 0`, and more — extensible per repository

### FR0013 — cosmetic

Redundant parentheses around single atomic arguments to a *function*: `List.max([4; 3])` → `List.max [4; 3]`, `Some("x")` → `Some "x"`

### FR0014 — performance

`ContainsKey` + indexer double lookup → single `TryGetValue` (two lookups become one — measured 1.26x — and on `ConcurrentDictionary` also a race fix); F# `Map` gets the `TryFind` option idiom

### FR0015 — performance

Literal regex patterns → `StartsWith`/`EndsWith`/`Contains`; static `Regex` calls inside loops are hoisted to a `let private xRegex = Regex "..."` module binding (advice-only when the `open` is missing or the name is taken; a call under `#if` hoists under the same `#if`)

### FR0016 — performance

Small value-type-only unions → `[<Struct>]` (perf: no heap allocation per value) Edits the companion .fsi in step

### FR0017 — correctness

`Async` discarded with `ignore` (never runs) — fix-less hint pointing at `Async.Ignore`/`Async.Start`; also a `ValueTask`/`ValueTask<T>` discarded with `ignore` (outcome lost, single consumption; plain `Task` is excluded)

### FR0018 — correctness

Check-then-add → single `TryAdd` (race fix on `ConcurrentDictionary`, double-lookup fix on `Dictionary`)

### FR0019 — correctness

`Equals` override without `GetHashCode` (hash-based collections misbehave); off by default — the compiler's FS0346 already warns on every shape this rule can see

### FR0020 — correctness

Abstract member used during construction (override runs before derived init)

### FR0021 — performance

Redundant `.ToString()` inside interpolated strings

### FR0022 — idiom

Non-public union cases with unnamed tuple fields take the field names the code already spells, from the strongest source that yields them: their match sites (`| Line(qty, price) ->`), a clear trailing comment (`// qty and price`, `// qty * price`, `// qty, price` — type-note comments like `// string * int` are recognized and excluded), or the case's own `XAndY` name (`InterestAndRate of float * float` → `interest: float * rate: float`). Definition-only edit, positional sites stay valid

### FR0023 — idiom

Private two-parameter functions called as `fun x -> f x k` are reordered data-last, all in one fix: the definition swaps to `let private f k x`, direct calls swap their arguments, and the lambda — which under the new order would read `fun x -> f k x` — eta-reduces to the partial application `f k` (`List.map (fun x -> scale x 2)` ends up as `List.map (scale 2)`)

### FR0024 — idiom

`raise (Exception msg)` → `failwith msg` (plain `System.Exception` only — the raised type and message are unchanged)

### FR0025 — idiom

Null test wrapping a value into an option → `Option.ofObj` / `ValueOption.ofObj` (`if isNull x then None else Some x`, the negated and `= null` forms, and the two-clause `match x with null -> ...`; `Some`/`None` typed-gated to FSharp.Core)

### FR0026 — idiom

Mutable backing field + trivial get/set member → `member val X = init with get, set` (field must be untouched elsewhere in the type; pure-atom initializer)

### FR0027 — correctness

GC-lifetime note (no fix): a lambda that captures `this` — directly or through an instance `let` field — handed to an event/observable sink (`.Add`, `.Subscribe`, `.AddHandler`, `Observable.add`, ...) keeps the whole object alive until the handler is removed; sinks are typed-gated so collection `.Add`s never fire; a handler on an `Event<_>` created in the same scope cannot outlive `this` and stays quiet, and the note tells a process-wide publisher (`AppDomain.CurrentDomain.*`, `Console.*` — the real leak) from one handed in

### FR0028 — performance

N+1 note (no fix): a `for` over an `IQueryable` nested inside another loop executes one database query per outer iteration; typed-gated so in-memory sequences never fire, and an outer loop batched with `chunkBySize` suppresses the note

### FR0029 — performance

Task state-machine advice (FS3511 itself is emitted at codegen, invisible to analyzers): a `let rec` in a resumable `task { }` body is flagged always (definite dynamic-fallback producer); oversized tasks (≥8 awaits or ≥60 lines) get the shrinking moves, three of them as automatic fixes — plain leading `let`s hoist above the builder (caveat in the message: a throw there then surfaces at the call instead of faulting the Task), a body that IS an if/else with at least one awaiting arm splits into per-branch tasks (arms cut as line regions between the `then`/`else`/`}` anchors, so their comments travel; a synchronous arm becomes a trivially static task), a long non-awaiting tail wraps into a local function inside the CE (a nested function's body is not resumable code, and closures capture the CE locals — no parameters, no annotations), and, outside the size gate because it costs nothing to take, a closing branch whose every leaf `return`s hoists that one keyword in front of the whole branch — the branch stays where it is and gains an indent level, so the builder is handed a value once instead of once per arm (declined when the branch itself awaits, when it spans a `#if`, and when a directive block opens on the line below it, where another configuration may hold arms this one cannot see). Two knobs: `tailLines` (default 10) is how many non-awaiting lines earn the tail extraction, and `hoistReturnOnAsync` (default false) extends ONLY the return hoist to `async { }` — worth ~27% less generated IL on a twelve-arm branch but identical on time and allocation, and async has no resumable state machine, so none of the rest of this rule applies there. What remains is advice: elif chains, tails referencing prefix `let!` bindings or foreign local mutables. The non-awaiting tail is measured structurally — the statement suffix after the last await on the spine or in the branch holding it; handlers, `finally` bodies and re-awaiting loop bodies never count, a `return!` is an await, and the note is anchored on the first tail statement (a tail inside a branch is advice only)

### FR0030 — performance

A loop whose whole body is a single `ResizeArray.Add` of the loop variable becomes one `AddRange` call (`for x in xs do acc.Add x` → `acc.AddRange xs`); a projected body (`acc.Add(x * 2)`) stays a loop — the `Seq.map` spelling measured no faster than the loop and read worse (suave); `Add` is typed-gated|> Seq.map (fun x -> x * 2))`); `Add` is typed-gated to `List<'T>` so `HashSet.Add` never matches

### FR0031 — idiom

String `+` chains mixing literals and string values → interpolated string (`"Hello " + name + "!"` → `$"Hello {name}!"`); every operand must be a literal or typed-`string` identifier/path and the `+` itself must resolve to FSharp.Core, so a custom `(+)` never rewrites; literals containing `{`/`}`/`%` leave the chain alone. AT MOST TWO holes: a 3-hole interpolation falls off the compiler's String.Concat optimization onto String.Format — measured 4.9x slower with 2.3x the allocation of the + chain, which is itself already ONE String.Concat call

### FR0032 — correctness

A type that creates a disposable field (`let stream = new FileStream(...)`) without implementing `IDisposable` is noted (no fix); injected constructor parameters don't count — the injector owns them; an interface that inherits `IDisposable` counts as implementing it; `StringReader`, `StringWriter` and buffer-backed `MemoryStream` fields own nothing and are not noted

### FR0033 — idiom

An instance member touching no instance state — no self identifier, instance `let` field, primary-constructor parameter, or `base` — can be `static member` (note only: call sites change). Every name an instance `let` binds counts as state, tuple-destructured ones and let-bound functions included; a constructor parameter read inside a lambda or a record copy counts; the note follows the Visibility gate (private/internal members always, public ones under `--api-changes`, beside a signature file only private ones); `inline` members, `()`/`defaultof` stub bodies, and types whose instances are boxed to `obj` in the file (reflection or dynamic dispatch consumes them) stay quiet

### FR0034 — idiom

`if x.IsSome then x.Value + 1 else e` → `match x with | Some v -> v + 1 | None -> e` (`.Value` throws when misused; the match cannot); handles the `IsNone`/negated and `x <> None`/`x = None` forms, multi-line branches (a match laid out over lines under an `if` that opens its line), else-less unit `if`, `x.Value.P` prefixes, and spells `ValueSome`/`ValueNone` when the receiver is a voption (typed-gated, so custom `IsSome`/`Value` members never match); boolean combos rewrite to combinators — `x.IsSome && p x.Value` → `Option.exists`, `x.IsNone || p x.Value` → `Option.forall`, chains join inside the lambda

### FR0035 — performance

`List/Array/Seq.contains x ys` inside a loop — or inside a callback given to a collection function — scans `ys` linearly per iteration. When `ys` is a startup-built module binding — immutable, unshadowed, never reassigned — the FIX converts: when EVERY use of the name is one of the probes and the binding is a list/array/`seq` literal, the binding itself becomes the set (`|> Set.ofList`/`ofArray`/`ofSeq` — no companion, still immutable, `Set`'s own `.Contains` takes the probes, measured 2.5× over the list scan even at five elements); when other uses pin the binding's type, a private HashSet companion lands beside it instead (built once, `open`-aware spelling) and every probe converts together. Otherwise the note recommends the same by hand, worthwhile only for long loops over more than a handful of elements, measured with the build cost charged (probing the loop variable itself never fires)

### FR0036 — correctness

Fragile runtime type comparisons (notes): `GetType().Name = "..."` breaks silently on renames/namespaces — compare types instead; `x.GetType() = typeof<T>` is exact-type equality — `x :? T` if subtypes are fine; quiet inside a `when` guard of a `:? T as x` clause that narrows to exactly T on purpose

### FR0037 — performance

Build-once types constructed inside a loop: `ConcurrentDictionary`, `HttpClient`, `JsonSerializerOptions` (CA1869), `Regex`, `SearchValues.Create` (CA1870) — all expensive by design; note suggests hoisting out or making static. `HttpClient` gets its own wording: per-iteration construction exhausts sockets under load, and the right lifetime (a shared instance, or `IHttpClientFactory` under DI) is the author's call

### FR0038 — performance

Char overloads for single-character strings (CA1834/1847/1865-67): `s.Contains "x"` → `s.Contains 'x'` and `sb.Append "x"` → `sb.Append 'x'` (both ordinal already — fix); `s.StartsWith("x", StringComparison.Ordinal)` → `s.StartsWith('x')` (fix); bare `StartsWith`/`EndsWith`/`IndexOf` are culture-sensitive where the char overload is ordinal, so those get an advisory note only; receivers typed-gated to `String`/`StringBuilder`, and the whole rule stays out of `query { }` and quotations, where the string overload is the shape the LINQ translator recognises. Where the project's narrowest target has no char overload (`Contains(char)` is netstandard2.1+), the editor offers the portable form instead — `s.Contains "x"` → `s.IndexOf 'x' >= 0`, both ordinal and compiling on every framework; `Contains` only, since changing a culture-sensitive method is the author's call, not a portability fix

### FR0039 — performance

Allocating case-insensitive comparisons (CA1862): `x.ToLower() = "literal"` gets a FIX to `String.Equals(x, "literal", StringComparison.OrdinalIgnoreCase)` when the literal is pure ASCII — measured across all of Unicode, the two spellings then diverge for exactly two compatibility characters no config value or role string contains (U+212A KELVIN SIGN when the literal has a k; U+017F LONG S in the upper direction when it has an s); qualified spelling when the file lacks `open System`, `<>` wraps in `not`. In EDITORS the light bulb offers a second action — the culture-aware `InvariantCultureIgnoreCase` spelling — while the CLI auto-applies only the ordinal primary: a bulk tool does not guess at linguistics. FR0031 offers the same pairing: interpolation primary, one explicit String.Concat call as the editor alternative. The method-call shape gets the same fix: `path.ToLower().StartsWith "file:"` → `path.StartsWith("file:", StringComparison.OrdinalIgnoreCase)` for StartsWith/EndsWith/Contains/IndexOf/LastIndexOf — gated on the literal's case AGREEING with the lowering direction (`.ToLower().StartsWith "FILE:"` can never match, and silently making it match is a behavior change), and Contains additionally on its StringComparison overload existing in the references (netstandard2.1+). Everything else — non-ASCII literals, `a.ToLower() = b.ToLower()`, non-literal arguments — stays a note: the comparison type is the author's deliberate choice (per the .NET string best-practices guide, which names exactly this rewrite)

### FR0040 — performance

Redundant membership guards (CA1853/1868, fix): `if d.ContainsKey k then d.Remove k |> ignore` → `d.Remove k |> ignore`, `if not (s.Contains x) then s.Add x |> ignore` → `s.Add x |> ignore` — the operations already return `false` on a miss; typed-gated to `Dictionary`/`HashSet`/`SortedSet`

### FR0041 — performance

`Array.sum/average/min/max/contains` on `int[]`/`int64[]` is a scalar loop; on .NET 8+ System.Linq's `Sum()`/`Average()`/`Min()`/`Max()`/`Contains()` are SIMD-vectorized (`Contains` measured ~5x at 1000 elements, ~6x at 100k; note only: LINQ `Sum` throws on overflow where `Array.sum` wraps; floats excluded — NaN semantics differ; quiet inside `query { }`, where the code is a quotation for a provider's translator and the LINQ spelling may not translate)

### FR0042 — idiom

Fully applied `sprintf` → typed interpolated string (`sprintf "asdf %s" x` → `$"asdf %s{x}"`); specifiers are kept verbatim so the output is byte-identical; guards: regular literal with no `{`/`}`, simple arguments only, no `%a`/`%t`/`*`-widths, partial applications never match

### FR0043 — idiom

In an interpolated string that *already* has a typed hole, the remaining plain holes gain specifiers (`$"%s{name} is {age}"` → `$"%s{name} is %d{age}"`) — free compile-time type pinning since the string is on the printf path anyway; specifier-free strings are left on the F# 8 `String.Concat` fast path, and only ToString-identical specifiers are used (`%s`/`%d`/`%c`; never `%b` or `%f`)

### FR0044 — correctness

`raise ex` in a `with` handler resets the stack trace → `reraise ()` (CA2200, fix); skipped inside lambdas/nested trys where `reraise` would not compile or would mean a different exception; inside a computation expression, where `reraise ()` is not allowed, a try/with whose only arm rethrows (`with ex -> raise ex`, `return raise ex`) is removed — its body stays and an unmatched exception propagates with its trace intact

### FR0045 — correctness

`x = nan` / `x <> Double.NaN` never holds (IEEE 754) → `System.Double.IsNaN x` / negated (CA2242, fix); `Single.NaN` uses `Single.IsNaN`

### FR0046 — correctness

`lock "str"` / `lock typeof<T>` / `lock (x.GetType())` — weak-identity objects are process-wide singletons, so the monitor is shared with strangers (CA2002, note): use a dedicated `let lockObj = obj ()`; the editor offers a private lock object declared next to the locked value (or before the enclosing binding) — `lock this`, `lock stdout` and `lock x <| ...` are recognised too

### FR0047 — correctness

A type implementing `IDisposable` whose `Dispose` never touches one of its `new`-constructed disposable fields (CA2213, note) — the mirror of FR0032; the interface `Dispose` is followed one hop into `this.Dispose()` or a let-bound `dispose ()`. A `Dispose` that USES the field without releasing it says so separately — `member this.Dispose() = cts.Cancel()` cancels the token and leaves the handle (fantomas's LSPFantomasService and CloudAgent's connection factory both do), where releasing means `Dispose`/`DisposeAsync`/`Close` on it, directly or through an upcast. Quiet when the body hands off to `base.Dispose()`, and in a file that opens `System.Reactive`/`FSharp.Control.Reactive`, where a `Dispose` that unsubscribes rather than releases is the design

### FR0048 — correctness

`String.Format("{0} of {1}", x)` — a placeholder without an argument throws `FormatException` at runtime (CA2241, note); `{{` escapes handled, culture-first overload ignored

### FR0049 — correctness

Sync-over-async (CA1849/VSTHRD): `.Result`, `.Wait()`, `GetAwaiter().GetResult()`, `Async.RunSynchronously`, `Thread.Sleep` **inside** `async`/`task { }` invite thread-pool starvation and deadlocks (typed-gated receivers; `Thread.Sleep n` gets a `do! Async.Sleep n` / `do! Task.Delay n` fix in statement position, and so do `t.Wait()` — `do! t`, a `Task<T>` upcast — and `Task.WaitAll(...)` — `do! Task.WhenAll(...)`, or `let! _ =` when the joined tasks carry values; `Task.WaitAll(tasks, timeout)` stays); a blocking call inside the delegate of `Assert.Throws<E>(fun () -> ...)` moves with the assert to `ThrowsAsync` — a `let!` for xUnit and MSTest, a plain replacement for NUnit, whose ThrowsAsync returns the exception; a `let x = <blocking>` as a direct CE statement gets the bind fix across the whole matrix — `.GetAwaiter().GetResult()`, `.Result`, and single-argument `Async.RunSynchronously` (pipe or direct form) all become `let! x = ...`, with the asymmetric adapters applied: task { } binds Tasks AND Asyncs with a plain `let!`, async { } binds Asyncs natively but Tasks go behind `Async.AwaitTask` (ValueTasks have no AwaitTask overload and stay advice there); `.Result`/`.Wait()`/`GetResult()` **outside** CEs get the boundary note — wrap in `task { }` or use the sync API — and `X.FooAsync(args).GetAwaiter().GetResult()` can swap to `X.Foo(args)` when the typed tree proves a synchronous sibling with the same argument count exists — but only as an editor action or behind `{ "FR0049": { "syncSwap": 1 } }`, never auto-applied: async-in-sync is usually a waypoint toward a full-async refactor, and the tool must not walk the code backward (`Async.RunSynchronously` outside a CE is F#'s intended sync boundary and stays quiet); `Task.Run(fun () -> c |> Async.RunSynchronously)` inside `task { }` becomes `c |> Async.StartAsTask` (fix), the one fix offered inside a lambda because it deletes the lambda: both queue the computation to the thread pool, but StartAsTask does not park a pool thread on the result (`Async.StartImmediateAsTask` is the wrong twin, running on the CALLING thread until the first await). The `|> ignore` spelling keeps its `do!` through a `:> Task` upcast, since `do!` refuses a `Task<T>`. One behavioural difference, in the rare non-happy path: a cancelled computation surfaces as a CANCELLED task rather than one faulted with OperationCanceledException, which is the more honest of the two; and the TASKIFY fix: a FILE-PRIVATE sync function draining a task at its boundary becomes task-returning (body wrapped in `task { }`, drains bound with `let!`/`return!`, tails `return`-prefixed) with every caller — each required to sit in a task/async CE in a bindable shape — awaiting it, `Async.AwaitTask`-bridged in `async`; one unconvertible caller vetoes everything. Quiet when the task is known complete — under its own `IsCompleted`/`IsCompletedSuccessfully` probe, a `Task.FromResult`/`CompletedTask`/`ValueTask.FromResult` value, or after the receiver's own `Wait(...)` above; `.Result` on the antecedent inside its own `ContinueWith` continuation gets its own note instead — a faulted antecedent throws wrapped in an AggregateException there, and the continuation is a bind: the plain `t.ContinueWith(fun a -> ... a.Result ...)` becomes `task { let! r = t; return ... r ... }` (fix, for a value-returning single-line continuation that only reads `a.Result` — one that tests IsFaulted handles the antecedent itself and stays a note); before FSharp.Core 6, or on Fable, `ContinueWith` IS the bind and nothing is reported, and the taskify fix follows the same gate, or after the receiver's own `Wait(...)` above; `Task.WaitAll(tasks, timeout|token)` outside a CE is the bounded idiom like `t.Wait(timeout)`; the spine of `[<EntryPoint>]` main, a runner ending in an exit-code literal, and `.fsx` top-level statements are the console's blocking point (no boundary note), and so is a wait in a function choreographed around a thread (a signal, a `Thread`, `Interlocked` — the body FR0142 refuses to convert for the same reason: no boundary note there, a bind inside such a CE stays a note without its fix, and the taskify fix never converts such a function; `Thread.Sleep` alone is a pause, not choreography); a wait in a `finally` of async/task gets an honest note and no fix (no bind is legal there); `ManualResetEventSlim`/`SemaphoreSlim`/`CountdownEvent.Wait()`, `WaitHandle.WaitOne()`, `Barrier.SignalAndWait()`, `Thread.Join()` and `Monitor.Wait` inside a CE get an advice-only note

### FR0050 — idiom

`let mutable total = 0` + `for x in xs do total <- total + x` → `let total = xs |> List.sum` (fix); projections → `sumBy`, general combines → `fold (fun acc x -> ...) init` — same expression, same bindings, no mutable. The module matches the source's resolved kind: measured, `List.sum`/`Array.sum` run LEVEL with the loop while `Seq.sum` is ~50% slower on a list, so this is an idiom rule, and the rewrite never spells `Seq` when it knows better

### FR0051 — performance

`acc <- acc @ [x]` / `acc <- Array.append acc [|x|]` inside a loop copies the accumulator per iteration — O(n²) (note): use a ResizeArray, or cons and `List.rev`. Also `acc <- acc + s` on a STRING (typed-proven) in any loop — the slowest string builder measured, 36x a StringBuilder at 1000 pieces; the note names StringBuilder or collect-then-`String.concat`

### FR0052 — performance

`q.Count = 0` on `ConcurrentQueue`/`Stack`/`Bag` → `q.IsEmpty` (CA1836, fix): their `Count` walks segments, `IsEmpty` peeks

### FR0053 — performance

`BitConverter.ToString(bytes).Replace("-", "")` → `System.Convert.ToHexString bytes` (CA1872, fix)

### FR0054 — correctness

`raise`/`failwith` inside `Equals`/`GetHashCode`/`ToString`/`Dispose` overrides (CA1065, note): implicit callers (hash containers, debuggers, formatting, finalization) never expect them to throw; raises inside the member's own `try` stay quiet

### FR0055 — correctness

`try ... with _ -> ()` (or `:? Exception -> ()`) swallows every exception including cancellation, and `with _ -> ""` / `0` / `false` / `Unchecked.defaultof` / `None` / `ValueNone` / `null` / `[]` additionally disguises the failure as a result (note): log or `reraise ()`, and catch the specific type; deliberately ignoring a *specific* exception stays quiet, and a bool fallback is quiet only for the genuine probe idiom — a try body answering with the opposite literal (`try ...; true with _ -> false`); the editor offers, where the shape allows: a guard instead of the catch (pure-arithmetic body with one integer or decimal division; float division never throws, so no guard there), `TryParse` for a one-call `Parse` body, an IO-only catch for file IO, and a log line in the file's own logging idiom naming the exception, the method and its parameters. Test files — a test framework `open` (Xunit, NUnit.Framework, Expecto, MSTest, Fuchu, TUnit), a test attribute or an Expecto test builder; the one predicate FR0055, FR0092 and FR0132 share — are quiet: a test's catch-all is the observation, not a leak. A catch-all after a `reraise ()` arm for cancellation, or followed by an unconditional failure, is a decision and stays quiet; the one-call teardown idiom (`try x.Dispose()/Close()/Shutdown()/Cancel() with _ -> ()`) and a try around a missing-path probe that never throws (`File.Exists`, `GetLastWriteTime`) are named for what they are — the latter's advice is to delete the try; fallbacks caught too: a variable, a tuple carrying a default, a `MaxValue` sentinel, and a `when` guard that never looks at the exception

### FR0057 — cosmetic

XML doc drift (note): a doc comment with `<param>` tags that misses some actual parameters — the compiler warns about *unknown* names (FS3390) but not *missing* ones; fully undocumented functions are a style choice and stay quiet; the editor offers to scaffold an empty `<param>` tag per missing name, a sweep never writes one

### FR0058 — performance

A `let rec` re-entering itself through `seq`/`taskSeq`/`asyncSeq { }` builds a fresh enumerator per recursion level — every element pays O(depth) `MoveNext`s (note): walk with an explicit `Stack`/queue inside a single builder

### FR0059 — performance

A `private` function returning `Some`/`None` moves to `ValueSome`/`ValueNone` (fix): definition constructors and every match site rewritten together — no heap allocation per call; any use where `option` is load-bearing (`List.tryPick f`, `Option.*` pipelines, `let`-bound results, explicit annotations) suppresses the whole suggestion

### FR0060 — cosmetic

Consecutive attribute brackets merge: `[<Attr1>] [<Attr2>]` (stacked or same-line) → `[<Attr1; Attr2>]` (fix); comments between brackets and `[<assembly: ...>]` targets suppress it

### FR0061 — correctness

`invalidArg "facotr" ...` / `ArgumentException("msg", "wrongName")` — the parameter-name string must name a real parameter of the enclosing function (CA2208, note); `nameof` keeps it honest

### FR0062 — correctness

Non-private module-level `let mutable` is visible global mutable state (CA2211, note) — but only when it CHURNS: two-plus assignment sites in the file, or self-referential updates (`x <- x + 1`). Assigned at most once and never from itself, it reads as the two legitimate patterns — the poor-man's-DI seam a test assembly swaps, or the set-once startup config — and stays quiet, as do private mutables and private/internal modules; the editor offers `private` in one click, a sweep only notes

### FR0063 — correctness

`raise`/`failwith` inside `finally` replaces any exception already in flight (CA2219, note); raises the finally itself catches stay quiet

### FR0064 — correctness

Raising runtime-reserved exceptions (`OutOfMemoryException`, `StackOverflowException`, `IndexOutOfRangeException`, `NullReferenceException`, ...) misleads catchers and debuggers (CA2201, note); a match whose sibling arms raise three or more distinct exception types is a fault-injection dispatch table and stays quiet

### FR0065 — correctness

Weak cryptography (CA5350/5351, note): MD5/SHA1/DES/TripleDES/RC2 construction, TLS certificate-validation bypass via `ServerCertificateValidationCallback`, and broken/deprecated protocol constants (`SecurityProtocolType`/`SslProtocols` Ssl2/Ssl3/Tls/Tls11 — prefer setting nothing and letting the OS negotiate, or Tls12+)  Editor alternatives: SHA1 swaps to SHA256/SHA512 (mind persisted hashes), and a weak protocol constant swaps to `Tls12` — safe even mid-OR-chain since flags-OR is idempotent, minding endpoints that only speak the legacy protocol. Quiet for the WebSocket handshake's SHA-1 when the file spells RFC 6455's GUID, and for a SHA-1 constructed in a match arm whose sibling constructs SHA-256 (a format option the caller chose)

### FR0066 — correctness

SQL assembled from strings (CA2100, note): interpolation holes, `+` chains or `sprintf` flowing into `CommandText` or a `*Command` constructor — parameterize instead; the text is followed one hop through a `let`, and `CreateCommand(con, text)` and helpers named for SQL (`executeSql`, `runQuery`) count as sinks

### FR0067 — correctness

`DateTime.Parse s` / `Double.Parse s` without a culture reads differently per server culture (CA1305); the editor offers the fix with `CultureInfo.InvariantCulture` (wire and config data — the clear default) and a `CurrentCulture` alternative that makes today's implicit behavior deliberate, spelled short under an existing `open System.Globalization` and fully qualified otherwise. The CLI auto-applies invariant under `{"FR0067": {"invariant": 1}}`. Integer parses are low-risk and stay quiet, and so is a Fable project — the target runtime's parsing is not culture-bound

### FR0068 — correctness

Duplicate enum literal values (`Red = 1 ... Crimson = 1`) silently conflate cases (CA1069, note); `[<Flags>]` enums (one bit under two names) and a zero `Default`/`None` alias declared right beside its twin are deliberate synonyms and stay quiet

### FR0069 — performance

A private/internal record field `X: int option` / `DateTime option` / `Guid option` boxes the struct payload; `voption` keeps it flat. For a strictly FILE-PRIVATE type this is a fix: the field type and every use migrate as one edit set (`Some`/`None` constructions and patterns → `ValueSome`/`ValueNone`, `Option.xxx` → `ValueOption.xxx`, `defaultArg` → `defaultValueArg`, `= None` comparisons, `.IsSome`/`.IsNone`/`.Value` untouched) — sound because private means this file, so the typed symbol's uses are complete. Any use outside those shapes (binding the option value, flowing one in from a variable) keeps the note, as do internal/public types

### FR0070 — performance

A private/internal record of at most four small struct fields gains `[<Struct>]` (fix), removing a heap allocation per instance — every field is an immutable small struct, so copies are semantically invisible. The fix needs the definition to head its decl (`type`, not `and`) with no other attributes (`[<CLIMutable>]` would conflict outright); a PUBLIC record under `--api-changes` stays a note, since `[<Struct>]` there is an ABI and serialization change

### FR0071 — performance

A pure binding inside a `for`/`while`/collection lambda that depends on nothing the loop changes is re-evaluated every iteration; the fix hoists it above the loop, keeping the `#if` it was written under (the directive opens its own line above the anchor)

### FR0072 — correctness

A DU match wildcard standing in for only 1-2 concrete cases is an open else; the fix expands them (`_` → `D`), so future union growth raises incomplete-match warnings

### FR0073 — idiom

`let! x = comp` whose binder exists only to be matched collapses to `match! comp with` (F# 4.5+)

### FR0074 — idiom

Nested record copy-and-update flattens to F# 8 path syntax: `{ r with X = { r.X with Y = v } }` → `{ r with X.Y = v }` (LangVersion-gated; fields named after their type stay nested — the flattened path would resolve as the type)

### FR0075 — correctness

A locally constructed disposable bound with `let` is never disposed: fix to `use` when every mention stays in scope, advice naming the destination when it is handed to a function or captured — a same-file function is read one hop: disposing the parameter (`use`, `.Dispose()`, handing it to another disposable's constructor) counts as adoption, keeping it names the leak; under `[<EntryPoint>]` a leaked stream, writer or transaction is called out as lost work (.NET runs no finalizers at exit; other handles the OS reclaims), and in an ASP.NET action, controller or SignalR hub member the leak is per request and carries warning weight; returning it (also inside a tuple, record, upcast or `Some`/`ValueSome`/`Ok`), passing it to another disposable's constructor, or storing it in a field, property, collection (`Add`, `xs.[i] <-`), module value or ref cell is an ownership transfer, not a leak (the holder is FR0032/FR0047's business) — a transfer silences the rule even when the value was also handed elsewhere; a store into a local mutable stays a note naming the local; manual `Dispose()` calls, `(x :> IDisposable).Dispose()` and `Close()` on streams, writers, readers and sockets exempt; `StringReader`, `StringWriter` and a `MemoryStream` over a caller's buffer own nothing and are skipped; `MD5`/`SHA*`/`Aes`/`RandomNumberGenerator.Create()` count as constructions

### FR0076 — performance

`List/Array.map f |> ignore` allocates a discarded list — fix to `iter (f >> ignore)`; `Seq.map f |> ignore` is lazy and runs NOTHING (advice, the FR0017 family)

### FR0077 — correctness

An object expression missing interface members (FS0366) gets `NotImplementedException` stubs for every missing method/property, inherited interfaces in their own `interface X with` sections — the only rule that runs on non-compiling code, which is its point The editor also offers stubs that return the empty value of each member type (`()`, `None`, `[]`, zeros, `Unchecked.defaultof<_>`) instead of raising; the sweep applies only the raising form.

### FR0078 — idiom

The three-part mutable-condition loop idiom (`let! first` / `let mutable go` / rebind at loop end) collapses to F# 8 `while!` — a lone stale-bool `while` never matches, `while!` re-evaluates per iteration

### FR0079 — performance

`Task.WhenAll [| t |]` / `Task.WaitAll` / `Async.Parallel [ c ]` over a single-element literal adds indirection for nothing (CA1842/CA1843, note — the direct form changes the result type, so the author picks the landing shape)

### FR0080 — correctness

Leading TABs (FS1161 — pasted code often brings them) expand to four spaces per tab, every affected line in one fix; files with triple-quoted/verbatim strings are skipped (a tab could be string content)

### FR0081 — idiom

Path fragments joined with a hard-coded `/` or `\` separator → `Path.Combine` advice; `\` fires alone, `/` needs positive path evidence (path-ish names, rooted/extension literals, or a literal existing on disk) and URL-smelling chains never fire — a same-file binding is resolved one hop for that test (`gitHome + "/" + name` where `gitHome = "https://github.com/" + owner`); a join that is only compared or searched for is a key, not a path; path evidence is read per operand, and a call counts only through the file-system API it invokes, so `path` in a function's name is no evidence

### FR0082 — cosmetic

`[<FooAttribute>]` → `[<Foo>]` — the compiler resolves the short form

### FR0083 — cosmetic

`[<Foo()>]` → `[<Foo>]` — an empty attribute argument list says nothing

### FR0084 — cosmetic

` ``name`` ` backticks around a plain non-keyword identifier do nothing; stripped per site

### FR0085 — cosmetic

`new` on a non-IDisposable construction is noise — F# convention reserves `new` for disposables (the compiler warns the inverse as FS0760); typed-gated

### FR0086 — cosmetic

`$"no holes"` → `"no holes"` — hole-free interpolation; skipped when escaped braces would need unescaping

### FR0087 — idiom

The pattern `x :: []` → `[ x ]`

### FR0088 — cosmetic

`Case(_, _)` → `Case _` when every field is a wildcard (typed-gated to real union cases; survives field-count changes)

### FR0089 — correctness

`[ 1, 2 ]` is a SINGLE-tuple list — `,` builds a tuple, `;` separates elements (note; the classic paste trap, single-tuple lists are sometimes intended); quiet when the slot the literal fills expects tuples — a parameter typed `(k * v) list`/`seq` (`Map.ofList [ k, v ]`, `dict [ 1, 1 ]`, a tupled method argument), or an annotation spelling the tuple out

### FR0090 — idiom

Tupled → curried for internal/public functions with every project call site rewritten (cross-file; `fsharp-refactor --api-changes` only, editors get the private-only FR0008)

### FR0091 — idiom

Data-last parameter reorder for internal/public functions with every project call site rewritten (cross-file; `fsharp-refactor --api-changes` only, editors get the private-only FR0023). The two parameters must have different concrete types, so that a call site outside the project — which we can neither see nor fix — fails to compile rather than silently swapping two interchangeable arguments

### FR0092 — idiom

A constant `failwith "Error"` gains the enclosing function's arguments — `failwith $"Error, calling mymethod with x: {x}"` — so the log says which call failed, not just which line. Static messages only; an already-interpolated one was written deliberately, as was one that already names a parameter. NOTE: the exception TEXT is observable behavior — a test asserting the exact message will need updating (found the honest way: one such assertion in a 4,949-test suite). Quotes only arguments whose type prints (primitives, strings, enums, small records — never readers, streams, sockets, functions or compiler contexts); quiet on invariant messages (unreachable, not possible, NYI, internal error, invalid case), in security-named scopes (auth/session/crypt/token/password/secret), in test files, and for a message that is the function's own name; two throws sharing a text both get the note, a tuple parameter no longer disqualifies the function, and a `function` names its wildcard arm to quote the argument

### FR0093 — performance

A private/internal record field `X: int * int` is a reference tuple — one heap object per value — where `struct (int * int)` stores it inline. At most four elements, since a struct tuple is copied by value. For a strictly FILE-PRIVATE type the fix migrates the field and every use in one edit set (literal-tuple constructions, match/let destructurings, literal comparisons — `struct` spelled onto each); any use passing the tuple along whole (`fst`, a binder) keeps it a note

### FR0094 — cosmetic

Redundant parentheses around a single atomic argument to an instance *method*: `s.Contains("x")` → `s.Contains "x"`. Separate from FR0013 so either preference can be switched off alone. Left alone where the line continues into an application (`s.Contains("x") <> false` would read as if `"x" <> false` were the argument), under a projection, and for uppercase-headed paths — `System.Uri("x")` is a constructor, whose parens are load-bearing

### FR0095 — idiom

A lambda that restates a built-in: `fun x -> x` → `id`, `fun (a, b) -> a` → `fst`, `fun (a, b) -> b` → `snd`. One unannotated parameter only, and never as a direct argument to a .NET method, where the lambda-to-delegate conversion is doing work a function value may not

### FR0096 — cosmetic

Redundant parentheses around a pattern: `| (Some y) ->` → `| Some y ->`, `let f (x) = x` → `let f x = x`. The whole pattern of a match clause, or a bare atom elsewhere — `Some (x, y)`, `Some (Some x)`, `f (x: int)` and member parameters all keep theirs

### FR0097 — cosmetic

Redundant parentheses around a type: `(x: (int))` → `(x: int)`, `(string) list` → `string list`. Function and tuple types keep theirs, where the parens bind the type together

### FR0098 — cosmetic

The BCL name of a type F# abbreviates: `System.Int32` → `int`, `System.String` → `string`, `System.Object` → `obj`. Only the fully qualified form; a bare `Int32` depends on the opens and on what the file declares

### FR0099 — cosmetic

A `;` ending a line does nothing in light syntax: `let x = 1;` → `let x = 1`. Kept where it separates rather than terminates — inside a list, array, record, anonymous record or attribute group — and everywhere in a file that sets `#light "off"`. `;;` is left alone. OFF BY DEFAULT: it lexes every file containing a line-ending `;` and rarely finds anything — enable via `"FR0099": true` in fsharprefactor.json, or ask for it with `--codes FR0099`

### FR0100 — correctness

A match branch that says it is unfinished and then returns a stand-in — `| Jordan ->` / `// Not supported yet` / `None` / `ValueNone` / `false` — becomes `raise (NotImplementedException())`, so the gap reports itself instead of reaching callers as a real-looking result. The comment must sit inside the branch, between the arrow and the value, where it describes that branch and nothing else; a bare `TODO` elsewhere never counts, and `| Unknown -> None` with no such comment is left alone. `null` and `Unchecked.defaultof<_>` need the comment too — `| [] -> Unchecked.defaultof<'T>` is the entire contract of a SingleOrDefault, and `| null -> null` passes a sentinel through. Only fires where sibling branches actually compute, so a table of constants is not mistaken for a stub

### FR0101 — idiom

The Python `range(len(xs))` loop: `for i in 0 .. xs.Length - 1 do ... xs.[i]` → `for item in xs do ... item`, when the index's every use is indexing that same collection. Fix rewrites the header and each `xs.[i]`/`xs[i]`; an index also used as a value wants `iteri`, which changes shape enough to stay the author's call, and any `xs.[i] <- ...` keeps the loop

### FR0102 — performance

Positional indexing into an F# LIST inside a loop — `names.[i]` walks i cons cells per access, the quietest quadratic in F#. Typed: arrays, ResizeArray and dictionaries share the syntax and are fine; `List.item`/`List.nth` pin the type by name. Constant indexes (`xs.[0]`) and receivers bound inside the loop — by a let, a lambda parameter or a match arm's pattern — are skipped; `xs.Length`/`List.length xs` on a loop-invariant list inside a loop body gets the same note (a `for` header evaluates once and is fine). Advice: iterate directly (FR0101 fixes the canonical shape) or convert once with `List.toArray`

### FR0103 — idiom

The Python isinstance ladder: an if/elif chain of `shape :? T` tests with `shape :?> T` casts in the branches becomes one `match` with `| :? T as v ->` patterns — one type test per branch instead of test-plus-cast, and the unsafe `:?>` (an InvalidCastException waiting for a branch reorder) disappears. Needs two or more bare type-tests on the same plain identifier, single-line branches, and every cast targeting its own branch's type; a compound condition or a cross-cast keeps the chain

### FR0104 — performance

A singleton append to an accumulator in a RECURSIVE call — `collect (acc @ [x]) rest` copies the whole accumulator every step, O(n²), and it is the shape first drafts produce more when told to avoid mutation. Note only: the repair is `x :: acc` with one `List.rev` in the base case, or an array/ResizeArray when the result is consumed positionally — the base case changes either way. A general `a @ b` merge is left alone

### FR0105 — correctness

Arithmetic (`+`, `-`, `*`) on a NEAR-LIMIT integer constant — within a factor of two of `Int32.MaxValue`, or ten-ish digits into int64 territory. F# operators are unchecked by default, so overflow wraps silently and the corrupted value flows on. Note only: `open Microsoft.FSharp.Core.Operators.Checked` makes the scope throw instead, a wider type removes the ceiling, or the wraparound is intended and deserves saying so. Decimal spellings only (hex is a mask), unsigned skipped, and a file already opening Checked is left alone; a multiplication by a million or more (the time-unit conversions) and `Int32.MaxValue + e` count too; the editor offers widening to int64 first and `Checked.( op )` second

### FR0106 — performance

`Int32.Parse(s.Substring(6, 5))` → `Int32.Parse(s.AsSpan(6, 5))` (fix — a one-identifier swap). The Substring copy is discarded the moment the parser reads it; AsSpan parses in place, measured 2.6x and allocation-free. Fires only when the Substring is DIRECTLY the parser's argument (no escape), the receiver is typed-proven string, and the compilation actually offers the `ReadOnlySpan<char>` overload — which is how netstandard2.0/net4x stay untouched with no TFM sniffing. Framework methods (StartsWith, Contains, interpolation) already run on spans internally and need no rule

### FR0107 — idiom

`let mutable found = false` + `for x in xs do if p x then found <- true` → `let found = xs |> List.exists (fun x -> p x)` (fix); the `true`-initialized dual becomes `forall` with the predicate negated. Tightly gated because `exists` SHORT-CIRCUITS where the flag loop kept iterating: the loop body must be the one `if` (no `else`) optionally preceded by pure, immutable, single-line `let` bindings, which fold into the lambda; the predicate must never mention the flag and must be visibly effect-free (any assignment, sequencing, statement construct or `ignore` inside it disqualifies), nothing may reassign the flag afterward, and the source must resolve to a real List/Array/Seq. Module-resolved like FR0050; measured level with the loop on the no-hit worst case, faster on any hit

### FR0108 — idiom

Boolean identity literals drop (fix): `x && true`, `true && x`, `x || false`, `false || x` — the literal contributes nothing, the expression is the other operand. `x && false` and `true || x` stay: their value is constant but `x`'s evaluation (and its effects) changes. Deliberately fires inside `query { }` too — removing a node leaves a strictly simpler tree of shapes the translator already accepted

### FR0109 — idiom

Idempotent duplicates collapse (fix): `a || a` and `a && a` → `a` — only when the operands are textually identical and contain no function or method call (operators, `not`, property chains and indexing pass). `tryConnect () || tryConnect ()` is the deliberate retry idiom and never matches; the message also flags the likelier truth, a copy-paste that meant another operand

### FR0110 — correctness

An incomplete DU match with no wildcard (the FS0025 warning shape) gains the missing arm(s) as `| Case -> raise (System.NotImplementedException())` (fix) — FR0072's dual: that rule expands a wildcard hiding real cases, this one closes a match that has none. Coverage counts only unguarded plain case patterns (a `when` may reject); at most three missing cases, past that a wildcard was probably the intent; multi-line matches only, new arms adopt the last clause's `|` column

### FR0111 — cosmetic

`else` holding a whole nested `if` flattens to `elif` (fix) — only when the `else` sits at the outer `if`'s column (offside rules for `elif`) and nothing but whitespace separates the keywords

### FR0112 — idiom

An if/elif chain comparing ONE identifier against distinct int/string/char literals becomes a `match` (fix). The scrutinee must be a bare identifier — a call re-evaluated per comparison today would be evaluated once after the rewrite — and every `=` must resolve to FSharp.Core's (match patterns use structural equality)

### FR0113 — idiom

Nested ifs merge into one `&&` (fix), in the two exactly-semantics-preserving shapes: identical else-branches (`if a then (if b then X else E) else E` — one branch runs either way, so even an effectful E is unchanged), and no else at all (unit result). An `||`-topped condition gains parens before joining the `&&`. The tempting third shape — inner if without else while the outer has one — is deliberately absent: the merge would run E where the original ran nothing

### FR0114 — idiom

Pyramid-of-doom flip (fix, OFF by default): a then-branch of 20+ lines behind an else of 3 or fewer (both thresholds configurable, see Configuration) flips — condition negated (an existing `not` unwraps instead), short exit first, big block last. Off because plenty of teams hold the exact opposite style (happy path first); turn on per repository when short-exit-first IS the house style

### FR0115 — idiom

Base case first behind a compound guard (note): `match v with | x when a && b -> base | _ -> err` hides the base case behind a guard every new error condition must be threaded into; inverted — error guards first, base case as the final arm — the match reads top-down and extends by appending. Advice only: which case is "the base" is intent — and only when the wildcard arm visibly fails (raises, `failwith`, `Error`/`None`), so a wildcard computing an ordinary alternative is left alone

### FR0116 — idiom

A member of a `let rec ... and` group that references no sibling takes part in no recursion and moves out, as a plain `let` above the group (fix) — callers in the group still see it, and it can call nothing in the group by construction. A self-recursive member (calls itself, nobody else) leaves as its own `let rec`; when the group's HEAD is the non-recursive one nothing moves at all — its `let rec` becomes `let` and the next binding is re-crowned `let rec`. No attributes on moved bindings, membership judged conservatively (any textual mention of a sibling keeps it in)

### FR0117 — idiom

Adjacent match arms with identical single-line bodies and no guards fold into one or-pattern arm (fix). Match order is semantics, so only a CONTIGUOUS run merges, in place — the same patterns are tried in the same order. Patterns must provably bind nothing (or-patterns demand identical bindings; a lone lowercase identifier reads as a binder and is refused); literal payloads like `Some 1`/`Some 2` are fine. Composes with FR0112: an equality chain becomes a match on one pass, and its duplicate arms fold on the next

### FR0118 — correctness

A CancellationToken in scope should reach the calls that take one (fix, two shapes): a call omitting the token when the resolved method has a same-name overload with the same parameter prefix plus a trailing token (or a trailing optional token) gains `, ct`; and `CancellationToken.None` passed as an argument while a real token is in scope is replaced by it — the chain was being cut one call too early. Typed-gated end to end; requires exactly ONE token parameter on the enclosing binding (two make the choice a human call), .NET tupled call shapes, and never rewrites a stored `None` binding

### FR0119 — correctness

A blocking call inside `task { }`/`async { }` where the typed tree proves a `<Name>Async` twin exists (same parameter prefix, `T` → `Task<T>` return, an extra trailing optional CancellationToken tolerated) rewrites to the twin (fix): `let x = reader.ReadLine()` → `let! x = reader.ReadLineAsync()`, statements gain `do!` when the twin returns non-generic Task, and `async { }` bridges with `|> Async.AwaitTask` (real Tasks only there). The preventive half of FR0049, and FR0118 hands the rewritten call its token on the next pass. Never inside a body choreographed around a thread (a signal, a `Thread`, `Interlocked` — the refusal FR0142 and FR0049 share), lambdas, nested CEs, finally blocks or handlers

### FR0120 — correctness

A LogError/LogCritical/LogWarning inside an exception handler that never mentions the caught exception gains it as the first argument (fix) — the ILogger exception-first overload lets the SINK decide rendering; the editor also offers `ex.GetBaseException()` for wrapped/aggregate root causes. ANY existing mention of the exception in the arguments counts as handled, `ex.Message` included: message-only logging is a legitimate GDPR/PII choice this rule must not escalate. Typed-gated to Microsoft.Extensions.Logging

### FR0121 — correctness

Wall-clock traps on servers: `DateTime.UtcNow.Date` cuts a calendar date at a timezone-random instant — UTC midnight is nobody's midnight — and `DateTime.Today` is the SERVER's date, which the end user never sees (note; convert to the user's timezone first). A bare `DateTime.Now` offers the `UtcNow` rewrite in editors and applies on the CLI only under `{ "FR0121": { "utcNow": 1 } }` — Fable/desktop code legitimately wants local time. `DateTime.Now.Date`-style calendar reads are excluded from the fix entirely: swapping Now for UtcNow underneath one manufactures the first bug. `DateTime.Now` handed to a non-Utc timestamp setter (`File.SetLastWriteTime`) takes local time and stays; `Now` read through a member is reached too — `.Ticks` as a version number gets the rewrite, `.ToString(...)` the note only

### FR0122 — correctness

A literal regex pattern .NET rejects is a GUARANTEED ArgumentException on first use — construction compiles the pattern without running any input, so the check is cheap and exact (note; static `Regex.IsMatch/Match/Matches/Replace/Split` second arguments and `Regex(...)` constructions)

### FR0123 — correctness

The canonical `Monitor.Enter x; try body finally Monitor.Exit x` IS F#'s `lock x (fun () -> body)` spelled dangerously — the fix rewrites it (body lines travel verbatim, comments included; the whole released-on-all-paths rule family closes at the source). Gated on single-argument Enter (the `(x, &taken)` overload carries protocol), identical lock text in Enter and Exit, and the typed Monitor entity. A bare `Monitor.Enter` with no try at all is the leak note; a `try/finally` that is the first statement after the Enter (with more following) is recognised as the guard

### FR0124 — correctness

Structured-log templates that lie (notes): a template naming more or fewer placeholders than it receives arguments logs holes or drops values silently; duplicate placeholder names overwrite each other in the sink; and an interpolated string as the template destroys structured logging outright — every message becomes a distinct event and the values lose their property names. A leading exception argument is skipped before counting. The template sibling of FR0048, typed-gated to Microsoft.Extensions.Logging; Serilog and Logary (`Message.eventX` pipelines filled by `setField`) are covered beside Microsoft.Extensions.Logging

### FR0125 — correctness

Invisible and bidirectional Unicode in source (bidi controls U+202A-202E/U+2066-2069 — Trojan Source CVE-2021-42574; the Unicode tag block U+E0001/U+E0020-E007F — the prompt-smuggling channel; zero-width spaces U+200B/U+2060-2064; mid-file BOMs). Inside a REGULAR string literal the fix rewrites the character as its `XXXX` escape — same string, now visible; elsewhere it stays a note. ZWJ/ZWNJ are deliberately exempt: emoji and Persian/Arabic text use them legitimately

### FR0126 — correctness

A dynamically built string (interpolation, concat, sprintf, String.Format) reaching `Process.Start`, a `ProcessStartInfo` construction, or an `.Arguments <-` set is the command/argument-injection sink (note) — doubly so when the string carries LLM or agent output; pass a fixed executable with an argument LIST instead. The process sibling of FR0066

### FR0127 — correctness

A string literal matching a provider's DOCUMENTED credential format — `sk-ant-…` (Anthropic), `sk-…`/`sk-proj-…` (OpenAI), `AIza…` (Google), `ghp_`/`github_pat_` (GitHub), `AKIA…` (AWS), `xoxb-…` (Slack), PEM private-key headers — is a leaked key until proven otherwise (note): not entropy guessing, format anchoring; a literal that says `test` anywhere is a test account's credential and stays quiet

### FR0128 — idiom

The obsolete `*Managed`/`*CryptoServiceProvider` crypto constructors (SYSLIB0021) become the static factories (fix): `new SHA256Managed()` → `SHA256.Create()`, `new RNGCryptoServiceProvider()` → `RandomNumberGenerator.Create()` — the SAME algorithm, so behavior is preserved; weak algorithms keep their FR0065 note separately. Zero-argument constructors only

### FR0129 — idiom

A when-guard that only equality-tests the clause's own binder against a literal IS the literal pattern (fix): `| x when x = "A" ->` becomes `| "A" ->`, per clause, on match/match!/`function` alike — gated on the body never mentioning the binder (it no longer exists after the rewrite) and the compared value being a constant the pattern language can spell

### FR0130 — idiom

A module-level constant binding (string/number/char/bool literal RHS, no attributes) gains `[<Literal>]` (fix): a true CLR const — const-folded at use sites, usable in patterns and attribute arguments. Contained bindings by default (`[<Literal>]` compiles a public field to a const, a binary-compatibility change — `--api-changes` opts in). Local `let`s cannot take attributes, so the rule is module-level by construction Edits the companion .fsi in step: its val gains the attribute and the value

### FR0131 — idiom

A module-level `let rec` whose every self-call provably sits in tail position gains `[<TailCall>]` (fix): pure metadata, no codegen change — the compiler then emits FS3569 if a later edit pushes a recursive call out of tail position. Verified structurally (match arms, if/elif/else, let bodies, sequencing, pipes; full application only); any mention of the name inside a lambda, try/with, CE, `use` scope or argument vetoes. Needs FSharp.Core 8+ (typed gate); single non-mutual bindings only

### FR0132 — idiom

A PUBLIC declaration (binding, type, union case) with no XML doc but a trailing same-line `//` comment gets that comment promoted to the `///` position (fix) — same text, but only the doc position reaches tooltips and generated docs. Instruction comments (`fsharpanalyzer:`, TODO/FIXME/HACK) and private declarations are left alone; the insert spells `/` + the original comment, so the comment-loss guards pass by construction

### FR0133 — cosmetic

A five-plus-word camel or snake name — `thisIsMyVeryComplexMethod`, `this_is_my_very_complex_case` — becomes the double-backtick name ` ``this is my very complex method`` ` at its definition and every use (fix). Local and file-private bindings only, plus TEST-attributed functions (`[<Test>]`/`[<Fact>]`/...) at any visibility when the project's uses prove nothing calls them cross-file — serialization APIs legitimately demand snake_case, and a public name is a contract. Names with ALL-CAPS acronym runs (`APRUnitRate`) are skipped. TEST-attributed names rewrite BY DEFAULT — there the name is nothing but a display name and the backtick spelling is the F# testing convention; local and file-private names are the config opt-in `{"FR0133": {"locals": 1}}`, since some editors still fumble backtick-name intellisense Renames the companion .fsi val in step

### FR0134 — idiom

A file-private record field `Seen: DateTime` migrates to `DateTimeOffset` in one all-or-nothing edit set (fix) — the instant keeps the clock it was read from, closing the FR0121 class of server-timezone accidents. Strict envelope: every write is `DateTime.UtcNow`/`.Now`/`.MinValue`/`.MaxValue` with Now and UtcNow never mixed (DateTime comparisons ignore Kind — mixing was already a bug, and fixing it silently is still a behavior change); every read is a parity member (`Year`..`Second`, `Add*`/`Subtract`, `DayOfWeek`...), a same-field comparison, or a same-field subtraction. `.Date` (type escapes), `ToString` (format changes) and any unfollowed dataflow bail. OFF BY DEFAULT — a serialization-shape change the repository owner opts into via `"FR0134": true`

### FR0135 — cosmetic

A multi-line `(* ... *)` block comment in an `.fsx` script carrying clear MARKDOWN — a fenced code block or a `###` heading — becomes the literate `(** ... *)` cell it reads as (fix: one star). FSharp.Formatting silently drops markdown from plain comments; the compiler sees no difference either way. Existing `(**` cells and `(*** command ***)` cells are left alone

### FR0136 — correctness

The zero-argument Guid constructor — `Guid()` / `new System.Guid()` — is the classic .NET slip: it reads like "a new guid" but produces `00000000-…`. The fix states the value as `Guid.Empty` (identical value and type, so the CLI applies it freely); the editor also offers `Guid.NewGuid()` — the likely intent, but a behavior change only a human confirms. Typed-gated to `System.Guid`, qualification preserved; `Guid(bytes)` and friends are deliberate and stay

### FR0137 — performance

Two consecutive `map` stages of the same collection module fuse into one pass (fix): `xs |> Array.map fst |> Array.map f` → `xs |> Array.map (fst >> f)` — the intermediate array stops existing (for `Seq`, one lazy wrapper fewer); `map id` disappears into the next stage outright. Fusing interleaves the two functions per element where the eager form ran the first over every element first, so the rule only fires when the first mapper is a provably pure `fst`/`snd`/`id` — an arbitrary first mapper's side effects could be observed reordering

### FR0138 — idiom

Hand-rolled string emptiness tests become the BCL predicate that says what they mean (fix): `isNull x || x = ""` → `String.IsNullOrEmpty x`, `not (isNull x) && x <> ""` → `not (String.IsNullOrEmpty x)`, and the `Trim()`-based spellings → `String.IsNullOrWhiteSpace x` — exact rewrites (null short-circuits the `||` exactly as the predicate answers; no-argument `Trim` strips precisely the `Char.IsWhiteSpace` set the predicate tests), and the Trim forms stop allocating a trimmed copy per call. Bare `x.Trim() = ""` without a null guard is EDITOR-only: null throws in the original and answers true in the rewrite — almost always the intended robustness, but a behavior change a human signs. Subjects must be identifiers or dotted paths (pure reads)

### FR0139 — performance

A `Seq.` function applied to something the typed tree proves is an **array** (fix): `arr |> Seq.head` → `arr |> Array.head`. Measured on **.NET 10** (the runtime the benchmarks target, because the answers differ from .NET 8): head 17.1→2.6ns, tryFind 583→233ns, find 707→237ns, fold 567→239ns, forall 572→237ns, length 3.1→2.2ns. Arrays ONLY: a `Seq.` call on a list or a lazy source can be the author's point, and on an `IQueryable` the `Seq` functions are what the provider translates. Excluded by measurement rather than by taste — `iter`/`iteri` (236.6 vs 235.4ns, a wash), collection-returning functions (`Seq.map` is `seq<'b>` where `Array.map` is `'b[]`, which ripples into the consumer), `item` (`Array.item` throws `IndexOutOfRangeException` where `Seq.item` throws `ArgumentException`), the numeric aggregates (FR0041 sends those to vectorised LINQ), and `contains` on REFERENCE arrays (`Seq.contains` 938ns actually beats `Array.contains` at 1024ns). `contains` on `int[]`/`int64[]` has TWO better answers, so it offers two: the CLI applies the FASTER one — vectorised `Enumerable.Contains` (**587→109ns**), spelled `System.Linq.`-qualified unless the file opens it — and an editor offers the idiomatic `Array.contains` (587→464ns) beside it for anyone who would rather not bring System.Linq in

### FR0140 — idiom

A construction immediately followed by property assignments on the new object folds into F#'s named-property construction (fix): `let h = Henkilo()` + `h.Id <- 1L` + `h.Etunimi <- "x"` becomes `let h = Henkilo(Id = 1L, Etunimi = "x")`. Not a constructor overload and not faster — the same calls in the same order — but the object reads as constructed rather than assembled, and the half-built value stops being nameable. Only the UNINTERRUPTED run of assignments straight after the binding folds in; anything in between could observe the half-built object, so the fold stops there. Each property must be distinct and typed-settable, and no assigned value may mention the object itself

### FR0141 — idiom

A `while` loop that carries STATE forward by mutation and leaves through a boolean flag is a tail-recursive function written inside out (note, OFF BY DEFAULT): raising the flag is not a `break`, so the rest of that iteration still runs and the loop leaves only at the next condition check. A tail-recursive function would take the state as parameters and return where the decision is made. The note counts the statements that would still run, and says so only when there are any. Silent inside `async` and `task`: in a task recursion is not even available (a resumable state machine grows the stack on a recursive `return!`, as FSharp.Azure.Quantum's polling loop records in a comment), and in an async the recursive function must return `Async<_>`, so the change reaches the signature rather than the loop. Deliberately NOT the search loop either — a carried value whose every assignment is `x <- x + <literal>` is an index, and that shape already short-circuits and allocates nothing (measured 12x faster than `Array.exists` on an early hit, so a pipeline there would be a regression dressed as a cleanup). Note only: naming the function and its parameters is the author's

### FR0142 — performance

A test (Fact, Theory, Test, TestCase, TestMethod) whose body blocks on async work - Async.RunSynchronously, .Result, .Wait(), GetAwaiter().GetResult() on a Task - returns the work instead: the body becomes a task block cast to System.Threading.Tasks.Task and each blocking statement a let!/do! bind (fix); `Task.WaitAll(...)` becomes `do! Task.WhenAll(...)` and `Assert.Throws<E>(fun () -> <blocking>)` the framework's async assert with the lambda returning the awaitable (bound with `let!` for xUnit and MSTest, replaced in place for NUnit). The shapes are shared with FR0049. xUnit, NUnit 3+ and MSTest await a Task-returning test, so the thread is free while the work is in flight; a test method shape is the framework business, not a consumer, so no API change. Only spine-level blocking sites move; FsCheck Property and Expecto builders stay out

### FR0143 — correctness

A script whose `#load` chain misses a file of the project it loads from gets it loaded, in the project's order (fix): the compiler's FS0039 names what is missing, the `#load` paths name the project, and its fsproj lists the compile item that declares the name. A missing NAMESPACE from a ProjectReference gets a `#r` to that project's newest built assembly, or a note to build it first. Runs on scripts that do not typecheck — that is its input.

### FR0144 — correctness

A script `#r` or `#I` path the package no longer has is re-pointed at what it has now (fix): the first missing segment, when it is a target-framework folder (net451, netstandard1.6) or a `Name.1.2.3` version folder, is swapped for the sibling under which the rest of the path exists — a file for `#r`, a directory for `#I`. Ranked for the runtime the original implies: a net4x original wants the newest net4y, then netstandard2.0 and below, never 2.1 or netX.0; anything else wants the newest netX.0 not above the SDK the script is checked against, then netstandard 2.1, 2.0, older, and netcoreapp only as a last resort; a version folder takes the newest. Quoting and separators stay as written; other candidates are listed. `.fsx` only; runs without a typecheck.

### FR0145 — correctness

A record expression that leaves fields unassigned (FS0764) gets them (fix): read off the typed tree through the labels it does assign, each with the empty value its type makes obvious — `None`, `ValueNone`, `[]`, `[||]`, `Map.empty`, `Set.empty`, `Seq.empty`, `()` — and, where none is obvious, a `raise (System.NotImplementedException "Field")` placeholder that fails when the record is built; the editor also offers zero values (`false`, `0`, `""`, `Unchecked.defaultof<_>`). The apply tool takes only the all-obvious case. Runs on files with type errors, like FR0077.

### FR0146 — correctness

A SQL command whose text carries no parameter at all — a full-table statement, or values written into the text (note): possible, but suspicious; parameters are where the values were supposed to go

### FR0147 — idiom

A namespace spelled out at every use — six times, or four when three segments deep, tunable with `{ "FR0147": { "uses": 6, "deepUses": 4 } }` — becomes one `open` after the file's last open, and every use loses the prefix; namespaces only, by the symbol's own namespace, so `System.IO.File.Exists` shortens to `File.Exists` and the longest namespace wins; a namespace whose open would clash with a name the file defines or already uses unqualified is noted, never fixed — the note names the clashing identifiers and where they come from (the file's own definition, another open, an FSharp.Core abbreviation, an unqualified use)

### FR0148 — correctness

A public `Dispose()` on a type that does not implement `IDisposable` — directly, through an interface inheriting it, or through a base type (typed) — is a resource nothing can `use` (CA1063, note); fsharp.formatting's FsiSession hid an FCS evaluation session behind one

### FR0149 — correctness

A computation handed to `Async.Start`/`Async.StartImmediate` has nobody to observe a failure — no caller to return to, no Task to fault — so an exception in it is **unhandled on a thread-pool thread and terminates the process** (measured in fsi: `try async { failwith "y" } |> Async.Start with _ -> ()` dies). A `try/with` around the call catches nothing, because the work never runs on that thread; `StartImmediate` differs only up to the first await. `Async.StartAsTask` (fault in the Task) and `Async.RunSynchronously` (raised on the caller) are observable and never reported. Handled means the body IS a `try ... with`, or `Async.Catch` appears and a match consumes both `Choice1Of2` and `Choice2Of2` — producing the `Choice` is not handling it. Only a body this file can see is judged: an inline `async { }` or a one-hop binding in the same file. Normally no fix: the repair is a handler whose body is a design decision, and where it goes changes the behaviour — wrapped around a looping computation it still stops on the first failure, inside the loop it keeps running — so the note names that choice when the body loops. The exception is a `try/with` that wraps the start AND NOTHING ELSE: the author already wrote the handler for this computation, so the editor offers it moved inside, every clause verbatim (typed patterns and `when` guards included, which the `Async.Catch` spelling could not carry — and `Async.Catch` does not even pipe into `Async.Start`, whose argument is `Async<unit>`). A tupled start keeps its cancellation token, so that form gets no move

### FR0150 — correctness

A `use`-bound disposable read by a `task`/`async` the scope RETURNS: `use` disposes at the end of the scope, the computation runs after it, and the first read past the return throws `ObjectDisposedException` (suave's ConnectionHealthChecker died on its first interval this way). The editor offers the move — the same `use` inside the computation, disposing when the work finishes — when nothing between the binding and the computation touches it; constructing later is a timing change, so a sweep never makes it. G-Research's `DisposedBeforeAsyncRunAnalyzer` covers the same shape and recommends the same repair; this one requires the computation to actually read the binder (theirs flags the shape either way) and carries the move as an edit. Already running theirs? `"FR0150": false`

### FR0151 — correctness

An exception handler that reads only `.Message` (or `.ToString()`) from a type whose real diagnosis lives elsewhere. `ReflectionTypeLoadException.Message` is the fixed string "Unable to load one or more of the requested types." and names no cause - `LoaderExceptions` holds one exception per failure, and `Types` is PARTIALLY POPULATED rather than null, so the types that did load are in it. `WebException.Message` never contains the server's error body; that is only in `Response.GetResponseStream()`. The ReflectionTypeLoadException case gets a fix (editor only, like FR0049's sync swap - it compiles either way, but what gets logged is the author's call) that joins the loader exceptions and FILTERS NULLS, because on .NET Framework those elements can be null. But the FIRST fix offered is a different one: .NET loads every referenced assembly, so what failed is routinely a dependency this code never uses - a localization satellite, an optional plugin - while `e.Types` already holds the types that DID load, nulls standing in for the rest. Where the try body is a `GetTypes()` call, so both branches are provably `Type[]`, the editor offers the filtered `e.Types` in place of a `reraise()`/`raise`: not failing at all beats reporting the failure better. It is not a silent swallow, though - the rewrite KEEPS the rethrow for the case where nothing loaded (`Types` can be null outright, and filtering can empty it, and then the original failure really was fatal), and appends a `// TODO: log e.LoaderExceptions as a warning` where the rethrow ends its line, never where a trailing comment would swallow an `else`. Reading either member counts as an informed handler, in the clause BODY or in its `when` guard - the corpus writes `when not (isNull wex.Response)` and that handler already knows where the body is; WebException is note-only, since reading the body needs two `use` bindings and a null-Response guard. A table, so AggregateException/SqlException slot in later. Distinct from FR0120, which treats `ex.Message` as handled on purpose because logging only the message can be a PII choice - this rule fires only where the message is provably uninformative

### FR0152 — correctness

`ConcurrentDictionary.GetOrAdd` whose VALUE TYPE is a `Task`, `ValueTask` or `Lazy`. Those REMEMBER a failure instead of raising it: a faulted entry stays in the dictionary and every later reader is handed the same failure, so one transient error - a timeout, a cold dependency - outlives whatever caused it and the dependency looks down long after it recovered. Remove the entry when the value faults. Gated on the value type, so a factory that simply THROWS is never reported: GetOrAdd propagates that and stores nothing, and the next caller retries. Note-only - the remedy is a change to how the cache is designed

### FR0153 — correctness

A credential in a `[<Literal>]`. A literal is a compile-time constant, baked into every use site, so FR0127's remedy does not apply - it cannot move to configuration or a secret store. The check is a different one, so it gets its own code and stays a note rather than a warning: the value should be a DEVELOPMENT credential. A loopback server (`localhost`, `127.0.0.1`, `::1`, `(local)`, `(localdb)...`, a bare `.`, each allowing an instance or port suffix) is not reported at all, under either code - it names a developer's own machine whatever its password looks like, which is a far better signal than guessing at the password's shape: `p4ssw0rd` reads as a sample and `Hunter2Real9x` does not, yet both are equally local

