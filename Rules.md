# Rules

Every rule fsharp-refactor knows, one line each: an example of the source
it fires on and the fix it offers for it. The README explains the rules in
prose and the safety model behind them; this table is the quick reference,
and the tool's own tests keep it complete — every code in the rule catalog
has a row, its category and its default state match the code.

| ID | Category | Enabled * | API ** | Priority *** | Fires on | Offered fix |
| -- | -- | -- | -- | -- | -- | -- |
| FR0001 | Idiom | v | | | `match x with true -> a \| false -> b` | `if x then a else b` |
| FR0002 | Idiom | | | | `match x with Some v -> f v \| None -> None` | `x \|> Option.bind (fun v -> f v)` |
| FR0003 | Idiom | v | | | `xs \|> List.map (fun x -> g (f x))` | `xs \|> List.map (f >> g)` |
| FR0004 | Performance | v | | | `xs \|> Seq.toList \|> List.map f` | `xs \|> Seq.map f \|> Seq.toList` |
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
| FR0049 | Correctness | v | | | `task { let x = t.Result in use x }`, `task { t.Wait() }`, `task { Task.WaitAll(a, b) }` | `task { let! x = t in use x }`, `do! t`, `do! Task.WhenAll(a, b)` |
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

\*) Enabled by default. A blank cell means the rule is off until
`fsharprefactor.json` turns it on (`"FR0099": true`) or a run asks for it
with `--codes`.

\*\*) The fix changes a public API — a signature, a type's shape, a field
name, an exception's text that callers may read — and is applied only with
`--api-changes`; without it the rule reports and, where a declaration is
private or internal, fixes that. See the README's `--api-changes` section.

\*\*\*) Priority: a likely defect too costly to hold back — an N+1 query
loop, SQL built from strings, a raise inside finally, a regex that cannot
compile. Orthogonal to the category: these notes print without `--notes`,
editors show them as warnings, and SARIF carries them at warning level.

A `—` under Offered fix means the rule only reports: it points at the
shape and leaves the rewrite to you, either because there is no single
safe rewrite or because the right one is a design decision.
