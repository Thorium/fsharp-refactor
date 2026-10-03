/// FR0175 DateFormat, FR0176 DateParts, and FR0067's Convert calls.
module FSharp.Refactor.Tests.DateRulesTests

open Xunit
open FSharp.Refactor
open FSharp.Refactor.Tests.Parsing

// ---- FR0175 DateFormat ----

let private formatsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DateFormat.find tree sourceText checkResults

let private patch (source: string) (edits: (FSharp.Compiler.Text.range * string) list) =
    edits
    |> List.sortByDescending (fun (r, _) -> r.StartLine, r.StartColumn)
    |> List.fold (fun acc (r, text) -> applyEdit acc r text) source

[<Theory>]
[<InlineData("yyyyMMddhhmmss", "yyyyMMddHHmmss")>]
[<InlineData("h:mm", "H:mm")>]
[<InlineData("yyyy-mm-dd", "yyyy-MM-dd")>]
[<InlineData("yyyymmdd", "yyyyMMdd")>]
[<InlineData("dd/mm/yyyy", "dd/MM/yyyy")>]
[<InlineData("d.m.yyyy", "d.M.yyyy")>]
[<InlineData("HH:MM", "HH:mm")>]
[<InlineData("HH:MM:ss", "HH:mm:ss")>]
[<InlineData("yyyyMMddHHMMss", "yyyyMMddHHmmss")>]
[<InlineData("yyyymmddhhmmss", "yyyyMMddHHmmss")>]
[<InlineData("yyyy-mm-dd HH:MM", "yyyy-MM-dd HH:mm")>]
[<InlineData("dd/mm/yyyy HH:MM:ss", "dd/MM/yyyy HH:mm:ss")>]
let ``FR0175: a slipped specifier is repaired in place`` (format: string, expected: string) =
    match DateFormat.repair format with
    | Some(repaired, _) -> Assert.Equal(expected, repaired)
    | None -> failwithf "Expected a repair of %s" format

[<Theory>]
[<InlineData("hh:mm tt")>]
[<InlineData("yyyyMMddHHmm")>]
[<InlineData("MM/dd/yyyy HH:mm")>]
[<InlineData("dd/MM/yyyy HH:mm:ss")>]
[<InlineData("d")>]
[<InlineData("mm:ss")>]
[<InlineData("MMM yyyy")>]
[<InlineData("HH:MMM")>]
[<InlineData("%h")>]
[<InlineData("yyyy-MM-dd 'at hh' HH:mm")>]
[<InlineData("yyyy\\mm")>]
[<InlineData("yyyy'-'mm'-'dd")>]
[<InlineData("yyyy-MM-dd mm")>]
[<InlineData("yyyy 'unclosed")>]
[<InlineData("HHhmm")>]
let ``FR0175: a sound, standard or unreadable format is left alone`` (format: string) =
    Assert.Equal(None, DateFormat.repair format)

[<Fact>]
let ``FR0175: ToString on a date type takes the repaired literal`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (d: DateTime) = d.ToString "yyyyMMddhhmmss"
            let b (d: DateTime) = d.ToString("yyyy-mm-dd")
            let c (d: DateTimeOffset) = d.ToString("HH:MM:ss", Globalization.CultureInfo.InvariantCulture)
            let e (d: DateTime) = d.ToString @"d.m.yyyy"
            let f (t: TimeOnly) = t.ToString "h:mm"
            let g () = DateTime.UtcNow.AddDays(1.0).ToString("dd/mm/yyyy")
            """

    match formatsIn source with
    | [ a; b; c; e; f; g ] as all ->
        Assert.Equal("\"yyyyMMddHHmmss\"", a.ReplacementText)
        Assert.Equal<DateFormat.Slip list>([ DateFormat.Slip.TwelveHour ], a.Slips)
        Assert.Equal("\"yyyy-MM-dd\"", b.ReplacementText)
        Assert.Equal<DateFormat.Slip list>([ DateFormat.Slip.MinutesForMonth ], b.Slips)
        Assert.Equal("\"HH:mm:ss\"", c.ReplacementText)
        Assert.Equal<DateFormat.Slip list>([ DateFormat.Slip.MonthForMinutes ], c.Slips)
        Assert.Equal("@\"d.M.yyyy\"", e.ReplacementText)
        Assert.Equal("\"H:mm\"", f.ReplacementText)
        Assert.Equal("\"dd/MM/yyyy\"", g.ReplacementText)
        Assert.All(all, (fun s -> Assert.False s.IsParse))

        let patched = patch source (all |> List.map (fun s -> s.Range, s.ReplacementText))
        Assert.Contains("d.ToString \"yyyyMMddHHmmss\"", patched)
        Assert.Contains("d.ToString @\"d.M.yyyy\"", patched)
        assertTypechecks "Patched source" patched
    | other -> failwithf "Expected six findings, got %A" other

[<Fact>]
let ``FR0175: a TimeSpan, a designator, another type and an escaped literal stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (t: TimeSpan) = t.ToString "hh"
            let b (d: DateTime) = d.ToString "hh:mm tt"
            let c (d: DateTime) = d.ToString "yyyyMMddHHmm"
            let e (d: DateTime) = d.ToString "d"
            let f (n: int) = n.ToString "hh"
            let g (d: DateTime) = d.ToString "hh\\:mm"
            let h (d: DateTime) (format: string) = d.ToString format
            """

    Assert.Empty(formatsIn source)

[<Fact>]
let ``FR0175: a parser's format is reported as one`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Globalization
            let a (s: string) = DateTime.ParseExact(s, "yyyymmdd", CultureInfo.InvariantCulture)
            let b (s: string) =
                DateTime.TryParseExact(s, [| "yyyy-mm-dd"; "dd/MM/yyyy" |], CultureInfo.InvariantCulture, DateTimeStyles.None)
            """

    match formatsIn source with
    | [ a; b ] ->
        Assert.True a.IsParse
        Assert.Equal("\"yyyyMMdd\"", a.ReplacementText)
        Assert.True b.IsParse
        Assert.Equal("\"yyyy-MM-dd\"", b.ReplacementText)
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0175: a format inside a query is left to the provider`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Linq
            let stamps (rows: IQueryable<DateTime>) =
                query {
                    for d in rows do
                        select (d.ToString "yyyy-mm-dd")
                }
            """

    Assert.Empty(formatsIn source)

// ---- FR0176 DateParts ----

let private partsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    DateParts.find tree sourceText checkResults

[<Fact>]
let ``FR0176: a year and a month read across a shift take the shifted instant`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (now: DateTime) = DateTime(now.Year, now.AddMonths(-1).Month, 25)
            let b () = DateTime(DateTime.UtcNow.AddMonths(-1).Year, DateTime.UtcNow.Month, 1)
            let c (now: DateTime) = new DateTime(now.Year, now.AddDays(1.0).Month, 1)
            let d (now: DateTime) (k: int) = DateTime(now.Year, now.AddMonths(k).Month, 1, 0, 0, 0)
            let e (now: DateTime) = DateOnly(now.Year, now.AddMonths(-1).Month, 1)
            """

    match partsIn source with
    | [ a; b; c; d; e ] as all ->
        Assert.Equal(("year", "now", "now.AddMonths(-1)"), (a.Part, a.BaseText, a.ShiftedText))
        Assert.Equal(("month", "DateTime.UtcNow", "DateTime.UtcNow.AddMonths(-1)"), (b.Part, b.BaseText, b.ShiftedText))
        Assert.Equal("now.AddDays(1.0)", c.ShiftedText)
        Assert.Equal("now.AddMonths(k)", d.ShiftedText)
        Assert.Equal("year", e.Part)

        let patched =
            patch
                source
                (all
                 |> List.map (fun s ->
                     match s.Fix with
                     | Some(r, _, replacement) -> r, replacement
                     | None -> failwithf "Expected a fix on %A" s))

        Assert.Contains("DateTime(now.AddMonths(-1).Year, now.AddMonths(-1).Month, 25)", patched)

        Assert.Contains("DateTime(DateTime.UtcNow.AddMonths(-1).Year, DateTime.UtcNow.AddMonths(-1).Month, 1)", patched)

        Assert.Contains("new DateTime(now.AddDays(1.0).Year, now.AddDays(1.0).Month, 1)", patched)
        Assert.Contains("DateOnly(now.AddMonths(-1).Year, now.AddMonths(-1).Month, 1)", patched)
        assertTypechecks "Patched source" patched
        Assert.Empty(partsIn patched)
    | other -> failwithf "Expected five findings, got %A" other

[<Fact>]
let ``FR0176: a shift that cannot be written twice, and a day read across one, are noted only`` () =
    let source =
        fsharp
            """
            module M
            open System
            let next () = 1
            let a (now: DateTime) = DateTime(now.Year, now.AddMonths(next ()).Month, 1)
            let b (now: DateTime) = DateTime(now.Year, now.Month, now.AddDays(1.0).Day)
            let c (now: DateTime) = DateTime(now.Year, now.AddYears(1).Month, 1)
            let d (now: DateTime) = DateTime(now.Year, now.AddMonths(-12).Month, 1)
            """

    match partsIn source with
    | [ a; b; c; d ] ->
        Assert.Equal("year", a.Part)
        Assert.True a.Fix.IsNone
        Assert.Equal("day", b.Part)
        Assert.True b.Fix.IsNone
        // AddYears keeps the month, so the shift is lost and nothing says
        // which year was meant
        Assert.Equal("year", c.Part)
        Assert.True c.Fix.IsNone
        // whole years written in months keep the month as well
        Assert.True d.Fix.IsNone
    | other -> failwithf "Expected four notes, got %A" other

[<Fact>]
let ``FR0176: one instant, two unrelated ones and a literal year stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (now: DateTime) = DateTime(now.Year, now.Month, 1)
            let b (now: DateTime) =
                let previous = now.AddMonths(-1)
                DateTime(previous.Year, previous.Month, 25)
            let c (opened: DateTime) (closed: DateTime) = DateTime(opened.Year, closed.AddMonths(1).Month, 1)
            let d (now: DateTime) = DateTime(2024, now.AddMonths(-1).Month, 1)
            let e (now: DateTime) = DateTime(now.AddMonths(-1).Year, now.AddMonths(-1).Month, 1)
            let f (now: DateTime) = DateTime(now.AddYears(1).Year, now.Month, 1)
            """

    Assert.Empty(partsIn source)

// ---- FR0067 Convert on a string ----

let private convertsIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    let _, parses, _ = MiscRules.findChecked (Some checkResults) tree sourceText
    parses

[<Fact>]
let ``FR0067: Convert of a string to a culture-sensitive type is the same parse`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (s: string) = Convert.ToDecimal s
            let b (s: string) = Convert.ToDouble(s)
            let c (s: string) = Convert.ToDateTime s
            """

    match convertsIn source with
    | [ a; b; c ] as all ->
        Assert.Equal("Convert.ToDecimal", a.CallName)
        Assert.Equal("Convert.ToDouble", b.CallName)
        Assert.Equal("Convert.ToDateTime", c.CallName)

        let patched =
            patch
                source
                (all
                 |> List.map (fun s ->
                     match s.CultureFix with
                     | Some mk ->
                         let r, _, replacement = mk "InvariantCulture"
                         r, replacement
                     | None -> failwithf "Expected a culture fix on %A" s.CallName))

        Assert.Contains("Convert.ToDecimal (s, System.Globalization.CultureInfo.InvariantCulture)", patched)
        Assert.Contains("Convert.ToDouble(s, System.Globalization.CultureInfo.InvariantCulture)", patched)
        assertTypechecks "Patched source" patched
        Assert.Empty(convertsIn patched)
    | other -> failwithf "Expected three notes, got %A" other

[<Fact>]
let ``FR0067: Convert of a number, an object, to an integer, or with a provider stays quiet`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (n: int) = Convert.ToDecimal n
            let b (o: obj) = Convert.ToDouble o
            let c (s: string) = Convert.ToInt32 s
            let d (s: string) = Convert.ToDecimal(s, Globalization.CultureInfo.InvariantCulture)
            let e (x: float) = Convert.ToSingle x
            """

    Assert.Empty(convertsIn source)

[<Fact>]
let ``FR0067: without check results a Convert call is not read`` () =
    let tree, sourceText =
        parse "module M\nlet a (s: string) = System.Convert.ToDecimal s"

    let _, parses, _ = MiscRules.find tree sourceText
    Assert.Empty parses

// ---- FR0017: an Async discarded by a wildcard binding ----

let private discardedIn (source: string) =
    let tree, sourceText, checkResults = parseAndCheck source
    AsyncIgnore.find tree sourceText checkResults

[<Fact>]
let ``FR0017: a call building an Async, bound to a wildcard inside a computation, never runs`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading.Tasks
            let save (x: int) = async { return x + 1 }
            let write (work: int -> Async<int>) = async { return! work 1 }
            let a () =
                async {
                    let _ = save 1
                    return 2
                }
            let b () =
                task {
                    let _ = write <| fun x -> async { return x }
                    return 2
                }
            let c (flag: bool) =
                async {
                    if flag then
                        let _ = save 3
                        ()
                    return 4
                }
            """

    match discardedIn source with
    | [ a; b; c ] as all ->
        Assert.All(all, (fun s -> Assert.True s.IsBinding))
        Assert.Equal("save", a.Name)
        Assert.Equal("let _ = save 1", a.OriginalText)
        Assert.Equal("write", b.Name)
        Assert.Equal("save", c.Name)

        let patched =
            patch
                source
                (all
                 |> List.map (fun s ->
                     match s.BindFix with
                     | Some(r, _, replacement) -> r, replacement
                     | None -> failwithf "Expected a bind fix on %s" s.OriginalText))

        Assert.Contains("let! _ = save 1", patched)
        Assert.Contains("let! _ = write <| fun x -> async { return x }", patched)
        assertTypechecks "Patched source" patched
        Assert.Empty(discardedIn patched)
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0017: outside a computation, or behind a lambda or a nested function, the note carries no fix`` () =
    let source =
        fsharp
            """
            module M
            let save (x: int) = async { return x + 1 }
            let a () =
                let _ = save 1
                2
            let b (xs: int list) =
                async {
                    let total = xs |> List.map (fun x -> let _ = save x in x) |> List.sum
                    return total
                }
            let c () =
                async {
                    let inner () =
                        let _ = save 5
                        6
                    return inner ()
                }
            let d () =
                seq {
                    let _ = save 7
                    yield 8
                }
            """

    match discardedIn source with
    | [ _; _; _; _ ] as all -> Assert.All(all, (fun s -> Assert.True(s.IsBinding && s.BindFix.IsNone)))
    | other -> failwithf "Expected four notes without a fix, got %A" other

[<Fact>]
let ``FR0017: a name bound to a wildcard, a started or running value, and a kept binding stay quiet`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading.Tasks
            let save (x: int) = async { return x + 1 }
            let saveTask (x: int) = Task.FromResult(x + 1)
            // the workflow is handed back to the caller, who decides when it runs
            let a () =
                let work = save 1
                let _ = work
                work
            let b () =
                async {
                    let _ = save 2 |> Async.StartAsTask
                    let _ = Async.Start(save 3 |> Async.Ignore)
                    let _ = saveTask 4
                    let _ = save
                    return 5
                }
            let c () =
                async {
                    let pending = save 6
                    let! _ = save 7
                    return! pending
                }
            """

    Assert.Empty(discardedIn source)

// ---- what a sweep may apply ----

[<Fact>]
let ``FR0175: the 12-hour repair is a sweep's only for a timestamp in a file with no designator`` () =
    let source =
        fsharp
            """
            module M
            open System
            let stamp (d: DateTime) = d.ToString "yyyyMMddhhmmss"
            let clock (d: DateTime) = d.ToString "hh:mm"
            let hour (d: DateTime) = d.ToString "hh"
            let date (d: DateTime) = d.ToString "yyyy-mm-dd"
            """

    match formatsIn source with
    | [ stamp; clock; hour; date ] ->
        Assert.True(stamp.SweepSafe, "a timestamp with a 12-hour clock and no designator anywhere")
        Assert.False(clock.SweepSafe, "a clock face may show AM/PM in another element")
        Assert.False(hour.SweepSafe, "an hour alone is a clock face too")
        Assert.True(date.SweepSafe, "minutes for the month has no other reading")
    | other -> failwithf "Expected four findings, got %A" other

[<Theory>]
[<InlineData("d.ToString \"tt\"")>]
[<InlineData("(if d.Hour < 12 then \"am\" else \"pm\")")>]
[<InlineData("\" PM\"")>]
[<InlineData("$\"{d:tt}\"")>]
let ``FR0175: a designator rendered by another literal keeps the 12-hour repair out of a sweep`` (designator: string) =
    let source =
        "module M\nopen System\n"
        + "let clock (d: DateTime) = d.ToString \"yyyy-MM-dd hh:mm\" + \" \" + "
        + designator
        + "\nlet date (d: DateTime) = d.ToString \"yyyy-mm-dd\"\n"

    match formatsIn source with
    | [ clock; date ] ->
        Assert.False(clock.SweepSafe, "the designator is rendered beside the clock")
        Assert.True(date.SweepSafe, "the month repair does not depend on a designator")
    | other -> failwithf "Expected two findings, got %A" other

[<Fact>]
let ``FR0175: a parser's format is never a sweep's`` () =
    let source =
        "module M\nopen System\nlet a (s: string) = DateTime.ParseExact(s, \"yyyymmdd\", Globalization.CultureInfo.InvariantCulture)"

    match formatsIn source with
    | [ a ] -> Assert.False a.SweepSafe
    | other -> failwithf "Expected one finding, got %A" other

[<Fact>]
let ``FR0017: work under way before the Async exists is not a discarded computation`` () =
    let source =
        fsharp
            """
            module M
            open System.Threading.Tasks
            let agent = MailboxProcessor<AsyncReplyChannel<int>>.Start(fun _ -> async { return () })
            let a () =
                async {
                    let _ = agent.PostAndAsyncReply id
                    let _ = Async.AwaitTask(Task.FromResult 1)
                    return 1
                }
            let b () =
                async {
                    let _ = Async.Sleep 100
                    return 1
                }
            """

    match discardedIn source with
    | [ sleep ] -> Assert.Equal("Sleep", sleep.Name)
    | other -> failwithf "Expected only the discarded sleep, got %A" other

[<Fact>]
let ``FR0175: a 12-hour parser format in the file keeps the writer's repair out of a sweep`` () =
    let source =
        fsharp
            """
            module M
            open System
            open System.Globalization
            let write (d: DateTime) = d.ToString "yyyy-MM-dd hh:mm:ss"
            let read (s: string) = DateTime.ParseExact(s, "yyyy-MM-dd hh:mm:ss", CultureInfo.InvariantCulture)
            let date (d: DateTime) = d.ToString "yyyy-mm-dd"
            """

    match formatsIn source with
    | [ write; read; date ] ->
        Assert.False(write.SweepSafe, "the reader would reject the hours the repaired writer produces")
        Assert.False read.SweepSafe
        Assert.True(date.SweepSafe, "the month repair has no reader to disagree with")
    | other -> failwithf "Expected three findings, got %A" other

[<Fact>]
let ``FR0176: only the plain year is a sweep's repair; a plain month is the editor's offer`` () =
    let source =
        fsharp
            """
            module M
            open System
            let a (now: DateTime) = DateTime(now.Year, now.AddMonths(-1).Month, 25)
            let b (now: DateTime) = DateTime(now.AddMonths(1).Year, now.Month, 1)
            """

    match partsIn source with
    | [ a; b ] ->
        Assert.True(a.SweepSafe, "the result changes only across a year boundary")
        Assert.True a.Fix.IsSome
        Assert.False(b.SweepSafe, "reading the month from the shifted instant changes the date every month")
        Assert.True b.Fix.IsSome
    | other -> failwithf "Expected two findings, got %A" other
