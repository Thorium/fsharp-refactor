/// FR0065 WeakCrypto, FR0066 SqlStrings, FR0146 UnparametrizedSql, FR0126
/// ProcessSinks, FR0127 / FR0153 SecretLiterals, FR0128 ObsoleteCrypto: the
/// security notes and the crypto spelling fix.
///
/// FR0065 and FR0126 offer their fixes only to an editor (`offerAlternatives`
/// in Analyzers.fs; the CLI applies none of them by default), and those
/// offers are what `Edits` returns here: a fix a person can pick still has to
/// leave a program that compiles.
///
/// The script rules run over Test.fsx, the name the harness checks under.
/// FR0143 ScriptLoads is not reachable from a generated program: it reads
/// the FS0039 diagnostics of a script whose `#load` chain misses a file of
/// an on-disk project, so its input IS a broken compilation, which property
/// (1) forbids; it is called all the same, so a damaged program exercises it.
/// FR0144 ScriptReferences re-points a `#r` or `#I` path at a sibling folder
/// on disk beside the script — no generated program owns a directory — or,
/// when the `packages/` folder is absent altogether, turns the `#r` into a
/// package reference: that branch fires here. Typed.check resolves no
/// file-level `#r` (its options come from an empty script), so the missing
/// dll costs the program no error in the harness, where `dotnet fsi` would
/// report FS0084; the shape stands on that blind spot and says so.
module FSharp.Refactor.PropertyTests.Families.Security

open FsCheck.FSharp
open FSharp.Compiler.Text
open FSharp.Refactor
open FSharp.Refactor.PropertyTests
open FSharp.Refactor.PropertyTests.Shapes

let private crypto = "System.Security.Cryptography"

let private shapes =
    [
        // FR0065: a legacy protocol set as a function's whole body; the
        // "comment the whole setting out" offer once left `let f () =` over a
        // bare comment, which does not parse (found by this suite)
        withFree "LegacyProtocolAlone" [ "FR0065" ] (Gen.elements [ "Ssl3"; "Tls"; "Tls11" ]) (fun proto i ->
            $"let f{i} () =\n    System.Net.ServicePointManager.SecurityProtocol <- System.Net.SecurityProtocolType.{proto}")
        // FR0065: a weak hash factory; the editor offers the SHA256 and SHA512 swaps
        withFree "WeakHashCreate" [ "FR0065" ] (Gen.elements [ "MD5"; "SHA1" ]) (fun algo i ->
            $"let f{i} (data: byte[]) =\n    use h = {crypto}.{algo}.Create()\n    h.ComputeHash data")
        // FR0065: a weak cipher factory, a note without a swap
        withFree "WeakCipherCreate" [ "FR0065" ] (Gen.elements [ "DES"; "TripleDES"; "RC2" ]) (fun algo i ->
            $"let f{i} () =\n    use c = {crypto}.{algo}.Create()\n    c.KeySize")
        // FR0065 and FR0128: the obsolete constructor of a weak hash
        withFree
            "WeakHashProvider"
            [ "FR0065"; "FR0128" ]
            (Gen.elements [ "MD5CryptoServiceProvider"; "SHA1CryptoServiceProvider"; "SHA1Managed" ])
            (fun name i -> $"let f{i} (data: byte[]) =\n    use h = new {crypto}.{name}()\n    h.ComputeHash data")
        // FR0065 and FR0128: the obsolete constructor of a weak cipher
        withFree
            "WeakCipherProvider"
            [ "FR0065"; "FR0128" ]
            (Gen.elements
                [
                    "DESCryptoServiceProvider"
                    "TripleDESCryptoServiceProvider"
                    "RC2CryptoServiceProvider"
                ])
            (fun name i -> $"let f{i} () =\n    use c = new {crypto}.{name}()\n    c.KeySize")
        // FR0065: certificate validation handed a callback that accepts anything
        withFree
            "CertificateBypass"
            [ "FR0065" ]
            (Gen.elements
                [
                    "let f{i} (handler: System.Net.Http.HttpClientHandler) =\n    handler.ServerCertificateCustomValidationCallback <- (fun _ _ _ _ -> true)"
                    "let f{i} () =\n    System.Net.ServicePointManager.ServerCertificateValidationCallback <- (fun _ _ _ _ -> true)"
                ])
            (fun text i -> text.Replace("{i}", string i))
        // FR0065: a legacy protocol OR-ed after the live one; the body keeps a
        // value after the setting so commenting the whole setting out stays valid
        withFree
            "LegacyProtocolAfter"
            [ "FR0065" ]
            (Gen.zip (Gen.elements [ "Ssl3"; "Tls"; "Tls11" ]) genSmall)
            (fun (proto, n) i ->
                $"let f{i} () =\n    System.Net.ServicePointManager.SecurityProtocol <- System.Net.SecurityProtocolType.Tls12 ||| System.Net.SecurityProtocolType.{proto}\n    {n}")
        // FR0065: the legacy protocol first, on the SslProtocols enum the
        // framework marks obsolete itself
        withFree "LegacyProtocolBefore" [ "FR0065" ] (Gen.elements [ "Ssl3"; "Tls"; "Tls11" ]) (fun proto i ->
            $"let f{i} (options: System.Net.Security.SslClientAuthenticationOptions) =\n    options.EnabledSslProtocols <- System.Security.Authentication.SslProtocols.{proto} ||| System.Security.Authentication.SslProtocols.Tls12\n    options")
        // FR0066: CommandText from an interpolation hole
        withFree "InterpolatedCommandText" [ "FR0066" ] genWord (fun w i ->
            $"let f{i} (cmd: System.Data.IDbCommand) (name: string) =\n    cmd.CommandText <- $\"select * from {w} where name = '{{name}}'\"")
        // FR0066: the dynamic text bound one hop before the sink
        withFree "ConcatenatedCommandTextOneHop" [ "FR0066" ] genWord (fun w i ->
            $"let f{i} (cmd: System.Data.IDbCommand) (id: int) =\n    let sql = \"select * from {w} where id = \" + string id\n    cmd.CommandText <- sql")
        // FR0066: sprintf and String.Format build the text
        withFree
            "FormattedCommandText"
            [ "FR0066" ]
            (Gen.zip
                (Gen.elements
                    [
                        "sprintf \"delete from {w} where id = %d\" id"
                        "String.Format(\"update {w} set x = {0}\", id)"
                    ])
                genWord)
            (fun (text, w) i ->
                $"let f{i} (cmd: System.Data.IDbCommand) (id: int) =\n    cmd.CommandText <- "
                + text.Replace("{w}", w))
        // FR0066: a helper whose name says it runs SQL, handed a concatenation
        withFree "SqlHelperConcat" [ "FR0066" ] genWord (fun w i ->
            $"let f{i} (executeSql: string -> unit) (name: string) = executeSql (\"update {w} set x = '\" + name + \"'\")")
        // FR0066: SQLProvider's CreateCommand(connection, text) spelling
        withFree "CreateCommandInterpolated" [ "FR0066" ] genWord (fun w i ->
            $"type Provider{i}() =\n    member _.CreateCommand(_con: obj, text: string) = text\n    static member Run(p: Provider{i}, name: string) = p.CreateCommand(null, $\"select * from {w} where n = '{{name}}'\")")
        // FR0146: a literal statement with no parameter marker
        withFree "UnparametrizedCommandText" [ "FR0146" ] genWord (fun w i ->
            $"let f{i} (cmd: System.Data.IDbCommand) = cmd.CommandText <- \"select * from {w}\"")
        // FR0146: the same statement handed to a SQL helper with an empty parameter list
        withFree "UnparametrizedHelper" [ "FR0146" ] genWord (fun w i ->
            $"let f{i} (readSqlInteger: string -> obj list -> int) = readSqlInteger \"select max(id) from {w}\" []")
        // FR0126: Process.Start with one dynamic command line, a note only
        fixed' "ProcessStartCommandLine" [ "FR0126" ] (fun i ->
            $"let f{i} (userInput: string) = System.Diagnostics.Process.Start($\"tool {{userInput}}\") |> ignore")
        // FR0126: a fixed executable and a template that splits into arguments;
        // the editor offers the argument list
        withFree "ProcessStartTemplate" [ "FR0126" ] genWord (fun w i ->
            $"let f{i} (target: string) = System.Diagnostics.Process.Start(\"chmod\", $\"-{w} {{target}}\") |> ignore")
        // FR0126: a shell's command line, left as it is
        fixed' "ProcessStartShell" [ "FR0126" ] (fun i ->
            $"let f{i} (command: string) = System.Diagnostics.Process.Start(\"cmd.exe\", $\"/c {{command}}\") |> ignore")
        // FR0126: a ProcessStartInfo built from a concatenation
        fixed' "ProcessStartInfoConcat" [ "FR0126" ] (fun i ->
            $"let f{i} (v: string) = new System.Diagnostics.ProcessStartInfo(\"git\", \"clone \" + v)")
        // FR0126: Arguments set from a template; the editor offers ArgumentList.Add per argument
        withFree "ArgumentsTemplate" [ "FR0126" ] genWord (fun w i ->
            $"let f{i} (psi: System.Diagnostics.ProcessStartInfo) (v: string) =\n    psi.Arguments <- $\"-{w} {{v}}\"")
        // FR0126: Arguments set from sprintf, a note only
        fixed' "ArgumentsSprintf" [ "FR0126" ] (fun i ->
            $"let f{i} (psi: System.Diagnostics.ProcessStartInfo) (v: string) =\n    psi.Arguments <- sprintf \"run %%s\" v")
        // FR0127: a provider-format key in a literal (digits vary it; a random
        // word could spell `test`, and a digit run `123456`, which the rule
        // reads as a fixture)
        withFree
            "ProviderKeyLiteral"
            [ "FR0127" ]
            (Gen.zip
                (Gen.elements
                    [
                        "AKIAIOSFODNN7EXAMP{n:D2}"
                        "sk-ant-api03-abcdefghijklmnop{n}"
                        "ghp_abcdefghijklmnopqrstuvwxyz0246813579{n}"
                        "eyJhbGciOiJIUzI1NiJ9.eyJzdWIiOiIxMjM0NTY3ODkwIn0.abcdefghijklmnopqrstuv{n}"
                        "Server=db{n}.example.net;Database=app;User Id=app;Password=Hunter2Real9x"
                    ])
                genSmall)
            (fun (key, n) i ->
                $"let k{i} = \""
                + key.Replace("{n:D2}", n.ToString "D2").Replace("{n}", string n)
                + "\"")
        // FR0127: PEM material
        fixed' "PemLiteral" [ "FR0127" ] (fun i -> $"let pem{i} = \"-----BEGIN RSA PRIVATE KEY-----\"")
        // FR0127: the literal part of an interpolated string
        fixed' "ProviderKeyInterpolated" [ "FR0127" ] (fun i -> $"let f{i} (n: int) = $\"AKIAIOSFODNN7EXAMPLE {{n}}\"")
        // FR0153: a connection string with its password in a [<Literal>]
        withFree "LiteralConnectionString" [ "FR0153" ] genSmall (fun n i ->
            $"[<Literal>]\nlet Cs{i} = \"Server=db{n}.example.net;Database=app;User Id=app;Password=Hunter2Real9x\"")
        // FR0128: an obsolete strong-hash constructor becomes the factory
        withFree
            "ObsoleteHashProvider"
            [ "FR0128" ]
            (Gen.elements
                [
                    "SHA256Managed"
                    "SHA384Managed"
                    "SHA512Managed"
                    "SHA256CryptoServiceProvider"
                    "SHA384CryptoServiceProvider"
                    "SHA512CryptoServiceProvider"
                ])
            (fun name i -> $"let f{i} (data: byte[]) =\n    use h = new {crypto}.{name}()\n    h.ComputeHash data")
        // FR0128: the obsolete AES spellings
        withFree "ObsoleteAes" [ "FR0128" ] (Gen.elements [ "AesManaged"; "AesCryptoServiceProvider" ]) (fun name i ->
            $"let f{i} () =\n    use a = new {crypto}.{name}()\n    a.KeySize")
        // FR0128: the random generator
        fixed' "ObsoleteRng" [ "FR0128" ] (fun i ->
            $"let f{i} (buffer: byte[]) =\n    use rng = new {crypto}.RNGCryptoServiceProvider()\n    rng.GetBytes buffer")
        // FR0128: the constructor called without `new`
        withFree "ObsoleteHashNoNew" [ "FR0128" ] (Gen.elements [ "SHA256Managed"; "SHA512Managed" ]) (fun name i ->
            $"let f{i} (data: byte[]) = ({crypto}.{name}()).ComputeHash data")
        // FR0144: a `#r` into a packages folder that was never restored beside
        // the script (paket's storage: none), which becomes a package reference
        withFree
            "PackagesReference"
            [ "FR0144" ]
            (Gen.zip (Gen.elements [ "net6.0"; "netstandard2.0" ]) genSmall)
            (fun (tfm, n) i -> $"#r \"packages/Probe{i}.1.{n}.0/lib/{tfm}/Probe{i}.dll\"")
    ]

/// The CLI's `isObsoleteProtocol`, as Analyzers.fs builds it over the check
/// results: an enum member carrying [<Obsolete>] counts beside the curated
/// list.
let private isObsoleteProtocol (c: Typed.Checked) (r: range) =
    try
        let lineText = c.Source.GetLineString(r.EndLine - 1)

        match c.Check.GetSymbolUseAtLocation(r.EndLine, r.EndColumn, lineText, [ Text.textOfRange c.Source r ]) with
        | Some symbolUse ->
            let attributes =
                match symbolUse.Symbol with
                | :? FSharp.Compiler.Symbols.FSharpField as field ->
                    Seq.toList field.FieldAttributes @ Seq.toList field.PropertyAttributes
                | :? FSharp.Compiler.Symbols.FSharpMemberOrFunctionOrValue as value -> Seq.toList value.Attributes
                | _ -> []

            attributes
            |> List.exists (fun a ->
                try
                    a.AttributeType.TryFullName = Some "System.ObsoleteAttribute"
                with _ ->
                    false)
        | None -> false
    with _ ->
        false

let private commentOut (c: Typed.Checked) (code: string) (r: range) =
    edit code r $"(* {Text.textOfRange c.Source r} *)"

/// The whole-setting variant keeps a `()` where the setting was, first, as
/// the analyzer spells it: the setting may be a function's entire body,
/// and a comment ahead of the `()` would move the block's offside column.
let private commentOutSetting (c: Typed.Checked) (code: string) (r: range) =
    edit code r $"() (* {Text.textOfRange c.Source r} *)"

/// The name the harness checks a program under; the script rules act on `.fsx` only.
let private scriptName = "Test.fsx"

/// Every advisory finding of the family, tagged with the code the CLI gives it.
let private notes (c: Typed.Checked) =
    let crypto, sql, sinks = SecurityRules.find c.Tree c.Source (isObsoleteProtocol c)

    [
        for s in crypto do
            yield "FR0065", s.Range
        for s in sql do
            yield (if s.Unparametrized then "FR0146" else "FR0066"), s.Range
        for s in sinks do
            yield "FR0126", s.Range
        for s in SecretLiterals.find c.Tree do
            yield (if s.DesignTimeLiteral then "FR0153" else "FR0127"), s.Range
        for s in ScriptLoads.find scriptName c.Tree c.Check.Diagnostics do
            if s.InsertText.IsNone then
                yield "FR0143", s.InsertRange
    ]

let family: Family =
    {
        Name = "Security"
        Shapes = shapes
        Edits =
            fun c ->
                let crypto, _, sinks = SecurityRules.find c.Tree c.Source (isObsoleteProtocol c)

                [
                    for s in crypto do
                        match s.Kind, s.AlgoRange with
                        | SecurityRules.WeakKind.Hash("SHA1" | "MD5"), Some algo ->
                            yield "FR0065", [ edit "FR0065" algo "SHA256" ]
                            yield "FR0065", [ edit "FR0065" algo "SHA512" ]
                        | SecurityRules.WeakKind.Protocol _, Some ident ->
                            match s.ObsoleteOperand with
                            | Some operand -> yield "FR0065", [ commentOut c "FR0065" operand ]
                            | None -> ()

                            match s.AssignmentRange with
                            | Some assignment -> yield "FR0065", [ commentOutSetting c "FR0065" assignment ]
                            | None -> ()

                            yield "FR0065", [ edit "FR0065" ident "Tls12" ]
                        | _ -> ()
                    for s in sinks do
                        match s.Fix with
                        | Some(r, _, replacement) -> yield "FR0126", [ edit "FR0126" r replacement ]
                        | None -> ()
                    for s in ObsoleteCrypto.find c.Tree c.Source do
                        yield "FR0128", [ edit "FR0128" s.Range s.Replacement ]
                    // the script rules read the directives of Test.fsx: FR0143
                    // over the check's diagnostics (a project result in the
                    // CLI, the file's here), FR0144 with no compiler options
                    for s in ScriptLoads.find scriptName c.Tree c.Check.Diagnostics do
                        match s.InsertText with
                        | Some text -> yield "FR0143", [ edit "FR0143" s.InsertRange text ]
                        | None -> ()
                    for s in ScriptReferences.find scriptName c.Tree c.Source [||] do
                        yield "FR0144", [ edit "FR0144" s.Range s.ReplacementText ]
                ]
        Notes = notes
    }
