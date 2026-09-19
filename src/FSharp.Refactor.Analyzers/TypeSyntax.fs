/// Two refactorings on type annotations.
///
/// FR0097 — parentheses a type does not need:
///
///     let f (x: (int)) = x        →  let f (x: int) = x
///     let xs: (string) list = []  →  let xs: string list = []
///
/// Only a NAMED type or a type variable loses its parens. A function or
/// tuple type keeps them, because there they bind the type together:
/// `(int -> int) list` and `int -> int list` are different types, as are
/// `(int * int) list` and `int * int list`.
///
/// FR0098 — the BCL name of a type that F# abbreviates:
///
///     let f (x: System.Int32) = x   →  let f (x: int) = x
///     let s: System.String = ""     →  let s: string = ""
///
/// Only the fully qualified `System.X` form is rewritten. A bare `Int32` or
/// `String` depends on what is open and on what the file itself declares —
/// a project is free to define its own `String` type — and telling those
/// apart needs symbol resolution rather than syntax.
module FSharp.Refactor.TypeSyntax

open FSharp.Compiler.Syntax
open FSharp.Compiler.Text
open FSharp.Analyzers.SDK.ASTCollecting
open FSharp.Refactor.Text

type Suggestion =
    {
        /// Range of the type, i.e. the text the fix replaces.
        Range: range
        OriginalText: string
        ReplacementText: string
    }

/// BCL names F# abbreviates. `System.Void` is absent on purpose: `unit` is
/// not its abbreviation, and the two behave differently in signatures.
let private abbreviations =
    Map.ofList
        [
            "Boolean", "bool"
            "Byte", "byte"
            "SByte", "sbyte"
            "Int16", "int16"
            "UInt16", "uint16"
            "Int32", "int"
            "UInt32", "uint32"
            "Int64", "int64"
            "UInt64", "uint64"
            "Single", "float32"
            "Double", "float"
            "Decimal", "decimal"
            "Char", "char"
            "String", "string"
            "Object", "obj"
            "IntPtr", "nativeint"
            "UIntPtr", "unativeint"
        ]

/// A type that reads the same without parentheses around it.
let private isAtomicType (t: SynType) =
    match t with
    | SynType.LongIdent _
    | SynType.Var _ -> true
    | _ -> false

/// FR0097: parenthesized types whose parens do nothing.
let findRedundantParens (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let suggestions: Suggestion list =
        [
            for _, synType in index.Types do
                match synType with
                | SynType.Paren(innerType = inner) when isSingleLine synType.Range && isAtomicType inner ->
                    {
                        Range = synType.Range
                        OriginalText = textOfRange source synType.Range
                        ReplacementText = separated source synType.Range (textOfRange source inner.Range)
                    }
                | _ -> ()
        ]

    suggestions

/// FR0098: `System.Int32` and friends, written the F# way.
let findAbbreviations (parseTree: ParsedInput) (source: ISourceText) : Suggestion list =
    let index = AstIndex.ofTree parseTree

    let suggestions: Suggestion list =
        [
            for _, synType in index.Types do
                match synType with
                | SynType.LongIdent(SynLongIdent(id = [ qualifier; name ])) when qualifier.idText = "System" ->
                    match abbreviations.TryFind name.idText with
                    | Some abbreviation ->
                        {
                            Range = synType.Range
                            OriginalText = textOfRange source synType.Range
                            ReplacementText = abbreviation
                        }
                    | None -> ()
                | _ -> ()
        ]

    suggestions
