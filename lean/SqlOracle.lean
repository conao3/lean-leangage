import Leanharbor.Sql

/-!
Runs the SQL compiler natively on lines read from standard input and prints one line per input
line. The generated Rust, Python and Go are checked against this output.

Text and bytes are hexadecimal. A value is `i<int64>`, `b0`, `b1`, `t<hex of UTF-8>`, `y<hex>` or
`n` (`NULL`). The lines:

- `reset`: empties the schema; prints `ok`.
- `table <name> <kl> <col>…` with `<col>` = `<name>:<int|bool|text|bytes>:<0|1 nullable>`: adds a
  table to the schema; prints `valid true` or `valid false`.
- `create`: prints `create`, then the text of `create` for each table.
- `put <tenant> <table> <keyLen> <value>…`, `del <tenant> <table> <value>…`,
  `delwhere <tenant> <table> <col> <value>`: compiles the planned write.
- `select <tenant> <table>`, `select <tenant> <table> <col> <value>`.

A compiled statement prints `none`, or `sql <text> <parameter>…`.
-/

open Leanharbor.Sql

def hexDigit (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigit a
    let y ← hexDigit b
    return (x * 16 + y).toUInt8 :: (← unhex rest)
  | _ => none

def hexChar (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def hex (bs : List UInt8) : String :=
  String.join (bs.map fun b => String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)])

def textOf (s : String) : Option String := do
  String.fromUTF8? ⟨(← unhex s.toList).toArray⟩

def parseVal (s : String) : Option Val :=
  match s.toList with
  | 'i' :: rest => do return .int (← (String.ofList rest).toInt?).toInt64
  | ['b', '0'] => some (.bool false)
  | ['b', '1'] => some (.bool true)
  | 't' :: rest => do return .text (← textOf (String.ofList rest))
  | 'y' :: rest => do return .bytes (← unhex rest).toArray
  | ['n'] => some .null
  | _ => none

def showVal : Val → String
  | .int v => s!"i{v.toInt}"
  | .bool false => "b0"
  | .bool true => "b1"
  | .text v => "t" ++ hex v.toUTF8.toList
  | .bytes v => "y" ++ hex v.toList
  | .null => "n"

def parseKind : String → Option Kind
  | "int" => some .int
  | "bool" => some .bool
  | "text" => some .text
  | "bytes" => some .bytes
  | _ => none

def parseCol (s : String) : Option Col :=
  match s.splitOn ":" with
  | [n, k, nullable] => do
    return ⟨← textOf n, ← parseKind k, ← match nullable with | "0" => some false | "1" => some true | _ => none⟩
  | _ => none

def showCompiled : Option (Sql × List Val) → String
  | none => "none"
  | some (q, ps) => " ".intercalate ("sql" :: hex (render q).toUTF8.toList :: ps.map showVal)

def run (schema : List Tab) (line : String) : Option (List Tab × String) := do
  let tenant (s : String) : Option Int64 := do return (← s.toInt?).toInt64
  match line.splitOn " " with
  | ["reset"] => return ([], "ok")
  | "table" :: n :: kl :: cols =>
    let schema' := schema ++ [⟨← textOf n, ← cols.mapM parseCol, ← kl.toNat?⟩]
    return (schema', s!"valid {valid schema'}")
  | ["create"] => return (schema, " ".intercalate ("create" :: schema.map fun t => hex (render (create t)).toUTF8.toList))
  | "put" :: tv :: t :: kl :: vs =>
    return (schema, showCompiled (compile schema (← tenant tv) (plan (.put (← t.toNat?) (← kl.toNat?) (← vs.mapM parseVal)))))
  | "del" :: tv :: t :: vs =>
    return (schema, showCompiled (compile schema (← tenant tv) (plan (.del (← t.toNat?) (← vs.mapM parseVal)))))
  | ["delwhere", tv, t, i, v] =>
    return (schema, showCompiled (compile schema (← tenant tv) (plan (.delWhere (← t.toNat?) (← i.toNat?) (← parseVal v)))))
  | ["select", tv, t] => return (schema, showCompiled (select schema (← tenant tv) (← t.toNat?) none))
  | ["select", tv, t, i, v] =>
    return (schema, showCompiled (select schema (← tenant tv) (← t.toNat?) (some (← i.toNat?, ← parseVal v))))
  | _ => none

partial def loop (stdin : IO.FS.Stream) (schema : List Tab) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match run schema line.trimAscii.toString with
  | none => IO.println "bad line"; loop stdin schema
  | some (schema', out) => IO.println out; loop stdin schema'

def main : IO Unit := do
  loop (← IO.getStdin) []
