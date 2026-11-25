import Leanharbor.Json

/-!
Runs `write` natively on lines read from standard input and prints one line per input line. The
generated Rust, Python and Go are checked against this output.

A line is `write` followed by tokens separated by spaces: `n` (null), `t` and `f` (true and
false), `u<decimal>` (a number), `sx<hex>` (a string), `kx<hex>` (a key), and `[`, `]`, `{`, `}`.
It prints `json x<hex>`, the hexadecimal of what `write` writes.
-/

open Leanharbor.Json

def hexDigitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigitValue a
    let y ← hexDigitValue b
    return (x * 16 + y).toUInt8 :: (← unhexChars rest)
  | _ => none

def hexChar (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def showBytes (bs : List UInt8) : String :=
  "x" ++ String.join (bs.map fun b => String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)])

def tok (s : String) : Option Tok :=
  match s.toList with
  | ['n'] => some .null
  | ['t'] => some (.bool true)
  | ['f'] => some (.bool false)
  | ['['] => some .arrOpen
  | [']'] => some .arrClose
  | ['{'] => some .objOpen
  | ['}'] => some .objClose
  | 'u' :: digits => do
    let n ← (String.ofList digits).toNat?
    if n < 2 ^ 64 then some (.num n.toUInt64) else none
  | 's' :: 'x' :: hex => (unhexChars hex).map .str
  | 'k' :: 'x' :: hex => (unhexChars hex).map .key
  | _ => none

def run (line : String) : Option String :=
  match line.splitOn " " with
  | "write" :: toks => do
    return "json " ++ showBytes (write (← toks.mapM tok))
  | _ => none

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  IO.println ((run line.trimAscii.toString).getD "bad line")
  loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
