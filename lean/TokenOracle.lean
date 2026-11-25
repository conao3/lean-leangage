import Leanharbor.Token

/-!
Runs the token functions natively on lines read from standard input and prints one line per input
line. The generated Rust, Python and Go are checked against this output.

Bytes are written as `x` followed by their hexadecimal, so that empty bytes are `x`. The
lines:

- `parse x<hex>`: prints `none`, or `parsed <tenant> <user> <exp> x<payload> x<signature>`.
- `issue <tenant> <user> <exp> x<signature>`: prints `token x<join (encodePayload …) signature>`.
-/

open Leanharbor.Token

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

def bytesOf (s : String) : Option (List UInt8) :=
  match s.toList with
  | 'x' :: rest => unhexChars rest
  | _ => none

def hexChar (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def showBytes (bs : List UInt8) : String :=
  "x" ++ String.join (bs.map fun b => String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)])

def uint64 (s : String) : Option UInt64 := do
  let n ← s.toNat?
  if n < 2 ^ 64 then some n.toUInt64 else none

def run (line : String) : Option String :=
  match line.splitOn " " with
  | ["parse", tok] => do
    match parse (← bytesOf tok) with
    | none => return "none"
    | some p => return s!"parsed {p.tenant} {p.user} {p.exp} {showBytes p.payload} {showBytes p.sig}"
  | ["issue", t, u, e, sig] => do
    return "token " ++ showBytes (join (encodePayload (← uint64 t) (← uint64 u) (← uint64 e)) (← bytesOf sig))
  | _ => none

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  IO.println ((run line.trimAscii.toString).getD "bad line")
  loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
