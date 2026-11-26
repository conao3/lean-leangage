/-!
# Bearer tokens

Based on `crates/h5i-app-token/src/lib.rs` and `crates/h5i-app-token/proofs/TokenSpec.lean` of
h5i (https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the functions are
written in Lean and generated to the shells; bytes are a `List UInt8` and the numbers are
`UInt64`s; a decimal or a hexadecimal field is accepted when it is the encoding of the value it
reads as; the loops over the token keep what they have read in an accumulator; `parseString`
reads the token as a `String` and returns arrays.

A token is `v1.<tenant>.<user>.<expiry>.<hex signature>`. The signature covers the payload, which
is every byte before the last dot. `encodePayload` writes the payload, `join` appends the
signature in lowercase hexadecimal, and `parse` splits a token into its fields. The shells call
`parseString`, which splits the bytes of a string as `parse` does, compute and compare the
signature and check the expiry.
-/

namespace Leangage.Token

/-- A token split into its fields. `payload` is the bytes of the token that the signature covers. -/
structure Parsed where
  tenant : UInt64
  user : UInt64
  exp : UInt64
  payload : List UInt8
  sig : List UInt8
deriving DecidableEq, Repr

/-- `n` in ASCII decimal, without leading zeros. -/
def decimal (n : Nat) : List UInt8 :=
  if n < 10 then [(n + 48).toUInt8] else decimal (n / 10) ++ [(n % 10 + 48).toUInt8]
termination_by n
decreasing_by omega

/-- `v1.<tenant>.<user>.<exp>`. -/
def encodePayload (tenant user exp : UInt64) : List UInt8 :=
  [118, 49, 46] ++ decimal tenant.toNat ++ 46 :: decimal user.toNat ++ 46 :: decimal exp.toNat

/-- The lowercase hexadecimal digit of `n < 16`. -/
def hexDigit (n : Nat) : UInt8 :=
  if n < 10 then (n + 48).toUInt8 else (n + 87).toUInt8

def hexByte (b : UInt8) : List UInt8 :=
  [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]

/-- `payload`, a dot and the lowercase hexadecimal of `sig`. -/
def join (payload sig : List UInt8) : List UInt8 :=
  payload ++ 46 :: sig.flatMap hexByte

/-- The bytes before the first dot, after the reversed `acc`, and the bytes after that dot if
there is one. -/
def splitDot (acc : List UInt8) : List UInt8 → List UInt8 × Option (List UInt8)
  | [] => (acc.reverse, none)
  | c :: rest => if c = 46 then (acc.reverse, some rest) else splitDot (c :: acc) rest

/-- The number that ASCII digits spell, most significant first. -/
def digitsValue (l : List UInt8) : Nat :=
  l.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- A field of at most 20 bytes that is the decimal of a `UInt64`. -/
def number (l : List UInt8) : Option UInt64 :=
  let n := (digitsValue l).toUInt64
  if l.length ≤ 20 && decimal n.toNat == l then some n else none

/-- The value of a lowercase hexadecimal digit, or 16. -/
def hexValue (c : UInt8) : Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then c.toNat - 48
  else if 97 ≤ c.toNat && c.toNat ≤ 102 then c.toNat - 87
  else 16

/-- The bytes that pairs of lowercase hexadecimal digits spell, after the reversed `acc`. -/
def unhex (acc : List UInt8) : List UInt8 → Option (List UInt8)
  | [] => some acc.reverse
  | [_] => none
  | a :: b :: rest =>
    if hexValue a < 16 && hexValue b < 16 then
      unhex ((hexValue a * 16 + hexValue b).toUInt8 :: acc) rest
    else none

/-- Splits `v1.<tenant>.<user>.<exp>.<hex>`; `none` unless every field is in the form
`encodePayload` and `join` write. -/
def parse (tok : List UInt8) : Option Parsed :=
  match splitDot [] tok with
  | (f0, some r0) =>
    match splitDot [] r0 with
    | (f1, some r1) =>
      match splitDot [] r1 with
      | (f2, some r2) =>
        match splitDot [] r2 with
        | (f3, some r3) =>
          match splitDot [] r3 with
          | (f4, none) =>
            if f0 = [118, 49] then
              match number f1, number f2, number f3, unhex [] f4 with
              | some t, some u, some e, some sig =>
                some ⟨t, u, e, f0 ++ 46 :: f1 ++ 46 :: f2 ++ 46 :: f3, sig⟩
              | _, _, _, _ => none
            else none
          | _ => none
        | _ => none
      | _ => none
    | _ => none
  | _ => none

/-! ## Over the bytes of a string

The functions below read a token as a `String` and write bytes into an `Array UInt8`, so a shell
passes the token without building a list. `Leangage.Token.Proofs` proves `parseString` equal to
`parse` of the bytes of the string.
-/

/-- A token split into its fields, the bytes in arrays. -/
structure ParsedArray where
  tenant : UInt64
  user : UInt64
  exp : UInt64
  payload : Array UInt8
  sig : Array UInt8
deriving DecidableEq, Repr

/-- The byte of `s` at `i`, or 0 past its end. -/
@[inline] def byteAt (s : String) (i : Nat) : UInt8 :=
  if h : i < s.utf8ByteSize then s.getUTF8Byte ⟨i⟩ h else 0

/-- The index of the first dot at `i` or after it, or the size of `s`. -/
def dotFrom (s : String) (i : Nat) : Nat :=
  if h : i < s.utf8ByteSize then
    if s.getUTF8Byte ⟨i⟩ h = 46 then i else dotFrom s (i + 1)
  else s.utf8ByteSize
termination_by s.utf8ByteSize - i

/-- `acc` followed by the digits of `s` from `i` to `j` or its end, as `digitsValue` reads them. -/
def digitsFrom (s : String) (i j acc : Nat) : Nat :=
  if i < j ∧ i < s.utf8ByteSize then digitsFrom s (i + 1) j (acc * 10 + ((byteAt s i).toNat - 48))
  else acc
termination_by s.utf8ByteSize - i

/-- Whether the bytes of `s` from `i` to `j` are `decimal n`, compared from the last digit. -/
def isDecimal (n : Nat) (s : String) (i j : Nat) : Bool :=
  if j ≤ i then false
  else if n < 10 then j = i + 1 && byteAt s i = (n + 48).toUInt8
  else byteAt s (j - 1) = (n % 10 + 48).toUInt8 && isDecimal (n / 10) s i (j - 1)
termination_by n
decreasing_by omega

/-- `number` of the bytes of `s` from `i` to `j`. -/
def numberAt (s : String) (i j : Nat) : Option UInt64 :=
  let n := (digitsFrom s i j 0).toUInt64
  if j - i ≤ 20 && isDecimal n.toNat s i j then some n else none

/-- `hexValue c` as a byte. -/
@[inline] def hexNibble (c : UInt8) : UInt8 :=
  if 48 ≤ c && c ≤ 57 then c - 48 else if 97 ≤ c && c ≤ 102 then c - 87 else 16

/-- `acc` followed by the bytes that the pairs of hexadecimal digits of `s` from `i` to `j`
spell. -/
def unhexAt (s : String) (i j : Nat) (acc : Array UInt8) : Option (Array UInt8) :=
  if i < j then
    if i + 1 < j then
      let a := hexNibble (byteAt s i)
      let b := hexNibble (byteAt s (i + 1))
      if a < 16 && b < 16 then unhexAt s (i + 2) j (acc.push (a * 16 + b)) else none
    else none
  else some acc
termination_by j - i

/-- `acc` followed by the bytes of `s` from `i` to `j` or its end. -/
def copyBytes (s : String) (i j : Nat) (acc : Array UInt8) : Array UInt8 :=
  if i < j ∧ i < s.utf8ByteSize then copyBytes s (i + 1) j (acc.push (byteAt s i)) else acc
termination_by s.utf8ByteSize - i

/-- `parse` of the bytes of `tok`. A dot after the fourth is not a hexadecimal digit, so
`unhexAt` refuses it. -/
def parseString (tok : String) : Option ParsedArray :=
  let n := tok.utf8ByteSize
  let d0 := dotFrom tok 0
  let d1 := dotFrom tok (d0 + 1)
  let d2 := dotFrom tok (d1 + 1)
  let d3 := dotFrom tok (d2 + 1)
  if d0 < n && d1 < n && d2 < n && d3 < n then
    if d0 = 2 && byteAt tok 0 = 118 && byteAt tok 1 = 49 then
      match numberAt tok (d0 + 1) d1, numberAt tok (d1 + 1) d2, numberAt tok (d2 + 1) d3,
          unhexAt tok (d3 + 1) n (.emptyWithCapacity 32) with
      | some t, some u, some e, some sig =>
        let payload := copyBytes tok (d2 + 1) d3 <| (copyBytes tok (d1 + 1) d2 <|
          (copyBytes tok (d0 + 1) d1 <|
            (copyBytes tok 0 d0 (.emptyWithCapacity d3)).push 46).push 46).push 46
        some ⟨t, u, e, payload, sig⟩
      | _, _, _, _ => none
    else none
  else none

end Leangage.Token
