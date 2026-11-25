/-!
# Bearer tokens

Based on `crates/h5i-app-token/src/lib.rs` and `crates/h5i-app-token/proofs/TokenSpec.lean` of
h5i (https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the functions are
written in Lean and generated to the shells; bytes are a `List UInt8` and the numbers are
`UInt64`s; a decimal or a hexadecimal field is accepted when it is the encoding of the value it
reads as; the loops over the token keep what they have read in an accumulator.

A token is `v1.<tenant>.<user>.<expiry>.<hex signature>`. The signature covers the payload, which
is every byte before the last dot. `encodePayload` writes the payload, `join` appends the
signature in lowercase hexadecimal, and `parse` splits a token into its fields. The shells compute
and compare the signature and check the expiry.
-/

namespace Leanharbor.Token

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

end Leanharbor.Token
