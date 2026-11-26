import Assay
import Leangage.Token.Proofs

/-!
Breaks the token functions in small ways and runs the theorems on each broken version. The build
fails when a broken version satisfies every theorem.

The bytes are mostly tokens, written here with `Nat.repr` and not with the functions under test,
and tokens with one byte replaced, inserted or removed, so that `parse_sound` and `number_sound`
run on inputs that `parse` and `number` accept or nearly accept. The numbers include those with
one, nineteen and twenty digits.
-/

open Plausible Leangage.Token

def tokenBytes : List UInt8 := [46, 47, 48, 49, 57, 58, 65, 70, 96, 97, 102, 103, 118, 43, 45, 0, 255]

instance (priority := high) tokenArbitraryUInt8 : Arbitrary UInt8 where
  arbitrary := Gen.frequency (pure 48)
    [(3, Gen.elements tokenBytes (by decide)),
     (1, return (← Gen.choose Nat 0 255 (Nat.zero_le _)).val.toUInt8)]

instance (priority := high) tokenArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.frequency (pure 0)
    [(3, return (← Gen.choose Nat 0 12 (Nat.zero_le _)).val.toUInt64),
     (2, return (← Gen.choose Nat 0 100000 (Nat.zero_le _)).val.toUInt64),
     (2, Gen.elements [9, 10, 99, 100, 9999999999999999999, 10000000000000000000,
       18446744073709551614, 18446744073709551615] (by decide))]

instance (priority := high) tokenArbitraryNat : Arbitrary Nat where
  arbitrary := Gen.frequency (pure 0)
    [(3, return (← Gen.choose Nat 0 20 (Nat.zero_le _)).val),
     (2, return (← Gen.choose Nat 0 100000 (Nat.zero_le _)).val),
     (1, Gen.elements [18446744073709551615, 18446744073709551616, 100000000000000000000] (by decide))]

def hexOf (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    String.ofList ["0123456789abcdef".toList.getD (b.toNat / 16) '0',
      "0123456789abcdef".toList.getD (b.toNat % 16) '0'])

def numberText : Gen String :=
  Gen.frequency (pure "0")
    [(6, return toString (← Arbitrary.arbitrary : UInt64).toNat),
     (1, Gen.elements ["", "00", "01", "+1", "-1", "18446744073709551616", "99999999999999999999",
       "000000000000000000001"] (by decide))]

def tokenText : Gen String := do
  let sig ← Gen.listOf (Arbitrary.arbitrary : Gen UInt8)
  return s!"v1.{← numberText}.{← numberText}.{← numberText}.{hexOf (sig.take 4)}"

def edit (l : List UInt8) : Gen (List UInt8) := do
  let i := (← Gen.choose Nat 0 l.length (Nat.zero_le _)).val
  let c ← (Arbitrary.arbitrary : Gen UInt8)
  Gen.elements [l.take i ++ c :: l.drop (i + 1), l.take i ++ c :: l.drop i, l.take i ++ l.drop (i + 1)]
    (by simp)

instance (priority := high) tokenArbitraryBytes : Arbitrary (List UInt8) where
  arbitrary := Gen.frequency (pure [])
    [(4, return (← tokenText).toUTF8.toList),
     (4, do edit (← tokenText).toUTF8.toList),
     (2, do
       let n := (← Gen.choose Nat 0 8 (Nat.zero_le _)).val
       (List.range n).mapM fun _ => (Arbitrary.arbitrary : Gen UInt8))]

/-- Tokens and tokens with one character replaced, inserted or removed, as strings, some with
characters of two and three bytes. -/
def stringEdit (cs : List Char) : Gen (List Char) := do
  let i := (← Gen.choose Nat 0 cs.length (Nat.zero_le _)).val
  let c ← Gen.elements ['.', '0', '1', '9', 'a', 'f', 'g', 'v', '+', 'é', '€'] (by decide)
  Gen.elements [cs.take i ++ c :: cs.drop (i + 1), cs.take i ++ c :: cs.drop i, cs.take i ++ cs.drop (i + 1)]
    (by simp)

instance (priority := high) tokenArbitraryString : Arbitrary String where
  arbitrary := Gen.frequency (pure "")
    [(4, tokenText),
     (4, return String.ofList (← stringEdit (← tokenText).toList)),
     (1, Gen.elements ["", ".", "....", "v1", "é.€", "v1.0.0.0.", "v1.0.0.0.0"] (by decide))]

instance (priority := high) tokenArbitraryArray : Arbitrary (Array UInt8) where
  arbitrary := return (← (Arbitrary.arbitrary : Gen (List UInt8))).toArray

instance (priority := high) tokenSampleableString : SampleableExt String := SampleableExt.selfContained

instance (priority := high) tokenSampleableArray : SampleableExt (Array UInt8) :=
  SampleableExt.selfContained

instance (priority := high) tokenSampleableNat : SampleableExt Nat := SampleableExt.selfContained

instance (priority := high) tokenSampleableUInt8 : SampleableExt UInt8 := SampleableExt.selfContained

instance (priority := high) tokenSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

instance (priority := high) tokenSampleableBytes : SampleableExt (List UInt8) := SampleableExt.selfContained

#assay Leangage.Token.decimal
  using Leangage.Token.decimal_digit Leangage.Token.decimal_head Leangage.Token.value_decimal

#assay Leangage.Token.digitsValue using Leangage.Token.digitsValue_spec

#assay Leangage.Token.number using Leangage.Token.number_decimal Leangage.Token.number_sound

#assay Leangage.Token.hexDigit using Leangage.Token.hexDigit_spec

#assay Leangage.Token.hexValue using Leangage.Token.hexValue_spec

#assay Leangage.Token.hexByte Leangage.Token.join using Leangage.Token.join_spec

#assay Leangage.Token.splitDot using Leangage.Token.splitDot_spec

#assay Leangage.Token.unhex using Leangage.Token.unhex_hex Leangage.Token.unhex_sound

#assay Leangage.Token.encodePayload Leangage.Token.parse
  using Leangage.Token.parse_join Leangage.Token.parse_sound

#assay Leangage.Token.byteAt using Leangage.Token.byteAt_spec

#assay Leangage.Token.dotFrom
  using Leangage.Token.splitDot_dotFrom Leangage.Token.dotFrom_le Leangage.Token.dotFrom_dot

#assay Leangage.Token.digitsFrom using Leangage.Token.digitsFrom_spec

#assay Leangage.Token.isDecimal using Leangage.Token.isDecimal_spec Leangage.Token.isDecimal_field

#assay Leangage.Token.numberAt using Leangage.Token.numberAt_spec Leangage.Token.numberAt_field

#assay Leangage.Token.hexNibble using Leangage.Token.hexNibble_toNat

#assay Leangage.Token.unhexAt using Leangage.Token.unhexAt_spec

#assay Leangage.Token.copyBytes using Leangage.Token.copyBytes_spec

#assay Leangage.Token.parseString
  using Leangage.Token.parseString_spec Leangage.Token.parseString_sound
