import Assay
import Leanharbor.Token.Proofs

/-!
Breaks the token functions in small ways and runs the theorems on each broken version. The build
fails when a broken version satisfies every theorem.

The bytes are mostly tokens, written here with `Nat.repr` and not with the functions under test,
and tokens with one byte replaced, inserted or removed, so that `parse_sound` and `number_sound`
run on inputs that `parse` and `number` accept or nearly accept. The numbers include those with
one, nineteen and twenty digits.
-/

open Plausible Leanharbor.Token

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

#assay Leanharbor.Token.decimal
  using Leanharbor.Token.decimal_digit Leanharbor.Token.decimal_head Leanharbor.Token.value_decimal

#assay Leanharbor.Token.digitsValue using Leanharbor.Token.digitsValue_spec

#assay Leanharbor.Token.number using Leanharbor.Token.number_decimal Leanharbor.Token.number_sound

#assay Leanharbor.Token.hexDigit using Leanharbor.Token.hexDigit_spec

#assay Leanharbor.Token.hexValue using Leanharbor.Token.hexValue_spec

#assay Leanharbor.Token.hexByte Leanharbor.Token.join using Leanharbor.Token.join_spec

#assay Leanharbor.Token.splitDot using Leanharbor.Token.splitDot_spec

#assay Leanharbor.Token.unhex using Leanharbor.Token.unhex_hex Leanharbor.Token.unhex_sound

#assay Leanharbor.Token.encodePayload Leanharbor.Token.parse
  using Leanharbor.Token.parse_join Leanharbor.Token.parse_sound

#assay Leanharbor.Token.byteAt using Leanharbor.Token.byteAt_spec

#assay Leanharbor.Token.dotFrom
  using Leanharbor.Token.splitDot_dotFrom Leanharbor.Token.dotFrom_le Leanharbor.Token.dotFrom_dot

#assay Leanharbor.Token.digitsFrom using Leanharbor.Token.digitsFrom_spec

#assay Leanharbor.Token.isDecimal using Leanharbor.Token.isDecimal_spec Leanharbor.Token.isDecimal_field

#assay Leanharbor.Token.numberAt using Leanharbor.Token.numberAt_spec Leanharbor.Token.numberAt_field

#assay Leanharbor.Token.hexNibble using Leanharbor.Token.hexNibble_toNat

#assay Leanharbor.Token.unhexAt using Leanharbor.Token.unhexAt_spec

#assay Leanharbor.Token.copyBytes using Leanharbor.Token.copyBytes_spec

#assay Leanharbor.Token.parseString
  using Leanharbor.Token.parseString_spec Leanharbor.Token.parseString_sound
