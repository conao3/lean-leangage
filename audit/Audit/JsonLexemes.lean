import Assay
import Leangage.Json.Lexemes.Proofs

/-!
Breaks the functions on the tokens of a JSON text in small ways and runs the theorems on each
broken version. The build fails when a broken version satisfies every theorem.

The texts of the number tokens are the decimals of the numbers sampled and texts close to one: a
leading zero, a sign, a fraction, an exponent, 2^64 and numbers of 20 and 21 digits above it. The
lists of tokens are those of an object of 2 members and lists close to one.
-/

open Plausible Leangage.Json.Lexemes

def edgeNumbers : List UInt64 := [0, 1, 7, 9, 10, 99, 100, 18446744073709551615, 18446744073709551614]

instance (priority := high) lexemesArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.elements edgeNumbers (by decide)

instance (priority := high) lexemesSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

def numberText : Gen String := do
  let n ← (Arbitrary.arbitrary : Gen UInt64)
  let text := toString n.toNat
  Gen.elements
    [text, text, text, "0" ++ text, "-" ++ text, text ++ ".0", text ++ "e2", text ++ "0", "+" ++ text,
      " " ++ text, text ++ " ", "18446744073709551616", "99999999999999999999", "100000000000000000000",
      "00", "", "a", "é"]
    (by simp)


def lexemeGen : Gen Lexeme := do
  let text ← numberText
  Gen.elements
    [.null, .bool true, .bool false, .number text, .number text, .str text, .key text, .arrOpen, .arrClose,
      .objOpen, .objClose]
    (by simp)

instance (priority := high) lexemesArbitraryLexeme : Arbitrary Lexeme where
  arbitrary := lexemeGen

instance : Shrinkable Lexeme := ⟨fun _ => []⟩

instance (priority := high) lexemesSampleableLexeme : SampleableExt Lexeme := SampleableExt.selfContained

def lexemesGen : Gen (List Lexeme) := do
  let a ← lexemeGen
  let b ← lexemeGen
  let text ← numberText
  let ms : List Lexeme := [.key "a", a, .key text, b]
  Gen.elements
    [.objOpen :: (ms ++ [.objClose]), .objOpen :: (ms ++ [.objClose]), [.objOpen, .objClose],
      .objOpen :: (ms.take 2 ++ [.objClose]), .objOpen :: ms, ms ++ [.objClose], .objOpen :: (ms.drop 1 ++ [.objClose]),
      .arrOpen :: (ms ++ [.objClose]), .objOpen :: (ms ++ [.objClose, .objClose]), [], [a]]
    (by simp)

instance (priority := high) lexemesArbitraryList : Arbitrary (List Lexeme) where
  arbitrary := lexemesGen

instance (priority := high) lexemesShrinkableList : Shrinkable (List Lexeme) := ⟨fun _ => []⟩

instance (priority := high) lexemesSampleableList : SampleableExt (List Lexeme) := SampleableExt.selfContained

def packedText : Gen String := do
  let packed := pack (← lexemesGen)
  Gen.elements
    [packed, packed, packed, packed ++ "x", packed.dropEnd 1 |>.toString, "?" ++ packed, "0" ++ packed,
      "{ks}\n3:cmdget", "{ks}\n03:cmdget", "{ks}\n9:cmdget", "{ks}\n:cmdget", "{ks}\ncmdget", "{}\nx",
      "{}\n", "{}", "{q}\n", "s\n", "#\n7", "ss\n0:", "kk\n1:é1"]
    (by simp)

instance (priority := high) lexemesArbitraryString : Arbitrary String where
  arbitrary := Gen.frequency numberText [(1, numberText), (2, packedText)]

instance (priority := high) lexemesSampleableString : SampleableExt String := SampleableExt.selfContained

instance (priority := high) lexemesArbitraryMembers : Arbitrary (List (String × Lexeme)) where
  arbitrary := do
    let a ← lexemeGen
    let b ← lexemeGen
    let text ← numberText
    Gen.elements [[("a", a), (text, b)], [("a", a)], [], [("a", a), ("a", b)], [(text, .number text)]] (by simp)

instance (priority := high) lexemesShrinkableMembers : Shrinkable (List (String × Lexeme)) := ⟨fun _ => []⟩

instance (priority := high) lexemesSampleableMembers : SampleableExt (List (String × Lexeme)) :=
  SampleableExt.selfContained

#assay Leangage.Json.Lexemes.zip using Leangage.Json.Lexemes.zip_encode

#assay Leangage.Json.Lexemes.isKind Leangage.Json.Lexemes.hasText Leangage.Json.Lexemes.splitAt
    Leangage.Json.Lexemes.lengthOf Leangage.Json.Lexemes.texts Leangage.Json.Lexemes.unpack
  using Leangage.Json.Lexemes.unpack_pack Leangage.Json.Lexemes.unpack_spec
    Leangage.Json.Lexemes.texts_packTexts Leangage.Json.Lexemes.lengthOf_toDigits

#assay Leangage.Json.Lexemes.numberOf
  using Leangage.Json.Lexemes.numberOf_iff Leangage.Json.Lexemes.numberOf_decimalText

#assay Leangage.Json.Lexemes.scalar Leangage.Json.Lexemes.members Leangage.Json.Lexemes.object
  using Leangage.Json.Lexemes.scalar_spec Leangage.Json.Lexemes.object_objectLexemes
    Leangage.Json.Lexemes.object_shape
