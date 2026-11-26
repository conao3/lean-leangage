import Assay
import Leangage.Json.Items.Proofs

/-!
Breaks the functions on the tokens of a JSON text in small ways and runs the theorems on each
broken version. The build fails when a broken version satisfies every theorem.

The texts of the number tokens are the decimals of the numbers sampled and texts close to one: a
leading zero, a sign, a fraction, an exponent, 2^64 and numbers of 20 and 21 digits above it. The
tokens are few, so that a list often holds a number token.
-/

open Plausible Leangage.Json.Items

def edgeNumbers : List UInt64 := [0, 1, 7, 9, 10, 99, 100, 18446744073709551615, 18446744073709551614]

instance (priority := high) itemsArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.elements edgeNumbers (by decide)

instance (priority := high) itemsSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

def numberText : Gen String := do
  let n ← (Arbitrary.arbitrary : Gen UInt64)
  let text := toString n.toNat
  Gen.elements
    [text, text, text, "0" ++ text, "-" ++ text, text ++ ".0", text ++ "e2", text ++ "0", "+" ++ text,
      " " ++ text, text ++ " ", "18446744073709551616", "99999999999999999999", "100000000000000000000",
      "00", "", "a", "é"]
    (by simp)

instance (priority := high) itemsArbitraryString : Arbitrary String where
  arbitrary := numberText

instance (priority := high) itemsSampleableString : SampleableExt String := SampleableExt.selfContained

def lexemeGen : Gen Lexeme := do
  let text ← numberText
  Gen.elements
    [.null, .bool true, .bool false, .number text, .number text, .str text, .key text, .arrOpen, .arrClose,
      .objOpen, .objClose]
    (by simp)

instance (priority := high) itemsArbitraryLexeme : Arbitrary Lexeme where
  arbitrary := lexemeGen

instance : Shrinkable Lexeme := ⟨fun _ => []⟩

instance (priority := high) itemsSampleableLexeme : SampleableExt Lexeme := SampleableExt.selfContained

#assay Leangage.Json.Items.numberItem
  using Leangage.Json.Items.numberItem_num_iff

#assay Leangage.Json.Items.item Leangage.Json.Items.items
  using Leangage.Json.Items.item_spec Leangage.Json.Items.items_spec
