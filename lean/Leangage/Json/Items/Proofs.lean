import Leangage.Json.Items
import Leangage.Json.Proofs
import Leangage.Token.Proofs

/-!
# What the functions on the tokens of a JSON text guarantee

The JSON library of a server is trusted to hand over the tokens of the text it reads: for the
text `Value.print v`, tokens whose items are `v.toks.map Item.ofTok`. The theorems of the kernels'
functions on the wire start from those items.

- `numberItem_num_iff`: a number token is `num n` exactly when its text is the decimal of `n`,
  digits without a sign, a fraction, an exponent or a leading zero, so for no text that spells
  2^64 or more. `numberItem_decimal` is the direction that reads the decimal of every `UInt64`,
  and `numberItem_number_iff` says that every other text is `number`.
- `item_spec`, `item_decimal`: `item` reads a number token with `numberItem` and takes a string
  and a key to the bytes of their UTF-8 (`itemOf`).
- `items_spec`: `items` is the item of each token, in order.
-/

namespace Leangage.Json.Items

open Leangage.Token (bytesOf)

/-- The item that a token of the writer is read back as. -/
def Item.ofTok : Tok → Item
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
  | .key s => .key s
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

/-- Whether the byte is one of the 10 decimal digits. -/
def isDigit (c : UInt8) : Bool :=
  48 ≤ c && c ≤ 57

theorem isDigit_spec (c : UInt8) : isDigit c = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [isDigit, UInt8.le_iff_toNat_le]

theorem decimal_isDigit (n : Nat) : ∀ c ∈ Token.decimal n, isDigit c = true :=
  fun c h => (isDigit_spec c).mpr (Token.decimal_digit n c h)

theorem numberAt_whole (s : String) :
    Token.numberAt s 0 s.utf8ByteSize = Token.number (bytesOf s) := by
  rw [Token.numberAt_spec s (Nat.le_refl _)]
  have h := Token.length_bytesOf s
  simp [Token.slice, ← h]

/-- A number token is `num n` exactly when its text is the decimal of `n`. -/
theorem numberItem_num_iff (text : String) (n : UInt64) :
    numberItem text = .num n ↔ bytesOf text = Token.decimal n.toNat := by
  unfold numberItem
  rw [numberAt_whole]
  cases h : Token.number (bytesOf text) with
  | none =>
    simp only [reduceCtorEq, false_iff]
    intro h'
    rw [h', Token.number_decimal] at h
    cases h
  | some m =>
    simp only [Item.num.injEq]
    constructor
    · intro e
      subst e
      exact Token.number_canon h
    · intro h'
      rw [h', Token.number_decimal] at h
      cases h
      rfl

/-- The decimal of a `UInt64` is read as that number. -/
theorem numberItem_decimal {text : String} (n : UInt64) (h : bytesOf text = Token.decimal n.toNat) :
    numberItem text = .num n :=
  (numberItem_num_iff text n).mpr h

/-- A number token whose text is the decimal of no `UInt64` is `number`, and no other. -/
theorem numberItem_number_iff (text : String) :
    numberItem text = .number ↔ ∀ n : UInt64, bytesOf text ≠ Token.decimal n.toNat := by
  constructor
  · intro h n hn
    rw [numberItem_decimal n hn] at h
    cases h
  · intro h
    unfold numberItem
    cases hn : Token.numberAt text 0 text.utf8ByteSize with
    | none => rfl
    | some m =>
      rw [numberAt_whole] at hn
      exact absurd (Token.number_canon hn) (h m)

/-- The item of each token: a number token as `numberItem` reads it, a string and a key as the
bytes of their UTF-8. -/
def itemOf : Lexeme → Item
  | .null => .null
  | .bool b => .bool b
  | .number text => numberItem text
  | .str s => .str (bytesOf s)
  | .key s => .key (bytesOf s)
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

theorem item_spec (lexeme : Lexeme) : item lexeme = itemOf lexeme := by
  cases lexeme <;> rfl

/-- The token of the decimal of a `UInt64` is the item of that number. -/
theorem item_decimal {text : String} (n : UInt64) (h : bytesOf text = Token.decimal n.toNat) :
    item (.number text) = .num n :=
  numberItem_decimal n h

/-- `items` is the item of each token, in order. -/
theorem items_spec (lexemes : List Lexeme) : items lexemes = lexemes.map itemOf := by
  simp [items, item_spec]

theorem items_length (lexemes : List Lexeme) : (items lexemes).length = lexemes.length := by
  simp [items]

end Leangage.Json.Items
