import Leangage.Json.Lexemes
import Leangage.Json.Proofs
import Leangage.Token.Proofs

/-!
# What the functions on the tokens of a JSON text guarantee

The JSON library of a server and its conversion are trusted to hand over the tokens of the text
they read, in the order of the document: for a number the text of its token, for a string and a
key their text, packed into one text as `pack` packs them. For the bytes `Json.writeArray toks`
writes, that text is `pack (toks.map Lexeme.ofStrTok)`. The theorems of the
kernels' functions on the wire start from those tokens.

- `unpack_pack`, `unpack_iff`: `unpack` gives back the tokens that `pack` packs into one text,
  so the kernels' functions read the tokens the conversion saw, and it gives tokens for no other
  text (`texts_packTexts`, `lengthOf_toDigits`).
- `numberOf_iff`: a number token has the value `n` exactly when its text is the decimal of `n`,
  digits without a sign, a fraction, an exponent or a leading zero, so no text that spells 2^64
  or more has a value. `numberOf_decimalText` reads the decimal of every `UInt64`, and
  `numberOf_some` says that no other text has its value.
- `scalar_spec`: the value of a token that is a value by itself; a number token is `num n` when
  `numberOf` gives `n` and `number` otherwise.
- `object_iff`, `object_objectLexemes`, `object_shape`, `members_object`: `object` gives members exactly for the
  tokens of an object whose values are values by themselves (`objectLexemes`), and the members
  are the names with the values of those tokens, in order, a member twice as two members
  (`scalars`).
-/

namespace Leangage.Json.Lexemes

open Leangage.Token (bytesOf)

theorem bytesOf_injective {s t : String} (h : bytesOf s = bytesOf t) : s = t := by
  apply String.toByteArray_inj.mp
  cases hs : s.toByteArray
  cases ht : t.toByteArray
  simp_all [bytesOf]

theorem ofList_bytes (cs : List Char) : bytesOf (String.ofList cs) = cs.flatMap String.utf8EncodeChar := by
  simp [bytesOf, String.ofList, List.utf8Encode]

theorem bytesOf_append (a b : String) : bytesOf (a ++ b) = bytesOf a ++ bytesOf b := by
  simp [bytesOf, String.toByteArray_append, ByteArray.data_append]

/-- A text starts with another exactly when its bytes start with the bytes of the other. -/
theorem startsWith_iff (s p : String) :
    s.startsWith p = true ↔ ∃ r, bytesOf s = bytesOf p ++ r := by
  rw [String.startsWith_string_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨bytesOf (String.ofList t), ?_⟩
    have hs : s = p ++ String.ofList t := by
      rw [← String.toList_inj, String.toList_append, String.toList_ofList, ht]
    conv => lhs; rw [hs]
    exact bytesOf_append _ _
  · rintro ⟨r, hr⟩
    apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (ByteArray.mk r.toArray)
    rw [String.utf8Encode_toList, String.utf8Encode_toList]
    apply ByteArray.ext
    rw [ByteArray.data_append, ← Array.toList_inj]
    simpa [bytesOf] using hr.symm

/-- The decimal digits of a number, as text. -/
def decimalText (n : UInt64) : String :=
  String.ofList (Nat.toDigits 10 n.toNat)

theorem bytesOf_decimalText (n : UInt64) : bytesOf (decimalText n) = Token.decimal n.toNat := by
  rw [Json.decimal_spec, Json.digits, Json.ascii, decimalText, ofList_bytes]
  have h : ∀ c ∈ Nat.toDigits 10 n.toNat, String.utf8EncodeChar c = [c.toNat.toUInt8] := by
    intro c hc
    have hd := Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at hd
    have h7 : c.val.toNat ≤ 127 := by
      have := hd.2
      rw [UInt32.le_iff_toNat_le] at this
      exact Nat.le_trans this (by decide)
    unfold String.utf8EncodeChar
    simp only [h7, ↓reduceIte]
    rfl
  generalize Nat.toDigits 10 n.toNat = cs at h
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [h c (by simp), ih (fun x hx => h x (by simp [hx]))]

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

/-- A number token has the value `n` exactly when its text is the decimal of `n`. -/
theorem numberOf_iff (text : String) (n : UInt64) :
    numberOf text = some n ↔ bytesOf text = Token.decimal n.toNat := by
  unfold numberOf
  rw [numberAt_whole]
  constructor
  · exact Token.number_canon
  · intro h
    rw [h, Token.number_decimal]

/-- The decimal of a `UInt64` is read as that number. -/
theorem numberOf_decimalText (n : UInt64) : numberOf (decimalText n) = some n :=
  (numberOf_iff _ n).mpr (bytesOf_decimalText n)

/-- A number token with a value is the decimal of that value. -/
theorem numberOf_some {text : String} {n : UInt64} (h : numberOf text = some n) :
    text = decimalText n :=
  bytesOf_injective (((numberOf_iff text n).mp h).trans (bytesOf_decimalText n).symm)

/-- The value of each token that is a value by itself. -/
def scalarOf : Lexeme → Option Scalar
  | .null => some .null
  | .bool b => some (.bool b)
  | .number text => some ((numberOf text).elim .number .num)
  | .str s => some (.str s)
  | .key _ | .arrOpen | .arrClose | .objOpen | .objClose => none

theorem scalar_spec (lexeme : Lexeme) : scalar lexeme = scalarOf lexeme := by
  cases lexeme <;> simp [scalar, scalarOf]
  split <;> simp_all

/-- The token of the decimal of a `UInt64` is that number. -/
theorem scalar_decimalText (n : UInt64) : scalar (.number (decimalText n)) = some (.num n) := by
  simp [scalar, numberOf_decimalText]

/-- The token a JSON library hands over for a token of the writer: a number as its decimal. -/
def Lexeme.ofStrTok : StrTok → Lexeme
  | .null => .null
  | .bool b => .bool b
  | .num n => .number (decimalText n)
  | .str s => .str s
  | .key s => .key s
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

/-- The character for the kind of a token. -/
def kindOf : Lexeme → Char
  | .null => 'n'
  | .bool true => 't'
  | .bool false => 'f'
  | .number _ => '#'
  | .str _ => 's'
  | .key _ => 'k'
  | .arrOpen => '['
  | .arrClose => ']'
  | .objOpen => '{'
  | .objClose => '}'

/-- The text of a number, a string and a key. -/
def textOf : Lexeme → Option String
  | .number text => some text
  | .str s => some s
  | .key s => some s
  | _ => none

/-- The texts as a server's conversion packs them: each text but the last after the count of its
characters in decimal and a colon. -/
def packTexts : List String → List Char
  | [] => []
  | [t] => t.toList
  | t :: t' :: ts => Nat.toDigits 10 t.toList.length ++ ':' :: (t.toList ++ packTexts (t' :: ts))

/-- The tokens as a server's conversion hands them over, in one text: the kinds of the tokens, a
line feed, and the texts of the numbers, the strings and the keys. -/
def pack (lexemes : List Lexeme) : String :=
  String.ofList (lexemes.map kindOf ++ '\n' :: packTexts (lexemes.filterMap textOf))

theorem zip_encode (lexemes : List Lexeme) : zip (lexemes.map kindOf) (lexemes.filterMap textOf) = lexemes := by
  induction lexemes with
  | nil => rfl
  | cons l ls ih =>
    cases l with
    | bool b => cases b <;> simp [kindOf, textOf, zip, List.filterMap_cons, ih]
    | _ => simp [kindOf, textOf, zip, List.filterMap_cons, ih]

theorem splitAt_append {stop : Char} {a : List Char} (b : List Char) (h : stop ∉ a) :
    splitAt stop (a ++ stop :: b) = some (a, b) := by
  induction a with
  | nil => simp [splitAt]
  | cons c a ih =>
    have hc : c ≠ stop := fun e => h (e ▸ List.mem_cons_self ..)
    simp [splitAt, hc, ih (fun m => h (List.mem_cons_of_mem _ m))]

theorem splitAt_some {stop : Char} {l a b : List Char} (h : splitAt stop l = some (a, b)) :
    l = a ++ stop :: b := by
  induction l generalizing a with
  | nil => simp [splitAt] at h
  | cons c l ih =>
    unfold splitAt at h
    split at h
    · rename_i hc
      cases h
      simp [hc]
    · split at h
      · rename_i before after hs
        cases h
        simp [ih hs]
      · cases h

theorem lengthOf_snoc (cs : List Char) (c : Char) :
    lengthOf (cs ++ [c]) = lengthOf cs * 10 + (c.toNat - 48) := by
  simp [lengthOf]

/-- The decimal digits of a number spell it. -/
theorem lengthOf_toDigits (n : Nat) : lengthOf (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hd : ∀ d, d < 10 → (Nat.digitChar d).toNat - 48 = d := by decide
    rw [Nat.toDigits_eq_ite (by decide)]
    by_cases h : n < 10
    · simp [h, lengthOf, hd n h]
    · simp only [h, ↓reduceIte]
      rw [lengthOf_snoc, ih (n / 10) (by omega), hd (n % 10) (Nat.mod_lt _ (by decide))]
      omega

theorem colon_not_mem_toDigits (n : Nat) : ':' ∉ Nat.toDigits 10 n := fun h => by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  simp at this

/-- `texts` reads back the texts that `packTexts` packs. -/
theorem texts_packTexts (ts : List String) : texts ts.length (packTexts ts) = some ts := by
  induction ts with
  | nil => simp [texts, packTexts]
  | cons t ts ih =>
    cases ts with
    | nil => simp [texts, packTexts]
    | cons t' ts =>
      simp only [List.length_cons, packTexts] at ih ⊢
      rw [texts, splitAt_append _ (colon_not_mem_toDigits _)]
      simp only [lengthOf_toDigits, List.length_append, Nat.le_add_right, and_self, ↓reduceIte,
        List.drop_left', List.take_left']
      simp [ih]

theorem kindOf_ne_lf (lexeme : Lexeme) : kindOf lexeme ≠ '\n' := by
  cases lexeme with
  | bool b => cases b <;> decide
  | _ => simp [kindOf]

theorem isKind_kindOf (lexeme : Lexeme) : isKind (kindOf lexeme) = true := by
  cases lexeme with
  | bool b => cases b <;> decide
  | _ => simp [kindOf, isKind]

theorem countP_kinds (lexemes : List Lexeme) :
    (lexemes.map kindOf).countP hasText = (lexemes.filterMap textOf).length := by
  induction lexemes with
  | nil => rfl
  | cons l ls ih =>
    cases l with
    | bool b => cases b <;> simp [kindOf, textOf, hasText, List.filterMap_cons, ih]
    | _ => simp [kindOf, textOf, hasText, List.filterMap_cons, ih]

/-- The packed text of a list of tokens is read back as that list. -/
theorem unpack_pack (lexemes : List Lexeme) : unpack (pack lexemes) = some lexemes := by
  have hlf : '\n' ∉ lexemes.map kindOf := by
    intro h
    obtain ⟨l, _, hl⟩ := List.mem_map.mp h
    exact kindOf_ne_lf l hl
  have hk : (lexemes.map kindOf).all isKind = true := by
    simp [List.all_eq_true, isKind_kindOf]
  simp only [unpack, pack, String.toList_ofList, splitAt_append _ hlf, hk, ↓reduceIte, countP_kinds,
    texts_packTexts, zip_encode]

theorem texts_some (count : Nat) :
    ∀ {cs : List Char} {ts : List String}, texts count cs = some ts →
      cs = packTexts ts ∧ ts.length = count := by
  induction count with
  | zero =>
    intro cs ts h
    unfold texts at h
    split at h
    · cases h
      rename_i he
      exact ⟨by simpa [packTexts] using he, rfl⟩
    · cases h
  | succ n ih =>
    intro cs ts h
    cases n with
    | zero =>
      unfold texts at h
      cases h
      simp [packTexts]
    | succ m =>
      unfold texts at h
      split at h
      · cases h
      · rename_i digits rest hs
        simp only at h
        split at h
        · rename_i hc
          split at h
          · rename_i ts' ht
            cases h
            obtain ⟨h1, h2⟩ := ih ht
            have hsplit := splitAt_some hs
            cases ts' with
            | nil => simp at h2
            | cons t' ts'' =>
              refine ⟨?_, by simp [h2]⟩
              rw [packTexts, String.toList_ofList, List.length_take, Nat.min_eq_left hc.2, ← hc.1, ← h1,
                List.take_append_drop, hsplit]
          · cases h
        · cases h

theorem zip_kinds (kinds : List Char) :
    ∀ ts : List String, kinds.all isKind = true → ts.length = kinds.countP hasText →
      (zip kinds ts).map kindOf = kinds ∧ (zip kinds ts).filterMap textOf = ts := by
  induction kinds with
  | nil =>
    intro ts _ hl
    cases ts with
    | nil => exact ⟨rfl, rfl⟩
    | cons t ts => simp at hl
  | cons c cs ih =>
    intro ts hk hl
    simp only [List.all_cons, Bool.and_eq_true] at hk
    obtain ⟨hc, hcs⟩ := hk
    simp only [isKind, Bool.or_eq_true, decide_eq_true_eq] at hc
    rcases hc with ((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h <;> subst h
    all_goals first
      | (have := ih ts hcs (by simpa [hasText] using hl)
         simp [zip, kindOf, textOf, List.filterMap_cons, this.1, this.2]; done)
      | (cases ts with
         | nil => simp [hasText] at hl
         | cons t ts =>
           have := ih ts hcs (by simpa [hasText] using hl)
           simp [zip, kindOf, textOf, this.1, this.2])

/-- A text that `unpack` gives tokens for is the packed text of those tokens. -/
theorem unpack_some {packed : String} {lexemes : List Lexeme} (h : unpack packed = some lexemes) :
    packed = pack lexemes := by
  unfold unpack at h
  split at h
  · cases h
  · rename_i kinds rest hs
    split at h
    · rename_i hk
      split at h
      · rename_i ts ht
        cases h
        obtain ⟨h1, h2⟩ := texts_some _ ht
        obtain ⟨z1, z2⟩ := zip_kinds kinds ts hk h2
        rw [pack, z1, z2, ← h1, ← splitAt_some hs, String.ofList_toList]
      · cases h
    · cases h

/-- `unpack` gives the tokens `lexemes` exactly for the packed text of `lexemes`. -/
theorem unpack_iff (packed : String) (lexemes : List Lexeme) :
    unpack packed = some lexemes ↔ packed = pack lexemes :=
  ⟨unpack_some, fun h => h ▸ unpack_pack lexemes⟩

/-- A text for which `unpack` gives tokens is the packed text of those tokens. -/
theorem unpack_spec (packed : String) :
    match unpack packed with
    | some lexemes => packed = pack lexemes
    | none => True := by
  cases h : unpack packed with
  | none => trivial
  | some lexemes => exact unpack_some h

/-- The tokens of an object with the given members. -/
def objectLexemes (ms : List (String × Lexeme)) : List Lexeme :=
  .objOpen :: (ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose])

/-- The members with the values of their tokens, when each is a value by itself. -/
def scalars : List (String × Lexeme) → Option (List (String × Scalar))
  | [] => some []
  | (k, v) :: rest =>
    match scalarOf v, scalars rest with
    | some x, some xs => some ((k, x) :: xs)
    | _, _ => none

theorem members_object (ms : List (String × Lexeme)) (acc : List (String × Scalar)) :
    members acc (ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose]) =
      (scalars ms).map (acc.reverse ++ ·) := by
  induction ms generalizing acc with
  | nil => simp [members, scalars]
  | cons m ms ih =>
    obtain ⟨k, v⟩ := m
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    cases hms : ms.flatMap (fun m => [Lexeme.key m.1, m.2]) ++ [Lexeme.objClose] with
    | nil => simp at hms
    | cons i rest =>
      rw [members, scalar_spec]
      cases hv : scalarOf v with
      | none => simp [scalars, hv]
      | some x =>
        have := ih ((k, x) :: acc)
        rw [hms] at this
        simp only [this, scalars, hv]
        cases scalars ms <;> simp

/-- The tokens of an object give its members with the values of their tokens. -/
theorem object_objectLexemes (ms : List (String × Lexeme)) : object (objectLexemes ms) = scalars ms := by
  simp [object, objectLexemes, members_object]

theorem members_some {acc : List (String × Scalar)} {rest : List Lexeme}
    {xs : List (String × Scalar)} (h : members acc rest = some xs) :
    ∃ ms xs', scalars ms = some xs' ∧ xs = acc.reverse ++ xs' ∧
      rest = ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose] := by
  induction acc, rest using members.induct with
  | case1 acc =>
    simp only [members, Option.some.injEq] at h
    exact ⟨[], [], rfl, by simp [h], rfl⟩
  | case2 acc k v rest x hv ih =>
    simp only [members, hv] at h
    obtain ⟨ms, xs', h1, rfl, rfl⟩ := ih h
    rw [scalar_spec] at hv
    exact ⟨(k, v) :: ms, (k, x) :: xs', by simp [scalars, hv, h1], by simp, by simp⟩
  | case3 acc k v rest hv =>
    simp [members, hv] at h
  | case4 acc rest h1 h2 =>
    unfold members at h
    split at h
    · exact absurd rfl h1
    · exact absurd rfl (h2 _ _ _)
    · cases h

/-- Tokens for which `object` gives members are the tokens of an object: an opening brace, then
names with one token each, then one closing brace. -/
theorem object_shape (lexemes : List Lexeme) :
    match object lexemes with
    | some xs =>
      lexemes.head? = some .objOpen ∧ lexemes.getLast? = some .objClose ∧
        lexemes.length = 2 * xs.length + 2
    | none => True := by
  cases h : object lexemes with
  | none => trivial
  | some xs =>
    unfold object at h
    split at h
    · obtain ⟨ms, xs', h1, h2, h3⟩ := members_some h
      simp only [List.reverse_nil, List.nil_append] at h2
      subst h2 h3
      have hl : ∀ (ms : List (String × Lexeme)) xs, scalars ms = some xs → ms.length = xs.length := by
        intro ms
        induction ms with
        | nil => intro xs h; cases h; rfl
        | cons m ms ih =>
          intro xs h
          obtain ⟨k, v⟩ := m
          unfold scalars at h
          split at h
          · cases h
            simp [ih _ ‹_›]
          · cases h
      have hf : ∀ ms : List (String × Lexeme),
          (ms.flatMap fun m => [Lexeme.key m.1, m.2]).length = 2 * ms.length := by
        intro ms
        induction ms with
        | nil => rfl
        | cons m ms ih => simp [ih]; omega
      have h4 := hl ms xs h1
      have h5 := hf ms
      refine ⟨rfl, ?_, ?_⟩
      · simp [List.getLast?_cons, List.getLast?_append]
      · simp only [List.length_cons, List.length_append, List.length_nil, h5, h4]
    · cases h

/-- `object` gives members exactly for the tokens of an object whose values are values by
themselves. -/
theorem object_iff (lexemes : List Lexeme) (xs : List (String × Scalar)) :
    object lexemes = some xs ↔ ∃ ms, lexemes = objectLexemes ms ∧ scalars ms = some xs := by
  constructor
  · intro h
    unfold object at h
    split at h
    · obtain ⟨ms, xs', h1, rfl, rfl⟩ := members_some h
      exact ⟨ms, rfl, by simpa using h1⟩
    · cases h
  · rintro ⟨ms, rfl, h⟩
    rw [object_objectLexemes, h]

end Leangage.Json.Lexemes
