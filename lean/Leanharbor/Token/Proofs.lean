import Leanharbor.Token

/-!
# What the token functions guarantee

Based on `crates/h5i-app-token/proofs/TokenSpec.lean` of h5i (https://github.com/h5i-dev/h5i,
commit 515c7b9, Apache-2.0). Changed: the statements are about the generated functions over
`List UInt8` and `UInt64`, so the bounds of the fields are their types, and the facts about
decimals are proved without Mathlib.

- `parse_join`: parsing the token that `join` makes of `encodePayload t u e` and a signature
  gives back `t`, `u`, `e`, that payload and that signature.
- `parse_sound`, `parse_canon`: a token that `parse` accepts is `join` of its payload and its
  signature, and the payload is `encodePayload` of its fields. So `parse` accepts one spelling of
  each token: no leading zero, no sign, no uppercase hexadecimal, no other version.
- `encodePayload_injective`: a payload determines the tenant, the user and the expiry, so a
  signature over it binds one reading.

- `parseString_spec`: `parseString`, which the shells call, reads a `String` and gives what
  `parse` gives for its bytes. `parseString_sound`, `parseString_canon` and `parseString_join`
  restate `parse_sound`, `parse_canon` and `parse_join` for it.

`splitDot_spec`, `digitsValue_spec`, `hexDigit_spec`, `hexValue_spec`, `join_spec`, the facts
about `decimal`, and `number_decimal`, `number_sound`, `unhex_hex` and `unhex_sound` restate the
generated functions in other terms, as `splitDot_dotFrom`, `digitsFrom_spec`, `isDecimal_spec`,
`numberAt_spec`, `hexNibble_toNat`, `unhexAt_spec`, `copyBytes_spec` and `byteAt_of_lt` do for the
functions over strings.
-/

namespace Leanharbor.Token

/-- The lowercase hexadecimal digits in ASCII. -/
def hexChars : List UInt8 := [48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 97, 98, 99, 100, 101, 102]

/-- The number that ASCII digits spell, most significant first. -/
def value (l : List UInt8) : Nat :=
  (l.map (·.toNat - 48)).foldl (fun a d => a * 10 + d) 0

theorem toNat_toUInt8 {n : Nat} (h : n < 256) : n.toUInt8.toNat = n := by
  simp; omega

/-! ## The pieces, restated -/

theorem digitsValue_spec (l : List UInt8) : digitsValue l = value l := by
  simp [digitsValue, value, List.foldl_map]

theorem hexDigit_spec (n : Nat) (h : n < 16) : hexDigit n = hexChars.getD n 0 := by
  revert n
  decide

theorem hexValue_spec (c : UInt8) : hexValue c = hexChars.idxOf c := by
  have h : ∀ n, n < 256 → hexValue n.toUInt8 = hexChars.idxOf n.toUInt8 := by decide +kernel
  simpa using h c.toNat c.toNat_lt

theorem join_spec (payload sig : List UInt8) :
    join payload sig =
      payload ++ 46 :: sig.flatMap (fun b => [hexChars.getD (b.toNat / 16) 0, hexChars.getD (b.toNat % 16) 0]) := by
  have h : hexByte = fun b => [hexChars.getD (b.toNat / 16) 0, hexChars.getD (b.toNat % 16) 0] := by
    funext b
    rw [hexByte, hexDigit_spec _ (by have := b.toNat_lt; omega), hexDigit_spec _ (by omega)]
  rw [join, h]

theorem splitDot_spec (acc l : List UInt8) :
    splitDot acc l =
      (acc.reverse ++ l.takeWhile (· != 46), if 46 ∈ l then some (l.dropWhile (· != 46)).tail else none) := by
  induction l generalizing acc with
  | nil => simp [splitDot]
  | cons c rest ih =>
    by_cases hc : c = 46
    · subst hc
      simp [splitDot]
    · simp [splitDot, hc, ih, Ne.symm hc]

/-! ## Decimal -/

theorem decimal_lt {n : Nat} (h : n < 10) : decimal n = [(n + 48).toUInt8] := by
  rw [decimal]
  simp [h]

theorem decimal_ge {n : Nat} (h : ¬n < 10) :
    decimal n = decimal (n / 10) ++ [(n % 10 + 48).toUInt8] := by
  rw [decimal]
  simp [h]

theorem decimal_digit (n : Nat) : ∀ c ∈ decimal n, 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  induction n using decimal.induct with
  | case1 n h =>
    rw [decimal_lt h]
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    rw [toNat_toUInt8 (by omega)]
    omega
  | case2 n h ih =>
    rw [decimal_ge h]
    intro c hc
    simp only [List.mem_append, List.mem_singleton] at hc
    rcases hc with hc | rfl
    · exact ih c hc
    · rw [toNat_toUInt8 (by omega)]
      omega

theorem dot_not_mem_decimal (n : Nat) : 46 ∉ decimal n := fun h => by
  have := decimal_digit n 46 h
  simp at this

theorem decimal_ne_nil (n : Nat) : decimal n ≠ [] := by
  by_cases h : n < 10
  · simp [decimal_lt h]
  · simp [decimal_ge h]

theorem value_append (l : List UInt8) (c : UInt8) :
    value (l ++ [c]) = value l * 10 + (c.toNat - 48) := by
  simp [value, List.foldl_append]

theorem value_decimal (n : Nat) : value (decimal n) = n := by
  induction n using decimal.induct with
  | case1 n h =>
    rw [decimal_lt h]
    simp only [value, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [toNat_toUInt8 (by omega)]
    omega
  | case2 n h ih =>
    rw [decimal_ge h, value_append, ih, toNat_toUInt8 (by omega)]
    omega

theorem decimal_head (n : Nat) : (decimal n).head? = some 48 → n = 0 := by
  induction n using decimal.induct with
  | case1 n h =>
    rw [decimal_lt h]
    intro hh
    have := congrArg UInt8.toNat (Option.some.inj hh)
    rw [toNat_toUInt8 (by omega)] at this
    simp at this
    omega
  | case2 n h ih =>
    rw [decimal_ge h]
    intro hh
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (decimal_ne_nil (n / 10))
    rw [hcs] at hh ih
    simp only [List.cons_append, List.head?_cons] at hh ih
    have := ih hh
    omega

theorem decimal_length (n k : Nat) (h : n < 10 ^ (k + 1)) : (decimal n).length ≤ k + 1 := by
  induction n using decimal.induct generalizing k with
  | case1 n hn =>
    rw [decimal_lt hn]
    simp
  | case2 n hn ih =>
    rw [decimal_ge hn]
    cases k with
    | zero => simp at h; omega
    | succ k =>
      have hp : 10 ^ (k + 1 + 1) = 10 ^ (k + 1) * 10 := by rw [Nat.pow_succ]
      have := ih k (by omega)
      simp
      omega

theorem decimal_length_uint64 (x : UInt64) : (decimal x.toNat).length ≤ 20 :=
  decimal_length x.toNat 19 (by have := x.toNat_lt; omega)

/-- A field accepted as a number is the decimal of that number. -/
theorem number_sound (l : List UInt8) :
    match number l with
    | some x => l = decimal x.toNat
    | none => True := by
  unfold number
  split
  · rename_i x h
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      cases h
      exact hc.2.symm
    · cases h
  · trivial

theorem number_canon {l : List UInt8} {x : UInt64} (h : number l = some x) : l = decimal x.toNat := by
  have := number_sound l
  rw [h] at this
  exact this

theorem number_decimal (x : UInt64) : number (decimal x.toNat) = some x := by
  have hv : (digitsValue (decimal x.toNat)).toUInt64 = x := by
    rw [digitsValue_spec, value_decimal]
    simp
  simp [number, hv, decimal_length_uint64]

/-! ## Hexadecimal -/

theorem hexValue_hexDigit (n : Nat) (h : n < 16) : hexValue (hexDigit n) = n := by
  revert n
  decide

theorem hexDigit_hexValue (c : UInt8) (h : hexValue c < 16) : hexDigit (hexValue c) = c := by
  have k : ∀ n, n < 256 → hexValue n.toUInt8 < 16 → hexDigit (hexValue n.toUInt8) = n.toUInt8 := by
    decide +kernel
  simpa using k c.toNat c.toNat_lt (by simpa using h)

theorem dot_not_mem_hexByte (b : UInt8) : 46 ∉ hexByte b := by
  have k : ∀ n, n < 256 → 46 ∉ hexByte n.toUInt8 := by decide +kernel
  simpa using k b.toNat b.toNat_lt

theorem dot_not_mem_hex (sig : List UInt8) : 46 ∉ sig.flatMap hexByte := by
  simp only [List.mem_flatMap, not_exists, not_and]
  intro b _
  exact dot_not_mem_hexByte b

theorem unhex_hexByte (acc rest : List UInt8) (b : UInt8) :
    unhex acc (hexByte b ++ rest) = unhex (b :: acc) rest := by
  have hb := b.toNat_lt
  have h1 := hexValue_hexDigit (b.toNat / 16) (by omega)
  have h2 := hexValue_hexDigit (b.toNat % 16) (by omega)
  have hv : (b.toNat / 16 * 16 + b.toNat % 16).toUInt8 = b := by
    rw [show b.toNat / 16 * 16 + b.toNat % 16 = b.toNat by omega]
    simp
  simp only [hexByte, List.cons_append, List.nil_append, unhex, h1, h2, hv]
  simp [show b.toNat / 16 < 16 by omega, show b.toNat % 16 < 16 by omega]

theorem unhex_hex (acc sig : List UInt8) : unhex acc (sig.flatMap hexByte) = some (acc.reverse ++ sig) := by
  induction sig generalizing acc with
  | nil => simp [unhex]
  | cons b sig ih => simp [List.flatMap_cons, unhex_hexByte, ih]

theorem unhex_some {acc l s : List UInt8} (h : unhex acc l = some s) :
    ∃ sig, s = acc.reverse ++ sig ∧ l = sig.flatMap hexByte := by
  induction acc, l using unhex.induct with
  | case1 acc =>
    simp only [unhex, Option.some.injEq] at h
    exact ⟨[], by simp [h], rfl⟩
  | case2 acc c => simp [unhex] at h
  | case3 acc a b rest hab ih =>
    simp only [unhex, hab, ↓reduceIte] at h
    obtain ⟨sig, hs, hr⟩ := ih h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hab
    let x : UInt8 := (hexValue a * 16 + hexValue b).toUInt8
    have hx : x.toNat = hexValue a * 16 + hexValue b := toNat_toUInt8 (by omega)
    have hxa : hexDigit (x.toNat / 16) = a := by
      rw [hx, show (hexValue a * 16 + hexValue b) / 16 = hexValue a by omega, hexDigit_hexValue a hab.1]
    have hxb : hexDigit (x.toNat % 16) = b := by
      rw [hx, show (hexValue a * 16 + hexValue b) % 16 = hexValue b by omega, hexDigit_hexValue b hab.2]
    refine ⟨x :: sig, by simp [hs, x], ?_⟩
    simp [List.flatMap_cons, hexByte, hxa, hxb, hr]
  | case4 acc a b rest hab =>
    simp [unhex, hab] at h

/-- Accepted hexadecimal is the lowercase hexadecimal of the bytes it reads as. -/
theorem unhex_sound (acc l : List UInt8) :
    match unhex acc l with
    | some s => s = acc.reverse ++ s.drop acc.length ∧ l = (s.drop acc.length).flatMap hexByte
    | none => True := by
  cases h : unhex acc l with
  | none => trivial
  | some s =>
    obtain ⟨sig, rfl, rfl⟩ := unhex_some h
    simp

/-! ## Splitting at dots -/

theorem splitDot_dot (acc : List UInt8) {f : List UInt8} (r : List UInt8) (hf : 46 ∉ f) :
    splitDot acc (f ++ 46 :: r) = (acc.reverse ++ f, some r) := by
  induction f generalizing acc with
  | nil => simp [splitDot]
  | cons c f ih =>
    simp only [List.mem_cons, not_or] at hf
    simp [splitDot, Ne.symm hf.1, ih _ hf.2]

theorem splitDot_nodot (acc : List UInt8) {f : List UInt8} (hf : 46 ∉ f) :
    splitDot acc f = (acc.reverse ++ f, none) := by
  induction f generalizing acc with
  | nil => simp [splitDot]
  | cons c f ih =>
    simp only [List.mem_cons, not_or] at hf
    simp [splitDot, Ne.symm hf.1, ih _ hf.2]

theorem splitDot_some {acc l g r : List UInt8} (h : splitDot acc l = (g, some r)) :
    ∃ f, 46 ∉ f ∧ g = acc.reverse ++ f ∧ l = f ++ 46 :: r := by
  induction l generalizing acc with
  | nil => simp [splitDot] at h
  | cons c l ih =>
    by_cases hc : c = 46
    · subst hc
      simp only [splitDot, ↓reduceIte, Prod.mk.injEq, Option.some.injEq] at h
      exact ⟨[], by simp, by simp [h.1], by simp [h.2]⟩
    · simp only [splitDot, hc, ↓reduceIte] at h
      obtain ⟨f, hf, hg, hl⟩ := ih h
      exact ⟨c :: f, by simp [hf, Ne.symm hc], by simp [hg], by simp [hl]⟩

theorem splitDot_none {acc l g : List UInt8} (h : splitDot acc l = (g, none)) :
    46 ∉ l ∧ g = acc.reverse ++ l := by
  induction l generalizing acc with
  | nil => simp [splitDot] at h; simp [h]
  | cons c l ih =>
    by_cases hc : c = 46
    · subst hc
      simp [splitDot] at h
    · simp only [splitDot, hc, ↓reduceIte] at h
      obtain ⟨hl, hg⟩ := ih h
      exact ⟨by simp [hl, Ne.symm hc], by simp [hg]⟩

/-! ## Tokens -/

/-- Parsing an issued token gives back exactly what was signed. -/
theorem parse_join (t u e : UInt64) (sig : List UInt8) :
    parse (join (encodePayload t u e) sig) = some ⟨t, u, e, encodePayload t u e, sig⟩ := by
  have e1 : join (encodePayload t u e) sig = [118, 49] ++ 46 ::
      (decimal t.toNat ++ 46 :: (decimal u.toNat ++ 46 :: (decimal e.toNat ++ 46 :: sig.flatMap hexByte))) := by
    simp [join, encodePayload]
  unfold parse
  simp only [e1, splitDot_dot [] _ (by simp : (46 : UInt8) ∉ [118, 49]),
    splitDot_dot [] _ (dot_not_mem_decimal t.toNat), splitDot_dot [] _ (dot_not_mem_decimal u.toNat),
    splitDot_dot [] _ (dot_not_mem_decimal e.toNat), splitDot_nodot [] (dot_not_mem_hex sig),
    List.reverse_nil, List.nil_append, ↓reduceIte, number_decimal, unhex_hex]
  simp [encodePayload]

/-- A token that `parse` accepts is `join` of its payload and its signature, and the payload is
`encodePayload` of its fields. -/
theorem parse_sound (l : List UInt8) :
    match parse l with
    | some p => p.payload = encodePayload p.tenant p.user p.exp ∧ l = join p.payload p.sig
    | none => True := by
  cases h : parse l with
  | none => trivial
  | some p =>
    simp only
    unfold parse at h
    split at h <;> try (simp at h; done)
    rename_i f0 r0 h0
    split at h <;> try (simp at h; done)
    rename_i f1 r1 h1
    split at h <;> try (simp at h; done)
    rename_i f2 r2 h2
    split at h <;> try (simp at h; done)
    rename_i f3 r3 h3
    split at h <;> try (simp at h; done)
    rename_i f4 h4
    split at h <;> try (simp at h; done)
    rename_i hv
    split at h <;> try (simp at h; done)
    rename_i t u e sig ht hu he hs
    cases h
    obtain ⟨_, _, hg0, rfl⟩ := splitDot_some h0
    obtain ⟨_, _, hg1, rfl⟩ := splitDot_some h1
    obtain ⟨_, _, hg2, rfl⟩ := splitDot_some h2
    obtain ⟨_, _, hg3, rfl⟩ := splitDot_some h3
    obtain ⟨_, hg4⟩ := splitDot_none h4
    simp only [List.reverse_nil, List.nil_append] at hg0 hg1 hg2 hg3 hg4
    subst hg0 hg1 hg2 hg3 hg4 hv
    obtain ⟨sig', hs', rfl⟩ := unhex_some hs
    simp only [List.reverse_nil, List.nil_append] at hs'
    subst hs'
    rw [number_canon ht, number_canon hu, number_canon he]
    simp [encodePayload, join]

theorem parse_canon {l : List UInt8} {p : Parsed} (h : parse l = some p) :
    p.payload = encodePayload p.tenant p.user p.exp ∧ l = join p.payload p.sig := by
  have := parse_sound l
  rw [h] at this
  exact this

/-- Different fields give different payloads, so a signature binds one reading. -/
theorem encodePayload_injective {t u e t' u' e' : UInt64}
    (h : encodePayload t u e = encodePayload t' u' e') : t = t' ∧ u = u' ∧ e = e' := by
  have h1 := parse_join t u e []
  rw [h, parse_join] at h1
  simp only [Option.some.injEq, Parsed.mk.injEq] at h1
  exact ⟨h1.1.symm, h1.2.1.symm, h1.2.2.1.symm⟩

/-! ## Over the bytes of a string -/

/-- The bytes of a string. -/
def bytesOf (s : String) : List UInt8 := s.toByteArray.data.toList

/-- The bytes of `l` from `i` to `j`. -/
def slice (l : List UInt8) (i j : Nat) : List UInt8 := (l.drop i).take (j - i)

/-- `ParsedArray` with lists. -/
def ParsedArray.toParsed (p : ParsedArray) : Parsed :=
  ⟨p.tenant, p.user, p.exp, p.payload.toList, p.sig.toList⟩

theorem length_bytesOf (s : String) : (bytesOf s).length = s.utf8ByteSize := by
  simp only [bytesOf, Array.length_toList]
  rfl

theorem byteAt_of_lt {s : String} {i : Nat} (h : i < (bytesOf s).length) :
    byteAt s i = (bytesOf s)[i] := by
  have h' : i < s.utf8ByteSize := length_bytesOf s ▸ h
  simp [byteAt, h', String.getUTF8Byte_eq_getElem, ByteArray.getElem_eq_getElem_data, bytesOf]

/-- `byteAt` reads the bytes of the string, and 0 past them. -/
theorem byteAt_spec (s : String) (i : Nat) : byteAt s i = (bytesOf s).getD i 0 := by
  by_cases h : i < (bytesOf s).length
  · rw [byteAt_of_lt h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
    rfl
  · have h' : ¬i < s.utf8ByteSize := length_bytesOf s ▸ h
    rw [byteAt, dite_eq_right h', List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

theorem getUTF8Byte_eq {s : String} {i : Nat} (h : i < s.utf8ByteSize) :
    s.getUTF8Byte ⟨i⟩ h = (bytesOf s)[i]'(length_bytesOf s ▸ h) := by
  simp [String.getUTF8Byte_eq_getElem, ByteArray.getElem_eq_getElem_data, bytesOf]

theorem slice_self (l : List UInt8) (i : Nat) : slice l i i = [] := by
  simp [slice]

theorem slice_of_le {l : List UInt8} {i j : Nat} (h : j ≤ i) : slice l i j = [] := by
  simp [slice, show j - i = 0 by omega]

theorem slice_cons {l : List UInt8} {i j : Nat} (hij : i < j) (hj : j ≤ l.length) :
    slice l i j = l[i]'(by omega) :: slice l (i + 1) j := by
  simp only [slice]
  rw [List.drop_eq_getElem_cons (by omega), show j - i = (j - (i + 1)) + 1 by omega,
    List.take_succ_cons]

theorem slice_snoc {l : List UInt8} {i j : Nat} (hij : i < j) (hj : j ≤ l.length) :
    slice l i j = slice l i (j - 1) ++ [l[j - 1]'(by omega)] := by
  simp only [slice]
  rw [show j - i = (j - 1 - i) + 1 by omega, List.take_add_one]
  simp [List.getElem?_drop, show i + (j - 1 - i) = j - 1 by omega, List.getElem?_eq_getElem (show j - 1 < l.length by omega)]

theorem length_slice {l : List UInt8} {i j : Nat} (hj : j ≤ l.length) :
    (slice l i j).length = j - i := by
  simp [slice]; omega

theorem dotFrom_le (s : String) (i : Nat) : dotFrom s i ≤ s.utf8ByteSize := by
  induction i using dotFrom.induct s with
  | case1 i h hb => rw [dotFrom]; simp [h, hb]; omega
  | case2 i h hb ih => rw [dotFrom]; simp [h, hb, ih]
  | case3 i h => rw [dotFrom]; simp [h]

theorem le_dotFrom (s : String) {i : Nat} (hi : i ≤ s.utf8ByteSize) : i ≤ dotFrom s i := by
  induction i using dotFrom.induct s with
  | case1 i h hb => rw [dotFrom]; simp [h, hb]
  | case2 i h hb ih => rw [dotFrom]; simp [h, hb]; have := ih (by omega); omega
  | case3 i h => rw [dotFrom]; simp [h]; omega

/-- `dotFrom` finds the dot that `splitDot` stops at. -/
theorem splitDot_dotFrom (s : String) (acc : List UInt8) {i : Nat} (hi : i ≤ s.utf8ByteSize) :
    splitDot acc ((bytesOf s).drop i) =
      (acc.reverse ++ slice (bytesOf s) i (dotFrom s i),
        if dotFrom s i < s.utf8ByteSize then some ((bytesOf s).drop (dotFrom s i + 1)) else none) := by
  induction i using dotFrom.induct s generalizing acc with
  | case1 i h hb =>
    rw [dotFrom]
    simp only [h, hb, dite_true, ite_true]
    rw [List.drop_eq_getElem_cons (by rw [length_bytesOf]; exact h), splitDot]
    rw [getUTF8Byte_eq] at hb
    simp [hb, slice_self]
  | case2 i h hb ih =>
    have hk := le_dotFrom s (show i + 1 ≤ s.utf8ByteSize by omega)
    have hl := length_bytesOf s
    rw [dotFrom]
    simp only [h, hb, dite_true, ite_false]
    rw [List.drop_eq_getElem_cons (by omega), splitDot]
    rw [getUTF8Byte_eq] at hb
    simp only [hb, ite_false, ih _ (by omega)]
    rw [slice_cons (show i < dotFrom s (i + 1) by omega) (by rw [hl]; exact dotFrom_le s _)]
    simp
  | case3 i h =>
    have hi' : i = s.utf8ByteSize := by omega
    subst hi'
    have hd : (bytesOf s).drop s.utf8ByteSize = [] := by
      rw [← length_bytesOf, List.drop_length]
    rw [dotFrom, hd]
    simp [splitDot, slice_self]

theorem digitsFrom_spec (s : String) {i j : Nat} (acc : Nat) (hj : j ≤ s.utf8ByteSize) :
    digitsFrom s i j acc =
      (slice (bytesOf s) i j).foldl (fun acc c => acc * 10 + (c.toNat - 48)) acc := by
  induction i, acc using digitsFrom.induct s j with
  | case1 i acc h ih =>
    have hl := length_bytesOf s
    rw [digitsFrom, ite_eq_left h, ih, slice_cons h.1 (by omega), List.foldl_cons,
      byteAt_of_lt (by omega)]
  | case2 i acc h =>
    rw [digitsFrom, ite_eq_right h, slice_of_le (by omega)]
    rfl

theorem isDecimal_spec (n : Nat) (s : String) {i j : Nat} (hj : j ≤ s.utf8ByteSize) :
    isDecimal n s i j = true ↔ decimal n = slice (bytesOf s) i j := by
  have hl := length_bytesOf s
  induction n, j using isDecimal.induct i with
  | case1 n j h =>
    rw [isDecimal, ite_eq_left h, slice_of_le h]
    simp [decimal_ne_nil]
  | case2 n j h hn =>
    rw [isDecimal, ite_eq_right h, ite_eq_left hn, decimal_lt hn, slice_cons (by omega) (by omega),
      byteAt_of_lt (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.cons.injEq]
    constructor
    · rintro ⟨rfl, h2⟩
      exact ⟨h2.symm, (slice_self _ _).symm⟩
    · rintro ⟨h1, h2⟩
      have := length_slice (l := bytesOf s) (i := i + 1) (j := j) (by omega)
      rw [← h2] at this
      exact ⟨by simp at this; omega, h1.symm⟩
  | case3 n j h hn ih =>
    rw [isDecimal, ite_eq_right h, ite_eq_right hn, decimal_ge hn, slice_snoc (by omega) (by omega),
      byteAt_of_lt (by omega)]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    have ih' := ih (show j - 1 ≤ s.utf8ByteSize by omega)
    constructor
    · rintro ⟨h1, h2⟩
      rw [ih'.mp h2, h1]
    · intro h'
      obtain ⟨h1, h2⟩ := List.append_inj' h' rfl
      exact ⟨by simpa using h2.symm, ih'.mpr h1⟩

theorem numberAt_spec (s : String) {i j : Nat} (hj : j ≤ s.utf8ByteSize) :
    numberAt s i j = number (slice (bytesOf s) i j) := by
  have hl := length_bytesOf s
  have hd : digitsFrom s i j 0 = digitsValue (slice (bytesOf s) i j) := by
    rw [digitsFrom_spec s 0 hj]; rfl
  have hb : ∀ x : Nat, isDecimal x s i j = (decimal x == slice (bytesOf s) i j) := by
    intro x
    rw [Bool.eq_iff_iff, isDecimal_spec x s hj, beq_iff_eq]
  simp only [numberAt, number, hd, hb, length_slice (show j ≤ (bytesOf s).length by omega)]

/-- `isDecimal_spec` on the first field after the version, as `parseString` calls it. -/
theorem isDecimal_field (s : String) :
    isDecimal (digitsFrom s (dotFrom s 0 + 1) (dotFrom s (dotFrom s 0 + 1)) 0) s (dotFrom s 0 + 1)
        (dotFrom s (dotFrom s 0 + 1)) =
      (decimal (digitsFrom s (dotFrom s 0 + 1) (dotFrom s (dotFrom s 0 + 1)) 0) ==
        slice (bytesOf s) (dotFrom s 0 + 1) (dotFrom s (dotFrom s 0 + 1))) := by
  rw [Bool.eq_iff_iff, isDecimal_spec _ s (dotFrom_le s _), beq_iff_eq]

/-- `numberAt_spec` on the first field after the version, as `parseString` calls it. -/
theorem numberAt_field (s : String) :
    numberAt s (dotFrom s 0 + 1) (dotFrom s (dotFrom s 0 + 1)) =
      number (slice (bytesOf s) (dotFrom s 0 + 1) (dotFrom s (dotFrom s 0 + 1))) :=
  numberAt_spec s (dotFrom_le s _)

theorem hexNibble_toNat_all : ∀ n, n < 256 → (hexNibble n.toUInt8).toNat = hexValue n.toUInt8 := by
  set_option maxRecDepth 100000 in decide

theorem hexNibble_toNat (c : UInt8) : (hexNibble c).toNat = hexValue c := by
  simpa using hexNibble_toNat_all c.toNat c.toNat_lt

theorem hexNibble_lt (c : UInt8) : hexNibble c < 16 ↔ hexValue c < 16 := by
  rw [UInt8.lt_iff_toNat_lt, hexNibble_toNat]
  rfl

theorem hexNibble_pair {a b : UInt8} (ha : hexValue a < 16) (hb : hexValue b < 16) :
    hexNibble a * 16 + hexNibble b = (hexValue a * 16 + hexValue b).toUInt8 := by
  apply UInt8.toNat_inj.mp
  rw [toNat_toUInt8 (by omega), UInt8.toNat_add, UInt8.toNat_mul, hexNibble_toNat, hexNibble_toNat]
  simp
  omega

theorem unhexAt_spec (s : String) {i j : Nat} (acc : Array UInt8) (hj : j ≤ s.utf8ByteSize) :
    (unhexAt s i j acc).map Array.toList = unhex acc.toList.reverse (slice (bytesOf s) i j) := by
  have hl := length_bytesOf s
  induction i, acc using unhexAt.induct s j with
  | case1 i acc h1 h2 a b hab ih =>
    rw [unhexAt, ite_eq_left h1, ite_eq_left h2]
    simp only [a, b] at hab ih ⊢
    have hab' := hab
    simp only [Bool.and_eq_true, decide_eq_true_eq, hexNibble_lt] at hab'
    rw [byteAt_of_lt (by omega), byteAt_of_lt (by omega)] at hab'
    rw [ite_eq_left hab, ih, slice_cons h1 (by omega), slice_cons h2 (by omega), unhex,
      ite_eq_left (by simp [hab'.1, hab'.2]), byteAt_of_lt (by omega), byteAt_of_lt (by omega),
      hexNibble_pair hab'.1 hab'.2, Array.toList_push]
    simp
  | case2 i acc h1 h2 a b hab =>
    rw [unhexAt, ite_eq_left h1, ite_eq_left h2]
    simp only [a, b] at hab ⊢
    have hab' := hab
    simp only [Bool.and_eq_true, decide_eq_true_eq, hexNibble_lt] at hab'
    rw [byteAt_of_lt (by omega), byteAt_of_lt (by omega)] at hab'
    rw [ite_eq_right hab, slice_cons h1 (by omega), slice_cons h2 (by omega), unhex,
      ite_eq_right (by simpa using hab')]
    rfl
  | case3 i acc h1 h2 =>
    rw [unhexAt, ite_eq_left h1, ite_eq_right h2, slice_cons h1 (by omega), slice_of_le (by omega)]
    simp [unhex]
  | case4 i acc h1 =>
    rw [unhexAt, ite_eq_right h1, slice_of_le (by omega)]
    simp [unhex]

theorem copyBytes_spec (s : String) {i j : Nat} (acc : Array UInt8) (hj : j ≤ s.utf8ByteSize) :
    (copyBytes s i j acc).toList = acc.toList ++ slice (bytesOf s) i j := by
  have hl := length_bytesOf s
  induction i, acc using copyBytes.induct s j with
  | case1 i acc h ih =>
    rw [copyBytes, ite_eq_left h, ih, slice_cons h.1 (by omega), Array.toList_push,
      byteAt_of_lt (by omega)]
    simp
  | case2 i acc h =>
    rw [copyBytes, ite_eq_right h, slice_of_le (by omega)]
    simp

theorem dotFrom_dot (s : String) {i : Nat} (h : dotFrom s i < s.utf8ByteSize) :
    (bytesOf s)[dotFrom s i]'(by rw [length_bytesOf]; exact h) = 46 := by
  induction i using dotFrom.induct s with
  | case1 i hi hb =>
    have e : dotFrom s i = i := by rw [dotFrom]; simp [hi, hb]
    simp only [e] at h ⊢
    rw [getUTF8Byte_eq] at hb
    exact hb
  | case2 i hi hb ih =>
    have e : dotFrom s i = dotFrom s (i + 1) := by rw [dotFrom]; simp [hi, hb]
    simp only [e] at h ⊢
    exact ih h
  | case3 i hi =>
    have e : dotFrom s i = s.utf8ByteSize := by rw [dotFrom]; simp [hi]
    simp [e] at h

theorem slice_v1 (s : String) {d : Nat} (hd : d ≤ s.utf8ByteSize) :
    slice (bytesOf s) 0 d = [118, 49] ↔ (d = 2 ∧ byteAt s 0 = 118 ∧ byteAt s 1 = 49) := by
  have hl := length_bytesOf s
  constructor
  · intro h
    have hlen := length_slice (l := bytesOf s) (i := 0) (j := d) (by omega)
    rw [h] at hlen
    simp at hlen
    subst hlen
    rw [slice_cons (by omega) (by omega), slice_cons (by omega) (by omega)] at h
    simp only [List.cons.injEq] at h
    rw [byteAt_of_lt (by omega), byteAt_of_lt (by omega)]
    exact ⟨rfl, h.1, h.2.1⟩
  · rintro ⟨rfl, h0, h1⟩
    rw [byteAt_of_lt (by omega)] at h0
    rw [byteAt_of_lt (by omega)] at h1
    rw [slice_cons (by omega) (by omega), slice_cons (by omega) (by omega), slice_self, h0, h1]

theorem unhex_dot {acc l : List UInt8} (h : 46 ∈ l) : unhex acc l = none := by
  cases hu : unhex acc l with
  | none => rfl
  | some r =>
    obtain ⟨sig, _, rfl⟩ := unhex_some hu
    exact absurd h (dot_not_mem_hex sig)

theorem mem_slice {l : List UInt8} {i j k : Nat} (hik : i ≤ k) (hkj : k < j) (hj : j ≤ l.length) :
    l[k]'(by omega) ∈ slice l i j := by
  rw [slice, List.mem_iff_getElem]
  refine ⟨k - i, by simp; omega, ?_⟩
  simp only [List.getElem_take, List.getElem_drop]
  congr 1
  omega

theorem parseString_spec (s : String) : (parseString s).map ParsedArray.toParsed = parse (bytesOf s) := by
  have hl := length_bytesOf s
  have split (i : Nat) (hi : i ≤ s.utf8ByteSize) := splitDot_dotFrom s [] hi
  have e0 := split 0 (Nat.zero_le _)
  simp only [List.drop_zero, List.reverse_nil, List.nil_append] at e0
  unfold parseString parse
  dsimp only
  generalize hd0 : dotFrom s 0 = d0 at e0 ⊢
  have le0 : d0 ≤ s.utf8ByteSize := hd0 ▸ dotFrom_le s 0
  rw [e0]
  by_cases h0 : d0 < s.utf8ByteSize
  case neg => simp [h0]
  have e1 := split (d0 + 1) (by omega)
  simp only [List.reverse_nil, List.nil_append] at e1
  generalize hd1 : dotFrom s (d0 + 1) = d1 at e1 ⊢
  have le1 : d0 + 1 ≤ d1 := hd1 ▸ le_dotFrom s (by omega)
  simp only [h0, ite_true, e1]
  by_cases h1 : d1 < s.utf8ByteSize
  case neg => simp [h1]
  have e2 := split (d1 + 1) (by omega)
  simp only [List.reverse_nil, List.nil_append] at e2
  generalize hd2 : dotFrom s (d1 + 1) = d2 at e2 ⊢
  have le2 : d1 + 1 ≤ d2 := hd2 ▸ le_dotFrom s (by omega)
  simp only [h1, ite_true, e2]
  by_cases h2 : d2 < s.utf8ByteSize
  case neg => simp [h2]
  have e3 := split (d2 + 1) (by omega)
  simp only [List.reverse_nil, List.nil_append] at e3
  generalize hd3 : dotFrom s (d2 + 1) = d3 at e3 ⊢
  have le3 : d2 + 1 ≤ d3 := hd3 ▸ le_dotFrom s (by omega)
  simp only [h2, ite_true, e3]
  by_cases h3 : d3 < s.utf8ByteSize
  case neg => simp [h3]
  have e4 := split (d3 + 1) (by omega)
  simp only [List.reverse_nil, List.nil_append] at e4
  have hu := unhexAt_spec s (i := d3 + 1) (Array.emptyWithCapacity 32) (Nat.le_refl _)
  simp only [Array.emptyWithCapacity_eq, List.reverse_nil] at hu
  have le4 : d3 + 1 ≤ dotFrom s (d3 + 1) := le_dotFrom s (by omega)
  simp only [h3, ite_true, e4]
  by_cases h4 : dotFrom s (d3 + 1) < s.utf8ByteSize
  · have hnone : unhexAt s (d3 + 1) s.utf8ByteSize (Array.emptyWithCapacity 32) = none := by
      have hd := mem_slice (l := bytesOf s) le4 h4 (by omega)
      rw [dotFrom_dot s h4] at hd
      rw [unhex_dot hd] at hu
      simpa using hu
    simp only [h4, ite_true, Array.emptyWithCapacity_eq] at hnone ⊢
    simp only [decide_true, Bool.and_self, ite_true, hnone]
    split
    · split <;> simp_all
    · rfl
  have he4 : dotFrom s (d3 + 1) = s.utf8ByteSize := by have := dotFrom_le s (d3 + 1); omega
  simp only [ite_false, he4, Nat.lt_irrefl]
  simp only [slice_v1 s le0]
  simp only [decide_true, Bool.and_self, ite_true]
  by_cases hv : d0 = 2 ∧ byteAt s 0 = 118 ∧ byteAt s 1 = 49
  case neg =>
    have hv' : ¬((decide (d0 = 2) && decide (byteAt s 0 = 118) && decide (byteAt s 1 = 49)) = true) := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact fun ⟨⟨a, b⟩, c⟩ => hv ⟨a, b, c⟩
    simp only [ite_eq_right hv', ite_eq_right hv, Option.map_none]
  have hv' : (decide (d0 = 2) && decide (byteAt s 0 = 118) && decide (byteAt s 1 = 49)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hv.1, hv.2.1⟩, hv.2.2⟩
  simp only [ite_eq_left hv', ite_eq_left hv]
  rw [numberAt_spec s (by omega), numberAt_spec s (by omega), numberAt_spec s (by omega)]
  simp only [Array.emptyWithCapacity_eq] at hu ⊢
  have c0 := copyBytes_spec s (i := 0) #[] (show d0 ≤ s.utf8ByteSize by omega)
  have c1 := copyBytes_spec s (i := d0 + 1) ((copyBytes s 0 d0 #[]).push 46)
    (show d1 ≤ s.utf8ByteSize by omega)
  have c2 := copyBytes_spec s (i := d1 + 1)
    ((copyBytes s (d0 + 1) d1 ((copyBytes s 0 d0 #[]).push 46)).push 46) (show d2 ≤ s.utf8ByteSize by omega)
  have c3 := copyBytes_spec s (i := d2 + 1)
    ((copyBytes s (d1 + 1) d2 ((copyBytes s (d0 + 1) d1 ((copyBytes s 0 d0 #[]).push 46)).push 46)).push 46)
    (show d3 ≤ s.utf8ByteSize by omega)
  generalize number (slice (bytesOf s) (d0 + 1) d1) = n1
  generalize number (slice (bytesOf s) (d1 + 1) d2) = n2
  generalize number (slice (bytesOf s) (d2 + 1) d3) = n3
  cases hU : unhexAt s (d3 + 1) s.utf8ByteSize #[] with
  | none =>
    rw [hU] at hu
    simp only [Option.map_none] at hu
    rw [← hu]
    rcases n1 with _ | t <;> rcases n2 with _ | u <;> rcases n3 with _ | e <;> rfl
  | some sig =>
    rw [hU] at hu
    simp only [Option.map_some] at hu
    rw [← hu]
    rcases n1 with _ | t <;> rcases n2 with _ | u <;> rcases n3 with _ | e <;> try rfl
    simp only [Option.map_some, ParsedArray.toParsed, c3, Array.toList_push, c2, c1, c0]
    simp

/-- A token that `parseString` accepts is `join` of its payload and its signature, and the payload
is `encodePayload` of its fields. -/
theorem parseString_sound (s : String) :
    match parseString s with
    | some p => p.payload.toList = encodePayload p.tenant p.user p.exp ∧
        bytesOf s = join p.payload.toList p.sig.toList
    | none => True := by
  cases h : parseString s with
  | none => trivial
  | some p =>
    have hp := parseString_spec s
    rw [h, Option.map_some] at hp
    exact parse_canon hp.symm

theorem parseString_canon {s : String} {p : ParsedArray} (h : parseString s = some p) :
    p.payload.toList = encodePayload p.tenant p.user p.exp ∧
      bytesOf s = join p.payload.toList p.sig.toList := by
  have := parseString_sound s
  rw [h] at this
  exact this

/-- Parsing the string of an issued token gives back exactly what was signed. -/
theorem parseString_join {s : String} (t u e : UInt64) (sig : List UInt8)
    (h : bytesOf s = join (encodePayload t u e) sig) :
    parseString s = some ⟨t, u, e, (encodePayload t u e).toArray, sig.toArray⟩ := by
  have hp := parseString_spec s
  rw [h, parse_join] at hp
  cases hs : parseString s with
  | none => rw [hs] at hp; cases hp
  | some p =>
    rw [hs, Option.map_some, Option.some.injEq] at hp
    cases p
    simp only [ParsedArray.toParsed, Parsed.mk.injEq] at hp
    obtain ⟨rfl, rfl, rfl, hpl, hsl⟩ := hp
    rw [← hpl, ← hsl]

end Leanharbor.Token
