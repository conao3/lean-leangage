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

`splitDot_spec`, `digitsValue_spec`, `hexDigit_spec`, `hexValue_spec`, `join_spec`, the facts
about `decimal`, and `number_decimal`, `number_sound`, `unhex_hex` and `unhex_sound` restate the
generated functions in other terms.
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

end Leanharbor.Token
