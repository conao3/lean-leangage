import Calculator.Wire
import Calculator.Proofs
import Leangage.Http.Proofs
import Leangage.Json.Read.Proofs

/-!
# What the calculator's functions on the wire guarantee

- `decode_encode`: a body whose bytes are `Value.print` of `encodeCommand c`, the JSON value that
  spells the command `c`, decodes to `c`. So every command has a spelling the servers accept.
- `spelled_spec`: `spelled` gives the command `c` exactly for the bodies whose bytes are
  `Value.print` of `encodeCommand c` (`spelled_print` for each command), and `closedNumber_spec`
  says what its number is read from. `decode_text`: `decode`, which answers such a body from
  `spelled`, is `decodeText`, the decision of the JSON reader, on every body; so each theorem
  below about `decode` is one about what `readString` reads.
- `decode_ok_iff`, `decodeItems_ok_iff`, `decodeMembers_ok_iff`: a body decodes to `c` exactly
  when it reads as the items of an object with as many members as `c` has fields (`fields c`,
  the members of `encodeCommand c`) and with each field among them. The members may come in any
  order; an object with another member, a member twice or a member whose value is an array or an
  object is refused.
- `decode_notJson_iff`: `notJson` is the refusal of the bodies `readString` refuses, and of no
  other. `decodeMembers_missingCmd_iff`: `missingCmd` is the refusal of the objects without a
  member `cmd`. `decodeMembers_badValue_iff`, `decodeMembers_badArg_iff`: `badValue` is the
  refusal of the objects of 2 members with `"cmd":"set"` whose `value` is not a number below 2^64
  in decimal digits, and `badArg` that of the objects of 3 members with `"cmd":"apply"` and an
  `op` that names an operation whose `arg` is not such a number. Every other refused object gets
  `notCommand`. `refusalMessage_spec` gives the message of each refusal.
- `request_expired`, `request_text`, `request_not_text`: a request whose token has expired is
  answered 401 `token expired` whatever its body; otherwise a body of text gives the command it
  decodes to for the principal of the token's tenant and user (`request_actor`), or 400 with the
  message of the refusal, and a body that is not text is answered 400 or 413.
  `request_encode` states the accepted case for the spelling of a command, and
  `request_refusal` that every answer of `request` has the status 400, 401 or 413 and a body
  `{"error": message}`.
- `respond_ok`, `respond_error`: an accepted command is answered 200 with `Value.print` of
  `replyValue`, a refused one 422 with `Value.print` of `errorValue`.
- `fingerprint_spec`: the fingerprint of a command is the text `Set { value: 6 }`,
  `Apply { op: Mul, arg: 7 }` or `Get`. `fingerprint_injective`: different commands have
  different fingerprints, so an idempotency key used with another command is recognised.
- `scope_spec`, `scope_injective`: the scope of a principal is `u` and its user in decimal, and
  two principals have the same scope exactly when they have the same user.
-/

namespace Calculator.Wire

open Calculator.Kernel Leangage
open Leangage.Json (Value ascii)
open Leangage.Json.Read (Item readString readString_print)
open Leangage.Token (bytesOf)

/-! ## Commands -/

/-- The name of an operation on the wire. -/
def opName : Op → List Char
  | .add => ['a', 'd', 'd']
  | .sub => ['s', 'u', 'b']
  | .mul => ['m', 'u', 'l']
  | .div => ['d', 'i', 'v']

/-- The JSON value that spells a command: `{"cmd":"set","value":n}`,
`{"cmd":"apply","op":"<name>","arg":n}`, `{"cmd":"get"}`. -/
def encodeCommand : Command → Value
  | .set n => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['s', 'e', 't'])), (ascii ['v', 'a', 'l', 'u', 'e'], .num n)]
  | .apply op n =>
    .obj [(ascii ['c', 'm', 'd'], .str (ascii ['a', 'p', 'p', 'l', 'y'])), (ascii ['o', 'p'], .str (ascii (opName op))),
      (ascii ['a', 'r', 'g'], .num n)]
  | .get => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['g', 'e', 't']))]

/-- The members of the object that spells a command, as they are read. -/
def fields : Command → List (List UInt8 × Item)
  | .set n => [(ascii ['c', 'm', 'd'], .str (ascii ['s', 'e', 't'])), (ascii ['v', 'a', 'l', 'u', 'e'], .num n)]
  | .apply op n =>
    [(ascii ['c', 'm', 'd'], .str (ascii ['a', 'p', 'p', 'l', 'y'])), (ascii ['o', 'p'], .str (ascii (opName op))),
      (ascii ['a', 'r', 'g'], .num n)]
  | .get => [(ascii ['c', 'm', 'd'], .str (ascii ['g', 'e', 't']))]

/-- The items of an object with the given members. -/
def objectItems (ms : List (List UInt8 × Item)) : List Item :=
  .objOpen :: (ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose])

theorem encodeCommand_items (c : Command) :
    (encodeCommand c).toks.map Item.ofTok = objectItems (fields c) := by
  cases c <;> rfl

theorem decodeMembers_fields (c : Command) : decodeMembers (fields c) = .ok c := by
  cases c with
  | set n => rfl
  | apply op n => cases op <;> rfl
  | get => rfl

theorem decodeText_encode {s : String} (c : Command) (h : bytesOf s = (encodeCommand c).print) :
    decodeText s = .ok c := by
  rw [decodeText, readString_print h, encodeCommand_items]
  cases c with
  | set n => rfl
  | apply op n => cases op <;> rfl
  | get => rfl

/-! ## The spellings read without the JSON reader -/

theorem startsWith_iff (s p : String) :
    s.startsWith p = true ↔ ∃ r, bytesOf s = bytesOf p ++ r := by
  rw [String.startsWith_string_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨bytesOf (String.ofList t), ?_⟩
    have hs : s = p ++ String.ofList t := by
      rw [← String.toList_inj, String.toList_append, String.toList_ofList, ht]
    conv => lhs; rw [hs]
    simp [bytesOf, String.toByteArray_append, ByteArray.data_append]
  · rintro ⟨r, hr⟩
    apply List.isPrefix_of_utf8Encode_append_eq_utf8Encode (ByteArray.mk r.toArray)
    rw [String.utf8Encode_toList, String.utf8Encode_toList]
    apply ByteArray.ext
    rw [ByteArray.data_append, ← Array.toList_inj]
    simpa [bytesOf] using hr.symm

theorem eq_iff (s p : String) : s = p ↔ bytesOf s = bytesOf p := by
  rw [← String.toByteArray_inj]
  constructor
  · intro h; rw [bytesOf, h]; rfl
  · intro h; exact ByteArray.ext (Array.toList_inj.mp h)

/-- `closedNumber` after a prefix: the rest is a number below 2^64 in decimal and `}`. -/
theorem closedNumber_iff {s : String} {p r : List UInt8} (h : bytesOf s = p ++ r) (x : UInt64) :
    closedNumber s p.length = some x ↔ r = Token.decimal x.toNat ++ [125] := by
  have hl := Token.length_bytesOf s
  have hlen : s.utf8ByteSize = p.length + r.length := by rw [← hl, h, List.length_append]
  simp only [closedNumber]
  rw [Token.numberAt_spec s (by omega)]
  by_cases hr : r = []
  · subst hr
    rw [Token.slice_of_le (by simp at hlen; omega)]
    have hn : Token.number [] = none := by
      cases hx : Token.number [] with
      | none => rfl
      | some y => exact absurd (Token.number_canon hx).symm (Token.decimal_ne_nil _)
    simp [hn]
  · have hpos : 0 < r.length := List.length_pos_iff.mpr hr
    have hdrop : r = Token.slice (bytesOf s) p.length (s.utf8ByteSize - 1) ++
        [(bytesOf s)[s.utf8ByteSize - 1]'(by omega)] := by
      rw [← Token.slice_snoc (by omega) (by omega), Token.slice, h, hlen]
      simp
    rw [Token.byteAt_of_lt (s := s) (i := s.utf8ByteSize - 1) (by omega)]
    constructor
    · intro hx
      split at hx
      · rename_i h125
        rw [hdrop, h125, Token.number_canon hx]
      · cases hx
    · intro hx
      obtain ⟨h1, h2⟩ := List.append_inj' (hx.symm.trans hdrop) rfl
      simp only [List.cons.injEq, and_true] at h2
      rw [ite_eq_left h2.symm, ← h1, Token.number_decimal]

theorem prefix_clash {a b x y : List UInt8} (k : Nat) (ha : k ≤ a.length) (hb : k ≤ b.length)
    (hne : a.take k ≠ b.take k) : a ++ x ≠ b ++ y := by
  intro h
  have := congrArg (List.take k) h
  rw [List.take_append_of_le_length ha, List.take_append_of_le_length hb] at this
  exact hne this

/-- The bytes of a command written without a space. -/
theorem print_set (x : UInt64) :
    (encodeCommand (.set x)).print =
      bytesOf "{\"cmd\":\"set\",\"value\":" ++ (Token.decimal x.toNat ++ [125]) := by
  rw [Json.decimal_spec]; rfl

theorem print_apply (op : Op) (x : UInt64) :
    (encodeCommand (.apply op x)).print =
      (match op with
        | .add => bytesOf "{\"cmd\":\"apply\",\"op\":\"add\",\"arg\":"
        | .sub => bytesOf "{\"cmd\":\"apply\",\"op\":\"sub\",\"arg\":"
        | .mul => bytesOf "{\"cmd\":\"apply\",\"op\":\"mul\",\"arg\":"
        | .div => bytesOf "{\"cmd\":\"apply\",\"op\":\"div\",\"arg\":") ++
        (Token.decimal x.toNat ++ [125]) := by
  rw [Json.decimal_spec]; cases op <;> rfl

theorem print_get : (encodeCommand .get).print = bytesOf "{\"cmd\":\"get\"}" := by rfl


theorem spelled_sound {s : String} {c : Command} (h : spelled s = some c) :
    bytesOf s = (encodeCommand c).print := by
  unfold spelled at h
  split at h
  · rename_i hp
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [print_apply, hr, (closedNumber_iff hr x).mp hx]
  split at h
  · rename_i hp
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [print_apply, hr, (closedNumber_iff hr x).mp hx]
  split at h
  · rename_i hp
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [print_apply, hr, (closedNumber_iff hr x).mp hx]
  split at h
  · rename_i hp
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [print_apply, hr, (closedNumber_iff hr x).mp hx]
  split at h
  · rename_i hp
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hp
    obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [print_set, hr, (closedNumber_iff hr x).mp hx]
  split at h
  · rename_i hp
    cases h
    rw [print_get, hp]
  · cases h

theorem startsWith_false {s p : String} {a x : List UInt8} (h : bytesOf s = a ++ x) (k : Nat)
    (ha : k ≤ a.length) (hb : k ≤ (bytesOf p).length) (hne : a.take k ≠ (bytesOf p).take k) :
    s.startsWith p = false := by
  rw [Bool.eq_false_iff, Ne, startsWith_iff]
  rintro ⟨r, hr⟩
  exact prefix_clash k ha hb hne (h.symm.trans hr)

theorem spelled_complete {s : String} {c : Command} (h : bytesOf s = (encodeCommand c).print) :
    spelled s = some c := by
  unfold spelled
  cases c with
  | set x =>
    rw [print_set] at h
    have hn : closedNumber s 21 = some x := (closedNumber_iff h x).mpr rfl
    rw [startsWith_false h 21 (by decide) (by decide) (by decide),
      startsWith_false h 21 (by decide) (by decide) (by decide),
      startsWith_false h 21 (by decide) (by decide) (by decide),
      startsWith_false h 21 (by decide) (by decide) (by decide),
      (startsWith_iff _ _).mpr ⟨_, h⟩]
    simp [hn]
  | get =>
    rw [print_get] at h
    have h' : bytesOf s = bytesOf "{\"cmd\":\"get\"}" ++ [] := by rw [h, List.append_nil]
    rw [startsWith_false h' 13 (by decide) (by decide) (by decide),
      startsWith_false h' 13 (by decide) (by decide) (by decide),
      startsWith_false h' 13 (by decide) (by decide) (by decide),
      startsWith_false h' 13 (by decide) (by decide) (by decide),
      startsWith_false h' 13 (by decide) (by decide) (by decide)]
    simp [(eq_iff _ _).mpr h]
  | apply op x =>
    cases op
    · replace h : bytesOf s = bytesOf "{\"cmd\":\"apply\",\"op\":\"add\",\"arg\":" ++
          (Token.decimal x.toNat ++ [125]) := h.trans (print_apply .add x)
      have hn : closedNumber s 32 = some x := (closedNumber_iff h x).mpr rfl
      rw [(startsWith_iff _ _).mpr ⟨_, h⟩]
      simp [hn]
    · replace h : bytesOf s = bytesOf "{\"cmd\":\"apply\",\"op\":\"sub\",\"arg\":" ++
          (Token.decimal x.toNat ++ [125]) := h.trans (print_apply .sub x)
      have hn : closedNumber s 32 = some x := (closedNumber_iff h x).mpr rfl
      rw [startsWith_false h 32 (by decide) (by decide) (by decide), (startsWith_iff _ _).mpr ⟨_, h⟩]
      simp [hn]
    · replace h : bytesOf s = bytesOf "{\"cmd\":\"apply\",\"op\":\"mul\",\"arg\":" ++
          (Token.decimal x.toNat ++ [125]) := h.trans (print_apply .mul x)
      have hn : closedNumber s 32 = some x := (closedNumber_iff h x).mpr rfl
      rw [startsWith_false h 32 (by decide) (by decide) (by decide),
        startsWith_false h 32 (by decide) (by decide) (by decide), (startsWith_iff _ _).mpr ⟨_, h⟩]
      simp [hn]
    · replace h : bytesOf s = bytesOf "{\"cmd\":\"apply\",\"op\":\"div\",\"arg\":" ++
          (Token.decimal x.toNat ++ [125]) := h.trans (print_apply .div x)
      have hn : closedNumber s 32 = some x := (closedNumber_iff h x).mpr rfl
      rw [startsWith_false h 32 (by decide) (by decide) (by decide),
        startsWith_false h 32 (by decide) (by decide) (by decide),
        startsWith_false h 32 (by decide) (by decide) (by decide), (startsWith_iff _ _).mpr ⟨_, h⟩]
      simp [hn]

/-- `spelled` gives the command `c` exactly for the bodies whose bytes are `Value.print` of
`encodeCommand c`. -/
theorem spelled_spec (s : String) (c : Command) :
    spelled s = some c ↔ bytesOf s = (encodeCommand c).print :=
  ⟨spelled_sound, spelled_complete⟩

/-- `closedNumber` of a string gives `x` exactly when its bytes from `i` on are the decimal of
`x` and `}`. -/
theorem closedNumber_spec (s : String) (i : Nat) (x : UInt64) :
    closedNumber s i = some x ↔
      i ≤ (bytesOf s).length ∧ (bytesOf s).drop i = Token.decimal x.toNat ++ [125] := by
  by_cases hi : i ≤ (bytesOf s).length
  · have h : bytesOf s = (bytesOf s).take i ++ (bytesOf s).drop i := (List.take_append_drop i _).symm
    have hl : ((bytesOf s).take i).length = i := List.length_take_of_le hi
    have := closedNumber_iff h x
    rw [hl] at this
    simp [this, hi]
  · have hn : s.utf8ByteSize - 1 ≤ i := by rw [← Token.length_bytesOf]; omega
    have hnum : Token.number [] = none := by
      cases hx : Token.number [] with
      | none => rfl
      | some y => exact absurd (Token.number_canon hx).symm (Token.decimal_ne_nil _)
    simp [closedNumber, Token.numberAt_spec s (Nat.sub_le _ _), Token.slice_of_le hn, hnum, hi]

theorem bytesOf_fromUTF8 {l : List UInt8} {s : String}
    (h : String.fromUTF8? (ByteArray.mk l.toArray) = some s) : bytesOf s = l := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

/-- After the bytes `p`, the decimal of `x` and `}` are read as `x`, and the decimal of `x` and
`]` as no number. -/
theorem closedNumber_built (p : List UInt8) (x : UInt64) (b : Bool) :
    match String.fromUTF8? (ByteArray.mk (p ++ (Token.decimal x.toNat ++ [if b then 125 else 93])).toArray) with
    | some s => closedNumber s p.length = if b then some x else none
    | none => True := by
  split
  · rename_i s hs
    have h := bytesOf_fromUTF8 hs
    cases b with
    | true => exact (closedNumber_iff h x).mpr rfl
    | false =>
      cases hy : closedNumber s p.length with
      | none => rfl
      | some y =>
        have h2 := (List.append_inj' ((closedNumber_iff h y).mp hy) rfl).2
        simp at h2
  · trivial

/-- The spelling of a command is read as the command. -/
theorem spelled_print (c : Command) :
    match String.fromUTF8? (ByteArray.mk (encodeCommand c).print.toArray) with
    | some s => spelled s = some c
    | none => True := by
  split
  · rename_i s hs
    exact spelled_complete (bytesOf_fromUTF8 hs)
  · trivial

/-- `decode` is `decodeText`: the JSON reader decides every body, and `spelled` answers for it
on the bodies it knows. -/
theorem decode_text (body : String) : decode body = decodeText body := by
  unfold decode
  cases h : spelled body with
  | none => rfl
  | some c => exact (decodeText_encode c (spelled_sound h)).symm

/-- A JSON text that spells a command decodes to it. -/
theorem decode_encode {s : String} (c : Command) (h : bytesOf s = (encodeCommand c).print) :
    decode s = .ok c := by
  rw [decode_text, decodeText_encode c h]

theorem lookup_mem {k : List UInt8} {v : Item} :
    ∀ {ms : List (List UInt8 × Item)}, ms.lookup k = some v → (k, v) ∈ ms
  | [], h => by cases h
  | (k', v') :: ms, h => by
    rw [List.lookup_cons] at h
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true, Option.some.injEq] at h
      subst h
      simp
    · have : (k == k') = false := by simpa using hk
      simp only [this] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

theorem opNamed_some {l : List UInt8} {op : Op} (h : opNamed l = some op) : l = ascii (opName op) := by
  unfold opNamed at h
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  split at h
  · cases h; assumption
  cases h

theorem length_two {α : Type} {l : List α} (h : l.length = 2) : ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

theorem length_three {α : Type} {l : List α} (h : l.length = 3) : ∃ x y z, l = [x, y, z] := by
  match l, h with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

theorem length_one {α : Type} {l : List α} (h : l.length = 1) : ∃ x, l = [x] := by
  match l, h with
  | [x], _ => exact ⟨x, rfl⟩

/-- An object with as many members as a command has fields, which has each of them, has no
other member. -/
theorem members_subset {ms : List (List UInt8 × Item)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) : ∀ m ∈ ms, m ∈ fields c := by
  cases c with
  | set n =>
    obtain ⟨x, y, rfl⟩ := length_two hl
    have h1 := hm _ (List.mem_cons_self ..)
    have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> first
      | (subst h2; simp [fields]; done)
      | (simp [ascii] at h2; done)
  | apply op n =>
    obtain ⟨x, y, z, rfl⟩ := length_three hl
    have h1 := hm _ (List.mem_cons_self ..)
    have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
      first
      | (subst h2; subst h3; simp [fields]; done)
      | (simp [ascii] at h2; done)
      | (simp [ascii] at h3; done)
      | (subst h2; simp [ascii] at h3; done)
  | get =>
    obtain ⟨x, rfl⟩ := length_one hl
    have h1 := hm _ (List.mem_cons_self ..)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    subst h1
    simp [fields]

/-- `decodeMembers` accepts, as the command `c`, exactly the members that are the fields of `c`
in some order: as many as `c` has fields, with each field among them. -/
theorem decodeMembers_ok_iff (ms : List (List UInt8 × Item)) (c : Command) :
    decodeMembers ms = .ok c ↔ ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  constructor
  · intro h
    unfold decodeMembers at h
    split at h
    · cases h
    · rename_i name hcmd
      split at h
      · rename_i hname
        subst hname
        split at h
        · rename_i hlen
          split at h
          · rename_i n hv
            cases h
            exact ⟨hlen, by
              intro m hm
              simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hm
              rcases hm with rfl | rfl
              · exact lookup_mem hcmd
              · exact lookup_mem hv⟩
          · cases h
          · cases h
        · cases h
      · split at h
        · rename_i hname
          subst hname
          split at h
          · rename_i hlen
            split at h
            · rename_i op arg hop harg
              split at h
              · rename_i op' hop'
                split at h
                · rename_i n
                  cases h
                  have := opNamed_some hop'
                  subst this
                  exact ⟨hlen, by
                    intro m hm
                    simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hm
                    rcases hm with rfl | rfl | rfl
                    · exact lookup_mem hcmd
                    · exact lookup_mem hop
                    · exact lookup_mem harg⟩
                · cases h
              · cases h
            · cases h
          · cases h
        · split at h
          · rename_i hname
            subst hname
            split at h
            · rename_i hlen
              cases h
              exact ⟨hlen, by
                intro m hm
                simp only [fields, List.mem_cons, List.not_mem_nil, or_false] at hm
                subst hm
                exact lookup_mem hcmd⟩
            · cases h
          · cases h
    · cases h
  · rintro ⟨hl, hm⟩
    cases c with
    | set n =>
      obtain ⟨x, y, rfl⟩ := length_two hl
      have h1 := hm _ (List.mem_cons_self ..)
      have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
      rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> first
        | (subst h2; rfl)
        | (simp [ascii] at h2; done)
    | apply op n =>
      obtain ⟨x, y, z, rfl⟩ := length_three hl
      have h1 := hm _ (List.mem_cons_self ..)
      have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have h3 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3
      rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
        first
        | (subst h2; subst h3; cases op <;> rfl)
        | (simp [ascii] at h2; done)
        | (simp [ascii] at h3; done)
        | (subst h2; simp [ascii] at h3; done)
    | get =>
      obtain ⟨x, rfl⟩ := length_one hl
      have h1 := hm _ (List.mem_cons_self ..)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      subst h1
      rfl

/-- The items that are a value by themselves: `null`, `true`, `false`, a number and a string. -/
def isScalar : Item → Bool
  | .null | .bool _ | .num _ | .number | .str _ => true
  | _ => false

theorem scalar_spec (i : Item) : scalar i = isScalar i := by
  cases i <;> rfl

theorem fields_scalar (c : Command) : ∀ m ∈ fields c, scalar m.2 = true := by
  cases c <;> simp [fields, scalar]

theorem members_flat (ms : List (List UInt8 × Item)) (hs : ∀ m ∈ ms, scalar m.2 = true)
    (acc : List (List UInt8 × Item)) :
    members acc (ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose]) = some (acc.reverse ++ ms) := by
  induction ms generalizing acc with
  | nil => simp [members]
  | cons m ms ih =>
    obtain ⟨k, v⟩ := m
    have hv : scalar v = true := hs (k, v) (List.mem_cons_self ..)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    cases hms : ms.flatMap (fun m => [Item.key m.1, m.2]) ++ [Item.objClose] with
    | nil => simp at hms
    | cons i rest =>
      have := ih (fun m hm => hs m (List.mem_cons_of_mem _ hm)) ((k, v) :: acc)
      rw [hms] at this
      cases v <;> simp_all [members, scalar]

theorem members_some {acc : List (List UInt8 × Item)} {rest : List Item}
    {ms : List (List UInt8 × Item)} (h : members acc rest = some ms) :
    ∃ ms', ms = acc.reverse ++ ms' ∧ rest = ms'.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose] := by
  induction acc, rest using members.induct with
  | case1 acc =>
    simp only [members, Option.some.injEq] at h
    exact ⟨[], by simp [h]⟩
  | case2 acc k v rest hv ih =>
    simp only [members, hv, ite_true] at h
    obtain ⟨ms', rfl, rfl⟩ := ih h
    exact ⟨(k, v) :: ms', by simp⟩
  | case3 acc k v rest hv =>
    simp [members, hv] at h
  | case4 acc rest h1 h2 =>
    unfold members at h
    split at h
    · exact absurd rfl (h1)
    · exact absurd rfl (h2 _ _ _)
    · cases h

/-- `decodeItems` accepts, as the command `c`, exactly the items of an object whose members are
the fields of `c` in some order. -/
theorem decodeItems_ok_iff (items : List Item) (c : Command) :
    decodeItems items = .ok c ↔
      ∃ ms, items = objectItems ms ∧ ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  constructor
  · intro h
    unfold decodeItems at h
    split at h
    · rename_i rest
      split at h
      · rename_i ms hms
        obtain ⟨ms', h1, rfl⟩ := members_some hms
        simp only [List.reverse_nil, List.nil_append] at h1
        subst h1
        exact ⟨ms, rfl, (decodeMembers_ok_iff _ c).mp h⟩
      · cases h
    · cases h
  · rintro ⟨ms, rfl, hl, hm⟩
    have hs : ∀ m ∈ ms, scalar m.2 = true := fun m h => fields_scalar c m (members_subset hl hm m h)
    simp only [decodeItems, objectItems, members_flat ms hs [], List.reverse_nil, List.nil_append]
    exact (decodeMembers_ok_iff ms c).mpr ⟨hl, hm⟩

/-- A body is decoded to the command `c` exactly when it reads as the items of an object whose
members are the fields of `c` in some order. -/
theorem decode_ok_iff (body : String) (c : Command) :
    decode body = .ok c ↔
      ∃ ms, readString body = some (objectItems ms) ∧ ms.length = (fields c).length ∧
        ∀ m ∈ fields c, m ∈ ms := by
  rw [decode_text, decodeText]
  cases h : readString body with
  | none => simp
  | some items =>
    simp only [decodeItems_ok_iff, Option.some.injEq]

/-- A body that is not a JSON text is refused as that. -/
theorem decodeText_notJson_iff (body : String) :
    decodeText body = .error .notJson ↔ readString body = none := by
  unfold decodeText
  cases h : readString body with
  | none => simp
  | some items =>
    simp only [reduceCtorEq, iff_false]
    unfold decodeItems
    split
    · split
      · unfold decodeMembers
        repeat' split
        all_goals simp
      · simp
    · simp

/-- A body that is not a JSON text is refused as that. -/
theorem decode_notJson_iff (body : String) :
    decode body = .error .notJson ↔ readString body = none := by
  rw [decode_text, decodeText_notJson_iff]

/-- An object without the member `cmd` is refused as that, and no other. -/
theorem decodeMembers_missingCmd_iff (ms : List (List UInt8 × Item)) :
    decodeMembers ms = .error .missingCmd ↔ ms.lookup (ascii ['c', 'm', 'd']) = none := by
  unfold decodeMembers
  rw [show ascii ['c', 'm', 'd'] = [99, 109, 100] from rfl]
  cases h : ms.lookup [99, 109, 100] with
  | none => simp
  | some v =>
    simp only [reduceCtorEq, iff_false]
    repeat' split
    all_goals simp_all

/-- The items of an object whose members are values by themselves decode as its members. -/
theorem decodeItems_object (ms : List (List UInt8 × Item)) (hs : ∀ m ∈ ms, isScalar m.2 = true) :
    decodeItems (objectItems ms) = decodeMembers ms := by
  have hs : ∀ m ∈ ms, scalar m.2 = true := fun m h => (scalar_spec m.2).trans (hs m h)
  simp only [decodeItems, objectItems, members_flat ms hs [], List.reverse_nil, List.nil_append]

/-- The items of the object that spells a command decode to it. -/
theorem decodeItems_fields (c : Command) : decodeItems (objectItems (fields c)) = .ok c := by
  rw [decodeItems_object _ fun m h => (scalar_spec m.2).symm.trans (fields_scalar c m h),
    decodeMembers_fields]

/-- The operations by their names. -/
theorem opNamed_spec (l : List UInt8) :
    opNamed l = [Op.add, .sub, .mul, .div].find? fun op => ascii (opName op) = l := by
  unfold opNamed
  rw [show ([97, 100, 100] : List UInt8) = ascii (opName .add) from rfl,
    show ([115, 117, 98] : List UInt8) = ascii (opName .sub) from rfl,
    show ([109, 117, 108] : List UInt8) = ascii (opName .mul) from rfl,
    show ([100, 105, 118] : List UInt8) = ascii (opName .div) from rfl]
  simp only [List.find?_cons, List.find?_nil]
  repeat' split
  all_goals simp_all [eq_comm]

/-- Whether a member looked up is there and is not a number below 2^64 in decimal digits. -/
def notNum : Option Item → Bool
  | some (.num _) => false
  | some _ => true
  | none => false

/-- Whether a member looked up is a string that names an operation. -/
def namesOp : Option Item → Bool
  | some (.str o) => ([Op.add, .sub, .mul, .div].find? fun op => ascii (opName op) = o).isSome
  | _ => false

/-- `badValue` is the refusal of the objects of 2 members with `"cmd":"set"` whose `value` is
not a number below 2^64 in decimal digits, and of no other. -/
theorem decodeMembers_badValue_iff (ms : List (List UInt8 × Item)) :
    decodeMembers ms = .error .badValue ↔
      ms.lookup (ascii ['c', 'm', 'd']) = some (.str (ascii ['s', 'e', 't'])) ∧ ms.length = 2 ∧
        notNum (ms.lookup (ascii ['v', 'a', 'l', 'u', 'e'])) = true := by
  rw [show ascii ['c', 'm', 'd'] = [99, 109, 100] from rfl,
    show ascii ['s', 'e', 't'] = [115, 101, 116] from rfl,
    show ascii ['v', 'a', 'l', 'u', 'e'] = [118, 97, 108, 117, 101] from rfl]
  unfold decodeMembers
  repeat' split
  all_goals simp_all [notNum, -List.lookup_eq_none_iff]

/-- `badArg` is the refusal of the objects of 3 members with `"cmd":"apply"` and an `op` that
names an operation whose `arg` is not a number below 2^64 in decimal digits, and of no other. -/
theorem decodeMembers_badArg_iff (ms : List (List UInt8 × Item)) :
    decodeMembers ms = .error .badArg ↔
      ms.lookup (ascii ['c', 'm', 'd']) = some (.str (ascii ['a', 'p', 'p', 'l', 'y'])) ∧
        ms.length = 3 ∧ namesOp (ms.lookup (ascii ['o', 'p'])) = true ∧
        notNum (ms.lookup (ascii ['a', 'r', 'g'])) = true := by
  rw [show ascii ['c', 'm', 'd'] = [99, 109, 100] from rfl,
    show ascii ['a', 'p', 'p', 'l', 'y'] = [97, 112, 112, 108, 121] from rfl,
    show ascii ['o', 'p'] = [111, 112] from rfl, show ascii ['a', 'r', 'g'] = [97, 114, 103] from rfl]
  unfold decodeMembers
  repeat' split
  all_goals first
    | (simp_all [notNum, namesOp, ← opNamed_spec, -List.lookup_eq_none_iff]; done)
    | (rename_i hx
       refine ⟨fun h => by simp at h, ?_⟩
       rintro ⟨-, -, hop, harg⟩
       exfalso
       cases ho : List.lookup [111, 112] ms with
       | none => simp [ho, namesOp] at hop
       | some v =>
         cases v with
         | str o =>
           cases ha : List.lookup [97, 114, 103] ms with
           | none => simp [ha, notNum] at harg
           | some a => exact hx o a ho ha
         | _ => simp [ho, namesOp] at hop)

/-- The message of each refusal. -/
theorem refusalMessage_spec (e : Refusal) :
    (refusalMessage e).toList =
      match e with
      | .notJson => "body is not JSON".toList
      | .notCommand => "not a calculator command".toList
      | .missingCmd => "missing field `cmd`".toList
      | .badValue => "`value` must be an integer below 2^64".toList
      | .badArg => "`arg` must be an integer below 2^64".toList := by
  cases e <;> rfl

/-! ## Requests -/

/-- A request whose token has expired is answered 401, whatever its body. -/
theorem request_expired {exp now : UInt64} (h : exp < now) (tenant user : UInt64) (body : Http.Body) :
    request tenant user exp now body = .error (Http.refuse 401 "token expired") := by
  simp [request, Http.admit_expired h]

/-- A request with a token that has not expired and a body of text: the command the body
decodes to, for the principal the token claims, or 400 with the message of the refusal. -/
theorem request_text {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64) (s : String) :
    request tenant user exp now (.text s) =
      match decode s with
      | .ok cmd => .ok ⟨⟨tenant, user⟩, cmd⟩
      | .error e => .error (Http.refuse 400 (refusalMessage e)) := by
  simp only [request, Http.admit_text h]
  cases decode s <;> rfl

/-- A request with a token that has not expired and a body that is not text. -/
theorem request_not_text {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64) :
    request tenant user exp now .notUtf8 = .error (Http.refuse 400 "body is not JSON") ∧
      request tenant user exp now .tooLarge = .error (Http.refuse 413 "request body too large") ∧
      request tenant user exp now .unreadable =
        .error (Http.refuse 400 "request body cannot be read") := by
  obtain ⟨h1, h2, h3⟩ := Http.admit_not_text h
  simp [request, h1, h2, h3]

/-- A request with a token that has not expired and a body that spells the command `c` gives
the engine `c` for the principal of the token's tenant and user. -/
theorem request_encode {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64) {s : String}
    (c : Command) (hs : bytesOf s = (encodeCommand c).print) :
    request tenant user exp now (.text s) = .ok ⟨⟨tenant, user⟩, c⟩ := by
  rw [request_text h, decode_encode c hs]

theorem request_actor_run (tenant user exp now : UInt64) (body : Http.Body) :
    match request tenant user exp now body with
    | .ok call => call.actor = ⟨tenant, user⟩
    | .error _ => True := by
  cases h : request tenant user exp now body with
  | error _ => trivial
  | ok call =>
    show call.actor = ⟨tenant, user⟩
    unfold request at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; rfl

/-- The principal `request` gives the engine is the tenant and the user it was given. -/
theorem request_actor {tenant user exp now : UInt64} {body : Http.Body} {call : Call}
    (h : request tenant user exp now body = .ok call) : call.actor = ⟨tenant, user⟩ := by
  have := request_actor_run tenant user exp now body
  rwa [h] at this

/-- Every answer of `request` has the status 400, 401 or 413 and a body `{"error": message}`. -/
theorem request_refusal {tenant user exp now : UInt64} {body : Http.Body} {r : Http.Response}
    (h : request tenant user exp now body = .error r) :
    (r.status = 400 ∨ r.status = 401 ∨ r.status = 413) ∧
      ∃ message, r.body.toList = (Http.errorValue message).print := by
  by_cases he : exp < now
  · rw [request_expired he] at h
    cases h
    exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
  · cases body with
    | text s =>
      rw [request_text he] at h
      cases hd : decode s with
      | ok cmd => simp [hd] at h
      | error e =>
        simp only [hd, Except.error.injEq] at h
        subst h
        exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | notUtf8 =>
      rw [(request_not_text he tenant user).1] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | tooLarge =>
      rw [(request_not_text he tenant user).2.1] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | unreadable =>
      rw [(request_not_text he tenant user).2.2] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩

/-! ## Responses -/

/-- An accepted command is answered 200 with the JSON value of its reply. -/
theorem respond_ok (r : Reply) :
    (respond (.ok r)).status = 200 ∧ (respond (.ok r)).body.toList = (replyValue r).print :=
  ⟨rfl, encodeReplyArray_spec r⟩

/-- A refused command is answered 422 with the JSON value of its refusal. -/
theorem respond_error (e : Error) :
    (respond (.error e)).status = 422 ∧ (respond (.error e)).body.toList = (errorValue e).print :=
  ⟨rfl, encodeErrorArray_spec e⟩

/-! ## Idempotency keys -/

/-- The name of an operation in a fingerprint. -/
def opTitle : Op → List Char
  | .add => ['A', 'd', 'd']
  | .sub => ['S', 'u', 'b']
  | .mul => ['M', 'u', 'l']
  | .div => ['D', 'i', 'v']

/-- The text of a fingerprint: `Set { value: 6 }`, `Apply { op: Mul, arg: 7 }`, `Get`. -/
def fingerprintText : Command → List UInt8
  | .set n => ascii "Set { value: ".toList ++ Json.digits n.toNat ++ ascii " }".toList
  | .apply op n =>
    ascii "Apply { op: ".toList ++ ascii (opTitle op) ++ ascii ", arg: ".toList ++ Json.digits n.toNat ++
      ascii " }".toList
  | .get => ascii "Get".toList

/-- The bytes of a fingerprint are its text. -/
theorem fingerprint_spec (c : Command) : (fingerprint c).toList = fingerprintText c := by
  cases c with
  | set n => simp [fingerprint, fingerprintText, Json.pushDecimal_spec, Json.decimal_spec, ascii]
  | apply op n =>
    cases op <;>
      simp [fingerprint, opFingerprint, fingerprintText, Json.pushDecimal_spec, Json.decimal_spec, ascii,
        opTitle]
  | get => rfl

theorem digits_injective {n m : Nat} (h : Json.digits n = Json.digits m) : n = m := by
  rw [← Json.decimal_spec, ← Json.decimal_spec] at h
  have := congrArg Token.value h
  rwa [Token.value_decimal, Token.value_decimal] at this

/-- Different commands have different fingerprints. -/
theorem fingerprint_injective {c c' : Command} (h : fingerprint c = fingerprint c') : c = c' := by
  have h' : fingerprintText c = fingerprintText c' := by
    rw [← fingerprint_spec, ← fingerprint_spec, h]
  cases c with
  | set n =>
    cases c' with
    | set m =>
      have hd : Json.digits n.toNat = Json.digits m.toNat := by
        simpa [fingerprintText, List.append_assoc] using h'
      rw [UInt64.toNat_inj.mp (digits_injective hd)]
    | apply op m => cases op <;> simp [fingerprintText, ascii, opTitle] at h'
    | get => simp [fingerprintText, ascii] at h'
  | apply op n =>
    cases c' with
    | set m => cases op <;> simp [fingerprintText, ascii, opTitle] at h'
    | apply op' m =>
      cases op <;> cases op' <;> first
        | (simp [fingerprintText, ascii, opTitle] at h'; done)
        | (have hd : Json.digits n.toNat = Json.digits m.toNat := by
             simpa [fingerprintText, List.append_assoc] using h'
           rw [UInt64.toNat_inj.mp (digits_injective hd)])
    | get => cases op <;> simp [fingerprintText, ascii, opTitle] at h'
  | get =>
    cases c' with
    | set m => simp [fingerprintText, ascii] at h'
    | apply op m => cases op <;> simp [fingerprintText, ascii, opTitle] at h'
    | get => rfl

/-- The scope of a principal is `u` and its user in decimal. -/
theorem scope_spec (a : Principal) : (scope a).toList = 'u' :: Nat.toDigits 10 a.user.toNat := by
  simp [scope, String.toList_append, Nat.toList_repr]

/-- The scopes of two principals are the same exactly when their users are. -/
theorem scope_injective {a b : Principal} : scope a = scope b ↔ a.user = b.user := by
  constructor
  · intro h
    have h1 : toString a.user.toNat = toString b.user.toNat := (String.append_right_inj _).mp h
    have h2 : Nat.toDigits 10 a.user.toNat = Nat.toDigits 10 b.user.toNat := by
      rw [← Nat.toList_repr, ← Nat.toList_repr]
      exact congrArg String.toList h1
    exact UInt64.toNat_inj.mp (digits_injective (by simp [Json.digits, h2]))
  · intro h
    simp [scope, h]

end Calculator.Wire
