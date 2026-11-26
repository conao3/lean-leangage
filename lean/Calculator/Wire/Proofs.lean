import Calculator.Wire
import Calculator.Proofs
import Leangage.Http.Proofs
import Leangage.Json.Lexemes.Proofs

/-!
# What the calculator's functions on the wire guarantee

The servers' JSON libraries are trusted to hand over the tokens of the text of a body
(`Leangage.Json.Lexemes.Proofs`); the theorems start from those tokens.

- `decode_encode`: the tokens of the JSON text that spells the command `c` (`lexemesOf c`, a
  number as its decimal) decode to `c`. So every command has a spelling the server accepts.
- `decode_eq`, `spelled_sound`, `spelled_lexemesOf`: `decode`, which answers the tokens of a
  command with its members in the order of `lexemesOf` from `spelled`, is `decodeObject`, the
  decision on the members by their names, on every list of tokens.
- `decode_ok_iff`, `decodeMembers_ok_iff`: tokens decode to `c` exactly when `object` gives
  members for them, as many as `c` has fields (`fields c`) and with each field among them. By
  `object_iff` those are the tokens of an object whose values are not arrays or objects. The
  members may come in any order; an object with another member or a member twice is refused.
  `decode_spec` and `decode_object` give the decision for the tokens of any object, and
  `decode_not_object` the refusal of every other list of tokens.
- `decodeMembers_missingCmd_iff`: `missingCmd` is the refusal of the objects without a member
  `cmd`. `decodeMembers_badValue_iff`, `decodeMembers_badArg_iff`: `badValue` is the refusal of
  the objects of 2 members with `"cmd":"set"` whose `value` is not a number below 2^64 in decimal
  digits, and `badArg` that of the objects of 3 members with `"cmd":"apply"` and an `op` that
  names an operation whose `arg` is not such a number. Every other refused object gets
  `notCommand`. `refusalMessage_spec` gives the message of each refusal.
- `request_expired`, `request_json`, `request_not_json`: a request whose token has expired is
  answered 401 `token expired` whatever its body; otherwise the tokens of a body give the command
  they decode to for the principal of the token's tenant and user (`request_actor`), or
  400 with the message of the refusal, and a body without tokens is answered 400 or 413.
  `request_encode` states the accepted case for the spelling of a command, and
  `request_refusal` that every answer of `request` has the status 400, 401 or 413 and a body
  `{"error": message}`.
- `answerOf_spec`, `call_spec`, `request_call`, `request_answer`: `answerOf`, `actorOf` and
  `cmdOf` take the result of `request` apart: the answer when there is one, and otherwise the
  principal and the command of the call.
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
open Leangage.Json.Lexemes
open Leangage.Token (bytesOf)

/-! ## Commands -/

/-- The name of an operation on the wire. -/
def opName : Op → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"

/-- The members of the object that spells a command, as they are read. -/
def fields : Command → List (String × Scalar)
  | .set n => [("cmd", .str "set"), ("value", .num n)]
  | .apply op n =>
    [("cmd", .str "apply"), ("op", .str (opName op)),
      ("arg", .num n)]
  | .get => [("cmd", .str ("get"))]

/-- The members of the object that spells a command, as tokens: a number as its decimal. -/
def lexFields : Command → List (String × Lexeme)
  | .set n => [("cmd", .str "set"), ("value", .number (decimalText n))]
  | .apply op n => [("cmd", .str "apply"), ("op", .str (opName op)), ("arg", .number (decimalText n))]
  | .get => [("cmd", .str "get")]

/-- The tokens of the JSON text that spells a command: `{"cmd":"set","value":n}`,
`{"cmd":"apply","op":"mul","arg":n}`, `{"cmd":"get"}`. -/
def lexemesOf (c : Command) : List Lexeme :=
  objectLexemes (lexFields c)

theorem scalars_lexFields (c : Command) : scalars (lexFields c) = some (fields c) := by
  cases c <;> simp [lexFields, fields, scalars, scalarOf, numberOf_decimalText]

theorem decodeMembers_fields (c : Command) : decodeMembers (fields c) = .ok c := by
  cases c with
  | set n => rfl
  | apply op n => cases op <;> rfl
  | get => rfl

/-- `decodeObject` decides on the members `object` gives, and refuses tokens without members. -/
theorem decodeObject_spec (lexemes : List Lexeme) :
    decodeObject lexemes =
      match object lexemes with
      | some ms => decodeMembers ms
      | none => .error .notCommand := rfl

/-- `numbered` gives the number `n` exactly for the text that is `start` and the decimal of `n`. -/
theorem numbered_iff (start packed : String) (n : UInt64) :
    numbered start packed = some n ↔ packed = start ++ decimalText n := by
  have slice_rest : ∀ r : List UInt8, bytesOf packed = bytesOf start ++ r →
      Token.slice (bytesOf packed) start.utf8ByteSize packed.utf8ByteSize = r := by
    intro r hr
    have hl := Token.length_bytesOf packed
    have hs := Token.length_bytesOf start
    rw [Token.slice, ← hl, ← hs, hr]
    simp
  unfold numbered
  constructor
  · intro h
    split at h
    · rename_i hs
      obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hs
      rw [Token.numberAt_spec packed (Nat.le_refl _), slice_rest r hr] at h
      apply bytesOf_injective
      rw [hr, bytesOf_append, bytesOf_decimalText, Token.number_canon h]
    · cases h
  · intro h
    have hb : bytesOf packed = bytesOf start ++ Token.decimal n.toNat := by
      rw [h, bytesOf_append, bytesOf_decimalText]
    simp only [(startsWith_iff _ _).mpr ⟨_, hb⟩, ↓reduceIte]
    rw [Token.numberAt_spec packed (Nat.le_refl _), slice_rest _ hb, Token.number_decimal]

theorem prefix_clash {a b x y : List UInt8} (k : Nat) (ha : k ≤ a.length) (hb : k ≤ b.length)
    (hne : a.take k ≠ b.take k) : a ++ x ≠ b ++ y := by
  intro h
  have := congrArg (List.take k) h
  rw [List.take_append_of_le_length ha, List.take_append_of_le_length hb] at this
  exact hne this

/-- `numbered` gives no number for a text whose bytes differ from those of `start` early on. -/
theorem numbered_none {start packed : String} {a x : List UInt8} (h : bytesOf packed = a ++ x)
    (k : Nat) (ha : k ≤ a.length) (hb : k ≤ (bytesOf start).length)
    (hne : a.take k ≠ (bytesOf start).take k) : numbered start packed = none := by
  unfold numbered
  split
  · rename_i hs
    obtain ⟨r, hr⟩ := (startsWith_iff _ _).mp hs
    exact absurd (h.symm.trans hr) (prefix_clash k ha hb hne)
  · rfl

/-- The packed text of the tokens of a command whose members come in the usual order. -/
def canonical : Command → String
  | .set n => "{ksk#}\n3:cmd3:set5:value" ++ decimalText n
  | .apply .add n => "{ksksk#}\n3:cmd5:apply2:op3:add3:arg" ++ decimalText n
  | .apply .sub n => "{ksksk#}\n3:cmd5:apply2:op3:sub3:arg" ++ decimalText n
  | .apply .mul n => "{ksksk#}\n3:cmd5:apply2:op3:mul3:arg" ++ decimalText n
  | .apply .div n => "{ksksk#}\n3:cmd5:apply2:op3:div3:arg" ++ decimalText n
  | .get => "{ks}\n3:cmdget"

theorem pack_lexemesOf (c : Command) : pack (lexemesOf c) = canonical c := by
  have h2 : Nat.toDigits 10 2 = ['2'] := by decide
  have h3 : Nat.toDigits 10 3 = ['3'] := by decide
  have h5 : Nat.toDigits 10 5 = ['5'] := by decide
  rw [← String.toList_inj]
  cases c with
  | set n =>
    simp [pack, lexemesOf, lexFields, objectLexemes, kindOf, textOf, packTexts, canonical, decimalText,
      List.filterMap_cons, h3, h5]
  | apply op n =>
    cases op <;>
      simp [pack, lexemesOf, lexFields, objectLexemes, kindOf, textOf, packTexts, canonical, decimalText,
        List.filterMap_cons, opName, h2, h3, h5]
  | get =>
    simp [pack, lexemesOf, lexFields, objectLexemes, kindOf, textOf, packTexts, canonical,
      List.filterMap_cons, h3]

/-- `spelled` gives the command `c` exactly for the packed text of the tokens of `c` with its
members in the usual order. -/
theorem spelled_iff (packed : String) (c : Command) : spelled packed = some c ↔ packed = canonical c := by
  constructor
  · intro h
    unfold spelled at h
    split at h
    · rename_i n hn; cases h; exact (numbered_iff _ _ n).mp hn
    · split at h
      · rename_i n hn; cases h; exact (numbered_iff _ _ n).mp hn
      · split at h
        · rename_i n hn; cases h; exact (numbered_iff _ _ n).mp hn
        · split at h
          · rename_i n hn; cases h; exact (numbered_iff _ _ n).mp hn
          · split at h
            · rename_i n hn; cases h; exact (numbered_iff _ _ n).mp hn
            · split at h
              · rename_i hg; cases h; exact hg
              · cases h
  · intro h
    subst h
    unfold spelled
    cases c with
    | set n =>
      have hb : bytesOf (canonical (.set n)) = bytesOf "{ksk#}\n3:cmd3:set5:value" ++ Token.decimal n.toNat := by
        rw [canonical, bytesOf_append, bytesOf_decimalText]
      rw [numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide)]
      simp only [canonical]
      rw [(numbered_iff _ _ n).mpr rfl]
    | apply op n =>
      cases op with
      | add =>
        have hb : bytesOf (canonical (.apply .add n)) = bytesOf "{ksksk#}\n3:cmd5:apply2:op3:add3:arg" ++ Token.decimal n.toNat := by
          rw [canonical, bytesOf_append, bytesOf_decimalText]
        simp only [canonical]
        rw [(numbered_iff _ _ n).mpr rfl]
      | sub =>
        have hb : bytesOf (canonical (.apply .sub n)) = bytesOf "{ksksk#}\n3:cmd5:apply2:op3:sub3:arg" ++ Token.decimal n.toNat := by
          rw [canonical, bytesOf_append, bytesOf_decimalText]
        rw [numbered_none hb 30 (by decide) (by decide) (by decide)]
        simp only [canonical]
        rw [(numbered_iff _ _ n).mpr rfl]
      | mul =>
        have hb : bytesOf (canonical (.apply .mul n)) = bytesOf "{ksksk#}\n3:cmd5:apply2:op3:mul3:arg" ++ Token.decimal n.toNat := by
          rw [canonical, bytesOf_append, bytesOf_decimalText]
        rw [numbered_none hb 30 (by decide) (by decide) (by decide), numbered_none hb 30 (by decide) (by decide) (by decide)]
        simp only [canonical]
        rw [(numbered_iff _ _ n).mpr rfl]
      | div =>
        have hb : bytesOf (canonical (.apply .div n)) = bytesOf "{ksksk#}\n3:cmd5:apply2:op3:div3:arg" ++ Token.decimal n.toNat := by
          rw [canonical, bytesOf_append, bytesOf_decimalText]
        rw [numbered_none hb 30 (by decide) (by decide) (by decide), numbered_none hb 30 (by decide) (by decide) (by decide), numbered_none hb 30 (by decide) (by decide) (by decide)]
        simp only [canonical]
        rw [(numbered_iff _ _ n).mpr rfl]
    | get =>
      have hb : bytesOf (canonical .get) = bytesOf "{ks}\n3:cmdget" ++ [] := by simp [canonical]
      rw [numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide), numbered_none hb 5 (by decide) (by decide) (by decide)]
      simp [canonical]

/-- A command `spelled` gives is the command of the tokens the packed text unpacks to. -/
theorem spelled_sound {packed : String} {c : Command} (h : spelled packed = some c) :
    unpack packed = some (lexemesOf c) := by
  rw [(spelled_iff packed c).mp h, ← pack_lexemesOf, unpack_pack]

theorem decodeObject_lexemesOf (c : Command) : decodeObject (lexemesOf c) = .ok c := by
  rw [decodeObject, lexemesOf, object_objectLexemes, scalars_lexFields]
  exact decodeMembers_fields c

/-- `decode` decides on the tokens a packed text unpacks to, and refuses a text that no list of
tokens packs to as no JSON. -/
theorem decode_eq (packed : String) :
    decode packed =
      match unpack packed with
      | some lexemes => decodeObject lexemes
      | none => .error .notJson := by
  unfold decode
  cases h : spelled packed with
  | none => rfl
  | some c =>
    simp only [spelled_sound h]
    exact (decodeObject_lexemesOf c).symm

/-- `spelled` reads the packed tokens of the JSON text that spells a command. -/
theorem spelled_lexemesOf (c : Command) : spelled (pack (lexemesOf c)) = some c :=
  (spelled_iff _ c).mpr (pack_lexemesOf c)

/-- The tokens of the JSON text that spells a command decode to it. -/
theorem decode_encode (c : Command) : decode (pack (lexemesOf c)) = .ok c := by
  rw [decode_eq, unpack_pack]
  exact decodeObject_lexemesOf c

theorem lookup_mem {k : String} {v : Scalar} :
    ∀ {ms : List (String × Scalar)}, ms.lookup k = some v → (k, v) ∈ ms
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

theorem opNamed_some {l : String} {op : Op} (h : opNamed l = some op) : l = opName op := by
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
theorem members_subset {ms : List (String × Scalar)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) : ∀ m ∈ ms, m ∈ fields c := by
  cases c with
  | set n =>
    obtain ⟨x, y, rfl⟩ := length_two hl
    have h1 := hm _ (List.mem_cons_self ..)
    have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl <;> rcases h2 with h2 | h2 <;> first
      | (subst h2; simp [fields]; done)
      | (simp at h2; done)
  | apply op n =>
    obtain ⟨x, y, z, rfl⟩ := length_three hl
    have h1 := hm _ (List.mem_cons_self ..)
    have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    have h3 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
      first
      | (subst h2; subst h3; simp [fields]; done)
      | (simp at h2; done)
      | (simp at h3; done)
      | (subst h2; simp at h3; done)
  | get =>
    obtain ⟨x, rfl⟩ := length_one hl
    have h1 := hm _ (List.mem_cons_self ..)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
    subst h1
    simp [fields]

/-- `decodeMembers` accepts, as the command `c`, exactly the members that are the fields of `c`
in some order: as many as `c` has fields, with each field among them. -/
theorem decodeMembers_ok_iff (ms : List (String × Scalar)) (c : Command) :
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
        | (simp at h2; done)
    | apply op n =>
      obtain ⟨x, y, z, rfl⟩ := length_three hl
      have h1 := hm _ (List.mem_cons_self ..)
      have h2 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      have h3 := hm _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1 h2 h3
      rcases h1 with rfl | rfl | rfl <;> rcases h2 with h2 | h2 | h2 <;> rcases h3 with h3 | h3 | h3 <;>
        first
        | (subst h2; subst h3; cases op <;> rfl)
        | (simp at h2; done)
        | (simp at h3; done)
        | (subst h2; simp at h3; done)
    | get =>
      obtain ⟨x, rfl⟩ := length_one hl
      have h1 := hm _ (List.mem_cons_self ..)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      subst h1
      rfl

theorem decodeMembers_ne_notJson (ms : List (String × Scalar)) :
    decodeMembers ms ≠ .error .notJson := by
  unfold decodeMembers
  repeat' split
  all_goals simp

/-- `decode` accepts, as the command `c`, exactly the packed tokens of an object whose members are
the fields of `c` in some order. -/
theorem decode_ok_iff (packed : String) (c : Command) :
    decode packed = .ok c ↔
      ∃ lexemes ms, unpack packed = some lexemes ∧ object lexemes = some ms ∧
        ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  rw [decode_eq]
  cases hu : unpack packed with
  | none => simp
  | some lexemes =>
    simp only [decodeObject]
    cases h : object lexemes with
    | none => simp [h]
    | some ms => simp [h, decodeMembers_ok_iff]

/-- `decode` decides on the members `object` gives for the tokens a packed text unpacks to,
refuses tokens without members as no command and a text that no list of tokens packs to as no
JSON. -/
theorem decode_spec (packed : String) :
    decode packed =
      match unpack packed with
      | some lexemes =>
        match object lexemes with
        | some ms => decodeMembers ms
        | none => .error .notCommand
      | none => .error .notJson := decode_eq packed

/-- A text that no list of tokens packs to is refused as no JSON. -/
theorem decode_malformed {packed : String} (h : unpack packed = none) :
    decode packed = .error .notJson := by
  rw [decode_spec, h]

/-- `notJson` is the refusal of the texts that no list of tokens packs to, and of no other. -/
theorem decode_notJson_iff (packed : String) :
    decode packed = .error .notJson ↔ ∀ lexemes, packed ≠ pack lexemes := by
  rw [decode_spec]
  constructor
  · intro h lexemes hp
    rw [hp, unpack_pack] at h
    simp only at h
    split at h
    · exact absurd h (decodeMembers_ne_notJson _)
    · cases h
  · intro h
    cases hu : unpack packed with
    | none => rfl
    | some lexemes => exact absurd (unpack_some hu) (h lexemes)

/-- Tokens that are not those of an object whose values are values by themselves are no command. -/
theorem decode_not_object {lexemes : List Lexeme} (h : object lexemes = none) :
    decode (pack lexemes) = .error .notCommand := by
  rw [decode_spec, unpack_pack]
  simp [h]

/-- The packed tokens of an object decode as its members. -/
theorem decode_object (ms : List (String × Lexeme)) :
    decode (pack (objectLexemes ms)) =
      match scalars ms with
      | some xs => decodeMembers xs
      | none => .error .notCommand := by
  rw [decode_spec, unpack_pack]
  simp only [object_objectLexemes]

/-- An object without the member `cmd` is refused as that, and no other. -/
theorem decodeMembers_missingCmd_iff (ms : List (String × Scalar)) :
    decodeMembers ms = .error .missingCmd ↔ ms.lookup "cmd" = none := by
  unfold decodeMembers
  cases h : ms.lookup "cmd" with
  | none => simp
  | some v =>
    simp only [reduceCtorEq, iff_false]
    repeat' split
    all_goals simp_all

/-- The operations by their names. -/
theorem opNamed_spec (l : String) :
    opNamed l = [Op.add, .sub, .mul, .div].find? fun op => opName op = l := by
  unfold opNamed
  simp only [List.find?_cons, List.find?_nil]
  repeat' split
  all_goals simp_all [eq_comm, opName]

/-- Whether a member looked up is there and is not a number below 2^64 in decimal digits. -/
def notNum : Option Scalar → Bool
  | some (.num _) => false
  | some _ => true
  | none => false

/-- Whether a member looked up is a string that names an operation. -/
def namesOp : Option Scalar → Bool
  | some (.str o) => ([Op.add, .sub, .mul, .div].find? fun op => opName op = o).isSome
  | _ => false

/-- `badValue` is the refusal of the objects of 2 members with `"cmd":"set"` whose `value` is
not a number below 2^64 in decimal digits, and of no other. -/
theorem decodeMembers_badValue_iff (ms : List (String × Scalar)) :
    decodeMembers ms = .error .badValue ↔
      ms.lookup "cmd" = some (.str "set") ∧ ms.length = 2 ∧
        notNum (ms.lookup "value") = true := by
  unfold decodeMembers
  repeat' split
  all_goals simp_all [notNum, -List.lookup_eq_none_iff]

/-- `badArg` is the refusal of the objects of 3 members with `"cmd":"apply"` and an `op` that
names an operation whose `arg` is not a number below 2^64 in decimal digits, and of no other. -/
theorem decodeMembers_badArg_iff (ms : List (String × Scalar)) :
    decodeMembers ms = .error .badArg ↔
      ms.lookup "cmd" = some (.str "apply") ∧
        ms.length = 3 ∧ namesOp (ms.lookup "op") = true ∧
        notNum (ms.lookup "arg") = true := by
  unfold decodeMembers
  repeat' split
  all_goals first
    | (simp_all [notNum, namesOp, ← opNamed_spec, -List.lookup_eq_none_iff]; done)
    | (rename_i hx
       refine ⟨fun h => by simp at h, ?_⟩
       rintro ⟨-, -, hop, harg⟩
       exfalso
       cases ho : List.lookup "op" ms with
       | none => simp [ho, namesOp] at hop
       | some v =>
         cases v with
         | str o =>
           cases ha : List.lookup "arg" ms with
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

/-- A request with a token that has not expired and a body the JSON library read: the command
its tokens decode to, for the principal the token claims, or 400 with the message of
the refusal. -/
theorem request_json {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64)
    (packed : String) :
    request tenant user exp now (.json packed) =
      match decode packed with
      | .ok cmd => .ok ⟨⟨tenant, user⟩, cmd⟩
      | .error e => .error (Http.refuse 400 (refusalMessage e)) := by
  simp only [request, Http.admit_json h]
  cases decode packed <;> rfl

/-- A request with a token that has not expired and a body without tokens. -/
theorem request_not_json {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64) :
    request tenant user exp now .notJson = .error (Http.refuse 400 "body is not JSON") ∧
      request tenant user exp now .tooLarge = .error (Http.refuse 413 "request body too large") ∧
      request tenant user exp now .unreadable =
        .error (Http.refuse 400 "request body cannot be read") := by
  obtain ⟨h1, h2, h3⟩ := Http.admit_not_json h
  simp [request, h1, h2, h3]

/-- A request with a token that has not expired and a body whose tokens are those of the JSON
value that spells the command `c` gives the engine `c` for the principal of the token's tenant and
user. -/
theorem request_encode {exp now : UInt64} (h : ¬exp < now) (tenant user : UInt64)
    (c : Command) :
    request tenant user exp now (.json (pack (lexemesOf c))) = .ok ⟨⟨tenant, user⟩, c⟩ := by
  rw [request_json h, decode_encode c]

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
    | json packed =>
      rw [request_json he] at h
      cases hd : decode packed with
      | ok cmd => simp [hd] at h
      | error e =>
        simp only [hd, Except.error.injEq] at h
        subst h
        exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | notJson =>
      rw [(request_not_json he tenant user).1] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | tooLarge =>
      rw [(request_not_json he tenant user).2.1] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩
    | unreadable =>
      rw [(request_not_json he tenant user).2.2] at h
      cases h
      exact ⟨by simp [Http.refuse_status], _, Http.refuse_body _ _⟩

/-- `answerOf` gives the answer of `request` and nothing for a call. -/
theorem answerOf_spec (r : Except Http.Response Call) :
    answerOf r =
      match r with
      | .ok _ => none
      | .error answer => some answer := by
  cases r <;> rfl

theorem answerOf_error (answer : Http.Response) : answerOf (.error answer) = some answer := rfl

theorem answerOf_refuse (status : UInt16) (message : String) :
    answerOf (.error (Http.refuse status message)) = some (Http.refuse status message) := rfl

theorem answerOf_ok (call : Call) : answerOf (.ok call) = none := rfl

/-- `actorOf` and `cmdOf` give the principal and the command of a call. -/
theorem call_spec (call : Call) : actorOf (.ok call) = call.actor ∧ cmdOf (.ok call) = call.cmd :=
  ⟨rfl, rfl⟩

/-- When `request` gives a call, `answerOf` gives no answer and `actorOf` and `cmdOf` give the
principal and the command of that call. -/
theorem request_call {tenant user exp now : UInt64} {body : Http.Body} {call : Call}
    (h : request tenant user exp now body = .ok call) :
    answerOf (request tenant user exp now body) = none ∧
      actorOf (request tenant user exp now body) = call.actor ∧
      cmdOf (request tenant user exp now body) = call.cmd := by
  rw [h]
  exact ⟨rfl, rfl, rfl⟩

/-- When `request` gives an answer, `answerOf` gives it. -/
theorem request_answer {tenant user exp now : UInt64} {body : Http.Body} {r : Http.Response}
    (h : request tenant user exp now body = .error r) :
    answerOf (request tenant user exp now body) = some r := by
  rw [h]
  rfl

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
