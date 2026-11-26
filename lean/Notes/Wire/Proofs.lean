import Notes.Wire
import Leangage.Http.Proofs
import Leangage.Json.Read.Proofs

/-!
# What the notes' functions on the wire guarantee

- `decode_encode`: a body whose bytes are `Value.print` of `encodeCommand c`, the JSON value that
  spells the command `c`, decodes to `c`. So every command has a spelling the server accepts.
- `decode_ok_iff`, `decodeItems_ok_iff`, `decodeMembers_ok_iff`: a body decodes to `c` exactly
  when it reads as the items of an object with as many members as `c` has fields (`fields c`,
  the members of `encodeCommand c`) and with each field among them. The members may come in any
  order; an object with another member, a member twice or a member whose value is an array or an
  object is refused. The body of `put_note` is the text whose UTF-8 is the bytes of the string
  read (`textOf_bytesOf`, `textOf_some`).
- `decode_notJson_iff`: `notJson` is the refusal of the bodies `readString` refuses, and of no
  other. `decodeMembers_missingCmd_iff`: `missingCmd` is the refusal of the objects without a
  member `cmd`. `decodeMembers_notCommand_iff`: `notCommand` is the refusal of the objects with a
  member `cmd` whose members are the fields of no command. `refusalMessage_spec` gives the
  message of each refusal.
- `request_expired`, `request_text`, `request_not_text`: a request whose token has expired is
  answered 401 `token expired` whatever its body; otherwise a body of text gives the command it
  decodes to for the principal of the token's organization and user (`request_actor`), or 400
  with the message of the refusal, and a body that is not text is answered 400 or 413.
  `request_encode` states the accepted case for the spelling of a command, and
  `request_refusal` that every answer of `request` has the status 400, 401 or 413 and a body
  `{"error": message}`.
- `respond_ok`, `encodeReply_spec`: an accepted command is answered 200 with `Value.print` of
  `replyValue`. `respond_error`: a refused one is answered with `refusalStatus` (403 for the
  guard's refusal, 404 for `notFound`, 422 for `badText`) and `{"error": name}` with
  `refusalName`.
- `decodeReply_encodeReply`, `decodeReply_print`, `decodeReplyItems_value`: the bytes
  `encodeReply` writes for a reply, which an engine stores under an idempotency key, are read
  back by `decodeReply` as that reply.
- `fingerprint_spec`: the fingerprint of a command is the text `fingerprintText` gives, such as
  `PutNote { id: 7, body: "text", shared: true }` with the body escaped as in a JSON string.
  `fingerprint_injective`: different commands have different fingerprints, so an idempotency key
  used with another command is recognised.
- `scope_spec`, `scope_injective`: the scope of a principal is `u` and its user in decimal, and
  two principals have the same scope exactly when they have the same user.
-/

namespace Notes.Wire

open Notes.Kernel Leangage
open Leangage.Authz (Guarded)
open Leangage.Json (Value ascii)
open Leangage.Json.Read (Item readString readString_print)
open Leangage.Token (bytesOf)

/-! ## Text -/

/-- The bytes of a text are read back as the text. -/
theorem textOf_bytesOf (s : String) : textOf (bytesOf s) = some s := by
  have h : s.toByteArray.IsValidUTF8 := s.isValidUTF8
  simp [textOf, bytesOf, String.fromUTF8?, h]
  rfl

/-- `textOf` gives only the text whose UTF-8 is the bytes. -/
theorem textOf_some {bs : List UInt8} {s : String} (h : textOf bs = some s) : bs = bytesOf s := by
  unfold textOf String.fromUTF8? at h
  split at h
  · cases h
    simp [bytesOf]
    rfl
  · cases h

theorem bytesOf_injective {s t : String} (h : bytesOf s = bytesOf t) : s = t := by
  have hs := textOf_bytesOf s
  rw [h, textOf_bytesOf] at hs
  exact (Option.some.inj hs).symm

theorem name_cmd : ascii ['c', 'm', 'd'] = [99, 109, 100] := rfl
theorem name_add_member : ascii ['a', 'd', 'd', '_', 'm', 'e', 'm', 'b', 'e', 'r'] = [97, 100, 100, 95,
  109, 101, 109, 98, 101, 114] := rfl
theorem name_remove_member : ascii ['r', 'e', 'm', 'o', 'v', 'e', '_', 'm', 'e', 'm', 'b', 'e',
  'r'] = [114, 101, 109, 111, 118, 101, 95, 109, 101, 109, 98, 101, 114] := rfl
theorem name_put_note : ascii ['p', 'u', 't', '_', 'n', 'o', 't', 'e'] = [112, 117, 116, 95, 110, 111, 116,
  101] := rfl
theorem name_delete_note : ascii ['d', 'e', 'l', 'e', 't', 'e', '_', 'n', 'o', 't', 'e'] = [100, 101, 108,
  101, 116, 101, 95, 110, 111, 116, 101] := rfl
theorem name_read_note : ascii ['r', 'e', 'a', 'd', '_', 'n', 'o', 't', 'e'] = [114, 101, 97, 100, 95, 110,
  111, 116, 101] := rfl
theorem name_list_notes : ascii ['l', 'i', 's', 't', '_', 'n', 'o', 't', 'e', 's'] = [108, 105, 115, 116,
  95, 110, 111, 116, 101, 115] := rfl
theorem name_list_members : ascii ['l', 'i', 's', 't', '_', 'm', 'e', 'm', 'b', 'e', 'r', 's'] = [108, 105,
  115, 116, 95, 109, 101, 109, 98, 101, 114, 115] := rfl
theorem name_user : ascii ['u', 's', 'e', 'r'] = [117, 115, 101, 114] := rfl
theorem name_admin : ascii ['a', 'd', 'm', 'i', 'n'] = [97, 100, 109, 105, 110] := rfl
theorem name_id : ascii ['i', 'd'] = [105, 100] := rfl
theorem name_body : ascii ['b', 'o', 'd', 'y'] = [98, 111, 100, 121] := rfl
theorem name_shared : ascii ['s', 'h', 'a', 'r', 'e', 'd'] = [115, 104, 97, 114, 101, 100] := rfl
theorem name_owner : ascii ['o', 'w', 'n', 'e', 'r'] = [111, 119, 110, 101, 114] := rfl
theorem name_done : ascii ['d', 'o', 'n', 'e'] = [100, 111, 110, 101] := rfl
theorem name_note : ascii ['n', 'o', 't', 'e'] = [110, 111, 116, 101] := rfl
theorem name_notes : ascii ['n', 'o', 't', 'e', 's'] = [110, 111, 116, 101, 115] := rfl
theorem name_members : ascii ['m', 'e', 'm', 'b', 'e', 'r', 's'] = [109, 101, 109, 98, 101, 114, 115] := rfl

/-! ## Commands -/

/-- The JSON value that spells a command. -/
def encodeCommand : Command → Value
  | .addMember user admin =>
    .obj [(ascii ['c', 'm', 'd'], .str (ascii ['a', 'd', 'd', '_', 'm', 'e', 'm', 'b', 'e', 'r'])),
      (ascii ['u', 's', 'e', 'r'], .num user), (ascii ['a', 'd', 'm', 'i', 'n'], .bool admin)]
  | .removeMember user => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['r', 'e', 'm', 'o', 'v', 'e', '_',
    'm', 'e', 'm', 'b', 'e', 'r'])), (ascii ['u', 's', 'e', 'r'], .num user)]
  | .putNote id body shared =>
    .obj [(ascii ['c', 'm', 'd'], .str (ascii ['p', 'u', 't', '_', 'n', 'o', 't', 'e'])), (ascii ['i',
      'd'], .num id), (ascii ['b', 'o', 'd', 'y'], .str (bytesOf body)),
      (ascii ['s', 'h', 'a', 'r', 'e', 'd'], .bool shared)]
  | .deleteNote id => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['d', 'e', 'l', 'e', 't', 'e', '_', 'n',
    'o', 't', 'e'])), (ascii ['i', 'd'], .num id)]
  | .readNote id => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['r', 'e', 'a', 'd', '_', 'n', 'o', 't',
    'e'])), (ascii ['i', 'd'], .num id)]
  | .listNotes => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['l', 'i', 's', 't', '_', 'n', 'o', 't', 'e',
    's']))]
  | .listMembers => .obj [(ascii ['c', 'm', 'd'], .str (ascii ['l', 'i', 's', 't', '_', 'm', 'e', 'm', 'b',
    'e', 'r', 's']))]

/-- The members of the object that spells a command, as they are read. -/
def fields : Command → List (List UInt8 × Item)
  | .addMember user admin =>
    [(ascii ['c', 'm', 'd'], .str (ascii ['a', 'd', 'd', '_', 'm', 'e', 'm', 'b', 'e', 'r'])), (ascii ['u',
      's', 'e', 'r'], .num user), (ascii ['a', 'd', 'm', 'i', 'n'], .bool admin)]
  | .removeMember user => [(ascii ['c', 'm', 'd'], .str (ascii ['r', 'e', 'm', 'o', 'v', 'e', '_', 'm',
    'e', 'm', 'b', 'e', 'r'])), (ascii ['u', 's', 'e', 'r'], .num user)]
  | .putNote id body shared =>
    [(ascii ['c', 'm', 'd'], .str (ascii ['p', 'u', 't', '_', 'n', 'o', 't', 'e'])), (ascii ['i', 'd'],
      .num id), (ascii ['b', 'o', 'd', 'y'], .str (bytesOf body)),
      (ascii ['s', 'h', 'a', 'r', 'e', 'd'], .bool shared)]
  | .deleteNote id => [(ascii ['c', 'm', 'd'], .str (ascii ['d', 'e', 'l', 'e', 't', 'e', '_', 'n', 'o',
    't', 'e'])), (ascii ['i', 'd'], .num id)]
  | .readNote id => [(ascii ['c', 'm', 'd'], .str (ascii ['r', 'e', 'a', 'd', '_', 'n', 'o', 't', 'e'])),
    (ascii ['i', 'd'], .num id)]
  | .listNotes => [(ascii ['c', 'm', 'd'], .str (ascii ['l', 'i', 's', 't', '_', 'n', 'o', 't', 'e', 's']))]
  | .listMembers => [(ascii ['c', 'm', 'd'], .str (ascii ['l', 'i', 's', 't', '_', 'm', 'e', 'm', 'b', 'e',
    'r', 's']))]

/-- The items of an object with the given members. -/
def objectItems (ms : List (List UInt8 × Item)) : List Item :=
  .objOpen :: (ms.flatMap (fun m => [.key m.1, m.2]) ++ [.objClose])

theorem encodeCommand_items (c : Command) :
    (encodeCommand c).toks.map Item.ofTok = objectItems (fields c) := by
  cases c <;> rfl

theorem decodeMembers_fields (c : Command) : decodeMembers (fields c) = .ok c := by
  cases c <;> simp [fields, decodeMembers, name_cmd, name_add_member, name_remove_member, name_put_note,
    name_delete_note, name_read_note, name_list_notes, name_list_members, name_user, name_admin, name_id,
    name_body, name_shared, textOf_bytesOf, List.lookup]

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

/-- A member that is the only one with its key is the one looked up. -/
theorem lookup_unique {k : List UInt8} {v : Item} :
    ∀ {ms : List (List UInt8 × Item)}, (k, v) ∈ ms → (∀ v', (k, v') ∈ ms → v' = v) →
      ms.lookup k = some v
  | [], h, _ => by cases h
  | (k', v') :: ms, h, hu => by
    rw [List.lookup_cons]
    by_cases hk : k = k'
    · subst hk
      simp only [beq_self_eq_true]
      rw [hu v' (List.mem_cons_self ..)]
    · have : (k == k') = false := by simpa using hk
      simp only [this]
      refine lookup_unique ?_ fun v'' h'' => hu v'' (List.mem_cons_of_mem _ h'')
      rcases List.mem_cons.mp h with h | h
      · cases h
        exact absurd rfl hk
      · exact h

/-- A list as long as a list without repetition that holds each element of it holds no other. -/
theorem subset_of_length {α : Type} :
    ∀ {fs ms : List α}, fs.Nodup → ms.length = fs.length → (∀ f ∈ fs, f ∈ ms) → ∀ m ∈ ms, m ∈ fs
  | [], ms, _, hl, _ => by
    cases ms with
    | nil => simp
    | cons m ms => simp at hl
  | f :: fs, ms, hn, hl, hm => by
    obtain ⟨a, b, rfl⟩ := List.append_of_mem (hm f (List.mem_cons_self ..))
    have hn' := List.nodup_cons.mp hn
    have ih := subset_of_length (fs := fs) (ms := a ++ b) hn'.2
      (by simp only [List.length_append, List.length_cons] at hl ⊢; omega)
      (by
        intro g hg
        have hne : g ≠ f := fun h => hn'.1 (h ▸ hg)
        have := hm g (List.mem_cons_of_mem _ hg)
        simp only [List.mem_append, List.mem_cons] at this ⊢
        rcases this with h | h | h
        · exact Or.inl h
        · exact absurd h hne
        · exact Or.inr h)
    intro m hm'
    simp only [List.mem_append, List.mem_cons] at hm' ⊢
    rcases hm' with h | h | h
    · exact Or.inr (ih m (List.mem_append.mpr (Or.inl h)))
    · exact Or.inl h
    · exact Or.inr (ih m (List.mem_append.mpr (Or.inr h)))

/-- The fields of a command have different keys. -/
theorem fields_keys (c : Command) : (fields c).Pairwise fun m m' => m.1 ≠ m'.1 := by
  cases c <;> simp [fields, name_cmd, name_add_member, name_remove_member, name_put_note, name_delete_note,
    name_read_note, name_list_notes, name_list_members, name_user, name_admin, name_id, name_body,
    name_shared]

theorem fields_nodup (c : Command) : (fields c).Nodup :=
  (fields_keys c).imp fun h e => h (congrArg Prod.fst e)

theorem fields_key_unique (c : Command) {m m' : List UInt8 × Item} (hm : m ∈ fields c)
    (hm' : m' ∈ fields c) (hk : m.1 = m'.1) : m = m' := by
  rcases List.mem_iff_getElem.mp hm with ⟨i, hi, rfl⟩
  rcases List.mem_iff_getElem.mp hm' with ⟨j, hj, rfl⟩
  have hp := List.pairwise_iff_getElem.mp (fields_keys c)
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · exact absurd hk (hp i j hi hj hij)
  · subst hij
    rfl
  · exact absurd hk.symm (hp j i hj hi hij)

/-- An object with as many members as a command has fields, which has each of them, has no
other member. -/
theorem members_subset {ms : List (List UInt8 × Item)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) : ∀ m ∈ ms, m ∈ fields c :=
  subset_of_length (fields_nodup c) hl hm

/-- In such an object, the field of each key is the member looked up. -/
theorem lookup_field {ms : List (List UInt8 × Item)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) :
    ∀ m ∈ fields c, ms.lookup m.1 = some m.2 := by
  intro m hmf
  refine lookup_unique (hm m hmf) fun v' hv' => ?_
  have := fields_key_unique c (members_subset hl hm _ hv') hmf rfl
  exact congrArg Prod.snd this

/-- `decodeMembers` accepts, as the command `c`, exactly the members that are the fields of `c`
in some order: as many as `c` has fields, with each field among them. -/
theorem decodeMembers_ok_iff (ms : List (List UInt8 × Item)) (c : Command) :
    decodeMembers ms = .ok c ↔ ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  constructor
  · intro h
    unfold decodeMembers at h
    repeat' split at h
    all_goals try cases h
    all_goals subst_vars
    all_goals try (have hb := textOf_some ‹textOf _ = some _›; subst hb)
    all_goals refine ⟨by assumption, ?_⟩
    all_goals simp only [fields, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true, name_cmd, name_add_member, name_remove_member, name_put_note, name_delete_note,
        name_read_note, name_list_notes, name_list_members, name_user, name_admin, name_id, name_body,
        name_shared]
    all_goals and_intros
    all_goals (apply lookup_mem; assumption)
  · rintro ⟨hl, hm⟩
    have hk := lookup_field hl hm
    cases c <;>
      simp only [fields, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true, name_cmd, name_add_member, name_remove_member, name_put_note, name_delete_note,
          name_read_note, name_list_notes, name_list_members, name_user, name_admin, name_id, name_body,
          name_shared, List.length_cons, List.length_nil] at hk hl <;>
      simp [decodeMembers, hk, hl, textOf_bytesOf]

/-- A JSON text that spells a command decodes to it. -/
theorem decode_encode {s : String} (c : Command) (h : bytesOf s = (encodeCommand c).print) :
    decode s = .ok c := by
  rw [decode, readString_print h, encodeCommand_items]
  cases c <;> simp [objectItems, fields, decodeItems, members, scalar, decodeMembers, name_cmd,
    name_add_member, name_remove_member, name_put_note, name_delete_note, name_read_note, name_list_notes,
    name_list_members, name_user, name_admin, name_id, name_body, name_shared,
    textOf_bytesOf, List.lookup]

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
  unfold decode
  cases h : readString body with
  | none => simp
  | some items =>
    simp only [decodeItems_ok_iff, Option.some.injEq]

theorem decodeMembers_ne_notJson (ms : List (List UInt8 × Item)) :
    decodeMembers ms ≠ .error .notJson := by
  unfold decodeMembers
  repeat' split
  all_goals simp

/-- A body that is not a JSON text is refused as that. -/
theorem decode_notJson_iff (body : String) :
    decode body = .error .notJson ↔ readString body = none := by
  unfold decode
  cases h : readString body with
  | none => simp
  | some items =>
    simp only [reduceCtorEq, iff_false]
    unfold decodeItems
    split
    · split
      · exact decodeMembers_ne_notJson _
      · simp
    · simp

/-- An object without the member `cmd` is refused as that, and no other. -/
theorem decodeMembers_missingCmd_iff (ms : List (List UInt8 × Item)) :
    decodeMembers ms = .error .missingCmd ↔ ms.lookup (ascii ['c', 'm', 'd']) = none := by
  unfold decodeMembers
  rw [name_cmd]
  cases h : ms.lookup [99, 109, 100] with
  | none => simp
  | some v =>
    simp only [reduceCtorEq, iff_false]
    repeat' split
    all_goals simp_all

/-- `notCommand` is the refusal of the objects with a member `cmd` whose members are the fields
of no command. -/
theorem decodeMembers_notCommand_iff (ms : List (List UInt8 × Item)) :
    decodeMembers ms = .error .notCommand ↔
      ms.lookup (ascii ['c', 'm', 'd']) ≠ none ∧
        ∀ c, ¬(ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms) := by
  simp only [← decodeMembers_ok_iff, ne_eq, ← decodeMembers_missingCmd_iff ms]
  cases h : decodeMembers ms with
  | ok c => simp
  | error e =>
    cases e with
    | notJson => exact absurd h (decodeMembers_ne_notJson ms)
    | notCommand => simp
    | missingCmd => simp

/-- The items of an object whose members are values by themselves decode as its members. -/
theorem decodeItems_object (ms : List (List UInt8 × Item)) (hs : ∀ m ∈ ms, isScalar m.2 = true) :
    decodeItems (objectItems ms) = decodeMembers ms := by
  have hs : ∀ m ∈ ms, scalar m.2 = true := fun m h => (scalar_spec m.2).trans (hs m h)
  simp only [decodeItems, objectItems, members_flat ms hs [], List.reverse_nil, List.nil_append]

/-- The items of the object that spells a command decode to it. -/
theorem decodeItems_fields (c : Command) : decodeItems (objectItems (fields c)) = .ok c := by
  rw [decodeItems_object _ fun m h => (scalar_spec m.2).symm.trans (fields_scalar c m h),
    decodeMembers_fields]

/-- The message of each refusal. -/
theorem refusalMessage_spec (e : Refusal) :
    (refusalMessage e).toList =
      match e with
      | .notJson => "body is not JSON".toList
      | .notCommand => "not a notes command".toList
      | .missingCmd => "missing field `cmd`".toList := by
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
the engine `c` for the principal of the token's organization and user. -/
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

/-- The principal `request` gives the engine is the organization and the user it was given. -/
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

/-- The JSON value of a note: `{"body":"text","id":7,"owner":1,"shared":true}`. -/
def noteValue (n : Note) : Value :=
  .obj [(ascii ['b', 'o', 'd', 'y'], .str (bytesOf n.body)), (ascii ['i', 'd'], .num n.id), (ascii ['o',
    'w', 'n', 'e', 'r'], .num n.owner),
    (ascii ['s', 'h', 'a', 'r', 'e', 'd'], .bool n.shared)]

/-- The JSON value of a member: `{"admin":false,"user":2}`. -/
def memberValue (m : Member) : Value :=
  .obj [(ascii ['a', 'd', 'm', 'i', 'n'], .bool m.admin), (ascii ['u', 's', 'e', 'r'], .num m.user)]

/-- The JSON value of a reply: `{"done":true}`, `{"note":<note>}`, `{"notes":[<note>,…]}`,
`{"members":[<member>,…]}`. -/
def replyValue : Reply → Value
  | .done => .obj [(ascii ['d', 'o', 'n', 'e'], .bool true)]
  | .found n => .obj [(ascii ['n', 'o', 't', 'e'], noteValue n)]
  | .notes ns => .obj [(ascii ['n', 'o', 't', 'e', 's'], .arr (ns.map noteValue))]
  | .members ms => .obj [(ascii ['m', 'e', 'm', 'b', 'e', 'r', 's'], .arr (ms.map memberValue))]

theorem noteToks_value (n : Note) : (noteToks n).map Json.StrTok.toTok = (noteValue n).toks := by
  simp only [noteToks, noteValue, List.map, Json.StrTok.toTok, Value.toks, Json.membersToks]
  congr

theorem memberToks_value (m : Member) : (memberToks m).map Json.StrTok.toTok = (memberValue m).toks := by
  simp only [memberToks, memberValue, List.map, Json.StrTok.toTok, Value.toks, Json.membersToks]
  congr

theorem notes_elems (ns : List Note) :
    (ns.flatMap noteToks).map Json.StrTok.toTok = Json.elemsToks (ns.map noteValue) := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [Json.elemsToks, noteToks_value, ih]

theorem members_elems (ms : List Member) :
    (ms.flatMap memberToks).map Json.StrTok.toTok = Json.elemsToks (ms.map memberValue) := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp [Json.elemsToks, memberToks_value, ih]

theorem replyToks_value (r : Reply) : (replyToks r).map Json.StrTok.toTok = (replyValue r).toks := by
  cases r with
  | done =>
    simp only [replyToks, replyValue, List.map, Json.StrTok.toTok, Value.toks, Json.membersToks]
    congr
  | found n =>
    simp only [replyToks, replyValue, List.map_cons, List.map_append, List.map_nil, Json.StrTok.toTok,
      Value.toks, Json.membersToks, noteToks_value, List.append_nil]
    congr
  | notes ns =>
    simp only [replyToks, replyValue, List.map_cons, List.map_append, List.map_nil, Json.StrTok.toTok,
      Value.toks, Json.membersToks, notes_elems, List.append_nil]
    simp
    rfl
  | members ms =>
    simp only [replyToks, replyValue, List.map_cons, List.map_append, List.map_nil, Json.StrTok.toTok,
      Value.toks, Json.membersToks, members_elems, List.append_nil]
    simp
    rfl

/-- The bytes of a reply are its JSON value. -/
theorem encodeReply_spec (r : Reply) : (encodeReply r).toList = (replyValue r).print :=
  Json.writeArray_value (replyToks_value r)

/-- An accepted command is answered 200 with the JSON value of its reply. -/
theorem respond_ok (r : Reply) :
    (respond (.ok r)).status = 200 ∧ (respond (.ok r)).body.toList = (replyValue r).print :=
  ⟨rfl, encodeReply_spec r⟩

/-- The status of a refusal: 403 for the guard's, 404 and 422 for the kernel's. -/
def refusalStatus : Guarded Error → UInt16
  | .denied => 403
  | .app .notFound => 404
  | .app .badText => 422

/-- The name of a refusal. -/
def refusalName : Guarded Error → String
  | .denied => "denied"
  | .app .notFound => "not_found"
  | .app .badText => "bad_text"

/-- A refused command is answered with the status of its refusal and `{"error": name}`. -/
theorem respond_error (e : Guarded Error) :
    (respond (.error e)).status = refusalStatus e ∧
      (respond (.error e)).body.toList = (Http.errorValue (refusalName e)).print := by
  cases e with
  | denied => exact ⟨rfl, Http.refuse_body _ _⟩
  | app e => cases e <;> exact ⟨rfl, Http.refuse_body _ _⟩

/-! ## Stored replies -/

theorem noteOf_note (n : Note) :
    noteOf (ascii ['b', 'o', 'd', 'y']) (bytesOf n.body) (ascii ['i', 'd']) n.id (ascii ['o', 'w', 'n',
      'e', 'r']) n.owner (ascii ['s', 'h', 'a', 'r', 'e', 'd']) n.shared = some n := by
  simp [noteOf, name_body, name_id, name_owner, name_shared, textOf_bytesOf]

theorem notesItems_elems (ns : List Note) (acc : List Note) :
    notesItems acc ((Json.elemsToks (ns.map noteValue)).map Item.ofTok ++ [.arrClose, .objClose]) =
      some (acc.reverse ++ ns) := by
  induction ns generalizing acc with
  | nil => simp [Json.elemsToks, notesItems]
  | cons n ns ih =>
    simp [Json.elemsToks, noteValue, Value.toks, Json.membersToks, Item.ofTok, notesItems, noteOf_note, ih]

theorem membersItems_elems (ms : List Member) (acc : List Member) :
    membersItems acc ((Json.elemsToks (ms.map memberValue)).map Item.ofTok ++ [.arrClose, .objClose]) =
      some (acc.reverse ++ ms) := by
  induction ms generalizing acc with
  | nil => simp [Json.elemsToks, membersItems]
  | cons m ms ih =>
    simp [Json.elemsToks, memberValue, Value.toks, Json.membersToks, Item.ofTok, membersItems, name_admin,
      name_user, ih]

/-- The items of the JSON value of a reply are read back as the reply. -/
theorem decodeReplyItems_value (r : Reply) :
    decodeReplyItems ((replyValue r).toks.map Item.ofTok) = some r := by
  cases r with
  | done => simp [replyValue, Value.toks, Json.membersToks, Item.ofTok, decodeReplyItems, name_done]
  | found n =>
    simp [replyValue, noteValue, Value.toks, Json.membersToks, Item.ofTok, decodeReplyItems, name_note,
      noteOf_note]
  | notes ns =>
    have := notesItems_elems ns []
    simp_all [replyValue, Value.toks, Json.membersToks, Item.ofTok, decodeReplyItems, name_notes]
  | members ms =>
    have := membersItems_elems ms []
    simp_all [replyValue, Value.toks, Json.membersToks, Item.ofTok, decodeReplyItems, name_members]

/-- A text whose bytes are the JSON value of a reply is read back as the reply. -/
theorem decodeReply_print {s : String} (r : Reply) (h : bytesOf s = (replyValue r).print) :
    decodeReply s = some r := by
  simp only [decodeReply, readString_print h, decodeReplyItems_value]

/-- The bytes `encodeReply` writes for a reply are read back as the reply. -/
theorem decodeReply_encodeReply {s : String} (r : Reply) (h : bytesOf s = (encodeReply r).toList) :
    decodeReply s = some r :=
  decodeReply_print r (h.trans (encodeReply_spec r))

/-! ## Idempotency keys -/

/-- `true` or `false`. -/
def flagText : Bool → List Char
  | true => "true".toList
  | false => "false".toList

/-- The text of a fingerprint: `AddMember { user: 2, admin: false }`,
`RemoveMember { user: 2 }`, `PutNote { id: 7, body: "text", shared: true }` with the body escaped
as in a JSON string, `DeleteNote { id: 7 }`, `ReadNote { id: 7 }`, `ListNotes`, `ListMembers`. -/
def fingerprintText : Command → List UInt8
  | .addMember user admin =>
    ascii "AddMember { user: ".toList ++ Json.digits user.toNat ++ ascii ", admin: ".toList ++
      ascii (flagText admin) ++ ascii " }".toList
  | .removeMember user => ascii "RemoveMember { user: ".toList ++ Json.digits user.toNat ++ ascii " }".toList
  | .putNote id body shared =>
    ascii "PutNote { id: ".toList ++ Json.digits id.toNat ++ ascii ", body: \"".toList ++
      Json.esc (bytesOf body) ++ ascii "\", shared: ".toList ++ ascii (flagText shared) ++ ascii " }".toList
  | .deleteNote id => ascii "DeleteNote { id: ".toList ++ Json.digits id.toNat ++ ascii " }".toList
  | .readNote id => ascii "ReadNote { id: ".toList ++ Json.digits id.toNat ++ ascii " }".toList
  | .listNotes => ascii "ListNotes".toList
  | .listMembers => ascii "ListMembers".toList

/-- The bytes of a fingerprint are its text. -/
theorem fingerprint_spec (c : Command) : (fingerprint c).toList = fingerprintText c := by
  cases c with
  | addMember user admin =>
    cases admin <;>
      simp [fingerprint, pushFlag, fingerprintText, flagText, Json.pushDecimal_spec, Json.decimal_spec, ascii]
  | removeMember user => simp [fingerprint, fingerprintText, Json.pushDecimal_spec, Json.decimal_spec, ascii]
  | putNote id body shared =>
    cases shared <;>
      simp [fingerprint, pushFlag, fingerprintText, flagText, Json.pushDecimal_spec, Json.decimal_spec,
        Json.pushEscaped_spec, Json.escape_spec, ascii]
  | deleteNote id => simp [fingerprint, fingerprintText, Json.pushDecimal_spec, Json.decimal_spec, ascii]
  | readNote id => simp [fingerprint, fingerprintText, Json.pushDecimal_spec, Json.decimal_spec, ascii]
  | listNotes => rfl
  | listMembers => rfl

theorem digits_injective {n m : Nat} (h : Json.digits n = Json.digits m) : n = m := by
  rw [← Json.decimal_spec, ← Json.decimal_spec] at h
  have := congrArg Token.value h
  rwa [Token.value_decimal, Token.value_decimal] at this

/-- Two lists that start with bytes of one kind, each followed by a byte of another kind, are
equal only when the starts are and what follows is. -/
theorem prefix_unique (p : UInt8 → Bool) :
    ∀ {l l' : List UInt8} {c c' : UInt8} {r r' : List UInt8}, (∀ x ∈ l, p x = true) →
      (∀ x ∈ l', p x = true) → p c = false → p c' = false → l ++ c :: r = l' ++ c' :: r' →
      l = l' ∧ c :: r = c' :: r'
  | [], [], _, _, _, _, _, _, _, _, h => ⟨rfl, h⟩
  | [], y :: l', c, _, _, _, _, hl', hc, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have := hl' y (List.mem_cons_self ..)
    rw [← h.1, hc] at this
    cases this
  | x :: l, [], _, c', _, _, hl, _, _, hc', h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    have := hl x (List.mem_cons_self ..)
    rw [h.1, hc'] at this
    cases this
  | x :: l, y :: l', _, _, _, _, hl, hl', hc, hc', h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨h1, h2⟩ := prefix_unique p (fun z hz => hl z (List.mem_cons_of_mem _ hz))
      (fun z hz => hl' z (List.mem_cons_of_mem _ hz)) hc hc' h.2
    exact ⟨by rw [h.1, h1], h2⟩

/-- A number in decimal followed by a byte that is not a digit: the number and what follows are
read off the bytes. -/
theorem digits_sep {n m : Nat} {c c' : UInt8} {r r' : List UInt8} (hc : Json.Read.isDigit c = false)
    (hc' : Json.Read.isDigit c' = false) (h : Json.digits n ++ c :: r = Json.digits m ++ c' :: r') :
    n = m ∧ c :: r = c' :: r' := by
  have hd : ∀ k, ∀ x ∈ Json.digits k, Json.Read.isDigit x = true := fun k => by
    rw [← Json.decimal_spec]
    exact Json.Read.decimal_isDigit k
  obtain ⟨h1, h2⟩ := prefix_unique _ (hd n) (hd m) hc hc' h
  exact ⟨digits_injective h1, h2⟩

/-- Different commands have different fingerprints. -/
theorem fingerprint_injective {c c' : Command} (h : fingerprint c = fingerprint c') : c = c' := by
  have h' : fingerprintText c = fingerprintText c' := by
    rw [← fingerprint_spec, ← fingerprint_spec, h]
  cases c <;> cases c' <;> first
    | rfl
    | (simp [fingerprintText, ascii] at h'; done)
    | skip
  · rename_i u a u' a'
    simp only [fingerprintText, List.append_assoc] at h'
    have h1 := List.append_cancel_left h'
    have hs : ascii ", admin: ".toList = 44 :: ascii " admin: ".toList := rfl
    rw [hs, List.cons_append, List.cons_append] at h1
    obtain ⟨hu, h2⟩ := digits_sep (by decide) (by decide) h1
    rw [UInt64.toNat_inj.mp hu]
    cases a <;> cases a' <;> first
      | rfl
      | (simp [flagText, ascii] at h2; done)
  · rename_i u u'
    have hd : Json.digits u.toNat = Json.digits u'.toNat := by
      simpa [fingerprintText, List.append_assoc] using h'
    rw [UInt64.toNat_inj.mp (digits_injective hd)]
  · rename_i i b s i' b' s'
    simp only [fingerprintText, List.append_assoc] at h'
    have h1 := List.append_cancel_left h'
    have hs : ascii ", body: \"".toList = 44 :: (ascii " body: ".toList ++ [34]) := rfl
    have hq : ascii "\", shared: ".toList = 34 :: ascii ", shared: ".toList := rfl
    simp only [hs, hq, List.cons_append, List.append_assoc, List.nil_append] at h1
    obtain ⟨hi, h2⟩ := digits_sep (by decide) (by decide) h1
    simp only [List.cons.injEq, true_and] at h2
    have h3 := List.append_cancel_left h2
    simp only [List.cons.injEq, true_and] at h3
    rw [← Json.escape_spec, ← Json.escape_spec] at h3
    have h4 := congrArg Json.lexStr h3
    rw [Json.lex_escape, Json.lex_escape] at h4
    simp only [Option.some.injEq, Prod.mk.injEq] at h4
    rw [UInt64.toNat_inj.mp hi, bytesOf_injective h4.1]
    cases s <;> cases s' <;> first
      | rfl
      | (have := h4.2; simp [flagText, ascii] at this; done)
  · rename_i i i'
    have hd : Json.digits i.toNat = Json.digits i'.toNat := by
      simpa [fingerprintText, List.append_assoc] using h'
    rw [UInt64.toNat_inj.mp (digits_injective hd)]
  · rename_i i i'
    have hd : Json.digits i.toNat = Json.digits i'.toNat := by
      simpa [fingerprintText, List.append_assoc] using h'
    rw [UInt64.toNat_inj.mp (digits_injective hd)]

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

end Notes.Wire
