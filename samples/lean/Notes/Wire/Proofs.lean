import Notes.Wire
import Leangage.Http.Proofs
import Leangage.Json.Lexemes.Proofs

/-!
# What the notes' functions on the wire guarantee

The server's JSON library is trusted to hand over the packed tokens of the text of a body and of a
stored reply (`Leangage.Json.Lexemes.Proofs`); the theorems start from those tokens.

- `decode_encode`: the packed tokens of the JSON text that spells the command `c`
  (`pack (lexemesOf c)`, a number as its decimal) decode to `c`. So every command has a spelling
  the server accepts.
- `decode_ok_iff`, `decodeMembers_ok_iff`: a packed text decodes to `c` exactly when `object`
  gives members for the tokens it unpacks to, as many as `c` has fields (`fields c`) and with
  each field among them. By `object_iff` those are the tokens of an object whose values are not
  arrays or objects. The members may come in any order; an object with another member or a
  member twice is refused. `decode_spec` and `decode_object` give the decision for the tokens of
  any object, and `decode_not_object` the refusal of every other list of tokens.
- `decode_malformed`, `decode_notJson_iff`: `notJson`, answered 400 `body is not JSON`, is the
  refusal of the texts that no list of tokens packs to, and of no other.
- `decodeMembers_missingCmd_iff`: `missingCmd` is the refusal of the objects without a member
  `cmd`. `decodeMembers_notCommand_iff`: `notCommand` is the refusal of the objects with a
  member `cmd` whose members are the fields of no command. `refusalMessage_spec` gives the
  message of each refusal.
- `request_expired`, `request_json`, `request_not_json`: a request whose token has expired is
  answered 401 `token expired` whatever its body; otherwise the tokens of a body give the command
  they decode to for the principal of the token's organization and user
  (`request_actor`), or 400 with the message of the refusal, and a body without tokens is
  answered 400 or 413. `request_encode` states the accepted case for the spelling of a command,
  and `request_refusal` that every answer of `request` has the status 400, 401 or 413 and a body
  `{"error": message}`.
- `respond_ok`, `encodeReply_spec`: an accepted command is answered 200 with `Value.print` of
  `replyValue`. `respond_error`: a refused one is answered with `refusalStatus` (403 for the
  guard's refusal, 404 for `notFound`, 422 for `badText`) and `{"error": name}` with
  `refusalName`.
- `decodeReply_encode`, `replyOf_lexemes`, `decodeReply_spec`: `encodeReply` writes `Value.print`
  of `replyValue r` for a reply, which an engine stores under an idempotency key, and
  `decodeReply` reads the tokens of that text (`(replyToks r).map Lexeme.ofStrTok`, the tokens
  `encodeReply` writes with a number as its decimal) back as `r`.
  `decodeReply_none`: stored bytes the JSON library refuses are no reply.
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
open Leangage.Json.Lexemes
open Leangage.Token (bytesOf)

/-! ## Commands -/

/-- The members of the object that spells a command, as they are read. -/
def fields : Command → List (String × Scalar)
  | .addMember user admin =>
    [("cmd", .str ("add_member")), ("user", .num user), ("admin", .bool admin)]
  | .removeMember user => [("cmd", .str ("remove_member")), ("user", .num user)]
  | .putNote id body shared =>
    [("cmd", .str ("put_note")), ("id",
      .num id), ("body", .str body),
      ("shared", .bool shared)]
  | .deleteNote id => [("cmd", .str ("delete_note")), ("id", .num id)]
  | .readNote id => [("cmd", .str ("read_note")),
    ("id", .num id)]
  | .listNotes => [("cmd", .str ("list_notes"))]
  | .listMembers => [("cmd", .str ("list_members"))]

/-- The members of the object that spells a command, as tokens: a number as its decimal. -/
def lexFields : Command → List (String × Lexeme)
  | .addMember user admin =>
    [("cmd", .str "add_member"), ("user", .number (decimalText user)), ("admin", .bool admin)]
  | .removeMember user => [("cmd", .str "remove_member"), ("user", .number (decimalText user))]
  | .putNote id body shared =>
    [("cmd", .str "put_note"), ("id", .number (decimalText id)), ("body", .str body), ("shared", .bool shared)]
  | .deleteNote id => [("cmd", .str "delete_note"), ("id", .number (decimalText id))]
  | .readNote id => [("cmd", .str "read_note"), ("id", .number (decimalText id))]
  | .listNotes => [("cmd", .str "list_notes")]
  | .listMembers => [("cmd", .str "list_members")]

/-- The tokens of the JSON text that spells a command, such as
`{"cmd":"put_note","id":7,"body":"text","shared":true}`. -/
def lexemesOf (c : Command) : List Lexeme :=
  objectLexemes (lexFields c)

theorem scalars_lexFields (c : Command) : scalars (lexFields c) = some (fields c) := by
  cases c <;> simp [lexFields, fields, scalars, scalarOf, numberOf_decimalText]

theorem decodeMembers_fields (c : Command) : decodeMembers (fields c) = .ok c := by
  cases c <;> simp [fields, decodeMembers, List.lookup]

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

/-- A member that is the only one with its key is the one looked up. -/
theorem lookup_unique {k : String} {v : Scalar} :
    ∀ {ms : List (String × Scalar)}, (k, v) ∈ ms → (∀ v', (k, v') ∈ ms → v' = v) →
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
  cases c <;> simp [fields]

theorem fields_nodup (c : Command) : (fields c).Nodup :=
  (fields_keys c).imp fun h e => h (congrArg Prod.fst e)

theorem fields_key_unique (c : Command) {m m' : String × Scalar} (hm : m ∈ fields c)
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
theorem members_subset {ms : List (String × Scalar)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) : ∀ m ∈ ms, m ∈ fields c :=
  subset_of_length (fields_nodup c) hl hm

/-- In such an object, the field of each key is the member looked up. -/
theorem lookup_field {ms : List (String × Scalar)} {c : Command}
    (hl : ms.length = (fields c).length) (hm : ∀ m ∈ fields c, m ∈ ms) :
    ∀ m ∈ fields c, ms.lookup m.1 = some m.2 := by
  intro m hmf
  refine lookup_unique (hm m hmf) fun v' hv' => ?_
  have := fields_key_unique c (members_subset hl hm _ hv') hmf rfl
  exact congrArg Prod.snd this

/-- `decodeMembers` accepts, as the command `c`, exactly the members that are the fields of `c`
in some order: as many as `c` has fields, with each field among them. -/
theorem decodeMembers_ok_iff (ms : List (String × Scalar)) (c : Command) :
    decodeMembers ms = .ok c ↔ ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  constructor
  · intro h
    unfold decodeMembers at h
    repeat' split at h
    all_goals try cases h
    all_goals subst_vars
    all_goals refine ⟨by assumption, ?_⟩
    all_goals simp only [fields, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
      and_true]
    all_goals and_intros
    all_goals (apply lookup_mem; assumption)
  · rintro ⟨hl, hm⟩
    have hk := lookup_field hl hm
    cases c <;>
      simp only [fields, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true,
        and_true, List.length_cons, List.length_nil] at hk hl <;>
      simp [decodeMembers, hk, hl]

/-- The tokens of the JSON text that spells a command decode to it. -/
theorem decode_encode (c : Command) : decode (pack (lexemesOf c)) = .ok c := by
  simp only [decode, unpack_pack, lexemesOf, object_objectLexemes, scalars_lexFields]
  exact decodeMembers_fields c

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
  unfold decode
  cases hu : unpack packed with
  | none => simp
  | some lexemes =>
    skip
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
      | none => .error .notJson := by
  unfold decode
  cases unpack packed <;> rfl

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

/-- `notCommand` is the refusal of the objects with a member `cmd` whose members are the fields
of no command. -/
theorem decodeMembers_notCommand_iff (ms : List (String × Scalar)) :
    decodeMembers ms = .error .notCommand ↔
      ms.lookup "cmd" ≠ none ∧
        ∀ c, ¬(ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms) := by
  simp only [← decodeMembers_ok_iff, ne_eq, ← decodeMembers_missingCmd_iff ms]
  cases h : decodeMembers ms with
  | ok c => simp
  | error e =>
    cases e with
    | notJson => exact absurd h (decodeMembers_ne_notJson ms)
    | notCommand => simp
    | missingCmd => simp

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
value that spells the command `c` gives the engine `c` for the principal of the token's organization and
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

/-- The tokens of a note, as a JSON library reads them from what `encodeReply` writes. -/
def noteLexemes (n : Note) : List Lexeme :=
  [.objOpen, .key "body", .str n.body, .key "id", .number (decimalText n.id), .key "owner",
    .number (decimalText n.owner), .key "shared", .bool n.shared, .objClose]

/-- The tokens of a member. -/
def memberLexemes (m : Member) : List Lexeme :=
  [.objOpen, .key "admin", .bool m.admin, .key "user", .number (decimalText m.user), .objClose]

/-- The tokens of a reply: those of the text `encodeReply` writes, a number as its decimal. -/
def replyLexemes : Reply → List Lexeme
  | .done => [.objOpen, .key "done", .bool true, .objClose]
  | .found n => .objOpen :: .key "note" :: (noteLexemes n ++ [.objClose])
  | .notes ns => .objOpen :: .key "notes" :: .arrOpen :: (ns.flatMap noteLexemes ++ [.arrClose, .objClose])
  | .members ms =>
    .objOpen :: .key "members" :: .arrOpen :: (ms.flatMap memberLexemes ++ [.arrClose, .objClose])

theorem noteOf_note (n : Note) :
    noteOf "body" n.body "id" (decimalText n.id) "owner" (decimalText n.owner) "shared" n.shared =
      some n := by
  simp [noteOf, numberOf_decimalText]

theorem notesOf_lexemes (ns : List Note) (acc : List Note) :
    notesOf acc (ns.flatMap noteLexemes ++ [.arrClose, .objClose]) = some (acc.reverse ++ ns) := by
  induction ns generalizing acc with
  | nil => simp [notesOf]
  | cons n ns ih => simp [noteLexemes, notesOf, noteOf_note, ih]

theorem membersOf_lexemes (ms : List Member) (acc : List Member) :
    membersOf acc (ms.flatMap memberLexemes ++ [.arrClose, .objClose]) = some (acc.reverse ++ ms) := by
  induction ms generalizing acc with
  | nil => simp [membersOf]
  | cons m ms ih => simp [memberLexemes, membersOf, numberOf_decimalText, ih]

/-- The tokens of a reply are read back as the reply. -/
theorem replyOf_lexemes (r : Reply) : replyOf (replyLexemes r) = some r := by
  cases r with
  | done => simp [replyLexemes, replyOf]
  | found n => simp [replyLexemes, noteLexemes, replyOf, noteOf_note]
  | notes ns =>
    have := notesOf_lexemes ns []
    simp_all [replyLexemes, replyOf]
  | members ms =>
    have := membersOf_lexemes ms []
    simp_all [replyLexemes, replyOf]

theorem replyLexemes_replyToks (r : Reply) : replyLexemes r = (replyToks r).map Lexeme.ofStrTok := by
  cases r with
  | done => rfl
  | found n => simp [replyLexemes, replyToks, noteLexemes, noteToks, Lexeme.ofStrTok]
  | notes ns =>
    simp only [replyLexemes, replyToks, List.map_cons, List.map_append, List.map_flatMap, Lexeme.ofStrTok,
      List.map_nil]
    congr
  | members ms =>
    simp only [replyLexemes, replyToks, List.map_cons, List.map_append, List.map_flatMap, Lexeme.ofStrTok,
      List.map_nil]
    congr

/-- The tokens of the text `encodeReply` writes for a reply are read back as the reply:
`encodeReply r` is `Json.writeArray (replyToks r)`, and the JSON library that reads the stored
bytes is trusted to hand over the tokens of the writer, a number as its decimal
(`Lexeme.ofStrTok`), packed by `pack`. -/
theorem decodeReply_encode (r : Reply) :
    decodeReply (some (pack ((replyToks r).map Lexeme.ofStrTok))) = some r := by
  simp only [← replyLexemes_replyToks, decodeReply, unpack_pack]
  exact replyOf_lexemes r

/-- The reply of the tokens of a stored reply. -/
theorem decodeReply_spec (packed : String) :
    decodeReply (some packed) = (unpack packed).bind replyOf := by
  simp only [decodeReply]
  cases unpack packed <;> rfl

/-- Stored bytes the JSON library refuses are read back as no reply. -/
theorem decodeReply_none : decodeReply none = none := rfl

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
theorem digits_sep {n m : Nat} {c c' : UInt8} {r r' : List UInt8} (hc : Json.Lexemes.isDigit c = false)
    (hc' : Json.Lexemes.isDigit c' = false) (h : Json.digits n ++ c :: r = Json.digits m ++ c' :: r') :
    n = m ∧ c :: r = c' :: r' := by
  have hd : ∀ k, ∀ x ∈ Json.digits k, Json.Lexemes.isDigit x = true := fun k => by
    rw [← Json.decimal_spec]
    exact Json.Lexemes.decimal_isDigit k
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
