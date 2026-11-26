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

/-- A command `spelled` gives is the command `decodeObject` gives for the tokens one by one. -/
theorem spelled_sound {tokens : Tokens} {c : Command} (h : spelled tokens = some c) :
    decodeObject tokens.lexemes = .ok c := by
  obtain ⟨kinds, texts⟩ := tokens
  unfold spelled at h
  simp only at h
  split at h
  · rename_i hk
    subst hk
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> try cases h
    split at h <;> cases h
    rename_i hop _ _ hn
    subst_vars
    have hl : "{ksksk#}".toList = ['{', 'k', 's', 'k', 's', 'k', '#', '}'] := by decide
    simp [Tokens.lexemes, hl, zip, decodeObject, object, members, scalar, hn, hop, decodeMembers,
      List.lookup]
  · split at h
    · rename_i hk
      subst hk
      split at h <;> try cases h
      split at h <;> try cases h
      split at h <;> cases h
      subst_vars
      have hl : "{ks}".toList = ['{', 'k', 's', '}'] := by decide
      simp [Tokens.lexemes, hl, zip, decodeObject, object, members, scalar, decodeMembers, List.lookup]
    · split at h
      · rename_i hk
        subst hk
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> try cases h
        split at h <;> cases h
        rename_i hn
        subst_vars
        have hl : "{ksk#}".toList = ['{', 'k', 's', 'k', '#', '}'] := by decide
        simp [Tokens.lexemes, hl, zip, decodeObject, object, members, scalar, hn, decodeMembers,
          List.lookup]
      · cases h

/-- `decode` is `decodeObject` of the tokens one by one, on every body. -/
theorem decode_eq (tokens : Tokens) : decode tokens = decodeObject tokens.lexemes := by
  unfold decode
  cases h : spelled tokens with
  | none => rfl
  | some c => exact (spelled_sound h).symm

/-- `spelled` reads the tokens of the JSON text that spells a command. -/
theorem spelled_lexemesOf (c : Command) : spelled (encode (lexemesOf c)) = some c := by
  cases c with
  | set n =>
    simp [lexemesOf, lexFields, objectLexemes, encode, kindOf, textOf, spelled, numberOf_decimalText,
      List.filterMap_cons]
  | apply op n =>
    cases op <;>
      simp [lexemesOf, lexFields, objectLexemes, encode, kindOf, textOf, spelled, numberOf_decimalText, opName,
        opNamed, List.filterMap_cons]
  | get => simp [lexemesOf, lexFields, objectLexemes, encode, kindOf, textOf, spelled, List.filterMap_cons]

/-- The tokens of the JSON text that spells a command decode to it. -/
theorem decode_encode (c : Command) : decode (encode (lexemesOf c)) = .ok c := by
  rw [decode_eq, lexemes_encode, decodeObject, lexemesOf, object_objectLexemes, scalars_lexFields]
  exact decodeMembers_fields c

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

/-- `decode` accepts, as the command `c`, exactly the tokens of an object whose members are the
fields of `c` in some order. -/
theorem decode_ok_iff (tokens : Tokens) (c : Command) :
    decode tokens = .ok c ↔
      ∃ ms, object tokens.lexemes = some ms ∧ ms.length = (fields c).length ∧ ∀ m ∈ fields c, m ∈ ms := by
  rw [decode_eq]
  unfold decodeObject
  cases h : object tokens.lexemes with
  | none => simp
  | some ms => simp [decodeMembers_ok_iff]

/-- `decode` decides on the members `object` gives, and refuses tokens without members. -/
theorem decode_spec (tokens : Tokens) :
    decode tokens =
      match object tokens.lexemes with
      | some ms => decodeMembers ms
      | none => .error .notCommand :=
  decode_eq tokens

/-- Tokens that are not those of an object whose values are values by themselves are no command. -/
theorem decode_not_object {tokens : Tokens} (h : object tokens.lexemes = none) :
    decode tokens = .error .notCommand := by
  simp [decode_eq, decodeObject, h]

/-- The tokens of an object decode as its members. -/
theorem decode_object (ms : List (String × Lexeme)) :
    decode (encode (objectLexemes ms)) =
      match scalars ms with
      | some xs => decodeMembers xs
      | none => .error .notCommand := by
  rw [decode_eq, lexemes_encode, decodeObject, object_objectLexemes]
  cases scalars ms <;> rfl

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
    (tokens : Tokens) :
    request tenant user exp now (.json tokens) =
      match decode tokens with
      | .ok cmd => .ok ⟨⟨tenant, user⟩, cmd⟩
      | .error e => .error (Http.refuse 400 (refusalMessage e)) := by
  simp only [request, Http.admit_json h]
  cases decode tokens <;> rfl

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
    request tenant user exp now (.json (encode (lexemesOf c))) = .ok ⟨⟨tenant, user⟩, c⟩ := by
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
    | json tokens =>
      rw [request_json he] at h
      cases hd : decode tokens with
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
