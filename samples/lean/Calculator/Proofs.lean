import Leangage.Obligation
import Leangage.Json.Proofs
import Calculator.Kernel

/-!
# What the calculator kernel guarantees

`transition_spec` and `compute_spec` tie the 64-bit implementation to arithmetic on unbounded
naturals. `get_after` and `others_unchanged` are about a command followed by `apply`.
`encodeReply_spec` and `encodeError_spec` say that the bytes of a reply and of a refusal are the
JSON values `replyValue` and `errorValue`, printed by `Leangage.Json.Value.print`;
`encodeReplyArray_spec` and `encodeErrorArray_spec` say the same of the arrays the servers send.
-/

namespace Calculator.Kernel

def kernel : Leangage.Kernel where
  Principal := Principal
  Snapshot := Snapshot
  Command := Command
  WriteSet := Option Memory
  Reply := Reply
  Error := Error
  init := init
  tenant := tenant
  transition := transition
  apply := apply
  readOnly := readOnly

/-- The arithmetic the calculator is meant to do, on unbounded naturals. -/
def eval (op : Op) (a b : Nat) : Except Error Nat :=
  match op with
  | .add => if a + b < 2 ^ 64 then .ok (a + b) else .error .overflow
  | .sub => if b ≤ a then .ok (a - b) else .error .underflow
  | .mul => if a * b < 2 ^ 64 then .ok (a * b) else .error .overflow
  | .div => if b = 0 then .error .divByZero else .ok (a / b)

theorem eq_iff_halves (u k : UInt64) : u = k ↔ u % 2 = k % 2 ∧ u / 2 = k / 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ := congrArg UInt64.toNat h₁
    have e₂ := congrArg UInt64.toNat h₂
    simp only [UInt64.toNat_mod, UInt64.toNat_div, UInt64.reduceToNat] at e₁ e₂
    exact UInt64.toNat_inj.mp (by omega)

theorem mod_two_ne_zero (x : UInt64) : ¬x % 2 = 0 ↔ x % 2 = 1 := by
  have h : (x % 2).toNat = 0 ∨ (x % 2).toNat = 1 := by
    simp only [UInt64.toNat_mod, UInt64.reduceToNat]; omega
  rcases h with h | h
  · have : x % 2 = 0 := UInt64.toNat_inj.mp h
    simp [this]
  · have : x % 2 = 1 := UInt64.toNat_inj.mp h
    simp [this]

theorem memoryOf_pair (k₁ v₁ k v u : UInt64) :
    memoryOf (pair k₁ v₁ k v) u = if u = k then v else if u = k₁ then v₁ else 0 := by
  fun_induction pair k₁ v₁ k v generalizing u <;>
    simp only [memoryOf, *] <;>
    simp only [eq_iff_halves u _] <;>
    by_cases hu : u % 2 = 0 <;> simp_all [mod_two_ne_zero]

theorem memoryOf_store (k v : UInt64) (ms : Memories) (u : UInt64) :
    memoryOf (store k v ms) u = if u = k then v else memoryOf ms u := by
  induction ms generalizing k u with
  | empty => simp [store, memoryOf]
  | leaf k₁ v₁ => simp [store, memoryOf, memoryOf_pair]
  | node even odd ihe iho =>
    unfold store
    simp only [eq_iff_halves u k]
    by_cases hu : u % 2 = 0 <;> by_cases hk : k % 2 = 0 <;>
      simp_all [memoryOf, mod_two_ne_zero]

theorem memoryOf_upsert_self (m : Memory) (ms : Memories) :
    memoryOf (upsert m ms) m.user = m.value := by
  simp [upsert, memoryOf_store]

theorem memoryOf_upsert_other (m : Memory) (ms : Memories) (u : UInt64) (h : u ≠ m.user) :
    memoryOf (upsert m ms) u = memoryOf ms u := by
  simp [upsert, memoryOf_store, h]

/-- After any accepted command, `get` by the same user returns that command's reply. -/
theorem get_after (a : Principal) (s : Snapshot) (c : Command) (w : Option Memory) (v : UInt64)
    (ht : transition a s c = .ok (w, .value v)) :
    transition a (apply s w) .get = .ok (none, .value v) := by
  cases c with
  | set value =>
    simp [transition] at ht
    obtain ⟨rfl, rfl⟩ := ht
    simp only [transition, apply]
    rw [memoryOf_upsert_self ⟨a.user, _⟩ s.memories]
  | apply op arg =>
    simp only [transition] at ht
    split at ht
    · simp at ht
      obtain ⟨rfl, rfl⟩ := ht
      simp only [transition, apply]
      rw [memoryOf_upsert_self ⟨a.user, _⟩ s.memories]
    · simp at ht
  | get =>
    simp [transition] at ht
    obtain ⟨rfl, rfl⟩ := ht
    simp [transition, apply]

/-- A command changes no other user's memory. -/
theorem others_unchanged (a : Principal) (s : Snapshot) (c : Command) (w : Option Memory)
    (r : Reply) (ht : transition a s c = .ok (w, r)) (u : UInt64) (hu : u ≠ a.user) :
    memoryOf (apply s w).memories u = memoryOf s.memories u := by
  have hw : w = none ∨ ∃ v, w = some { user := a.user, value := v } := by
    cases c with
    | set value => simp [transition] at ht; exact .inr ⟨value, ht.1.symm⟩
    | apply op arg =>
      simp only [transition] at ht
      split at ht
      · simp at ht; exact .inr ⟨_, ht.1.symm⟩
      · simp at ht
    | get => simp [transition] at ht; exact .inl ht.1.symm
  rcases hw with rfl | ⟨v, rfl⟩
  · rfl
  · exact memoryOf_upsert_other _ _ _ hu

theorem read_only_sound :
    Leangage.Obligation.ReadOnlySound kernel (fun w : Option Memory => w.toList) := by
  intro a s c ws r hro ht
  cases c with
  | set value => simp [kernel, readOnly] at hro
  | apply op arg => simp [kernel, readOnly] at hro
  | get =>
    have ht' : (none, Reply.value (memoryOf s.memories a.user)) = (ws, r) := by
      simpa [kernel, transition] using ht
    cases ht'
    rfl

/-- `compute` is the unbounded arithmetic, refused exactly when the result leaves 64 bits. -/
theorem compute_spec (op : Op) (a b : UInt64) :
    (compute op a b).map (·.toNat) = eval op a.toNat b.toNat := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  cases op with
  | add =>
    simp only [compute, eval, gt_iff_lt, UInt64.lt_iff_toNat_lt]
    rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)]
    simp only [UInt64.toNat_ofNat]
    split <;> split <;> simp [Except.map, UInt64.toNat_add] <;> omega
  | sub =>
    simp only [compute, eval, UInt64.lt_iff_toNat_lt]
    split <;> split <;> simp [Except.map] <;> first | omega | (rw [UInt64.toNat_sub_of_le _ _ (by simp [UInt64.le_iff_toNat_le]; omega)])
  | mul =>
    simp only [compute, eval, gt_iff_lt, UInt64.lt_iff_toNat_lt]
    by_cases h : b = 0
    · subst h; simp [Except.map]
    · have hb0 : 0 < b.toNat :=
        Nat.pos_of_ne_zero fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
      have hd : (18446744073709551615 / b).toNat = 18446744073709551615 / b.toNat := by
        simp [UInt64.toNat_div]
      have hk : 18446744073709551615 / b.toNat < a.toNat ↔ 2 ^ 64 ≤ a.toNat * b.toNat := by
        rw [Nat.div_lt_iff_lt_mul hb0]; omega
      simp only [h, ne_eq, not_false_eq_true, true_and, hd]
      split <;> split <;> simp [Except.map, UInt64.toNat_mul] <;> first | omega | (apply Nat.mod_eq_of_lt; omega)
  | div =>
    simp only [compute, eval]
    by_cases h : b = 0
    · simp [h, Except.map]
    · have : b.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
      simp [h, this, Except.map, UInt64.toNat_div]

/-- `get_after` without a hypothesis on the result, so it can be run on any input. -/
theorem get_after_run (a : Principal) (s : Snapshot) (c : Command) :
    match transition a s c with
    | .ok (w, .value v) => transition a (apply s w) .get = .ok (none, .value v)
    | .error _ => True := by
  split
  · rename_i w v h; exact get_after a s c w v h
  · trivial

theorem others_unchanged_run (a : Principal) (s : Snapshot) (c : Command) (u : UInt64) :
    match transition a s c with
    | .ok (w, _) => u = a.user ∨ memoryOf (apply s w).memories u = memoryOf s.memories u
    | .error _ => True := by
  split
  · rename_i w r h
    by_cases hu : u = a.user
    · exact .inl hu
    · exact .inr (others_unchanged a s c w r h u hu)
  · trivial

/-- What a command does to one user's number, on unbounded naturals. -/
def specStep (mem : Nat) : Command → Except Error Nat
  | .set value => .ok value.toNat
  | .apply op arg => eval op mem arg.toNat
  | .get => .ok mem

/-- `transition` replies with `specStep` of the caller's number, and refuses exactly when it does. -/
theorem transition_spec (a : Principal) (s : Snapshot) (c : Command) :
    (transition a s c).map (fun (_, .value v) => v.toNat) =
      specStep (memoryOf s.memories a.user).toNat c := by
  cases c with
  | set value => rfl
  | apply op arg =>
    have h := compute_spec op (memoryOf s.memories a.user) arg
    simp only [transition, specStep, ← h]
    cases compute op (memoryOf s.memories a.user) arg <;> rfl
  | get => rfl

/-! ## Replies and refusals on the wire -/

/-- The name of a refusal on the wire. -/
def wireName : Error → List Char
  | .overflow => ['o', 'v', 'e', 'r', 'f', 'l', 'o', 'w']
  | .underflow => ['u', 'n', 'd', 'e', 'r', 'f', 'l', 'o', 'w']
  | .divByZero => ['d', 'i', 'v', 'i', 's', 'i', 'o', 'n', '_', 'b', 'y', '_', 'z', 'e', 'r', 'o']

/-- `{"value":<v>}`. -/
def replyValue : Reply → Leangage.Json.Value
  | .value v => .obj [(Leangage.Json.ascii ['v', 'a', 'l', 'u', 'e'], .num v)]

/-- `{"error":"<name>"}`. -/
def errorValue (e : Error) : Leangage.Json.Value :=
  .obj [(Leangage.Json.ascii ['e', 'r', 'r', 'o', 'r'], .str (Leangage.Json.ascii (wireName e)))]

theorem errorName_spec (e : Error) : errorName e = Leangage.Json.ascii (wireName e) := by
  cases e <;> decide

theorem replyToks_spec (r : Reply) : replyToks r = (replyValue r).toks := by
  cases r
  simp [replyToks, replyValue, Leangage.Json.Value.toks, Leangage.Json.membersToks,
    Leangage.Json.ascii]

theorem errorToks_spec (e : Error) : errorToks e = (errorValue e).toks := by
  simp [errorToks, errorValue, Leangage.Json.Value.toks, Leangage.Json.membersToks,
    Leangage.Json.ascii, errorName_spec]

/-- The bytes of a reply are its JSON value. -/
theorem encodeReply_spec (r : Reply) : encodeReply r = (replyValue r).print := by
  rw [encodeReply, replyToks_spec, Leangage.Json.write_value]

/-- The bytes of a refusal are its JSON value. -/
theorem encodeError_spec (e : Error) : encodeError e = (errorValue e).print := by
  rw [encodeError, errorToks_spec, Leangage.Json.write_value]

theorem errorString_spec (e : Error) : Leangage.Token.bytesOf (errorString e) = errorName e := by
  cases e <;> decide

theorem encodeReplyArray_eq (r : Reply) : (encodeReplyArray r).toList = encodeReply r := by
  cases r
  rw [encodeReplyArray, Leangage.Json.writeArray_spec, encodeReply, replyToks]
  simp only [List.map, Leangage.Json.StrTok.toTok]
  congr

theorem encodeErrorArray_eq (e : Error) : (encodeErrorArray e).toList = encodeError e := by
  rw [encodeErrorArray, Leangage.Json.writeArray_spec, encodeError, errorToks]
  simp only [List.map, Leangage.Json.StrTok.toTok, errorString_spec]
  congr

/-- The bytes of a reply that the servers send are its JSON value. -/
theorem encodeReplyArray_spec (r : Reply) : (encodeReplyArray r).toList = (replyValue r).print := by
  rw [encodeReplyArray_eq, encodeReply_spec]

/-- The bytes of a refusal that the servers send are its JSON value. -/
theorem encodeErrorArray_spec (e : Error) : (encodeErrorArray e).toList = (errorValue e).print := by
  rw [encodeErrorArray_eq, encodeError_spec]

end Calculator.Kernel
