import Leanharbor.Kernel
import Calculator.Kernel

/-!
# What the calculator kernel guarantees

`transition_spec` and `compute_spec` tie the 64-bit implementation to arithmetic on unbounded
naturals. `get_after` and `others_unchanged` are about a command followed by `apply`.
-/

namespace Calculator.Kernel

def kernel : Leanharbor.Kernel where
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

theorem memoryOf_upsert_self (m : Memory) (ms : List Memory) :
    memoryOf (upsert m ms) m.user = m.value := by
  induction ms with
  | nil => simp [upsert, memoryOf]
  | cons x xs ih =>
    unfold upsert
    split
    · simp [memoryOf]
    · rename_i h; simp [memoryOf, h, ih]

theorem memoryOf_upsert_other (m : Memory) (ms : List Memory) (u : UInt64) (h : u ≠ m.user) :
    memoryOf (upsert m ms) u = memoryOf ms u := by
  induction ms with
  | nil => simp [upsert, memoryOf, Ne.symm h]
  | cons x xs ih =>
    unfold upsert
    split
    · rename_i hx; simp [memoryOf, hx, Ne.symm h]
    · simp [memoryOf, ih]

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
    kernel.ReadOnlySound (fun w : Option Memory => w.toList) := by
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

/-- `step` is `transition`, written with `Outcome`. -/
theorem step_eq (a : Principal) (s : Snapshot) (c : Command) :
    step a s c = match transition a s c with
      | .ok (w, r) => .accepted w r
      | .error e => .refused e := rfl

end Calculator.Kernel
