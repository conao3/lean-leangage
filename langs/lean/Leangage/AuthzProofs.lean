import Leangage.Kernel
import Leangage.Authz

/-!
# What the authorization guard guarantees

Based on h5i's `crates/h5i-app-std/proofs/AuthzSpecs.lean` (commit 515c7b9, Apache-2.0), restated
for the guard of `Leangage.Authz`: the statements are about Lean functions instead of the
extraction of Rust, so they need no `Result` of the extraction and no lemmas about its loops.

Every theorem holds for every kernel (`transition` and `apply`), policy, disclosure, `readOnly` and
`view`: none looks inside them. A kernel that runs behind `guard` or `guardViewed` gets them by
instantiating them.
-/

namespace Leangage.Authz

variable {A S C W R E D : Type}

/-- Every write is permitted in the state the writes before it leave, by the kernel's own
`apply`. -/
def WritesPermitted (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S) (ws : List W) :
    Prop :=
  ∀ i (h : i < ws.length), p.permits a (apply s (ws.take i)) ws[i] = true

/-- The row is stored in the state, exactly as given, and the actor may see it there. -/
def Shown (p : Policy A S W D) (a : A) (s : S) (d : D) : Prop :=
  p.stored s d = true ∧ p.visible a s d = true

/-- Every row the reply discloses is `Shown` before the command or after it. -/
def ReadsVisible (apply : S → List W → S) (p : Policy A S W D) (disclosed : R → List D) (a : A)
    (s : S) (ws : List W) (r : R) : Prop :=
  ∀ d ∈ disclosed r, Shown p a s d ∨ Shown p a (apply s ws) d

instance (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S) (ws : List W) :
    Decidable (WritesPermitted apply p a s ws) := by
  unfold WritesPermitted; infer_instance

instance (p : Policy A S W D) (a : A) (s : S) (d : D) : Decidable (Shown p a s d) := by
  unfold Shown; infer_instance

instance (apply : S → List W → S) (p : Policy A S W D) (disclosed : R → List D) (a : A) (s : S)
    (ws : List W) (r : R) : Decidable (ReadsVisible apply p disclosed a s ws r) := by
  unfold ReadsVisible; infer_instance

theorem checkWritesFrom_iff (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S)
    (done ws : List W) :
    checkWritesFrom apply p a s done ws = true ↔
      ∀ i (h : i < ws.length), p.permits a (apply s (done ++ ws.take i)) ws[i] = true := by
  induction ws generalizing done with
  | nil => simp [checkWritesFrom]
  | cons w rest ih =>
    simp only [checkWritesFrom, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h0, hr⟩ i hi
      cases i with
      | zero => simpa only [List.take_zero, List.append_nil, List.getElem_cons_zero] using h0
      | succ j =>
        have := hr j (by simp at hi; omega)
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.append_assoc,
          List.singleton_append] at this ⊢
        exact this
    · intro h
      constructor
      · have := h 0 (by simp)
        simp only [List.take_zero, List.append_nil, List.getElem_cons_zero] at this
        exact this
      · intro j hj
        have := h (j + 1) (by simp; omega)
        simp only [List.take_succ_cons, List.getElem_cons_succ, List.append_assoc,
          List.singleton_append] at this ⊢
        exact this

theorem checkWrites_iff (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S)
    (ws : List W) : checkWrites apply p a s ws = true ↔ WritesPermitted apply p a s ws := by
  simp [checkWrites, checkWritesFrom_iff, WritesPermitted]

theorem shown_iff (p : Policy A S W D) (a : A) (s : S) (d : D) :
    shown p a s d = true ↔ Shown p a s d := by
  simp [shown, Shown]

theorem checkReads_iff (p : Policy A S W D) (a : A) (before after : S) (ds : List D) :
    checkReads p a before after ds = true ↔
      ∀ d ∈ ds, Shown p a before d ∨ Shown p a after d := by
  simp [checkReads, shown_iff]

section Guard

variable (transition : A → S → C → Except E (List W × R)) (apply : S → List W → S)
  (p : Policy A S W D) (disclosed : R → List D)

/-- The guard refuses with `denied` exactly the accepted commands whose writes are not all
permitted or whose disclosed rows are not all shown, passes the kernel's refusals through, and
changes nothing else. -/
theorem guard_eq (a : A) (s : S) (c : C) :
    guard transition apply p disclosed a s c =
      match transition a s c with
      | .error e => .error (.app e)
      | .ok (ws, r) =>
        if WritesPermitted apply p a s ws ∧ ReadsVisible apply p disclosed a s ws r then .ok (ws, r)
        else .error .denied := by
  unfold guard
  cases transition a s c with
  | error e => rfl
  | ok out =>
    obtain ⟨ws, r⟩ := out
    dsimp only
    have : (checkWrites apply p a s ws && checkReads p a s (apply s ws) (disclosed r)) = true ↔
        WritesPermitted apply p a s ws ∧ ReadsVisible apply p disclosed a s ws r := by
      simp only [Bool.and_eq_true, checkWrites_iff, checkReads_iff, ReadsVisible]
    by_cases h : WritesPermitted apply p a s ws ∧ ReadsVisible apply p disclosed a s ws r
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (this.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt this.mp h)), ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- The guard's theorem, for every kernel and policy: a command the guard accepts is the kernel's
own result, its writes are permitted and its disclosed rows visible. -/
theorem guard_authorized {a : A} {s : S} {c : C} {ws : List W} {r : R}
    (h : guard transition apply p disclosed a s c = .ok (ws, r)) :
    transition a s c = .ok (ws, r) ∧ WritesPermitted apply p a s ws ∧
      ReadsVisible apply p disclosed a s ws r := by
  rw [guard_eq] at h
  split at h
  · cases h
  · rename_i ws' r' ht
    split at h
    · rename_i hc
      cases h
      exact ⟨ht, hc⟩
    · cases h

/-- The guard passes the kernel's refusals through. -/
theorem guard_app_error {a : A} {s : S} {c : C} {e : E} (h : transition a s c = .error e) :
    guard transition apply p disclosed a s c = .error (.app e) := by
  rw [guard_eq, h]

/-- The guard accepts every command the kernel accepts whose writes are permitted and whose
disclosed rows are shown: it adds no other refusal. -/
theorem guard_complete {a : A} {s : S} {c : C} {ws : List W} {r : R}
    (ht : transition a s c = .ok (ws, r)) (hw : WritesPermitted apply p a s ws)
    (hr : ReadsVisible apply p disclosed a s ws r) :
    guard transition apply p disclosed a s c = .ok (ws, r) := by
  rw [guard_eq, ht]
  exact ite_eq_left_of_eq_true _ _ (eq_true ⟨hw, hr⟩)

variable (readOnly : C → Bool) (view : A → S → S)

/-- `guardViewed` on a command that writes is `guard`; on a read-only command it runs the kernel
on the actor's view and refuses with `denied` a result with writes or with a disclosed row not
shown in the view. -/
theorem guard_viewed_eq (a : A) (s : S) (c : C) :
    guardViewed transition apply p disclosed readOnly view a s c =
      if readOnly c then
        match transition a (view a s) c with
        | .error e => .error (.app e)
        | .ok (ws, r) =>
          if ws = [] ∧ ∀ d ∈ disclosed r, Shown p a (view a s) d then .ok (ws, r)
          else .error .denied
      else guard transition apply p disclosed a s c := by
  unfold guardViewed
  cases readOnly c with
  | false => rfl
  | true =>
    simp only [ite_true]
    cases transition a (view a s) c with
    | error e => rfl
    | ok out =>
      obtain ⟨ws, r⟩ := out
      dsimp only
      have : (ws.isEmpty && checkReads p a (view a s) (view a s) (disclosed r)) = true ↔
          ws = [] ∧ ∀ d ∈ disclosed r, Shown p a (view a s) d := by
        simp [checkReads_iff]
      by_cases h : ws = [] ∧ ∀ d ∈ disclosed r, Shown p a (view a s) d
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (this.mpr h)), ite_eq_left_of_eq_true _ _ (eq_true h)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (mt this.mp h)), ite_eq_right_of_eq_false _ _ (eq_false h)]

/-- A command `guardViewed` accepts is either a command that writes, accepted by `guard`, or a
read-only command whose result is the kernel's on the actor's view, with no writes and only rows
shown in the view. -/
theorem guard_viewed_authorized {a : A} {s : S} {c : C} {ws : List W} {r : R}
    (h : guardViewed transition apply p disclosed readOnly view a s c = .ok (ws, r)) :
    (readOnly c = false ∧ transition a s c = .ok (ws, r) ∧ WritesPermitted apply p a s ws ∧
        ReadsVisible apply p disclosed a s ws r) ∨
      (readOnly c = true ∧ ws = [] ∧ transition a (view a s) c = .ok (ws, r) ∧
        ∀ d ∈ disclosed r, Shown p a (view a s) d) := by
  rw [guard_viewed_eq] at h
  split at h
  · rename_i hro
    right
    split at h
    · cases h
    · rename_i ws' r' ht
      split at h
      · rename_i hc
        cases h
        exact ⟨hro, hc.1, ht, hc.2⟩
      · cases h
  · rename_i hro
    left
    exact ⟨by simpa using hro, guard_authorized transition apply p disclosed h⟩

/-- Noninterference of read-only commands: two states with the same view give the same result,
refusals and denials included. Nothing of the state outside the view reaches the reply. -/
theorem guard_viewed_noninterference {a : A} {s₁ s₂ : S} {c : C} (hro : readOnly c = true)
    (hv : view a s₁ = view a s₂) :
    guardViewed transition apply p disclosed readOnly view a s₁ c =
      guardViewed transition apply p disclosed readOnly view a s₂ c := by
  simp [guardViewed, hro, hv]

/-- The kernel that runs a kernel's `transition` and `apply` behind `guardViewed`. -/
def viewedKernel (init : S) (tenant : A → UInt64) : Kernel where
  Principal := A
  Snapshot := S
  Command := C
  WriteSet := List W
  Reply := R
  Error := Guarded E
  init := init
  tenant := tenant
  transition := guardViewed transition apply p disclosed readOnly view
  apply := apply
  readOnly := readOnly

/-- A kernel behind `guardViewed` meets the read-only obligation of the kernel contract for the
view's `readOnly`: an engine may run those commands without a write transaction. -/
theorem read_only_sound_of_viewed (init : S) (tenant : A → UInt64) :
    (viewedKernel transition apply p disclosed readOnly view init tenant).ReadOnlySound
      (fun ws : List W => ws) := by
  intro a s c ws r hro h
  rcases guard_viewed_authorized transition apply p disclosed readOnly view h with
    ⟨hf, _⟩ | ⟨_, hnil, _⟩
  · exact absurd hro (by simp [viewedKernel] at hf ⊢; simp [hf])
  · exact hnil

end Guard

end Leangage.Authz
