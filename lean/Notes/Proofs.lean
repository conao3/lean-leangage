import Leanharbor.Obligation
import Leanharbor.AuthzProofs
import Notes.Kernel

/-!
# What the notes kernel guarantees

`transition` is `handle` behind `Leanharbor.Authz.guardViewed`, so the guard's theorems hold for
it by instantiation (`transition_authorized`, `transition_noninterference`, `read_only_sound`).
The other theorems are about what the commands do and what the policy lets each user do, and
`transition_congr`: two snapshots with unique keys that store the same row under each key answer
every command the same.
-/

namespace Notes.Kernel

open Leanharbor Leanharbor.Authz

def policy : Policy Principal Snapshot Write Row := ⟨permits, visible, stored⟩

def kernel : Kernel := viewedKernel handle apply policy disclosed readOnly view init tenant

theorem transition_eq (a : Principal) (s : Snapshot) (c : Command) :
    transition a s c = guardViewed handle apply policy disclosed readOnly view a s c := rfl

/-! ## The guard's theorems, for this kernel and policy -/

/-- An accepted command that writes is `handle`'s result, with every write permitted and every
disclosed row stored and visible; an accepted read-only command is `handle`'s result on the
caller's view, with no writes and only rows stored and visible in the view. -/
theorem transition_authorized {a : Principal} {s : Snapshot} {c : Command} {ws : List Write}
    {r : Reply} (h : transition a s c = .ok (ws, r)) :
    (readOnly c = false ∧ handle a s c = .ok (ws, r) ∧ WritesPermitted apply policy a s ws ∧
        ReadsVisible apply policy disclosed a s ws r) ∨
      (readOnly c = true ∧ ws = [] ∧ handle a (view a s) c = .ok (ws, r) ∧
        ∀ d ∈ disclosed r, Shown policy a (view a s) d) :=
  guard_viewed_authorized handle apply policy disclosed readOnly view h

/-- Two snapshots with the same view give a read-only command the same result. -/
theorem transition_noninterference {a : Principal} {s₁ s₂ : Snapshot} {c : Command}
    (hro : readOnly c = true) (hv : view a s₁ = view a s₂) : transition a s₁ c = transition a s₂ c :=
  guard_viewed_noninterference handle apply policy disclosed readOnly view hro hv

theorem read_only_sound : Obligation.ReadOnlySound kernel (fun ws : List Write => ws) :=
  read_only_sound_of_viewed handle apply policy disclosed readOnly view init tenant

theorem textOk_iff {t : String} :
    textOk t = true ↔ 0 < t.utf8ByteSize ∧ t.utf8ByteSize ≤ 4096 ∧ '\x00' ∉ t.toList := by
  unfold textOk maxText
  simp [and_assoc]

/-! ## Lists keyed by an id -/

section Keys

variable {α : Type} (key : α → UInt64)

theorem find?_replace (l : List α) (x : α) (k : UInt64) :
    (l.map fun y => if key y == key x then x else y).find? (key · == k) =
      if key x = k then (if l.any (key · == key x) then some x else none)
      else l.find? (key · == k) := by
  induction l with
  | nil => simp
  | cons y l ih =>
    by_cases hy : key y = key x <;> by_cases hk : key x = k <;> simp_all [List.find?_cons]

theorem find?_append_absent (l : List α) (x : α) (k : UInt64) (h : l.any (key · == key x) = false) :
    (l ++ [x]).find? (key · == k) = if key x = k then some x else l.find? (key · == k) := by
  rw [List.find?_append]
  by_cases hk : key x = k
  · subst hk
    have : l.find? (key · == key x) = none := by simpa using h
    simp [this]
  · simp [hk]

theorem find?_upsert (l : List α) (x : α) (k : UInt64) :
    (if l.any (key · == key x) then l.map (fun y => if key y == key x then x else y)
      else l ++ [x]).find? (key · == k) = if key x = k then some x else l.find? (key · == k) := by
  split
  · rename_i h; rw [find?_replace]; simp [h]
  · rename_i h; exact find?_append_absent key l x k (by simpa using h)

theorem find?_remove (l : List α) (v k : UInt64) :
    (l.filter (key · != v)).find? (key · == k) = if v = k then none else l.find? (key · == k) := by
  rw [List.find?_filter]
  by_cases h : v = k
  · subst h; simp
  · simp only [h, ite_false]
    congr 1
    funext y
    by_cases hy : key y = k <;> simp [hy, Ne.symm h]

theorem nodup_upsert (l : List α) (x : α) (h : (l.map key).Nodup) :
    ((if l.any (key · == key x) then l.map (fun y => if key y == key x then x else y)
      else l ++ [x]).map key).Nodup := by
  split
  · have : (l.map fun y => if key y == key x then x else y).map key = l.map key := by
      rw [List.map_map]
      apply List.map_congr_left
      intro y _
      by_cases hy : key y = key x <;> simp [hy]
    rw [this]; exact h
  · rename_i hn
    rw [List.map_append, List.nodup_append]
    refine ⟨h, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    simp only [List.mem_map] at ha
    obtain ⟨y, hy, rfl⟩ := ha
    simp only [List.any_eq_true, beq_iff_eq, not_exists, not_and] at hn
    exact hn y hy

theorem nodup_remove (l : List α) (v : UInt64) (h : (l.map key).Nodup) :
    ((l.filter (key · != v)).map key).Nodup :=
  h.sublist ((List.filter_sublist).map key)

/-- In a list of unique keys, a row is the one found under its key. -/
theorem find?_of_mem {l : List α} {x : α} (h : (l.map key).Nodup) (hx : x ∈ l) :
    l.find? (key · == key x) = some x := by
  induction l with
  | nil => simp at hx
  | cons y l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    rw [List.find?_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have hne' : key y ≠ key x := fun e => h.1 (by rw [e]; exact List.mem_map_of_mem hx)
      have hne : (key y == key x) = false := by simp [hne']
      simp only [hne, ih h.2 hx]

end Keys

theorem findMember_putMember (ms : List Member) (m : Member) (u : UInt64) :
    findMember (putMember ms m) u = if m.user = u then some m else findMember ms u := by
  unfold findMember putMember
  exact find?_upsert (fun x : Member => x.user) ms m u

theorem findNote_putNote (ns : List Note) (n : Note) (k : UInt64) :
    findNote (putNote ns n) k = if n.id = k then some n else findNote ns k := by
  unfold findNote putNote
  exact find?_upsert (fun x : Note => x.id) ns n k

theorem keys_upsert {α : Type} (key : α → UInt64) (l : List α) (x : α) :
    (if l.any (key · == key x) then l.map (fun y => if key y == key x then x else y)
      else l ++ [x]).map key = if l.any (key · == key x) then l.map key else l.map key ++ [key x] := by
  split
  · rw [List.map_map]
    apply List.map_congr_left
    intro y _
    by_cases hy : key y = key x <;> simp [hy]
  · simp

/-- Adding a member puts it after every stored member, and replacing one keeps its place. -/
theorem users_putMember (ms : List Member) (m : Member) :
    (putMember ms m).map (·.user) =
      if ms.any (·.user == m.user) then ms.map (·.user) else ms.map (·.user) ++ [m.user] := by
  unfold putMember
  exact keys_upsert (fun x : Member => x.user) ms m

/-- Creating a note puts it after every stored note, and replacing one keeps its place. -/
theorem ids_putNote (ns : List Note) (n : Note) :
    (putNote ns n).map (·.id) = if ns.any (·.id == n.id) then ns.map (·.id) else ns.map (·.id) ++ [n.id] := by
  unfold putNote
  exact keys_upsert (fun x : Note => x.id) ns n

/-- The caller's own member row is in the view, so the view keeps whether the caller is an
admin. -/
theorem isAdmin_view (a : Principal) (s : Snapshot) : isAdmin (view a s) a.user = isAdmin s a.user := by
  have : findMember (view a s).members a.user = findMember s.members a.user := by
    simp only [view, findMember, visible, List.find?_filter]
    congr 1
    funext m
    by_cases h : m.user = a.user <;> simp [h]
  simp only [isAdmin, this]

theorem visible_view (a : Principal) (s : Snapshot) (d : Row) :
    visible a (view a s) d = visible a s d := by
  cases d <;> simp only [visible, isAdmin_view]

theorem isAdmin_eq (s : Snapshot) (u : UInt64) :
    isAdmin s u = (findMember s.members u).any (·.admin) := by
  unfold isAdmin
  cases findMember s.members u <;> rfl

theorem visible_note (a : Principal) (s : Snapshot) (n : Note) :
    visible a s (.note n) =
      (n.shared || n.owner == a.user || (findMember s.members a.user).any (·.admin)) := by
  simp only [visible, isAdmin_eq]

theorem visible_member (a : Principal) (s : Snapshot) (m : Member) :
    visible a s (.member m) = (m.user == a.user || (findMember s.members a.user).any (·.admin)) := by
  simp only [visible, isAdmin_eq]

section Filter

variable {α : Type}

theorem find?_filter_of_find? {p q : α → Bool} {l : List α} {x : α} (h : l.find? p = some x)
    (hq : q x = true) : (l.filter q).find? p = some x := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [List.find?_cons] at h
    by_cases hp : p y = true
    · simp only [hp] at h
      cases h
      simp [hq, hp]
    · simp only [hp] at h
      by_cases hqy : q y = true <;> simp [hqy, hp, ih h]

theorem find?_filter_of_none {p q : α → Bool} {l : List α} (h : l.find? p = none) :
    (l.filter q).find? p = none := by
  simp only [List.find?_eq_none] at h ⊢
  intro x hx
  exact h x (List.mem_filter.mp hx).1

theorem eq_of_key_eq (key : α → UInt64) {l : List α} (h : (l.map key).Nodup) {x y : α} (hx : x ∈ l)
    (hy : y ∈ l) (he : key x = key y) : x = y := by
  have h₁ := find?_of_mem key h hx
  have h₂ := find?_of_mem key h hy
  rw [he, h₂] at h₁
  exact (Option.some.inj h₁).symm

end Filter

/-! ## Listings in key order -/

section Sorting

variable {α : Type} (key : α → UInt64)

/-- Inserts `x` before the first element with a larger key. -/
def insertKey (x : α) : List α → List α
  | [] => [x]
  | y :: l => if key x ≤ key y then x :: y :: l else y :: insertKey x l

/-- Sorts a list by `key`, by insertion. -/
def sortKey : List α → List α
  | [] => []
  | x :: l => insertKey key x (sortKey l)

theorem perm_insertKey (x : α) (l : List α) : (insertKey key x l).Perm (x :: l) := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons y l ih =>
    unfold insertKey
    split
    · exact List.Perm.refl _
    · exact ((ih.cons y).trans (List.Perm.swap x y l))

theorem perm_sortKey (l : List α) : (sortKey key l).Perm l := by
  induction l with
  | nil => exact List.Perm.refl _
  | cons x l ih => exact (perm_insertKey key x _).trans (ih.cons x)

theorem sorted_insertKey (x : α) {l : List α} (h : l.Pairwise (key · ≤ key ·)) :
    (insertKey key x l).Pairwise (key · ≤ key ·) := by
  induction l with
  | nil => exact List.pairwise_singleton _ _
  | cons y l ih =>
    rw [List.pairwise_cons] at h
    unfold insertKey
    split
    · rename_i hxy
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, List.pairwise_cons.mpr h⟩
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact UInt64.le_trans hxy (h.1 z hz)
    · rename_i hxy
      refine List.pairwise_cons.mpr ⟨fun z hz => ?_, ih h.2⟩
      rcases List.mem_cons.mp ((perm_insertKey key x l).mem_iff.mp hz) with rfl | hz
      · exact UInt64.le_of_lt (UInt64.not_le.mp hxy)
      · exact h.1 z hz

theorem sorted_sortKey (l : List α) : (sortKey key l).Pairwise (key · ≤ key ·) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x l ih => exact sorted_insertKey key x ih

/-- Two lists in strictly increasing key order with the same elements are equal. -/
theorem eq_of_sorted {l₁ l₂ : List α} (h₁ : l₁.Pairwise (key · < key ·))
    (h₂ : l₂.Pairwise (key · < key ·)) (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : l₁ = l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => rfl
    | cons y l₂ => exact absurd ((h y).mpr List.mem_cons_self) List.not_mem_nil
  | cons x l₁ ih =>
    cases l₂ with
    | nil => exact absurd ((h x).mp List.mem_cons_self) List.not_mem_nil
    | cons y l₂ =>
      rw [List.pairwise_cons] at h₁ h₂
      have hxy : x = y := by
        rcases List.mem_cons.mp ((h x).mp List.mem_cons_self) with e | hx
        · exact e
        · rcases List.mem_cons.mp ((h y).mpr List.mem_cons_self) with e | hy
          · exact e.symm
          · exact absurd (UInt64.lt_trans (h₁.1 y hy) (h₂.1 x hx)) (UInt64.lt_irrefl _)
      subst hxy
      congr 1
      refine ih h₁.2 h₂.2 (fun z => ⟨fun hz => ?_, fun hz => ?_⟩)
      · rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (h₁.1 _ hz) (UInt64.lt_irrefl _)
        · exact hz'
      · rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with rfl | hz'
        · exact absurd (h₂.1 _ hz) (UInt64.lt_irrefl _)
        · exact hz'

theorem strict_sortKey {l : List α} (hn : (l.map key).Nodup) :
    (sortKey key l).Pairwise (key · < key ·) := by
  have hn' : ((sortKey key l).map key).Nodup := hn.perm ((perm_sortKey key l).map key).symm
  rw [List.Nodup, List.pairwise_map] at hn'
  exact ((sorted_sortKey key l).and hn').imp fun ⟨hle, hne⟩ => UInt64.lt_of_le_of_ne hle hne

/-- Lists with no key twice and the same elements sort to the same list. -/
theorem sortKey_eq {l₁ l₂ : List α} (hn₁ : (l₁.map key).Nodup) (hn₂ : (l₂.map key).Nodup)
    (h : ∀ x, x ∈ l₁ ↔ x ∈ l₂) : sortKey key l₁ = sortKey key l₂ :=
  eq_of_sorted key (strict_sortKey key hn₁) (strict_sortKey key hn₂) fun x => by
    rw [(perm_sortKey key l₁).mem_iff, (perm_sortKey key l₂).mem_iff]
    exact h x

end Sorting

theorem insertMember_eq (m : Member) (ms : List Member) :
    insertMember m ms = insertKey (·.user) m ms := by
  induction ms with
  | nil => rfl
  | cons x ms ih => simp only [insertMember, insertKey, ih]

theorem sortMembers_eq (ms : List Member) : sortMembers ms = sortKey (·.user) ms := by
  induction ms with
  | nil => rfl
  | cons m ms ih => simp only [sortMembers, sortKey, ih, insertMember_eq]

theorem insertNote_eq (n : Note) (ns : List Note) : insertNote n ns = insertKey (·.id) n ns := by
  induction ns with
  | nil => rfl
  | cons x ns ih => simp only [insertNote, insertKey, ih]

theorem sortNotes_eq (ns : List Note) : sortNotes ns = sortKey (·.id) ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp only [sortNotes, sortKey, ih, insertNote_eq]

/-- `listMembers` lists members in the order of their user ids, each once. -/
theorem sortMembers_spec (ms : List Member) :
    (sortMembers ms).Pairwise (·.user ≤ ·.user) ∧ (sortMembers ms).Perm ms := by
  rw [sortMembers_eq]
  exact ⟨sorted_sortKey _ ms, perm_sortKey _ ms⟩

/-- `listNotes` lists notes in the order of their ids, each once. -/
theorem sortNotes_spec (ns : List Note) :
    (sortNotes ns).Pairwise (·.id ≤ ·.id) ∧ (sortNotes ns).Perm ns := by
  rw [sortNotes_eq]
  exact ⟨sorted_sortKey _ ns, perm_sortKey _ ns⟩

/-- `readNote` of the note stored under the id returns it when the caller may see it. -/
theorem read_visible {a : Principal} {s : Snapshot} {id : UInt64} {n : Note}
    (hf : findNote s.notes id = some n) (hv : visible a s (.note n) = true) :
    transition a s (.readNote id) = .ok ([], .found n) := by
  have hid : n.id = id := by simpa using List.find?_some hf
  have hfv : findNote (view a s).notes id = some n := find?_filter_of_find? hf hv
  rw [transition_eq, guard_viewed_eq]
  simp only [readOnly, ite_true, handle, hfv]
  split
  · rfl
  rename_i hc
  refine absurd ⟨by simp, fun d hd => ?_⟩ hc
  simp only [disclosed, List.mem_singleton] at hd
  subst hd
  refine ⟨?_, ?_⟩
  · simp [policy, stored, hid, hfv]
  · simpa [policy, visible_view] using hv

/-- `readNote` of an id under which the caller's view has no note is refused with `notFound`. -/
theorem read_hidden {a : Principal} {s : Snapshot} {id : UInt64}
    (hf : findNote (view a s).notes id = none) :
    transition a s (.readNote id) = .error (.app .notFound) := by
  rw [transition_eq, guard_viewed_eq]
  simp only [readOnly, ite_true, handle, hf]

/-- `readNote` of an id under which no note is stored is refused with `notFound`. -/
theorem read_none {a : Principal} {s : Snapshot} {id : UInt64} (hf : findNote s.notes id = none) :
    transition a s (.readNote id) = .error (.app .notFound) :=
  read_hidden (find?_filter_of_none hf)

/-- An accepted command that writes is `handle`'s result with every write permitted. -/
theorem write_of_transition {a : Principal} {s : Snapshot} {c : Command} {ws : List Write}
    {r : Reply} (h : transition a s c = .ok (ws, r)) (hro : readOnly c = false) :
    handle a s c = .ok (ws, r) ∧ WritesPermitted apply policy a s ws := by
  rcases transition_authorized h with ⟨_, hh, hw, _⟩ | ⟨hro', _⟩
  · exact ⟨hh, hw⟩
  · simp [hro] at hro'

theorem permits_of_one {a : Principal} {s : Snapshot} {w : Write}
    (h : WritesPermitted apply policy a s [w]) : permits a s w = true := by
  simpa [apply, policy] using h 0 (by simp)

/-- A command that writes replies `done`. -/
theorem handle_reply_done {a : Principal} {s : Snapshot} {c : Command} {ws : List Write}
    {r : Reply} (hro : readOnly c = false) (h : handle a s c = .ok (ws, r)) : r = .done := by
  cases c with
  | addMember u admin => cases h; rfl
  | removeMember u =>
    simp only [handle] at h
    split at h
    · cases h
    · cases h; rfl
  | putNote id body shared =>
    simp only [handle] at h
    split at h
    · cases h; rfl
    · cases h
  | deleteNote id =>
    simp only [handle] at h
    split at h
    · cases h
    · cases h; rfl
  | readNote _ => cases hro
  | listNotes => cases hro
  | listMembers => cases hro

theorem transition_write (a : Principal) (s : Snapshot) (c : Command) (hro : readOnly c = false) :
    transition a s c = guard handle apply policy disclosed a s c := by
  rw [transition_eq, guard_viewed_eq]
  simp [hro]

/-! ## Unique keys -/

/-- No two members have the same user id and no two notes the same id. -/
def Keyed (s : Snapshot) : Prop :=
  (s.members.map (·.user)).Nodup ∧ (s.notes.map (·.id)).Nodup

instance (s : Snapshot) : Decidable (Keyed s) := by unfold Keyed; infer_instance

/-- Every write keeps the keys unique. -/
theorem keyed_applyWrite (s : Snapshot) (w : Write) (h : Keyed s) : Keyed (applyWrite s w) := by
  cases w with
  | putMember m => exact ⟨nodup_upsert (·.user) s.members m h.1, h.2⟩
  | delMember u => exact ⟨nodup_remove (·.user) s.members u h.1, h.2⟩
  | putNote n => exact ⟨h.1, nodup_upsert (·.id) s.notes n h.2⟩
  | delNote id => exact ⟨h.1, nodup_remove (·.id) s.notes id h.2⟩

theorem keyed_apply (s : Snapshot) (ws : List Write) (h : Keyed s) : Keyed (apply s ws) := by
  induction ws generalizing s with
  | nil => exact h
  | cons w ws ih => exact ih (applyWrite s w) (keyed_applyWrite s w h)

/-- `init` has unique keys and every accepted command keeps them unique. -/
theorem keyed_invariant : Obligation.Invariant kernel Keyed :=
  ⟨⟨List.nodup_nil, List.nodup_nil⟩, fun _ s _ ws _ hs _ => keyed_apply s ws hs⟩

/-- Every snapshot a tenant reaches has unique keys. -/
theorem keyed_of_run {s : Snapshot} (h : kernel.Run s) : Keyed s :=
  keyed_invariant.run h

/-! ## What a write does -/

theorem findMember_applyWrite (s : Snapshot) (w : Write) (u : UInt64) :
    findMember (applyWrite s w).members u =
      match w with
      | .putMember m => if m.user = u then some m else findMember s.members u
      | .delMember v => if v = u then none else findMember s.members u
      | _ => findMember s.members u := by
  cases w with
  | putMember m => exact findMember_putMember s.members m u
  | delMember v => exact find?_remove (·.user) s.members v u
  | putNote n => rfl
  | delNote id => rfl

theorem findNote_applyWrite (s : Snapshot) (w : Write) (k : UInt64) :
    findNote (applyWrite s w).notes k =
      match w with
      | .putNote n => if n.id = k then some n else findNote s.notes k
      | .delNote id => if id = k then none else findNote s.notes k
      | _ => findNote s.notes k := by
  cases w with
  | putMember m => rfl
  | delMember v => rfl
  | putNote n => exact findNote_putNote s.notes n k
  | delNote id => exact find?_remove (·.id) s.notes id k

/-! ## What the commands do -/

/-- After an accepted `putNote`, the same user's `readNote` returns the note with the body and the
sharing that `putNote` gave, owned by the user that owned the id before or else by the caller. -/
theorem read_after_put {a : Principal} {s : Snapshot} {id : UInt64} {body : String}
    {shared : Bool} {ws : List Write} {r : Reply}
    (h : transition a s (.putNote id body shared) = .ok (ws, r)) :
    transition a (apply s ws) (.readNote id) =
      .ok ([], .found { id, owner := ((findNote s.notes id).map (·.owner)).getD a.user, shared, body }) := by
  obtain ⟨hh, hw⟩ := write_of_transition h rfl
  simp only [handle] at hh
  split at hh
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    have hp := permits_of_one hw
    apply read_visible
    · simp [apply, findNote_applyWrite]
      cases findNote s.notes id <;> rfl
    · simp only [permits] at hp
      simp only [apply, List.foldl, applyWrite, visible, isAdmin] at hp ⊢
      cases hf : findNote s.notes id with
      | none => simp_all
      | some old =>
        simp only [hf, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hp
        rcases hp.2 with hp | hp <;> simp [hp]
  · cases hh

/-- After an accepted `deleteNote`, no note has the id. -/
theorem read_after_delete {a : Principal} {s : Snapshot} {id : UInt64} {ws : List Write} {r : Reply}
    (h : transition a s (.deleteNote id) = .ok (ws, r)) :
    transition a (apply s ws) (.readNote id) = .error (.app .notFound) := by
  obtain ⟨hh, _⟩ := write_of_transition h rfl
  simp only [handle] at hh
  split at hh
  · cases hh
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    apply read_none
    simp [apply, findNote_applyWrite]

/-- After an accepted `addMember`, the member is stored with the admin flag it was given. -/
theorem member_after_add {a : Principal} {s : Snapshot} {u : UInt64} {admin : Bool}
    {ws : List Write} {r : Reply} (h : transition a s (.addMember u admin) = .ok (ws, r)) :
    findMember (apply s ws).members u = some { user := u, admin } := by
  obtain ⟨hh, _⟩ := write_of_transition h rfl
  simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
  obtain ⟨rfl, rfl⟩ := hh
  simp [apply, findMember_applyWrite]

/-- After an accepted `removeMember`, no member has the user id. -/
theorem member_after_remove {a : Principal} {s : Snapshot} {u : UInt64} {ws : List Write}
    {r : Reply} (h : transition a s (.removeMember u) = .ok (ws, r)) :
    findMember (apply s ws).members u = none := by
  obtain ⟨hh, _⟩ := write_of_transition h rfl
  simp only [handle] at hh
  split at hh
  · cases hh
  · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl⟩ := hh
    simp [apply, findMember_applyWrite]

/-- In a snapshot with unique keys, `readNote` returns the note stored under the id when it is
shared, the caller owns it or the caller is an admin, and `notFound` otherwise. -/
theorem read_note_spec (a : Principal) (s : Snapshot) (id : UInt64) (hk : Keyed s) :
    transition a s (.readNote id) =
      match findNote s.notes id with
      | some n =>
        if n.shared || n.owner == a.user || (findMember s.members a.user).any (·.admin) then
          .ok ([], .found n)
        else .error (.app .notFound)
      | none => .error (.app .notFound) := by
  simp only [← visible_note]
  cases hf : findNote s.notes id with
  | none => exact read_none hf
  | some n =>
    dsimp only
    by_cases hv : visible a s (.note n) = true
    · simp only [hv, ite_true]
      exact read_visible hf hv
    · simp only [hv, Bool.false_eq_true, ite_false]
      apply read_hidden
      rw [findNote, List.find?_eq_none]
      intro m hmf hmid
      obtain ⟨hm, hmv⟩ := List.mem_filter.mp hmf
      replace hmid : m.id = id := by simpa using hmid
      have hnid : n.id = id := by simpa using List.find?_some hf
      have := eq_of_key_eq (·.id) hk.2 hm (List.mem_of_find?_eq_some hf) (hmid.trans hnid.symm)
      subst this
      exact hv hmv

/-- In a snapshot with unique keys, `listNotes` returns, in the order of their ids, the notes that
are shared or owned by the caller, or every note when the caller is an admin. -/
theorem list_notes_spec (a : Principal) (s : Snapshot) (hk : Keyed s) :
    transition a s .listNotes =
      .ok ([], .notes (sortKey (·.id) (s.notes.filter fun n =>
        n.shared || n.owner == a.user || (findMember s.members a.user).any (·.admin)))) := by
  simp only [← visible_note]
  rw [transition_eq, guard_viewed_eq]
  simp only [readOnly, ite_true, handle, sortNotes_eq]
  split
  · rfl
  rename_i hc
  refine absurd ⟨by simp, fun d hd => ?_⟩ hc
  simp only [disclosed, List.mem_map] at hd
  obtain ⟨n, hn, rfl⟩ := hd
  rw [(perm_sortKey _ _).mem_iff] at hn
  have hkv : ((view a s).notes.map (·.id)).Nodup := hk.2.sublist ((List.filter_sublist).map _)
  refine ⟨?_, ?_⟩
  · simp [policy, stored, findNote, find?_of_mem (·.id) hkv hn]
  · simp only [policy, visible_view]
    exact (List.mem_filter.mp hn).2

/-- In a snapshot with unique keys, `listMembers` returns the caller's own member row, or every
member in the order of their user ids when the caller is an admin. -/
theorem list_members_spec (a : Principal) (s : Snapshot) (hk : Keyed s) :
    transition a s .listMembers =
      .ok ([], .members (sortKey (·.user) (s.members.filter fun m =>
        m.user == a.user || (findMember s.members a.user).any (·.admin)))) := by
  simp only [← visible_member]
  rw [transition_eq, guard_viewed_eq]
  simp only [readOnly, ite_true, handle, sortMembers_eq]
  split
  · rfl
  rename_i hc
  refine absurd ⟨by simp, fun d hd => ?_⟩ hc
  simp only [disclosed, List.mem_map] at hd
  obtain ⟨m, hm, rfl⟩ := hd
  rw [(perm_sortKey _ _).mem_iff] at hm
  have hkv : ((view a s).members.map (·.user)).Nodup := hk.1.sublist ((List.filter_sublist).map _)
  refine ⟨?_, ?_⟩
  · simp [policy, stored, findMember, find?_of_mem (·.user) hkv hm]
  · simp only [policy, visible_view]
    exact (List.mem_filter.mp hm).2

/-- A note's body is refused exactly when it is empty, longer than 4096 bytes or holds NUL. -/
theorem bad_text (a : Principal) (s : Snapshot) (id : UInt64) (body : String) (shared : Bool) :
    transition a s (.putNote id body shared) = .error (.app .badText) ↔
      ¬(0 < body.utf8ByteSize ∧ body.utf8ByteSize ≤ 4096 ∧ '\x00' ∉ body.toList) := by
  rw [transition_write a s _ rfl, guard_eq]
  by_cases ht : textOk body = true
  · obtain ⟨ws, hh⟩ : ∃ ws, handle a s (.putNote id body shared) = .ok (ws, .done) := by
      simp only [handle, ht, ite_true]
      exact ⟨_, rfl⟩
    rw [hh]
    have hn : 0 < body.utf8ByteSize ∧ body.utf8ByteSize ≤ 4096 ∧ '\x00' ∉ body.toList :=
      textOk_iff.mp ht
    simp only [hn]
    split <;> simp
  · have hh : handle a s (.putNote id body shared) = .error .badText := by
      simp [handle, ht]
    rw [hh]
    simpa [textOk_iff] using ht

/-- Removing a member or deleting a note is refused with `notFound` exactly when none is stored
under the key. -/
theorem not_found (a : Principal) (s : Snapshot) (k : UInt64) :
    (transition a s (.removeMember k) = .error (.app .notFound) ↔ findMember s.members k = none) ∧
      (transition a s (.deleteNote k) = .error (.app .notFound) ↔ findNote s.notes k = none) := by
  constructor
  · rw [transition_write a s _ rfl, guard_eq]
    cases h : findMember s.members k with
    | none => simp [handle, h]
    | some m =>
      simp only [handle, h, reduceCtorEq, iff_false]
      split <;> simp
  · rw [transition_write a s _ rfl, guard_eq]
    cases h : findNote s.notes k with
    | none => simp [handle, h]
    | some n =>
      simp only [handle, h, reduceCtorEq, iff_false]
      split <;> simp

/-! ## What the policy lets each user do -/

/-- A user who is not an admin changes only notes they own, before and after the command. -/
theorem others_unchanged {a : Principal} {s : Snapshot} {c : Command} {ws : List Write}
    {r : Reply} (h : transition a s c = .ok (ws, r))
    (hadmin : (findMember s.members a.user).any (·.admin) = false) (k : UInt64) :
    findNote (apply s ws).notes k = findNote s.notes k ∨
      ((findNote s.notes k).all (·.owner == a.user) ∧
        (findNote (apply s ws).notes k).all (·.owner == a.user)) := by
  have hna : isAdmin s a.user = false := by rw [isAdmin_eq]; exact hadmin
  rcases transition_authorized h with ⟨hro, hh, hw, _⟩ | ⟨_, rfl, _⟩
  · cases c with
    | addMember u admin =>
      simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      left; rfl
    | removeMember u =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        left; rfl
    | putNote id body shared =>
      simp only [handle] at hh
      split at hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have hp := permits_of_one hw
        simp only [apply, List.foldl, findNote_applyWrite]
        by_cases hk : id = k
        · subst hk
          right
          simp only [permits, hna, Bool.or_false] at hp
          cases hf : findNote s.notes id with
          | none => simp_all
          | some old => simp_all
        · left; simp [hk]
      · cases hh
    | deleteNote id =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · rename_i old hf
        simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have hp := permits_of_one hw
        simp only [apply, List.foldl, findNote_applyWrite]
        by_cases hk : id = k
        · subst hk
          right
          simp only [permits, hf, hna, Bool.or_false] at hp
          simp [hf, hp]
        · left; simp [hk]
    | readNote _ => cases hro
    | listNotes => cases hro
    | listMembers => cases hro
  · left; rfl

/-- A user who is not an admin changes the members only of an organization that has none. -/
theorem members_unchanged {a : Principal} {s : Snapshot} {c : Command} {ws : List Write}
    {r : Reply} (h : transition a s c = .ok (ws, r))
    (hadmin : (findMember s.members a.user).any (·.admin) = false) :
    (apply s ws).members = s.members ∨ s.members = [] := by
  have hna : isAdmin s a.user = false := by rw [isAdmin_eq]; exact hadmin
  rcases transition_authorized h with ⟨hro, hh, hw, _⟩ | ⟨_, rfl, _⟩
  · cases c with
    | addMember u admin =>
      simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl⟩ := hh
      have hp := permits_of_one hw
      simp only [permits, hna, Bool.false_or] at hp
      split at hp
      · right; simpa using hp
      · cases hp
    | removeMember u =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · rename_i old hf
        simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        have hp := permits_of_one hw
        simp [permits, hf, hna] at hp
    | putNote id body shared =>
      simp only [handle] at hh
      split at hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        left; rfl
      · cases hh
    | deleteNote id =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        left; rfl
    | readNote _ => cases hro
    | listNotes => cases hro
    | listMembers => cases hro
  · left; rfl

/-- The guard denies no command that writes when the caller is an admin. -/
theorem admin_not_denied (a : Principal) (s : Snapshot) (c : Command)
    (hadmin : (findMember s.members a.user).any (·.admin) = true) (hro : readOnly c = false) :
    transition a s c = (handle a s c).mapError .app := by
  have ha : isAdmin s a.user = true := by rw [isAdmin_eq]; exact hadmin
  rw [transition_write a s c hro]
  cases hh : handle a s c with
  | error e => exact guard_app_error handle apply policy disclosed hh
  | ok out =>
    obtain ⟨ws, r⟩ := out
    have hw : ∀ w, ws = [w] → permits a s w = true → WritesPermitted apply policy a s ws := by
      rintro w rfl hp i hi
      have : i = 0 := by simp at hi; omega
      subst this
      simpa [apply, policy] using hp
    have hr : r = .done → ReadsVisible apply policy disclosed a s ws r := by
      rintro rfl d hd
      simp [disclosed] at hd
    have hwr : WritesPermitted apply policy a s ws ∧ ReadsVisible apply policy disclosed a s ws r := by
      cases c with
      | addMember u admin =>
        simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, rfl⟩ := hh
        refine ⟨hw _ rfl ?_, hr rfl⟩
        simp only [permits, ha, Bool.true_or]
        split <;> rfl
      | removeMember u =>
        simp only [handle] at hh
        split at hh
        · cases hh
        · rename_i old hf
          simp only [Except.ok.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          exact ⟨hw _ rfl (by simp [permits, hf, ha]), hr rfl⟩
      | putNote id body shared =>
        simp only [handle] at hh
        split at hh
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          refine ⟨hw _ rfl ?_, hr rfl⟩
          cases hf : findNote s.notes id <;> simp [permits, hf, ha]
        · cases hh
      | deleteNote id =>
        simp only [handle] at hh
        split at hh
        · cases hh
        · rename_i old hf
          simp only [Except.ok.injEq, Prod.mk.injEq] at hh
          obtain ⟨rfl, rfl⟩ := hh
          exact ⟨hw _ rfl (by simp [permits, hf, ha]), hr rfl⟩
      | readNote _ => exact absurd hro (by simp [readOnly])
      | listNotes => exact absurd hro (by simp [readOnly])
      | listMembers => exact absurd hro (by simp [readOnly])
    exact guard_complete handle apply policy disclosed hh hwr.1 hwr.2

/-- The owner of a note may replace it, and anyone may create a note under a free id. -/
theorem owner_may_put (a : Principal) (s : Snapshot) (id : UInt64) (body : String) (shared : Bool)
    (ht : textOk body = true) (hown : (findNote s.notes id).all (·.owner == a.user)) :
    transition a s (.putNote id body shared) =
      .ok ([.putNote { id, owner := a.user, shared, body }], .done) := by
  rw [transition_write a s _ rfl]
  have hh : handle a s (.putNote id body shared) =
      .ok ([.putNote { id, owner := a.user, shared, body }], .done) := by
    simp only [handle, ht, ite_true]
    cases hf : findNote s.notes id with
    | none => rfl
    | some old => simp_all
  apply guard_complete handle apply policy disclosed hh
  · intro i hi
    simp at hi
    subst hi
    simp only [apply, policy, permits, List.take_zero, List.foldl, List.getElem_cons_zero]
    cases hf : findNote s.notes id with
    | none => simp
    | some old => simp_all
  · simp [ReadsVisible, disclosed]

/-- The owner of the note stored under an id may delete it. -/
theorem owner_may_delete (a : Principal) (s : Snapshot) (id : UInt64) :
    match findNote s.notes id with
    | some n => transition { a with user := n.owner } s (.deleteNote id) = .ok ([.delNote id], .done)
    | none => True := by
  split
  · rename_i n hn
    rw [transition_write _ s _ rfl]
    have hh : handle { a with user := n.owner } s (.deleteNote id) = .ok ([.delNote id], .done) := by
      simp [handle, hn]
    apply guard_complete handle apply policy disclosed hh
    · intro i hi
      simp at hi
      subst hi
      simp [apply, policy, permits, hn]
    · simp [ReadsVisible, disclosed]
  · trivial

/-- The first member of an organization with no members may be added by anyone. -/
theorem first_member (a : Principal) (s : Snapshot) (u : UInt64) (admin : Bool)
    (h : s.members = []) :
    transition a s (.addMember u admin) = .ok ([.putMember { user := u, admin }], .done) := by
  rw [transition_write a s _ rfl]
  apply guard_complete handle apply policy disclosed rfl
  · intro i hi
    simp at hi
    subst hi
    simp [apply, policy, permits, findMember, h]
  · simp [ReadsVisible, disclosed]

/-! ## The order of the rows -/

section Order

variable {α : Type} (key : α → UInt64)

theorem mem_iff_find? {l : List α} (h : (l.map key).Nodup) (x : α) :
    x ∈ l ↔ l.find? (key · == key x) = some x :=
  ⟨find?_of_mem key h, List.mem_of_find?_eq_some⟩

/-- In a list with no key twice, the element under a key among those that pass a filter is the
element under that key, if it passes. -/
theorem find?_filter_key {l : List α} (h : (l.map key).Nodup) (p : α → Bool) (k : UInt64) :
    (l.filter p).find? (key · == k) = (l.find? (key · == k)).filter p := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    by_cases hy : key y = k
    · have hnone : (l.filter p).find? (key · == k) = none := by
        rw [List.find?_eq_none]
        intro x hx hkx
        have hkx : key x = k := by simpa using hkx
        exact h.1 (hy ▸ hkx ▸ List.mem_map_of_mem (List.mem_filter.mp hx).1)
      have hk : (key y == k) = true := by simpa using hy
      by_cases hp : p y = true
      · rw [List.filter_cons_of_pos hp]
        simp only [List.find?_cons, hk]
        exact (Option.filter_some_pos hp).symm
      · rw [List.filter_cons_of_neg hp, hnone]
        simp only [List.find?_cons, hk]
        exact (Option.filter_some_neg (by simpa using hp)).symm
    · have hk : (key y == k) = false := by simpa using hy
      by_cases hp : p y = true
      · rw [List.filter_cons_of_pos hp]
        simp only [List.find?_cons, hk]
        exact ih h.2
      · rw [List.filter_cons_of_neg hp]
        simp only [List.find?_cons, hk]
        exact ih h.2

end Order

/-- `s` and `s'` have unique keys and store the same member under each user id and the same note
under each id: they differ at most in the order of their rows. -/
def SameRows (s s' : Snapshot) : Prop :=
  Keyed s ∧ Keyed s' ∧ (∀ u, findMember s.members u = findMember s'.members u) ∧
    ∀ k, findNote s.notes k = findNote s'.notes k

theorem members_eq_nil (s : Snapshot) :
    s.members = [] ↔ ∀ u, findMember s.members u = none := by
  constructor
  · intro h u
    simp [findMember, h]
  · intro h
    cases hm : s.members with
    | nil => rfl
    | cons m ms =>
      have := h m.user
      simp [findMember, hm] at this

namespace SameRows

variable {s s' : Snapshot} (h : SameRows s s')
include h

theorem isAdmin_eq (u : UInt64) : isAdmin s u = isAdmin s' u := by
  simp only [isAdmin, h.2.2.1 u]

theorem isEmpty_eq : s.members.isEmpty = s'.members.isEmpty := by
  have e : s.members = [] ↔ s'.members = [] := by
    rw [members_eq_nil, members_eq_nil]
    simp only [h.2.2.1]
  cases h1 : s.members <;> cases h2 : s'.members <;> simp_all

theorem permits_eq (a : Principal) (w : Write) : permits a s w = permits a s' w := by
  cases w <;> simp only [permits, h.2.2.1, h.2.2.2, h.isAdmin_eq, h.isEmpty_eq]

theorem visible_eq (a : Principal) (d : Row) : visible a s d = visible a s' d := by
  cases d <;> simp only [visible, h.isAdmin_eq]

theorem stored_eq (d : Row) : stored s d = stored s' d := by
  cases d <;> simp only [stored, h.2.2.1, h.2.2.2]

theorem symm : SameRows s' s :=
  ⟨h.2.1, h.1, fun u => (h.2.2.1 u).symm, fun k => (h.2.2.2 k).symm⟩

omit h in
theorem refl (hk : Keyed s) : SameRows s s := ⟨hk, hk, fun _ => rfl, fun _ => rfl⟩

theorem applyWrite (w : Write) : SameRows (applyWrite s w) (applyWrite s' w) := by
  refine ⟨keyed_applyWrite s w h.1, keyed_applyWrite s' w h.2.1, fun u => ?_, fun k => ?_⟩
  · rw [findMember_applyWrite, findMember_applyWrite]
    cases w <;> simp only [h.2.2.1]
  · rw [findNote_applyWrite, findNote_applyWrite]
    cases w <;> simp only [h.2.2.2]

omit h in
theorem apply {s s' : Snapshot} (h : SameRows s s') (ws : List Write) :
    SameRows (Notes.Kernel.apply s ws) (Notes.Kernel.apply s' ws) := by
  induction ws generalizing s s' with
  | nil => exact h
  | cons w ws ih => exact ih (h.applyWrite w)

theorem view (a : Principal) : SameRows (view a s) (view a s') := by
  have hv : ∀ d, visible a s d = visible a s' d := h.visible_eq a
  refine ⟨⟨h.1.1.sublist ((List.filter_sublist).map _), h.1.2.sublist ((List.filter_sublist).map _)⟩,
    ⟨h.2.1.1.sublist ((List.filter_sublist).map _), h.2.1.2.sublist ((List.filter_sublist).map _)⟩,
    fun u => ?_, fun k => ?_⟩
  · have e := h.2.2.1 u
    simp only [findMember] at e
    simp only [Notes.Kernel.view, findMember]
    rw [find?_filter_key (fun m : Member => m.user) h.1.1,
      find?_filter_key (fun m : Member => m.user) h.2.1.1, e]
    simp only [hv]
  · have e := h.2.2.2 k
    simp only [findNote] at e
    simp only [Notes.Kernel.view, findNote]
    rw [find?_filter_key (fun n : Note => n.id) h.1.2, find?_filter_key (fun n : Note => n.id) h.2.1.2, e]
    simp only [hv]

theorem sortMembers_eq : sortMembers s.members = sortMembers s'.members := by
  rw [Notes.Kernel.sortMembers_eq, Notes.Kernel.sortMembers_eq]
  refine sortKey_eq _ h.1.1 h.2.1.1 fun m => ?_
  rw [mem_iff_find? (·.user) h.1.1, mem_iff_find? (·.user) h.2.1.1]
  exact iff_of_eq (congrArg (· = some m) (h.2.2.1 m.user))

theorem sortNotes_eq : sortNotes s.notes = sortNotes s'.notes := by
  rw [Notes.Kernel.sortNotes_eq, Notes.Kernel.sortNotes_eq]
  refine sortKey_eq _ h.1.2 h.2.1.2 fun n => ?_
  rw [mem_iff_find? (·.id) h.1.2, mem_iff_find? (·.id) h.2.1.2]
  exact iff_of_eq (congrArg (· = some n) (h.2.2.2 n.id))

theorem handle_eq (a : Principal) (c : Command) : handle a s c = handle a s' c := by
  cases c <;> simp only [handle, h.2.2.1, h.2.2.2, h.sortMembers_eq, h.sortNotes_eq]

theorem checkWritesFrom_eq (a : Principal) (done ws : List Write) :
    checkWritesFrom Notes.Kernel.apply policy a s done ws =
      checkWritesFrom Notes.Kernel.apply policy a s' done ws := by
  induction ws generalizing done with
  | nil => rfl
  | cons w ws ih =>
    simp only [checkWritesFrom, ih]
    rw [show policy.permits = permits from rfl, (h.apply done).permits_eq]

omit h in
theorem checkReads_eq {b b' f f' : Snapshot} (hb : SameRows b b') (hf : SameRows f f') (a : Principal)
    (ds : List Row) : checkReads policy a b f ds = checkReads policy a b' f' ds := by
  simp only [checkReads, shown, show policy.stored = stored from rfl,
    show policy.visible = visible from rfl, hb.stored_eq, hb.visible_eq, hf.stored_eq, hf.visible_eq]

end SameRows

/-- Two snapshots that differ at most in the order of their rows answer every command of every
principal the same. -/
theorem transition_congr {s s' : Snapshot} (h : SameRows s s') (a : Principal) (c : Command) :
    transition a s c = transition a s' c := by
  rw [transition_eq, transition_eq]
  unfold guardViewed Authz.guard checkWrites
  simp only [h.handle_eq, (h.view a).handle_eq, h.checkWritesFrom_eq,
    fun ws ds => SameRows.checkReads_eq h (h.apply ws) a ds,
    fun ds => SameRows.checkReads_eq (h.view a) (h.view a) a ds]

/-- A read-only command gives the same result on two snapshots whose views differ at most in the
order of their rows. -/
theorem transition_view_congr {a : Principal} {s s' : Snapshot} {c : Command}
    (hro : readOnly c = true) (h : SameRows (view a s) (view a s')) :
    transition a s c = transition a s' c := by
  rw [transition_eq, transition_eq]
  simp only [guardViewed, hro, ite_true, h.handle_eq,
    fun ds => SameRows.checkReads_eq h h a ds]

/-! ## Forms without a hypothesis on the result, for the audit -/

theorem read_after_put_run (a : Principal) (s : Snapshot) (id : UInt64) (body : String)
    (shared : Bool) :
    match transition a s (.putNote id body shared) with
    | .ok (ws, _) => transition a (apply s ws) (.readNote id) =
      .ok ([], .found { id, owner := ((findNote s.notes id).map (·.owner)).getD a.user, shared, body })
    | .error _ => True := by
  split
  · exact read_after_put ‹_›
  · trivial

theorem read_after_delete_run (a : Principal) (s : Snapshot) (id : UInt64) :
    match transition a s (.deleteNote id) with
    | .ok (ws, _) => transition a (apply s ws) (.readNote id) = .error (.app .notFound)
    | .error _ => True := by
  split
  · exact read_after_delete ‹_›
  · trivial

theorem member_after_add_run (a : Principal) (s : Snapshot) (u : UInt64) (admin : Bool) :
    match transition a s (.addMember u admin) with
    | .ok (ws, _) => findMember (apply s ws).members u = some { user := u, admin }
    | .error _ => True := by
  split
  · exact member_after_add ‹_›
  · trivial

theorem member_after_remove_run (a : Principal) (s : Snapshot) (u : UInt64) :
    match transition a s (.removeMember u) with
    | .ok (ws, _) => findMember (apply s ws).members u = none
    | .error _ => True := by
  split
  · exact member_after_remove ‹_›
  · trivial

theorem transition_authorized_run (a : Principal) (s : Snapshot) (c : Command) :
    match transition a s c with
    | .ok (ws, r) =>
      (readOnly c = false ∧ handle a s c = .ok (ws, r) ∧ WritesPermitted apply policy a s ws ∧
          ReadsVisible apply policy disclosed a s ws r) ∨
        (readOnly c = true ∧ ws = [] ∧ handle a (view a s) c = .ok (ws, r) ∧
          ∀ d ∈ disclosed r, Shown policy a (view a s) d)
    | .error _ => True := by
  split
  · exact transition_authorized ‹_›
  · trivial

theorem others_unchanged_run (a : Principal) (s : Snapshot) (c : Command) (k : UInt64) :
    match transition a s c with
    | .ok (ws, _) => (findMember s.members a.user).any (·.admin) = false →
      findNote (apply s ws).notes k = findNote s.notes k ∨
        ((findNote s.notes k).all (·.owner == a.user) ∧
          (findNote (apply s ws).notes k).all (·.owner == a.user))
    | .error _ => True := by
  split
  · exact fun hna => others_unchanged ‹_› hna k
  · trivial

theorem members_unchanged_run (a : Principal) (s : Snapshot) (c : Command) :
    match transition a s c with
    | .ok (ws, _) => (findMember s.members a.user).any (·.admin) = false →
      (apply s ws).members = s.members ∨ s.members = []
    | .error _ => True := by
  split
  · exact fun hna => members_unchanged ‹_› hna
  · trivial

/-- Every row a reply returns is the row stored under its key in the caller's view. -/
theorem rows_stored_run (a : Principal) (s : Snapshot) (c : Command) :
    match transition a s c with
    | .ok (_, r) =>
      match r with
      | .done => True
      | .found n => findNote (view a s).notes n.id = some n
      | .notes ns => ∀ n ∈ ns, findNote (view a s).notes n.id = some n
      | .members ms => ∀ m ∈ ms, findMember (view a s).members m.user = some m
    | .error _ => True := by
  cases ht : transition a s c with
  | error e => trivial
  | ok out =>
    obtain ⟨ws, r⟩ := out
    have key : ∀ d ∈ disclosed r, stored (view a s) d = true := by
      rcases transition_authorized ht with ⟨hro, hh, _, _⟩ | ⟨_, _, _, hd⟩
      · rw [handle_reply_done hro hh]
        simp [disclosed]
      · exact fun d hd' => (hd d hd').1
    cases r with
    | done => trivial
    | found n => simpa [disclosed, stored] using key (.note n) (by simp [disclosed])
    | notes ns =>
      intro n hn
      simpa [stored] using key (.note n) (by simp [disclosed]; exact hn)
    | members ms =>
      intro m hm
      simpa [stored] using key (.member m) (by simp [disclosed]; exact hm)

end Notes.Kernel
