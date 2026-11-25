import Leanharbor.Sql.Model

/-!
# The generated statements do what `exec` says

Based on `crates/h5i-app-core/proofs/H5iAppLib/Pg.lean`, `Sql.lean`, `Tables.lean` and
`Store.lean` of h5i (https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the
theorems are about the generated `compile`, `select` and `create`, whose `Bool` checks
`valid_iff`, `fitsFrom_iff` and `typed_iff` decide, instead of `compileA`, `selectA` and
`createA`; a tenant is an `Int64`, so it is never `NULL`; the model is `Leanharbor.Sql.Model`.

All of it is relative to the model of PostgreSQL in `Leanharbor.Sql.Model`, on tables that
`create` made (`Matches`).

- `compile_sound`: a compiled statement runs, keeps the tables as `create` made them, changes the
  tenant's database as `exec` says, and leaves every other tenant's database and every table
  outside the schema as it was. `compileAll_sound` is the same for a list of statements.
- `select_sound`: a compiled `SELECT` returns the tenant's rows of the table that pass the filter,
  each once, in any order. `lists_of_selects`: a `SELECT` of every table lists the tenant's
  database.
- `create_sound`: creating the tables of a valid schema in a database without them gives tables
  that match the schema, empty for every tenant, and changes no other table. `create_kept`:
  `CREATE TABLE IF NOT EXISTS` leaves tables that exist as they are.
-/

namespace Leanharbor.Sql

open Classical

/-! ## Lists -/

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    exact List.nodup_cons.2 ⟨fun ha => h.1 ⟨a, ha, rfl⟩, ih h.2⟩

theorem eq_of_nodup_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    rcases List.mem_cons.1 ha with rfl | ha' <;> rcases List.mem_cons.1 hb with rfl | hb'
    · rfl
    · exact absurd ⟨b, hb', he.symm⟩ h.1
    · exact absurd ⟨a, ha', he⟩ h.1
    · exact ih h.2 ha' hb'

/-- `x` in place of the element with its key, or at the end. -/
def upsert {α κ : Type} [DecidableEq κ] (key : α → κ) (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if key y = key x then x :: ys else y :: upsert key x ys

section Upsert
variable {α β κ : Type} [DecidableEq κ]

theorem mem_upsert_of {k : α → κ} {x z : α} {l : List α} (h : z ∈ upsert k x l) : z = x ∨ z ∈ l := by
  induction l with
  | nil => simp [upsert] at h; exact Or.inl h
  | cons y ys ih =>
    unfold upsert at h
    split at h
    · simp at h; rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons_of_mem _ h)
    · simp at h; rcases h with h | h
      · exact Or.inr (h ▸ List.mem_cons_self)
      · rcases ih h with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_upsert_self (k : α → κ) (x : α) (l : List α) : x ∈ upsert k x l := by
  induction l with
  | nil => simp [upsert]
  | cons y ys ih => unfold upsert; split <;> simp [ih]

theorem mem_upsert_of_ne {k : α → κ} {x z : α} {l : List α} (hz : z ∈ l) (hk : k z ≠ k x) :
    z ∈ upsert k x l := by
  induction l with
  | nil => simp at hz
  | cons y ys ih =>
    unfold upsert
    simp at hz
    split
    · rename_i hy
      rcases hz with rfl | hz
      · exact absurd hy hk
      · exact List.mem_cons_of_mem _ hz
    · rcases hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hz)

/-- With unique keys, `upsert` replaces exactly the element with `x`'s key. -/
theorem mem_upsert_iff {k : α → κ} {x z : α} {l : List α} (hl : (l.map k).Nodup) :
    z ∈ upsert k x l ↔ z = x ∨ (z ∈ l ∧ k z ≠ k x) := by
  constructor
  · intro h
    induction l with
    | nil => simp [upsert] at h; exact Or.inl h
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hl
      unfold upsert at h
      split at h
      · rename_i hy
        simp at h; rcases h with h | h
        · exact Or.inl h
        · right; refine ⟨List.mem_cons_of_mem _ h, ?_⟩
          intro hzk; exact hl.1 ⟨z, h, hzk.trans hy.symm⟩
      · rename_i hy
        simp at h; rcases h with rfl | h
        · exact Or.inr ⟨List.mem_cons_self, hy⟩
        · rcases ih hl.2 h with h | ⟨h1, h2⟩
          · exact Or.inl h
          · exact Or.inr ⟨List.mem_cons_of_mem _ h1, h2⟩
  · rintro (rfl | ⟨hz, hk⟩)
    · exact mem_upsert_self k _ l
    · exact mem_upsert_of_ne hz hk

theorem upsert_found (key : α → κ) (a : α) (l : List α) (hn : (l.map key).Nodup)
    (h : ∃ y ∈ l, key y = key a) : upsert key a l = l.map (fun y => if key y = key a then a else y) := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    unfold upsert
    by_cases hy : key y = key a
    · have e : ys.map (fun y => if key y = key a then a else y) = ys := by
        refine (List.map_congr_left (g := id) (fun z hz => ?_)).trans (List.map_id ys)
        have : key z ≠ key a := fun he => hn.1 ⟨z, hz, he.trans hy.symm⟩
        simp [this]
      simp only [hy, ite_true, List.map_cons, e]
    · simp only [hy, ite_false, List.map_cons]
      rw [ih hn.2]
      obtain ⟨z, hz, he⟩ := h
      rcases List.mem_cons.1 hz with rfl | hz
      · exact absurd he hy
      · exact ⟨z, hz, he⟩

theorem upsert_new (key : α → κ) (a : α) (l : List α) (h : ∀ y ∈ l, key y ≠ key a) :
    upsert key a l = l ++ [a] := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    unfold upsert
    simp [h y List.mem_cons_self, ih (fun z hz => h z (List.mem_cons_of_mem _ hz))]

/-- With unique keys, the element found by its key is the element of the list with that key. -/
theorem find_key_iff (key : α → κ) (l : List α) (hn : (l.map key).Nodup) (k : κ) (r : α) :
    l.find? (fun x => key x = k) = some r ↔ r ∈ l ∧ key r = k := by
  constructor
  · intro h
    exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩
  · rintro ⟨hr, rfl⟩
    obtain ⟨r', hr'⟩ : ∃ r', l.find? (fun x => key x = key r) = some r' := by
      cases h : l.find? (fun x => key x = key r) with
      | some r' => exact ⟨r', rfl⟩
      | none => simp [List.find?_eq_none] at h; exact absurd rfl (h r hr)
    have hm := List.mem_of_find?_eq_some hr'
    have hk : key r' = key r := by simpa using List.find?_some hr'
    rw [hr', eq_of_nodup_map key hn hm hr hk]

end Upsert

/-! ## Keyed tables -/

section Keyed
variable (kl : Nat → Nat)

/-- What a write does to keyed tables; `kl t` is table `t`'s key length. -/
def applyW (tabs : Tables) : Write → Tables
  | .put t _ row => fun t' => if t' = t then upsert (·.take (kl t)) row (tabs t) else tabs t'
  | .del t k => fun t' => if t' = t then (tabs t).filter (fun r => ¬ r.take (kl t) = k) else tabs t'
  | .delWhere t i v => fun t' => if t' = t then (tabs t).filter (fun r => ¬ r[i]? = some v) else tabs t'

/-- Keys are unique and every row has a full key. -/
def WellKeyed (tabs : Tables) : Prop :=
  ∀ t, ((tabs t).map (·.take (kl t))).Nodup ∧ ∀ r ∈ tabs t, kl t ≤ r.length

/-- A put uses its table's key length. Deletes are on keyed tables. -/
def WriteOk : Write → Prop
  | .put t n row => n = kl t ∧ kl t ≤ row.length
  | .del t _ => 0 < kl t
  | .delWhere t _ _ => 0 < kl t

end Keyed

theorem find_upsert (n : Nat) (row : List Val) (k : List Val) (rs : List (List Val)) :
    (upsert (·.take n) row rs).find? (fun r => r.take n = k) =
      if row.take n = k then some row else rs.find? (fun r => r.take n = k) := by
  induction rs with
  | nil => simp [upsert]
  | cons r rs ih =>
    unfold upsert
    by_cases hr : r.take n = row.take n
    · simp only [hr, ite_true, List.find?_cons]
      by_cases hk : row.take n = k <;> simp_all
    · simp only [hr, ite_false, List.find?_cons, ih]
      by_cases hk : row.take n = k <;> by_cases hk' : r.take n = k <;> simp_all

theorem keys_upsert (n : Nat) (row : List Val) (rs : List (List Val)) :
    (upsert (·.take n) row rs).map (·.take n) =
      if row.take n ∈ rs.map (·.take n) then rs.map (·.take n) else rs.map (·.take n) ++ [row.take n] := by
  induction rs with
  | nil => simp [upsert]
  | cons r rs ih =>
    unfold upsert
    by_cases hr : r.take n = row.take n
    · simp [hr]
    · simp only [hr, ite_false, List.map_cons, ih, List.mem_cons]
      by_cases hm : row.take n ∈ rs.map (·.take n)
      · simp [hm]
      · have : ¬ row.take n = r.take n := fun h => hr h.symm
        simp [hm, this]

theorem find_filter_ne (n : Nat) (k k' : List Val) (h : k' ≠ k) (rs : List (List Val)) :
    (rs.filter (fun r => ¬ r.take n = k)).find? (fun r => r.take n = k') =
      rs.find? (fun r => r.take n = k') := by
  simp only [List.find?_filter]
  congr 1
  funext r
  by_cases hr : r.take n = k' <;> simp_all

theorem find_filter_eq (n : Nat) (k : List Val) (rs : List (List Val)) :
    (rs.filter (fun r => ¬ r.take n = k)).find? (fun r => r.take n = k) = none := by
  rw [List.find?_eq_none]
  intro x hx
  simp only [List.mem_filter, decide_eq_true_eq] at hx
  simpa using hx.2

/-- With unique keys, looking a key up after filtering is filtering the lookup. -/
theorem find_filter_unique (n : Nat) (q : List Val → Prop) [DecidablePred q] (rs : List (List Val))
    (hn : (rs.map (·.take n)).Nodup) (k : List Val) :
    (rs.filter (fun r => ¬ q r)).find? (fun r => r.take n = k) =
      (rs.find? (fun r => r.take n = k)).filter (fun r => !decide (q r)) := by
  induction rs with
  | nil => simp
  | cons r rs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    by_cases hr : r.take n = k
    · have hnone : (rs.filter (fun r => ¬ q r)).find? (fun r => r.take n = k) = none := by
        rw [List.find?_eq_none]
        intro x hx
        have := (List.mem_filter.1 hx).1
        simp only [decide_eq_true_eq]
        intro hx'
        exact hn.1 ⟨x, this, hx'.trans hr.symm⟩
      by_cases hq : q r
      · simp only [List.filter_cons, hq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false, hnone, List.find?_cons, hr, decide_true, Option.filter_some, Bool.not_true]
      · simp only [List.filter_cons, hq, not_false_eq_true, decide_true, ite_true, List.find?_cons, hr,
          Option.filter_some, decide_false, Bool.not_false]
    · have ih' := ih hn.2
      by_cases hq : q r
      · simp only [List.filter_cons, hq, not_true_eq_false, decide_false, Bool.false_eq_true,
          ite_false, List.find?_cons, hr]
        exact ih'
      · simp only [List.filter_cons, hq, not_false_eq_true, decide_true, ite_true, List.find?_cons, hr,
          decide_false]
        exact ih'

/-- A write on keyed tables is `exec` of its planned statement on the database they stand for, and
keys stay unique. -/
theorem step_sound (kl : Nat → Nat) (tabs : Tables) (w : Write) (hk : WellKeyed kl tabs)
    (hw : WriteOk kl w) :
    readBack kl (applyW kl tabs w) = exec (readBack kl tabs) (plan w) ∧
      WellKeyed kl (applyW kl tabs w) := by
  cases w with
  | put t n row =>
    obtain ⟨rfl, hlen⟩ := hw
    refine ⟨?_, ?_⟩
    · funext t' k'
      simp only [readBack, applyW, exec, plan, List.take_append_drop]
      by_cases ht : t' = t
      · subst ht
        simp only [ite_true, true_and, find_upsert]
        by_cases hk' : k' = row.take (kl t') <;> simp_all [eq_comm]
      · simp [ht]
    · intro t'
      simp only [applyW]
      by_cases ht : t' = t
      · subst ht
        simp only [ite_true, keys_upsert]
        refine ⟨?_, fun r hr => ?_⟩
        · split
          · exact (hk t').1
          · rename_i hm
            exact List.nodup_append.2 ⟨(hk t').1, by simp, fun a ha b hb hab =>
              hm (by rw [List.mem_singleton] at hb; subst hb; subst hab; exact ha)⟩
        · rcases (mem_upsert_iff (hk t').1).1 hr with rfl | ⟨hr, _⟩
          · exact hlen
          · exact (hk t').2 r hr
      · simpa [ht] using hk t'
  | del t k =>
    refine ⟨?_, ?_⟩
    · funext t' k'
      simp only [readBack, applyW, exec, plan]
      by_cases ht : t' = t
      · subst ht
        by_cases hk' : k' = k
        · subst hk'
          simp only [ite_true, and_self]
          exact find_filter_eq _ _ _
        · simp only [ite_true, true_and, hk', ite_false]
          exact find_filter_ne _ _ _ hk' _
      · simp [ht]
    · intro t'
      simp only [applyW]
      by_cases ht : t' = t
      · subst ht
        simp only [ite_true]
        refine ⟨?_, fun r hr => (hk t').2 r (List.mem_filter.1 hr).1⟩
        exact (hk t').1.sublist (List.Sublist.map _ List.filter_sublist)
      · simpa [ht] using hk t'
  | delWhere t i v =>
    refine ⟨?_, ?_⟩
    · funext t' k'
      simp only [readBack, applyW, exec, plan]
      by_cases ht : t' = t
      · subst ht
        simp only [ite_true, true_and]
        exact find_filter_unique _ _ _ (hk t').1 _
      · simp only [ht, ite_false, false_and, decide_false, Bool.not_false]
        cases (tabs t').find? (fun r => decide (r.take (kl t') = k')) <;> rfl
    · intro t'
      simp only [applyW]
      by_cases ht : t' = t
      · subst ht
        simp only [ite_true]
        refine ⟨?_, fun r hr => (hk t').2 r (List.mem_filter.1 hr).1⟩
        exact (hk t').1.sublist (List.Sublist.map _ List.filter_sublist)
      · simpa [ht] using hk t'

/-! ## Names resolve to positions -/

theorem colDefs_names (t : Tab) : (colDefs t).map (·.name) = names t := by
  apply List.ext_getElem
  · simp [colDefs, names]
  · intro i h1 h2
    cases i with
    | zero => rfl
    | succ i => simp [colDefs, names]

theorem colDefs_length (t : Tab) : (colDefs t).length = t.cols.length + 1 := by
  simp [colDefs]

theorem names_length (t : Tab) : (names t).length = t.cols.length + 1 := by
  simp [names]

theorem keyNames_take (tb : Tab) : keyNames tb = (names tb).take (tb.kl + 1) := by
  simp [keyNames, names, List.map_take]

/-- In columns with distinct names, a name is found at its position. -/
theorem colIdx_of_nodup (cols : List ColDef) (h : (cols.map (·.name)).Nodup) (j : Nat)
    (hj : j < cols.length) : colIdx cols cols[j].name = some j := by
  induction cols generalizing j with
  | nil => simp at hj
  | cons c cs ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
    cases j with
    | zero => simp [colIdx, List.findIdx?_cons]
    | succ j =>
      have hj' : j < cs.length := by simpa using hj
      have hne : ¬ c.name = cs[j].name := fun he => h.1 ⟨cs[j], List.getElem_mem hj', he.symm⟩
      have := ih h.2 j hj'
      simp only [colIdx] at this ⊢
      simp [List.findIdx?_cons, hne]
      exact this

theorem colIdx_colDefs (t : Tab) (hn : (names t).Nodup) (j : Nat) (hj : j < t.cols.length + 1) :
    colIdx (colDefs t) ((names t)[j]'(by rw [names_length]; exact hj)) = some j := by
  have hl : j < (colDefs t).length := by rw [colDefs_length]; exact hj
  have e : ((names t)[j]'(by rw [names_length]; exact hj)) = (colDefs t)[j].name := by
    simp only [← colDefs_names, List.getElem_map]
  rw [e]
  exact colIdx_of_nodup _ (by rw [colDefs_names]; exact hn) j hl

theorem names_succ (t : Tab) (i : Nat) (h : i < t.cols.length) :
    ((names t)[i + 1]'(by simp [names]; omega)) = t.cols[i].name := by
  simp [names]

theorem rowOk_length {tb : Tab} {r : List Val} (h : RowOk tb r) : r.length = tb.cols.length + 1 := by
  rw [← h.1, colDefs_length]

theorem tabOk_of {ts : List Tab} (hv : Valid ts) {t : Nat} {tb : Tab} (ht : ts[t]? = some tb) : TabOk tb :=
  hv.1 tb (List.mem_of_getElem? ht)

theorem names_nodup {tb : Tab} (h : TabOk tb) : (names tb).Nodup := h.2.2.2.2.2.2

theorem kl_le {tb : Tab} (h : TabOk tb) : tb.kl ≤ tb.cols.length := h.2.2.2.2.1

/-! ## One table changes -/

theorem klOf_some {ts : List Tab} {t : Nat} {tb : Tab} (h : ts[t]? = some tb) : klOf ts t = tb.kl := by
  simp [klOf, h]

theorem tenantTabs_some {ts : List Tab} {tv : Int64} {db : PgDb} {t : Nat} {tb : Tab} {tab : Table}
    (h : ts[t]? = some tb) (hdb : db tb.name = some tab) :
    tenantTabs ts tv db t = (tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail := by
  simp [tenantTabs, h, hdb]

/-- Tables of a valid schema with the same name are the same table. -/
theorem index_of_name {ts : List Tab} (hv : Valid ts) {t t' : Nat} {tb tb' : Tab}
    (h : ts[t]? = some tb) (h' : ts[t']? = some tb') (hn : tb'.name = tb.name) : t' = t := by
  obtain ⟨ht, rfl⟩ := List.getElem?_eq_some_iff.1 h
  obtain ⟨ht', rfl⟩ := List.getElem?_eq_some_iff.1 h'
  exact (List.Nodup.getElem_inj hv.2 (hi := by simpa using ht') (hj := by simpa using ht)).1
    (by simpa using hn)

theorem tenant_rows_keyed (tb : Tab) (tab : Table) (tv : Int64) (hok : TableOk tb tab)
    (hkl : tb.kl ≤ tb.cols.length) :
    (((tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail).map (·.take tb.kl)).Nodup ∧
      ∀ r ∈ (tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail, tb.kl ≤ r.length := by
  obtain ⟨-, -, hrows, hnd⟩ := hok
  refine ⟨?_, ?_⟩
  · have h1 : ((tab.rows.filter (fun r => r.head? = some (.int tv))).map (·.take (tb.kl + 1))).Nodup :=
      hnd.sublist (List.filter_sublist.map _)
    rw [List.map_map]
    have e : ∀ r ∈ tab.rows.filter (fun r => r.head? = some (.int tv)),
        r.take (tb.kl + 1) = .int tv :: ((·.take tb.kl) ∘ List.tail) r := by
      intro r hr
      have hh := (List.mem_filter.1 hr).2
      cases r with
      | nil => simp at hh
      | cons x xs => simp at hh; subst hh; simp
    rw [List.map_congr_left e] at h1
    have h2 : (((tab.rows.filter (fun r => r.head? = some (.int tv))).map ((·.take tb.kl) ∘ List.tail)).map
        (List.cons (Val.int tv))).Nodup := by
      simpa [List.map_map, Function.comp_def] using h1
    exact nodup_of_map _ h2
  · intro r hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.1 hr
    have := rowOk_length (hrows r0 (List.mem_filter.1 hr0).1)
    simp only [List.length_tail]
    omega

theorem put_self (db : PgDb) (n : String) (t : Table) : put db n t n = some t := by simp [put]

theorem put_other (db : PgDb) (n n' : String) (t : Table) (h : n' ≠ n) : put db n t n' = db n' := by
  simp [put, h]

/-- Replacing the rows of one table: the schema still matches, the tenant's rows of that table
change by `F`, other tables and tenants keep theirs. -/
theorem put_sound {ts : List Tab} {tv : Int64} {db : PgDb} (hv : Valid ts) (hm : Matches ts db)
    {t : Nat} {tb : Tab} {tab : Table} (ht : ts[t]? = some tb) (hdb : db tb.name = some tab)
    (rows' : List (List Val)) (hok : TableOk tb { tab with rows := rows' })
    (F : List (List Val) → List (List Val))
    (hF : (rows'.filter (fun r => r.head? = some (.int tv))).map List.tail =
      F ((tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail))
    (hother : ∀ tv', tv' ≠ tv →
      rows'.filter (fun r => r.head? = some (.int tv')) = tab.rows.filter (fun r => r.head? = some (.int tv'))) :
    Matches ts (put db tb.name { tab with rows := rows' }) ∧
      tenantTabs ts tv (put db tb.name { tab with rows := rows' }) =
        (fun t' => if t' = t then F (tenantTabs ts tv db t) else tenantTabs ts tv db t') ∧
      (∀ tv', tv' ≠ tv → tenantTabs ts tv' (put db tb.name { tab with rows := rows' }) = tenantTabs ts tv' db) ∧
      ∀ n, n ∉ ts.map (·.name) → put db tb.name { tab with rows := rows' } n = db n := by
  have same : ∀ {t' : Nat} {tb' : Tab}, ts[t']? = some tb' → (tb'.name = tb.name ↔ t' = t) := by
    intro t' tb' h'
    constructor
    · exact fun hn => index_of_name hv ht h' hn
    · rintro rfl
      rw [ht] at h'
      rw [Option.some.inj h']
  have eq_of : ∀ {t' : Nat} {tb' : Tab}, ts[t']? = some tb' → tb'.name = tb.name → tb' = tb := by
    intro t' tb' h' hn
    have e := (same h').1 hn
    subst e
    rw [ht] at h'
    exact (Option.some.inj h').symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro tb' hmem
    obtain ⟨t', h'⟩ := List.mem_iff_getElem?.1 hmem
    by_cases hn : tb'.name = tb.name
    · rw [eq_of h' hn]
      exact ⟨_, put_self _ _ _, hok⟩
    · rw [put_other _ _ _ _ hn]; exact hm tb' hmem
  · funext t'
    cases h' : ts[t']? with
    | none =>
      have : t' ≠ t := by rintro rfl; rw [ht] at h'; cases h'
      simp [tenantTabs, h', this]
    | some tb' =>
      by_cases hn : tb'.name = tb.name
      · have e := (same h').1 hn
        have hb := eq_of h' hn
        subst e hb
        rw [tenantTabs_some h' (put_self _ _ _), tenantTabs_some h' hdb, ite_eq_left rfl]
        exact hF
      · have : t' ≠ t := fun e => hn ((same h').2 e)
        simp only [tenantTabs, h', put_other _ _ _ _ hn, this, ite_false]
  · intro tv' hne
    funext t'
    cases h' : ts[t']? with
    | none => simp [tenantTabs, h']
    | some tb' =>
      by_cases hn : tb'.name = tb.name
      · have hb := eq_of h' hn
        subst hb
        rw [tenantTabs_some h' (put_self _ _ _), tenantTabs_some h' hdb, hother tv' hne]
      · simp only [tenantTabs, h', put_other _ _ _ _ hn]
  · intro n hn
    apply put_other
    rintro rfl
    exact hn (List.mem_map.2 ⟨tb, List.mem_of_getElem? ht, rfl⟩)

theorem wellKeyed_tenant {ts : List Tab} (hv : Valid ts) (tv : Int64) {db : PgDb} (hm : Matches ts db) :
    WellKeyed (klOf ts) (tenantTabs ts tv db) := by
  intro t
  cases ht : ts[t]? with
  | none => simp [tenantTabs, ht]
  | some tb =>
    obtain ⟨tab, hdb, hok⟩ := hm tb (List.mem_of_getElem? ht)
    rw [tenantTabs_some ht hdb, klOf_some ht]
    exact tenant_rows_keyed tb tab tv hok (kl_le (tabOk_of hv ht))

theorem filter_tail (rows : List (List Val)) (tv : Int64) (P : List Val → Prop) (Q : List Val → Prop)
    [DecidablePred P] [DecidablePred Q]
    (h : ∀ r ∈ rows, r.head? = some (.int tv) → (P r ↔ Q r.tail)) :
    ((rows.filter (fun r => ¬ P r)).filter (fun r => r.head? = some (.int tv))).map List.tail =
      ((rows.filter (fun r => r.head? = some (.int tv))).map List.tail).filter (fun x => ¬ Q x) := by
  rw [List.filter_map, List.filter_filter, List.filter_filter]
  congr 1
  apply List.filter_congr
  intro r hr
  by_cases hh : r.head? = some (.int tv)
  · simp [hh, h r hr hh]
  · simp [hh]

theorem filter_other (rows : List (List Val)) (tv tv' : Int64) (hne : tv' ≠ tv) (P : List Val → Prop)
    [DecidablePred P] (h : ∀ r ∈ rows, P r → r.head? = some (.int tv)) :
    (rows.filter (fun r => ¬ P r)).filter (fun r => r.head? = some (.int tv')) =
      rows.filter (fun r => r.head? = some (.int tv')) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro r hr
  by_cases hh : r.head? = some (.int tv')
  · have : ¬ P r := fun hp => hne (Val.int.inj (Option.some.inj (hh.symm.trans (h r hr hp))))
    simp [hh, this]
  · simp [hh]

theorem tableOk_sublist {tb : Tab} {tab : Table} (hok : TableOk tb tab) {rows' : List (List Val)}
    (hs : rows'.Sublist tab.rows) : TableOk tb { tab with rows := rows' } :=
  ⟨hok.1, hok.2.1, fun r hr => hok.2.2.1 r (hs.subset hr), hok.2.2.2.sublist (hs.map _)⟩

theorem colIdx_tenant {tb : Tab} (hn : (names tb).Nodup) : colIdx (colDefs tb) "tenant_id" = some 0 :=
  colIdx_colDefs tb hn 0 (by omega)

theorem colIdx_col {tb : Tab} (hn : (names tb).Nodup) (i : Nat) (hi : i < tb.cols.length) :
    colIdx (colDefs tb) tb.cols[i].name = some (i + 1) := by
  have := colIdx_colDefs tb hn (i + 1) (by omega)
  rwa [names_succ tb i hi] at this

theorem colDefs_succ (tb : Tab) (i : Nat) (hi : i < tb.cols.length) :
    (colDefs tb)[i + 1]? = some ⟨tb.cols[i].name, tb.cols[i].kind, !tb.cols[i].nullable || decide (i < tb.kl)⟩ := by
  simp [colDefs, hi]

theorem condOk_tenant {tb : Tab} (hn : (names tb).Nodup) (tv : Int64) (ps : List Val) :
    CondOk (colDefs tb) (.int tv :: ps) (.eq "tenant_id" 1) :=
  ⟨0, _, .int tv, colIdx_tenant hn, rfl, by simp [arg], Or.inr rfl⟩

theorem holds_tenant {tb : Tab} (hn : (names tb).Nodup) (tv : Int64) (ps : List Val) (r : List Val) :
    CondHolds (colDefs tb) (.int tv :: ps) r (.eq "tenant_id" 1) ↔ r.head? = some (.int tv) := by
  simp only [CondHolds, colIdx_tenant hn, arg]
  constructor
  · rintro ⟨i, v, hi, hv, hr, -⟩
    cases hi; simp at hv; subst hv; rwa [List.head?_eq_getElem?]
  · intro h
    exact ⟨0, .int tv, rfl, by simp, by rwa [← List.head?_eq_getElem?], by simp [kindOf]⟩

theorem mapM_some {α β : Type} (f : α → Option β) (l : List α) (out : List β) (hl : l.length = out.length)
    (h : ∀ j (hj : j < l.length), f l[j] = some (out[j]'(hl ▸ hj))) : l.mapM f = some out := by
  induction l generalizing out with
  | nil => cases out with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons a xs ih =>
    cases out with
    | nil => simp at hl
    | cons o os =>
      have h0 := h 0 (by simp)
      have ht := ih os (by simpa using hl) (fun j hj => h (j + 1) (by simp; omega))
      simp only [List.getElem_cons_zero] at h0
      simp [List.mapM_cons, h0, ht]

theorem newRow_self (tb : Tab) (hn : (names tb).Nodup) (ps : List Val) (hl : ps.length = tb.cols.length + 1) :
    newRow (colDefs tb) (names tb) ps = some ps := by
  apply mapM_some _ _ _ (by rw [colDefs_length, hl])
  intro j hj
  have hj' : j < (names tb).length := by rw [names_length]; rw [colDefs_length] at hj; exact hj
  have e : (colDefs tb)[j].name = (names tb)[j] := by simp only [← colDefs_names, List.getElem_map]
  rw [e, List.Nodup.idxOf_getElem hn j hj']
  simp

/-- Projecting on the first `m` names takes the first `m` values. -/
theorem project_take (tb : Tab) (hn : (names tb).Nodup) (x : List Val) (hx : x.length = tb.cols.length + 1) :
    ∀ m, m ≤ tb.cols.length + 1 → project (colDefs tb) ((names tb).take m) x = x.take m := by
  intro m
  induction m with
  | zero => intro _; simp [project]
  | succ m ih =>
    intro hm
    have hm' : m < (names tb).length := by rw [names_length]; omega
    rw [List.take_succ_eq_append_getElem hm', List.take_succ_eq_append_getElem (by omega)]
    simp only [project, List.filterMap_append] at ih ⊢
    have hc := colIdx_colDefs tb hn m (by omega)
    rw [ih (by omega)]
    simp [hc, List.getElem?_eq_getElem (show m < x.length by omega)]

theorem project_key (tb : Tab) (hn : (names tb).Nodup) (hkl : tb.kl ≤ tb.cols.length) (x : List Val)
    (hx : x.length = tb.cols.length + 1) : project (colDefs tb) (keyNames tb) x = x.take (tb.kl + 1) := by
  rw [keyNames_take]; exact project_take tb hn x hx _ (by omega)

/-- On a key conflict, `DO UPDATE SET` of the columns outside the key gives the new row. -/
theorem setCols_eq (tb : Tab) (hn : (names tb).Nodup) (x new : List Val)
    (hx : x.length = tb.cols.length + 1) (hnew : new.length = tb.cols.length + 1)
    (hk : x.take (tb.kl + 1) = new.take (tb.kl + 1)) :
    setCols (colDefs tb) ((tb.cols.drop tb.kl).map (·.name)) x new = new := by
  have hup : (tb.cols.drop tb.kl).map (·.name) = (names tb).drop (tb.kl + 1) := by
    simp [names, List.map_drop]
  rw [hup]
  apply List.ext_getElem
  · simp [setCols, colDefs_length, hx, hnew]
  · intro j h1 h2
    simp only [setCols, List.getElem_map, List.getElem_zip]
    have hj : j < (names tb).length := by rw [names_length]; omega
    have e : ((colDefs tb)[j]'(by rw [colDefs_length]; omega)).name = (names tb)[j] := by
      simp only [← colDefs_names, List.getElem_map]
    rw [e]
    by_cases hjk : tb.kl + 1 ≤ j
    · rw [ite_eq_left]
      rw [List.mem_iff_getElem]
      exact ⟨j - (tb.kl + 1), by simp; omega, by simp; congr 1; omega⟩
    · rw [ite_eq_right]
      · have := congrArg (·[j]?) hk
        simp only [List.getElem?_take, ite_eq_left (show j < tb.kl + 1 by omega)] at this
        rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega)] at this
        exact Option.some.inj this
      · rw [List.mem_iff_getElem]
        rintro ⟨i, hi, he⟩
        simp only [List.getElem_drop] at he
        have := (List.Nodup.getElem_inj hn).1 he
        simp at hi; omega

/-! ## Each compiled statement does what `exec` says -/

theorem forall_zipIdx (P : Nat → Val → Prop) (l : List Val) (n : Nat) :
    (∀ p ∈ l.zipIdx n, P p.2 p.1) ↔ ∀ i (h : i < l.length), P (n + i) l[i] := by
  induction l generalizing n with
  | nil => simp
  | cons v l ih =>
    simp only [List.zipIdx_cons, List.forall_mem_cons, ih]
    constructor
    · rintro ⟨h0, h⟩ i hi
      cases i with
      | zero => exact h0
      | succ i =>
        have := h i (by simp at hi; omega)
        rw [show n + (i + 1) = n + 1 + i by omega]
        exact this
    · intro h
      refine ⟨h 0 (by simp), fun i hi => ?_⟩
      have := h (i + 1) (by simp; omega)
      rw [show n + (i + 1) = n + 1 + i by omega] at this
      exact this

theorem fitsFrom_get {tb : Tab} {n : Nat} {l : List Val} (h : fitsFrom tb n l = true) :
    ∀ i (hi : i < l.length), FitsAt tb (n + i) l[i] :=
  (forall_zipIdx (fun i v => FitsAt tb i v) l n).1 ((fitsFrom_iff tb n l).1 h)

theorem fitsAt_exists {tb : Tab} {i : Nat} {v : Val} (h : FitsAt tb i v) :
    ∃ c, tb.cols[i]? = some c ∧ Typed c.kind v ∧ (kindOf v = none → c.nullable = true ∧ tb.kl ≤ i) := by
  unfold FitsAt at h
  split at h
  · exact h.elim
  · rename_i c hc
    exact ⟨c, hc, h.1, h.2⟩

/-- What a compiled statement does, on the tables: it changes the tenant's rows as `applyW` does,
and nothing else. -/
def Effect (ts : List Tab) (tv : Int64) (db db' : PgDb) (w : Write) : Prop :=
  Matches ts db' ∧ tenantTabs ts tv db' = applyW (klOf ts) (tenantTabs ts tv db) w ∧
    (∀ tv', tv' ≠ tv → tenantTabs ts tv' db' = tenantTabs ts tv' db) ∧
    ∀ n, n ∉ ts.map (·.name) → db' n = db n

theorem del_sound {ts : List Tab} {tv : Int64} {db : PgDb} (hvb : valid ts = true) (hm : Matches ts db)
    {t : Nat} {k : List Val} {q : Sql} {ps : List Val}
    (hc : compile ts tv (.delete t k) = some (q, ps)) :
    ∃ db', run db q ps = some db' ∧ Effect ts tv db db' (.del t k) ∧ 0 < klOf ts t := by
  have hv := (valid_iff ts).1 hvb
  simp only [compile, hvb, ite_true] at hc
  cases ht : ts[t]? with
  | none => simp [ht] at hc
  | some tb =>
    simp only [ht] at hc
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcond
      obtain ⟨⟨hkl0, hlen⟩, hfb⟩ := hcond
      have hfit : ∀ i (hi : i < k.length), FitsAt tb i k[i] := fun i hi => by
        simpa using fitsFrom_get hfb i hi
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨tab, hdb, hok⟩ := hm tb (List.mem_of_getElem? ht)
      have tok := tabOk_of hv ht
      have hn := names_nodup tok
      have hkl := kl_le tok
      obtain ⟨hcols, hkey, hrows, hnd⟩ := hok
      have hki : ∀ i (hi : i < k.length), i < tb.cols.length ∧ kindOf k[i] ≠ none ∧
          (colDefs tb)[i + 1]? = some ⟨tb.cols[i].name, tb.cols[i].kind, !tb.cols[i].nullable || decide (i < tb.kl)⟩ ∧
          Typed tb.cols[i].kind k[i] := by
        intro i hi
        have hic : i < tb.cols.length := by omega
        obtain ⟨c, hc, hty, hnull⟩ := fitsAt_exists (hfit i hi)
        rw [List.getElem?_eq_getElem hic, Option.some.injEq] at hc
        subst hc
        exact ⟨hic, fun h0 => by have := (hnull h0).2; omega, colDefs_succ tb i hic, hty⟩
      -- The conditions: the tenant, then each key column.
      have hmem : ∀ c ∈ (tb.cols.take tb.kl).mapIdx (fun i c => Cond.eq c.name (i + 2)),
          ∃ i, ∃ hi : i < k.length, c = .eq tb.cols[i].name (i + 2) := by
        intro c hc
        obtain ⟨i, hi, rfl⟩ := List.mem_mapIdx.1 hc
        have hi' : i < k.length := by simp at hi; omega
        exact ⟨i, hi', by simp⟩
      have hok' : ∀ c ∈ Cond.eq "tenant_id" 1 :: (tb.cols.take tb.kl).mapIdx (fun i c => Cond.eq c.name (i + 2)),
          CondOk tab.cols (.int tv :: k) c := by
        intro c hc
        rw [hcols]
        rcases List.mem_cons.1 hc with rfl | hc
        · exact condOk_tenant hn tv k
        · obtain ⟨i, hi, rfl⟩ := hmem c hc
          obtain ⟨hic, -, hd, hty⟩ := hki i hi
          exact ⟨i + 1, _, k[i], colIdx_col hn i hic, hd, by simp [arg, hi], hty⟩
      -- On the tenant's rows, the conditions say that the key is `k`.
      have hall : ∀ r ∈ tab.rows, r.head? = some (.int tv) →
          (AllHold tab.cols (.int tv :: k) r (Cond.eq "tenant_id" 1 :: (tb.cols.take tb.kl).mapIdx
            (fun i c => Cond.eq c.name (i + 2))) ↔ r.tail.take tb.kl = k) := by
        intro r hr hh
        have hrl := rowOk_length (hrows r hr)
        rw [hcols]
        constructor
        · intro hA
          apply List.ext_getElem?
          intro i
          by_cases hi : i < k.length
          · have hc : Cond.eq tb.cols[i].name (i + 2) ∈ (tb.cols.take tb.kl).mapIdx (fun i c => Cond.eq c.name (i + 2)) := by
              apply List.mem_mapIdx.2
              exact ⟨i, by simp; omega, by simp⟩
            obtain ⟨j, v, hj, hv', hrv, -⟩ := hA _ (List.mem_cons_of_mem _ hc)
            rw [colIdx_col hn i (hki i hi).1] at hj
            cases hj
            have hv2 : k[i]? = some v := by simpa [arg] using hv'
            rw [hv2, List.getElem?_take, ite_eq_left (by omega), List.getElem?_tail, hrv]
          · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]
        · intro hk c hc
          rcases List.mem_cons.1 hc with rfl | hc
          · exact (holds_tenant hn tv k r).2 hh
          · obtain ⟨i, hi, rfl⟩ := hmem c hc
            refine ⟨i + 1, k[i], colIdx_col hn i (hki i hi).1, by simp [arg, hi], ?_, (hki i hi).2.1⟩
            have := congrArg (·[i]?) hk
            simp only [List.getElem?_take, ite_eq_left (show i < tb.kl by omega), List.getElem?_tail] at this
            rw [this, List.getElem?_eq_getElem hi]
      have htenant : ∀ r ∈ tab.rows, AllHold tab.cols (.int tv :: k) r (Cond.eq "tenant_id" 1 ::
          (tb.cols.take tb.kl).mapIdx (fun i c => Cond.eq c.name (i + 2))) → r.head? = some (.int tv) := by
        intro r _ hA
        have := hA _ List.mem_cons_self
        rw [hcols] at this
        exact (holds_tenant hn tv k r).1 this
      refine ⟨_, by simp only [run, hdb]; rw [ite_eq_left hok'], ?_⟩
      obtain ⟨h1, h2, h3, h4⟩ := put_sound hv hm ht hdb _
        (tableOk_sublist ⟨hcols, hkey, hrows, hnd⟩ List.filter_sublist)
        (fun l => l.filter (fun x => ¬ x.take tb.kl = k))
        (filter_tail _ tv _ _ hall)
        (fun tv' hne => filter_other _ tv tv' hne _ htenant)
      refine ⟨⟨h1, ?_, h3, h4⟩, by rw [klOf_some ht]; exact hkl0⟩
      rw [h2]
      funext t'
      simp only [applyW, klOf_some ht]
    · simp at hc

theorem delWhere_sound {ts : List Tab} {tv : Int64} {db : PgDb} (hvb : valid ts = true)
    (hm : Matches ts db) {t i : Nat} {v : Val} {q : Sql} {ps : List Val}
    (hc : compile ts tv (.deleteWhere t i v) = some (q, ps)) :
    ∃ db', run db q ps = some db' ∧ Effect ts tv db db' (.delWhere t i v) ∧ 0 < klOf ts t := by
  have hv := (valid_iff ts).1 hvb
  simp only [compile, hvb, ite_true] at hc
  cases ht : ts[t]? with
  | none => simp [ht] at hc
  | some tb =>
    simp only [ht] at hc
    cases hci : tb.cols[i]? with
    | none => simp [hci] at hc
    | some c =>
      simp only [hci] at hc
      split at hc
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq, typed_iff] at hcond
        obtain ⟨hkl0, hty⟩ := hcond
        simp only [Option.some.injEq, Prod.mk.injEq] at hc
        obtain ⟨rfl, rfl⟩ := hc
        obtain ⟨tab, hdb, hcols, hkey, hrows, hnd⟩ := hm tb (List.mem_of_getElem? ht)
        have hn := names_nodup (tabOk_of hv ht)
        obtain ⟨hic, rfl⟩ := List.getElem?_eq_some_iff.1 hci
        have hcol := colIdx_col hn i hic
        have hok' : ∀ d ∈ [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2],
            CondOk tab.cols [.int tv, v] d := by
          intro d hd
          rw [hcols]
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
          rcases hd with rfl | rfl
          · exact condOk_tenant hn tv [v]
          · exact ⟨i + 1, _, v, hcol, colDefs_succ tb i hic, by simp [arg], hty⟩
        have hall : ∀ r ∈ tab.rows, r.head? = some (.int tv) →
            (AllHold tab.cols [.int tv, v] r [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2] ↔
              r.tail[i]? = some v) := by
          intro r _ hh
          have e : AllHold (colDefs tb) [.int tv, v] r [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2] ↔
              CondHolds (colDefs tb) [.int tv, v] r (Cond.eq "tenant_id" 1) ∧
                CondHolds (colDefs tb) [.int tv, v] r (Cond.same tb.cols[i].name 2) := by
            simp [AllHold]
          rw [hcols, e, holds_tenant hn tv [v] r, List.getElem?_tail]
          simp only [hh, true_and, CondHolds, hcol]
          constructor
          · rintro ⟨j, w, hj, hw, hr⟩
            cases hj; simp [arg] at hw; subst hw; exact hr
          · intro hr
            exact ⟨i + 1, v, rfl, by simp [arg], hr⟩
        have htenant : ∀ r ∈ tab.rows,
            AllHold tab.cols [.int tv, v] r [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2] →
              r.head? = some (.int tv) := by
          intro r _ hA
          have := hA _ List.mem_cons_self
          rw [hcols] at this
          exact (holds_tenant hn tv [v] r).1 this
        refine ⟨_, by simp only [run, hdb]; rw [ite_eq_left hok'], ?_⟩
        obtain ⟨h1, h2, h3, h4⟩ := put_sound hv hm ht hdb _
          (tableOk_sublist ⟨hcols, hkey, hrows, hnd⟩ List.filter_sublist)
          (fun l => l.filter (fun x => ¬ x[i]? = some v))
          (filter_tail _ tv _ _ hall)
          (fun tv' hne => filter_other _ tv tv' hne _ htenant)
        refine ⟨⟨h1, ?_, h3, h4⟩, by rw [klOf_some ht]; exact hkl0⟩
        rw [h2]
        funext t'
        simp only [applyW]
      · simp at hc

theorem stores_row (tb : Tab) (tv : Int64) (row : List Val) (hl : row.length = tb.cols.length)
    (hfit : ∀ i (hi : i < row.length), FitsAt tb i row[i]) : RowOk tb (.int tv :: row) := by
  refine ⟨by simp [colDefs_length, hl], fun j h1 h2 => ?_⟩
  cases j with
  | zero => exact ⟨Or.inr rfl, fun _ => by simp [kindOf]⟩
  | succ i =>
    have hi : i < row.length := by simp at h2; omega
    obtain ⟨c, hc, hty, hnull⟩ := fitsAt_exists (hfit i hi)
    have hic : i < tb.cols.length := by omega
    rw [List.getElem?_eq_getElem hic, Option.some.injEq] at hc
    subst hc
    have e : (colDefs tb)[i + 1] = ⟨tb.cols[i].name, tb.cols[i].kind, !tb.cols[i].nullable || decide (i < tb.kl)⟩ := by
      simp [colDefs]
    rw [e]
    refine ⟨by simpa using hty, fun hnn h0 => ?_⟩
    obtain ⟨h3, h4⟩ := hnull (by simpa using h0)
    simp [h3] at hnn; omega

theorem up_sound {ts : List Tab} {tv : Int64} {db : PgDb} (hvb : valid ts = true) (hm : Matches ts db)
    {t : Nat} {k r : List Val} {q : Sql} {ps : List Val}
    (hc : compile ts tv (.upsert t k r) = some (q, ps)) :
    ∃ db', run db q ps = some db' ∧ Effect ts tv db db' (.put t (klOf ts t) (k ++ r)) ∧
      k.length = klOf ts t := by
  have hv := (valid_iff ts).1 hvb
  simp only [compile, hvb, ite_true] at hc
  cases ht : ts[t]? with
  | none => simp [ht] at hc
  | some tb =>
    simp only [ht] at hc
    split at hc
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      obtain ⟨⟨⟨hlen, hlen2⟩, hfkb⟩, hfrb⟩ := hcond
      have hfk : ∀ i (hi : i < k.length), FitsAt tb i k[i] := fun i hi => by
        simpa using fitsFrom_get hfkb i hi
      have hfr := fitsFrom_get hfrb
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      obtain ⟨tab, hdb, hcols, hkey, hrows, hnd⟩ := hm tb (List.mem_of_getElem? ht)
      have tok := tabOk_of hv ht
      have hn := names_nodup tok
      have hkl := kl_le tok
      rw [klOf_some ht]
      have hrl : (k ++ r).length = tb.cols.length := by simp; omega
      have hfit : ∀ i (hi : i < (k ++ r).length), FitsAt tb i (k ++ r)[i] := by
        intro i hi
        by_cases hik : i < k.length
        · rw [List.getElem_append_left hik]; exact hfk i hik
        · rw [List.getElem_append_right (by omega)]
          have := hfr (i - k.length) (by simp at hi; omega)
          rwa [show tb.kl + (i - k.length) = i by omega] at this
      have hnewok := stores_row tb tv (k ++ r) hrl hfit
      have hlnew : (Val.int tv :: (k ++ r)).length = tb.cols.length + 1 := by simp [hrl]
      have hkeynew : (Val.int tv :: (k ++ r)).take (tb.kl + 1) = .int tv :: k := by
        simp [← hlen]
      have hrowlen : ∀ x ∈ tab.rows, x.length = tb.cols.length + 1 := fun x hx => rowOk_length (hrows x hx)
      -- The key the conflict clause compares.
      have hkeyof : ∀ x : List Val, x.length = tb.cols.length + 1 →
          project tab.cols tab.key x = x.take (tb.kl + 1) := by
        intro x hx; rw [hcols, hkey]; exact project_key tb hn hkl x hx
      have hchecks : (names tb).length = (Val.int tv :: (k ++ r)).length ∧ (names tb).Nodup ∧
          (∀ c ∈ tab.cols, c.name ∈ names tb) ∧ (∀ n ∈ names tb, ∃ c ∈ tab.cols, c.name = n) ∧
          (∀ n, n ∈ keyNames tb ↔ n ∈ tab.key) ∧
          (∀ n ∈ (tb.cols.drop tb.kl).map (·.name), ∃ c ∈ tab.cols, c.name = n) := by
        rw [hcols, hkey]
        refine ⟨by rw [names_length, hlnew], hn, fun c hc => ?_, fun n hn' => ?_, fun _ => Iff.rfl, fun n hn' => ?_⟩
        · rw [← colDefs_names]; exact List.mem_map_of_mem hc
        · rw [← colDefs_names] at hn'; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hn'; exact ⟨c, hc, rfl⟩
        · have : n ∈ names tb := by
            simp only [names, List.mem_cons]; right; exact List.map_subset _ (List.drop_subset _ _) hn'
          rw [← colDefs_names] at this; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 this; exact ⟨c, hc, rfl⟩
      have hnr : newRow tab.cols (names tb) (.int tv :: (k ++ r)) = some (.int tv :: (k ++ r)) := by
        rw [hcols]; exact newRow_self tb hn _ hlnew
      have hst : StoresAll tab.cols (.int tv :: (k ++ r)) := by rw [hcols]; exact hnewok
      -- The tenant's rows, and a row's key among them.
      have htk : ∀ x ∈ tab.rows,
          (x.take (tb.kl + 1) = .int tv :: k ↔ x.head? = some (.int tv) ∧ x.tail.take tb.kl = k) := by
        intro x hx
        have := hrowlen x hx
        cases x with
        | nil => simp at this
        | cons y ys => simp [List.take_succ_cons]
      have hwk := tenant_rows_keyed tb tab tv ⟨hcols, hkey, hrows, hnd⟩ hkl
      by_cases hex : ∃ x ∈ tab.rows, project tab.cols tab.key x = project tab.cols tab.key (.int tv :: (k ++ r))
      · -- A conflict: the row with the key becomes the new row.
        have hg : ∀ x ∈ tab.rows, (if project tab.cols tab.key x = project tab.cols tab.key (.int tv :: (k ++ r)) ∧
            (tb.cols.drop tb.kl).map (·.name) ≠ [] then
              setCols tab.cols ((tb.cols.drop tb.kl).map (·.name)) x (.int tv :: (k ++ r)) else x) =
            if x.take (tb.kl + 1) = .int tv :: k then .int tv :: (k ++ r) else x := by
          intro x hx
          rw [hkeyof x (hrowlen x hx), hkeyof _ hlnew, hkeynew]
          by_cases hxk : x.take (tb.kl + 1) = .int tv :: k
          · rw [ite_eq_left hxk]
            by_cases hup : (tb.cols.drop tb.kl).map (·.name) = []
            · rw [ite_eq_right (fun h => h.2 hup)]
              have hcl : tb.cols.length ≤ tb.kl := by simpa using hup
              rw [← List.take_of_length_le (show x.length ≤ tb.kl + 1 by rw [hrowlen x hx]; omega), hxk,
                ← hkeynew, List.take_of_length_le (by rw [hlnew]; omega)]
            · rw [ite_eq_left ⟨hxk, hup⟩, hcols]
              exact setCols_eq tb hn x _ (hrowlen x hx) hlnew (hxk.trans hkeynew.symm)
          · rw [ite_eq_right (fun h => hxk h.1), ite_eq_right hxk]
        let g : List Val → List Val := fun x => if x.take (tb.kl + 1) = .int tv :: k then .int tv :: (k ++ r) else x
        have hrows' : tab.rows.map (fun x => if project tab.cols tab.key x = project tab.cols tab.key (.int tv :: (k ++ r)) ∧
            (tb.cols.drop tb.kl).map (·.name) ≠ [] then
              setCols tab.cols ((tb.cols.drop tb.kl).map (·.name)) x (.int tv :: (k ++ r)) else x) =
            tab.rows.map g := List.map_congr_left hg
        refine ⟨put db tb.name { tab with rows := tab.rows.map g }, ?_, ?_, hlen⟩
        · simp only [run, hdb]
          rw [ite_eq_left hchecks, hnr]
          simp only
          rw [ite_eq_left hst, ite_eq_left hex, hrows']
        have hgk : ∀ x, (g x).take (tb.kl + 1) = x.take (tb.kl + 1) := by
          intro x; simp only [g]; split
          · rename_i h; rw [hkeynew, h]
          · rfl
        have hgh : ∀ x, (g x).head? = x.head? := by
          intro x; simp only [g]; split
          · rename_i h
            have := congrArg List.head? h
            rw [List.head?_take] at this
            simp at this; simp [this]
          · rfl
        have hok' : TableOk tb { tab with rows := tab.rows.map g } := by
          refine ⟨hcols, hkey, fun x hx => ?_, ?_⟩
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            simp only [g]; split
            · exact hnewok
            · exact hrows y hy
          · rw [List.map_map]
            have : ((fun x : List Val => x.take (tb.kl + 1)) ∘ g) = fun x => x.take (tb.kl + 1) := funext hgk
            rw [this]; exact hnd
        obtain ⟨h1, h2, h3, h4⟩ := put_sound (tv := tv) hv hm ht hdb _ hok'
          (fun l : List (List Val) => l.map (fun y : List Val => if y.take tb.kl = k then k ++ r else y))
          (by
            rw [List.filter_map, List.map_map, List.map_map]
            have e1 : ((fun r : List Val => decide (r.head? = some (Val.int tv))) ∘ g) =
                fun r => decide (r.head? = some (Val.int tv)) := by
              funext x; simp [hgh]
            rw [e1]
            apply List.map_congr_left
            intro x hx
            have hh := (List.mem_filter.1 hx).2
            have hxr := (List.mem_filter.1 hx).1
            simp only [decide_eq_true_eq] at hh
            simp only [Function.comp, g]
            by_cases hxk : x.take (tb.kl + 1) = .int tv :: k
            · rw [ite_eq_left hxk, ite_eq_left ((htk x hxr).1 hxk).2]; rfl
            · rw [ite_eq_right hxk, ite_eq_right (fun h => hxk ((htk x hxr).2 ⟨hh, h⟩))])
          (fun tv' hne => by
            rw [List.filter_map]
            have e1 : ((fun r : List Val => decide (r.head? = some (Val.int tv'))) ∘ g) =
                fun r => decide (r.head? = some (Val.int tv')) := by
              funext x; simp [hgh]
            rw [e1]
            refine (List.map_congr_left (g := id) (fun x hx => ?_)).trans (List.map_id _)
            have hh := (List.mem_filter.1 hx).2
            simp only [decide_eq_true_eq] at hh
            simp only [g, id]
            rw [ite_eq_right]
            intro hxk
            have := congrArg List.head? hxk
            rw [List.head?_take] at this
            simp [hh] at this
            exact hne this)
        refine ⟨h1, ?_, h3, h4⟩
        rw [h2]
        funext t'
        simp only [applyW, klOf_some ht]
        split
        · rename_i e
          subst e
          have hkk : (k ++ r).take tb.kl = k := by
            rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
          rw [tenantTabs_some ht hdb, upsert_found _ _ _ hwk.1]
          · simp only [hkk]
          · obtain ⟨x, hx, hxk⟩ := hex
            rw [hkeyof x (hrowlen x hx), hkeyof _ hlnew, hkeynew] at hxk
            obtain ⟨hh, hk⟩ := (htk x hx).1 hxk
            refine ⟨x.tail, List.mem_map.2 ⟨x, List.mem_filter.2 ⟨hx, by simpa using hh⟩, rfl⟩, ?_⟩
            rw [hk, hkk]
        · rfl
      · -- No conflict: the new row is appended.
        refine ⟨put db tb.name { tab with rows := tab.rows ++ [.int tv :: (k ++ r)] }, ?_, ?_, hlen⟩
        · simp only [run, hdb]
          rw [ite_eq_left hchecks, hnr]
          simp only
          rw [ite_eq_left hst, ite_eq_right hex]
        have hnot : ∀ x ∈ tab.rows, ¬ x.take (tb.kl + 1) = .int tv :: k := by
          intro x hx hxk
          apply hex
          refine ⟨x, hx, ?_⟩
          rw [hkeyof x (hrowlen x hx), hkeyof _ hlnew, hkeynew, hxk]
        have hok' : TableOk tb { tab with rows := tab.rows ++ [.int tv :: (k ++ r)] } := by
          refine ⟨hcols, hkey, fun x hx => ?_, ?_⟩
          · rcases List.mem_append.1 hx with hx | hx
            · exact hrows x hx
            · simp at hx; subst hx; exact hnewok
          · rw [List.map_append]
            apply List.nodup_append.2
            refine ⟨hnd, by simp, ?_⟩
            intro a ha b hb hab
            simp at hb; subst hb
            obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
            exact hnot x hx (hab.trans hkeynew)
        obtain ⟨h1, h2, h3, h4⟩ := put_sound (tv := tv) hv hm ht hdb _ hok'
          (fun l : List (List Val) => l ++ [k ++ r])
          (by simp [List.filter_append])
          (fun tv' hne => by
            rw [List.filter_append]
            have : ¬ tv = tv' := fun h => hne h.symm
            simp [this])
        refine ⟨h1, ?_, h3, h4⟩
        rw [h2]
        funext t'
        simp only [applyW, klOf_some ht]
        split
        · rename_i e
          subst e
          rw [tenantTabs_some ht hdb, upsert_new]
          intro y hy hyk
          obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hy
          have hh := (List.mem_filter.1 hx).2
          simp only [decide_eq_true_eq] at hh
          apply hnot x (List.mem_filter.1 hx).1
          rw [(htk x (List.mem_filter.1 hx).1).2]
          refine ⟨hh, ?_⟩
          rw [hyk, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
        · rfl
    · simp at hc

/-- The view after an effect: `exec`, for this tenant; the same, for the others. -/
theorem effect_view {ts : List Tab} (hv : Valid ts) {tv : Int64} {db db' : PgDb} (hm : Matches ts db)
    {w : Write} (he : Effect ts tv db db' w) (hw : WriteOk (klOf ts) w) :
    view ts tv db' = exec (view ts tv db) (plan w) ∧ ∀ tv', tv' ≠ tv → view ts tv' db' = view ts tv' db := by
  obtain ⟨-, h2, h3, -⟩ := he
  refine ⟨?_, fun tv' hne => by simp only [view, h3 tv' hne]⟩
  simp only [view, h2]
  exact (step_sound (klOf ts) _ w (wellKeyed_tenant hv tv hm) hw).1

/-- A compiled statement runs, keeps the tables as `create` made them, does to the tenant's
database what `exec` says, and changes no other tenant's database and no table outside the
schema. -/
theorem compile_sound {ts : List Tab} {tv : Int64} {db : PgDb} {s : Stmt} {q : Sql} {ps : List Val}
    (hv : valid ts = true) (hm : Matches ts db) (hc : compile ts tv s = some (q, ps)) :
    ∃ db', run db q ps = some db' ∧ Matches ts db' ∧ view ts tv db' = exec (view ts tv db) s ∧
      (∀ tv', tv' ≠ tv → view ts tv' db' = view ts tv' db) ∧ ∀ n, n ∉ ts.map (·.name) → db' n = db n := by
  have hV := (valid_iff ts).1 hv
  cases s with
  | upsert t k r =>
    obtain ⟨db', hr, he, hk⟩ := up_sound hv hm hc
    have hw : WriteOk (klOf ts) (.put t (klOf ts t) (k ++ r)) := ⟨rfl, by simp; omega⟩
    obtain ⟨h1, h2⟩ := effect_view hV hm he hw
    have e : plan (Write.put t (klOf ts t) (k ++ r)) = .upsert t k r := by
      simp [plan, ← hk, List.take_left', List.drop_left']
    exact ⟨db', hr, he.1, e ▸ h1, h2, he.2.2.2⟩
  | delete t k =>
    obtain ⟨db', hr, he, hk⟩ := del_sound hv hm hc
    obtain ⟨h1, h2⟩ := effect_view hV hm he hk
    exact ⟨db', hr, he.1, h1, h2, he.2.2.2⟩
  | deleteWhere t i v =>
    obtain ⟨db', hr, he, hk⟩ := delWhere_sound hv hm hc
    obtain ⟨h1, h2⟩ := effect_view hV hm he hk
    exact ⟨db', hr, he.1, h1, h2, he.2.2.2⟩

/-- Compiled statements, run in order, do what `execAll` says. -/
theorem compileAll_sound {ts : List Tab} {tv : Int64} (hv : valid ts = true) :
    ∀ (ss : List Stmt) (qs : List (Sql × List Val)) (db : PgDb), Matches ts db →
      ss.mapM (compile ts tv) = some qs →
      ∃ db', runAll db qs = some db' ∧ Matches ts db' ∧ view ts tv db' = execAll (view ts tv db) ss ∧
        (∀ tv', tv' ≠ tv → view ts tv' db' = view ts tv' db) ∧ ∀ n, n ∉ ts.map (·.name) → db' n = db n := by
  intro ss
  induction ss with
  | nil =>
    intro qs db hm h
    simp at h; subst h
    exact ⟨db, rfl, hm, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | cons s ss ih =>
    intro qs db hm h
    cases hq : compile ts tv s with
    | none => simp [List.mapM_cons, hq] at h
    | some q =>
    cases hqs : ss.mapM (compile ts tv) with
    | none => simp [List.mapM_cons, hq, hqs] at h
    | some qs' =>
    simp [List.mapM_cons, hq, hqs] at h
    subst h
    obtain ⟨db1, hr1, hm1, hv1, ho1, hn1⟩ := compile_sound hv hm hq
    obtain ⟨db2, hr2, hm2, hv2, ho2, hn2⟩ := ih qs' db1 hm1 hqs
    refine ⟨db2, by simp [runAll, hr1, hr2], hm2, ?_, fun tv' hne => (ho2 tv' hne).trans (ho1 tv' hne),
      fun n hn => (hn2 n hn).trans (hn1 n hn)⟩
    rw [hv2, hv1]; rfl

/-! ## A compiled `SELECT` returns the tenant's rows -/

/-- Selecting every column but `tenant_id` drops the `tenant_id` value. -/
theorem project_cols (tb : Tab) (hn : (names tb).Nodup) (x : List Val) (hx : x.length = tb.cols.length + 1) :
    project (colDefs tb) (tb.cols.map (·.name)) x = x.tail := by
  have h := project_take tb hn x hx (tb.cols.length + 1) (Nat.le_refl _)
  rw [List.take_of_length_le (by simp [names_length]), List.take_of_length_le (by omega)] at h
  have hc := colIdx_tenant (tb := tb) hn
  cases x with
  | nil => simp at hx
  | cons y ys =>
    simp only [names, project, List.filterMap_cons, hc] at h
    simp only [Option.bind_some, List.getElem?_cons_zero, List.cons.injEq] at h
    exact h.2

/-- A compiled `SELECT` returns the tenant's rows of the table that pass the filter, each once,
in any order. -/
theorem select_sound {ts : List Tab} {tv : Int64} {db : PgDb} {t : Nat} {f : Option (Nat × Val)}
    {q : Sql} {ps : List Val} (hvb : valid ts = true) (hm : Matches ts db)
    (hc : select ts tv t f = some (q, ps)) :
    ∃ R0, selected db q ps = some R0 ∧ ∀ R, R.Perm R0 → Sel (klOf ts) (view ts tv db) t (Filter f) R := by
  have hv := (valid_iff ts).1 hvb
  simp only [select, hvb, ite_true] at hc
  cases ht : ts[t]? with
  | none => simp [ht] at hc
  | some tb =>
    simp only [ht] at hc
    obtain ⟨tab, hdb, hcols, hkey, hrows, hnd⟩ := hm tb (List.mem_of_getElem? ht)
    have hn := names_nodup (tabOk_of hv ht)
    have hkl := kl_le (tabOk_of hv ht)
    have hrowlen : ∀ x ∈ tab.rows, x.length = tb.cols.length + 1 := fun x hx => rowOk_length (hrows x hx)
    have hwk := tenant_rows_keyed tb tab tv ⟨hcols, hkey, hrows, hnd⟩ hkl
    have hL := tenantTabs_some (tv := tv) ht hdb
    have hns : ∀ n ∈ tb.cols.map (·.name), ∃ c ∈ tab.cols, c.name = n := by
      intro n hn'
      have : n ∈ names tb := List.mem_cons_of_mem _ hn'
      rw [hcols, ← colDefs_names] at *
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 this; exact ⟨c, hc, rfl⟩
    -- Once the statement is known: its rows are the tenant's rows that pass the filter.
    have key : ∀ conds, (∀ c ∈ conds, CondOk tab.cols ps c) →
        (∀ x ∈ tab.rows, (AllHold tab.cols ps x conds ↔ x.head? = some (.int tv) ∧ Filter f x.tail)) →
        q = .select tb.name (tb.cols.map (·.name)) conds ((tb.cols.take tb.kl).map (·.name)) →
        ∃ R0, selected db q ps = some R0 ∧ ∀ R, R.Perm R0 → Sel (klOf ts) (view ts tv db) t (Filter f) R := by
      intro conds hok hall hq
      subst hq
      refine ⟨_, by simp only [selected, hdb]; rw [ite_eq_left ⟨hok, hns⟩], fun R hR => ?_⟩
      have e : (tab.rows.filter (fun x => AllHold tab.cols ps x conds)).map
          (project tab.cols (tb.cols.map (·.name))) =
          ((tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail).filter (Filter f) := by
        rw [List.filter_map, List.filter_filter]
        rw [List.map_congr_left (g := List.tail) (fun x hx => by
          rw [hcols]; exact project_cols tb hn x (hrowlen x (List.mem_filter.1 hx).1))]
        congr 1
        apply List.filter_congr
        intro x hx
        rw [hall x hx]
        simp only [Function.comp]
        by_cases h1 : x.head? = some (.int tv) <;> by_cases h2 : Filter f x.tail <;> simp [h1, h2]
      rw [e] at hR
      have hLn : ((tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail).Nodup :=
        nodup_of_map _ hwk.1
      refine ⟨hR.nodup_iff.2 (hLn.sublist List.filter_sublist), fun row => ?_⟩
      rw [hR.mem_iff, List.mem_filter, decide_eq_true_eq]
      simp only [view, readBack, klOf_some ht, hL]
      rw [find_key_iff (fun r : List Val => r.take tb.kl) _ hwk.1 _ row]
      simp
    cases f with
    | none =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      apply key [Cond.eq "tenant_id" 1]
      · intro c hc'; simp at hc'; subst hc'; rw [hcols]; exact condOk_tenant hn tv []
      · intro x _
        simp only [AllHold, List.mem_singleton, forall_eq, hcols, holds_tenant hn tv [] x, Filter, and_true]
      · rfl
    | some p =>
      obtain ⟨i, v⟩ := p
      cases hci : tb.cols[i]? with
      | none => simp [hci] at hc
      | some c =>
        simp only [hci] at hc
        split at hc
        · rename_i htyb
          have hty : Typed c.kind v := (typed_iff _ _).1 htyb
          simp only [Option.some.injEq, Prod.mk.injEq] at hc
          obtain ⟨rfl, rfl⟩ := hc
          obtain ⟨hic, rfl⟩ := List.getElem?_eq_some_iff.1 hci
          have hcol := colIdx_col hn i hic
          apply key [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2]
          · intro d hd
            rw [hcols]
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
            rcases hd with rfl | rfl
            · exact condOk_tenant hn tv [v]
            · exact ⟨i + 1, _, v, hcol, colDefs_succ tb i hic, by simp [arg], hty⟩
          · intro x _
            have e : AllHold (colDefs tb) [.int tv, v] x [Cond.eq "tenant_id" 1, Cond.same tb.cols[i].name 2] ↔
                CondHolds (colDefs tb) [.int tv, v] x (Cond.eq "tenant_id" 1) ∧
                  CondHolds (colDefs tb) [.int tv, v] x (Cond.same tb.cols[i].name 2) := by
              simp [AllHold]
            rw [hcols, e, holds_tenant hn tv [v] x]
            simp only [CondHolds, hcol, Filter, ColIs, List.getElem?_tail]
            constructor
            · rintro ⟨hh, j, w, hj, hw, hr⟩
              cases hj; simp [arg] at hw; subst hw; exact ⟨hh, hr⟩
            · rintro ⟨hh, hr⟩
              exact ⟨hh, i + 1, v, rfl, by simp [arg], hr⟩
          · rfl
        · simp at hc

/-- A `SELECT` of every table lists the tenant's database. -/
theorem lists_of_selects {ts : List Tab} {tv : Int64} {db : PgDb} (hv : valid ts = true)
    (hm : Matches ts db) (R : Tables) (hlen : ∀ t, ts.length ≤ t → R t = [])
    (hsel : ∀ t, t < ts.length → ∃ q ps R0, select ts tv t none = some (q, ps) ∧
      selected db q ps = some R0 ∧ (R t).Perm R0) :
    Lists (klOf ts) (view ts tv db) R := by
  intro t
  by_cases ht : t < ts.length
  · obtain ⟨q, ps, R0, hq, hs, hp⟩ := hsel t ht
    obtain ⟨R1, hs1, hR⟩ := select_sound hv hm hq
    rw [hs] at hs1; cases hs1
    obtain ⟨hn, hmem⟩ := hR (R t) hp
    exact ⟨hn, fun row => by rw [hmem row]; simp [Filter]⟩
  · rw [hlen t (by omega)]
    refine ⟨List.nodup_nil, fun row => ?_⟩
    simp [view, readBack, tenantTabs, List.getElem?_eq_none (show ts.length ≤ t by omega)]

/-! ## Creating the tables -/

theorem keyNames_ok (tb : Tab) (hn : (names tb).Nodup) (hkl : tb.kl ≤ tb.cols.length) :
    (keyNames tb).Nodup ∧ ∀ n ∈ keyNames tb, ∃ c ∈ colDefs tb, c.name = n ∧ c.notNull = true := by
  rw [keyNames_take]
  refine ⟨hn.sublist (List.take_sublist _ _), fun n hn' => ?_⟩
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hn'
  simp only [List.length_take, names_length] at hj
  have hj' : j < (colDefs tb).length := by rw [colDefs_length]; omega
  refine ⟨(colDefs tb)[j], List.getElem_mem hj', ?_, ?_⟩
  · simp only [List.getElem_take, ← colDefs_names, List.getElem_map]
  · cases j with
    | zero => rfl
    | succ i => simp [colDefs]; omega

/-- Creating tables in a database without them: each is then empty and as `create` says; nothing
else changes. -/
theorem create_all (l : List Tab) (hok : ∀ tb ∈ l, TabOk tb) (hn : (l.map (·.name)).Nodup) :
    ∀ db : PgDb, (∀ tb ∈ l, db tb.name = none) →
      ∃ db', runAll db (l.map (fun tb => (create tb, []))) = some db' ∧
        (∀ tb ∈ l, db' tb.name = some ⟨colDefs tb, keyNames tb, []⟩) ∧
        ∀ n, n ∉ l.map (·.name) → db' n = db n := by
  induction l with
  | nil => intro db _; exact ⟨db, rfl, by simp, fun _ _ => rfl⟩
  | cons tb l ih =>
    intro db hnone
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hn
    have tok := hok tb List.mem_cons_self
    have hc : run db (create tb) [] = some (put db tb.name ⟨colDefs tb, keyNames tb, []⟩) := by
      simp only [create, run, hnone tb List.mem_cons_self]
      rw [ite_eq_left ⟨by rw [colDefs_names]; exact names_nodup tok, keyNames_ok tb (names_nodup tok) (kl_le tok)⟩]
    obtain ⟨db', hr, hin, hout⟩ := ih (fun tb' h => hok tb' (List.mem_cons_of_mem _ h)) hn.2
      (put db tb.name ⟨colDefs tb, keyNames tb, []⟩) (fun tb' h => by
        simp only [put]
        rw [ite_eq_right (fun he => hn.1 ⟨tb', h, he⟩)]
        exact hnone tb' (List.mem_cons_of_mem _ h))
    refine ⟨db', by simp [runAll, hc, hr], fun tb' h => ?_, fun n hn' => ?_⟩
    · rcases List.mem_cons.1 h with rfl | h
      · rw [hout _ (fun hm => hn.1 (by simpa using hm))]
        simp [put]
      · exact hin tb' h
    · simp only [List.map_cons, List.mem_cons, not_or] at hn'
      rw [hout n hn'.2]
      simp [put, hn'.1]

/-- After creating a valid schema's tables in a database without them, the tables match the
schema, every tenant's database is empty, and no other table changed. -/
theorem create_sound {ts : List Tab} (hv : valid ts = true) (db : PgDb)
    (hnone : ∀ tb ∈ ts, db tb.name = none) :
    ∃ db', runAll db (ts.map (fun tb => (create tb, []))) = some db' ∧ Matches ts db' ∧
      (∀ tv, view ts tv db' = fun _ _ => none) ∧ ∀ n, n ∉ ts.map (·.name) → db' n = db n := by
  have hV := (valid_iff ts).1 hv
  obtain ⟨db', hr, hin, hout⟩ := create_all ts hV.1 hV.2 db hnone
  refine ⟨db', hr, fun tb h => ⟨_, hin tb h, rfl, rfl, by simp, by simp⟩, fun tv => ?_, hout⟩
  funext t k
  cases ht : ts[t]? with
  | none => simp [view, readBack, tenantTabs, ht]
  | some tb => simp [view, readBack, tenantTabs, ht, hin tb (List.mem_of_getElem? ht)]

/-- `CREATE TABLE IF NOT EXISTS` leaves tables that exist as they are. -/
theorem create_kept (l : List Tab) :
    ∀ db : PgDb, (∀ tb ∈ l, db tb.name ≠ none) → runAll db (l.map (fun tb => (create tb, []))) = some db := by
  induction l with
  | nil => intro db _; rfl
  | cons tb l ih =>
    intro db h
    obtain ⟨tab, htab⟩ := Option.ne_none_iff_exists'.1 (h tb List.mem_cons_self)
    simp only [List.map_cons, runAll, create, run, htab, Option.bind_some]
    exact ih db (fun tb' h' => h tb' (List.mem_cons_of_mem _ h'))

end Leanharbor.Sql
