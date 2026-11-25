import Leanharbor.Kernel
import Leanharbor.Sql.Sound

/-!
# A kernel's snapshot, stored in PostgreSQL

Based on `crates/h5i-app-core/proofs/H5iAppLib/Store.lean` and `Obligation.lean` and on
`pg_served` and `pg_loaded_inv`, which `crates/h5i-app-schema/src/lean.rs` writes into each
app's `generated/Schema.lean`, of h5i (https://github.com/h5i-dev/h5i, commit 515c7b9,
Apache-2.0). Changed: what a snapshot stores is a tenant's database (`Db`) instead of tables of
rows, so that row order does not enter the obligations; the statements are about a
`Leanharbor.Kernel`, the generated `compile` and `select`, and the storage's `load`; a tenant is
an `Int64`.

A kernel declares its tables as a `List Tab`, and each row type as an instance of `Row`. A
`Storage` adds to the kernel the rows each write set stores (`writes`) and the snapshot the rows
of the tables give back (`load`), with the database a snapshot stands for (`enc`) and four
obligations. `Storage.Stored` is what an engine does to one tenant on a shared database: it loads
the snapshot from the rows a `SELECT` of each table returned, or takes the snapshot it remembers,
runs an accepted command, and stores its writes, with other tenants' statements in between.
Proved once, for every storage:

- `Storage.stored_view`: the tenant's rows are those of the snapshot that `apply` computed;
- `Storage.stored_load`: loading them gives back a snapshot that stands for the same rows;
- `Storage.stored_inv`: a property kept by every accepted command and shared by snapshots that
  stand for the same rows holds on every snapshot loaded;
- `Storage.stored_commit`: the `SELECT`s return rows, the rows load, and compiled statements run;
- `Storage.create_stored`: the tables `create` makes start every tenant from `init`.

All of it is relative to the model of PostgreSQL in `Leanharbor.Sql.Model`.
-/

namespace Leanharbor

open Sql

/-- A row type: the values of a row, and the row of values. Rows that `fromRow` accepts and
values are in one-to-one correspondence. -/
class Row (α : Type) where
  toRow : α → List Val
  fromRow : List Val → Option α
  fromRow_toRow : ∀ x, fromRow (toRow x) = some x
  toRow_fromRow : ∀ r x, fromRow r = some x → toRow x = r

namespace Row

variable {α : Type} [Row α]

/-- Rows that encode values decode, one by one, to values that encode them. -/
theorem mapM_fromRow {rs : List (List Val)} (h : ∀ r ∈ rs, ∃ x : α, toRow x = r) :
    ∃ xs : List α, rs.mapM fromRow = some xs ∧ xs.map toRow = rs := by
  induction rs with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons r rs ih =>
    obtain ⟨x, rfl⟩ := h r List.mem_cons_self
    obtain ⟨xs, hxs, hmap⟩ := ih (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))
    exact ⟨x :: xs, by simp [List.mapM_cons, fromRow_toRow, hxs], by simp [hmap]⟩

/-- Rows that decode are the rows of what they decode to. -/
theorem toRow_mapM {rs : List (List Val)} {xs : List α} (h : rs.mapM fromRow = some xs) :
    xs.map toRow = rs := by
  induction rs generalizing xs with
  | nil => simp at h; subst h; rfl
  | cons r rs ih =>
    cases hr : (fromRow r : Option α) with
    | none => simp [List.mapM_cons, hr] at h
    | some x =>
      cases hrs : rs.mapM (fromRow : List Val → Option α) with
      | none => simp [List.mapM_cons, hr, hrs] at h
      | some xs' =>
        simp [List.mapM_cons, hr, hrs] at h
        subst h
        simp [toRow_fromRow r x hr, ih hrs]

end Row

/-- How a kernel's snapshots are stored. `tables` are the tables, `writes ws` the rows a write
set stores, `load rows` the snapshot that the rows of each table, in the order of `tables`, give
back, and `enc s` the tenant's database the snapshot `s` stands for. -/
structure Storage (k : Kernel) where
  tables : List Tab
  writes : k.WriteSet → List Write
  load : List (List (List Val)) → Option k.Snapshot
  enc : k.Snapshot → Db
  valid_tables : valid tables = true
  /-- The first snapshot stands for an empty database. -/
  enc_init : enc k.init = fun _ _ => none
  /-- The rows an accepted write set stores turn the snapshot's database into that of the
  snapshot `apply` computes. -/
  enc_apply : ∀ a s c ws r, k.transition a s c = .ok (ws, r) →
    execAll (enc s) ((writes ws).map plan) = enc (k.apply s ws)
  /-- Rows that list the snapshot's database, table by table and in any order, load to a
  snapshot that stands for the same database. -/
  load_enc : ∀ s (rows : List (List (List Val))), rows.length = tables.length →
    Lists (klOf tables) (enc s) (fun t => rows.getD t []) → ∃ s', load rows = some s' ∧ enc s' = enc s

namespace Storage

variable {k : Kernel} (st : Storage k)

/-- `rows` holds, for each table in order, what a compiled `SELECT` of the tenant's rows
returned, in any order. -/
def Loaded (tv : Int64) (db : PgDb) (rows : List (List (List Val))) : Prop :=
  rows.length = st.tables.length ∧ ∀ t (h : t < rows.length), ∃ q ps R0,
    select st.tables tv t none = some (q, ps) ∧ selected db q ps = some R0 ∧ rows[t].Perm R0

/-- The databases an engine produces for the tenant `tv` from tables `create` made, with a
snapshot an engine may hold for each. A commit loads the snapshot from the rows a `SELECT` of
each table returned, runs an accepted command of any principal on it, and stores the statements
compiled from its write set; the snapshot it holds is what `apply` computes. An engine may
remember the snapshot it loaded from the rows, and commit on the snapshot it holds instead of
loading one. Statements compiled for other tenants may run in between. -/
inductive Stored (st : Storage k) (tv : Int64) : PgDb → k.Snapshot → Prop
  | fresh {db : PgDb} :
      Matches st.tables db → view st.tables tv db = (fun _ _ => none) → Stored st tv db k.init
  | commit {db db' : PgDb} {s snap : k.Snapshot} {rows : List (List (List Val))} {a : k.Principal}
      {c : k.Command} {ws : k.WriteSet} {r : k.Reply} {qs : List (Sql × List Val)} :
      Stored st tv db s → st.Loaded tv db rows → st.load rows = some snap →
      k.transition a snap c = .ok (ws, r) →
      ((st.writes ws).map plan).mapM (compile st.tables tv) = some qs → runAll db qs = some db' →
      Stored st tv db' (k.apply snap ws)
  | loaded {db : PgDb} {s snap : k.Snapshot} {rows : List (List (List Val))} :
      Stored st tv db s → st.Loaded tv db rows → st.load rows = some snap → Stored st tv db snap
  | cached {db db' : PgDb} {s : k.Snapshot} {a : k.Principal} {c : k.Command} {ws : k.WriteSet}
      {r : k.Reply} {qs : List (Sql × List Val)} :
      Stored st tv db s → k.transition a s c = .ok (ws, r) →
      ((st.writes ws).map plan).mapM (compile st.tables tv) = some qs → runAll db qs = some db' →
      Stored st tv db' (k.apply s ws)
  | other {db db' : PgDb} {s : k.Snapshot} {tv' : Int64} {ss : List Stmt}
      {qs : List (Sql × List Val)} :
      Stored st tv db s → tv' ≠ tv → ss.mapM (compile st.tables tv') = some qs →
      runAll db qs = some db' → Stored st tv db' s

theorem getD_of_lt {α : Type} (l : List α) (d : α) {t : Nat} (h : t < l.length) : l.getD t d = l[t] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem lists_of_loaded {tv : Int64} {db : PgDb} {rows : List (List (List Val))}
    (hm : Matches st.tables db) (hl : st.Loaded tv db rows) :
    Lists (klOf st.tables) (view st.tables tv db) (fun t => rows.getD t []) := by
  refine lists_of_selects st.valid_tables hm _ (fun t ht => ?_) (fun t ht => ?_)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show rows.length ≤ t by rw [hl.1]; exact ht)]
  · have ht' : t < rows.length := by rw [hl.1]; exact ht
    obtain ⟨q, ps, R0, hq, hs, hp⟩ := hl.2 t ht'
    exact ⟨q, ps, R0, hq, hs, by rw [getD_of_lt _ _ ht']; exact hp⟩

/-- The tenant's rows are those of the snapshot that `apply` computed, and the tables stay as
`create` made them. -/
theorem stored_view {tv : Int64} {db : PgDb} {s : k.Snapshot} (h : st.Stored tv db s) :
    Matches st.tables db ∧ view st.tables tv db = st.enc s := by
  induction h with
  | fresh hm he => exact ⟨hm, he.trans st.enc_init.symm⟩
  | commit _ hl hload ht hq hr ih =>
    obtain ⟨hm, he⟩ := ih
    obtain ⟨snap', hsnap, hes⟩ := st.load_enc _ _ hl.1 (he ▸ st.lists_of_loaded hm hl)
    rw [hload] at hsnap
    cases hsnap
    obtain ⟨db2, hr2, hm2, hv2, -, -⟩ := compileAll_sound st.valid_tables _ _ _ hm hq
    rw [hr] at hr2
    cases hr2
    refine ⟨hm2, ?_⟩
    rw [hv2, he, ← hes, st.enc_apply _ _ _ _ _ ht]
  | loaded _ hl hload ih =>
    obtain ⟨hm, he⟩ := ih
    obtain ⟨snap', hsnap, hes⟩ := st.load_enc _ _ hl.1 (he ▸ st.lists_of_loaded hm hl)
    rw [hload] at hsnap
    cases hsnap
    exact ⟨hm, he.trans hes.symm⟩
  | cached _ ht hq hr ih =>
    obtain ⟨hm, he⟩ := ih
    obtain ⟨db2, hr2, hm2, hv2, -, -⟩ := compileAll_sound st.valid_tables _ _ _ hm hq
    rw [hr] at hr2
    cases hr2
    refine ⟨hm2, ?_⟩
    rw [hv2, he, st.enc_apply _ _ _ _ _ ht]
  | other _ hne hq hr ih =>
    obtain ⟨hm, he⟩ := ih
    obtain ⟨db2, hr2, hm2, -, ho, -⟩ := compileAll_sound st.valid_tables _ _ _ hm hq
    rw [hr] at hr2
    cases hr2
    exact ⟨hm2, (ho _ (Ne.symm hne)).trans he⟩

/-- Loading the tenant's rows gives back a snapshot that stands for the same database as the
snapshot `apply` computed. -/
theorem stored_load {tv : Int64} {db : PgDb} {s : k.Snapshot} {rows : List (List (List Val))}
    (h : st.Stored tv db s) (hl : st.Loaded tv db rows) :
    ∃ s', st.load rows = some s' ∧ st.enc s' = st.enc s := by
  obtain ⟨hm, he⟩ := st.stored_view h
  exact st.load_enc s rows hl.1 (he ▸ st.lists_of_loaded hm hl)

/-- A property of `init`, kept by every accepted command, that holds for a snapshot when it holds
for one standing for the same database, holds for every snapshot an engine stores and every
snapshot it loads. -/
theorem stored_inv (I : k.Snapshot → Prop) (hinit : I k.init)
    (henc : ∀ s s', st.enc s' = st.enc s → I s → I s')
    (hstep : ∀ a s c ws r, I s → k.transition a s c = .ok (ws, r) → I (k.apply s ws))
    {tv : Int64} {db : PgDb} {s : k.Snapshot} (h : st.Stored tv db s) :
    I s ∧ ∀ rows, st.Loaded tv db rows → ∃ s', st.load rows = some s' ∧ I s' := by
  have hI : I s := by
    induction h with
    | fresh => exact hinit
    | commit h₀ hl hload ht _ _ ih =>
      obtain ⟨s', hs', he⟩ := st.stored_load h₀ hl
      rw [hload] at hs'
      cases hs'
      exact hstep _ _ _ _ _ (henc _ _ he ih) ht
    | loaded h₀ hl hload ih =>
      obtain ⟨s', hs', he⟩ := st.stored_load h₀ hl
      rw [hload] at hs'
      cases hs'
      exact henc _ _ he ih
    | cached _ ht _ _ ih => exact hstep _ _ _ _ _ ih ht
    | other _ _ _ _ ih => exact ih
  refine ⟨hI, fun rows hl => ?_⟩
  obtain ⟨s', hs', he⟩ := st.stored_load h hl
  exact ⟨s', hs', henc _ _ he hI⟩

/-- Every step of a commit has an outcome: the `SELECT`s of the tables return rows, the rows
load, and statements compiled for any tenant run. -/
theorem stored_commit {tv : Int64} {db : PgDb} {s : k.Snapshot} (h : st.Stored tv db s) :
    (∃ rows s', st.Loaded tv db rows ∧ st.load rows = some s') ∧
      ∀ tv' (ss : List Stmt) qs, ss.mapM (compile st.tables tv') = some qs → ∃ db', runAll db qs = some db' := by
  obtain ⟨hm, -⟩ := st.stored_view h
  refine ⟨?_, fun tv' ss qs hq => ?_⟩
  · have hsel : ∀ t, t < st.tables.length → ∃ q ps R0, select st.tables tv t none = some (q, ps) ∧
        selected db q ps = some R0 := by
      intro t ht
      obtain ⟨tb, htb⟩ : ∃ tb, st.tables[t]? = some tb := ⟨_, List.getElem?_eq_getElem ht⟩
      have hq : select st.tables tv t none = some (.select tb.name (tb.cols.map (·.name))
          [.eq "tenant_id" 1] ((tb.cols.take tb.kl).map (·.name)), [.int tv]) := by
        simp [select, st.valid_tables, htb]
      obtain ⟨R0, hs, -⟩ := select_sound st.valid_tables hm hq
      exact ⟨_, _, R0, hq, hs⟩
    let rows := (List.range st.tables.length).map (fun t =>
      match select st.tables tv t none with
      | some (q, ps) => (selected db q ps).getD []
      | none => [])
    have hl : st.Loaded tv db rows := by
      refine ⟨by simp [rows], fun t ht => ?_⟩
      have ht' : t < st.tables.length := by simpa [rows] using ht
      obtain ⟨q, ps, R0, hq, hs⟩ := hsel t ht'
      refine ⟨q, ps, R0, hq, hs, ?_⟩
      simp [rows, hq, hs]
    obtain ⟨s', hs', -⟩ := st.stored_load h hl
    exact ⟨rows, s', hl, hs'⟩
  · obtain ⟨db', hr, -⟩ := compileAll_sound st.valid_tables ss qs db hm hq
    exact ⟨db', hr⟩

/-- Creating the tables in a database without them starts every tenant from `init`. -/
theorem create_stored (db : PgDb) (hnone : ∀ tb ∈ st.tables, db tb.name = none) :
    ∃ db', runAll db (st.tables.map (fun tb => (create tb, []))) = some db' ∧
      ∀ tv, st.Stored tv db' k.init := by
  obtain ⟨db', hr, hm, hv, -⟩ := create_sound st.valid_tables db hnone
  exact ⟨db', hr, fun tv => .fresh hm (hv tv)⟩

end Storage

end Leanharbor
