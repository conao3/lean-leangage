import Calculator.Proofs
import Calculator.Store
import Leanharbor.Store

/-!
# The calculator's table holds what `apply` computes

`Memory` is a `Row`, and `storage` stores the calculator kernel in the table `tables` declares.
`enc s` has, for each user with a stored number (`lookup`), the row of the user and the number.

- `writes_compile`: every write set compiles, for every tenant;
- `enc_apply`, `load_enc`: the obligations of `storage`;
- `stored_lookup`, `stored_transition`: on PostgreSQL, the snapshot loaded from a tenant's rows
  has the numbers of the snapshot the engine holds and answers every command as it does;
- `stored_commit`: every commit goes through.

The theorems that end in `_run` and `load_toRow`, `load_isSome` and `lookup_storeAll` are stated
so that leanassay can run them.
-/

namespace Calculator.Store

open Calculator.Kernel Leanharbor Leanharbor.Sql

/-- The number stored for a user, if any. -/
def lookup : Memories → UInt64 → Option UInt64
  | .empty, _ => none
  | .leaf key value, u => if u = key then some value else none
  | .node even odd, u => if u % 2 = 0 then lookup even (u / 2) else lookup odd (u / 2)

theorem lookup_pair (k₁ v₁ k v u : UInt64) :
    lookup (pair k₁ v₁ k v) u = if u = k then some v else if u = k₁ then some v₁ else none := by
  fun_induction pair k₁ v₁ k v generalizing u <;>
    simp only [lookup, *] <;>
    simp only [eq_iff_halves u _] <;>
    by_cases hu : u % 2 = 0 <;> simp_all [mod_two_ne_zero]

theorem lookup_store (k v : UInt64) (ms : Memories) (u : UInt64) :
    lookup (store k v ms) u = if u = k then some v else lookup ms u := by
  induction ms generalizing k u with
  | empty => simp [store, lookup]
  | leaf k₁ v₁ => simp [store, lookup, lookup_pair]
  | node even odd ihe iho =>
    unfold store
    simp only [eq_iff_halves u k]
    by_cases hu : u % 2 = 0 <;> by_cases hk : k % 2 = 0 <;>
      simp_all [lookup, mod_two_ne_zero]

/-- A user without a stored number has `0`. -/
theorem memoryOf_lookup (ms : Memories) (u : UInt64) : memoryOf ms u = (lookup ms u).getD 0 := by
  induction ms generalizing u with
  | empty => rfl
  | leaf k v => by_cases h : u = k <;> simp [memoryOf, lookup, h]
  | node e o ihe iho => by_cases h : u % 2 = 0 <;> simp [memoryOf, lookup, h, ihe, iho]

/-! ## Rows -/

theorem fromRow_toRow (m : Memory) : fromRow (toRow m) = some m := by
  simp [fromRow, toRow]

theorem toRow_fromRow (r : List Val) (m : Memory) (h : fromRow r = some m) : toRow m = r := by
  unfold fromRow at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [toRow]
  · simp at h

instance rowMemory : Row Memory := ⟨toRow, fromRow, fromRow_toRow, toRow_fromRow⟩

@[simp] theorem rowMemory_toRow : (Row.toRow : Memory → List Val) = toRow := rfl

@[simp] theorem rowMemory_fromRow : (Row.fromRow : List Val → Option Memory) = fromRow := rfl

/-- `toRow_fromRow` without a hypothesis on the result, so it can be run on any input. -/
theorem toRow_fromRow_run (r : List Val) :
    match fromRow r with
    | some m => toRow m = r
    | none => True := by
  cases h : fromRow r with
  | none => trivial
  | some m => exact toRow_fromRow r m h

/-! ## The table -/

theorem valid_tables : valid tables = true := by decide

/-- The statement that creates the table. -/
theorem tables_create :
    tables.map (fun tb => render (create tb)) =
      ["CREATE TABLE IF NOT EXISTS \"memories\" (\"tenant_id\" BIGINT NOT NULL, " ++
        "\"user\" BIGINT NOT NULL, \"value\" BIGINT NOT NULL, PRIMARY KEY (\"tenant_id\", \"user\"))"] := by
  decide +kernel

/-- Every write set compiles, for every tenant. -/
theorem writes_compile (tv : Int64) (ws : Option Memory) :
    (((writes ws).map plan).mapM (compile tables tv)).isSome = true := by
  cases ws with
  | none => rfl
  | some m =>
    simp only [writes, List.map_cons, List.map_nil, plan, List.mapM_cons, List.mapM_nil, compile,
      valid_tables, ite_true]
    simp [tables, toRow, fitsFrom, fitsAt, typed, valKind]

/-! ## The rows of a snapshot -/

/-- The tenant's database a snapshot stands for: for each stored number, the row of `memories`
with the user and the number. -/
def enc (s : Snapshot) : Db := fun t k =>
  match t, k with
  | 0, [.int u] => (lookup s.memories u.toUInt64).map (fun v => [.int u, .int v.toInt64])
  | _, _ => none

theorem toUInt64_eq_iff (u : Int64) (x : UInt64) : u.toUInt64 = x ↔ u = x.toInt64 := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

/-- The rows a write set stores turn the snapshot's rows into those of the snapshot `apply`
computes. -/
theorem enc_apply (s : Snapshot) (ws : Option Memory) :
    execAll (enc s) ((writes ws).map plan) = enc (apply s ws) := by
  cases ws with
  | none => rfl
  | some m =>
    have e : execAll (enc s) ((writes (some m)).map plan) =
        exec (enc s) (.upsert 0 [.int m.user.toInt64] [.int m.value.toInt64]) := rfl
    rw [e]
    funext t k
    simp only [exec, apply, List.cons_append, List.nil_append]
    rcases t with _ | t
    · rcases k with _ | ⟨v, _ | ⟨w, k⟩⟩
      · simp [enc]
      · cases v with
        | int u =>
          simp only [enc, Calculator.Kernel.upsert, lookup_store, true_and, List.cons.injEq,
            Val.int.injEq, and_true, toUInt64_eq_iff]
          by_cases hu : u = m.user.toInt64 <;> simp [hu]
        | _ => simp [enc]
      · simp [enc]
    · simp [enc]

/-- `enc_apply` at one user, so it can be run. -/
theorem enc_apply_run (s : Snapshot) (ws : Option Memory) (t : Nat) (u : UInt64) :
    execAll (enc s) ((writes ws).map plan) t [.int u.toInt64] = enc (apply s ws) t [.int u.toInt64] := by
  rw [enc_apply]

/-! ## Loading -/

theorem lookup_storeAll (acc : Memories) (ms : List Memory) (u : UInt64) :
    lookup (storeAll acc ms) u =
      match ms.reverse.find? (·.user = u) with
      | some m => some m.value
      | none => lookup acc u := by
  induction ms generalizing acc with
  | nil => rfl
  | cons m ms ih =>
    simp only [storeAll, ih, List.reverse_cons, List.find?_append, Calculator.Kernel.upsert, lookup_store]
    cases hf : ms.reverse.find? (·.user = u) with
    | some m' => rfl
    | none =>
      by_cases hu : u = m.user
      · simp [hu]
      · have : ¬ m.user = u := fun h => hu h.symm
        simp [hu, this]

theorem load_toRow (ms : List Memory) (u : UInt64) :
    (load [ms.map toRow]).map (fun s => lookup s.memories u) =
      some ((ms.reverse.find? (·.user = u)).map (·.value)) := by
  have h : (ms.map toRow).mapM fromRow = some ms := by
    induction ms with
    | nil => rfl
    | cons m ms ih => simp [List.mapM_cons, fromRow_toRow, ih]
  simp only [load, h, Option.map_some, lookup_storeAll]
  cases ms.reverse.find? (·.user = u) <;> rfl

/-- `load` takes one table, whose rows all decode. -/
theorem load_isSome (rows : List (List (List Val))) :
    (load rows).isSome =
      match rows with
      | [rs] => rs.all (fun r => (fromRow r).isSome)
      | _ => false := by
  rcases rows with _ | ⟨rs, _ | ⟨r₂, rows⟩⟩
  · rfl
  · simp only [load]
    cases h : rs.mapM fromRow with
    | none =>
      simp only [Option.isSome_none]
      symm
      induction rs with
      | nil => simp at h
      | cons r rs ih =>
        cases hr : fromRow r with
        | none => simp [hr]
        | some m =>
          cases hrs : rs.mapM fromRow with
          | none => simp [hr, ih hrs]
          | some _ => simp [List.mapM_cons, hr, hrs] at h
    | some ms =>
      simp only [Option.isSome_some]
      symm
      rw [List.all_eq_true]
      intro r hr
      have e := Row.toRow_mapM (α := Memory) h
      simp only [rowMemory_toRow] at e
      obtain ⟨m, -, rfl⟩ := List.mem_map.1 (e ▸ hr)
      simp [fromRow_toRow]
  · rfl

/-! ## The calculator on PostgreSQL -/

theorem toInt64_inj (v w : UInt64) : v.toInt64 = w.toInt64 ↔ v = w :=
  ⟨fun h => by simpa using congrArg Int64.toUInt64 h, fun h => h ▸ rfl⟩

theorem enc_user (s : Snapshot) (u : UInt64) :
    enc s 0 [.int u.toInt64] = (lookup s.memories u).map (fun v => [.int u.toInt64, .int v.toInt64]) := by
  simp [enc]

/-- A row of the snapshot's database is the row of a stored number. -/
theorem enc_some {s : Snapshot} {row : List Val} (h : enc s 0 (row.take 1) = some row) :
    ∃ m, toRow m = row ∧ lookup s.memories m.user = some m.value := by
  rcases row with _ | ⟨x, rest⟩
  · simp [enc] at h
  · cases x with
    | int u =>
      simp only [List.take_succ_cons, List.take_zero, enc, Option.map_eq_some_iff] at h
      obtain ⟨v, hv, he⟩ := h
      exact ⟨⟨u.toUInt64, v⟩, by simp [toRow, ← he], hv⟩
    | _ => simp [enc] at h

theorem enc_eq {s s' : Snapshot} (h : ∀ u, lookup s.memories u = lookup s'.memories u) :
    enc s = enc s' := by
  funext t k
  unfold enc
  split <;> simp [h]

theorem lookup_of_enc {s s' : Snapshot} (h : enc s = enc s') (u : UInt64) :
    lookup s.memories u = lookup s'.memories u := by
  have e := congrFun (congrFun h 0) [.int u.toInt64]
  simp only [enc_user] at e
  cases h1 : lookup s.memories u <;> cases h2 : lookup s'.memories u <;> simp_all [toInt64_inj]

/-- Rows that list the snapshot's database load to a snapshot with the same numbers. -/
theorem load_enc (s : Snapshot) (rows : List (List (List Val))) (hlen : rows.length = tables.length)
    (hl : Lists (klOf tables) (enc s) (fun t => rows.getD t [])) :
    ∃ s', load rows = some s' ∧ enc s' = enc s := by
  obtain ⟨R0, rfl⟩ : ∃ R0, rows = [R0] := by
    match rows, hlen with
    | [R0], _ => exact ⟨R0, rfl⟩
  have hmem : ∀ row, row ∈ R0 ↔ enc s 0 (row.take 1) = some row := (hl 0).2
  have hrow : ∀ r ∈ R0, ∃ m, toRow m = r ∧ lookup s.memories m.user = some m.value :=
    fun r hr => enc_some ((hmem r).1 hr)
  obtain ⟨ms, hms, hmap⟩ := Row.mapM_fromRow (α := Memory) (rs := R0)
    (fun r hr => (hrow r hr).imp fun _ h => h.1)
  simp only [rowMemory_toRow, rowMemory_fromRow] at hms hmap
  refine ⟨⟨storeAll .empty ms⟩, by simp [load, hms], enc_eq (fun u => ?_)⟩
  rw [lookup_storeAll]
  cases hf : ms.reverse.find? (·.user = u) with
  | some m =>
    have hm : m ∈ ms := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hu : m.user = u := by simpa using List.find?_some hf
    obtain ⟨m', hm', hl'⟩ := hrow (toRow m) (hmap ▸ List.mem_map_of_mem hm)
    have e : m' = m := by simpa [fromRow_toRow] using congrArg fromRow hm'
    subst e
    simp only
    rw [← hu, hl']
  | none =>
    simp only [lookup]
    symm
    cases hv : lookup s.memories u with
    | none => rfl
    | some v =>
      exfalso
      have hin : toRow ⟨u, v⟩ ∈ R0 := (hmem _).2 (by simp [toRow, enc, hv])
      rw [← hmap] at hin
      obtain ⟨m, hm, he⟩ := List.mem_map.1 hin
      have e : m = ⟨u, v⟩ := by simpa [fromRow_toRow] using congrArg fromRow he
      subst e
      have := List.find?_eq_none.1 hf _ (List.mem_reverse.2 hm)
      simp at this

/-- The calculator kernel, stored in `tables`. -/
def storage : Storage kernel where
  tables := tables
  writes := writes
  load := load
  enc := enc
  valid_tables := valid_tables
  enc_init := by
    funext t k
    show enc init t k = none
    unfold enc
    split <;> rfl
  enc_apply := fun _ s _ ws _ _ => enc_apply s ws
  load_enc := load_enc

/-- On PostgreSQL, loading a tenant's rows gives back the numbers of the snapshot that `apply`
computed: the same users have a stored number, with the same value. -/
theorem stored_lookup {tv : Int64} {db : PgDb} {s : Snapshot} {rows : List (List (List Val))}
    (h : storage.Stored tv db s) (hl : storage.Loaded tv db rows) :
    ∃ s', load rows = some s' ∧ ∀ u, lookup s'.memories u = lookup s.memories u := by
  obtain ⟨s', hs', he⟩ := storage.stored_load h hl
  exact ⟨s', hs', lookup_of_enc he⟩

/-- On PostgreSQL, the snapshot loaded from a tenant's rows answers every command of every
principal as the snapshot the engine holds does. -/
theorem stored_transition {tv : Int64} {db : PgDb} {s : Snapshot} {rows : List (List (List Val))}
    (h : storage.Stored tv db s) (hl : storage.Loaded tv db rows) :
    ∃ s', load rows = some s' ∧ ∀ a c, transition a s' c = transition a s c := by
  obtain ⟨s', hs', he⟩ := stored_lookup h hl
  have hm : ∀ u, memoryOf s'.memories u = memoryOf s.memories u := fun u => by
    rw [memoryOf_lookup, memoryOf_lookup, he u]
  exact ⟨s', hs', fun a c => by cases c <;> simp [transition, hm a.user]⟩

/-- On PostgreSQL, every commit of the calculator goes through: the `SELECT` returns rows, they
load, and every write set compiles and runs. -/
theorem stored_commit {tv : Int64} {db : PgDb} {s : Snapshot} (h : storage.Stored tv db s) :
    ∃ rows s', storage.Loaded tv db rows ∧ load rows = some s' ∧
      ∀ ws, ∃ qs db', ((writes ws).map plan).mapM (compile tables tv) = some qs ∧
        runAll db qs = some db' := by
  obtain ⟨⟨rows, s', hl, hs'⟩, hrun⟩ := storage.stored_commit h
  refine ⟨rows, s', hl, hs', fun ws => ?_⟩
  obtain ⟨qs, hq⟩ := Option.isSome_iff_exists.1 (writes_compile tv ws)
  obtain ⟨db', hr⟩ := hrun tv _ qs hq
  exact ⟨qs, db', hq, hr⟩

end Calculator.Store
