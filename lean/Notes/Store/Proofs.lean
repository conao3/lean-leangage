import Notes.Proofs
import Notes.Store
import Leanharbor.Store

/-!
# The notes' tables hold what `apply` computes, and the guard holds on what they load

`Member` and `Note` are `Row`s, and `storage` stores the notes kernel in the two tables `tables`
declares. `enc s` has, for each user with a member row and each id with a note, the row of the
member and of the note.

- `writes_compile`: every write set compiles, for every tenant;
- `enc_apply`, `load_enc`: the obligations of `storage`;
- `stored_keyed`, `stored_transition`: on PostgreSQL, every snapshot an engine stores and every
  snapshot it loads has unique keys, and the snapshot loaded from a tenant's rows answers every
  command of every principal as the snapshot the engine holds does;
- `stored_authorized`, `stored_noninterference`: the guard's theorems about the snapshot loaded
  from the rows, stated against the snapshot the engine holds;
- `accepted_no_nul`: no body an accepted command writes holds NUL;
- `stored_commit`: every commit goes through.

The theorems that end in `_run` and `load_rows`, `load_isSome` are stated so that leanassay can
run them.
-/

namespace Notes.Store

open Notes.Kernel Leanharbor Leanharbor.Sql Leanharbor.Authz

/-! ## Rows -/

theorem toUInt64_eq_iff (u : Int64) (x : UInt64) : u.toUInt64 = x ↔ u = x.toInt64 := by
  constructor
  · rintro rfl; simp
  · rintro rfl; simp

theorem memberOfRow_memberRow (m : Member) : memberOfRow (memberRow m) = some m := by
  simp [memberOfRow, memberRow]

theorem memberRow_memberOfRow (r : List Val) (m : Member) (h : memberOfRow r = some m) :
    memberRow m = r := by
  unfold memberOfRow at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [memberRow]
  · simp at h

theorem noteOfRow_noteRow (n : Note) : noteOfRow (noteRow n) = some n := by
  simp [noteOfRow, noteRow]

theorem noteRow_noteOfRow (r : List Val) (n : Note) (h : noteOfRow r = some n) : noteRow n = r := by
  unfold noteOfRow at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp [noteRow]
  · simp at h

instance rowMember : Row Member := ⟨memberRow, memberOfRow, memberOfRow_memberRow, memberRow_memberOfRow⟩

instance rowNote : Row Note := ⟨noteRow, noteOfRow, noteOfRow_noteRow, noteRow_noteOfRow⟩

/-- `memberRow_memberOfRow` without a hypothesis on the result, so it can be run on any input. -/
theorem memberRow_memberOfRow_run (r : List Val) :
    match memberOfRow r with
    | some m => memberRow m = r
    | none => True := by
  cases h : memberOfRow r with
  | none => trivial
  | some m => exact memberRow_memberOfRow r m h

/-- `noteRow_noteOfRow` without a hypothesis on the result, so it can be run on any input. -/
theorem noteRow_noteOfRow_run (r : List Val) :
    match noteOfRow r with
    | some n => noteRow n = r
    | none => True := by
  cases h : noteOfRow r with
  | none => trivial
  | some n => exact noteRow_noteOfRow r n h

/-! ## The tables -/

theorem valid_tables : valid tables = true := by decide

/-- The statements that create the tables. -/
theorem tables_create :
    tables.map (fun tb => render (create tb)) =
      ["CREATE TABLE IF NOT EXISTS \"members\" (\"tenant_id\" BIGINT NOT NULL, " ++
        "\"user\" BIGINT NOT NULL, \"admin\" BOOLEAN NOT NULL, PRIMARY KEY (\"tenant_id\", \"user\"))",
       "CREATE TABLE IF NOT EXISTS \"notes\" (\"tenant_id\" BIGINT NOT NULL, " ++
        "\"id\" BIGINT NOT NULL, \"owner\" BIGINT NOT NULL, \"shared\" BOOLEAN NOT NULL, " ++
        "\"body\" TEXT NOT NULL, PRIMARY KEY (\"tenant_id\", \"id\"))"] := by
  decide +kernel

theorem write_compile (tv : Int64) (w : Notes.Kernel.Write) :
    (compile tables tv (plan (write w))).isSome = true := by
  cases w with
  | putMember m =>
    simp only [write, plan, compile, valid_tables, ite_true]
    simp [tables, memberRow, fitsFrom, fitsAt, typed, valKind]
  | delMember u =>
    simp only [write, plan, compile, valid_tables, ite_true]
    simp [tables, fitsFrom, fitsAt, typed, valKind]
  | putNote n =>
    simp only [write, plan, compile, valid_tables, ite_true]
    simp [tables, noteRow, fitsFrom, fitsAt, typed, valKind]
  | delNote id =>
    simp only [write, plan, compile, valid_tables, ite_true]
    simp [tables, fitsFrom, fitsAt, typed, valKind]

/-- Every write set compiles, for every tenant. -/
theorem writes_compile (tv : Int64) (ws : List Notes.Kernel.Write) :
    (((writes ws).map plan).mapM (compile tables tv)).isSome = true := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (write_compile tv w)
    obtain ⟨qs, hqs⟩ := Option.isSome_iff_exists.1 ih
    simp only [writes, List.map_cons, List.mapM_cons] at hqs ⊢
    rw [hq, hqs]
    rfl

/-! ## The rows of a snapshot -/

/-- A table's rows by key: under `[.int k]`, the row of the element whose key has the bits of
`k`. -/
def encTable {α : Type} (key : α → UInt64) (row : α → List Val) (l : List α) :
    List Val → Option (List Val)
  | [.int k] => (l.find? (key · == k.toUInt64)).map row
  | _ => none

/-- The tenant's database a snapshot stands for: for each user with a member row, the row of
`members` with the user and whether the member is an admin, and for each id with a note, the row
of `notes` with the id, the owner, whether the note is shared and the body. -/
def enc (s : Snapshot) : Db
  | 0 => encTable (·.user) (fun m => [.int m.user.toInt64, .bool m.admin]) s.members
  | 1 => encTable (·.id) (fun n => [.int n.id.toInt64, .int n.owner.toInt64, .bool n.shared, .text n.body])
      s.notes
  | _ => fun _ => none

theorem encTable_eq {α : Type} {key : α → UInt64} {row : α → List Val} {l l' : List α}
    (h : ∀ k, l.find? (key · == k) = l'.find? (key · == k)) :
    encTable key row l = encTable key row l' := by
  funext k
  unfold encTable
  split <;> simp only [h]

theorem enc_eq {s s' : Snapshot} (hm : ∀ u, findMember s.members u = findMember s'.members u)
    (hn : ∀ k, findNote s.notes k = findNote s'.notes k) : enc s = enc s' := by
  funext t
  match t with
  | 0 => exact encTable_eq hm
  | 1 => exact encTable_eq hn
  | _ + 2 => rfl

theorem map_inj {α : Type} {row : α → List Val} {ofRow : List Val → Option α}
    (hof : ∀ x, ofRow (row x) = some x) {a b : Option α} (e : a.map row = b.map row) : a = b := by
  cases a <;> cases b <;> simp at e ⊢
  have := congrArg ofRow e
  rw [hof, hof] at this
  exact Option.some.inj this

theorem find?_of_encTable {α : Type} {key : α → UInt64} {row : α → List Val}
    {ofRow : List Val → Option α} (hof : ∀ x, ofRow (row x) = some x) {l l' : List α}
    (h : encTable key row l = encTable key row l') (k : UInt64) :
    l.find? (key · == k) = l'.find? (key · == k) := by
  have e := congrFun h [.int k.toInt64]
  have hk : k.toInt64.toUInt64 = k := by simp
  simp only [encTable] at e
  rw [hk] at e
  exact map_inj hof e

/-- Two snapshots that stand for the same rows have the same member under each user id and the
same note under each id. -/
theorem find_of_enc {s s' : Snapshot} (h : enc s = enc s') :
    (∀ u, findMember s.members u = findMember s'.members u) ∧
      ∀ k, findNote s.notes k = findNote s'.notes k :=
  ⟨find?_of_encTable (ofRow := memberOfRow) memberOfRow_memberRow (congrFun h 0),
    find?_of_encTable (ofRow := noteOfRow) noteOfRow_noteRow (congrFun h 1)⟩

theorem enc_init : enc init = fun _ _ => none := by
  funext t k
  match t with
  | 0 =>
    show encTable _ _ init.members k = none
    unfold encTable
    split <;> rfl
  | 1 =>
    show encTable _ _ init.notes k = none
    unfold encTable
    split <;> rfl
  | _ + 2 => rfl

/-! ## What the writes do to the rows -/

theorem exec_write (s : Snapshot) (w : Notes.Kernel.Write) :
    exec (enc s) (plan (write w)) = enc (applyWrite s w) := by
  funext t k
  cases w with
  | putMember m =>
    simp only [write, memberRow, plan, List.take, List.drop, exec, List.cons_append, List.nil_append]
    match t with
    | 0 =>
      simp only [true_and]
      match k with
      | [.int u] =>
        simp only [enc, encTable, Notes.Kernel.applyWrite, List.cons.injEq, Val.int.injEq, and_true]
        rw [← findMember, ← findMember, findMember_putMember]
        by_cases hu : u = m.user.toInt64
        · subst hu
          simp
        · have : ¬ m.user = u.toUInt64 := fun e => hu (by rw [e]; simp)
          simp [hu, this]
      | [] => simp [enc, encTable]
      | [.bool _] | [.text _] | [.bytes _] | [.null] => simp [enc, encTable]
      | _ :: _ :: _ => simp [enc, encTable]
    | 1 => simp [enc, Notes.Kernel.applyWrite]
    | _ + 2 => simp [enc]
  | delMember u =>
    simp only [write, plan, exec]
    match t with
    | 0 =>
      simp only [true_and]
      match k with
      | [.int v] =>
        simp only [enc, encTable, Notes.Kernel.applyWrite, List.cons.injEq, Val.int.injEq, and_true]
        rw [← findMember, ← findMember]
        simp only [findMember]
        rw [find?_remove (fun m : Member => m.user)]
        by_cases hv : v = u.toInt64
        · subst hv
          simp
        · have : ¬ u = v.toUInt64 := fun e => hv (by rw [e]; simp)
          simp [hv, this]
      | [] => simp [enc, encTable]
      | [.bool _] | [.text _] | [.bytes _] | [.null] => simp [enc, encTable]
      | _ :: _ :: _ => simp [enc, encTable]
    | 1 => simp [enc, Notes.Kernel.applyWrite]
    | _ + 2 => simp [enc]
  | putNote n =>
    simp only [write, noteRow, plan, List.take, List.drop, exec, List.cons_append, List.nil_append]
    match t with
    | 0 => simp [enc, Notes.Kernel.applyWrite]
    | 1 =>
      simp only [true_and]
      match k with
      | [.int i] =>
        simp only [enc, encTable, Notes.Kernel.applyWrite, List.cons.injEq, Val.int.injEq, and_true]
        rw [← findNote, ← findNote, findNote_putNote]
        by_cases hi : i = n.id.toInt64
        · subst hi
          simp
        · have : ¬ n.id = i.toUInt64 := fun e => hi (by rw [e]; simp)
          simp [hi, this]
      | [] => simp [enc, encTable]
      | [.bool _] | [.text _] | [.bytes _] | [.null] => simp [enc, encTable]
      | _ :: _ :: _ => simp [enc, encTable]
    | _ + 2 => simp [enc]
  | delNote id =>
    simp only [write, plan, exec]
    match t with
    | 0 => simp [enc, Notes.Kernel.applyWrite]
    | 1 =>
      simp only [true_and]
      match k with
      | [.int i] =>
        simp only [enc, encTable, Notes.Kernel.applyWrite, List.cons.injEq, Val.int.injEq, and_true]
        rw [← findNote, ← findNote]
        simp only [findNote]
        rw [find?_remove (fun n : Note => n.id)]
        by_cases hi : i = id.toInt64
        · subst hi
          simp
        · have : ¬ id = i.toUInt64 := fun e => hi (by rw [e]; simp)
          simp [hi, this]
      | [] => simp [enc, encTable]
      | [.bool _] | [.text _] | [.bytes _] | [.null] => simp [enc, encTable]
      | _ :: _ :: _ => simp [enc, encTable]
    | _ + 2 => simp [enc]

/-- The rows a write set stores turn the snapshot's rows into those of the snapshot `apply`
computes. -/
theorem enc_apply (s : Snapshot) (ws : List Notes.Kernel.Write) :
    execAll (enc s) ((writes ws).map plan) = enc (apply s ws) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    simp only [writes, List.map_cons, execAll, List.foldl_cons, apply] at ih ⊢
    rw [exec_write]
    exact ih (applyWrite s w)

/-- `enc_apply` at the key of a user and of a note, so it can be run. -/
theorem enc_apply_run (s : Snapshot) (ws : List Notes.Kernel.Write) (k : UInt64) :
    execAll (enc s) ((writes ws).map plan) 0 [.int k.toInt64] = enc (apply s ws) 0 [.int k.toInt64] ∧
      execAll (enc s) ((writes ws).map plan) 1 [.int k.toInt64] = enc (apply s ws) 1 [.int k.toInt64] := by
  rw [enc_apply]
  exact ⟨rfl, rfl⟩

/-! ## Loading -/

section Table

variable {α : Type} (key : α → UInt64) (row : α → List Val) (ofRow : List Val → Option α)

/-- Rows that list, once each, the rows of a table of `l` decode to a list with no key twice and
the same element under each key as `l`. -/
theorem decode_listed (hof : ∀ x, ofRow (row x) = some x) (hto : ∀ r x, ofRow r = some x → row x = r)
    (hkey : ∀ x, (row x).take 1 = [.int (key x).toInt64]) {l : List α} {R : List (List Val)}
    (hR : R.Nodup) (hmem : ∀ r, r ∈ R ↔ encTable key row l (r.take 1) = some r) :
    ∃ xs, R.mapM ofRow = some xs ∧ (xs.map key).Nodup ∧
      ∀ k, xs.find? (key · == k) = l.find? (key · == k) := by
  letI : Row α := ⟨row, ofRow, hof, hto⟩
  have hfind : ∀ r ∈ R, ∃ x, row x = r ∧ l.find? (key · == key x) = some x := by
    intro r hr
    have he := (hmem r).1 hr
    match r, he with
    | .int k :: rest, he =>
      simp only [List.take_succ_cons, List.take_zero, encTable, Option.map_eq_some_iff] at he
      obtain ⟨x, hx, hxr⟩ := he
      have hk : key x = k.toUInt64 := by simpa using List.find?_some hx
      exact ⟨x, hxr, by rw [hk]; exact hx⟩
  obtain ⟨xs, hxs, hmap⟩ := Row.mapM_fromRow (α := α) (rs := R)
    (fun r hr => (hfind r hr).imp fun _ h => h.1)
  have hinj : ∀ x y, row x = row y → x = y := fun x y e => by
    have := congrArg ofRow e
    rw [hof, hof] at this
    exact Option.some.inj this
  have hfy : ∀ y ∈ xs, l.find? (key · == key y) = some y := by
    intro y hy
    obtain ⟨x, hx, hf⟩ := hfind (row y) (hmap ▸ List.mem_map_of_mem hy)
    rw [← hinj x y hx]
    exact hf
  have hnd : xs.Nodup := nodup_of_map row (hmap ▸ hR)
  refine ⟨xs, hxs, ?_, fun k => ?_⟩
  · rw [List.Nodup, List.pairwise_map]
    refine hnd.imp_of_mem fun hx hy hne he => hne ?_
    have h1 := hfy _ hx
    rw [he, hfy _ hy] at h1
    exact (Option.some.inj h1).symm
  · cases hx : xs.find? (key · == k) with
    | some y =>
      have hk : key y = k := by simpa using List.find?_some hx
      rw [← hk, hfy y (List.mem_of_find?_eq_some hx)]
    | none =>
      cases hl : l.find? (key · == k) with
      | none => rfl
      | some x =>
        exfalso
        have hk : key x = k := by simpa using List.find?_some hl
        have hin : row x ∈ R := by
          refine (hmem _).2 ?_
          rw [hkey x]
          simp [encTable, hk, hl]
        rw [← hmap] at hin
        obtain ⟨y, hy, hyx⟩ := List.mem_map.1 hin
        have := hinj y x hyx
        subst this
        exact List.find?_eq_none.1 hx y hy (by simp [hk])

end Table

/-- Rows that list the snapshot's rows, table by table and in any order, load to a snapshot with
unique keys that stands for the same rows. -/
theorem load_keyed (s : Snapshot) (rows : List (List (List Val))) (hlen : rows.length = tables.length)
    (hl : Lists (klOf tables) (enc s) (fun t => rows.getD t [])) :
    ∃ s', load rows = some s' ∧ enc s' = enc s ∧ Keyed s' := by
  obtain ⟨R0, R1, rfl⟩ : ∃ R0 R1, rows = [R0, R1] := by
    match rows, hlen with
    | [R0, R1], _ => exact ⟨R0, R1, rfl⟩
  obtain ⟨ms, hms, hmk, hmf⟩ := decode_listed (fun m : Member => m.user)
    (fun m => [.int m.user.toInt64, .bool m.admin])
    memberOfRow memberOfRow_memberRow memberRow_memberOfRow (fun _ => rfl) (hl 0).1 (hl 0).2
  obtain ⟨ns, hns, hnk, hnf⟩ := decode_listed (fun n : Note => n.id)
    (fun n => [.int n.id.toInt64, .int n.owner.toInt64, .bool n.shared, .text n.body])
    noteOfRow noteOfRow_noteRow noteRow_noteOfRow (fun _ => rfl) (hl 1).1 (hl 1).2
  have hms' : R0.mapM memberOfRow = some ms := hms
  have hns' : R1.mapM noteOfRow = some ns := hns
  refine ⟨⟨ms, ns⟩, by simp [load, hms', hns'], enc_eq hmf hnf, hmk, hnk⟩

theorem load_enc (s : Snapshot) (rows : List (List (List Val))) (hlen : rows.length = tables.length)
    (hl : Lists (klOf tables) (enc s) (fun t => rows.getD t [])) :
    ∃ s', load rows = some s' ∧ enc s' = enc s :=
  (load_keyed s rows hlen hl).imp fun _ h => ⟨h.1, h.2.1⟩

theorem mapM_rows {α : Type} [Row α] (xs : List α) : (xs.map Row.toRow).mapM Row.fromRow = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, Row.fromRow_toRow, ih]

/-- The rows of members and notes load to those members and notes. -/
theorem load_rows (ms : List Member) (ns : List Note) :
    load [ms.map memberRow, ns.map noteRow] = some ⟨ms, ns⟩ := by
  have hm : (ms.map memberRow).mapM memberOfRow = some ms := mapM_rows (α := Member) ms
  have hn : (ns.map noteRow).mapM noteOfRow = some ns := mapM_rows (α := Note) ns
  simp [load, hm, hn]

/-- `load` takes two tables, whose rows all decode. -/
theorem load_isSome (rows : List (List (List Val))) :
    (load rows).isSome =
      match rows with
      | [rs, ts] => rs.all (fun r => (memberOfRow r).isSome) && ts.all (fun r => (noteOfRow r).isSome)
      | _ => false := by
  have hall : ∀ {α : Type} (f : List Val → Option α) (rs : List (List Val)),
      (rs.mapM f).isSome = rs.all (fun r => (f r).isSome) := by
    intro α f rs
    induction rs with
    | nil => rfl
    | cons r rs ih =>
      cases hr : f r with
      | none => simp [List.mapM_cons, hr]
      | some x =>
        cases hrs : rs.mapM f with
        | none => simp_all [List.mapM_cons]
        | some _ => simp_all [List.mapM_cons]
  match rows with
  | [] => rfl
  | [_] => rfl
  | [rs, ts] =>
    simp only [load, ← hall memberOfRow rs, ← hall noteOfRow ts]
    cases rs.mapM memberOfRow <;> cases ts.mapM noteOfRow <;> rfl
  | _ :: _ :: _ :: _ => rfl

/-! ## The notes on PostgreSQL -/

/-- The notes kernel, stored in `tables`. -/
def storage : Storage kernel where
  tables := tables
  writes := writes
  load := load
  enc := enc
  valid_tables := valid_tables
  enc_init := enc_init
  enc_apply := fun _ s _ ws _ _ => enc_apply s ws
  load_enc := load_enc

/-- On PostgreSQL, the snapshot loaded from a tenant's rows has unique keys and stands for the
rows of the snapshot the engine holds. -/
theorem stored_load {tv : Int64} {db : PgDb} {s : Snapshot} {rows : List (List (List Val))}
    (h : storage.Stored tv db s) (hl : storage.Loaded tv db rows) :
    ∃ s', load rows = some s' ∧ enc s' = enc s ∧ Keyed s' := by
  obtain ⟨hm, he⟩ := storage.stored_view h
  have hL := storage.lists_of_loaded hm hl
  rw [he] at hL
  exact load_keyed s rows hl.1 hL

/-- On PostgreSQL, every snapshot an engine stores has unique keys. -/
theorem stored_keyed {tv : Int64} {db : PgDb} {s : kernel.Snapshot} (h : storage.Stored tv db s) :
    Keyed s := by
  induction h with
  | fresh => exact keyed_invariant.1
  | commit h₀ hl hload _ _ _ _ =>
    obtain ⟨s', hs', -, hk⟩ := stored_load h₀ hl
    have hload' : load _ = some _ := hload
    rw [hload'] at hs'
    cases hs'
    exact keyed_apply _ _ hk
  | loaded h₀ hl hload _ =>
    obtain ⟨s', hs', -, hk⟩ := stored_load h₀ hl
    have hload' : load _ = some _ := hload
    rw [hload'] at hs'
    cases hs'
    exact hk
  | cached _ _ _ _ ih => exact keyed_apply _ _ ih
  | other _ _ _ _ ih => exact ih

/-- On PostgreSQL, the snapshot loaded from a tenant's rows answers every command of every
principal as the snapshot the engine holds does. -/
theorem stored_transition {tv : Int64} {db : PgDb} {s : Snapshot} {rows : List (List (List Val))}
    (h : storage.Stored tv db s) (hl : storage.Loaded tv db rows) :
    ∃ s', load rows = some s' ∧ ∀ a c, transition a s' c = transition a s c := by
  obtain ⟨s', hs', he, hk⟩ := stored_load h hl
  obtain ⟨hm, hn⟩ := find_of_enc he
  exact ⟨s', hs', transition_congr ⟨hk, stored_keyed h, hm, hn⟩⟩

/-- On PostgreSQL, a command accepted on the snapshot loaded from a tenant's rows is authorized
against the snapshot the engine holds: a command that writes is `handle`'s result on it, with
every write permitted and every disclosed row stored and visible, before or after the command; a
read-only command is `handle`'s result on the caller's view of it, with no writes and only rows
stored and visible in the view. So the writes an engine stores are those the guard permits in the
state the tenant's rows stand for. -/
theorem stored_authorized {tv : Int64} {db : PgDb} {s s' : Snapshot} {rows : List (List (List Val))}
    {a : Principal} {c : Command} {ws : List Notes.Kernel.Write} {r : Reply}
    (h : storage.Stored tv db s) (hl : storage.Loaded tv db rows) (hs' : load rows = some s')
    (ht : transition a s' c = .ok (ws, r)) :
    (readOnly c = false ∧ handle a s c = .ok (ws, r) ∧ WritesPermitted apply policy a s ws ∧
        ReadsVisible apply policy disclosed a s ws r) ∨
      (readOnly c = true ∧ ws = [] ∧ handle a (view a s) c = .ok (ws, r) ∧
        ∀ d ∈ disclosed r, Shown policy a (view a s) d) := by
  obtain ⟨s'', hs'', he⟩ := stored_transition h hl
  rw [hs'] at hs''
  cases hs''
  exact transition_authorized (he a c ▸ ht)

/-- On PostgreSQL, a read-only command of a principal gives the same result on the snapshots
loaded from two tenants' rows, in two databases, when the rows the principal may see stand for
the same rows: nothing of the rows outside the caller's view reaches the reply. -/
theorem stored_noninterference {tv₁ tv₂ : Int64} {db₁ db₂ : PgDb} {s₁ s₂ : Snapshot}
    {rows₁ rows₂ : List (List (List Val))} {a : Principal} {c : Command} (hro : readOnly c = true)
    (h₁ : storage.Stored tv₁ db₁ s₁) (hl₁ : storage.Loaded tv₁ db₁ rows₁)
    (h₂ : storage.Stored tv₂ db₂ s₂) (hl₂ : storage.Loaded tv₂ db₂ rows₂)
    (hv : enc (view a s₁) = enc (view a s₂)) :
    ∃ s₁' s₂', load rows₁ = some s₁' ∧ load rows₂ = some s₂' ∧
      transition a s₁' c = transition a s₂' c := by
  obtain ⟨s₁', hs₁, he₁⟩ := stored_transition h₁ hl₁
  obtain ⟨s₂', hs₂, he₂⟩ := stored_transition h₂ hl₂
  obtain ⟨hm, hn⟩ := find_of_enc hv
  have hsame : SameRows (view a s₁) (view a s₂) :=
    ⟨(SameRows.refl (stored_keyed h₁)).view a |>.1, (SameRows.refl (stored_keyed h₂)).view a |>.1,
      hm, hn⟩
  exact ⟨s₁', s₂', hs₁, hs₂, by rw [he₁, he₂]; exact transition_view_congr hro hsame⟩

/-- No body a command accepted writes holds NUL, which PostgreSQL cannot store in `TEXT`. -/
theorem accepted_no_nul {a : Principal} {s : Snapshot} {c : Command} {ws : List Notes.Kernel.Write}
    {r : Reply} (h : transition a s c = .ok (ws, r)) :
    ∀ n, Notes.Kernel.Write.putNote n ∈ ws → '\x00' ∉ n.body.toList := by
  intro n hn
  rcases transition_authorized h with ⟨_, hh, _⟩ | ⟨_, hnil, _⟩
  · cases c with
    | putNote id body shared =>
      simp only [handle] at hh
      split at hh
      · rename_i hok
        simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        simp only [List.mem_singleton, Notes.Kernel.Write.putNote.injEq] at hn
        subst hn
        exact (textOk_iff.mp hok).2.2
      · cases hh
    | addMember u admin =>
      simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, -⟩ := hh
      simp at hn
    | removeMember u =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        simp at hn
    | deleteNote id =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        simp at hn
    | readNote id =>
      simp only [handle] at hh
      split at hh
      · cases hh
      · simp only [Except.ok.injEq, Prod.mk.injEq] at hh
        obtain ⟨rfl, -⟩ := hh
        simp at hn
    | listNotes =>
      simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, -⟩ := hh
      simp at hn
    | listMembers =>
      simp only [handle, Except.ok.injEq, Prod.mk.injEq] at hh
      obtain ⟨rfl, -⟩ := hh
      simp at hn
  · subst hnil
    simp at hn

/-- On PostgreSQL, every commit of the notes goes through: the `SELECT`s return rows, they load,
and every write set compiles and runs. -/
theorem stored_commit {tv : Int64} {db : PgDb} {s : Snapshot} (h : storage.Stored tv db s) :
    ∃ rows s', storage.Loaded tv db rows ∧ load rows = some s' ∧
      ∀ ws, ∃ qs db', ((writes ws).map plan).mapM (compile tables tv) = some qs ∧
        runAll db qs = some db' := by
  obtain ⟨⟨rows, s', hl, hs'⟩, hrun⟩ := storage.stored_commit h
  refine ⟨rows, s', hl, hs', fun ws => ?_⟩
  obtain ⟨qs, hq⟩ := Option.isSome_iff_exists.1 (writes_compile tv ws)
  obtain ⟨db', hr⟩ := hrun tv _ qs hq
  exact ⟨qs, db', hq, hr⟩

end Notes.Store
