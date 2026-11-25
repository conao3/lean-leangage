import Leanharbor.Sql.Proofs

/-!
# A model of PostgreSQL, and what a statement means to a tenant

Based on `crates/h5i-app-core/proofs/H5iAppLib/Pg.lean` and `Sql.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the model is about `Val`
and `kindOf` instead of any value type with a `kind` function, names are `String`s, a row is
checked against its columns position by position, a tenant is an `Int64` whose rows hold
`.int tv` in `tenant_id`, and `exec` is about the generated `Stmt`.

`run` says what PostgreSQL does to the tables when it is sent `render q` with the parameters `ps`,
and `selected` which rows a `SELECT` returns, in no particular order. `none` is where the model
makes no claim: PostgreSQL may fail there, or the statement is outside the subset `compile`,
`select` and `create` produce.

Trusted: PostgreSQL, sent `render q` with `ps`, fails or does what `run` says, and a `SELECT`
returns a reordering of what `selected` says. Values compare as Lean values do (text character by
character, bytes byte by byte). The tables were made by `create` of the same schema;
`CREATE TABLE IF NOT EXISTS` keeps a table of that name as it is.

`view ts tv db` is the tenant `tv`'s database as a kernel sees it, and `exec` says what a
statement does to it.
-/

namespace Leanharbor.Sql

open Classical

/-! ## PostgreSQL -/

structure Table where
  cols : List ColDef
  key : List String
  rows : List (List Val)

/-- A database: the table with each name, if any. -/
def PgDb := String → Option Table

def colIdx (cols : List ColDef) (n : String) : Option Nat := cols.findIdx? (fun c => c.name = n)

/-- The value of `$p`. -/
def arg (ps : List Val) (p : Nat) : Option Val := if p = 0 then none else ps[p - 1]?

/-- A value can be bound where kind `k` is expected: `NULL`, or of kind `k`. -/
def Typed (k : Kind) (v : Val) : Prop := kindOf v = none ∨ kindOf v = some k

/-- `v` can be stored in column `c`. -/
def Stores (c : ColDef) (v : Val) : Prop := Typed c.kind v ∧ (c.notNull = true → kindOf v ≠ none)

/-- `row` has one value for each column, and each value can be stored in its column. -/
def StoresAll (cols : List ColDef) (row : List Val) : Prop :=
  cols.length = row.length ∧ ∀ i (h1 : i < cols.length) (h2 : i < row.length), Stores cols[i] row[i]

/-- The condition names a column, and its parameter has the column's kind. -/
def CondOk (cols : List ColDef) (ps : List Val) : Cond → Prop
  | .eq n p | .same n p =>
    ∃ i c v, colIdx cols n = some i ∧ cols[i]? = some c ∧ arg ps p = some v ∧ Typed c.kind v

/-- The condition is true of `row`. `=` is true only of two equal values that are not `NULL`;
`IS NOT DISTINCT FROM` is equality, `NULL` included. -/
def CondHolds (cols : List ColDef) (ps : List Val) (row : List Val) : Cond → Prop
  | .eq n p => ∃ i v, colIdx cols n = some i ∧ arg ps p = some v ∧ row[i]? = some v ∧ kindOf v ≠ none
  | .same n p => ∃ i v, colIdx cols n = some i ∧ arg ps p = some v ∧ row[i]? = some v

def AllHold (cols : List ColDef) (ps : List Val) (row : List Val) (cs : List Cond) : Prop :=
  ∀ c ∈ cs, CondHolds cols ps row c

/-- The values of the named columns. -/
def project (cols : List ColDef) (ns : List String) (row : List Val) : List Val :=
  ns.filterMap (fun n => (colIdx cols n).bind (row[·]?))

/-- The row an `INSERT` of all columns builds: each column gets the parameter at its position in
the column list. -/
def newRow (cols : List ColDef) (ns : List String) (ps : List Val) : Option (List Val) :=
  cols.mapM (fun c => ps[ns.idxOf c.name]?)

/-- `DO UPDATE SET u = EXCLUDED.u, ...`: the columns in `up` from `new`, the others from `old`. -/
def setCols (cols : List ColDef) (up : List String) (old new : List Val) : List Val :=
  (cols.zip (old.zip new)).map (fun x => if x.1.name ∈ up then x.2.2 else x.2.1)

def put (db : PgDb) (n : String) (t : Table) : PgDb := fun n' => if n' = n then some t else db n'

/-- What a statement does to the tables. -/
noncomputable def run (db : PgDb) : Sql → List Val → Option PgDb
  | .create t cols key, _ =>
    match db t with
    | some _ => some db
    | none =>
      if (cols.map (·.name)).Nodup ∧ key.Nodup ∧ ∀ n ∈ key, ∃ c ∈ cols, c.name = n ∧ c.notNull = true then
        some (put db t ⟨cols, key, []⟩)
      else none
  | .insert t ns conflict up, ps =>
    match db t with
    | none => none
    | some tab =>
      if ns.length = ps.length ∧ ns.Nodup ∧ (∀ c ∈ tab.cols, c.name ∈ ns) ∧
          (∀ n ∈ ns, ∃ c ∈ tab.cols, c.name = n) ∧ (∀ n, n ∈ conflict ↔ n ∈ tab.key) ∧
          (∀ n ∈ up, ∃ c ∈ tab.cols, c.name = n) then
        match newRow tab.cols ns ps with
        | none => none
        | some new =>
          if StoresAll tab.cols new then
            let key := project tab.cols tab.key
            if ∃ r ∈ tab.rows, key r = key new then
              some (put db t { tab with rows := tab.rows.map (fun r =>
                if key r = key new ∧ up ≠ [] then setCols tab.cols up r new else r) })
            else some (put db t { tab with rows := tab.rows ++ [new] })
          else none
      else none
  | .delete t conds, ps =>
    match db t with
    | none => none
    | some tab =>
      if ∀ c ∈ conds, CondOk tab.cols ps c then
        some (put db t { tab with rows := tab.rows.filter (fun r => ¬ AllHold tab.cols ps r conds) })
      else none
  | .select .., _ => some db

/-- The rows a `SELECT` returns, in some order. -/
noncomputable def selected (db : PgDb) : Sql → List Val → Option (List (List Val))
  | .select t ns conds _, ps =>
    match db t with
    | none => none
    | some tab =>
      if (∀ c ∈ conds, CondOk tab.cols ps c) ∧ ∀ n ∈ ns, ∃ c ∈ tab.cols, c.name = n then
        some ((tab.rows.filter (fun r => AllHold tab.cols ps r conds)).map (project tab.cols ns))
      else none
  | _, _ => none

/-- Statements run in order; `none` if one of them has no claimed outcome. -/
noncomputable def runAll (db : PgDb) : List (Sql × List Val) → Option PgDb
  | [] => some db
  | q :: qs => (run db q.1 q.2).bind (fun db' => runAll db' qs)

/-! ## A tenant's database -/

/-- Rows per table. -/
def Tables := Nat → List (List Val)

/-- One tenant's database: the row stored at each table and key, if any. -/
def Db := Nat → List Val → Option (List Val)

/-- The key length of table `t`. -/
def klOf (ts : List Tab) (t : Nat) : Nat := (ts[t]?.map (·.kl)).getD 0

/-- The tenant's rows of each table, without `tenant_id`. -/
def tenantTabs (ts : List Tab) (tv : Int64) (db : PgDb) : Tables := fun t =>
  match ts[t]? with
  | none => []
  | some tb =>
    match db tb.name with
    | none => []
    | some tab => (tab.rows.filter (fun r => r.head? = some (.int tv))).map List.tail

/-- The database a set of keyed tables stands for; `kl t` is table `t`'s key length. -/
def readBack (kl : Nat → Nat) (tabs : Tables) : Db :=
  fun t k => (tabs t).find? (fun r => r.take (kl t) = k)

/-- The tenant's database. -/
def view (ts : List Tab) (tv : Int64) (db : PgDb) : Db := readBack (klOf ts) (tenantTabs ts tv db)

def RowOk (tb : Tab) (r : List Val) : Prop := StoresAll (colDefs tb) r

/-- A table as `create` made it, with rows PostgreSQL accepted: typed, and unique on the primary
key. -/
def TableOk (tb : Tab) (tab : Table) : Prop :=
  tab.cols = colDefs tb ∧ tab.key = keyNames tb ∧ (∀ r ∈ tab.rows, RowOk tb r) ∧
    (tab.rows.map (·.take (tb.kl + 1))).Nodup

/-- Every table of the schema exists, as `create` made it. -/
def Matches (ts : List Tab) (db : PgDb) : Prop :=
  ∀ tb ∈ ts, ∃ tab, db tb.name = some tab ∧ TableOk tb tab

/-! ## What a statement means -/

/-- What a statement does to one tenant's database. -/
def exec (db : Db) : Stmt → Db
  | .upsert t k r => fun t' k' => if t' = t ∧ k' = k then some (k ++ r) else db t' k'
  | .delete t k => fun t' k' => if t' = t ∧ k' = k then none else db t' k'
  | .deleteWhere t i v => fun t' k' => (db t' k').filter (fun r => !decide (t' = t ∧ r[i]? = some v))

def execAll (db : Db) (ss : List Stmt) : Db := ss.foldl exec db

/-- Column `i` holds `v`. -/
def ColIs (i : Nat) (v : Val) (row : List Val) : Prop := row[i]? = some v

/-- The rows a `SELECT` with this filter keeps. -/
def Filter : Option (Nat × Val) → List Val → Prop
  | none, _ => True
  | some (i, v), row => ColIs i v row

/-- `R` lists every stored row of table `t` that satisfies `Q`, once each, in any order. -/
def Sel (kl : Nat → Nat) (db : Db) (t : Nat) (Q : List Val → Prop) (R : List (List Val)) : Prop :=
  R.Nodup ∧ ∀ row, row ∈ R ↔ db t (row.take (kl t)) = some row ∧ Q row

/-- `R t` lists every stored row of table `t`, once each, in any order. -/
def Lists (kl : Nat → Nat) (db : Db) (R : Tables) : Prop :=
  ∀ t, (R t).Nodup ∧ ∀ row, row ∈ R t ↔ db t (row.take (kl t)) = some row

end Leanharbor.Sql
