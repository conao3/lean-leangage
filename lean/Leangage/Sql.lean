/-!
# SQL for a tenant's rows

Based on `crates/h5i-app-core/proofs/H5iAppLib/Pg.lean` and `Sql.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: names are `String`s and
the text is a `String`; the conditions of `compileA` and `selectA` are decided by `Bool`
functions, so that `compile`, `select`, `create` and `render` run and are generated; a tenant is
an `Int64`; bytes are an `Array UInt8`.

A kernel writes rows as `Write`s. `plan` turns a write into a `Stmt`, `compile` turns a statement
into PostgreSQL text and parameters for one tenant, `select` reads a tenant's rows of a table and
`create` makes a table. Every value is a parameter (`$1` is the tenant), and every name is quoted.
-/

namespace Leangage.Sql

inductive Kind where
  | int | bool | text | bytes
deriving DecidableEq, Repr

/-- A column value. `bytes` is an `Array UInt8` so that every host language can receive it. -/
inductive Val where
  | int (v : Int64)
  | bool (v : Bool)
  | text (v : String)
  | bytes (v : Array UInt8)
  | null
deriving DecidableEq, Repr

/-- What a kernel writes. `put` stores a row of table `table` whose first `keyLen` values are
its key, `del` removes the row with that key, `delWhere` removes the rows whose column `col`
holds `val`. -/
inductive Write where
  | put (table keyLen : Nat) (row : List Val)
  | del (table : Nat) (key : List Val)
  | delWhere (table col : Nat) (val : Val)
deriving DecidableEq, Repr

inductive Stmt where
  | upsert (table : Nat) (key rest : List Val)
  | delete (table : Nat) (key : List Val)
  | deleteWhere (table col : Nat) (val : Val)
deriving DecidableEq, Repr

structure Col where
  name : String
  kind : Kind
  nullable : Bool
deriving DecidableEq, Repr

/-- A tenant table: `tenant_id`, then `cols`. Its primary key is `tenant_id` and the first `kl`
columns. -/
structure Tab where
  name : String
  cols : List Col
  kl : Nat
deriving DecidableEq, Repr

structure ColDef where
  name : String
  kind : Kind
  notNull : Bool
deriving DecidableEq, Repr

/-- A condition of a `WHERE` clause; `p` is the parameter, counted from 1. -/
inductive Cond where
  /-- `"col" = $p` -/
  | eq (col : String) (p : Nat)
  /-- `"col" IS NOT DISTINCT FROM $p` -/
  | same (col : String) (p : Nat)
deriving DecidableEq, Repr

inductive Sql where
  | create (table : String) (cols : List ColDef) (key : List String)
  | select (table : String) (cols : List String) (conds : List Cond) (order : List String)
  | insert (table : String) (cols conflict update : List String)
  | delete (table : String) (conds : List Cond)
deriving DecidableEq, Repr, Inhabited

/-! ## Text -/

/-- Each `"` doubled. -/
def escape : List Char → List Char
  | [] => []
  | c :: cs => if c = '"' then '"' :: '"' :: escape cs else c :: escape cs

/-- A quoted identifier: `"` around the name, and each `"` inside doubled. -/
def quote (n : String) : String := String.ofList ('"' :: escape n.toList ++ ['"'])

def commaSep : List String → String
  | [] => ""
  | [x] => x
  | x :: y :: xs => x ++ ", " ++ commaSep (y :: xs)

/-- `$p` -/
def param (p : Nat) : String := "$" ++ toString p

def condText : Cond → String
  | .eq c p => quote c ++ " = " ++ param p
  | .same c p => quote c ++ " IS NOT DISTINCT FROM " ++ param p

def whereText : List Cond → String
  | [] => ""
  | c :: cs => " WHERE " ++ condText c ++ String.join (cs.map (fun c => " AND " ++ condText c))

def kindText : Kind → String
  | .int => "BIGINT"
  | .bool => "BOOLEAN"
  | .text => "TEXT"
  | .bytes => "BYTEA"

def colDefText (c : ColDef) : String :=
  quote c.name ++ " " ++ kindText c.kind ++ (if c.notNull then " NOT NULL" else "") ++ ", "

/-- `$1, $2, ..., $n` -/
def placeholders (n : Nat) : String := commaSep ((List.range n).map (fun i => param (i + 1)))

/-- The text PostgreSQL receives for a statement. -/
def render : Sql → String
  | .create t cols key =>
    "CREATE TABLE IF NOT EXISTS " ++ quote t ++ " (" ++ String.join (cols.map colDefText) ++
      "PRIMARY KEY (" ++ commaSep (key.map quote) ++ "))"
  | .select t cols conds order =>
    "SELECT " ++ commaSep (cols.map quote) ++ " FROM " ++ quote t ++ whereText conds ++
      (if order.isEmpty then "" else " ORDER BY " ++ commaSep (order.map quote))
  | .insert t cols conflict update =>
    "INSERT INTO " ++ quote t ++ " (" ++ commaSep (cols.map quote) ++ ") VALUES (" ++
      placeholders cols.length ++ ") ON CONFLICT (" ++ commaSep (conflict.map quote) ++
      (if update.isEmpty then ") DO NOTHING"
       else ") DO UPDATE SET " ++ commaSep (update.map (fun n => quote n ++ " = EXCLUDED." ++ quote n)))
  | .delete t conds => "DELETE FROM " ++ quote t ++ whereText conds

/-! ## The schema -/

/-- Every column's name, `tenant_id` first. -/
def names (t : Tab) : List String := "tenant_id" :: t.cols.map (·.name)

/-- A name PostgreSQL keeps as written when quoted: not empty, at most 63 bytes, without NUL. -/
def nameOk (n : String) : Bool := !n.isEmpty && n.utf8ByteSize ≤ 63 && !n.toList.contains '\x00'

/-- The prefix of the engine's own tables. -/
def reserved (n : String) : Bool := "leangage_".toList.isPrefixOf n.toList

def distinct : List String → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

def tabOk (t : Tab) : Bool :=
  nameOk t.name && !reserved t.name && !t.cols.isEmpty && t.cols.length < 1600 &&
    t.kl ≤ t.cols.length && (names t).all nameOk && distinct (names t)

def valid (ts : List Tab) : Bool := ts.all tabOk && distinct (ts.map (·.name))

def colDefs (t : Tab) : List ColDef :=
  ⟨"tenant_id", .int, true⟩ :: t.cols.mapIdx (fun i c => ⟨c.name, c.kind, !c.nullable || decide (i < t.kl)⟩)

def keyNames (t : Tab) : List String := "tenant_id" :: (t.cols.take t.kl).map (·.name)

/-- `CREATE TABLE IF NOT EXISTS` of a table. -/
def create (t : Tab) : Sql := .create t.name (colDefs t) (keyNames t)

/-! ## Statements -/

def valKind : Val → Option Kind
  | .int _ => some .int
  | .bool _ => some .bool
  | .text _ => some .text
  | .bytes _ => some .bytes
  | .null => none

/-- `v` may be stored in a column of kind `k`: it has that kind or is `NULL`. -/
def typed (k : Kind) (v : Val) : Bool :=
  match valKind v with
  | none => true
  | some k' => k' == k

/-- Column `i` may hold `v`: its kind, and `NULL` only in a nullable column outside the key. -/
def fitsAt (t : Tab) (i : Nat) (v : Val) : Bool :=
  match t.cols[i]? with
  | none => false
  | some c => typed c.kind v && ((valKind v).isSome || (c.nullable && decide (t.kl ≤ i)))

/-- Each value fits the column it lands in, counting from column `i`. -/
def fitsFrom (t : Tab) (i : Nat) : List Val → Bool
  | [] => true
  | v :: vs => fitsAt t i v && fitsFrom t (i + 1) vs

def plan : Write → Stmt
  | .put t kl row => .upsert t (row.take kl) (row.drop kl)
  | .del t k => .delete t k
  | .delWhere t i v => .deleteWhere t i v

/-- The statement and parameters that run a statement for the tenant `tv`: `none` when the schema
is not valid or the statement does not fit its table. -/
def compile (ts : List Tab) (tv : Int64) : Stmt → Option (Sql × List Val)
  | .upsert t k r =>
    if valid ts then
      match ts[t]? with
      | none => none
      | some tb =>
        if k.length == tb.kl && tb.kl + r.length == tb.cols.length && fitsFrom tb 0 k &&
            fitsFrom tb tb.kl r then
          some (.insert tb.name (names tb) (keyNames tb) ((tb.cols.drop tb.kl).map (·.name)),
            .int tv :: (k ++ r))
        else none
    else none
  | .delete t k =>
    if valid ts then
      match ts[t]? with
      | none => none
      | some tb =>
        if 0 < tb.kl && k.length == tb.kl && fitsFrom tb 0 k then
          some (.delete tb.name (.eq "tenant_id" 1 :: (tb.cols.take tb.kl).mapIdx (fun i c => .eq c.name (i + 2))),
            .int tv :: k)
        else none
    else none
  | .deleteWhere t i v =>
    if valid ts then
      match ts[t]? with
      | none => none
      | some tb =>
        match tb.cols[i]? with
        | none => none
        | some c =>
          if 0 < tb.kl && typed c.kind v then
            some (.delete tb.name [.eq "tenant_id" 1, .same c.name 2], [.int tv, v])
          else none
    else none

/-- `SELECT` of the tenant's rows of table `t` in key order; with `f = some (i, v)` only the rows
whose column `i` is not distinct from `v`. -/
def select (ts : List Tab) (tv : Int64) (t : Nat) (f : Option (Nat × Val)) : Option (Sql × List Val) :=
  if valid ts then
    match ts[t]? with
    | none => none
    | some tb =>
      match f with
      | none => some (.select tb.name (tb.cols.map (·.name)) [.eq "tenant_id" 1]
          ((tb.cols.take tb.kl).map (·.name)), [.int tv])
      | some (i, v) =>
        match tb.cols[i]? with
        | none => none
        | some c =>
          if typed c.kind v then
            some (.select tb.name (tb.cols.map (·.name)) [.eq "tenant_id" 1, .same c.name 2]
              ((tb.cols.take tb.kl).map (·.name)), [.int tv, v])
          else none
  else none

end Leangage.Sql
