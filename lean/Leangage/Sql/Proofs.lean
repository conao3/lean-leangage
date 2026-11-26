import Leangage.Sql

/-!
# What the SQL compiler guarantees

Based on `crates/h5i-app-core/proofs/H5iAppLib/Pg.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the lexer and the text
are lists of characters, the conditions of `compileA` and `selectA` are stated as `Prop`s that the
`Bool` checks of `Leangage.Sql` decide, and the statements are about the generated functions.

- `lexName_quote`: a quoted name followed by anything but `"` reads back as that name.
- `compile_params`, `select_params`: the parameters are the tenant, then the statement's values.
- `compile_placeholders`, `select_placeholders`: the text refers to `$1` … `$n`, once each and in
  order, for the `n` parameters.
- `compile_erase`, `select_erase`: the statement does not depend on the tenant or on the values,
  only on the kinds of the values.

`render_spec`, `valid_iff`, `compile_spec`, `select_spec`, `create_spec` and `plan_spec` restate
the generated functions in other terms.
-/

namespace Leangage.Sql

/-! ## A quoted name cannot end early

PostgreSQL reads a quoted identifier up to the first `"` not followed by another `"`, and reads
`""` as one `"`. -/

/-- The rest of a quoted identifier, after its opening `"`: its name and what follows the closing
`"`. -/
def lexBody : List Char → Option (List Char × List Char)
  | [] => none
  | [c] => if c = '"' then some ([], []) else none
  | c :: d :: rest =>
    if c = '"' then
      if d = '"' then (lexBody rest).map (fun p => ('"' :: p.1, p.2)) else some ([], d :: rest)
    else (lexBody (d :: rest)).map (fun p => (c :: p.1, p.2))

def lexName : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest => if c = '"' then lexBody rest else none

theorem lexBody_escape (n rest : List Char) (h : rest.head? ≠ some '"') :
    lexBody (escape n ++ '"' :: rest) = some (n, rest) := by
  induction n with
  | nil =>
    cases rest with
    | nil => simp [escape, lexBody]
    | cons d rs =>
      have : d ≠ '"' := by simpa using h
      simp [escape, lexBody, this]
  | cons c n ih =>
    by_cases hc : c = '"'
    · subst hc
      simp [escape, lexBody, ih]
    · obtain ⟨d, ds, hd⟩ : ∃ d ds, escape n ++ '"' :: rest = d :: ds := by
        cases escape n <;> exact ⟨_, _, rfl⟩
      simp only [escape, hc, ↓reduceIte, List.cons_append]
      rw [hd, lexBody]
      simp only [hc, ↓reduceIte]
      rw [← hd, ih]
      rfl

/-- A quoted name followed by anything but `"` reads back as that name. -/
theorem lexName_quote (n : String) (rest : List Char) (h : rest.head? ≠ some '"') :
    lexName ((quote n).toList ++ rest) = some (n.toList, rest) := by
  simp only [quote, String.toList_ofList, List.cons_append, List.append_assoc, lexName, ↓reduceIte]
  exact lexBody_escape n.toList rest h

/-! ## The text, as characters -/

def sepSpec (sep : List Char) : List (List Char) → List Char
  | [] => []
  | x :: xs => x ++ xs.flatMap (fun y => sep ++ y)

def quoteSpec (n : String) : List Char :=
  '"' :: n.toList.flatMap (fun c => if c = '"' then ['"', '"'] else [c]) ++ ['"']

def paramSpec (p : Nat) : List Char := '$' :: (toString p).toList

def condSpec : Cond → List Char
  | .eq c p => quoteSpec c ++ " = ".toList ++ paramSpec p
  | .same c p => quoteSpec c ++ " IS NOT DISTINCT FROM ".toList ++ paramSpec p

def whereSpec : List Cond → List Char
  | [] => []
  | c :: cs => " WHERE ".toList ++ condSpec c ++ cs.flatMap (fun c => " AND ".toList ++ condSpec c)

def kindSpec : Kind → List Char
  | .int => "BIGINT".toList
  | .bool => "BOOLEAN".toList
  | .text => "TEXT".toList
  | .bytes => "BYTEA".toList

def colDefSpec (c : ColDef) : List Char :=
  quoteSpec c.name ++ [' '] ++ kindSpec c.kind ++ (if c.notNull then " NOT NULL".toList else []) ++
    ", ".toList

/-- The text of a statement, written on lists of characters as h5i writes it on lists of bytes. -/
def renderSpec : Sql → List Char
  | .create t cols key =>
    "CREATE TABLE IF NOT EXISTS ".toList ++ quoteSpec t ++ " (".toList ++ cols.flatMap colDefSpec ++
      "PRIMARY KEY (".toList ++ sepSpec ", ".toList (key.map quoteSpec) ++ "))".toList
  | .select t cols conds order =>
    "SELECT ".toList ++ sepSpec ", ".toList (cols.map quoteSpec) ++ " FROM ".toList ++ quoteSpec t ++
      whereSpec conds ++
      (if order = [] then [] else " ORDER BY ".toList ++ sepSpec ", ".toList (order.map quoteSpec))
  | .insert t cols conflict update =>
    "INSERT INTO ".toList ++ quoteSpec t ++ " (".toList ++ sepSpec ", ".toList (cols.map quoteSpec) ++
      ") VALUES (".toList ++ sepSpec ", ".toList ((List.range' 1 cols.length).map paramSpec) ++
      ") ON CONFLICT (".toList ++ sepSpec ", ".toList (conflict.map quoteSpec) ++
      (if update = [] then ") DO NOTHING".toList
       else ") DO UPDATE SET ".toList ++
         sepSpec ", ".toList (update.map (fun n => quoteSpec n ++ " = EXCLUDED.".toList ++ quoteSpec n)))
  | .delete t conds => "DELETE FROM ".toList ++ quoteSpec t ++ whereSpec conds

theorem escape_eq (l : List Char) : escape l = l.flatMap (fun c => if c = '"' then ['"', '"'] else [c]) := by
  induction l with
  | nil => rfl
  | cons c l ih => by_cases hc : c = '"' <;> simp [escape, hc, ih]

theorem quote_toList (n : String) : (quote n).toList = quoteSpec n := by
  simp [quote, quoteSpec, escape_eq]

theorem commaSep_toList (xs : List String) :
    (commaSep xs).toList = sepSpec ", ".toList (xs.map String.toList) := by
  induction xs with
  | nil => simp [commaSep, sepSpec]
  | cons x xs ih =>
    cases xs with
    | nil => simp [commaSep, sepSpec]
    | cons y ys => simp [commaSep, ih, sepSpec]

theorem whereText_toList (cs : List Cond) : (whereText cs).toList = whereSpec cs := by
  cases cs with
  | nil => simp [whereText, whereSpec]
  | cons c cs =>
    have hc : ∀ c, (condText c).toList = condSpec c := by
      intro c; cases c <;> simp [condText, condSpec, quote_toList, param, paramSpec]
    simp [whereText, whereSpec, hc, String.toList_join, List.flatMap_map]

theorem kindText_toList (k : Kind) : (kindText k).toList = kindSpec k := by
  cases k <;> rfl

theorem colDefText_toList (c : ColDef) : (colDefText c).toList = colDefSpec c := by
  unfold colDefText colDefSpec
  cases c.notNull <;> simp [quote_toList, kindText_toList]

theorem placeholders_toList (n : Nat) :
    (placeholders n).toList = sepSpec ", ".toList ((List.range' 1 n).map paramSpec) := by
  rw [placeholders, commaSep_toList, List.map_map, List.range_eq_range', List.range'_eq_map_range,
    List.range'_eq_map_range, List.map_map, List.map_map]
  congr 2
  funext i
  simp [param, paramSpec, Nat.add_comm]

/-- `render` writes what `renderSpec` says. -/
theorem render_spec (q : Sql) : (render q).toList = renderSpec q := by
  cases q with
  | create t cols key =>
    simp [render, renderSpec, quote_toList, commaSep_toList, String.toList_join, List.flatMap_map,
      colDefText_toList, List.map_map, Function.comp_def]
  | select t cols conds order =>
    by_cases ho : order = [] <;>
      simp [render, renderSpec, quote_toList, commaSep_toList, whereText_toList, List.map_map,
        Function.comp_def, ho]
  | insert t cols conflict update =>
    by_cases hu : update = [] <;>
      simp [render, renderSpec, quote_toList, commaSep_toList, placeholders_toList, List.map_map,
        Function.comp_def, hu]
  | delete t conds => simp [render, renderSpec, quote_toList, whereText_toList]

/-! ## The schema checks -/

/-- A name PostgreSQL keeps as written when quoted. -/
def NameOk (n : String) : Prop := n ≠ "" ∧ n.utf8ByteSize ≤ 63 ∧ '\x00' ∉ n.toList

/-- A name of the engine's own tables. -/
def Reserved (n : String) : Prop := "leangage_".toList <+: n.toList

def TabOk (t : Tab) : Prop :=
  NameOk t.name ∧ ¬ Reserved t.name ∧ t.cols ≠ [] ∧ t.cols.length < 1600 ∧ t.kl ≤ t.cols.length ∧
    (∀ n ∈ "tenant_id" :: t.cols.map (·.name), NameOk n) ∧ ("tenant_id" :: t.cols.map (·.name)).Nodup

/-- Every table is well formed and no two tables share a name. -/
def Valid (ts : List Tab) : Prop := (∀ t ∈ ts, TabOk t) ∧ (ts.map (·.name)).Nodup

instance : DecidablePred NameOk := fun n => by unfold NameOk; infer_instance

instance : DecidablePred Reserved := fun n => by unfold Reserved; infer_instance

instance : DecidablePred TabOk := fun t => by unfold TabOk; infer_instance

instance : DecidablePred Valid := fun ts => by unfold Valid; infer_instance

theorem distinct_iff (l : List String) : distinct l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [distinct]
  | cons x xs ih => simp [distinct, ih]

theorem nameOk_iff (n : String) : nameOk n = true ↔ NameOk n := by
  simp [nameOk, NameOk, and_assoc]

theorem reserved_iff (n : String) : reserved n = true ↔ Reserved n := by
  simp [reserved, Reserved, List.isPrefixOf_iff_prefix]

theorem tabOk_iff (t : Tab) : tabOk t = true ↔ TabOk t := by
  simp [tabOk, TabOk, nameOk_iff, ← reserved_iff, distinct_iff, names, and_assoc]

theorem valid_iff (ts : List Tab) : valid ts = true ↔ Valid ts := by
  simp [valid, Valid, tabOk_iff, distinct_iff]

/-! ## What a statement compiles to -/

def Stmt.table : Stmt → Nat
  | .upsert t _ _ => t
  | .delete t _ => t
  | .deleteWhere t _ _ => t

/-- The values a statement passes, in order. -/
def Stmt.vals : Stmt → List Val
  | .upsert _ k r => k ++ r
  | .delete _ k => k
  | .deleteWhere _ _ v => [v]

/-- The kind of a value; `none` for `NULL`. -/
def kindOf : Val → Option Kind
  | .int _ => some .int
  | .bool _ => some .bool
  | .text _ => some .text
  | .bytes _ => some .bytes
  | .null => none

/-- Column `i` may hold `v`: its kind, and `NULL` only in a nullable column outside the key. -/
def FitsAt (t : Tab) (i : Nat) (v : Val) : Prop :=
  match t.cols[i]? with
  | none => False
  | some c => (kindOf v = none ∨ kindOf v = some c.kind) ∧ (kindOf v = none → c.nullable = true ∧ t.kl ≤ i)

/-- `v` may be stored in column `i` of `t`, outside the key. -/
def Holds (t : Tab) (i : Nat) (v : Val) : Prop :=
  match t.cols[i]? with
  | none => False
  | some c => kindOf v = none ∨ kindOf v = some c.kind

/-- The statement fits table `tb`: a full key, every column of an upsert, and values the columns
hold. Deletes are on tables with a key. -/
def Accepts (tb : Tab) : Stmt → Prop
  | .upsert _ k r =>
    k.length = tb.kl ∧ tb.kl + r.length = tb.cols.length ∧ (∀ p ∈ k.zipIdx, FitsAt tb p.2 p.1) ∧
      ∀ p ∈ r.zipIdx tb.kl, FitsAt tb p.2 p.1
  | .delete _ k => 0 < tb.kl ∧ k.length = tb.kl ∧ ∀ p ∈ k.zipIdx, FitsAt tb p.2 p.1
  | .deleteWhere _ i v => 0 < tb.kl ∧ Holds tb i v

instance (t : Tab) (i : Nat) (v : Val) : Decidable (FitsAt t i v) := by
  unfold FitsAt; split <;> infer_instance

instance (t : Tab) (i : Nat) (v : Val) : Decidable (Holds t i v) := by
  unfold Holds; split <;> infer_instance

instance (tb : Tab) (s : Stmt) : Decidable (Accepts tb s) := by
  cases s <;> unfold Accepts <;> infer_instance

/-- The SQL of a statement on table `tb`. -/
def sqlOf (tb : Tab) : Stmt → Sql
  | .upsert _ _ _ =>
    .insert tb.name ("tenant_id" :: tb.cols.map (·.name)) ("tenant_id" :: (tb.cols.map (·.name)).take tb.kl)
      ((tb.cols.map (·.name)).drop tb.kl)
  | .delete _ _ =>
    .delete tb.name ((("tenant_id" :: (tb.cols.map (·.name)).take tb.kl).zip (List.range' 1 (tb.kl + 1))).map
      (fun (n, p) => .eq n p))
  | .deleteWhere _ i _ =>
    .delete tb.name [.eq "tenant_id" 1, .same ((tb.cols[i]?.map (·.name)).getD "") 2]

theorem valKind_spec (v : Val) : valKind v = kindOf v := by
  cases v <;> rfl

theorem typed_iff (k : Kind) (v : Val) : typed k v = true ↔ kindOf v = none ∨ kindOf v = some k := by
  cases v <;> cases k <;> simp [typed, valKind, kindOf]

theorem fitsAt_iff (t : Tab) (i : Nat) (v : Val) : fitsAt t i v = true ↔ FitsAt t i v := by
  unfold fitsAt FitsAt
  cases h : t.cols[i]? with
  | none => simp
  | some c =>
    simp only [Bool.and_eq_true, typed_iff, Bool.or_eq_true, Option.isSome_iff_ne_none,
      decide_eq_true_eq, valKind_spec]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun hn => (h2.resolve_left (· hn))⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_cases hn : kindOf v = none
      · exact .inr (h2 hn)
      · exact .inl hn

theorem fitsFrom_iff (t : Tab) (i : Nat) (vs : List Val) :
    fitsFrom t i vs = true ↔ ∀ p ∈ vs.zipIdx i, FitsAt t p.2 p.1 := by
  induction vs generalizing i with
  | nil => simp [fitsFrom]
  | cons v vs ih => simp [fitsFrom, ih, fitsAt_iff, List.zipIdx_cons]

theorem mapIdx_eq_zip (tb : Tab) :
    (tb.cols.take tb.kl).mapIdx (fun i c => Cond.eq c.name (i + 2)) =
      (((tb.cols.map (·.name)).take tb.kl).zip (List.range' 2 tb.kl)).map (fun (n, p) => .eq n p) := by
  apply List.ext_getElem
  · simp [List.length_zip]
  · intro j h1 h2
    simp [Nat.add_comm]

theorem delete_conds (tb : Tab) :
    Cond.eq "tenant_id" 1 :: (tb.cols.take tb.kl).mapIdx (fun i c => .eq c.name (i + 2)) =
      ((("tenant_id" :: (tb.cols.map (·.name)).take tb.kl).zip (List.range' 1 (tb.kl + 1))).map
        (fun (n, p) => .eq n p)) := by
  rw [mapIdx_eq_zip, List.range'_succ]
  rfl

/-- `compile` returns the SQL of `sqlOf` with the tenant and the values when the schema is valid
and the statement fits its table, and `none` otherwise. -/
theorem compile_spec (ts : List Tab) (tv : Int64) (s : Stmt) :
    compile ts tv s =
      match ts[s.table]? with
      | none => none
      | some tb => if Valid ts ∧ Accepts tb s then some (sqlOf tb s, .int tv :: s.vals) else none := by
  cases s with
  | upsert t k r =>
    simp only [compile, Stmt.table, ← valid_iff]
    cases ht : ts[t]? with
    | none => simp
    | some tb =>
      simp only [Accepts, sqlOf, Stmt.vals, names, keyNames, ← fitsFrom_iff, List.map_take,
        List.map_drop]
      by_cases hv : valid ts = true <;> simp [hv, and_assoc]
  | delete t k =>
    simp only [compile, Stmt.table, ← valid_iff]
    cases ht : ts[t]? with
    | none => simp
    | some tb =>
      simp only [Accepts, sqlOf, Stmt.vals, ← fitsFrom_iff, ← delete_conds]
      by_cases hv : valid ts = true <;> simp [hv, and_assoc]
  | deleteWhere t i v =>
    simp only [compile, Stmt.table, ← valid_iff]
    cases ht : ts[t]? with
    | none => simp
    | some tb =>
      simp only [Accepts, sqlOf, Stmt.vals]
      by_cases hv : valid ts = true
      · cases hc : tb.cols[i]? with
        | none => simp [hv, Holds, hc]
        | some c => by_cases hk : 0 < tb.kl <;> simp [hv, hc, hk, typed_iff, Holds]
      · simp [hv]

/-- The `SELECT` of table `tb`, with a filter on column `i` when `filter` holds. -/
def selectOf (tb : Tab) (filter : Option Nat) : Sql :=
  .select tb.name (tb.cols.map (·.name))
    (.eq "tenant_id" 1 :: (filter.map (fun i => Cond.same ((tb.cols[i]?.map (·.name)).getD "") 2)).toList)
    ((tb.cols.map (·.name)).take tb.kl)

/-- `select` returns the `SELECT` of the table with the tenant and the filter's value when the
schema is valid, the table exists and the filter's value fits its column. -/
theorem select_spec (ts : List Tab) (tv : Int64) (t : Nat) (f : Option (Nat × Val)) :
    select ts tv t f =
      match ts[t]? with
      | none => none
      | some tb =>
        if Valid ts ∧ ∀ p ∈ f.toList, Holds tb p.1 p.2 then
          some (selectOf tb (f.map (·.1)), .int tv :: (f.map (·.2)).toList)
        else none := by
  simp only [select, ← valid_iff]
  cases ht : ts[t]? with
  | none => simp
  | some tb =>
    by_cases hv : valid ts = true
    · cases f with
      | none => simp [hv, selectOf, List.map_take]
      | some p =>
        obtain ⟨i, v⟩ := p
        cases hc : tb.cols[i]? with
        | none => simp [hv, hc, Holds]
        | some c => by_cases hk : typed c.kind v = true <;>
            simp_all [selectOf, List.map_take, typed_iff, Holds]
    · simp [hv]

/-- `create` makes `tenant_id` a `BIGINT NOT NULL`, keeps each column's kind, makes a column
`NOT NULL` when it is in the key or not nullable, and keys the table on `tenant_id` and the first
`kl` columns. -/
theorem create_spec (t : Tab) :
    create t = .create t.name
      (⟨"tenant_id", .int, true⟩ :: t.cols.zipIdx.map (fun (c, i) => ⟨c.name, c.kind, !c.nullable || decide (i < t.kl)⟩))
      ("tenant_id" :: (t.cols.map (·.name)).take t.kl) := by
  simp only [create, colDefs, keyNames, List.map_take, Sql.create.injEq, true_and,
    List.cons.injEq, and_true]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp

/-- `plan` splits a put's row after its key and keeps deletes as they are. -/
theorem plan_spec (w : Write) :
    match w with
    | .put t kl row => ∃ k r, plan w = .upsert t k r ∧ k ++ r = row ∧ k.length = min kl row.length
    | .del t k => plan w = .delete t k
    | .delWhere t i v => plan w = .deleteWhere t i v := by
  cases w with
  | put t kl row => exact ⟨_, _, rfl, List.take_append_drop _ _, List.length_take⟩
  | del t k => rfl
  | delWhere t i v => rfl

/-! ## Parameters, placeholders and tenants -/

/-- The parameters the text refers to, in the order it writes them. -/
def Sql.params : Sql → List Nat
  | .create _ _ _ => []
  | .select _ _ conds _ => conds.map (fun | .eq _ p => p | .same _ p => p)
  | .insert _ cols _ _ => List.range' 1 cols.length
  | .delete _ conds => conds.map (fun | .eq _ p => p | .same _ p => p)

/-- The parameters of a compiled statement are the tenant, then the statement's values in order. -/
theorem compile_params (ts : List Tab) (tv : Int64) (s : Stmt) :
    match compile ts tv s with
    | some (_, ps) => ps = .int tv :: s.vals
    | none => True := by
  rw [compile_spec]
  cases ts[s.table]? with
  | none => trivial
  | some tb => by_cases h : Valid ts ∧ Accepts tb s <;> simp [h]

/-- The parameters of a `SELECT` are the tenant, then the filter's value. -/
theorem select_params (ts : List Tab) (tv : Int64) (t : Nat) (f : Option (Nat × Val)) :
    match select ts tv t f with
    | some (_, ps) => ps = .int tv :: (f.map (·.2)).toList
    | none => True := by
  rw [select_spec]
  cases ts[t]? with
  | none => trivial
  | some tb =>
    dsimp only
    by_cases h : Valid ts ∧ ∀ p ∈ f.toList, Holds tb p.1 p.2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; trivial

theorem tabOk_of_mem {ts : List Tab} {t : Nat} {tb : Tab} (hv : Valid ts) (h : ts[t]? = some tb) :
    TabOk tb :=
  hv.1 tb (List.mem_of_getElem? h)

/-- The text of a compiled statement refers to `$1` … `$n` for its `n` parameters, each once and in
order: every parameter is used and no value is written into the text. -/
theorem compile_placeholders (ts : List Tab) (tv : Int64) (s : Stmt) :
    match compile ts tv s with
    | some (q, ps) => q.params = List.range' 1 ps.length
    | none => True := by
  rw [compile_spec]
  cases ht : ts[s.table]? with
  | none => trivial
  | some tb =>
    by_cases h : Valid ts ∧ Accepts tb s
    · simp only [h, and_self, ↓reduceIte]
      have hkl := (tabOk_of_mem h.1 ht).2.2.2.2.1
      cases s with
      | upsert t k r =>
        obtain ⟨hk, hr, -, -⟩ := h.2
        simp [sqlOf, Sql.params, Stmt.vals]
        omega
      | delete t k =>
        obtain ⟨-, hk, -⟩ := h.2
        have hl : (List.range' 1 (tb.kl + 1)).length ≤ ("tenant_id" :: (tb.cols.map (·.name)).take tb.kl).length := by
          simp; omega
        simp only [sqlOf, Sql.params, Stmt.vals, List.map_map, List.length_cons, hk]
        have e : ((fun c => match c with | Cond.eq _ p => p | Cond.same _ p => p) ∘
            fun x : String × Nat => Cond.eq x.1 x.2) = Prod.snd := by
          funext x; rfl
        rw [e, List.map_snd_zip hl]
      | deleteWhere t i v => simp [sqlOf, Sql.params, Stmt.vals, List.range'_succ]
    · simp [h]

/-- The text of a `SELECT` refers to `$1` … `$n` for its `n` parameters, each once and in order. -/
theorem select_placeholders (ts : List Tab) (tv : Int64) (t : Nat) (f : Option (Nat × Val)) :
    match select ts tv t f with
    | some (q, ps) => q.params = List.range' 1 ps.length
    | none => True := by
  rw [select_spec]
  cases ts[t]? with
  | none => trivial
  | some tb =>
    dsimp only
    by_cases h : Valid ts ∧ ∀ p ∈ f.toList, Holds tb p.1 p.2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      cases f <;> simp [selectOf, Sql.params, List.range'_succ]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; trivial

/-- A value of the same kind: what the text may depend on. -/
def Val.erase : Val → Val
  | .int _ => .int 0
  | .bool _ => .bool false
  | .text _ => .text ""
  | .bytes _ => .bytes #[]
  | .null => .null

def Stmt.erase : Stmt → Stmt
  | .upsert t k r => .upsert t (k.map Val.erase) (r.map Val.erase)
  | .delete t k => .delete t (k.map Val.erase)
  | .deleteWhere t i v => .deleteWhere t i v.erase

theorem kind_erase (v : Val) : kindOf v.erase = kindOf v := by
  cases v <;> rfl

theorem fitsAt_erase (tb : Tab) (i : Nat) (v : Val) : FitsAt tb i v.erase ↔ FitsAt tb i v := by
  unfold FitsAt; split <;> simp [kind_erase]

theorem fitsAll_erase (tb : Tab) (l : List Val) (i : Nat) :
    (∀ p ∈ (l.map Val.erase).zipIdx i, FitsAt tb p.2 p.1) ↔ ∀ p ∈ l.zipIdx i, FitsAt tb p.2 p.1 := by
  induction l generalizing i with
  | nil => simp
  | cons v l ih => simp only [List.map_cons, List.zipIdx_cons, List.forall_mem_cons, fitsAt_erase, ih]

theorem accepts_erase (tb : Tab) (s : Stmt) : Accepts tb s.erase ↔ Accepts tb s := by
  cases s with
  | upsert t k r => simp only [Stmt.erase, Accepts, fitsAll_erase, List.length_map]
  | delete t k => simp only [Stmt.erase, Accepts, fitsAll_erase, List.length_map]
  | deleteWhere t i v => simp only [Stmt.erase, Accepts, Holds, kind_erase]

/-- The SQL of a statement is the same for every tenant and for every value of the same kinds:
it depends on the schema, the table, the column and the kinds of the values only. -/
theorem compile_erase (ts : List Tab) (tv : Int64) (s : Stmt) :
    (compile ts tv s).map (·.1) = (compile ts 0 s.erase).map (·.1) := by
  have ht : s.erase.table = s.table := by cases s <;> rfl
  have hq : ∀ tb, sqlOf tb s.erase = sqlOf tb s := by intro tb; cases s <;> rfl
  rw [compile_spec, compile_spec, ht]
  cases ts[s.table]? with
  | none => rfl
  | some tb => by_cases h : Valid ts ∧ Accepts tb s <;> simp [h, accepts_erase, hq]

/-- The SQL of a `SELECT` is the same for every tenant and every filter value of the same kind. -/
theorem select_erase (ts : List Tab) (tv : Int64) (t : Nat) (f : Option (Nat × Val)) :
    (select ts tv t f).map (·.1) = (select ts 0 t (f.map (fun (i, v) => (i, v.erase)))).map (·.1) := by
  rw [select_spec, select_spec]
  cases ts[t]? with
  | none => rfl
  | some tb =>
    dsimp only
    have hc : (∀ p ∈ (f.map (fun (i, v) => (i, v.erase))).toList, Holds tb p.1 p.2) ↔
        ∀ p ∈ f.toList, Holds tb p.1 p.2 := by
      cases f with
      | none => simp
      | some p => obtain ⟨i, v⟩ := p; simp [Holds, kind_erase]
    split <;> split
    · cases f <;> rfl
    · rename_i h1 h2; exact absurd ⟨h1.1, hc.2 h1.2⟩ h2
    · rename_i h1 h2; exact absurd ⟨h2.1, hc.1 h2.2⟩ h1
    · rfl

end Leangage.Sql
