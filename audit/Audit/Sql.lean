import Assay
import Leanharbor.Sql.Proofs

/-!
Breaks the SQL compiler in small ways and runs the theorems on each broken version. The build
fails when a broken version satisfies every theorem.

The schemas are mostly two fixed valid ones and otherwise drawn from a few names, and the
statements are drawn on tables, keys and values those schemas have, so that `compile` and `select`
accept a good share of the inputs.
-/

open Plausible Leanharbor.Sql

def upTo (n : Nat) (g : Gen α) : Gen (List α) := do
  let k ← Gen.choose Nat 0 n (Nat.zero_le _)
  (List.range k.val).mapM (fun _ => g)

def nameGen : Gen String :=
  Gen.frequency (pure "a")
    [(9, Gen.elements ["a", "b", "id", "x\"y", "é", "\"\""] (by decide)),
     (1, Gen.elements ["", "tenant_id", "leanharbor_t", String.ofList (List.replicate 64 'n'), "a\x00"]
       (by decide))]

def notes : List Tab :=
  [⟨"notes", [⟨"id", .int, false⟩, ⟨"body", .text, true⟩], 1⟩,
   ⟨"tags", [⟨"note", .int, false⟩, ⟨"tag", .text, false⟩], 2⟩]

def odd : List Tab :=
  [⟨"x\"y", [⟨"é", .int, true⟩], 0⟩,
   ⟨"kv", [⟨"k", .text, false⟩, ⟨"v", .bytes, true⟩, ⟨"n", .int, true⟩], 1⟩]

instance (priority := high) : Arbitrary Nat where
  arbitrary := Gen.frequency (pure 0) [(5, pure 0), (3, pure 1), (1, pure 2), (1, pure 3)]

instance : Arbitrary Int64 where
  arbitrary := Gen.elements [0, 1, -1, 7, -9223372036854775808, 9223372036854775807] (by decide)

instance : Shrinkable Int64 := {}

instance : Arbitrary Kind where
  arbitrary := Gen.frequency (pure .int) [(5, pure .int), (3, pure .text), (1, pure .bool), (1, pure .bytes)]

instance : Arbitrary Val where
  arbitrary := Gen.frequency (pure .null)
    [(9, return .int (← Arbitrary.arbitrary)),
     (1, Gen.elements [.bool false, .bool true] (by decide)),
     (6, Gen.elements [.text "", .text "a", .text "\""] (by decide)),
     (2, Gen.elements [.bytes #[], .bytes #[0, 255]] (by decide)),
     (2, pure .null)]

instance : Shrinkable Val := {}

instance : Arbitrary Col where
  arbitrary := return ⟨← nameGen, ← Arbitrary.arbitrary, ← Gen.elements [false, true] (by decide)⟩

instance : Shrinkable Col := {}

instance : Arbitrary Tab where
  arbitrary := do
    let cols ← Gen.frequency (pure [])
      [(9, return (← Arbitrary.arbitrary) :: (← upTo 2 Arbitrary.arbitrary)), (1, pure [])]
    let kl ← Gen.choose Nat 0 (cols.length + 1) (Nat.zero_le _)
    return ⟨← nameGen, cols, kl.val⟩

instance : Shrinkable Tab := {}

instance (priority := high) : Arbitrary (List Tab) where
  arbitrary := Gen.frequency (pure notes)
    [(4, pure notes), (3, pure odd), (3, upTo 3 Arbitrary.arbitrary)]

instance (priority := high) : Arbitrary (List Val) where
  arbitrary := Gen.frequency (pure [])
    [(2, return [← Arbitrary.arbitrary]), (2, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary]),
     (1, pure []), (1, upTo 3 Arbitrary.arbitrary)]

instance : Arbitrary Stmt where
  arbitrary := Gen.oneOf #[
    return .upsert (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary),
    return .delete (← Arbitrary.arbitrary) (← Arbitrary.arbitrary),
    return .deleteWhere (← Arbitrary.arbitrary) (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)]

instance : Shrinkable Stmt := {}

instance (priority := high) : SampleableExt Nat := SampleableExt.selfContained

instance (priority := high) : SampleableExt (List Tab) := SampleableExt.selfContained

instance (priority := high) : SampleableExt (List Val) := SampleableExt.selfContained

#assay Leanharbor.Sql.escape Leanharbor.Sql.quote
  using Leanharbor.Sql.lexName_quote Leanharbor.Sql.render_spec

#assay Leanharbor.Sql.commaSep Leanharbor.Sql.param Leanharbor.Sql.condText Leanharbor.Sql.whereText
    Leanharbor.Sql.kindText Leanharbor.Sql.colDefText Leanharbor.Sql.placeholders Leanharbor.Sql.render
  using Leanharbor.Sql.render_spec

#assay Leanharbor.Sql.nameOk Leanharbor.Sql.reserved Leanharbor.Sql.distinct Leanharbor.Sql.tabOk
    Leanharbor.Sql.valid
  using Leanharbor.Sql.nameOk_iff Leanharbor.Sql.reserved_iff Leanharbor.Sql.distinct_iff
    Leanharbor.Sql.tabOk_iff Leanharbor.Sql.valid_iff

#assay Leanharbor.Sql.valKind Leanharbor.Sql.typed Leanharbor.Sql.fitsAt Leanharbor.Sql.fitsFrom
  using Leanharbor.Sql.valKind_spec Leanharbor.Sql.typed_iff Leanharbor.Sql.fitsAt_iff
    Leanharbor.Sql.fitsFrom_iff

#assay Leanharbor.Sql.names Leanharbor.Sql.colDefs Leanharbor.Sql.keyNames
    Leanharbor.Sql.create
  using Leanharbor.Sql.create_spec Leanharbor.Sql.tabOk_iff Leanharbor.Sql.compile_spec

#assay Leanharbor.Sql.plan using Leanharbor.Sql.plan_spec

#assay Leanharbor.Sql.compile
  using Leanharbor.Sql.compile_spec Leanharbor.Sql.compile_params Leanharbor.Sql.compile_placeholders
    Leanharbor.Sql.compile_erase

#assay Leanharbor.Sql.select
  using Leanharbor.Sql.select_spec Leanharbor.Sql.select_params Leanharbor.Sql.select_placeholders
    Leanharbor.Sql.select_erase
