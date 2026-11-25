import Assay
import Audit.Calculator
import Calculator.Store.Proofs

/-!
Breaks the calculator's table and its row functions in small ways and runs the theorems on each
broken version. The build fails when a broken version satisfies every theorem.

Rows are mostly two `BIGINT`s, so that `fromRow` accepts a good share of them, and `load` mostly
receives one table. The instances `#assay` derives for the calculator kernel come from
`Audit.Calculator`.
-/

open Plausible Leanharbor.Sql

instance storeArbitraryInt64 : Arbitrary Int64 where
  arbitrary := Gen.elements [0, 1, -1, 7, -9223372036854775808, 9223372036854775807] (by decide)

instance storeShrinkableInt64 : Shrinkable Int64 := {}

instance storeArbitraryVal : Arbitrary Val where
  arbitrary := Gen.frequency (pure .null)
    [(8, return .int (← Arbitrary.arbitrary)), (1, pure (.bool true)), (1, pure (.text "a")),
     (1, pure (.bytes #[0])), (1, pure .null)]

instance storeShrinkableVal : Shrinkable Val := {}

instance (priority := high) storeArbitraryRow : Arbitrary (List Val) where
  arbitrary := Gen.frequency (pure [])
    [(6, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary]), (1, return [← Arbitrary.arbitrary]),
     (1, pure []), (1, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary, ← Arbitrary.arbitrary])]

instance (priority := high) storeSampleableRow : SampleableExt (List Val) :=
  SampleableExt.selfContained

instance (priority := high) storeArbitraryTables : Arbitrary (List (List (List Val))) where
  arbitrary := Gen.frequency (pure [])
    [(6, return [← Arbitrary.arbitrary]), (1, pure []),
     (1, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary])]

instance (priority := high) storeSampleableTables : SampleableExt (List (List (List Val))) :=
  SampleableExt.selfContained

#assay Calculator.Store.tables Calculator.Store.toRow Calculator.Store.fromRow
    Calculator.Store.writes Calculator.Store.storeAll Calculator.Store.load
  using Calculator.Store.fromRow_toRow Calculator.Store.toRow_fromRow_run
    Calculator.Store.valid_tables Calculator.Store.tables_create Calculator.Store.writes_compile
    Calculator.Store.enc_apply_run Calculator.Store.lookup_storeAll Calculator.Store.load_toRow
    Calculator.Store.load_isSome
