import Assay
import Audit.NotesGen
import Notes.Store.Proofs

/-!
Breaks the notes' tables and their row functions in small ways and runs the theorems on each
broken version. The build fails when a broken version satisfies every theorem.

Rows are mostly those of a member (a `BIGINT` and a `BOOLEAN`) or of a note (two `BIGINT`s, a
`BOOLEAN` and a `TEXT`), so that the row functions accept a good share of them, and `load` mostly
receives two tables.
-/

open Plausible Leanharbor.Sql

instance notesStoreArbitraryInt64 : Arbitrary Int64 where
  arbitrary := Gen.elements [0, 1, 2, -1, -9223372036854775808, 9223372036854775807] (by decide)

instance notesStoreShrinkableInt64 : Shrinkable Int64 := {}

instance notesStoreArbitraryVal : Arbitrary Val where
  arbitrary := Gen.frequency (pure .null)
    [(4, return .int (← Arbitrary.arbitrary)), (2, return .bool (← Arbitrary.arbitrary)),
     (2, pure (.text "a")), (1, pure (.text "")), (1, pure (.bytes #[0])), (1, pure .null)]

instance notesStoreShrinkableVal : Shrinkable Val := {}

instance (priority := high) notesStoreArbitraryRow : Arbitrary (List Val) where
  arbitrary := Gen.frequency (pure [])
    [(4, return [.int (← Arbitrary.arbitrary), .bool (← Arbitrary.arbitrary)]),
     (4, return [.int (← Arbitrary.arbitrary), .int (← Arbitrary.arbitrary),
       .bool (← Arbitrary.arbitrary), .text (← Gen.elements ["", "a", "b"] (by decide))]),
     (1, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary]), (1, pure []),
     (1, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary, ← Arbitrary.arbitrary,
       ← Arbitrary.arbitrary])]

instance (priority := high) notesStoreSampleableRow : SampleableExt (List Val) :=
  SampleableExt.selfContained

instance (priority := high) notesStoreArbitraryTables : Arbitrary (List (List (List Val))) where
  arbitrary := Gen.frequency (pure [])
    [(6, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary]), (1, pure []),
     (1, return [← Arbitrary.arbitrary]),
     (1, return [← Arbitrary.arbitrary, ← Arbitrary.arbitrary, ← Arbitrary.arbitrary])]

instance (priority := high) notesStoreSampleableTables : SampleableExt (List (List (List Val))) :=
  SampleableExt.selfContained

#assay Notes.Store.tables Notes.Store.memberRow Notes.Store.memberOfRow Notes.Store.noteRow
    Notes.Store.noteOfRow Notes.Store.write Notes.Store.writes Notes.Store.load
  using Notes.Store.memberOfRow_memberRow Notes.Store.memberRow_memberOfRow_run
    Notes.Store.noteOfRow_noteRow Notes.Store.noteRow_noteOfRow_run Notes.Store.valid_tables
    Notes.Store.tables_create Notes.Store.write_compile Notes.Store.writes_compile
    Notes.Store.enc_apply_run Notes.Store.load_rows Notes.Store.load_isSome
