import Plausible

/-!
Random inputs for the notes audits. Ids, users and orgs are drawn from 0 to 3, so that random
snapshots often hold the caller's member row, notes the caller owns and notes under the same id.
-/

open Plausible

instance (priority := high) : Arbitrary UInt64 where
  arbitrary := do return (← Gen.chooseNatLt 0 4 (by decide)).val.toUInt64
