import Lean
import Leangage
import Calculator
import Notes

/-!
Fails the build when a theorem of the listed modules depends on an axiom other than `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Lean Elab Command

elab "#assert_standard_axioms " mods:ident+ : command => do
  let env ← getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked : Nat := 0
  for m in mods do
    let some idx := env.getModuleIdx? m.getId
      | throwErrorAt m "unknown module {m.getId}"
    for name in env.header.moduleData[idx.toNat]!.constNames do
      let some (.thmInfo _) := env.find? name | continue
      checked := checked + 1
      for ax in ← liftCoreM (collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends on the axiom {ax}"
  if checked == 0 then throwError "no theorem found"
  logInfo m!"{checked} theorems depend only on propext, Classical.choice and Quot.sound"

#assert_standard_axioms Leangage.Kernel Leangage.Obligation Leangage.AuthzProofs
  Leangage.Sql.Proofs Leangage.Sql.Sound Leangage.Sql.Isolation Leangage.Store
  Leangage.Token.Proofs Leangage.Json.Proofs Leangage.Json.Items.Proofs Leangage.Http.Proofs
  Calculator.Proofs Calculator.Store.Proofs Calculator.Wire.Proofs
  Notes.Proofs Notes.Store.Proofs Notes.Wire.Proofs
