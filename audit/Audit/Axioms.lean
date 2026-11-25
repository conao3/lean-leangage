import Lean
import Leanharbor
import Calculator

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

#assert_standard_axioms Leanharbor.Kernel Leanharbor.Sql.Proofs Leanharbor.Sql.Sound
  Leanharbor.Sql.Isolation Leanharbor.Store Calculator.Proofs
