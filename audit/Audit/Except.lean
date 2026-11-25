import Plausible

/-!
Instances for `Except` that the audits share: equality of outputs, and random values for the
kernels and policies the guard's theorems quantify over.
-/

open Plausible

deriving instance DecidableEq for Except

instance {ε α : Type} [Arbitrary ε] [Arbitrary α] : Arbitrary (Except ε α) where
  arbitrary := do
    if ← Gen.chooseAny Bool then return .ok (← Arbitrary.arbitrary)
    else return .error (← Arbitrary.arbitrary)

instance {ε α : Type} : Shrinkable (Except ε α) := {}
