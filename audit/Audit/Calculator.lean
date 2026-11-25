import Assay
import Calculator.Proofs

/-!
Breaks the calculator kernel in small ways and runs the theorems on each broken version. The
build fails when a broken version satisfies every theorem.
-/

deriving instance DecidableEq for Except
deriving instance DecidableEq for
  Calculator.Kernel.Principal, Calculator.Kernel.Snapshot, Calculator.Kernel.Command

#assay Calculator.Kernel.transition Calculator.Kernel.apply Calculator.Kernel.compute
    Calculator.Kernel.memoryOf Calculator.Kernel.pair Calculator.Kernel.store
  using Calculator.Kernel.transition_spec Calculator.Kernel.compute_spec
    Calculator.Kernel.get_after_run Calculator.Kernel.others_unchanged_run
    Calculator.Kernel.memoryOf_pair Calculator.Kernel.memoryOf_store
