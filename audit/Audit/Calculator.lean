import Assay
import Audit.Except
import Audit.Obligations
import Calculator.Proofs

/-!
Checks that the calculator's theorems state the obligations of `Leanharbor.Obligation`, then
breaks the calculator kernel in small ways and runs the theorems on each broken version. The
build fails when an obligation has no theorem or a broken version satisfies every theorem.
-/

#obligations Calculator.Kernel.kernel

deriving instance DecidableEq for
  Calculator.Kernel.Principal, Calculator.Kernel.Snapshot, Calculator.Kernel.Command

#assay Calculator.Kernel.transition Calculator.Kernel.apply Calculator.Kernel.compute
    Calculator.Kernel.memoryOf Calculator.Kernel.pair Calculator.Kernel.store
  using Calculator.Kernel.transition_spec Calculator.Kernel.compute_spec
    Calculator.Kernel.get_after_run Calculator.Kernel.others_unchanged_run
    Calculator.Kernel.memoryOf_pair Calculator.Kernel.memoryOf_store

#assay Calculator.Kernel.errorName Calculator.Kernel.replyToks Calculator.Kernel.errorToks
    Calculator.Kernel.encodeReply Calculator.Kernel.encodeError
  using Calculator.Kernel.errorName_spec Calculator.Kernel.replyToks_spec
    Calculator.Kernel.errorToks_spec Calculator.Kernel.encodeReply_spec
    Calculator.Kernel.encodeError_spec

#assay Calculator.Kernel.errorString Calculator.Kernel.encodeReplyArray Calculator.Kernel.encodeErrorArray
  using Calculator.Kernel.errorString_spec Calculator.Kernel.encodeReplyArray_eq
    Calculator.Kernel.encodeErrorArray_eq Calculator.Kernel.encodeReplyArray_spec
    Calculator.Kernel.encodeErrorArray_spec
