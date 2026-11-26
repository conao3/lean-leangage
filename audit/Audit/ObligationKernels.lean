import Leangage.Kernel

/-!
Small kernels for the tests of `#obligations`. `counter` adds two on `true` and reads on `false`,
which is read-only; its snapshot stays even.
-/

namespace Audit.ObligationKernels

def counter : Leangage.Kernel where
  Principal := Unit
  Snapshot := Nat
  Command := Bool
  WriteSet := Option Nat
  Reply := Nat
  Error := Unit
  init := 0
  tenant := fun _ => 0
  transition := fun _ s c => if c then .ok (some (s + 2), s + 2) else .ok (none, s)
  apply := fun s w => w.getD s
  readOnly := fun c => !c

def Even (s : Nat) : Prop := s % 2 = 0

end Audit.ObligationKernels
