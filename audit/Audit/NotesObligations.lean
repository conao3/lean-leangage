import Audit.Obligations
import Notes.Proofs

/-!
Checks that the notes kernel's theorems state the obligations of `Leangage.Obligation`, with the
invariant `Keyed`.
-/

#obligations Notes.Kernel.kernel invariant Notes.Kernel.Keyed
