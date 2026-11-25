import Leanharbor.Kernel

/-!
# Obligations: the statements the framework fixes

Based on `crates/h5i-app-core/proofs/H5iAppLib/Obligation.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the statements take a
`Leanharbor.Kernel`, whose functions are Lean definitions that are generated and run, so they
carry no `Result` of Aeneas; `ReadOnlySound` is `Kernel.ReadOnlySound`; `Invariant` is new and
states the hypotheses of `Kernel.Run.inv`.

Each `def` here is a statement about a kernel `k` that has the same form for every kernel. A
kernel's theorem must state exactly it: `#obligations` (in `audit/`) elaborates the statement for
`k` and requires a theorem whose type is definitionally equal to it. An argument the kernel
chooses (the write list of `ReadOnlySound`) is filled in from the theorem and printed.
-/

namespace Leanharbor.Obligation

open Kernel

/-- A command marked read-only returns no writes: whenever `readOnly c` is `true` and
`transition` accepts `c`, `writes` of the write set is empty. -/
def ReadOnlySound {α : Type} (k : Kernel) (writes : k.WriteSet → List α) : Prop :=
  k.ReadOnlySound writes

/-- `I` holds for `init` and is kept by every accepted command of every principal. -/
def Invariant (k : Kernel) (I : k.Snapshot → Prop) : Prop :=
  I k.init ∧ ∀ a s c ws r, I s → k.transition a s c = .ok (ws, r) → I (k.apply s ws)

/-- An invariant holds in every snapshot a tenant can reach. -/
theorem Invariant.run {k : Kernel} {I : k.Snapshot → Prop} (h : Invariant k I) {s : k.Snapshot}
    (hs : Run k s) : I s :=
  Run.inv I h.1 h.2 hs

end Leanharbor.Obligation
