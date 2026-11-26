/-!
# The kernel contract

A kernel decides, for one tenant, what a command does: `transition` returns the writes and the
reply or refuses, and `apply` says what the writes mean. Both are pure and total. The engine (the
trusted shell around it) loads the tenant's snapshot, calls `transition`, stores the writes and
answers with the reply.
-/

namespace Leangage

structure Kernel where
  Principal : Type
  Snapshot : Type
  Command : Type
  WriteSet : Type
  Reply : Type
  Error : Type
  /-- A tenant's snapshot before its first command. -/
  init : Snapshot
  /-- The only tenant the principal may read or write. -/
  tenant : Principal → UInt64
  transition : Principal → Snapshot → Command → Except Error (WriteSet × Reply)
  apply : Snapshot → WriteSet → Snapshot
  /-- Commands the engine may run without a write transaction. -/
  readOnly : Command → Bool

namespace Kernel

/-- A command marked read-only returns no writes. An engine relies on this to run it on a
read-only transaction. -/
def ReadOnlySound {α : Type} (k : Kernel) (writes : k.WriteSet → List α) : Prop :=
  ∀ a s c ws r, k.readOnly c = true → k.transition a s c = .ok (ws, r) → writes ws = []

/-- The snapshots a tenant can reach from `init` by accepted commands of any principals. -/
inductive Run (k : Kernel) : k.Snapshot → Prop
  | init : Run k k.init
  | step {s a c ws r} : Run k s → k.transition a s c = .ok (ws, r) → Run k (k.apply s ws)

/-- A property that holds initially and is kept by every accepted command holds in every
reachable snapshot. -/
theorem Run.inv {k : Kernel} {s : k.Snapshot} (I : k.Snapshot → Prop) (h0 : I k.init)
    (hs : ∀ a s c ws r, I s → k.transition a s c = .ok (ws, r) → I (k.apply s ws))
    (h : Run k s) : I s := by
  induction h with
  | init => exact h0
  | step _ ht ih => exact hs _ _ _ _ _ ih ht

end Kernel

end Leangage
