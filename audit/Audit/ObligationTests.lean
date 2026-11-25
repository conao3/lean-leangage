import Audit.Obligations
import Audit.ObligationKernels

/-!
The check passes for `counter` with the theorems below, one of them stated without the names of
`Leanharbor.Obligation`. The files in `audit/fail/` are `counter` without them, and `make check`
requires each to fail with its message.
-/

namespace Audit.ObligationTests

open Audit.ObligationKernels

theorem counter_read_only :
    ∀ a s c ws r, counter.readOnly c = true → counter.transition a s c = .ok (ws, r) →
      Option.toList ws = ([] : List Nat) := by
  intro a s c ws r hro ht
  cases c with
  | true => simp [counter] at hro
  | false =>
    simp only [counter] at ht
    cases ht
    rfl

theorem counter_even : Leanharbor.Obligation.Invariant counter Even := by
  refine ⟨rfl, fun a s c ws r hs ht => ?_⟩
  cases c with
  | true =>
    simp only [counter, ite_true] at ht
    cases ht
    simp only [counter, Even, Option.getD] at hs ⊢
    omega
  | false =>
    simp only [counter] at ht
    cases ht
    exact hs

/--
info: ReadOnlySound: Audit.ObligationTests.counter_read_only states Leanharbor.Obligation.ReadOnlySound counter Option.toList
Invariant Even: Audit.ObligationTests.counter_even states Leanharbor.Obligation.Invariant counter Even
-/
#guard_msgs in
#obligations counter invariant Even

end Audit.ObligationTests
