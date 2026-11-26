import Audit.Obligations
import Audit.ObligationKernels

-- expect: ReadOnlySound: no theorem states `Leangage.Obligation.ReadOnlySound counter _` with only the standard axioms

open Audit.ObligationKernels

theorem counter_read_only_from_zero :
    ∀ a s c ws r, counter.readOnly c = true → s = (0 : Nat) → counter.transition a s c = .ok (ws, r) →
      Option.toList ws = ([] : List Nat) := by
  intro a s c ws r hro _ ht
  cases c with
  | true => simp [counter] at hro
  | false =>
    simp only [counter] at ht
    cases ht
    rfl

#obligations counter
