import Audit.Obligations
import Audit.ObligationKernels

-- expect: Invariant Even: no theorem states `Leanharbor.Obligation.Invariant counter Even` with only the standard axioms

open Audit.ObligationKernels

theorem counter_read_only :
    Leanharbor.Obligation.ReadOnlySound counter (fun ws : Option Nat => ws.toList) := by
  intro a s c ws r hro ht
  cases c with
  | true => simp [counter] at hro
  | false =>
    simp only [counter] at ht
    cases ht
    rfl

theorem counter_even_from_init : Even counter.init := rfl

#obligations counter invariant Even
