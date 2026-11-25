import Audit.Obligations
import Audit.ObligationKernels

-- expect: Invariant _: the statement `Leanharbor.Obligation.Invariant counter _` has 1 holes, and it may have 0

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

theorem counter_true : Leanharbor.Obligation.Invariant counter (fun _ => True) :=
  ⟨trivial, fun _ _ _ _ _ _ _ => trivial⟩

#obligations counter invariant _
