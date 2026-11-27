import Leangage.Sql.Sound

/-!
# Tenant isolation

Based on `TenantIsolation` and `tenant_isolation` in
`crates/h5i-app-core/proofs/H5iAppLib/Obligation.lean` of h5i (https://github.com/h5i-dev/h5i,
commit 515c7b9, Apache-2.0). Changed: the statement is about the generated `valid`, `compile` and
`select`; a tenant is an `Int64`, so h5i's hypothesis that it is not `NULL` is its type.
-/

namespace Leangage.Sql

/-- Tenants do not see each other, on the model of PostgreSQL, for every schema `valid` accepts:

- statements compiled for another tenant leave the tenant's rows (`view ts tv`) as they were;
- what a compiled `SELECT` for a tenant returns depends only on the tenant's rows: two databases
  that agree on them give the same rows, up to order. -/
def TenantIsolation : Prop :=
  (∀ (ts : List Tab) (tv tv' : Int64) (ss : List Stmt) (qs : List (Sql × List Val)) (db db' : PgDb),
    valid ts = true → tv' ≠ tv → Matches ts db → ss.mapM (compile ts tv') = some qs →
    runAll db qs = some db' → view ts tv db' = view ts tv db) ∧
  (∀ (ts : List Tab) (tv : Int64) (db₁ db₂ : PgDb) (t : Nat) (f : Option (Nat × Val)) (q : Sql)
      (ps : List Val) (R₁ R₂ : List (List Val)),
    valid ts = true → Matches ts db₁ → Matches ts db₂ → view ts tv db₁ = view ts tv db₂ →
    select ts tv t f = some (q, ps) → selected db₁ q ps = some R₁ → selected db₂ q ps = some R₂ →
    R₁.Perm R₂)

theorem tenant_isolation : TenantIsolation := by
  refine ⟨?_, ?_⟩
  · intro ts tv tv' ss qs db db' hv hne hm hq hr
    obtain ⟨db2, hr2, -, -, ho, -⟩ := compileAll_sound hv ss qs db hm hq
    rw [hr] at hr2
    cases hr2
    exact ho tv (Ne.symm hne)
  · intro ts tv db₁ db₂ t f q ps R₁ R₂ hv hm₁ hm₂ heq hc h₁ h₂
    obtain ⟨R₁', e₁, hs₁⟩ := select_sound hv hm₁ hc
    obtain ⟨R₂', e₂, hs₂⟩ := select_sound hv hm₂ hc
    rw [h₁] at e₁
    rw [h₂] at e₂
    cases e₁
    cases e₂
    have a := hs₁ R₁ (.refl _)
    have b := hs₂ R₂ (.refl _)
    rw [heq] at a
    exact (List.perm_ext_iff_of_nodup a.1 b.1).2 (fun row => (a.2 row).trans (b.2 row).symm)

end Leangage.Sql
