import Assay
import Audit.Except
import Leangage.AuthzProofs

open Plausible

instance : SampleableExt (Leangage.Authz.Policy Int Int Int Int) where
  proxy := SampleableExt.proxy (Int → Int → Int → Bool) × SampleableExt.proxy (Int → Int → Int → Bool) ×
    SampleableExt.proxy (Int → Int → Bool)
  interp := fun (p, v, s) =>
    { permits := SampleableExt.interp p, visible := SampleableExt.interp v,
      stored := SampleableExt.interp s }

#assay Leangage.Authz.guard Leangage.Authz.guardViewed Leangage.Authz.checkWrites
    Leangage.Authz.checkWritesFrom Leangage.Authz.checkReads Leangage.Authz.shown
  using Leangage.Authz.guard_eq Leangage.Authz.guard_viewed_eq
    Leangage.Authz.checkWritesFrom_iff Leangage.Authz.checkReads_iff Leangage.Authz.shown_iff
