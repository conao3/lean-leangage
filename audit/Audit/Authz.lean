import Assay
import Audit.Except
import Leanharbor.AuthzProofs

open Plausible

instance : SampleableExt (Leanharbor.Authz.Policy Int Int Int Int) where
  proxy := SampleableExt.proxy (Int → Int → Int → Bool) × SampleableExt.proxy (Int → Int → Int → Bool) ×
    SampleableExt.proxy (Int → Int → Bool)
  interp := fun (p, v, s) =>
    { permits := SampleableExt.interp p, visible := SampleableExt.interp v,
      stored := SampleableExt.interp s }

#assay Leanharbor.Authz.guard Leanharbor.Authz.guardViewed Leanharbor.Authz.checkWrites
    Leanharbor.Authz.checkWritesFrom Leanharbor.Authz.checkReads Leanharbor.Authz.shown
  using Leanharbor.Authz.guard_eq Leanharbor.Authz.guard_viewed_eq
    Leanharbor.Authz.checkWritesFrom_iff Leanharbor.Authz.checkReads_iff Leanharbor.Authz.shown_iff
