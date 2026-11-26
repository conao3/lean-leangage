import Assay
import Audit.Except
import Audit.Token
import Leangage.Http.Proofs

/-!
Breaks the functions on requests and responses in small ways and runs the theorems on each broken
version. The build fails when a broken version satisfies every theorem.

The headers are `Bearer ` followed by a token of `Audit.Token`, accepted or nearly accepted, and
headers close to that: another scheme, another case, no space, two spaces, no token. `refuse`
is one constructor applied to its arguments, and leanassay makes no broken version of it.
-/

open Plausible Leangage.Http

def headerText : Gen String := do
  let tok ← tokenText
  Gen.elements
    [s!"Bearer {tok}", s!"Bearer {tok}", s!"Bearer {tok}", s!"bearer {tok}", s!"Basic {tok}", tok,
      s!"Bearer  {tok}", s!" Bearer {tok}", "Bearer", "Bearer ", ""]
    (by simp)

instance (priority := high) httpArbitraryString : Arbitrary String where
  arbitrary := Gen.frequency (pure "") [(3, headerText), (3, tokenText)]

instance (priority := high) httpSampleableString : SampleableExt String := SampleableExt.selfContained

#assay Leangage.Http.bearerToken
  using Leangage.Http.bearerToken_append Leangage.Http.bearerToken_eq_some_iff

#assay Leangage.Http.authenticate
  using Leangage.Http.authenticate_missing Leangage.Http.authenticate_other
    Leangage.Http.authenticate_bearer

#assay Leangage.Http.admit
  using Leangage.Http.admit_expired Leangage.Http.admit_text Leangage.Http.admit_not_text

#assay Leangage.Http.failed using Leangage.Http.failed_spec
