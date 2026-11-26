import Assay
import Audit.JsonReadGen

/-!
Breaks the JSON reader in small ways and runs the theorems on each broken version. The build
fails when a broken version satisfies every theorem while it changes what the reader returns on an
input of a theorem. `Audit.JsonReadStrings` and `Audit.JsonReadNumbers` do the same for the
functions of the loop that read a string and a number.

The theorems read what the writer printed, with space around it. A broken version that differs
from the reader only on other texts (a sign, a fraction or an exponent, an escape the writer does
not write, a text that is not JSON) is counted as behaving the same.
-/

open Plausible Leangage.Json Leangage.Json.Read

#assay Leangage.Json.Read.stepFrom Leangage.Json.Read.readString
  using Leangage.Json.Read.stepFrom_spec Leangage.Json.Read.readString_spec

set_option assay.samples 40 in
#assay Leangage.Json.Read.step Leangage.Json.Read.stepValue Leangage.Json.Read.stepFirst
    Leangage.Json.Read.stepKey Leangage.Json.Read.stepColon Leangage.Json.Read.startValue
    Leangage.Json.Read.afterValue Leangage.Json.Read.emit Leangage.Json.Read.clean
    Leangage.Json.Read.finish Leangage.Json.Read.read Leangage.Json.Read.isWs
  using Leangage.Json.Read.read_spaced Leangage.Json.Read.run_escape
    Leangage.Json.Read.clean_spec Leangage.Json.Read.isWs_spec
