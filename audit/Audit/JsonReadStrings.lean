import Assay
import Audit.JsonReadGen

/-!
Breaks the functions of the JSON reader that read a string and `true`, `false` and `null`, and
runs the theorems on each broken version, as `Audit.JsonRead` does for the rest of the loop.
-/

open Plausible Leangage.Json Leangage.Json.Read

set_option assay.samples 40 in
#assay Leangage.Json.Read.stepStr Leangage.Json.Read.stepEsc Leangage.Json.Read.stepHex
    Leangage.Json.Read.endHex Leangage.Json.Read.hexVal Leangage.Json.Read.pushUtf8
    Leangage.Json.Read.stepLit
  using Leangage.Json.Read.read_spaced Leangage.Json.Read.run_escape
    Leangage.Json.Read.run_escapeByte Leangage.Json.Read.hexVal_spec
