import Assay
import Audit.JsonReadGen

/-!
Breaks the functions of the JSON reader that read a number, and runs the theorems on each broken
version, as `Audit.JsonRead` does for the rest of the loop.
-/

open Plausible Leangage.Json Leangage.Json.Read

set_option assay.samples 40 in
#assay Leangage.Json.Read.stepZero Leangage.Json.Read.stepInt Leangage.Json.Read.stepDigits
    Leangage.Json.Read.intItem Leangage.Json.Read.isDigit
  using Leangage.Json.Read.read_spaced Leangage.Json.Read.run_decimal_pos
    Leangage.Json.Read.read_fraction Leangage.Json.Read.isDigit_spec
