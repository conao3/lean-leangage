import Assay
import Leanharbor.Json.Proofs

/-!
Breaks the JSON writer in small ways and runs the theorems on each broken version. The build fails
when a broken version satisfies every theorem.

The bytes are mostly those the writer treats apart: the quote, the backslash, control bytes and
the bytes around 0x20, and bytes of UTF-8. The token lists are random lists, which need not be a
JSON document, and the tokens of random JSON values, so that `write_spec` and `write_value` run on
both.
-/

open Plausible Leanharbor.Json

deriving instance Repr for Leanharbor.Json.Value

def jsonBytes : List UInt8 :=
  [0, 1, 8, 9, 10, 12, 13, 15, 16, 26, 31, 32, 33, 34, 47, 58, 91, 92, 93, 117, 123, 125, 127, 128, 169,
    195, 255]

instance (priority := high) jsonArbitraryUInt8 : Arbitrary UInt8 where
  arbitrary := Gen.frequency (pure 97)
    [(4, Gen.elements jsonBytes (by decide)),
     (1, return (← Gen.choose Nat 0 255 (Nat.zero_le _)).val.toUInt8)]

instance (priority := high) jsonArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.frequency (pure 0)
    [(3, return (← Gen.choose Nat 0 12 (Nat.zero_le _)).val.toUInt64),
     (2, return (← Gen.choose Nat 0 100000 (Nat.zero_le _)).val.toUInt64),
     (1, Gen.elements [9, 10, 99, 100, 18446744073709551615] (by decide))]

def jsonString : Gen (List UInt8) := do
  let n := (← Gen.choose Nat 0 6 (Nat.zero_le _)).val
  (List.range n).mapM fun _ => (Arbitrary.arbitrary : Gen UInt8)

instance (priority := high) jsonArbitraryBytes : Arbitrary (List UInt8) where
  arbitrary := jsonString

def jsonTok : Gen Tok := do
  match (← Gen.choose Nat 0 9 (Nat.zero_le _)).val with
  | 0 => return .null
  | 1 => return .bool (← Arbitrary.arbitrary)
  | 2 => return .num (← Arbitrary.arbitrary)
  | 3 => return .str (← jsonString)
  | 4 => return .key (← jsonString)
  | 5 => return .arrOpen
  | 6 => return .arrClose
  | 7 => return .objOpen
  | 8 => return .objClose
  | _ => return .str (← jsonString)

instance (priority := high) jsonArbitraryTok : Arbitrary Tok where
  arbitrary := jsonTok

def jsonValue : Nat → Gen Value
  | 0 => do
    match (← Gen.choose Nat 0 3 (Nat.zero_le _)).val with
    | 0 => return .null
    | 1 => return .bool (← Arbitrary.arbitrary)
    | 2 => return .num (← Arbitrary.arbitrary)
    | _ => return .str (← jsonString)
  | fuel + 1 => do
    let n := (← Gen.choose Nat 0 3 (Nat.zero_le _)).val
    match (← Gen.choose Nat 0 2 (Nat.zero_le _)).val with
    | 0 => return .arr (← (List.range n).mapM fun _ => jsonValue fuel)
    | 1 => return .obj (← (List.range n).mapM fun _ => return (← jsonString, ← jsonValue fuel))
    | _ => jsonValue 0

instance (priority := high) jsonArbitraryValue : Arbitrary Value where
  arbitrary := do jsonValue (← Gen.choose Nat 0 3 (Nat.zero_le _)).val

instance (priority := high) jsonArbitraryToks : Arbitrary (List Tok) where
  arbitrary := Gen.frequency (pure [])
    [(1, do
       let n := (← Gen.choose Nat 0 8 (Nat.zero_le _)).val
       (List.range n).mapM fun _ => jsonTok),
     (1, return (← (Arbitrary.arbitrary : Gen Value)).toks)]

def jsonChars : List Char :=
  ['\x00', '\x01', '\x08', '\t', '\n', '\x0c', '\r', '\x1f', ' ', '"', '\\', '/', 'a', 'u', '\x7f', 'é',
    '€', '😀']

def jsonStr : Gen String := do
  let n := (← Gen.choose Nat 0 6 (Nat.zero_le _)).val
  return String.ofList (← (List.range n).mapM fun _ => Gen.elements jsonChars (by decide))

instance (priority := high) jsonArbitraryString : Arbitrary String where
  arbitrary := jsonStr

def jsonStrTok : Gen StrTok := do
  match (← Gen.choose Nat 0 9 (Nat.zero_le _)).val with
  | 0 => return .null
  | 1 => return .bool (← Arbitrary.arbitrary)
  | 2 => return .num (← Arbitrary.arbitrary)
  | 3 => return .str (← jsonStr)
  | 4 => return .key (← jsonStr)
  | 5 => return .arrOpen
  | 6 => return .arrClose
  | 7 => return .objOpen
  | 8 => return .objClose
  | _ => return .str (← jsonStr)

instance (priority := high) jsonArbitraryStrTok : Arbitrary StrTok where
  arbitrary := jsonStrTok

instance (priority := high) jsonArbitraryStrToks : Arbitrary (List StrTok) where
  arbitrary := do
    let n := (← Gen.choose Nat 0 8 (Nat.zero_le _)).val
    (List.range n).mapM fun _ => jsonStrTok

instance (priority := high) jsonArbitraryArray : Arbitrary (Array UInt8) where
  arbitrary := return (← jsonString).toArray

instance (priority := high) jsonArbitraryNat : Arbitrary Nat where
  arbitrary := Gen.frequency (pure 0)
    [(3, return (← Gen.choose Nat 0 12 (Nat.zero_le _)).val),
     (2, return (← Gen.choose Nat 0 100000 (Nat.zero_le _)).val),
     (1, Gen.elements [9, 10, 99, 100, 18446744073709551615, 18446744073709551616] (by decide))]

instance : Shrinkable Tok := ⟨fun _ => []⟩

instance : Shrinkable StrTok := ⟨fun _ => []⟩

instance (priority := high) jsonShrinkableStrToks : Shrinkable (List StrTok) := ⟨fun _ => []⟩

instance : Shrinkable Value := ⟨fun _ => []⟩

instance (priority := high) jsonShrinkableToks : Shrinkable (List Tok) := ⟨fun _ => []⟩

instance (priority := high) jsonSampleableUInt8 : SampleableExt UInt8 := SampleableExt.selfContained

instance (priority := high) jsonSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

instance (priority := high) jsonSampleableBytes : SampleableExt (List UInt8) := SampleableExt.selfContained

instance (priority := high) jsonSampleableTok : SampleableExt Tok := SampleableExt.selfContained

instance (priority := high) jsonSampleableToks : SampleableExt (List Tok) := SampleableExt.selfContained

instance (priority := high) jsonSampleableValue : SampleableExt Value := SampleableExt.selfContained

instance (priority := high) jsonSampleableString : SampleableExt String := SampleableExt.selfContained

instance (priority := high) jsonSampleableStrTok : SampleableExt StrTok := SampleableExt.selfContained

instance (priority := high) jsonSampleableStrToks : SampleableExt (List StrTok) :=
  SampleableExt.selfContained

instance (priority := high) jsonSampleableArray : SampleableExt (Array UInt8) :=
  SampleableExt.selfContained

instance (priority := high) jsonSampleableNat : SampleableExt Nat := SampleableExt.selfContained

#assay Leanharbor.Json.escapeByte Leanharbor.Json.escape
  using Leanharbor.Json.escapeByte_spec Leanharbor.Json.escape_spec Leanharbor.Json.lex_escape
    Leanharbor.Json.escape_no_control

#assay Leanharbor.Json.tokBytes using Leanharbor.Json.tokBytes_spec

#assay Leanharbor.Json.isClose using Leanharbor.Json.isClose_spec

#assay Leanharbor.Json.endsValue using Leanharbor.Json.endsValue_spec

#assay Leanharbor.Json.writeFrom Leanharbor.Json.write
  using Leanharbor.Json.writeFrom_spec Leanharbor.Json.write_spec Leanharbor.Json.write_value

#assay Leanharbor.Json.pushEscapedByte using Leanharbor.Json.pushEscapedByte_spec

#assay Leanharbor.Json.pushEscaped using Leanharbor.Json.pushEscaped_spec

#assay Leanharbor.Json.pushDecimal using Leanharbor.Json.pushDecimal_spec

#assay Leanharbor.Json.pushTok using Leanharbor.Json.pushTok_spec

#assay Leanharbor.Json.StrTok.isClose using Leanharbor.Json.StrTok.isClose_toTok

#assay Leanharbor.Json.StrTok.endsValue using Leanharbor.Json.StrTok.endsValue_toTok

#assay Leanharbor.Json.writeArrayFrom Leanharbor.Json.writeArray
  using Leanharbor.Json.writeArrayFrom_spec Leanharbor.Json.writeArray_spec
