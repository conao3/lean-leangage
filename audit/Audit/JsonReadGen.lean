import Audit.Json
import Leangage.Json.Read.Proofs

/-!
The inputs of the audits of the JSON reader: those of `Audit.Json`, JSON values whose strings
hold quotes, backslashes, control bytes and bytes of UTF-8, and numbers up to 2^64 - 1; the space
before and after a value; and the bytes of the hexadecimal digits.
-/

open Plausible Leangage.Json Leangage.Json.Read

def spaces : Gen (List UInt8) := do
  let n := (← Gen.choose Nat 0 3 (Nat.zero_le _)).val
  (List.range n).mapM fun _ => Gen.elements [32, 9, 10, 13] (by decide)

instance (priority := high) readArbitraryUInt8 : Arbitrary UInt8 where
  arbitrary := Gen.frequency (pure 97)
    [(3, Gen.elements jsonBytes (by decide)),
     (2, Gen.elements [47, 48, 57, 58, 64, 65, 70, 71, 96, 97, 102, 103, 11, 14] (by decide)),
     (1, return (← Gen.choose Nat 0 255 (Nat.zero_le _)).val.toUInt8)]

instance (priority := high) readArbitraryBytes : Arbitrary (List UInt8) where
  arbitrary := Gen.frequency (pure []) [(1, jsonString), (3, spaces)]

instance (priority := high) readSampleableBytes : SampleableExt (List UInt8) :=
  SampleableExt.selfContained

instance (priority := high) readArbitraryString : Arbitrary String where
  arbitrary := Gen.frequency (pure "")
    [(1, jsonStr),
     (3, do
       let v ← (Arbitrary.arbitrary : Gen Value)
       return (String.fromUTF8? (ByteArray.mk v.print.toArray)).getD "[1, 2]")]

instance (priority := high) readSampleableString : SampleableExt String := SampleableExt.selfContained
