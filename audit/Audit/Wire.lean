import Assay
import Audit.Except
import Calculator.Wire.Proofs

/-!
Breaks the calculator's functions on the wire in small ways and runs the theorems on each broken
version. The build fails when a broken version satisfies every theorem.

The members are the fields of a command, in their order, reversed and rotated, and the same with
a member removed, added, repeated or holding another value. The bodies are the tokens of the
spellings of the commands and lists of tokens close to one. The numbers are few, so that two commands are often the same.
-/

open Plausible Calculator.Kernel Calculator.Wire Leangage Leangage.Json.Lexemes

instance (priority := high) wireArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.elements [0, 1, 2, 9, 10, 99, 100, 18446744073709551615] (by decide)

instance (priority := high) wireSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

def opGen : Gen Op := Gen.elements [.add, .sub, .mul, .div] (by decide)

def commandGen : Gen Command := do
  let n ← (Arbitrary.arbitrary : Gen UInt64)
  match (← Gen.choose Nat 0 2 (Nat.zero_le _)).val with
  | 0 => return .set n
  | 1 => return .apply (← opGen) n
  | _ => return .get

deriving instance Repr for Calculator.Kernel.Principal, Calculator.Kernel.Command

instance (priority := high) wireArbitraryCommand : Arbitrary Command where
  arbitrary := commandGen

instance : Shrinkable Command := ⟨fun _ => []⟩

instance (priority := high) wireSampleableCommand : SampleableExt Command := SampleableExt.selfContained

def otherScalar : Gen Scalar :=
  Gen.elements [.null, .bool true, .number, .num 7, .str "get", .str "pow"] (by decide)

def membersGen : Gen (List (String × Scalar)) := do
  let ms := fields (← commandGen)
  let other ← otherScalar
  let i := (← Gen.choose Nat 0 2 (Nat.zero_le _)).val
  Gen.elements
    [ms, ms, ms.reverse, ms.drop 1 ++ ms.take 1, ms.drop 2 ++ ms.take 2, ms.drop 1, ms.take 1, ms.take 2,
      ms ++ [("x", other)], ("x", other) :: ms, ms ++ ms.take 1, ms.take 1 ++ ms,
      (ms.take i ++ ms.drop (i + 1)), ms.set i (((ms.getD i ("", .null)).1), other),
      ms.set i ("CMD", (ms.getD i ("", .null)).2), []]
    (by simp)

instance (priority := high) wireArbitraryMembers : Arbitrary (List (String × Scalar)) where
  arbitrary := membersGen

instance (priority := high) wireShrinkableMembers : Shrinkable (List (String × Scalar)) :=
  ⟨fun _ => []⟩

instance (priority := high) wireSampleableMembers : SampleableExt (List (String × Scalar)) :=
  SampleableExt.selfContained

instance (priority := high) wireArbitraryNames : Arbitrary String where
  arbitrary := Gen.elements ["add", "sub", "mul", "div", "pow", "", "ad", "Add", "add "] (by decide)

instance (priority := high) wireSampleableNames : SampleableExt String := SampleableExt.selfContained

def bodyLexemes : Gen (List Lexeme) := do
  let ls := lexemesOf (← commandGen)
  Gen.elements
    [ls, ls, ls, ls.drop 1, ls.dropLast, ls ++ ls, .arrOpen :: ls, [], [.objOpen, .objClose],
      [.objOpen, .key "cmd", .str "get", .key "cmd", .str "get", .objClose],
      [.objOpen, .key "cmd", .str "set", .key "value", .number "6.0", .objClose],
      [.objOpen, .key "value", .number "1", .key "cmd", .str "set", .objClose],
      [.objOpen, .key "cmd", .str "apply", .key "arg", .number "-1", .key "op", .str "add", .objClose],
      [.number "7"]]
    (by simp)

instance (priority := high) wireArbitraryLexemes : Arbitrary (List Lexeme) where
  arbitrary := bodyLexemes

instance (priority := high) wireShrinkableLexemes : Shrinkable (List Lexeme) := ⟨fun _ => []⟩

instance (priority := high) wireSampleableLexemes : SampleableExt (List Lexeme) :=
  SampleableExt.selfContained

deriving instance DecidableEq for Principal, Command, Call

#assay Calculator.Wire.decodeMembers
  using Calculator.Wire.decodeMembers_fields Calculator.Wire.decodeMembers_ok_iff
    Calculator.Wire.decodeMembers_missingCmd_iff Calculator.Wire.decodeMembers_badValue_iff
    Calculator.Wire.decodeMembers_badArg_iff

#assay Calculator.Wire.decodeObject using Calculator.Wire.decodeObject_spec

#assay Calculator.Wire.spelled Calculator.Wire.decode
  using Calculator.Wire.spelled_lexemesOf Calculator.Wire.decode_eq Calculator.Wire.decode_encode

#assay Calculator.Wire.opNamed using Calculator.Wire.opNamed_spec

#assay Calculator.Wire.refusalMessage using Calculator.Wire.refusalMessage_spec

#assay Calculator.Wire.request
  using Calculator.Wire.request_expired Calculator.Wire.request_json
    Calculator.Wire.request_not_json Calculator.Wire.request_actor_run

#assay Calculator.Wire.respond using Calculator.Wire.respond_ok Calculator.Wire.respond_error

#assay Calculator.Wire.opFingerprint Calculator.Wire.fingerprint
  using Calculator.Wire.fingerprint_spec Calculator.Wire.fingerprint_injective

#assay Calculator.Wire.scope using Calculator.Wire.scope_spec Calculator.Wire.scope_injective
