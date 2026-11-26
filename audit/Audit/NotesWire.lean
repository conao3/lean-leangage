import Assay
import Audit.Except
import Notes.Wire.Proofs

/-!
Breaks the notes' functions on the wire in small ways and runs the theorems on each broken
version. The build fails when a broken version satisfies every theorem.

The members are the fields of a command, in their order, reversed and rotated, and the same with
a member removed, added, repeated or holding another value. The bodies are the tokens of the
spellings of the commands and of the replies, and lists of tokens close to one. The numbers and the texts are few, so that two commands are
often the same.
-/

open Plausible Notes.Kernel Notes.Wire Leangage Leangage.Json.Lexemes

instance (priority := high) notesWireArbitraryUInt64 : Arbitrary UInt64 where
  arbitrary := Gen.elements [0, 1, 2, 9, 10, 99, 100, 18446744073709551615] (by decide)

instance (priority := high) notesWireSampleableUInt64 : SampleableExt UInt64 := SampleableExt.selfContained

def noteText : Gen String :=
  Gen.elements ["", "a", "draft", "say \"hi\"", "back\\slash", "line\nbreak", "é", "\x01", ", shared: true }"]
    (by decide)

def commandGen : Gen Command := do
  let n ← (Arbitrary.arbitrary : Gen UInt64)
  let b ← Gen.chooseAny Bool
  match (← Gen.choose Nat 0 7 (Nat.zero_le _)).val with
  | 0 => return .addMember n b
  | 1 => return .removeMember n
  | 2 | 3 => return .putNote n (← noteText) b
  | 4 => return .deleteNote n
  | 5 => return .readNote n
  | 6 => return .listNotes
  | _ => return .listMembers

deriving instance Repr for Notes.Wire.Call

instance (priority := high) notesWireArbitraryCommand : Arbitrary Command where
  arbitrary := commandGen

instance : Shrinkable Command := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableCommand : SampleableExt Command := SampleableExt.selfContained

def otherScalar : Gen Scalar :=
  Gen.elements [.null, .bool true, .number, .num 7, .str "list_notes", .str "é", .str "put"] (by decide)

def membersGen : Gen (List (String × Scalar)) := do
  let ms := fields (← commandGen)
  let other ← otherScalar
  let i := (← Gen.choose Nat 0 3 (Nat.zero_le _)).val
  Gen.elements
    [ms, ms, ms.reverse, ms.drop 1 ++ ms.take 1, ms.drop 2 ++ ms.take 2, ms.drop 1, ms.take 1, ms.take 2,
      ms ++ [("x", other)], ("x", other) :: ms, ms ++ ms.take 1, ms.take 1 ++ ms,
      (ms.take i ++ ms.drop (i + 1)), ms.set i (((ms.getD i ("", .null)).1), other),
      ms.set i ("CMD", (ms.getD i ("", .null)).2), []]
    (by simp)

instance (priority := high) notesWireArbitraryMembers : Arbitrary (List (String × Scalar)) where
  arbitrary := membersGen

instance (priority := high) notesWireShrinkableMembers : Shrinkable (List (String × Scalar)) :=
  ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableMembers : SampleableExt (List (String × Scalar)) :=
  SampleableExt.selfContained

def bodyLexemes : Gen (List Lexeme) := do
  let ls := lexemesOf (← commandGen)
  let n ← (Arbitrary.arbitrary : Gen UInt64)
  let b ← Gen.chooseAny Bool
  let text ← noteText
  let note := noteLexemes ⟨n, n, b, text⟩
  let member : List Lexeme :=
    [.objOpen, .key "admin", Lexeme.bool b, .key "user", .number (toString n.toNat), .objClose]
  Gen.elements
    [ls, ls, ls, ls.drop 1, ls.dropLast, ls ++ ls, .arrOpen :: ls, [], [.objOpen, .objClose],
      [.objOpen, .key "cmd", .str "list_notes", .key "cmd", .str "list_notes", .objClose],
      [.objOpen, .key "cmd", .str "read_note", .key "id", .number "6.0", .objClose],
      [.objOpen, .key "id", .number "1", .key "cmd", .str "delete_note", .objClose],
      [.objOpen, .key "done", .bool true, .objClose], [.objOpen, .key "done", .bool false, .objClose],
      [.objOpen, .key "note"] ++ note ++ [.objClose],
      [.objOpen, .key "notes", .arrOpen] ++ note ++ note ++ [.arrClose, .objClose],
      [.objOpen, .key "notes", .arrOpen, .arrClose, .objClose],
      [.objOpen, .key "members", .arrOpen] ++ member ++ [.arrClose, .objClose],
      [.objOpen, .key "members", .arrOpen] ++ note ++ [.arrClose, .objClose]]
    (by simp)

instance (priority := high) notesWireArbitraryLexemes : Arbitrary (List Lexeme) where
  arbitrary := bodyLexemes

instance (priority := high) notesWireShrinkableLexemes : Shrinkable (List Lexeme) := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableLexemes : SampleableExt (List Lexeme) :=
  SampleableExt.selfContained

instance (priority := high) notesWireArbitraryTokens : Arbitrary Tokens where
  arbitrary := do
    let tokens := encode (← bodyLexemes)
    Gen.elements
      [tokens, tokens, tokens, tokens, ⟨tokens.kinds, tokens.texts.drop 1⟩, ⟨tokens.kinds ++ "s", tokens.texts⟩,
        ⟨tokens.kinds, tokens.texts ++ ["x"]⟩]
      (by simp)

instance : Shrinkable Tokens := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableTokens : SampleableExt Tokens := SampleableExt.selfContained

instance (priority := high) notesWireArbitraryGuarded : Arbitrary (Authz.Guarded Error) where
  arbitrary := Gen.elements [.denied, .app .notFound, .app .badText] (by decide)

instance : Shrinkable (Authz.Guarded Error) := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableGuarded : SampleableExt (Authz.Guarded Error) :=
  SampleableExt.selfContained

deriving instance DecidableEq for Principal, Command, Call

#assay Notes.Wire.decodeMembers
  using Notes.Wire.decodeMembers_fields Notes.Wire.decodeMembers_ok_iff
    Notes.Wire.decodeMembers_missingCmd_iff

#assay Notes.Wire.decode using Notes.Wire.decode_encode Notes.Wire.decode_spec

#assay Notes.Wire.refusalMessage using Notes.Wire.refusalMessage_spec

#assay Notes.Wire.request
  using Notes.Wire.request_expired Notes.Wire.request_json Notes.Wire.request_not_json
    Notes.Wire.request_actor_run

#assay Notes.Wire.noteToks Notes.Wire.memberToks Notes.Wire.replyToks Notes.Wire.encodeReply
    Notes.Wire.respond
  using Notes.Wire.respond_ok Notes.Wire.respond_error Notes.Wire.encodeReply_spec

#assay Notes.Wire.noteOf Notes.Wire.notesOf Notes.Wire.membersOf Notes.Wire.replyOf
  using Notes.Wire.replyOf_lexemes Notes.Wire.noteOf_note

#assay Notes.Wire.decodeReply using Notes.Wire.decodeReply_encode Notes.Wire.decodeReply_spec Notes.Wire.decodeReply_none

#assay Notes.Wire.pushFlag Notes.Wire.fingerprint
  using Notes.Wire.fingerprint_spec Notes.Wire.fingerprint_injective

#assay Notes.Wire.scope using Notes.Wire.scope_spec Notes.Wire.scope_injective
