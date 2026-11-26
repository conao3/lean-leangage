import Assay
import Audit.Except
import Notes.Wire.Proofs

/-!
Breaks the notes' functions on the wire in small ways and runs the theorems on each broken
version. The build fails when a broken version satisfies every theorem.

The members are the fields of a command, in their order, reversed and rotated, and the same with
a member removed, added, repeated or holding another value. The bodies are the spellings of the
commands and texts close to one. The numbers and the texts are few, so that two commands are
often the same.
-/

open Plausible Notes.Kernel Notes.Wire Leangage Leangage.Json.Read

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

def otherItem : Gen Item :=
  Gen.elements
    [.null, .bool true, .number, .num 7, .str [108, 105, 115, 116, 95, 110, 111, 116, 101, 115], .str [255],
      .str [112, 117, 116], .arrOpen, .objClose] (by decide)

instance (priority := high) notesWireArbitraryItem : Arbitrary Item where
  arbitrary := Gen.elements
    [.null, .bool true, .bool false, .num 7, .number, .str [103], .key [103], .arrOpen, .arrClose,
      .objOpen, .objClose] (by decide)

instance : Shrinkable Item := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableItem : SampleableExt Item := SampleableExt.selfContained

def membersGen : Gen (List (List UInt8 × Item)) := do
  let ms := fields (← commandGen)
  let other ← otherItem
  let i := (← Gen.choose Nat 0 3 (Nat.zero_le _)).val
  Gen.elements
    [ms, ms, ms.reverse, ms.drop 1 ++ ms.take 1, ms.drop 2 ++ ms.take 2, ms.drop 1, ms.take 1, ms.take 2,
      ms ++ [([120], other)], ([120], other) :: ms, ms ++ ms.take 1, ms.take 1 ++ ms,
      (ms.take i ++ ms.drop (i + 1)), ms.set i (((ms.getD i ([], .null)).1), other),
      ms.set i ([67, 77, 68], (ms.getD i ([], .null)).2), []]
    (by simp)

instance (priority := high) notesWireArbitraryMembers : Arbitrary (List (List UInt8 × Item)) where
  arbitrary := membersGen

instance (priority := high) notesWireShrinkableMembers : Shrinkable (List (List UInt8 × Item)) :=
  ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableMembers : SampleableExt (List (List UInt8 × Item)) :=
  SampleableExt.selfContained

instance (priority := high) notesWireArbitraryItems : Arbitrary (List Item) where
  arbitrary := do
    let items := objectItems (← membersGen)
    Gen.elements [items, items, items, items.drop 1, items.dropLast, .arrOpen :: items, items ++ [.null], []]
      (by simp)

instance (priority := high) notesWireShrinkableItems : Shrinkable (List Item) := ⟨fun _ => []⟩

instance (priority := high) notesWireSampleableItems : SampleableExt (List Item) := SampleableExt.selfContained

def bodyText : Gen String := do
  let c ← commandGen
  let text := (String.fromUTF8? (ByteArray.mk (encodeCommand c).print.toArray)).getD ""
  Gen.elements
    [text, text, text, " " ++ text ++ "\n", text ++ " x", text.dropEnd 1 |>.toString, "{}", "[]", "",
      "{\"cmd\":\"list_notes\",\"cmd\":\"list_notes\"}", "{\"cmd\":\"read_note\",\"id\":6.0}",
      "{\"id\":1,\"cmd\":\"delete_note\"}", "{\"cmd\":\"list_notes\",\"id\":1}", "7", "{", "draft",
      "say \"hi\""]
    (by simp)

instance (priority := high) notesWireArbitraryString : Arbitrary String where
  arbitrary := bodyText

instance (priority := high) notesWireSampleableString : SampleableExt String := SampleableExt.selfContained

deriving instance DecidableEq for Principal, Command, Call

#assay Notes.Wire.textOf using Notes.Wire.textOf_bytesOf

#assay Notes.Wire.decodeMembers
  using Notes.Wire.decodeMembers_fields Notes.Wire.decodeMembers_ok_iff
    Notes.Wire.decodeMembers_missingCmd_iff

#assay Notes.Wire.scalar Notes.Wire.members Notes.Wire.decodeItems
  using Notes.Wire.decodeItems_object Notes.Wire.decodeItems_fields Notes.Wire.scalar_spec

#assay Notes.Wire.decode using Notes.Wire.decode_notJson_iff

#assay Notes.Wire.refusalMessage using Notes.Wire.refusalMessage_spec

#assay Notes.Wire.request
  using Notes.Wire.request_expired Notes.Wire.request_text Notes.Wire.request_not_text
    Notes.Wire.request_actor_run

#assay Notes.Wire.noteToks Notes.Wire.memberToks Notes.Wire.replyToks Notes.Wire.encodeReply
    Notes.Wire.respond
  using Notes.Wire.respond_ok Notes.Wire.respond_error Notes.Wire.encodeReply_spec

#assay Notes.Wire.noteOf Notes.Wire.notesItems Notes.Wire.membersItems Notes.Wire.decodeReplyItems
  using Notes.Wire.decodeReplyItems_value Notes.Wire.noteOf_note

#assay Notes.Wire.pushFlag Notes.Wire.fingerprint
  using Notes.Wire.fingerprint_spec Notes.Wire.fingerprint_injective

#assay Notes.Wire.scope using Notes.Wire.scope_spec Notes.Wire.scope_injective
