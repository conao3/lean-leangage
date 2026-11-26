import Notes.Kernel
import Leangage.Http
import Leangage.Json.Read

/-!
# The notes on the wire

What the notes' server does with a request once its token's tag is checked, and with the engine's
result. `request` reads the body into the command and the principal the engine runs, or gives the
answer to a request the engine does not see. `respond` gives the answer to an accepted and to a
refused command. `fingerprint` is the bytes that identify a command under an idempotency key, and
`scope` the name that separates the keys of the users of an organization. `encodeReply` is the
bytes of a reply, which an engine also stores under an idempotency key, and `decodeReply` reads
them back.

A command is a JSON object: `{"cmd":"add_member","user":2,"admin":false}`,
`{"cmd":"remove_member","user":2}`, `{"cmd":"put_note","id":7,"body":"text","shared":true}`,
`{"cmd":"delete_note","id":7}`, `{"cmd":"read_note","id":7}`, `{"cmd":"list_notes"}` and
`{"cmd":"list_members"}`. Its members may come in any order; an object with another member, or
with a member twice, is not a command.

A reply is `{"done":true}`, `{"note":<note>}`, `{"notes":[<note>,…]}` or
`{"members":[<member>,…]}`, with a note `{"body":"text","id":7,"owner":1,"shared":true}` and a
member `{"admin":false,"user":2}`.
-/

namespace Notes.Wire

open Notes.Kernel Leangage Leangage.Json.Read
open Leangage.Authz (Guarded)

/-- What the engine runs. -/
structure Call where
  actor : Principal
  cmd : Command

/-- Why a body is not a command. -/
inductive Refusal where
  /-- The body is not a JSON text. -/
  | notJson
  | notCommand
  /-- A JSON object without the member `cmd`. -/
  | missingCmd
deriving DecidableEq, Repr

/-- Whether the item is a value by itself. -/
def scalar : Item → Bool
  | .null | .bool _ | .num _ | .number | .str _ => true
  | .key _ | .arrOpen | .arrClose | .objOpen | .objClose => false

/-- The members of an object after its `{`, when no value is an array or an object; `acc` holds
those read, last first. -/
def members (acc : List (List UInt8 × Item)) : List Item → Option (List (List UInt8 × Item))
  | [.objClose] => some acc.reverse
  | .key k :: v :: rest => if scalar v then members ((k, v) :: acc) rest else none
  | _ => none

/-- The text whose UTF-8 is the bytes. -/
def textOf (bytes : List UInt8) : Option String :=
  String.fromUTF8? (ByteArray.mk bytes.toArray)

/-- The command with the given members. -/
def decodeMembers (ms : List (List UInt8 × Item)) : Except Refusal Command :=
  match ms.lookup [99, 109, 100] with
  | none => .error .missingCmd
  | some (.str name) =>
    if name = [97, 100, 100, 95, 109, 101, 109, 98, 101, 114] then
      if ms.length = 3 then
        match ms.lookup [117, 115, 101, 114], ms.lookup [97, 100, 109, 105, 110] with
        | some (.num user), some (.bool admin) => .ok (.addMember user admin)
        | _, _ => .error .notCommand
      else .error .notCommand
    else if name = [114, 101, 109, 111, 118, 101, 95, 109, 101, 109, 98, 101, 114] then
      if ms.length = 2 then
        match ms.lookup [117, 115, 101, 114] with
        | some (.num user) => .ok (.removeMember user)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = [112, 117, 116, 95, 110, 111, 116, 101] then
      if ms.length = 4 then
        match ms.lookup [105, 100], ms.lookup [98, 111, 100, 121], ms.lookup [115, 104, 97, 114, 101,
          100] with
        | some (.num id), some (.str body), some (.bool shared) =>
          match textOf body with
          | some body => .ok (.putNote id body shared)
          | none => .error .notCommand
        | _, _, _ => .error .notCommand
      else .error .notCommand
    else if name = [100, 101, 108, 101, 116, 101, 95, 110, 111, 116, 101] then
      if ms.length = 2 then
        match ms.lookup [105, 100] with
        | some (.num id) => .ok (.deleteNote id)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = [114, 101, 97, 100, 95, 110, 111, 116, 101] then
      if ms.length = 2 then
        match ms.lookup [105, 100] with
        | some (.num id) => .ok (.readNote id)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = [108, 105, 115, 116, 95, 110, 111, 116, 101, 115] then
      if ms.length = 1 then .ok .listNotes else .error .notCommand
    else if name = [108, 105, 115, 116, 95, 109, 101, 109, 98, 101, 114, 115] then
      if ms.length = 1 then .ok .listMembers else .error .notCommand
    else .error .notCommand
  | some _ => .error .notCommand

/-- The command that the items of a JSON text spell. -/
def decodeItems : List Item → Except Refusal Command
  | .objOpen :: rest =>
    match members [] rest with
    | some ms => decodeMembers ms
    | none => .error .notCommand
  | _ => .error .notCommand

/-- The command that a body spells. -/
def decode (body : String) : Except Refusal Command :=
  match readString body with
  | none => .error .notJson
  | some items => decodeItems items

/-- What a refused body is answered with. -/
def refusalMessage : Refusal → String
  | .notJson => "body is not JSON"
  | .notCommand => "not a notes command"
  | .missingCmd => "missing field `cmd`"

/-- What the engine runs for a request whose token, checked, claims `tenant`, `user` and the
expiry `exp`, at the time `now`; or the answer to the request. -/
def request (tenant user exp now : UInt64) (body : Http.Body) : Except Http.Response Call :=
  match Http.admit exp now body with
  | .error r => .error r
  | .ok text =>
    match decode text with
    | .error e => .error (Http.refuse 400 (refusalMessage e))
    | .ok cmd => .ok ⟨⟨tenant, user⟩, cmd⟩

/-- The tokens of a note: `{"body":"text","id":7,"owner":1,"shared":true}`. -/
def noteToks (n : Note) : List Json.StrTok :=
  [.objOpen, .key "body", .str n.body, .key "id", .num n.id, .key "owner", .num n.owner, .key "shared",
    .bool n.shared, .objClose]

/-- The tokens of a member: `{"admin":false,"user":2}`. -/
def memberToks (m : Member) : List Json.StrTok :=
  [.objOpen, .key "admin", .bool m.admin, .key "user", .num m.user, .objClose]

/-- The tokens of a reply. -/
def replyToks : Reply → List Json.StrTok
  | .done => [.objOpen, .key "done", .bool true, .objClose]
  | .found n => .objOpen :: .key "note" :: (noteToks n ++ [.objClose])
  | .notes ns => .objOpen :: .key "notes" :: .arrOpen :: (ns.flatMap noteToks ++ [.arrClose, .objClose])
  | .members ms =>
    .objOpen :: .key "members" :: .arrOpen :: (ms.flatMap memberToks ++ [.arrClose, .objClose])

/-- The bytes of a reply. -/
def encodeReply (r : Reply) : Array UInt8 :=
  Json.writeArray (replyToks r)

/-- The answer to a command the kernel accepted, the kernel refused or the guard denied. -/
def respond : Except (Guarded Error) Reply → Http.Response
  | .ok r => ⟨200, encodeReply r⟩
  | .error .denied => Http.refuse 403 "denied"
  | .error (.app .notFound) => Http.refuse 404 "not_found"
  | .error (.app .badText) => Http.refuse 422 "bad_text"

/-- The note with the given members, when their keys are `body`, `id`, `owner` and `shared`. -/
def noteOf (kb body ki : List UInt8) (id : UInt64) (ko : List UInt8) (owner : UInt64)
    (ks : List UInt8) (shared : Bool) : Option Note :=
  if kb = [98, 111, 100, 121] ∧ ki = [105, 100] ∧ ko = [111, 119, 110, 101, 114] ∧
      ks = [115, 104, 97, 114, 101, 100] then
    match textOf body with
    | some body => some ⟨id, owner, shared, body⟩
    | none => none
  else none

/-- The notes of an array after its `[`, up to the end of the reply; `acc` holds those read, last
first. -/
def notesItems (acc : List Note) : List Item → Option (List Note)
  | [.arrClose, .objClose] => some acc.reverse
  | .objOpen :: .key kb :: .str body :: .key ki :: .num id :: .key ko :: .num owner :: .key ks ::
      .bool shared :: .objClose :: rest =>
    match noteOf kb body ki id ko owner ks shared with
    | some n => notesItems (n :: acc) rest
    | none => none
  | _ => none

/-- The members of an array after its `[`, up to the end of the reply; `acc` holds those read,
last first. -/
def membersItems (acc : List Member) : List Item → Option (List Member)
  | [.arrClose, .objClose] => some acc.reverse
  | .objOpen :: .key ka :: .bool admin :: .key ku :: .num user :: .objClose :: rest =>
    if ka = [97, 100, 109, 105, 110] ∧ ku = [117, 115, 101, 114] then
      membersItems (⟨user, admin⟩ :: acc) rest
    else none
  | _ => none

/-- The reply whose tokens are the items. -/
def decodeReplyItems : List Item → Option Reply
  | [.objOpen, .key k, .bool true, .objClose] => if k = [100, 111, 110, 101] then some .done else none
  | [.objOpen, .key k, .objOpen, .key kb, .str body, .key ki, .num id, .key ko, .num owner, .key ks,
      .bool shared, .objClose, .objClose] =>
    if k = [110, 111, 116, 101] then
      match noteOf kb body ki id ko owner ks shared with
      | some n => some (.found n)
      | none => none
    else none
  | .objOpen :: .key k :: .arrOpen :: rest =>
    if k = [110, 111, 116, 101, 115] then
      match notesItems [] rest with
      | some ns => some (.notes ns)
      | none => none
    else if k = [109, 101, 109, 98, 101, 114, 115] then
      match membersItems [] rest with
      | some ms => some (.members ms)
      | none => none
    else none
  | _ => none

/-- The reply whose bytes `encodeReply` writes are the UTF-8 of the text. -/
def decodeReply (stored : String) : Option Reply :=
  match readString stored with
  | none => none
  | some items => decodeReplyItems items

/-- `acc` followed by `true` or `false` and ` }`. -/
def pushFlag (acc : Array UInt8) (b : Bool) : Array UInt8 :=
  (if b then acc ++ #[116, 114, 117, 101] else acc ++ #[102, 97, 108, 115, 101]) ++ #[32, 125]

/-- The bytes that identify a command under an idempotency key:
`AddMember { user: 2, admin: false }`, `RemoveMember { user: 2 }`,
`PutNote { id: 7, body: "text", shared: true }` with the body escaped as in a JSON string,
`DeleteNote { id: 7 }`, `ReadNote { id: 7 }`, `ListNotes`, `ListMembers`. -/
def fingerprint : Command → Array UInt8
  | .addMember user admin =>
    pushFlag
      (Json.pushDecimal #[65, 100, 100, 77, 101, 109, 98, 101, 114, 32, 123, 32, 117, 115, 101, 114, 58, 32]
        user.toNat ++ #[44, 32, 97, 100, 109, 105, 110, 58, 32])
      admin
  | .removeMember user =>
    Json.pushDecimal
      #[82, 101, 109, 111, 118, 101, 77, 101, 109, 98, 101, 114, 32, 123, 32, 117, 115, 101, 114, 58, 32]
      user.toNat ++ #[32, 125]
  | .putNote id body shared =>
    pushFlag
      (Json.pushEscaped body 0
        (Json.pushDecimal #[80, 117, 116, 78, 111, 116, 101, 32, 123, 32, 105, 100, 58, 32] id.toNat ++
          #[44, 32, 98, 111, 100, 121, 58, 32, 34]) ++
        #[34, 44, 32, 115, 104, 97, 114, 101, 100, 58, 32])
      shared
  | .deleteNote id =>
    Json.pushDecimal #[68, 101, 108, 101, 116, 101, 78, 111, 116, 101, 32, 123, 32, 105, 100, 58,
      32] id.toNat ++
      #[32, 125]
  | .readNote id =>
    Json.pushDecimal #[82, 101, 97, 100, 78, 111, 116, 101, 32, 123, 32, 105, 100, 58,
      32] id.toNat ++ #[32, 125]
  | .listNotes => #[76, 105, 115, 116, 78, 111, 116, 101, 115]
  | .listMembers => #[76, 105, 115, 116, 77, 101, 109, 98, 101, 114, 115]

/-- `u<user>`: the keys of one user of an organization. -/
def scope (actor : Principal) : String :=
  "u" ++ toString actor.user.toNat

end Notes.Wire
