import Notes.Kernel
import Leangage.Http

/-!
# The notes on the wire

What the notes' server does with a request once its token's tag is checked, and with the engine's
result. `request` reads the tokens of the body into the command and the principal the engine runs, or gives the
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

open Notes.Kernel Leangage Leangage.Json.Lexemes
open Leangage.Authz (Guarded)

/-- What the engine runs. -/
structure Call where
  actor : Principal
  cmd : Command

/-- Why a body is not a command. -/
inductive Refusal where
  | notCommand
  /-- A JSON object without the member `cmd`. -/
  | missingCmd
deriving DecidableEq, Repr

/-- The command with the given members. -/
def decodeMembers (ms : List (String × Scalar)) : Except Refusal Command :=
  match ms.lookup "cmd" with
  | none => .error .missingCmd
  | some (.str name) =>
    if name = "add_member" then
      if ms.length = 3 then
        match ms.lookup "user", ms.lookup "admin" with
        | some (.num user), some (.bool admin) => .ok (.addMember user admin)
        | _, _ => .error .notCommand
      else .error .notCommand
    else if name = "remove_member" then
      if ms.length = 2 then
        match ms.lookup "user" with
        | some (.num user) => .ok (.removeMember user)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = "put_note" then
      if ms.length = 4 then
        match ms.lookup "id", ms.lookup "body", ms.lookup "shared" with
        | some (.num id), some (.str body), some (.bool shared) => .ok (.putNote id body shared)
        | _, _, _ => .error .notCommand
      else .error .notCommand
    else if name = "delete_note" then
      if ms.length = 2 then
        match ms.lookup "id" with
        | some (.num id) => .ok (.deleteNote id)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = "read_note" then
      if ms.length = 2 then
        match ms.lookup "id" with
        | some (.num id) => .ok (.readNote id)
        | _ => .error .notCommand
      else .error .notCommand
    else if name = "list_notes" then
      if ms.length = 1 then .ok .listNotes else .error .notCommand
    else if name = "list_members" then
      if ms.length = 1 then .ok .listMembers else .error .notCommand
    else .error .notCommand
  | some _ => .error .notCommand

/-- The command that the tokens of a JSON text spell. -/
def decode (tokens : Tokens) : Except Refusal Command :=
  match object tokens.lexemes with
  | some ms => decodeMembers ms
  | none => .error .notCommand

/-- What a refused body is answered with. -/
def refusalMessage : Refusal → String
  | .notCommand => "not a notes command"
  | .missingCmd => "missing field `cmd`"

/-- What the engine runs for a request whose token, checked, claims `tenant`, `user` and the
expiry `exp`, at the time `now`; or the answer to the request. -/
def request (tenant user exp now : UInt64) (body : Http.Body) : Except Http.Response Call :=
  match Http.admit exp now body with
  | .error r => .error r
  | .ok tokens =>
    match decode tokens with
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

/-- The note with the given members, when their names are `body`, `id`, `owner` and `shared` and
the number tokens are decimals of a `UInt64`. -/
def noteOf (kb body ki id ko owner ks : String) (shared : Bool) : Option Note :=
  if kb = "body" ∧ ki = "id" ∧ ko = "owner" ∧ ks = "shared" then
    match numberOf id, numberOf owner with
    | some id, some owner => some ⟨id, owner, shared, body⟩
    | _, _ => none
  else none

/-- The notes of an array after its `[`, up to the end of the reply; `acc` holds those read, last
first. -/
def notesOf (acc : List Note) : List Lexeme → Option (List Note)
  | [.arrClose, .objClose] => some acc.reverse
  | .objOpen :: .key kb :: .str body :: .key ki :: .number id :: .key ko :: .number owner :: .key ks ::
      .bool shared :: .objClose :: rest =>
    match noteOf kb body ki id ko owner ks shared with
    | some n => notesOf (n :: acc) rest
    | none => none
  | _ => none

/-- The members of an array after its `[`, up to the end of the reply; `acc` holds those read,
last first. -/
def membersOf (acc : List Member) : List Lexeme → Option (List Member)
  | [.arrClose, .objClose] => some acc.reverse
  | .objOpen :: .key ka :: .bool admin :: .key ku :: .number user :: .objClose :: rest =>
    if ka = "admin" ∧ ku = "user" then
      match numberOf user with
      | some user => membersOf (⟨user, admin⟩ :: acc) rest
      | none => none
    else none
  | _ => none

/-- The reply whose tokens are the given ones. -/
def replyOf : List Lexeme → Option Reply
  | [.objOpen, .key k, .bool true, .objClose] => if k = "done" then some .done else none
  | [.objOpen, .key k, .objOpen, .key kb, .str body, .key ki, .number id, .key ko, .number owner, .key ks,
      .bool shared, .objClose, .objClose] =>
    if k = "note" then
      match noteOf kb body ki id ko owner ks shared with
      | some n => some (.found n)
      | none => none
    else none
  | .objOpen :: .key k :: .arrOpen :: rest =>
    if k = "notes" then
      match notesOf [] rest with
      | some ns => some (.notes ns)
      | none => none
    else if k = "members" then
      match membersOf [] rest with
      | some ms => some (.members ms)
      | none => none
    else none
  | _ => none

/-- The reply that the tokens of a stored reply spell, the tokens being those a JSON library reads
from the bytes `encodeReply` wrote; `none` stands for bytes the library refuses. -/
def decodeReply (stored : Option Tokens) : Option Reply :=
  match stored with
  | none => none
  | some tokens => replyOf tokens.lexemes

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
