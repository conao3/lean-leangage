import Leangage.Http
import Oracle.JsonText
import Leangage.Json.Lexemes.Proofs
import Notes.Wire

/-!
Runs the notes' functions on requests and responses natively on lines read from standard input
and prints one line per input line. The generated Rust is checked against this output.

Bytes are written `x<hex>`, and a text as the `x<hex>` of its UTF-8. A flag is `t` or `f`. A
command is `add_member <user> <admin>`, `remove_member <user>`, `put_note <id> <shared> <body>`,
`delete_note <id>`, `read_note <id>`, `list_notes` or `list_members`. A reply is `done`,
`found <note>`, `notes` and its notes, or `members` and its members, with a note
`<id>:<owner>:<shared>:<body>` and a member `<user>:<admin>`.

| line | prints |
|---|---|
| `request <tenant> <user> <exp> <now> <body>` | for `Notes.Wire.request`: `ok <org> <user> <command>` or `err <status> x<body>` |
| `respond ok <reply>`, `respond err <name>` | `resp <status> x<body>` of `Notes.Wire.respond` |
| `fingerprint <command>` | `bytes x<hex>` |
| `scope <user>` | `text x<hex>` |
| `stored x<hex>` | for `Notes.Wire.decodeReply`: `reply <reply>` or `none` |

A body is `x<hex>` (its bytes), `toolarge` or `unreadable`. The names of the refusals are
`denied`, `not_found` and `bad_text`.
-/

open Leangage Notes.Kernel

def hexDigitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigitValue a
    let y ← hexDigitValue b
    return (x * 16 + y).toUInt8 :: (← unhexChars rest)
  | _ => none

def hexChar (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def showBytes (bs : List UInt8) : String :=
  "x" ++ String.join (bs.map fun b => String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)])

def bytes (s : String) : Option (List UInt8) :=
  match s.toList with
  | 'x' :: hex => unhexChars hex
  | _ => none

def text (s : String) : Option String := do
  String.fromUTF8? (ByteArray.mk (← bytes s).toArray)

def showText (s : String) : String := showBytes s.toUTF8.toList

def number (s : String) : Option UInt64 := do
  let n ← s.toNat?
  if n < 2 ^ 64 then some n.toUInt64 else none

def flag : String → Option Bool
  | "t" => some true
  | "f" => some false
  | _ => none

def showFlag (b : Bool) : String := if b then "t" else "f"

def showResponse (head : String) (r : Http.Response) : String :=
  s!"{head} {r.status} {showBytes r.body.toList}"

def command : List String → Option Command
  | ["add_member", user, admin] => do return .addMember (← number user) (← flag admin)
  | ["remove_member", user] => do return .removeMember (← number user)
  | ["put_note", id, shared, body] => do return .putNote (← number id) (← text body) (← flag shared)
  | ["delete_note", id] => do return .deleteNote (← number id)
  | ["read_note", id] => do return .readNote (← number id)
  | ["list_notes"] => some .listNotes
  | ["list_members"] => some .listMembers
  | _ => none

def showCommand : Command → String
  | .addMember user admin => s!"add_member {user} {showFlag admin}"
  | .removeMember user => s!"remove_member {user}"
  | .putNote id body shared => s!"put_note {id} {showFlag shared} {showText body}"
  | .deleteNote id => s!"delete_note {id}"
  | .readNote id => s!"read_note {id}"
  | .listNotes => "list_notes"
  | .listMembers => "list_members"

def note (s : String) : Option Note :=
  match s.splitOn ":" with
  | [id, owner, shared, body] => do
    return ⟨← number id, ← number owner, ← flag shared, ← text body⟩
  | _ => none

def member (s : String) : Option Member :=
  match s.splitOn ":" with
  | [user, admin] => do return ⟨← number user, ← flag admin⟩
  | _ => none

def showNote (n : Note) : String :=
  s!"{n.id}:{n.owner}:{showFlag n.shared}:{showText n.body}"

def showMember (m : Member) : String :=
  s!"{m.user}:{showFlag m.admin}"

def reply : List String → Option Reply
  | ["done"] => some .done
  | ["found", n] => do return .found (← note n)
  | "notes" :: ns => do return .notes (← ns.mapM note)
  | "members" :: ms => do return .members (← ms.mapM member)
  | _ => none

def showReply : Reply → String
  | .done => "done"
  | .found n => s!"found {showNote n}"
  | .notes ns => " ".intercalate ("notes" :: ns.map showNote)
  | .members ms => " ".intercalate ("members" :: ms.map showMember)

def body : String → Option Http.Body
  | "toolarge" => some .tooLarge
  | "unreadable" => some .unreadable
  | s => do
    match Oracle.JsonText.lexemes (← bytes s) with
    | some lexemes => return .json (Json.Lexemes.encode lexemes)
    | none => return .notJson

def refusal : String → Option (Authz.Guarded Error)
  | "denied" => some .denied
  | "not_found" => some (.app .notFound)
  | "bad_text" => some (.app .badText)
  | _ => none

def run (line : String) : Option String :=
  match line.splitOn " " with
  | ["request", tenant, user, exp, now, b] => do
    match Notes.Wire.request (← number tenant) (← number user) (← number exp) (← number now)
        (← body b) with
    | .ok call => return s!"ok {call.actor.org} {call.actor.user} {showCommand call.cmd}"
    | .error r => return showResponse "err" r
  | "respond" :: "ok" :: r => do
    return showResponse "resp" (Notes.Wire.respond (.ok (← reply r)))
  | ["respond", "err", name] => do
    return showResponse "resp" (Notes.Wire.respond (.error (← refusal name)))
  | "fingerprint" :: cmd => do
    return "bytes " ++ showBytes (Notes.Wire.fingerprint (← command cmd)).toList
  | ["scope", user] => do
    return "text " ++ showText (Notes.Wire.scope ⟨0, ← number user⟩)
  | ["stored", b] => do
    match Notes.Wire.decodeReply ((Oracle.JsonText.lexemes (← bytes b)).map Json.Lexemes.encode) with
    | some r => return s!"reply {showReply r}"
    | none => return "none"
  | _ => none

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  IO.println ((run line.trimAscii.toString).getD "bad line")
  loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
