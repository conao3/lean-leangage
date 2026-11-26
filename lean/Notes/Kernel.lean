import Leangage.Authz

/-!
# Notes

Based on h5i's `examples/app/notes/kernel/src/lib.rs` (commit 515c7b9, Apache-2.0), rewritten in
Lean: the policy that h5i declares in a `policy` block of `schema!` is written here as the Bool
functions `permits`, `visible`, `stored` and `view`, rows are kept in lists, and a note's body is a
`String`.

Notes in an organization, with members and admins. A note is visible to everyone if it is shared,
otherwise to its owner and admins; the owner or an admin edits and deletes it, and its owner never
changes. Admins add and remove members; anyone may add the first member of an organization with
none.

`handle` decides what each command does and checks input and existence only. The listings are in
key order, so that no reply depends on the order of the rows. `transition`, the function the
engine runs, is `handle` behind the guard of `Leangage.Authz`.
-/

namespace Notes.Kernel

open Leangage.Authz

/-- Who is calling: an organization (the tenant) and a user in it. -/
structure Principal where
  org : UInt64
  user : UInt64
deriving DecidableEq, Repr

structure Member where
  user : UInt64
  admin : Bool
deriving DecidableEq, Repr

structure Note where
  id : UInt64
  owner : UInt64
  /-- Visible to everyone in the organization. -/
  shared : Bool
  body : String
deriving DecidableEq, Repr

/-- One organization's state. -/
structure Snapshot where
  members : List Member
  notes : List Note
deriving DecidableEq, Repr

inductive Command where
  /-- Add a member, as admin if asked: the policy decides who may. -/
  | addMember (user : UInt64) (admin : Bool)
  | removeMember (user : UInt64)
  /-- Create note `id` as the caller, or replace its body and whether it is shared. -/
  | putNote (id : UInt64) (body : String) (shared : Bool)
  | deleteNote (id : UInt64)
  | readNote (id : UInt64)
  | listNotes
  | listMembers
deriving DecidableEq, Repr

inductive Write where
  | putMember (m : Member)
  | delMember (user : UInt64)
  | putNote (n : Note)
  | delNote (id : UInt64)
deriving DecidableEq, Repr

inductive Reply where
  | done
  | found (n : Note)
  | notes (ns : List Note)
  | members (ms : List Member)
deriving DecidableEq, Repr

inductive Error where
  | notFound | badText
deriving DecidableEq, Repr

/-- A row a reply discloses, one constructor per table. -/
inductive Row where
  | member (m : Member)
  | note (n : Note)
deriving DecidableEq, Repr

/-- The longest note, in bytes. -/
def maxText : Nat := 4096

/-- A body is not empty, at most `maxText` bytes, and holds no NUL, which PostgreSQL cannot store
in a `TEXT` column. -/
def textOk (t : String) : Bool :=
  0 < t.utf8ByteSize && t.utf8ByteSize ≤ maxText && !t.toList.contains '\x00'

/-- The member stored under the user id, if any. -/
def findMember (ms : List Member) (user : UInt64) : Option Member := ms.find? (·.user == user)

/-- The note stored under the id, if any. -/
def findNote (ns : List Note) (id : UInt64) : Option Note := ns.find? (·.id == id)

/-- Replaces the member with the same user id, or adds it at the end. -/
def putMember (ms : List Member) (m : Member) : List Member :=
  if ms.any (·.user == m.user) then ms.map fun x => if x.user == m.user then m else x
  else ms ++ [m]

/-- Replaces the note with the same id, or adds it at the end. -/
def putNote (ns : List Note) (n : Note) : List Note :=
  if ns.any (·.id == n.id) then ns.map fun x => if x.id == n.id then n else x
  else ns ++ [n]

/-- What one write does to the state. -/
def applyWrite (s : Snapshot) : Write → Snapshot
  | .putMember m => { s with members := putMember s.members m }
  | .delMember user => { s with members := s.members.filter (·.user != user) }
  | .putNote n => { s with notes := putNote s.notes n }
  | .delNote id => { s with notes := s.notes.filter (·.id != id) }

def apply (s : Snapshot) (ws : List Write) : Snapshot := ws.foldl applyWrite s

/-- Puts the member before the first member with a larger user id. -/
def insertMember (m : Member) : List Member → List Member
  | [] => [m]
  | x :: ms => if m.user ≤ x.user then m :: x :: ms else x :: insertMember m ms

/-- The members in the order of their user ids. -/
def sortMembers : List Member → List Member
  | [] => []
  | m :: ms => insertMember m (sortMembers ms)

/-- Puts the note before the first note with a larger id. -/
def insertNote (n : Note) : List Note → List Note
  | [] => [n]
  | x :: ns => if n.id ≤ x.id then n :: x :: ns else x :: insertNote n ns

/-- The notes in the order of their ids. -/
def sortNotes : List Note → List Note
  | [] => []
  | n :: ns => insertNote n (sortNotes ns)

/-! ## The policy -/

/-- The user's own member row has `admin` set. -/
def isAdmin (s : Snapshot) (user : UInt64) : Bool :=
  match findMember s.members user with
  | some m => m.admin
  | none => false

/-- Admins add, replace and delete members, and anyone may add the first member of an organization
with none. A note is created by its owner or an admin, and replaced or deleted by the stored note's
owner or an admin; a replacement keeps the owner. A delete of a key that is not stored is
refused. -/
def permits (a : Principal) (s : Snapshot) : Write → Bool
  | .putMember m =>
    match findMember s.members m.user with
    | none => isAdmin s a.user || s.members.isEmpty
    | some _ => isAdmin s a.user
  | .delMember user =>
    match findMember s.members user with
    | none => false
    | some _ => isAdmin s a.user
  | .putNote n =>
    match findNote s.notes n.id with
    | none => n.owner == a.user || isAdmin s a.user
    | some old => n.owner == old.owner && (old.owner == a.user || isAdmin s a.user)
  | .delNote id =>
    match findNote s.notes id with
    | none => false
    | some old => old.owner == a.user || isAdmin s a.user

/-- A member row is visible to that member and to admins; a note to everyone if it is shared,
otherwise to its owner and admins. -/
def visible (a : Principal) (s : Snapshot) : Row → Bool
  | .member m => m.user == a.user || isAdmin s a.user
  | .note n => n.shared || n.owner == a.user || isAdmin s a.user

/-- The row is the one stored under its key. -/
def stored (s : Snapshot) : Row → Bool
  | .member m => findMember s.members m.user == some m
  | .note n => findNote s.notes n.id == some n

/-- The rows the policy lets the actor see. -/
def view (a : Principal) (s : Snapshot) : Snapshot :=
  { members := s.members.filter fun m => visible a s (.member m)
    notes := s.notes.filter fun n => visible a s (.note n) }

/-- Every row a reply carries. -/
def disclosed : Reply → List Row
  | .done => []
  | .found n => [.note n]
  | .notes ns => ns.map .note
  | .members ms => ms.map .member

def readOnly : Command → Bool
  | .readNote _ | .listNotes | .listMembers => true
  | _ => false

/-! ## The handlers: what each command does, with no authorization -/

def handle (a : Principal) (s : Snapshot) : Command → Except Error (List Write × Reply)
  | .addMember user admin => .ok ([.putMember { user, admin }], .done)
  | .removeMember user =>
    match findMember s.members user with
    | none => .error .notFound
    | some _ => .ok ([.delMember user], .done)
  | .putNote id body shared =>
    if textOk body then
      let owner := match findNote s.notes id with
        | some old => old.owner
        | none => a.user
      .ok ([.putNote { id, owner, shared, body }], .done)
    else .error .badText
  | .deleteNote id =>
    match findNote s.notes id with
    | none => .error .notFound
    | some _ => .ok ([.delNote id], .done)
  | .readNote id =>
    match findNote s.notes id with
    | none => .error .notFound
    | some n => .ok ([], .found n)
  | .listNotes => .ok ([], .notes (sortNotes s.notes))
  | .listMembers => .ok ([], .members (sortMembers s.members))

/-- The kernel the engine runs: `handle` behind the guard. -/
def transition (a : Principal) (s : Snapshot) (c : Command) :
    Except (Guarded Error) (List Write × Reply) :=
  guardViewed handle apply ⟨permits, visible, stored⟩ disclosed readOnly view a s c

def init : Snapshot := { members := [], notes := [] }

def tenant (a : Principal) : UInt64 := a.org

end Notes.Kernel
