import Notes.Kernel
import Leangage.Sql

/-!
# The notes' tables

A tenant's members are rows of `members`: the user (`BIGINT`) and whether the member is an admin
(`BOOLEAN`). Its notes are rows of `notes`: the id and the owner (`BIGINT`), whether the note is
shared (`BOOLEAN`) and the body (`TEXT`). The first column of each table is its key. A `UInt64`
is stored as the `Int64` with the same bits.

`writes` turns a write set into the rows it stores and deletes, and `load` builds a snapshot from
the rows a `SELECT` of each table returned, in any order.
-/

namespace Notes.Store

open Notes.Kernel Leangage.Sql

/-- The tables, in the order `load` receives their rows. -/
def tables : List Tab :=
  [⟨"members", [⟨"user", .int, false⟩, ⟨"admin", .bool, false⟩], 1⟩,
   ⟨"notes", [⟨"id", .int, false⟩, ⟨"owner", .int, false⟩, ⟨"shared", .bool, false⟩,
     ⟨"body", .text, false⟩], 1⟩]

def memberRow (m : Member) : List Val := [.int m.user.toInt64, .bool m.admin]

def memberOfRow : List Val → Option Member
  | [.int user, .bool admin] => some { user := user.toUInt64, admin }
  | _ => none

def noteRow (n : Note) : List Val :=
  [.int n.id.toInt64, .int n.owner.toInt64, .bool n.shared, .text n.body]

def noteOfRow : List Val → Option Note
  | [.int id, .int owner, .bool shared, .text body] =>
    some { id := id.toUInt64, owner := owner.toUInt64, shared, body }
  | _ => none

/-- The row one write stores, or the key of the row it deletes. -/
def write : Notes.Kernel.Write → Leangage.Sql.Write
  | .putMember m => .put 0 1 (memberRow m)
  | .delMember user => .del 0 [.int user.toInt64]
  | .putNote n => .put 1 1 (noteRow n)
  | .delNote id => .del 1 [.int id.toInt64]

/-- The rows a write set stores and deletes. -/
def writes (ws : List Notes.Kernel.Write) : List Leangage.Sql.Write := ws.map write

/-- The snapshot of the rows of each table; `none` when a row is not a member or a note. -/
def load : List (List (List Val)) → Option Snapshot
  | [members, notes] =>
    match members.mapM memberOfRow, notes.mapM noteOfRow with
    | some ms, some ns => some { members := ms, notes := ns }
    | _, _ => none
  | _ => none

end Notes.Store
