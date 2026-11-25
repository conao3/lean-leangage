import Calculator.Kernel
import Leanharbor.Sql

/-!
# The calculator's table

A tenant's numbers are rows of one table, `memories`: the user, then the number, both `BIGINT`.
The user is the key. A `UInt64` is stored as the `Int64` with the same bits.

`writes` turns a write set into the rows it stores, and `load` builds a snapshot from the rows a
`SELECT` of each table returned, in any order.
-/

namespace Calculator.Store

open Calculator.Kernel Leanharbor.Sql

/-- The tables, in the order `load` receives their rows. -/
def tables : List Tab := [⟨"memories", [⟨"user", .int, false⟩, ⟨"value", .int, false⟩], 1⟩]

def toRow (m : Memory) : List Val := [.int m.user.toInt64, .int m.value.toInt64]

def fromRow : List Val → Option Memory
  | [.int user, .int value] => some { user := user.toUInt64, value := value.toUInt64 }
  | _ => none

/-- The rows a write set stores. -/
def writes : Option Memory → List Write
  | none => []
  | some m => [.put 0 1 (toRow m)]

/-- The numbers of `ms`, stored in order into `acc`. -/
def storeAll (acc : Memories) : List Memory → Memories
  | [] => acc
  | m :: ms => storeAll (upsert m acc) ms

/-- The snapshot of the rows of each table; `none` when a row is not a `Memory`. -/
def load : List (List (List Val)) → Option Snapshot
  | [rows] =>
    match rows.mapM fromRow with
    | some ms => some { memories := storeAll .empty ms }
    | none => none
  | _ => none

end Calculator.Store
