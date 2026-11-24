/-!
# Calculator

One number per user. `set` stores a number, `apply` combines the stored number with an argument and
refuses when the result leaves 64 bits, `get` reads it.
-/

namespace Calculator.Kernel

structure Principal where
  org : UInt64
  user : UInt64

structure Memory where
  user : UInt64
  value : UInt64
deriving DecidableEq, Repr

structure Snapshot where
  memories : List Memory

inductive Op where
  | add | sub | mul | div
deriving DecidableEq, Repr

inductive Command where
  | set (value : UInt64)
  | apply (op : Op) (arg : UInt64)
  | get

inductive Reply where
  | value (v : UInt64)
deriving DecidableEq, Repr

inductive Error where
  | overflow | underflow | divByZero
deriving DecidableEq, Repr

def memoryOf : List Memory → UInt64 → UInt64
  | [], _ => 0
  | m :: ms, u => if m.user = u then m.value else memoryOf ms u

def upsert (m : Memory) : List Memory → List Memory
  | [] => [m]
  | x :: xs => if x.user = m.user then m :: xs else x :: upsert m xs

def compute (op : Op) (a b : UInt64) : Except Error UInt64 :=
  match op with
  | .add => if a > 18446744073709551615 - b then .error .overflow else .ok (a + b)
  | .sub => if a < b then .error .underflow else .ok (a - b)
  | .mul => if b ≠ 0 ∧ a > 18446744073709551615 / b then .error .overflow else .ok (a * b)
  | .div => if b = 0 then .error .divByZero else .ok (a / b)

def transition (actor : Principal) (snap : Snapshot) (cmd : Command) :
    Except Error (Option Memory × Reply) :=
  match cmd with
  | .set value => .ok (some { user := actor.user, value }, .value value)
  | .apply op arg =>
    match compute op (memoryOf snap.memories actor.user) arg with
    | .ok v => .ok (some { user := actor.user, value := v }, .value v)
    | .error e => .error e
  | .get => .ok (none, .value (memoryOf snap.memories actor.user))

def apply (snap : Snapshot) (w : Option Memory) : Snapshot :=
  match w with
  | none => snap
  | some m => { memories := upsert m snap.memories }

def init : Snapshot := { memories := [] }

def tenant (actor : Principal) : UInt64 := actor.org

def readOnly : Command → Bool
  | .get => true
  | _ => false

end Calculator.Kernel
