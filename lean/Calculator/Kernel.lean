/-!
# Calculator

One number per user. `set` stores a number, `apply` combines the stored number with an argument and
refuses when the result leaves 64 bits, `get` reads it.

A tenant's numbers are a binary trie on the user id, lowest bit first: a lookup and an update
visit one node per bit until the id is alone in its subtree.
-/

namespace Calculator.Kernel

structure Principal where
  org : UInt64
  user : UInt64

structure Memory where
  user : UInt64
  value : UInt64
deriving DecidableEq, Repr

/-- The numbers of a tenant. A `leaf` holds the bits of the user id that the path to it has not
used. -/
inductive Memories where
  | empty
  | leaf (key value : UInt64)
  | node (even odd : Memories)
deriving DecidableEq, Repr

structure Snapshot where
  memories : Memories

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

def memoryOf : Memories → UInt64 → UInt64
  | .empty, _ => 0
  | .leaf key value, u => if u = key then value else 0
  | .node even odd, u => if u % 2 = 0 then memoryOf even (u / 2) else memoryOf odd (u / 2)

/-- The trie of two different ids. -/
def pair (k₁ v₁ k v : UInt64) : Memories :=
  if h : k₁ = k then .leaf k v
  else if k % 2 = 0 then
    if k₁ % 2 = 0 then .node (pair (k₁ / 2) v₁ (k / 2) v) .empty
    else .node (.leaf (k / 2) v) (.leaf (k₁ / 2) v₁)
  else
    if k₁ % 2 = 0 then .node (.leaf (k₁ / 2) v₁) (.leaf (k / 2) v)
    else .node .empty (pair (k₁ / 2) v₁ (k / 2) v)
termination_by k₁.toNat + k.toNat
decreasing_by
  all_goals
    have hne : k₁.toNat ≠ k.toNat := fun h' => h (UInt64.toNat_inj.mp h')
    simp only [UInt64.toNat_div, UInt64.reduceToNat]
    omega

def store (k v : UInt64) : Memories → Memories
  | .empty => .leaf k v
  | .leaf k₁ v₁ => pair k₁ v₁ k v
  | .node even odd =>
    if k % 2 = 0 then .node (store (k / 2) v even) odd else .node even (store (k / 2) v odd)

def upsert (m : Memory) (ms : Memories) : Memories := store m.user m.value ms

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

def init : Snapshot := { memories := .empty }

def tenant (actor : Principal) : UInt64 := actor.org

def readOnly : Command → Bool
  | .get => true
  | _ => false

end Calculator.Kernel
