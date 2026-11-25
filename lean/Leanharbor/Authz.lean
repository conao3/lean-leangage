/-!
# The authorization guard

Based on h5i's `crates/h5i-app-std/src/authz.rs` (commit 515c7b9, Apache-2.0), rewritten in Lean:
the traits `Transition`, `Policy`, `Disclose` and `View` became function arguments and the
structure `Policy`, and the loops over indices became recursion on lists.

A kernel's `transition` decides a command with no authorization of its own; the guard runs it and
refuses the command unless the policy permits every write and lets the actor see every row the
reply discloses. Write `i` is checked in the state the writes before it leave (`apply s (ws.take i)`),
so a command may create a row and then act on it. A disclosed row must be stored, exactly as
disclosed, and visible, in the state before the command or in the state after it. One refused write
or row refuses the whole command, and nothing is stored.

`Leanharbor.AuthzProofs` proves what the guard guarantees, for every kernel and policy.
-/

namespace Leanharbor.Authz

/-- A command's refusal: the kernel's own, or the guard's. -/
inductive Guarded (ε : Type) where
  | app (e : ε)
  /-- A write the policy does not permit, or a row it does not let the actor see. -/
  | denied
deriving DecidableEq, Repr

/-- What each actor may write and see. `D` is the type of disclosed rows. -/
structure Policy (A S W D : Type) where
  /-- May the actor make the write in the state? -/
  permits : A → S → W → Bool
  /-- May the actor see the row in the state? The guard asks only about rows `stored` accepts. -/
  visible : A → S → D → Bool
  /-- Is the row stored in the state, exactly as given? -/
  stored : S → D → Bool

variable {A S C W R E D : Type}

/-- Every write of `ws` is permitted in the state that `done` and the writes before it leave. -/
def checkWritesFrom (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S)
    (done : List W) : List W → Bool
  | [] => true
  | w :: rest => p.permits a (apply s done) w && checkWritesFrom apply p a s (done ++ [w]) rest

/-- Every write is permitted in the state the writes before it leave. -/
def checkWrites (apply : S → List W → S) (p : Policy A S W D) (a : A) (s : S) (ws : List W) :
    Bool :=
  checkWritesFrom apply p a s [] ws

/-- The row is stored in the state, exactly as given, and the actor may see it there. -/
def shown (p : Policy A S W D) (a : A) (s : S) (d : D) : Bool :=
  p.stored s d && p.visible a s d

/-- Every row is `shown` in `before` or in `after`. -/
def checkReads (p : Policy A S W D) (a : A) (before after : S) (ds : List D) : Bool :=
  ds.all fun d => shown p a before d || shown p a after d

/-- `transition`, refused with `denied` unless every write is permitted and every disclosed row is
visible. -/
def guard (transition : A → S → C → Except E (List W × R)) (apply : S → List W → S)
    (p : Policy A S W D) (disclosed : R → List D) (a : A) (s : S) (c : C) :
    Except (Guarded E) (List W × R) :=
  match transition a s c with
  | .error e => .error (.app e)
  | .ok (ws, r) =>
    if checkWrites apply p a s ws && checkReads p a s (apply s ws) (disclosed r) then .ok (ws, r)
    else .error .denied

/-- `guard` for commands that write. A read-only command runs on the actor's view: it is denied if
it returns writes or discloses a row not shown in the view, and nothing else of the state reaches
its result. -/
def guardViewed (transition : A → S → C → Except E (List W × R)) (apply : S → List W → S)
    (p : Policy A S W D) (disclosed : R → List D) (readOnly : C → Bool) (view : A → S → S)
    (a : A) (s : S) (c : C) : Except (Guarded E) (List W × R) :=
  if readOnly c then
    let v := view a s
    match transition a v c with
    | .error e => .error (.app e)
    | .ok (ws, r) =>
      if ws.isEmpty && checkReads p a v v (disclosed r) then .ok (ws, r) else .error .denied
  else guard transition apply p disclosed a s c

end Leanharbor.Authz
