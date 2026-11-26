import Calculator.Kernel
import Leangage.Http
import Leangage.Json.Read

/-!
# The calculator on the wire

What the calculator's servers do with a request once its token's tag is checked, and with the
engine's result. `request` reads the body into the command and the principal the engine runs, or
gives the answer to a request the engine does not see. `respond` gives the answer to an accepted
and to a refused command. `fingerprint` is the bytes that identify a command under an idempotency
key, and `scope` the name that separates the keys of the users of a tenant.

A command is a JSON object: `{"cmd":"set","value":6}`, `{"cmd":"apply","op":"mul","arg":7}` with
the operations `add`, `sub`, `mul` and `div`, and `{"cmd":"get"}`. Its members may come in any
order; an object with another member, or with a member twice, is not a command.
-/

namespace Calculator.Wire

open Calculator.Kernel Leangage Leangage.Json.Read

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
  /-- `set` whose `value` is not a number below 2^64 in decimal digits. -/
  | badValue
  /-- `apply` whose `arg` is not a number below 2^64 in decimal digits. -/
  | badArg
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

/-- The operation with the given name. -/
def opNamed (name : List UInt8) : Option Op :=
  if name = [97, 100, 100] then some .add
  else if name = [115, 117, 98] then some .sub
  else if name = [109, 117, 108] then some .mul
  else if name = [100, 105, 118] then some .div
  else none

/-- The command with the given members. -/
def decodeMembers (ms : List (List UInt8 × Item)) : Except Refusal Command :=
  match ms.lookup [99, 109, 100] with
  | none => .error .missingCmd
  | some (.str name) =>
    if name = [115, 101, 116] then
      if ms.length = 2 then
        match ms.lookup [118, 97, 108, 117, 101] with
        | some (.num n) => .ok (.set n)
        | some _ => .error .badValue
        | none => .error .notCommand
      else .error .notCommand
    else if name = [97, 112, 112, 108, 121] then
      if ms.length = 3 then
        match ms.lookup [111, 112], ms.lookup [97, 114, 103] with
        | some (.str op), some arg =>
          match opNamed op with
          | some op =>
            match arg with
            | .num n => .ok (.apply op n)
            | _ => .error .badArg
          | none => .error .notCommand
        | _, _ => .error .notCommand
      else .error .notCommand
    else if name = [103, 101, 116] then
      if ms.length = 1 then .ok .get else .error .notCommand
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
  | .notCommand => "not a calculator command"
  | .missingCmd => "missing field `cmd`"
  | .badValue => "`value` must be an integer below 2^64"
  | .badArg => "`arg` must be an integer below 2^64"

/-- What the engine runs for a request whose token, checked, claims `tenant`, `user` and the
expiry `exp`, at the time `now`; or the answer to the request. -/
def request (tenant user exp now : UInt64) (body : Http.Body) : Except Http.Response Call :=
  match Http.admit exp now body with
  | .error r => .error r
  | .ok text =>
    match decode text with
    | .error e => .error (Http.refuse 400 (refusalMessage e))
    | .ok cmd => .ok ⟨⟨tenant, user⟩, cmd⟩

/-- The answer to a command the kernel accepted or refused. -/
def respond : Except Error Reply → Http.Response
  | .ok r => ⟨200, encodeReplyArray r⟩
  | .error e => ⟨422, encodeErrorArray e⟩

/-- The name of an operation in a fingerprint. -/
def opFingerprint : Op → Array UInt8
  | .add => #[65, 112, 112, 108, 121, 32, 123, 32, 111, 112, 58, 32, 65, 100, 100, 44, 32, 97, 114, 103, 58, 32]
  | .sub => #[65, 112, 112, 108, 121, 32, 123, 32, 111, 112, 58, 32, 83, 117, 98, 44, 32, 97, 114, 103, 58, 32]
  | .mul => #[65, 112, 112, 108, 121, 32, 123, 32, 111, 112, 58, 32, 77, 117, 108, 44, 32, 97, 114, 103, 58, 32]
  | .div => #[65, 112, 112, 108, 121, 32, 123, 32, 111, 112, 58, 32, 68, 105, 118, 44, 32, 97, 114, 103, 58, 32]

/-- The bytes that identify a command under an idempotency key: `Set { value: 6 }`,
`Apply { op: Mul, arg: 7 }`, `Get`. -/
def fingerprint : Command → Array UInt8
  | .set value =>
    ((Json.pushDecimal #[83, 101, 116, 32, 123, 32, 118, 97, 108, 117, 101, 58, 32]
      value.toNat).push 32).push 125
  | .apply op arg => ((Json.pushDecimal (opFingerprint op) arg.toNat).push 32).push 125
  | .get => #[71, 101, 116]

/-- `u<user>`: the keys of one user of a tenant. -/
def scope (actor : Principal) : String :=
  "u" ++ toString actor.user.toNat

end Calculator.Wire
