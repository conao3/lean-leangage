import Leanharbor.Token

/-!
# JSON output

Based on `crates/h5i-app-json/src/lib.rs` and `crates/h5i-app-json/proofs/JsonSpec.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the functions are written
in Lean and generated to the shells; bytes are a `List UInt8` and numbers are `UInt64`s; the
decimal and hexadecimal digits are those of `Leanharbor.Token`; the loop over the tokens keeps
what it has written, reversed, in an accumulator.

A document is a list of `Tok`s. `write` adds the commas and the colons: a comma goes before a
token that follows a value and does not close an array or an object, and `key` writes its colon.
In a string, `"` and `\` get a backslash, bytes below 0x20 become `\u00XX` with lowercase
hexadecimal, and every other byte passes through, so UTF-8 in gives UTF-8 out.
-/

namespace Leanharbor.Json

/-- One JSON token. `key` is the name of an object's member. -/
inductive Tok where
  | null
  | bool (b : Bool)
  | num (n : UInt64)
  | str (s : List UInt8)
  | key (s : List UInt8)
  | arrOpen
  | arrClose
  | objOpen
  | objClose
deriving DecidableEq, Repr

/-- One byte of a string, escaped. -/
def escapeByte (c : UInt8) : List UInt8 :=
  if c = 34 then [92, 34]
  else if c = 92 then [92, 92]
  else if c < 32 then
    [92, 117, 48, 48, Token.hexDigit (c.toNat / 16), Token.hexDigit (c.toNat % 16)]
  else [c]

/-- The bytes of a string between its quotes. -/
def escape (s : List UInt8) : List UInt8 :=
  s.flatMap escapeByte

/-- A token without the comma before it. -/
def tokBytes : Tok → List UInt8
  | .null => [110, 117, 108, 108]
  | .bool true => [116, 114, 117, 101]
  | .bool false => [102, 97, 108, 115, 101]
  | .num n => Token.decimal n.toNat
  | .str s => 34 :: escape s ++ [34]
  | .key s => 34 :: escape s ++ [34, 58]
  | .arrOpen => [91]
  | .arrClose => [93]
  | .objOpen => [123]
  | .objClose => [125]

/-- Whether a comma goes before the next token that does not close. -/
def endsValue : Tok → Bool
  | .null | .bool _ | .num _ | .str _ | .arrClose | .objClose => true
  | .key _ | .arrOpen | .objOpen => false

def isClose : Tok → Bool
  | .arrClose | .objClose => true
  | _ => false

/-- The reversed `acc`, then the tokens; `afterValue` says whether the token before them ended a
value. -/
def writeFrom (acc : List UInt8) (afterValue : Bool) : List Tok → List UInt8
  | [] => acc.reverse
  | t :: ts =>
    let piece := (if afterValue && !isClose t then [44] else []) ++ tokBytes t
    writeFrom (piece.reverseAux acc) (endsValue t) ts

/-- The bytes of a document. -/
def write (ts : List Tok) : List UInt8 :=
  writeFrom [] false ts

end Leanharbor.Json
