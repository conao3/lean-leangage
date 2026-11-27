import Leangage.Token

/-!
# JSON output

Based on `crates/h5i-app-json/src/lib.rs` and `crates/h5i-app-json/proofs/JsonSpec.lean` of h5i
(https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the functions are written
in Lean and generated to the three languages; bytes are a `List UInt8` and numbers are `UInt64`s; the five
control bytes that JSON has a short escape for are written with it; the decimal and hexadecimal
digits are those of `Leangage.Token`; the loop over the tokens keeps what it has written,
reversed, in an accumulator; `writeArray` takes strings as `String`s and writes into an array.

A document is a list of `Tok`s. `write` adds the commas and the colons: a comma goes before a
token that follows a value and does not close an array or an object, and `key` writes its colon.
In a string, `"` and `\` get a backslash, backspace, form feed, line feed, carriage return and tab
become `\b`, `\f`, `\n`, `\r` and `\t`, the other bytes below 0x20 become `\u00XX` with lowercase
hexadecimal, and every other byte passes through, so UTF-8 in gives UTF-8 out. These are the
escapes `serde_json` writes.
-/

namespace Leangage.Json

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
  else if c = 8 then [92, 98]
  else if c = 12 then [92, 102]
  else if c = 10 then [92, 110]
  else if c = 13 then [92, 114]
  else if c = 9 then [92, 116]
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

/-! ## Into an array

`writeArray` writes the same bytes as `write` into an `Array UInt8`, from tokens whose strings are
`String`s, so a server passes strings without building lists. `Leangage.Json.Proofs` proves it
equal to `write`.
-/

/-- One JSON token whose strings are `String`s. -/
inductive StrTok where
  | null
  | bool (b : Bool)
  | num (n : UInt64)
  | str (s : String)
  | key (s : String)
  | arrOpen
  | arrClose
  | objOpen
  | objClose
deriving DecidableEq, Repr

/-- `acc` followed by `escapeByte c`. -/
def pushEscapedByte (acc : Array UInt8) (c : UInt8) : Array UInt8 :=
  if 32 ≤ c && c ≠ 34 && c ≠ 92 then acc.push c
  else if c = 34 then (acc.push 92).push 34
  else if c = 92 then (acc.push 92).push 92
  else if c = 8 then (acc.push 92).push 98
  else if c = 12 then (acc.push 92).push 102
  else if c = 10 then (acc.push 92).push 110
  else if c = 13 then (acc.push 92).push 114
  else if c = 9 then (acc.push 92).push 116
  else if c < 32 then
    (((((acc.push 92).push 117).push 48).push 48).push (Token.hexDigit (c.toNat / 16))).push
      (Token.hexDigit (c.toNat % 16))
  else acc.push c

/-- `acc` followed by the bytes of `s` from `i` on, escaped. -/
def pushEscaped (s : String) (i : Nat) (acc : Array UInt8) : Array UInt8 :=
  if h : i < s.utf8ByteSize then pushEscaped s (i + 1) (pushEscapedByte acc (s.getUTF8Byte ⟨i⟩ h))
  else acc
termination_by s.utf8ByteSize - i

/-- `acc` followed by `Token.decimal n`. -/
def pushDecimal (acc : Array UInt8) (n : Nat) : Array UInt8 :=
  if n < 10 then acc.push (n + 48).toUInt8
  else (pushDecimal acc (n / 10)).push (n % 10 + 48).toUInt8
termination_by n
decreasing_by omega

/-- `acc` followed by a token without the comma before it. -/
def pushTok (acc : Array UInt8) : StrTok → Array UInt8
  | .null => (((acc.push 110).push 117).push 108).push 108
  | .bool true => (((acc.push 116).push 114).push 117).push 101
  | .bool false => ((((acc.push 102).push 97).push 108).push 115).push 101
  | .num n => pushDecimal acc n.toNat
  | .str s => (pushEscaped s 0 (acc.push 34)).push 34
  | .key s => ((pushEscaped s 0 (acc.push 34)).push 34).push 58
  | .arrOpen => acc.push 91
  | .arrClose => acc.push 93
  | .objOpen => acc.push 123
  | .objClose => acc.push 125

/-- Whether a comma goes before the next token that does not close. -/
def StrTok.endsValue : StrTok → Bool
  | .null | .bool _ | .num _ | .str _ | .arrClose | .objClose => true
  | .key _ | .arrOpen | .objOpen => false

def StrTok.isClose : StrTok → Bool
  | .arrClose | .objClose => true
  | _ => false

/-- `acc`, then the tokens; `afterValue` says whether the token before them ended a value. -/
def writeArrayFrom (acc : Array UInt8) (afterValue : Bool) : List StrTok → Array UInt8
  | [] => acc
  | t :: ts =>
    let acc := if afterValue && !t.isClose then acc.push 44 else acc
    writeArrayFrom (pushTok acc t) t.endsValue ts

/-- The bytes of a document, as `write` writes them. -/
def writeArray (ts : List StrTok) : Array UInt8 :=
  writeArrayFrom (.emptyWithCapacity 64) false ts

end Leangage.Json
