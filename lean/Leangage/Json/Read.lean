import Leangage.Json

/-!
# JSON input

`read` reads the bytes of a JSON text (RFC 8259) into a list of `Item`s, the tokens of
`Leangage.Json.Tok` and one more for a number that is not the decimal of a `UInt64`. It is one
loop over the bytes: `step` takes the state and a byte to the next state, and `finish` gives the
items when the bytes ended a document. The state holds the place in the grammar (`At`), what is
read of the string or the number the loop is in, the open arrays and objects, innermost first,
and the items read so far, last first. Nothing recurses on the nesting of the text, so a deep text
grows the state and not the call stack.

A number written as decimal digits without a sign, a fraction or an exponent and below 2^64 is
read as `num`; every other number of the grammar is read as `number`. A string is read as its
bytes: an escape as the UTF-8 of its character, a `\u` pair of surrogates as the UTF-8 of the
character the pair encodes, every other byte of 0x20 and above as itself. A `\u` escape of a
surrogate outside such a pair is refused.

`readString`, which the servers' functions call, runs the same loop over the bytes of a `String`
by index. `Leangage.Json.Read.Proofs` proves it equal to `read` of the bytes of the string.
-/

namespace Leangage.Json.Read

/-- One token of a JSON text as it is read. -/
inductive Item where
  | null
  | bool (b : Bool)
  | num (n : UInt64)
  /-- A number that is not the decimal of a `UInt64`: signed, with a fraction or an exponent, or
  2^64 and above. -/
  | number
  | str (s : List UInt8)
  | key (s : List UInt8)
  | arrOpen
  | arrClose
  | objOpen
  | objClose
deriving DecidableEq, Repr

/-- The place in the grammar after the bytes read so far. -/
inductive At where
  /-- A value comes next. -/
  | value
  /-- After `[`: a value or `]`. -/
  | first
  /-- After a comma in an object: a key. -/
  | key
  /-- After `{`: a key or `}`. -/
  | firstKey
  /-- After a key: a colon. -/
  | colon
  /-- After a value: a comma or the close of the innermost array or object. -/
  | next
  /-- In `true`, `false` and `null`. -/
  | litTrue
  | litFalse
  | litNull
  /-- In a string. -/
  | str
  /-- After a backslash. -/
  | esc
  /-- In the 4 hexadecimal digits of `\u`. -/
  | hex
  /-- After the escape of a high surrogate: a backslash. -/
  | lowEsc
  /-- After that backslash: `u`. -/
  | lowU
  /-- After `-`: a digit. -/
  | minus
  /-- After `0` or `-0`. -/
  | zero
  /-- In the digits of the integer part. -/
  | int
  /-- After the point: a digit. -/
  | dot
  | frac
  /-- After `e` or `E`: a sign or a digit. -/
  | exp
  /-- After the sign of the exponent: a digit. -/
  | expSign
  | expDigits
  /-- The bytes read are not the start of a JSON text. -/
  | bad
deriving DecidableEq, Repr

/-- The state of the loop. Between two tokens, every field but `place`, `nest` and `out` has the
value it has in `clean`. -/
structure State where
  place : At
  /-- The string being read is a key. -/
  isKey : Bool
  /-- The number being read has a minus sign. -/
  neg : Bool
  /-- In an integer part: the value of its digits while there are at most 20. In a `\u` escape:
  the value of the digits read. -/
  n : Nat
  /-- In an integer part: the count of its digits. In a `\u` escape: the digits still to come. -/
  len : Nat
  /-- The high surrogate of the `\u` escape before, or 0. -/
  high : Nat
  /-- The bytes of `true`, `false` or `null` still to come. -/
  pending : List UInt8
  /-- The bytes of the string being read. -/
  acc : Array UInt8
  /-- `true` for each open object and `false` for each open array, innermost first. -/
  nest : List Bool
  /-- The items read, last first. -/
  out : List Item
deriving DecidableEq, Repr

/-- The state between two tokens. -/
@[inline] def clean (place : At) (nest : List Bool) (out : List Item) : State :=
  ⟨place, false, false, 0, 0, 0, [], #[], nest, out⟩

def start : State := clean .value [] []

@[inline] def isWs (c : UInt8) : Bool :=
  c = 32 || c = 9 || c = 10 || c = 13

@[inline] def isDigit (c : UInt8) : Bool :=
  48 ≤ c && c ≤ 57

/-- The value of a hexadecimal digit of either case, or 16. -/
@[inline] def hexVal (c : UInt8) : Nat :=
  if 48 ≤ c && c ≤ 57 then c.toNat - 48
  else if 97 ≤ c && c ≤ 102 then c.toNat - 87
  else if 65 ≤ c && c ≤ 70 then c.toNat - 55
  else 16

/-- `acc` followed by the UTF-8 of the character `n`. -/
def pushUtf8 (n : Nat) (acc : Array UInt8) : Array UInt8 :=
  if n < 0x80 then acc.push n.toUInt8
  else if n < 0x800 then (acc.push (0xC0 + n / 64).toUInt8).push (0x80 + n % 64).toUInt8
  else if n < 0x10000 then
    ((acc.push (0xE0 + n / 4096).toUInt8).push (0x80 + n / 64 % 64).toUInt8).push
      (0x80 + n % 64).toUInt8
  else
    (((acc.push (0xF0 + n / 262144).toUInt8).push (0x80 + n / 4096 % 64).toUInt8).push
      (0x80 + n / 64 % 64).toUInt8).push (0x80 + n % 64).toUInt8

/-- The state after the item `i` that ends a value. -/
@[inline] def emit (st : State) (i : Item) : State :=
  clean .next st.nest (i :: st.out)

/-- The first byte of a value. -/
@[noinline] def startValue (st : State) (c : UInt8) : State :=
  if c = 34 then { st with place := .str }
  else if c = 123 then clean .firstKey (true :: st.nest) (.objOpen :: st.out)
  else if c = 91 then clean .first (false :: st.nest) (.arrOpen :: st.out)
  else if c = 116 then { st with place := .litTrue, pending := [114, 117, 101] }
  else if c = 102 then { st with place := .litFalse, pending := [97, 108, 115, 101] }
  else if c = 110 then { st with place := .litNull, pending := [117, 108, 108] }
  else if c = 45 then { st with place := .minus, neg := true }
  else if c = 48 then { st with place := .zero }
  else if isDigit c then { st with place := .int, n := c.toNat - 48, len := 1 }
  else { st with place := .bad }

/-- The byte after a value. -/
@[noinline] def afterValue (st : State) (c : UInt8) : State :=
  if isWs c then st
  else
    match st.nest with
    | [] => { st with place := .bad }
    | true :: rest =>
      if c = 44 then { st with place := .key }
      else if c = 125 then clean .next rest (.objClose :: st.out)
      else { st with place := .bad }
    | false :: rest =>
      if c = 44 then { st with place := .value }
      else if c = 93 then clean .next rest (.arrClose :: st.out)
      else { st with place := .bad }

/-- The item of an integer part without a fraction or an exponent. -/
def intItem (neg : Bool) (n len : Nat) : Item :=
  if !neg && len ≤ 20 && n < 18446744073709551616 then .num n.toUInt64 else .number

/-- One more byte of `true`, `false` or `null`, which make `item`. -/
@[noinline] def stepLit (st : State) (item : Item) (c : UInt8) : State :=
  match st.pending with
  | [b] => if c = b then emit st item else { st with place := .bad }
  | b :: rest => if c = b then { st with pending := rest } else { st with place := .bad }
  | [] => { st with place := .bad }

/-- The state after the 4 digits of a `\u` escape that spell `code`. -/
@[noinline] def endHex (st : State) (code : Nat) : State :=
  if st.high = 0 then
    if 0xD800 ≤ code && code < 0xDC00 then { st with place := .lowEsc, n := 0, len := 0, high := code }
    else if 0xDC00 ≤ code && code < 0xE000 then { st with place := .bad }
    else { st with place := .str, n := 0, len := 0, acc := pushUtf8 code st.acc }
  else if 0xDC00 ≤ code && code < 0xE000 then
    { st with
      place := .str, n := 0, len := 0, high := 0,
      acc := pushUtf8 (0x10000 + (st.high - 0xD800) * 0x400 + (code - 0xDC00)) st.acc }
  else { st with place := .bad }

/-- One more byte where a value comes next. -/
@[noinline] def stepValue (st : State) (c : UInt8) : State :=
  if isWs c then st else startValue st c

/-- One more byte after `[`. -/
@[noinline] def stepFirst (st : State) (c : UInt8) : State :=
  if isWs c then st
  else if c = 93 then
    match st.nest with
    | false :: rest => clean .next rest (.arrClose :: st.out)
    | _ => { st with place := .bad }
  else startValue st c

/-- One more byte where a key comes next; `first` says that `}` may come instead. -/
@[noinline] def stepKey (st : State) (first : Bool) (c : UInt8) : State :=
  if isWs c then st
  else if c = 34 then { st with place := .str, isKey := true }
  else if first && c = 125 then
    match st.nest with
    | true :: rest => clean .next rest (.objClose :: st.out)
    | _ => { st with place := .bad }
  else { st with place := .bad }

/-- One more byte after a key. -/
@[noinline] def stepColon (st : State) (c : UInt8) : State :=
  if isWs c then st else if c = 58 then { st with place := .value } else { st with place := .bad }

/-- One more byte in a string. -/
@[noinline] def stepStr (st : State) (c : UInt8) : State :=
  if c = 34 then
    if st.isKey then clean .colon st.nest (.key st.acc.toList :: st.out)
    else emit st (.str st.acc.toList)
  else if c = 92 then { st with place := .esc }
  else if c < 32 then { st with place := .bad }
  else { st with acc := st.acc.push c }

/-- The byte after a backslash. -/
@[noinline] def stepEsc (st : State) (c : UInt8) : State :=
  if c = 34 then { st with place := .str, acc := st.acc.push 34 }
  else if c = 92 then { st with place := .str, acc := st.acc.push 92 }
  else if c = 47 then { st with place := .str, acc := st.acc.push 47 }
  else if c = 98 then { st with place := .str, acc := st.acc.push 8 }
  else if c = 102 then { st with place := .str, acc := st.acc.push 12 }
  else if c = 110 then { st with place := .str, acc := st.acc.push 10 }
  else if c = 114 then { st with place := .str, acc := st.acc.push 13 }
  else if c = 116 then { st with place := .str, acc := st.acc.push 9 }
  else if c = 117 then { st with place := .hex, n := 0, len := 4 }
  else { st with place := .bad }

/-- One more of the 4 digits of a `\u` escape. -/
@[noinline] def stepHex (st : State) (c : UInt8) : State :=
  if hexVal c < 16 then
    if st.len ≤ 1 then endHex st (st.n * 16 + hexVal c)
    else { st with n := st.n * 16 + hexVal c, len := st.len - 1 }
  else { st with place := .bad }

/-- The byte after `0` or `-0`. -/
@[noinline] def stepZero (st : State) (c : UInt8) : State :=
  if c = 46 then { st with place := .dot }
  else if c = 101 || c = 69 then { st with place := .exp }
  else if isDigit c then { st with place := .bad }
  else afterValue (emit st (intItem st.neg 0 1)) c

/-- One more byte in the digits of the integer part. -/
@[noinline] def stepInt (st : State) (c : UInt8) : State :=
  if isDigit c then
    { st with n := if st.len < 20 then st.n * 10 + (c.toNat - 48) else st.n, len := st.len + 1 }
  else if c = 46 then { st with place := .dot }
  else if c = 101 || c = 69 then { st with place := .exp }
  else afterValue (emit st (intItem st.neg st.n st.len)) c

/-- One more byte in the digits of the fraction (`exp` is `false`) or of the exponent. -/
@[noinline] def stepDigits (st : State) (exp : Bool) (c : UInt8) : State :=
  if isDigit c then st
  else if !exp && (c = 101 || c = 69) then { st with place := .exp }
  else afterValue (emit st .number) c

/-- The state after one more byte. -/
def step (st : State) (c : UInt8) : State :=
  match st.place with
  | .value => stepValue st c
  | .first => stepFirst st c
  | .key => stepKey st false c
  | .firstKey => stepKey st true c
  | .colon => stepColon st c
  | .next => afterValue st c
  | .litTrue => stepLit st (.bool true) c
  | .litFalse => stepLit st (.bool false) c
  | .litNull => stepLit st .null c
  | .str => stepStr st c
  | .esc => stepEsc st c
  | .hex => stepHex st c
  | .lowEsc => if c = 92 then { st with place := .lowU } else { st with place := .bad }
  | .lowU =>
    if c = 117 then { st with place := .hex, n := 0, len := 4 } else { st with place := .bad }
  | .minus =>
    if c = 48 then { st with place := .zero }
    else if isDigit c then { st with place := .int, len := 1 }
    else { st with place := .bad }
  | .zero => stepZero st c
  | .int => stepInt st c
  | .dot => if isDigit c then { st with place := .frac } else { st with place := .bad }
  | .frac => stepDigits st false c
  | .exp =>
    if c = 43 || c = 45 then { st with place := .expSign }
    else if isDigit c then { st with place := .expDigits }
    else { st with place := .bad }
  | .expSign => if isDigit c then { st with place := .expDigits } else { st with place := .bad }
  | .expDigits => stepDigits st true c
  | .bad => st

/-- The items read, when the bytes read are a JSON text. -/
def finish (st : State) : Option (List Item) :=
  match st.nest with
  | [] =>
    match st.place with
    | .next => some st.out.reverse
    | .zero => some (intItem st.neg 0 1 :: st.out).reverse
    | .int => some (intItem st.neg st.n st.len :: st.out).reverse
    | .frac | .expDigits => some (.number :: st.out).reverse
    | _ => none
  | _ => none

/-- The items of a JSON text, or `none` for bytes that are not one. -/
def read (l : List UInt8) : Option (List Item) :=
  finish (l.foldl step start)

/-- The state after the bytes of `s` from `i` on. -/
def stepFrom (s : String) (i : Nat) (st : State) : State :=
  if h : i < s.utf8ByteSize then stepFrom s (i + 1) (step st (s.getUTF8Byte ⟨i⟩ h)) else st
termination_by s.utf8ByteSize - i

/-- `read` of the bytes of `s`. -/
def readString (s : String) : Option (List Item) :=
  finish (stepFrom s 0 start)

end Leangage.Json.Read
