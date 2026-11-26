import Leangage.Token

/-!
# JSON input

A server reads the text of a request body with the JSON library of its language and hands over
the tokens of the text in the order of the document, each a `Lexeme`: a number as the text of its
token, a string and a key as text, a member twice as two members. `items` takes them to the
`Item`s the kernels' functions decide on.

`numberItem` reads a number token: decimal digits without a sign, a fraction or an exponent that
spell a value below 2^64 without a leading zero are `num`, every other text is `number`. A string
and a key become the bytes of their UTF-8.
-/

namespace Leangage.Json.Items

/-- One token of a JSON text as the kernels' functions read it. -/
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

/-- One token of a JSON text as a JSON library hands it over. -/
inductive Lexeme where
  | null
  | bool (b : Bool)
  /-- A number, as the text of its token. -/
  | number (text : String)
  | str (s : String)
  | key (s : String)
  | arrOpen
  | arrClose
  | objOpen
  | objClose
deriving DecidableEq, Repr

/-- The item of a number token. -/
def numberItem (text : String) : Item :=
  match Token.numberAt text 0 text.utf8ByteSize with
  | some n => .num n
  | none => .number

/-- The item of a token. -/
def item : Lexeme → Item
  | .null => .null
  | .bool b => .bool b
  | .number text => numberItem text
  | .str s => .str s.toByteArray.data.toList
  | .key s => .key s.toByteArray.data.toList
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

/-- The items of the tokens of a JSON text. -/
def items (lexemes : List Lexeme) : List Item :=
  lexemes.map item

end Leangage.Json.Items
