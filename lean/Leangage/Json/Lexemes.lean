import Leangage.Token

/-!
# JSON input

A server reads the text of a request body with the JSON library of its language and hands over
the tokens of the text in the order of the document, a member twice as two members, as `Tokens`:
one character for the kind of each token (`{`, `}`, `[`, `]`, `n` for null, `t` and `f` for true
and false, `#` for a number, `s` for a string, `k` for a key) and the texts of the numbers, the
strings and the keys. `Tokens.lexemes` gives the tokens one by one, each a `Lexeme`: a number as
the text of its token, a string and a key as text.

`numberOf` reads a number token: decimal digits without a sign, a fraction or an exponent that
spell a value below 2^64 without a leading zero are that value, and every other text is no value.
`object` gives the members of an object whose values are not arrays or objects, each value a
`Scalar`, in the order of the document. The kernels' functions decide on those members.
-/

namespace Leangage.Json.Lexemes

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

/-- A value that is not an array or an object. -/
inductive Scalar where
  | null
  | bool (b : Bool)
  | num (n : UInt64)
  /-- A number that is not the decimal of a `UInt64`: signed, with a fraction or an exponent, or
  2^64 and above. -/
  | number
  | str (s : String)
deriving DecidableEq, Repr

/-- The tokens of a JSON text as a server's conversion hands them over: one character for each
token, and the texts of the numbers, the strings and the keys, in the order of the document. -/
structure Tokens where
  kinds : String
  texts : List String
deriving DecidableEq, Repr

/-- The tokens with the given kinds, the texts taken in order: a kind that is none of the others
is a number, and a number, a string or a key without a text left is no token. -/
def zip : List Char → List String → List Lexeme
  | [], _ => []
  | c :: cs, texts =>
    if c = '{' then .objOpen :: zip cs texts
    else if c = '}' then .objClose :: zip cs texts
    else if c = '[' then .arrOpen :: zip cs texts
    else if c = ']' then .arrClose :: zip cs texts
    else if c = 'n' then .null :: zip cs texts
    else if c = 't' then .bool true :: zip cs texts
    else if c = 'f' then .bool false :: zip cs texts
    else
      match texts with
      | [] => zip cs []
      | text :: rest =>
        if c = 'k' then .key text :: zip cs rest
        else if c = 's' then .str text :: zip cs rest
        else .number text :: zip cs rest

/-- The tokens, one by one. -/
def Tokens.lexemes (tokens : Tokens) : List Lexeme :=
  zip tokens.kinds.toList tokens.texts

/-- The value of a number token whose text is the decimal of a `UInt64`. -/
def numberOf (text : String) : Option UInt64 :=
  Token.numberAt text 0 text.utf8ByteSize

/-- The value of a token that is a value by itself. -/
def scalar : Lexeme → Option Scalar
  | .null => some .null
  | .bool b => some (.bool b)
  | .number text =>
    match numberOf text with
    | some n => some (.num n)
    | none => some .number
  | .str s => some (.str s)
  | .key _ | .arrOpen | .arrClose | .objOpen | .objClose => none

/-- The members of an object after its `{`, when no value is an array or an object; `acc` holds
those read, last first. -/
def members (acc : List (String × Scalar)) : List Lexeme → Option (List (String × Scalar))
  | [.objClose] => some acc.reverse
  | .key k :: v :: rest =>
    match scalar v with
    | some x => members ((k, x) :: acc) rest
    | none => none
  | _ => none

/-- The members of the object that the tokens of a JSON text are. -/
def object : List Lexeme → Option (List (String × Scalar))
  | .objOpen :: rest => members [] rest
  | _ => none

end Leangage.Json.Lexemes
