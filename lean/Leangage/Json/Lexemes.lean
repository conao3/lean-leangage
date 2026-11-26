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

/-- Whether the character is the kind of a token. -/
def isKind (c : Char) : Bool :=
  c = '{' || c = '}' || c = '[' || c = ']' || c = 'n' || c = 't' || c = 'f' || c = '#' || c = 's' ||
    c = 'k'

/-- Whether the kind is that of a token with a text: a number, a string or a key. -/
def hasText (c : Char) : Bool :=
  c = '#' || c = 's' || c = 'k'

/-- The characters before the first `stop` and those after it. -/
def splitAt (stop : Char) : List Char → Option (List Char × List Char)
  | [] => none
  | c :: cs =>
    if c = stop then some ([], cs)
    else
      match splitAt stop cs with
      | some (before, after) => some (c :: before, after)
      | none => none

/-- The number that decimal digits spell. -/
def lengthOf (digits : List Char) : Nat :=
  digits.foldl (fun acc c => acc * 10 + (c.toNat - 48)) 0

/-- The given count of texts in the characters: each text but the last comes after the count of
its characters in decimal and a colon, and the last text is the characters that are left. -/
def texts : Nat → List Char → Option (List String)
  | 0, cs => if cs.isEmpty then some [] else none
  | 1, cs => some [String.ofList cs]
  | count + 2, cs =>
    match splitAt ':' cs with
    | none => none
    | some (digits, rest) =>
      let length := lengthOf digits
      if digits = Nat.toDigits 10 length ∧ length ≤ rest.length then
        match texts (count + 1) (rest.drop length) with
        | some ts => some (String.ofList (rest.take length) :: ts)
        | none => none
      else none

/-- The tokens of a packed text: the kinds of the tokens, a line feed, and the texts of the
numbers, the strings and the keys as `texts` reads them. `none` for a text that no list of tokens
is packed to. -/
def unpack (packed : String) : Option (List Lexeme) :=
  match splitAt '\n' packed.toList with
  | none => none
  | some (kinds, rest) =>
    if kinds.all isKind then
      match texts (kinds.countP hasText) rest with
      | some ts => some (zip kinds ts)
      | none => none
    else none

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
