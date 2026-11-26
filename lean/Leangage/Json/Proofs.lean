import Leangage.Json
import Leangage.Token.Proofs

/-!
# What the JSON writer guarantees

Based on `crates/h5i-app-json/proofs/JsonSpec.lean` and `crates/h5i-app-json/proofs/JsonProofs.lean`
of h5i (https://github.com/h5i-dev/h5i, commit 515c7b9, Apache-2.0). Changed: the statements are
about the generated functions over `List UInt8` and `UInt64`, so they need no bound on the
length of the output; the printer of the specification also prints a tree of JSON values, and
`write_value` ties the writer to it; numbers are specified by `Nat.toDigits`; the proofs use no
Mathlib; the five control bytes that JSON has a short escape for are written with it.

- `write_spec`: `write` of any list of tokens is `printToks` of it, the printer over tokens of
  the specification.
- `write_value`: `write` of the tokens of a JSON value is `Value.print` of the value, which prints
  the tree directly.
- `lex_escape`: a JSON string lexer reading `escape s` followed by a quote returns `s` and stops
  at that quote, whatever follows. So no byte of `s` ends the string early.
- `escape_no_control`: `escape s` has no byte below 0x20.

- `writeArray_spec`: `writeArray`, which the shells call, writes into an array the bytes that
  `write` writes for the tokens its tokens over strings stand for (`StrTok.toTok`, the bytes of
  each string). `writeArray_value` is `write_value` for it.

`escapeByte_spec`, `escape_spec`, `tokBytes_spec`, `isClose_spec`, `endsValue_spec` and
`writeFrom_spec` restate the generated functions in other terms, as `pushEscapedByte_spec`,
`pushEscaped_spec`, `pushDecimal_spec`, `pushTok_spec` and `writeArrayFrom_spec` do for the
functions into an array.
-/

namespace Leangage.Json

open Leangage.Token (hexChars)

/-! ## The specification -/

/-- The bytes of ASCII characters. -/
def ascii (cs : List Char) : List UInt8 :=
  cs.map fun c => c.toNat.toUInt8

/-- `n` in decimal: the characters of `Nat.repr n`. -/
def digits (n : Nat) : List UInt8 :=
  ascii (Nat.toDigits 10 n)

def escByte (c : UInt8) : List UInt8 :=
  if c = 34 then ascii ['\\', '"']
  else if c = 92 then ascii ['\\', '\\']
  else if c = 8 then ascii ['\\', 'b']
  else if c = 12 then ascii ['\\', 'f']
  else if c = 10 then ascii ['\\', 'n']
  else if c = 13 then ascii ['\\', 'r']
  else if c = 9 then ascii ['\\', 't']
  else if c.toNat < 32 then
    ascii ['\\', 'u', '0', '0'] ++ [hexChars.getD (c.toNat / 16) 0, hexChars.getD (c.toNat % 16) 0]
  else [c]

def esc (s : List UInt8) : List UInt8 :=
  s.flatMap escByte

def quote (s : List UInt8) : List UInt8 :=
  34 :: esc s ++ [34]

def text : Tok → List UInt8
  | .null => ascii ['n', 'u', 'l', 'l']
  | .bool true => ascii ['t', 'r', 'u', 'e']
  | .bool false => ascii ['f', 'a', 'l', 's', 'e']
  | .num n => digits n.toNat
  | .str s => quote s
  | .key s => quote s ++ ascii [':']
  | .arrOpen => ascii ['[']
  | .arrClose => ascii [']']
  | .objOpen => ascii ['{']
  | .objClose => ascii ['}']

def closes : Tok → Bool
  | .arrClose | .objClose => true
  | _ => false

def ends : Tok → Bool
  | .null | .bool _ | .num _ | .str _ | .arrClose | .objClose => true
  | _ => false

/-- The tokens after one that ended a value (`afterValue`) or not: a comma goes before a token
that follows a value and does not close. -/
def printFrom (afterValue : Bool) : List Tok → List UInt8
  | [] => []
  | t :: ts => (if afterValue && !closes t then ascii [','] else []) ++ text t ++ printFrom (ends t) ts

def printToks (ts : List Tok) : List UInt8 :=
  printFrom false ts

/-- A JSON value. -/
inductive Value where
  | null
  | bool (b : Bool)
  | num (n : UInt64)
  | str (s : List UInt8)
  | arr (vs : List Value)
  | obj (ms : List (List UInt8 × Value))

mutual
/-- A value printed directly from the tree. -/
def Value.print : Value → List UInt8
  | .null => ascii ['n', 'u', 'l', 'l']
  | .bool true => ascii ['t', 'r', 'u', 'e']
  | .bool false => ascii ['f', 'a', 'l', 's', 'e']
  | .num n => digits n.toNat
  | .str s => quote s
  | .arr vs => ascii ['['] ++ printElems vs ++ ascii [']']
  | .obj ms => ascii ['{'] ++ printMembers ms ++ ascii ['}']

/-- Values separated by commas. -/
def printElems : List Value → List UInt8
  | [] => []
  | [v] => v.print
  | v :: vs => v.print ++ ascii [','] ++ printElems vs

/-- Members `"<key>":<value>` separated by commas. -/
def printMembers : List (List UInt8 × Value) → List UInt8
  | [] => []
  | [(k, v)] => quote k ++ ascii [':'] ++ v.print
  | (k, v) :: ms => quote k ++ ascii [':'] ++ v.print ++ ascii [','] ++ printMembers ms
end

mutual
/-- The tokens of a value. -/
def Value.toks : Value → List Tok
  | .null => [.null]
  | .bool b => [.bool b]
  | .num n => [.num n]
  | .str s => [.str s]
  | .arr vs => .arrOpen :: elemsToks vs ++ [.arrClose]
  | .obj ms => .objOpen :: membersToks ms ++ [.objClose]

def elemsToks : List Value → List Tok
  | [] => []
  | v :: vs => v.toks ++ elemsToks vs

def membersToks : List (List UInt8 × Value) → List Tok
  | [] => []
  | (k, v) :: ms => .key k :: v.toks ++ membersToks ms
end

/-- The value of a hexadecimal digit of either case. -/
def unhexDigit (c : UInt8) : Option Nat :=
  if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c.toNat ∧ c.toNat ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c.toNat ∧ c.toNat ≤ 70 then some (c.toNat - 55)
  else none

/-- A JSON string lexer from after the opening quote: the bytes of the string and what follows its
closing quote. `\uXXXX` is read when it is below 0x80. -/
def lexStr : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | c :: r =>
    if c = 34 then some ([], r)
    else if c = 92 then
      match r with
      | e :: r' =>
        let short : Option UInt8 :=
          if e = 34 then some 34 else if e = 92 then some 92 else if e = 47 then some 47
          else if e = 98 then some 8 else if e = 102 then some 12 else if e = 110 then some 10
          else if e = 114 then some 13 else if e = 116 then some 9 else none
        match short with
        | some v => (lexStr r').map fun p => (v :: p.1, p.2)
        | none =>
          if e = 117 then
            match r' with
            | a :: b :: x :: y :: r'' =>
              match unhexDigit a, unhexDigit b, unhexDigit x, unhexDigit y with
              | some a, some b, some x, some y =>
                let v := ((a * 16 + b) * 16 + x) * 16 + y
                if v < 128 then (lexStr r'').map fun p => (v.toUInt8 :: p.1, p.2) else none
              | _, _, _, _ => none
            | _ => none
          else none
      | [] => none
    else if c.toNat < 32 then none
    else (lexStr r).map fun p => (c :: p.1, p.2)
termination_by l => l.length

/-! ## The pieces, restated -/

theorem escapeByte_spec (c : UInt8) : escapeByte c = escByte c := by
  have h : ∀ n, n < 256 → escapeByte n.toUInt8 = escByte n.toUInt8 := by decide +kernel
  simpa using h c.toNat c.toNat_lt

theorem escape_spec (s : List UInt8) : escape s = esc s := by
  simp [escape, esc, funext escapeByte_spec]

theorem decimal_spec (n : Nat) : Token.decimal n = digits n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hd : ∀ d, d < 10 → ((Nat.digitChar d).toNat).toUInt8 = (d + 48).toUInt8 := by decide
    rw [digits, ascii, Nat.toDigits_eq_ite (by decide)]
    by_cases h : n < 10
    · simp [Token.decimal_lt h, h, hd n h]
    · simp [Token.decimal_ge h, h, ih (n / 10) (by omega), digits, ascii,
        hd (n % 10) (Nat.mod_lt _ (by decide))]

theorem tokBytes_spec (t : Tok) : tokBytes t = text t := by
  cases t with
  | bool b => cases b <;> rfl
  | num n => simp [tokBytes, text, decimal_spec]
  | str s => simp [tokBytes, text, quote, escape_spec]
  | key s => simp [tokBytes, text, quote, escape_spec, ascii]
  | _ => rfl

theorem isClose_spec (t : Tok) : isClose t = closes t := by
  cases t <;> rfl

theorem endsValue_spec (t : Tok) : endsValue t = ends t := by
  cases t <;> rfl

theorem writeFrom_spec (acc : List UInt8) (a : Bool) (ts : List Tok) :
    writeFrom acc a ts = acc.reverse ++ printFrom a ts := by
  induction ts generalizing acc a with
  | nil => simp [writeFrom, printFrom]
  | cons t ts ih =>
    rw [writeFrom, ih, printFrom, List.reverseAux_eq, tokBytes_spec, isClose_spec, endsValue_spec]
    simp [ascii]

/-! ## The writer prints the specification -/

/-- `write` prints any list of tokens as the printer over tokens does. -/
theorem write_spec (ts : List Tok) : write ts = printToks ts := by
  simp [write, printToks, writeFrom_spec]

/-- A comma, if the token before ended a value. -/
def comma (afterValue : Bool) : List UInt8 :=
  if afterValue then ascii [','] else []

theorem toks_ne_nil (v : Value) : ∃ t ts, v.toks = t :: ts ∧ closes t = false := by
  cases v <;> simp [Value.toks, closes]

mutual
theorem printFrom_toks (v : Value) (a : Bool) (rest : List Tok) :
    printFrom a (v.toks ++ rest) = comma a ++ v.print ++ printFrom true rest := by
  match v with
  | .null => cases a <;> simp [Value.toks, Value.print, printFrom, text, closes, ends, comma]
  | .bool b => cases a <;> cases b <;> simp [Value.toks, Value.print, printFrom, text, closes, ends, comma]
  | .num n => cases a <;> simp [Value.toks, Value.print, printFrom, text, closes, ends, comma]
  | .str s => cases a <;> simp [Value.toks, Value.print, printFrom, text, closes, ends, comma]
  | .arr vs =>
    rw [show (Value.arr vs).toks ++ rest = .arrOpen :: (elemsToks vs ++ .arrClose :: rest) by
      simp [Value.toks]]
    rw [printFrom.eq_2, printFrom_elemsToks]
    cases vs <;> cases a <;> simp [Value.print, printElems, printFrom, text, closes, ends, comma]
  | .obj ms =>
    rw [show (Value.obj ms).toks ++ rest = .objOpen :: (membersToks ms ++ .objClose :: rest) by
      simp [Value.toks]]
    rw [printFrom.eq_2, printFrom_membersToks]
    cases ms <;> cases a <;> simp [Value.print, printMembers, printFrom, text, closes, ends, comma]

theorem printFrom_elemsToks (vs : List Value) (a : Bool) (rest : List Tok) :
    printFrom a (elemsToks vs ++ rest) =
      if vs = [] then printFrom a rest else comma a ++ printElems vs ++ printFrom true rest := by
  match vs with
  | [] => simp [elemsToks]
  | [v] => simp [elemsToks, printElems, printFrom_toks v a rest]
  | v :: w :: vs =>
    have h := printFrom_elemsToks (w :: vs) true rest
    simp only [elemsToks, List.append_assoc] at h ⊢
    rw [printFrom_toks v a, h]
    simp [printElems, comma]

theorem printFrom_membersToks (ms : List (List UInt8 × Value)) (a : Bool) (rest : List Tok) :
    printFrom a (membersToks ms ++ rest) =
      if ms = [] then printFrom a rest else comma a ++ printMembers ms ++ printFrom true rest := by
  match ms with
  | [] => simp [membersToks]
  | [(k, v)] =>
    rw [show membersToks [(k, v)] ++ rest = .key k :: (v.toks ++ rest) by simp [membersToks]]
    rw [printFrom.eq_2]
    simp only [ends]
    rw [printFrom_toks v false rest]
    cases a <;> simp [printMembers, text, closes, comma]
  | (k, v) :: m :: ms =>
    have h := printFrom_membersToks (m :: ms) true rest
    rw [show membersToks ((k, v) :: m :: ms) ++ rest =
        .key k :: (v.toks ++ (membersToks (m :: ms) ++ rest)) by simp [membersToks]]
    rw [printFrom.eq_2]
    simp only [ends]
    rw [printFrom_toks v false, h]
    cases a <;> simp [printMembers, text, closes, comma]
end

/-- `write` of the tokens of a value prints the value as the printer over trees does. -/
theorem write_value (v : Value) : write v.toks = v.print := by
  have h := printFrom_toks v false []
  simp [comma, printFrom] at h
  rw [write_spec, printToks, h]

/-! ## Strings cannot end early -/

theorem unhexDigit_hexChars (d : Nat) (h : d < 16) : unhexDigit (hexChars.getD d 0) = some d := by
  revert d
  decide

theorem lexStr_short (e v : UInt8) (r : List UInt8)
    (h : (if e = 34 then some 34 else if e = 92 then some 92 else if e = 47 then some 47
      else if e = 98 then some 8 else if e = 102 then some 12 else if e = 110 then some 10
      else if e = 114 then some 13 else if e = 116 then some 9 else none) = some v) :
    lexStr (92 :: e :: r) = (lexStr r).map fun p => (v :: p.1, p.2) := by
  rw [lexStr.eq_def]
  simp only [show (92 : UInt8) ≠ 34 by decide, ite_false, ite_true]
  simp only [h]

/-- The lexer reads the escape of a byte as that byte. -/
theorem lexStr_escByte (c : UInt8) (r : List UInt8) :
    lexStr (escByte c ++ r) = (lexStr r).map fun p => (c :: p.1, p.2) := by
  by_cases h34 : c = 34
  · subst h34; exact lexStr_short 34 34 r (by decide)
  by_cases h92 : c = 92
  · subst h92; exact lexStr_short 92 92 r (by decide)
  by_cases h8 : c = 8
  · subst h8; exact lexStr_short 98 8 r (by decide)
  by_cases h12 : c = 12
  · subst h12; exact lexStr_short 102 12 r (by decide)
  by_cases h10 : c = 10
  · subst h10; exact lexStr_short 110 10 r (by decide)
  by_cases h13 : c = 13
  · subst h13; exact lexStr_short 114 13 r (by decide)
  by_cases h9 : c = 9
  · subst h9; exact lexStr_short 116 9 r (by decide)
  by_cases h32 : c.toNat < 32
  · have h1 : c.toNat / 16 < 16 := by omega
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    rw [show escByte c = ascii ['\\', 'u', '0', '0'] ++
        [hexChars.getD (c.toNat / 16) 0, hexChars.getD (c.toNat % 16) 0] by
      simp [escByte, h34, h92, h8, h12, h10, h13, h9, h32]]
    simp only [ascii, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [lexStr.eq_def]
    have h0 : unhexDigit 48 = some 0 := by decide
    have hu : ∀ e : UInt8, e.toNat = 117 →
        (if e = 34 then some (34 : UInt8) else if e = 92 then some 92 else if e = 47 then some 47
        else if e = 98 then some 8 else if e = 102 then some 12 else if e = 110 then some 10
        else if e = 114 then some 13 else if e = 116 then some 9 else none) = none := by
      intro e he
      have : e = 117 := UInt8.toNat_inj.mp he
      subst this; decide
    simp only [unhexDigit_hexChars _ h1, unhexDigit_hexChars _ h2]
    erw [h0]
    have hc : ∀ n, n < 32 → UInt8.ofNat (n / 16) * 16 + UInt8.ofNat (n % 16) = n.toUInt8 := by
      decide
    simp [hc c.toNat h32]
    omega
  · rw [show escByte c = [c] by simp [escByte, h34, h92, h8, h12, h10, h13, h9, h32]]
    rw [List.cons_append, lexStr.eq_def]
    simp [h34, h92, h32]

/-- Reading `escape s` and a quote gives back `s` and what follows the quote: the lexer stops at
the quote after `escape s` and at no byte of `escape s`. -/
theorem lex_escape (s rest : List UInt8) : lexStr (escape s ++ 34 :: rest) = some (s, rest) := by
  rw [escape_spec]
  induction s with
  | nil => rw [esc, List.flatMap_nil, List.nil_append, lexStr.eq_def]; simp
  | cons c s ih =>
    simp only [esc, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [lexStr_escByte, ih]
    rfl

/-- `escape s` has no control byte. -/
theorem escape_no_control (s : List UInt8) : ∀ c ∈ escape s, 32 ≤ c.toNat := by
  rw [escape_spec]
  intro c hc
  simp only [esc, List.mem_flatMap] at hc
  obtain ⟨x, -, hx⟩ := hc
  have h : ∀ n, n < 256 → ∀ c ∈ escByte n.toUInt8, 32 ≤ c.toNat := by decide +kernel
  exact h x.toNat x.toNat_lt c (by simpa using hx)

/-! ## Into an array -/

open Leangage.Token (bytesOf length_bytesOf getUTF8Byte_eq)

/-- The token over lists that a token over strings stands for. -/
def StrTok.toTok : StrTok → Tok
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str (bytesOf s)
  | .key s => .key (bytesOf s)
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

theorem pushEscapedByte_spec (acc : Array UInt8) (c : UInt8) :
    (pushEscapedByte acc c).toList = acc.toList ++ escapeByte c := by
  unfold pushEscapedByte escapeByte
  by_cases h : 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92
  · have h1 : c ≠ 34 := h.2.1
    have h2 : c ≠ 92 := h.2.2
    have h3 : ¬c < 32 := by have := h.1; simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at *; omega
    have h4 : c ≠ 8 := by intro e; subst e; exact h3 (by decide)
    have h5 : c ≠ 12 := by intro e; subst e; exact h3 (by decide)
    have h6 : c ≠ 10 := by intro e; subst e; exact h3 (by decide)
    have h7 : c ≠ 13 := by intro e; subst e; exact h3 (by decide)
    have h8 : c ≠ 9 := by intro e; subst e; exact h3 (by decide)
    simp [h.1, h1, h2, h3, h4, h5, h6, h7, h8]
  · have hf : (decide (32 ≤ c) && decide (c ≠ 34) && decide (c ≠ 92)) = false := by
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      by_cases a : 32 ≤ c <;> by_cases b : c ≠ 34 <;> simp_all
    simp only [hf, Bool.false_eq_true, ite_false]
    split <;> try simp
    split <;> try simp
    split <;> try simp
    split <;> try simp
    split <;> try simp
    split <;> try simp
    split <;> try simp
    split
    · simp
    · rename_i a1 a2 a3 a4 a5 a6 a7 a8
      exfalso
      apply h
      refine ⟨?_, a1, a2⟩
      simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at a8 ⊢
      omega

theorem pushEscaped_spec (s : String) (i : Nat) (acc : Array UInt8) :
    (pushEscaped s i acc).toList = acc.toList ++ escape ((bytesOf s).drop i) := by
  induction i, acc using pushEscaped.induct s with
  | case1 i acc h ih =>
    rw [pushEscaped, dite_eq_left h, ih, pushEscapedByte_spec, getUTF8Byte_eq]
    conv => rhs; rw [List.drop_eq_getElem_cons (i := i) (by rw [length_bytesOf]; exact h)]
    simp only [escape, List.flatMap_cons, List.append_assoc]
  | case2 i acc h =>
    rw [pushEscaped, dite_eq_right h, List.drop_eq_nil_of_le (by rw [length_bytesOf]; omega)]
    simp [escape]

theorem pushDecimal_spec (acc : Array UInt8) (n : Nat) :
    (pushDecimal acc n).toList = acc.toList ++ Token.decimal n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [pushDecimal]
    by_cases h : n < 10
    · simp [h, Token.decimal_lt h]
    · simp [h, ih (n / 10) (by omega), Token.decimal_ge h]

theorem pushTok_spec (acc : Array UInt8) (t : StrTok) :
    (pushTok acc t).toList = acc.toList ++ tokBytes t.toTok := by
  cases t with
  | bool b => cases b <;> simp [pushTok, StrTok.toTok, tokBytes]
  | num n => simp [pushTok, StrTok.toTok, tokBytes, pushDecimal_spec]
  | str s => simp [pushTok, StrTok.toTok, tokBytes, pushEscaped_spec]
  | key s => simp [pushTok, StrTok.toTok, tokBytes, pushEscaped_spec]
  | _ => simp [pushTok, StrTok.toTok, tokBytes]

theorem StrTok.isClose_toTok (t : StrTok) : t.isClose = Json.isClose t.toTok := by
  cases t <;> rfl

theorem StrTok.endsValue_toTok (t : StrTok) : t.endsValue = Json.endsValue t.toTok := by
  cases t <;> rfl

theorem writeArrayFrom_spec (acc : Array UInt8) (a : Bool) (ts : List StrTok) :
    (writeArrayFrom acc a ts).toList = writeFrom acc.toList.reverse a (ts.map StrTok.toTok) := by
  induction ts generalizing acc a with
  | nil => simp [writeArrayFrom, writeFrom]
  | cons t ts ih =>
    rw [writeArrayFrom, ih, List.map_cons, writeFrom, pushTok_spec, StrTok.isClose_toTok,
      StrTok.endsValue_toTok, List.reverseAux_eq]
    congr 1
    split <;> simp

/-- `writeArray` writes what `write` writes. -/
theorem writeArray_spec (ts : List StrTok) : (writeArray ts).toList = write (ts.map StrTok.toTok) := by
  simp [writeArray, write, writeArrayFrom_spec, Array.emptyWithCapacity_eq]

/-- `writeArray` of tokens that stand for the tokens of a JSON value prints the value. -/
theorem writeArray_value {ts : List StrTok} {v : Value} (h : ts.map StrTok.toTok = v.toks) :
    (writeArray ts).toList = v.print := by
  rw [writeArray_spec, h, write_value]

end Leangage.Json
