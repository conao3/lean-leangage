import Leangage.Json.Read
import Leangage.Json.Proofs

/-!
# What the JSON reader guarantees

- `read_print`: `read` of `Value.print v`, the bytes `Leangage.Json.write` writes for the tokens
  of a JSON value `v`, is the items of those tokens (`read_write`). So what a writer proved in
  `Leangage.Json.Proofs` writes reads back as what was written: every string with its bytes,
  every number below 2^64, arrays and objects of any depth.
- `readString_spec`: `readString`, which the servers' functions call, is `read` of the bytes of
  the string.
- `read_spaced`: spaces, tabs, line feeds and carriage returns before and after a printed JSON
  value change nothing.
- `read_fraction`: decimal digits, a point and decimal digits, and decimal digits, `e` and decimal
  digits, are read as the one item `number`.
- `isWs_spec`, `isDigit_spec`, `hexVal_spec`, `clean_spec`: the generated helpers equal
  definitions written another way.

Not proved: that every text `read` accepts is a JSON text of RFC 8259, and that `read` accepts
every JSON text of RFC 8259 apart from those with a `\u` escape of a surrogate outside a pair.
-/

namespace Leangage.Json.Read

open Leangage.Token (bytesOf length_bytesOf getUTF8Byte_eq)

/-- The item that a token of the writer reads back as. -/
def Item.ofTok : Tok → Item
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n
  | .str s => .str s
  | .key s => .key s
  | .arrOpen => .arrOpen
  | .arrClose => .arrClose
  | .objOpen => .objOpen
  | .objClose => .objClose

/-- The state after the bytes `l`. -/
def run (st : State) (l : List UInt8) : State :=
  l.foldl step st

theorem run_append (st : State) (l m : List UInt8) : run st (l ++ m) = run (run st l) m := by
  simp [run]

theorem run_cons (st : State) (c : UInt8) (l : List UInt8) : run st (c :: l) = run (step st c) l :=
  rfl

theorem run_nil (st : State) : run st [] = st :=
  rfl

/-! ## Over the bytes of a string -/

theorem stepFrom_spec (s : String) (i : Nat) (st : State) :
    stepFrom s i st = run st ((bytesOf s).drop i) := by
  induction i, st using stepFrom.induct s with
  | case1 i st h ih =>
    rw [stepFrom, dite_eq_left h, ih, getUTF8Byte_eq]
    conv => rhs; rw [List.drop_eq_getElem_cons (i := i) (by rw [length_bytesOf]; exact h)]
    rfl
  | case2 i st h =>
    rw [stepFrom, dite_eq_right h, List.drop_eq_nil_of_le (by rw [length_bytesOf]; omega)]
    rfl

/-- `readString` reads what `read` reads from the bytes of the string. -/
theorem readString_spec (s : String) : readString s = read (bytesOf s) := by
  simp [readString, read, stepFrom_spec, run]

/-! ## Reading what the writer wrote -/

/-- The state in a string whose bytes so far are `a`. -/
def inStr (k : Bool) (a : Array UInt8) (nest : List Bool) (out : List Item) : State :=
  ⟨.str, k, false, 0, 0, 0, [], a, nest, out⟩

/-- The state in the digits of an integer part of value `n` and `len` digits. -/
def inInt (n len : Nat) (nest : List Bool) (out : List Item) : State :=
  ⟨.int, false, false, n, len, 0, [], #[], nest, out⟩

theorem hexVal_hexDigit : ∀ d, d < 16 → hexVal (Token.hexDigit d) = d := by decide

theorem run_escapeByte (k : Bool) (a : Array UInt8) (nest : List Bool) (out : List Item) (c : UInt8) :
    run (inStr k a nest out) (escapeByte c) = inStr k (a.push c) nest out := by
  unfold escapeByte
  by_cases h34 : c = 34
  · subst h34; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h92 : c = 92
  · subst h92; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h8 : c = 8
  · subst h8; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h12 : c = 12
  · subst h12; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h10 : c = 10
  · subst h10; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h13 : c = 13
  · subst h13; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h9 : c = 9
  · subst h9; simp [run, step, stepStr, stepEsc, inStr]
  by_cases h32 : c < 32
  · have hlt : c.toNat < 32 := by simpa [UInt8.lt_iff_toNat_lt] using h32
    have h1 : c.toNat / 16 < 16 := by omega
    have h2 : c.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have hc : (c.toNat / 16 * 16 + c.toNat % 16) = c.toNat := by omega
    have h0 : hexVal 48 = 0 := by decide
    have h128 : c.toNat < 128 := by omega
    have hs : ¬55296 ≤ c.toNat := by omega
    have hs' : ¬56320 ≤ c.toNat := by omega
    simp [h34, h92, h8, h12, h10, h13, h9, h32, run, step, stepStr, stepEsc, stepHex, inStr,
      hexVal_hexDigit _ h1, hexVal_hexDigit _ h2, h0, h1, h2, endHex, pushUtf8, hc, h128, hs, hs']
  · simp [h34, h92, h8, h12, h10, h13, h9, h32, run, step, stepStr, inStr]

/-- Reading an escaped string and its closing quote gives the string. -/
theorem run_escape (k : Bool) (nest : List Bool) (out : List Item) (s : List UInt8)
    (a : Array UInt8) :
    run (inStr k a nest out) (escape s ++ [34]) =
      if k then clean .colon nest (.key (a.toList ++ s) :: out)
      else clean .next nest (.str (a.toList ++ s) :: out) := by
  induction s generalizing a with
  | nil => cases k <;> simp [escape, run, step, stepStr, inStr, emit]
  | cons c s ih =>
    simp only [escape, List.flatMap_cons, List.append_assoc] at ih ⊢
    rw [run_append, run_escapeByte, ih]
    simp

theorem digit_facts : ∀ d, d < 10 →
    isWs (d + 48).toUInt8 = false ∧ isDigit (d + 48).toUInt8 = true ∧
      (d + 48).toUInt8 ≠ 34 ∧ (d + 48).toUInt8 ≠ 123 ∧ (d + 48).toUInt8 ≠ 91 ∧
      (d + 48).toUInt8 ≠ 116 ∧ (d + 48).toUInt8 ≠ 102 ∧ (d + 48).toUInt8 ≠ 110 ∧
      (d + 48).toUInt8 ≠ 45 ∧ (d + 48).toUInt8 ≠ 93 ∧ ((d + 48).toUInt8 = 48 ↔ d = 0) ∧
      (d + 48).toUInt8.toNat - 48 = d := by
  decide

/-- Reading the decimal digits of a positive number leaves the loop in its integer part. -/
theorem run_decimal_pos (p : At) (hp : p = .value ∨ p = .first) (nest : List Bool) (out : List Item) :
    ∀ n, 0 < n → (Token.decimal n).length ≤ 20 →
      run (clean p nest out) (Token.decimal n) = inInt n (Token.decimal n).length nest out := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro hn hlen
    by_cases h : n < 10
    · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ := digit_facts n h
      have f11' : (n + 48).toUInt8 ≠ 48 := fun e => by have := f11.mp e; omega
      rw [Token.decimal_lt h]
      generalize (n + 48).toUInt8 = c at *
      rcases hp with rfl | rfl <;>
        simp [run, step, stepValue, stepFirst, startValue, clean, inInt, f1, f2, f3, f4, f5, f6, f7,
          f8, f9, f10, f11', f12]
    · obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12⟩ :=
        digit_facts (n % 10) (Nat.mod_lt _ (by decide))
      rw [Token.decimal_ge h] at hlen ⊢
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      rw [run_append, ih (n / 10) (by omega) (by omega) (by omega)]
      have hl : (Token.decimal (n / 10)).length < 20 := by omega
      have hv : n / 10 * 10 + n % 10 = n := by omega
      generalize (n % 10 + 48).toUInt8 = c at *
      simp [run, step, stepInt, inInt, f2, f12, hl, hv]

/-- A byte that may follow a value: a space, a tab, a line feed, a carriage return, a comma, `]`
or `}`. -/
def Sep (c : UInt8) : Prop :=
  c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13 ∨ c = 44 ∨ c = 93 ∨ c = 125

/-- What a state that has read a value is: the byte after a value, and the end of the bytes,
give what they give in the state between two tokens that holds the items `out`. -/
def Done (st : State) (nest : List Bool) (out : List Item) : Prop :=
  (∀ c, Sep c → step st c = afterValue (clean .next nest out) c) ∧
    finish st = finish (clean .next nest out)

theorem done_clean (nest : List Bool) (out : List Item) : Done (clean .next nest out) nest out :=
  ⟨fun _ _ => rfl, rfl⟩

theorem done_num (p : At) (hp : p = .value ∨ p = .first) (nest : List Bool) (out : List Item)
    (x : UInt64) :
    Done (run (clean p nest out) (Token.decimal x.toNat)) nest (.num x :: out) := by
  have hlen := Token.decimal_length_uint64 x
  have hx : x.toNat < 18446744073709551616 := x.toNat_lt
  by_cases h0 : x.toNat = 0
  · have hx0 : x = 0 := UInt64.toNat_inj.mp h0
    subst hx0
    have hrun : run (clean p nest out) (Token.decimal (0 : UInt64).toNat) =
        ⟨.zero, false, false, 0, 0, 0, [], #[], nest, out⟩ := by
      rw [show (0 : UInt64).toNat = 0 from rfl, Token.decimal_lt (by decide : 0 < 10)]
      rcases hp with rfl | rfl <;> rfl
    rw [hrun]
    refine ⟨?_, ?_⟩
    · rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> rfl
    · cases nest <;> rfl
  · rw [run_decimal_pos p hp nest out x.toNat (by omega) hlen]
    have hi : intItem false x.toNat (Token.decimal x.toNat).length = .num x := by
      simp [intItem, hlen, hx]
    refine ⟨?_, ?_⟩
    · rintro c (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp [step, stepInt, inInt, isDigit, emit, hi]
    · cases nest <;> simp [finish, inInt, clean, hi]

theorem step_open_value (p : At) (hp : p = .value ∨ p = .first) (nest : List Bool) (out : List Item) :
    step (clean p nest out) 34 = inStr false #[] nest out ∧
      step (clean p nest out) 91 = clean .first (false :: nest) (.arrOpen :: out) ∧
      step (clean p nest out) 123 = clean .firstKey (true :: nest) (.objOpen :: out) ∧
      run (clean p nest out) [110, 117, 108, 108] = clean .next nest (.null :: out) ∧
      run (clean p nest out) [116, 114, 117, 101] = clean .next nest (.bool true :: out) ∧
      run (clean p nest out) [102, 97, 108, 115, 101] = clean .next nest (.bool false :: out) := by
  rcases hp with rfl | rfl <;> refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem toks_reverse_cons (ts : List Tok) (t : Tok) (out : List Item) :
    Item.ofTok t :: ((ts.map Item.ofTok).reverse ++ out) = ((ts ++ [t]).map Item.ofTok).reverse ++ out := by
  simp

mutual
/-- Reading a printed value where a value may start reads its tokens. -/
theorem run_value (v : Value) (p : At) (hp : p = .value ∨ p = .first) (nest : List Bool)
    (out : List Item) :
    Done (run (clean p nest out) v.print) nest ((v.toks.map Item.ofTok).reverse ++ out) := by
  obtain ⟨hq, ha, ho, hn, ht, hf⟩ := step_open_value p hp nest out
  match v with
  | .null =>
    rw [show Value.null.print = [110, 117, 108, 108] from rfl, hn]
    exact done_clean _ _
  | .bool true =>
    rw [show (Value.bool true).print = [116, 114, 117, 101] from rfl, ht]
    exact done_clean _ _
  | .bool false =>
    rw [show (Value.bool false).print = [102, 97, 108, 115, 101] from rfl, hf]
    exact done_clean _ _
  | .num n =>
    rw [show (Value.num n).print = Token.decimal n.toNat by simp [Value.print, decimal_spec]]
    exact done_num p hp nest out n
  | .str s =>
    rw [show (Value.str s).print = 34 :: (escape s ++ [34]) by
      simp [Value.print, quote, escape_spec], run_cons, hq, run_escape]
    simpa [Value.toks, Item.ofTok] using done_clean nest (.str s :: out)
  | .arr [] =>
    rw [show (Value.arr []).print = [91, 93] from rfl, run_cons, ha]
    exact done_clean _ _
  | .arr (v :: vs) =>
    rw [show (Value.arr (v :: vs)).print = 91 :: (printElems (v :: vs) ++ [93]) by
      simp [Value.print, ascii], run_cons, ha,
      run_elems (v :: vs) (by simp) .first (Or.inr rfl) nest (.arrOpen :: out)]
    simpa [Value.toks, Item.ofTok] using
      done_clean nest (.arrClose :: (((elemsToks (v :: vs)).map Item.ofTok).reverse ++ .arrOpen :: out))
  | .obj [] =>
    rw [show (Value.obj []).print = [123, 125] from rfl, run_cons, ho]
    exact done_clean _ _
  | .obj (m :: ms) =>
    rw [show (Value.obj (m :: ms)).print = 123 :: (printMembers (m :: ms) ++ [125]) by
      simp [Value.print, ascii], run_cons, ho,
      run_members (m :: ms) (by simp) .firstKey (Or.inr rfl) nest (.objOpen :: out)]
    simpa [Value.toks, Item.ofTok] using
      done_clean nest (.objClose :: (((membersToks (m :: ms)).map Item.ofTok).reverse ++ .objOpen :: out))

/-- Reading the printed elements of an array and its `]` reads their tokens and closes it. -/
theorem run_elems (vs : List Value) (hvs : vs ≠ []) (p : At) (hp : p = .value ∨ p = .first)
    (nest : List Bool) (out : List Item) :
    run (clean p (false :: nest) out) (printElems vs ++ [93]) =
      clean .next nest (.arrClose :: (((elemsToks vs).map Item.ofTok).reverse ++ out)) := by
  match vs with
  | [] => exact absurd rfl hvs
  | [v] =>
    have hd := run_value v p hp (false :: nest) out
    rw [show printElems [v] ++ [93] = v.print ++ [93] from rfl, run_append, run_cons, run_nil,
      hd.1 93 (by simp [Sep])]
    simp [afterValue, isWs, clean, elemsToks]
  | v :: w :: vs =>
    have hd := run_value v p hp (false :: nest) out
    have ih := run_elems (w :: vs) (by simp) .value (Or.inl rfl) nest
      ((v.toks.map Item.ofTok).reverse ++ out)
    rw [show printElems (v :: w :: vs) ++ [93] = v.print ++ 44 :: (printElems (w :: vs) ++ [93]) by
      simp [printElems, ascii], run_append, run_cons, hd.1 44 (by simp [Sep])]
    rw [show afterValue (clean .next (false :: nest) ((v.toks.map Item.ofTok).reverse ++ out)) 44 =
      clean .value (false :: nest) ((v.toks.map Item.ofTok).reverse ++ out) from rfl, ih]
    simp [elemsToks]

/-- Reading the printed members of an object and its `}` reads their tokens and closes it. -/
theorem run_members (ms : List (List UInt8 × Value)) (hms : ms ≠ []) (q : At)
    (hq : q = .key ∨ q = .firstKey) (nest : List Bool) (out : List Item) :
    run (clean q (true :: nest) out) (printMembers ms ++ [125]) =
      clean .next nest (.objClose :: (((membersToks ms).map Item.ofTok).reverse ++ out)) := by
  have hk : step (clean q (true :: nest) out) 34 = inStr true #[] (true :: nest) out := by
    rcases hq with rfl | rfl <;> rfl
  match ms with
  | [] => exact absurd rfl hms
  | [(k, v)] =>
    have hd := run_value v .value (Or.inl rfl) (true :: nest) (.key k :: out)
    rw [show printMembers [(k, v)] ++ [125] = 34 :: ((escape k ++ [34]) ++ 58 :: (v.print ++ [125])) by
      simp [printMembers, quote, escape_spec, ascii], run_cons, hk, run_append, run_escape]
    simp only [ite_true, List.nil_append, run_cons]
    rw [show step (clean .colon (true :: nest) (.key k :: out)) 58 =
      clean .value (true :: nest) (.key k :: out) from rfl, run_append, run_cons, run_nil,
      hd.1 125 (by simp [Sep])]
    simp [afterValue, isWs, clean, membersToks, Item.ofTok]
  | (k, v) :: m :: ms =>
    have hd := run_value v .value (Or.inl rfl) (true :: nest) (.key k :: out)
    have ih := run_members (m :: ms) (by simp) .key (Or.inl rfl) nest
      ((v.toks.map Item.ofTok).reverse ++ .key k :: out)
    rw [show printMembers ((k, v) :: m :: ms) ++ [125] =
        34 :: ((escape k ++ [34]) ++ 58 :: (v.print ++ 44 :: (printMembers (m :: ms) ++ [125]))) by
      simp [printMembers, quote, escape_spec, ascii], run_cons, hk, run_append, run_escape]
    simp only [ite_true, List.nil_append, run_cons]
    rw [show step (clean .colon (true :: nest) (.key k :: out)) 58 =
      clean .value (true :: nest) (.key k :: out) from rfl, run_append, run_cons,
      hd.1 44 (by simp [Sep])]
    rw [show afterValue (clean .next (true :: nest) ((v.toks.map Item.ofTok).reverse ++ .key k :: out)) 44 =
      clean .key (true :: nest) ((v.toks.map Item.ofTok).reverse ++ .key k :: out) from rfl, ih]
    simp [membersToks, Item.ofTok]
end

/-- `read` of a printed JSON value is the items of its tokens. -/
theorem read_print (v : Value) : read v.print = some (v.toks.map Item.ofTok) := by
  have h := (run_value v .value (Or.inl rfl) [] []).2
  rw [read, show List.foldl step start v.print = run (clean .value [] []) v.print from rfl, h]
  simp [finish, clean]

/-- The 4 bytes of space. -/
theorem isWs_spec (c : UInt8) : isWs c = true ↔ c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13 := by
  simp [isWs, or_assoc]

/-- The 10 decimal digits. -/
theorem isDigit_spec (c : UInt8) : isDigit c = true ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp [isDigit, UInt8.le_iff_toNat_le]

/-- The value of a hexadecimal digit of either case. -/
theorem hexVal_spec (c : UInt8) : hexVal c = (unhexDigit c).getD 16 := by
  have h : ∀ n, n < 256 → hexVal n.toUInt8 = (unhexDigit n.toUInt8).getD 16 := by decide +kernel
  simpa using h c.toNat c.toNat_lt

/-- The state between two tokens holds nothing of a string or a number. -/
theorem clean_spec (p : At) (nest : List Bool) (out : List Item) :
    clean p nest out = ⟨p, false, false, 0, 0, 0, [], #[], nest, out⟩ :=
  rfl

theorem run_ws (p : At) (hp : p = .value ∨ p = .next) (nest : List Bool) (out : List Item)
    (ws : List UInt8) (h : ∀ c ∈ ws, isWs c = true) :
    run (clean p nest out) ws = clean p nest out := by
  induction ws with
  | nil => rfl
  | cons c ws ih =>
    have hc : isWs c = true := h c (List.mem_cons_self ..)
    have hs : step (clean p nest out) c = clean p nest out := by
      rcases hp with rfl | rfl
      · simp [step, stepValue, clean, hc]
      · simp [step, afterValue, clean, hc]
    rw [run_cons, hs]
    exact ih fun c hc => h c (List.mem_cons_of_mem _ hc)

theorem sep_of_isWs {c : UInt8} (h : isWs c = true) : Sep c := by
  simp only [isWs, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h <;> simp [Sep, h]

/-- The space RFC 8259 allows before and after a value changes nothing: `read` of a printed JSON
value between spaces, tabs, line feeds and carriage returns is the items of its tokens. -/
theorem read_spaced (v : Value) (before after : List UInt8)
    (hb : ∀ c ∈ before, c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13)
    (ha : ∀ c ∈ after, c = 32 ∨ c = 9 ∨ c = 10 ∨ c = 13) :
    read (before ++ v.print ++ after) = some (v.toks.map Item.ofTok) := by
  have hb : ∀ c ∈ before, isWs c = true := fun c h => (isWs_spec c).mpr (hb c h)
  have ha : ∀ c ∈ after, isWs c = true := fun c h => (isWs_spec c).mpr (ha c h)
  have hd := run_value v .value (Or.inl rfl) [] []
  have hrun : List.foldl step start (before ++ v.print ++ after) =
      run (run (clean .value [] []) v.print) after := by
    rw [show List.foldl step start (before ++ v.print ++ after) =
      run (clean .value [] []) (before ++ v.print ++ after) from rfl, run_append, run_append,
      run_ws .value (Or.inl rfl) [] [] before hb]
  rw [read, hrun]
  cases after with
  | nil =>
    rw [run_nil, hd.2]
    simp [finish, clean]
  | cons c rest =>
    have hc : isWs c = true := ha c (List.mem_cons_self ..)
    rw [run_cons, hd.1 c (sep_of_isWs hc)]
    have hs : afterValue (clean .next [] ((v.toks.map Item.ofTok).reverse ++ [])) c =
        clean .next [] ((v.toks.map Item.ofTok).reverse ++ []) := by
      simp [afterValue, clean, hc]
    rw [hs, run_ws .next (Or.inr rfl) [] _ rest fun c h => ha c (List.mem_cons_of_mem _ h)]
    simp [finish, clean]

/-! ## Numbers with a fraction or an exponent -/

theorem int_part (x : UInt64) :
    ∃ st, run (clean .value [] []) (Token.decimal x.toNat) = st ∧
      (st.place = .zero ∨ st.place = .int) ∧ st.nest = [] ∧ st.out = [] := by
  by_cases h0 : x.toNat = 0
  · rw [h0, Token.decimal_lt (by decide : 0 < 10)]
    exact ⟨_, rfl, Or.inl rfl, rfl, rfl⟩
  · exact ⟨_, run_decimal_pos .value (Or.inl rfl) [] [] x.toNat (by omega)
      (Token.decimal_length_uint64 x), Or.inr rfl, rfl, rfl⟩

theorem decimal_isDigit (n : Nat) : ∀ c ∈ Token.decimal n, isDigit c = true :=
  fun c h => (isDigit_spec c).mpr (Token.decimal_digit n c h)

theorem run_digits (st : State) (h : st.place = .frac ∨ st.place = .expDigits) (l : List UInt8)
    (hl : ∀ c ∈ l, isDigit c = true) : run st l = st := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    have hc : isDigit c = true := hl c (List.mem_cons_self ..)
    have hs : step st c = st := by
      rcases h with h | h <;> simp [step, h, stepDigits, hc]
    rw [run_cons, hs]
    exact ih fun c h => hl c (List.mem_cons_of_mem _ h)

/-- Decimal digits, a point and decimal digits, and decimal digits, `e` and decimal digits, are
read as a number that is not the decimal of a `UInt64`. -/
theorem read_fraction (x y : UInt64) :
    read (Token.decimal x.toNat ++ 46 :: Token.decimal y.toNat) = some [.number] ∧
      read (Token.decimal x.toNat ++ 101 :: Token.decimal y.toNat) = some [.number] := by
  obtain ⟨st, hst, hp, hn, ho⟩ := int_part x
  have hy := decimal_isDigit y.toNat
  cases hd : Token.decimal y.toNat with
  | nil => exact absurd hd (Token.decimal_ne_nil _)
  | cons d ds =>
    rw [hd] at hy
    have hdig : isDigit d = true := hy d (List.mem_cons_self ..)
    have hds : ∀ c ∈ ds, isDigit c = true := fun c h => hy c (List.mem_cons_of_mem _ h)
    have hd' := (isDigit_spec d).mp hdig
    have h43 : d ≠ 43 := fun e => by subst e; simp at hd'
    have h45 : d ≠ 45 := fun e => by subst e; simp at hd'
    have hfinish : ∀ p, p = At.frac ∨ p = At.expDigits →
        finish { st with place := p } = some [.number] := by
      rintro p (rfl | rfl) <;> simp [finish, hn, ho]
    constructor
    · have h1 : step st 46 = { st with place := .dot } := by
        rcases hp with h | h <;> simp [step, h, stepZero, stepInt, isDigit]
      have h2 : step { st with place := .dot } d = { st with place := .frac } := by
        simp [step, hdig]
      rw [read, show List.foldl step start (Token.decimal x.toNat ++ 46 :: d :: ds) =
        run (run (clean .value [] []) (Token.decimal x.toNat)) (46 :: d :: ds) by
          simp [run, start], hst, run_cons, h1, run_cons, h2,
        run_digits _ (Or.inl rfl) ds hds]
      exact hfinish _ (Or.inl rfl)
    · have h1 : step st 101 = { st with place := .exp } := by
        rcases hp with h | h <;> simp [step, h, stepZero, stepInt, isDigit]
      have h2 : step { st with place := .exp } d = { st with place := .expDigits } := by
        simp [step, hdig, h43, h45]
      rw [read, show List.foldl step start (Token.decimal x.toNat ++ 101 :: d :: ds) =
        run (run (clean .value [] []) (Token.decimal x.toNat)) (101 :: d :: ds) by
          simp [run, start], hst, run_cons, h1, run_cons, h2,
        run_digits _ (Or.inr rfl) ds hds]
      exact hfinish _ (Or.inr rfl)

/-- `read` of what `write` writes for the tokens of a JSON value is the items of those tokens. -/
theorem read_write (v : Value) : read (write v.toks) = some (v.toks.map Item.ofTok) := by
  rw [write_value, read_print]

/-- `readString` of a string whose bytes are a printed JSON value is the items of its tokens. -/
theorem readString_print {s : String} {v : Value} (h : bytesOf s = v.print) :
    readString s = some (v.toks.map Item.ofTok) := by
  rw [readString_spec, h, read_print]

end Leangage.Json.Read
