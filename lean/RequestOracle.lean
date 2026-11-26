import Leangage.Http
import Leangage.Json.Read
import Calculator.Wire

/-!
Runs the functions on requests and responses natively on lines read from standard input and
prints one line per input line. The generated Rust, Python and Go are checked against this
output.

Bytes are written `x<hex>`, and a text as the `x<hex>` of its UTF-8. A command is `set <n>`,
`apply <add|sub|mul|div> <n>` or `get`.

| line | prints |
|---|---|
| `read x<hex>` | `items` and the items `read` returns, or `none` |
| `auth -`, `auth x<hex>` | for `authenticate` without and with a header: `ok <tenant> <user> <exp> x<payload> x<tag>` or `err <status> x<body>` |
| `request <tenant> <user> <exp> <now> <body>` | for `Calculator.Wire.request`: `ok <org> <user> <command>` or `err <status> x<body>` |
| `respond ok <v>`, `respond err <name>` | `resp <status> x<body>` of `Calculator.Wire.respond` |
| `failure <name>` | `resp <status> x<body>` of `failed` |
| `fingerprint <command>` | `bytes x<hex>` |
| `scope <user>` | `text x<hex>` |

An item is `n` (null), `t` and `f` (true and false), `u<decimal>` (a number below 2^64 in decimal
digits), `#` (another number), `sx<hex>` (a string), `kx<hex>` (a key), `[`, `]`, `{` or `}`.
A body is `x<hex>` (text), `notutf8`, `toolarge` or `unreadable`. The names of the refusals are
`overflow`, `underflow` and `division_by_zero`, and those of the failures `bad_signature`,
`conflict`, `stopped`, `retries_exhausted`, `database`, `commit_unknown` and `broken`.
-/

open Leangage Leangage.Json.Read Calculator.Kernel

def hexDigitValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def unhexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let x ← hexDigitValue a
    let y ← hexDigitValue b
    return (x * 16 + y).toUInt8 :: (← unhexChars rest)
  | _ => none

def hexChar (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def showBytes (bs : List UInt8) : String :=
  "x" ++ String.join (bs.map fun b => String.ofList [hexChar (b.toNat / 16), hexChar (b.toNat % 16)])

def bytes (s : String) : Option (List UInt8) :=
  match s.toList with
  | 'x' :: hex => unhexChars hex
  | _ => none

def text (s : String) : Option String := do
  String.fromUTF8? (ByteArray.mk (← bytes s).toArray)

def number (s : String) : Option UInt64 := do
  let n ← s.toNat?
  if n < 2 ^ 64 then some n.toUInt64 else none

def showItem : Item → String
  | .null => "n"
  | .bool true => "t"
  | .bool false => "f"
  | .num n => s!"u{n}"
  | .number => "#"
  | .str s => "s" ++ showBytes s
  | .key s => "k" ++ showBytes s
  | .arrOpen => "["
  | .arrClose => "]"
  | .objOpen => "{"
  | .objClose => "}"

def showResponse (head : String) (r : Http.Response) : String :=
  s!"{head} {r.status} {showBytes r.body.toList}"

def op : String → Option Op
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "div" => some .div
  | _ => none

def showOp : Op → String
  | .add => "add"
  | .sub => "sub"
  | .mul => "mul"
  | .div => "div"

def command : List String → Option Command
  | ["set", n] => do return .set (← number n)
  | ["apply", o, n] => do return .apply (← op o) (← number n)
  | ["get"] => some .get
  | _ => none

def showCommand : Command → String
  | .set n => s!"set {n}"
  | .apply o n => s!"apply {showOp o} {n}"
  | .get => "get"

def body : String → Option Http.Body
  | "notutf8" => some .notUtf8
  | "toolarge" => some .tooLarge
  | "unreadable" => some .unreadable
  | s => (text s).map .text

def refusal : String → Option Error
  | "overflow" => some .overflow
  | "underflow" => some .underflow
  | "division_by_zero" => some .divByZero
  | _ => none

def failure : String → Option Http.Failure
  | "bad_signature" => some .badSignature
  | "conflict" => some .conflict
  | "stopped" => some .stopped
  | "retries_exhausted" => some .retriesExhausted
  | "database" => some .database
  | "commit_unknown" => some .commitUnknown
  | "broken" => some .broken
  | _ => none

def showAuth : Except Http.Response Http.Bearer → String
  | .ok b => s!"ok {b.tenant} {b.user} {b.exp} {showBytes b.payload.toList} {showBytes b.sig.toList}"
  | .error r => showResponse "err" r

def run (line : String) : Option String :=
  match line.splitOn " " with
  | ["read", b] => do
    match read (← bytes b) with
    | some items => return " ".intercalate ("items" :: items.map showItem)
    | none => return "none"
  | ["auth", "-"] => some (showAuth (Http.authenticate none))
  | ["auth", h] => do return showAuth (Http.authenticate (some (← text h)))
  | ["request", tenant, user, exp, now, b] => do
    match Calculator.Wire.request (← number tenant) (← number user) (← number exp) (← number now)
        (← body b) with
    | .ok call => return s!"ok {call.actor.org} {call.actor.user} {showCommand call.cmd}"
    | .error r => return showResponse "err" r
  | ["respond", "ok", v] => do
    return showResponse "resp" (Calculator.Wire.respond (.ok (.value (← number v))))
  | ["respond", "err", name] => do
    return showResponse "resp" (Calculator.Wire.respond (.error (← refusal name)))
  | ["failure", name] => do return showResponse "resp" (Http.failed (← failure name))
  | "fingerprint" :: cmd => do
    return "bytes " ++ showBytes (Calculator.Wire.fingerprint (← command cmd)).toList
  | ["scope", user] => do
    return "text " ++ showBytes (Calculator.Wire.scope ⟨0, ← number user⟩).toUTF8.toList
  | _ => none

partial def loop (stdin : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  IO.println ((run line.trimAscii.toString).getD "bad line")
  loop stdin

def main : IO Unit := do
  loop (← IO.getStdin)
