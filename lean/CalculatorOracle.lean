import Calculator.Kernel

/-!
Runs the calculator kernel natively on commands read from standard input, one per line
(`<org> <user> set <n>`, `<org> <user> apply <add|sub|mul|div> <n>`, `<org> <user> get`), keeping
one snapshot per org, and prints one line per command. The generated Rust and Python are checked
against this output.
-/

open Calculator.Kernel

def parseOp : String → Option Op
  | "add" => some .add
  | "sub" => some .sub
  | "mul" => some .mul
  | "div" => some .div
  | _ => none

def parseLine (line : String) : Option (Principal × Command) := do
  match line.splitOn " " with
  | [org, user, "set", n] =>
    some ({ org := (← org.toNat?).toUInt64, user := (← user.toNat?).toUInt64 }, .set (← n.toNat?).toUInt64)
  | [org, user, "apply", op, n] =>
    some ({ org := (← org.toNat?).toUInt64, user := (← user.toNat?).toUInt64 },
      .apply (← parseOp op) (← n.toNat?).toUInt64)
  | [org, user, "get"] =>
    some ({ org := (← org.toNat?).toUInt64, user := (← user.toNat?).toUInt64 }, .get)
  | _ => none

def showError : Error → String
  | .overflow => "overflow"
  | .underflow => "underflow"
  | .divByZero => "division_by_zero"

partial def loop (stdin : IO.FS.Stream) (state : List (UInt64 × Snapshot)) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match parseLine line.trimAscii.toString with
  | none => IO.println "bad line"; loop stdin state
  | some (actor, cmd) =>
    let snap := (state.lookup (tenant actor)).getD init
    match transition actor snap cmd with
    | .ok (w, .value v) =>
      IO.println s!"ok {v}"
      loop stdin ((tenant actor, apply snap w) :: state.filter (·.1 != tenant actor))
    | .error e =>
      IO.println s!"error {showError e}"
      loop stdin state

def main : IO Unit := do
  loop (← IO.getStdin) []
