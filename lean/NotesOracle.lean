import Notes.Kernel

/-!
Runs the notes kernel natively on commands read from standard input, one per line, keeping one
snapshot per org, and prints one line per command. The generated Rust, Python and Go are checked
against this output.

```
<org> <user> add-member <user> <0|1>
<org> <user> remove-member <user>
<org> <user> put-note <id> <0|1> <body>
<org> <user> delete-note <id>
<org> <user> read-note <id>
<org> <user> list-notes
<org> <user> list-members
```

A body has no space; it may be empty.
-/

open Notes.Kernel Leangage.Authz

def parseFlag : String → Option Bool
  | "0" => some false
  | "1" => some true
  | _ => none

def parseCommand : List String → Option Command
  | ["add-member", u, admin] => do return .addMember (← u.toNat?).toUInt64 (← parseFlag admin)
  | ["remove-member", u] => do return .removeMember (← u.toNat?).toUInt64
  | ["put-note", id, shared, body] => do
    return .putNote (← id.toNat?).toUInt64 body (← parseFlag shared)
  | ["delete-note", id] => do return .deleteNote (← id.toNat?).toUInt64
  | ["read-note", id] => do return .readNote (← id.toNat?).toUInt64
  | ["list-notes"] => some .listNotes
  | ["list-members"] => some .listMembers
  | _ => none

def parseLine (line : String) : Option (Principal × Command) := do
  match line.splitOn " " with
  | org :: user :: rest =>
    return ({ org := (← org.toNat?).toUInt64, user := (← user.toNat?).toUInt64 }, ← parseCommand rest)
  | _ => none

def flag (b : Bool) : String := if b then "1" else "0"

def showNote (n : Note) : String := s!"{n.id}:{n.owner}:{flag n.shared}:{n.body}"

def showReply : Reply → String
  | .done => "done"
  | .found n => s!"found {showNote n}"
  | .notes ns => " ".intercalate (s!"notes {ns.length}" :: ns.map showNote)
  | .members ms => " ".intercalate (s!"members {ms.length}" :: ms.map fun m => s!"{m.user}:{flag m.admin}")

def showError : Guarded Error → String
  | .app .notFound => "not_found"
  | .app .badText => "bad_text"
  | .denied => "denied"

partial def loop (stdin : IO.FS.Stream) (state : List (UInt64 × Snapshot)) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  match parseLine (String.ofList (line.toList.filter (· ≠ '\n'))) with
  | none => IO.println "bad line"; loop stdin state
  | some (actor, cmd) =>
    let snap := (state.lookup (tenant actor)).getD init
    match transition actor snap cmd with
    | .ok (ws, r) =>
      IO.println s!"ok {showReply r}"
      loop stdin ((tenant actor, apply snap ws) :: state.filter (·.1 != tenant actor))
    | .error e =>
      IO.println s!"error {showError e}"
      loop stdin state

def main : IO Unit := do
  loop (← IO.getStdin) []
