# The notes

[`samples/lean/Notes/Kernel.lean`](../samples/lean/Notes/Kernel.lean) keeps notes in an organization
with members and admins, after h5i's notes example. A note is visible to everyone if it is shared,
otherwise to its owner and admins; the owner or an admin edits and deletes it, and its owner never
changes. Admins add and remove members, and anyone may add the first member of an organization with
none.

`handle` decides what each command does and checks input and existence only. It lists notes and
members in key order, so that no reply depends on the order in which a snapshot holds its rows.
The policy is the Bool functions `permits`, `visible` and `stored`, and `view`, the rows of a
snapshot the caller may see. The function the engine runs is `handle` behind the guard of
[`langs/lean/Leangage/Authz.lean`](../langs/lean/Leangage/Authz.lean):

```lean
def transition (a : Principal) (s : Snapshot) (c : Command) :
    Except (Guarded Error) (List Write × Reply) :=
  guardViewed handle apply ⟨permits, visible, stored⟩ disclosed readOnly view a s c
```

The guard checks each write in the state the writes before it leave, and each row the reply
discloses against the state before or after the command. One refused write or row refuses the
whole command with `denied`, and nothing is stored. A read-only command runs on the caller's view,
the rows the policy lets the caller see.

[`langs/lean/Leangage/AuthzProofs.lean`](../langs/lean/Leangage/AuthzProofs.lean) proves, for every
kernel (`transition` and `apply`), policy, disclosure, `readOnly` and `view`:

| Theorem | Statement |
|---|---|
| `guard_authorized` | a command the guard accepts is the kernel's own result, each write is permitted in the state the writes before it leave, and each disclosed row is stored, exactly as disclosed, and visible, before or after the command |
| `guard_complete` | the guard accepts every such command, and `guard_app_error`: it passes the kernel's refusals through. `guard_eq` states the 3 as one equation |
| `guard_viewed_authorized` | with `guardViewed`, an accepted command that writes is `guard`'s case, and an accepted read-only command is the kernel's result on the caller's view, with no writes and only rows stored and visible in the view |
| `guard_viewed_noninterference` | 2 states with the same view give a read-only command the same result, refusals included |
| `read_only_sound_of_viewed` | a kernel behind `guardViewed` meets `ReadOnlySound`, the read-only obligation of the kernel contract |

[`samples/lean/Notes/Proofs.lean`](../samples/lean/Notes/Proofs.lean) applies them to the notes
(`transition_authorized`, `transition_noninterference`, `read_only_sound`) and proves, for every
principal, snapshot and command:

| Theorem | Statement |
|---|---|
| `read_after_put` | after an accepted `putNote`, the same user's `readNote` returns that body and sharing, owned by the note's earlier owner or else by the caller |
| `read_after_delete`, `member_after_add`, `member_after_remove` | after an accepted `deleteNote`, `readNote` finds no note; after `addMember`, the member is stored with its admin flag; after `removeMember`, it is gone |
| `others_unchanged` | a user who isn't an admin changes only notes they own, before and after the command |
| `members_unchanged` | a user who isn't an admin changes the members only of an organization that has none |
| `admin_not_denied` | the guard denies no command of an admin that writes |
| `owner_may_put`, `owner_may_delete` | the guard denies no edit or delete by a note's owner and no creation under a free id |
| `first_member` | anyone may add the first member of an organization with none |
| `read_note_spec`, `list_notes_spec`, `list_members_spec` | in a snapshot with unique keys, `readNote` returns the note under the id when the caller may see it and `notFound` otherwise, and the listings return exactly the rows the caller may see, in key order |
| `sortNotes_spec`, `sortMembers_spec` | a listing is in key order and holds each row of the list it sorts once |
| `transition_congr` | 2 snapshots with unique keys that store the same row under each key answer every command of every principal the same, whatever the order of their rows |
| `rows_stored_run` | every row a reply returns is the row stored under its key in the caller's view |
| `keyed_of_run` | every snapshot a tenant reaches has unique keys |
| `findNote_applyWrite`, `findMember_applyWrite` | what each write does to the row stored under each key |
| `ids_putNote`, `users_putMember` | a new row goes after the stored rows and a replaced row keeps its place |
| `bad_text` | a body is refused exactly when it is empty, longer than 4096 bytes in UTF-8, or holds NUL |
| `not_found` | removing a member or deleting a note that isn't stored is refused with `notFound` |

[`samples/lean/Notes/Wire.lean`](../samples/lean/Notes/Wire.lean) is what the notes server does with
a request, in the form of `Calculator.Wire`: `request` reads the tokens of the body into a command,
`respond` gives the status and the body of the answer, `fingerprint` and `scope` name a command and
a user under an idempotency key, and `encodeReply` and `decodeReply` write and read the reply an
engine stores under such a key.
[`samples/lean/Notes/Wire/Proofs.lean`](../samples/lean/Notes/Wire/Proofs.lean) proves:

| Theorem | Statement |
|---|---|
| `decode_encode` | every command has a JSON spelling (`{"cmd":"add_member","user":2,"admin":false}`, `{"cmd":"remove_member","user":2}`, `{"cmd":"put_note","id":7,"body":"text","shared":true}`, `{"cmd":"delete_note","id":7}`, `{"cmd":"read_note","id":7}`, `{"cmd":"list_notes"}`, `{"cmd":"list_members"}`) whose tokens decode to it |
| `decode_ok_iff`, `object_iff` | tokens decode to a command exactly when they are those of an object whose members are the fields of that command in some order; an object with another member or with a member twice is refused |
| `decodeMembers_missingCmd_iff`, `decodeMembers_notCommand_iff` | which refusal each other object gets: ``missing field `cmd` `` or `not a notes command` |
| `request_expired`, `request_json`, `request_not_json` | the status and the message of each answer `request` gives by itself (401, 400, 413) |
| `respond_ok`, `respond_error` | an accepted command is answered 200 with the JSON value of its reply; the guard's refusal is answered 403 `{"error":"denied"}`, `notFound` 404 `{"error":"not_found"}` and `badText` 422 `{"error":"bad_text"}` |
| `decodeReply_encode` | the tokens `encodeReply` writes for a reply, a number as its decimal, packed as a conversion packs them (`pack ((replyToks r).map Lexeme.ofStrTok)`), are read back as that reply |
| `fingerprint_injective`, `scope_injective` | different commands have different fingerprints, and 2 principals have the same scope exactly when they have the same user |

The Rust server ([`samples/rust/notes`](../samples/rust/notes)) passes each request to those
functions, as the calculator's servers do with theirs. It keeps the snapshots in its memory, or in
PostgreSQL when `LEANGAGE_DATABASE_URL` is set, as the calculator does:

```console
$ export LEANGAGE_SECRET=dev-secret
$ A=$(cd samples/rust && LEANGAGE_ISSUE=1:1 cargo run --release -q --bin leangage-notes)
$ B=$(cd samples/rust && LEANGAGE_ISSUE=1:2 cargo run --release -q --bin leangage-notes)
$ cd samples/rust && LEANGAGE_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leangage-notes &
$ curl -s -H "Authorization: Bearer $A" -d '{"cmd":"add_member","user":1,"admin":true}' 127.0.0.1:8080/rpc
{"done":true}
$ curl -s -H "Authorization: Bearer $A" -d '{"cmd":"put_note","id":7,"body":"draft","shared":false}' 127.0.0.1:8080/rpc
{"done":true}
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"read_note","id":7}' 127.0.0.1:8080/rpc
{"error":"not_found"}
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"put_note","id":7,"body":"mine now","shared":true}' 127.0.0.1:8080/rpc
{"error":"denied"}
$ curl -s -H "Authorization: Bearer $A" -d '{"cmd":"put_note","id":7,"body":"for everyone","shared":true}' 127.0.0.1:8080/rpc
{"done":true}
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"read_note","id":7}' 127.0.0.1:8080/rpc
{"note":{"body":"for everyone","id":7,"owner":1,"shared":true}}
```

The kernel and the tables are generated to Python
([`samples/python/notes/leangage_notes`](../samples/python/notes/leangage_notes)) and Go
([`samples/go/notes`](../samples/go/notes)) too. The kernel runs behind their memory engines in the
differential tests; neither has a notes server, and `Notes.Wire` is generated to Rust only.
