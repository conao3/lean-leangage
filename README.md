# leanharbor

Web services whose core is one pure function written and proved in Lean 4.

You write the kernel of a service — what a command does to one tenant's state — as a Lean
function, prove what callers rely on, and [leanfran](https://github.com/conao3/lean-leanfran)
generates it to your language. leanharbor is the contract the kernel fills, an authorization guard
proved once for every kernel and policy, and the shell that runs the generated code behind HTTP.
The same kernel runs today from Rust, from Python and from Go.

The design follows [h5i-app](https://github.com/h5i-dev/h5i/blob/main/crates/h5i-app/README.md),
which does this for Rust by translating Rust to Lean. leanharbor goes the other way: Lean is the
source, and the host language is generated.

## The calculator

[`lean/Calculator/Kernel.lean`](lean/Calculator/Kernel.lean) keeps one number per user:

```lean
def transition (actor : Principal) (snap : Snapshot) (cmd : Command) :
    Except Error (Option Memory × Reply) :=
  match cmd with
  | .set value => .ok (some { user := actor.user, value }, .value value)
  | .apply op arg =>
    match compute op (memoryOf snap.memories actor.user) arg with
    | .ok v => .ok (some { user := actor.user, value := v }, .value v)
    | .error e => .error e
  | .get => .ok (none, .value (memoryOf snap.memories actor.user))
```

A tenant's numbers are a binary trie on the user id, lowest bit first. A command visits at most
64 nodes, and about log₂ n in a tenant whose n user ids are 0 to n − 1. `memoryOf` reads a number and `apply` stores one with `store`.

[`lean/Calculator/Proofs.lean`](lean/Calculator/Proofs.lean) proves, for every principal, snapshot
and command:

| Theorem | Statement |
|---|---|
| `transition_spec` | the reply is `specStep` (arithmetic on unbounded naturals) of the caller's number, and the command is refused exactly when `specStep` refuses |
| `compute_spec` | `compute` is `+`, `-`, `*`, `/` on naturals when the result fits 64 bits, and a refusal otherwise |
| `get_after` | after an accepted command, `get` by the same user returns that command's reply |
| `others_unchanged` | a command leaves every other user's number as it was |
| `read_only_sound` | `get` returns no writes |
| `memoryOf_store` | after `store k v`, `memoryOf` returns `v` for `k` and what it returned before for every other id |

The Rust server is the generated kernel behind an ordinary axum router
([`rust/calculator`](rust/calculator)):

```console
$ export LEANHARBOR_SECRET=dev-secret
$ TOKEN=$(LEANHARBOR_ISSUE=1:7 cargo run --release -q --bin leanharbor-calculator)
$ LEANHARBOR_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leanharbor-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8080/rpc
{"value":6}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"mul","arg":7}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"get"}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"div","arg":0}' 127.0.0.1:8080/rpc
{"error":"division_by_zero"}
```

The Python server ([`python/src/leanharbor_calculator`](python/src/leanharbor_calculator)) runs
the same Lean module, generated to Python, and the Go server
([`go/calculator`](go/calculator)) runs it generated to Go. Accepted and refused commands get the
same status and body from the three servers, and a token issued by one is accepted by the others:

```console
$ cd python && LEANHARBOR_LISTEN=127.0.0.1:8081 uv run leanharbor-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8081/rpc
{"value":6}
$ cd go && LEANHARBOR_LISTEN=127.0.0.1:8082 go run ./calculator/cmd/leanharbor-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8082/rpc
{"value":6}
```

## The notes

[`lean/Notes/Kernel.lean`](lean/Notes/Kernel.lean) keeps notes in an organization with members
and admins, after h5i's notes example. A note is visible to everyone if it is shared, otherwise to
its owner and admins; the owner or an admin edits and deletes it, and its owner never changes.
Admins add and remove members, and anyone may add the first member of an organization with none.

`handle` decides what each command does and checks input and existence only. The policy is the
Bool functions `permits`, `visible` and `stored`, and `view`, the rows of a snapshot the caller may
see. The function the engine runs is `handle` behind the guard of
[`lean/Leanharbor/Authz.lean`](lean/Leanharbor/Authz.lean):

```lean
def transition (a : Principal) (s : Snapshot) (c : Command) :
    Except (Guarded Error) (List Write × Reply) :=
  guardViewed handle apply ⟨permits, visible, stored⟩ disclosed readOnly view a s c
```

The guard checks each write in the state the writes before it leave, and each row the reply
discloses against the state before or after the command. One refused write or row refuses the
whole command with `denied`, and nothing is stored. A read-only command runs on the caller's view,
the rows the policy lets the caller see.

[`lean/Leanharbor/AuthzProofs.lean`](lean/Leanharbor/AuthzProofs.lean) proves, for every kernel
(`transition` and `apply`), policy, disclosure, `readOnly` and `view`:

| Theorem | Statement |
|---|---|
| `guard_authorized` | a command the guard accepts is the kernel's own result, each write is permitted in the state the writes before it leave, and each disclosed row is stored, exactly as disclosed, and visible, before or after the command |
| `guard_complete` | the guard accepts every such command, and `guard_app_error`: it passes the kernel's refusals through. `guard_eq` states the three as one equation |
| `guard_viewed_authorized` | with `guardViewed`, an accepted command that writes is `guard`'s case, and an accepted read-only command is the kernel's result on the caller's view, with no writes and only rows stored and visible in the view |
| `guard_viewed_noninterference` | two states with the same view give a read-only command the same result, refusals included |
| `read_only_sound_of_viewed` | a kernel behind `guardViewed` meets `ReadOnlySound`, the read-only obligation of the kernel contract |

[`lean/Notes/Proofs.lean`](lean/Notes/Proofs.lean) applies them to the notes
(`transition_authorized`, `transition_noninterference`, `read_only_sound`) and proves, for every
principal, snapshot and command:

| Theorem | Statement |
|---|---|
| `read_after_put` | after an accepted `putNote`, the same user's `readNote` returns that body and sharing, owned by the note's earlier owner or else by the caller |
| `read_after_delete`, `member_after_add`, `member_after_remove` | after an accepted `deleteNote`, `readNote` finds no note; after `addMember`, the member is stored with its admin flag; after `removeMember`, it is gone |
| `others_unchanged` | a user who is not an admin changes only notes they own, before and after the command |
| `members_unchanged` | a user who is not an admin changes the members only of an organization that has none |
| `admin_not_denied` | the guard denies no command of an admin that writes |
| `owner_may_put`, `owner_may_delete` | the guard denies no edit or delete by a note's owner and no creation under a free id |
| `first_member` | anyone may add the first member of an organization with none |
| `read_note_spec`, `list_notes_spec`, `list_members_spec` | in a snapshot with unique keys, `readNote` returns the note under the id when the caller may see it and `notFound` otherwise, and the listings return exactly the rows the caller may see, in order |
| `rows_stored_run` | every row a reply returns is the row stored under its key in the caller's view |
| `keyed_of_run` | every snapshot a tenant reaches has unique keys |
| `findNote_applyWrite`, `findMember_applyWrite` | what each write does to the row stored under each key |
| `ids_putNote`, `users_putMember` | a new row goes after the stored rows and a replaced row keeps its place |
| `bad_text` | a body is refused exactly when it is empty or longer than 4096 bytes in UTF-8 |
| `not_found` | removing a member or deleting a note that is not stored is refused with `notFound` |

The Rust server ([`rust/notes`](rust/notes)) answers a denied command with 403, a missing note
with 404 and a bad body with 422:

```console
$ export LEANHARBOR_SECRET=dev-secret
$ A=$(LEANHARBOR_ISSUE=1:1 cargo run --release -q --bin leanharbor-notes)
$ B=$(LEANHARBOR_ISSUE=1:2 cargo run --release -q --bin leanharbor-notes)
$ LEANHARBOR_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leanharbor-notes &
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

The same module is generated to Python ([`python/src/leanharbor_notes`](python/src/leanharbor_notes))
and Go ([`go/notes`](go/notes)) and runs behind their memory engines in the differential tests;
neither has a notes server.

## What is proved, and what is trusted

Proved in Lean, about the definitions that are generated and run:

- the six theorems above, for the calculator kernel. The three shells call `transition` and
  `apply`;
- the guard's theorems above, for every kernel and policy, and the notes theorems, for the notes
  kernel. Its `transition` is `handle` behind `guardViewed`, and the three shells call it;
- `Leanharbor.Kernel.Run.inv`: a property that holds for the initial snapshot and is kept by
  every accepted command holds in every snapshot a tenant can reach.

Checked by `make check`, not proved:

- **The theorems constrain the kernel.** [leanassay](https://github.com/conao3/lean-leanassay)
  breaks functions in small ways and runs the theorems on each broken version. For the
  calculator, it breaks `transition`, `apply`, `compute` and the three functions of the trie in
  167 ways: 132 are rejected, 5 behave the same on every input tried, 30 do not compile, and none
  satisfies every theorem while changing an output. For the guard, it breaks
  `guard`, `guardViewed` and the four checks in 28 ways and runs `guard_eq`, `guard_viewed_eq` and
  the lemmas about the checks on random kernels and policies: 22 are rejected, 1 behaves the same,
  5 do not compile, and none satisfies every theorem while changing an output. For the notes, it
  breaks `handle`, `apply`, `applyWrite`, `textOk`, the four functions on the row lists and the
  seven functions of the policy in 180 ways: 108 are rejected, 5 behave the same, 67 do not
  compile, and none satisfies every theorem while changing an output. The notes' `transition` is
  one call of `guardViewed`, and no edit of it compiles.
- **The generated code computes what Lean computes.** 5,000 calculator commands (698 refusals,
  values up to 2^64 − 1) and 3,000 notes commands (1,826 refusals: 1,383 denied by the guard, 336
  not found, 107 bodies refused; bodies of characters of 1 to 4 bytes, up to and past 4096 bytes)
  run through the generated Rust, the generated Python and the generated Go give the same output
  as the kernels compiled natively by Lean.
- **The Rust notes server answers the guard's refusals with 403.** `rust/notes/tests/http.rs`
  sends denied writes, a read of a note the caller may not see (404) and a bad body (422).
- **The code that runs is generated from the proved source.** The build regenerates the three
  targets and fails on a difference from the committed files.
- **No extra axioms.** Every theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

Trusted, with no theorem. The Rust, Python and Go shells are written by hand, and every row
holds for each of them:

| | Trusted |
|---|---|
| Translation | leanfran's Rust, Python and Go backends and their runtimes, rustc, CPython, the Go compiler, Lean's kernel |
| Engine | the memory engine: one command at a time per process, under one lock; replies stored per idempotency key |
| Authentication | the token format and its parser, HMAC-SHA256, the secret and its storage, the system clock |
| Wire format | JSON decoding of commands and encoding of replies and refusals (`Api`) |
| HTTP | axum, hyper and tokio (Rust); `http.server` (Python); `net/http` (Go) |
| Call site | that a shell runs the notes' `transition`. `handle`, the kernel without the guard, is generated and public too, and the guard's theorems say nothing about a caller of `handle` |
| Specification | that `specStep` and the statements above say what a calculator and the notes should do |
| Policy | that `permits`, `visible`, `stored`, `view`, `disclosed` and `readOnly` of the notes say who should see and change what: the guard enforces them as written |

The Python and Go notes kernels run only in the differential tests; only Rust has a notes server.
State lives in the server's memory and is lost on restart. PostgreSQL storage with proved SQL
generation and tenant isolation is designed and not yet built.

## Speed

Measured on a cloud VM with 4 virtual CPUs (Intel Xeon, 2.10 GHz) and 16 GB of memory by
`tools/measure.py`, which runs every measurement alone and writes the runs to
[`docs/speed.json`](docs/speed.json). `tools/speed-charts.py` draws the charts and prints the
tables from that file. Every number is a rate, so higher is better. All numbers come from one
run of the program: the same measurement on another VM of this kind differs by up to 2 times, so
compare rows within this section only.

### One command through the kernel

Commands per second through `transition` and `apply`. Each cell is the inverse of the median
time of three runs; the runs of one cell differ by up to 1.3 times. M is a million.

![Commands per second by the number of users in the tenant](docs/speed-engine.svg)

| Commands per second | 1 user | 100 users | 1,000 users | 10,000 users |
|---|---:|---:|---:|---:|
| Rust, generated kernel, snapshot as a Rust value | 6.37 M | 271,700 | 24,400 | 1,850 |
| Rust, generated kernel, snapshot as a Lean value | 9.8 M | 2.73 M | 290,300 | 25,500 |
| Rust, memory engine | 7.87 M | 2.73 M | 357,800 | 37,600 |
| Rust, the same logic by hand (not proved) | 90.9 M | 23.8 M | 5.43 M | 621,900 |
| Go, memory engine | 726,200 | 532,800 | 124,200 | 3,320 |
| Python, memory engine | 47,300 | 22,300 | 3,120 | 297 |

### Over HTTP, next to servers without a kernel

Replies per second to `POST /rpc` on the same VM, with `oha` for 8 seconds against a tenant of
one user. Each cell is the mean of two runs, and every reply had status 200. The load generator
runs on the same four CPUs as the server.

The servers marked "no kernel" ([`bench/`](bench)) are the usual servers of each language doing
the least a JSON endpoint does: they decode the JSON body and reply with a JSON value. They check
no token, hold no state and call no kernel, so the difference from a leanharbor row is what the
token check, the engine and the generated kernel cost.

![Replies per second over HTTP, Rust](docs/speed-http-rust.svg)

| Replies per second, Rust | get, 1 connection | apply, 1 connection | get, 64 connections | apply, 64 connections |
|---|---:|---:|---:|---:|
| leanharbor, Rust (axum) | 17,100 | 16,800 | 128,000 | 120,800 |
| axum, no kernel | 18,300 | 18,300 | 141,900 | 137,800 |
| actix-web, no kernel | 18,800 | 18,600 | 191,200 | 188,900 |

![Replies per second over HTTP, Go](docs/speed-http-go.svg)

| Replies per second, Go | get, 1 connection | apply, 1 connection | get, 64 connections | apply, 64 connections |
|---|---:|---:|---:|---:|
| leanharbor, Go (net/http) | 10,900 | 9,950 | 68,700 | 62,500 |
| net/http, no kernel | 12,200 | 10,900 | 90,200 | 87,400 |
| gin, no kernel | 11,800 | 12,000 | 74,700 | 70,600 |

![Replies per second over HTTP, Python](docs/speed-http-python.svg)

| Replies per second, Python | get, 1 connection | apply, 1 connection | get, 64 connections | apply, 64 connections |
|---|---:|---:|---:|---:|
| leanharbor, Python (http.server) | 5,960 | 5,350 | 2,940 | 2,470 |
| FastAPI on uvicorn, 4 processes, no kernel | 6,060 | 5,980 | 24,600 | 24,700 |
| Flask on gunicorn, 4 processes, no kernel | 2,900 | 2,940 | 7,700 | 7,510 |

- The Rust shell runs on axum and gives 93% of the replies of axum without a kernel on one
  connection and 90% on 64.
- The Go shell runs on `net/http` and gives 89% of the replies of `net/http` without a kernel on
  one connection and 76% on 64.
- The Python shell is one process on `http.server`, with one lock around the engine. On one
  connection it gives as many replies as FastAPI. On 64 connections it gives fewer than on one,
  while FastAPI and Flask spread the connections over four processes.

A generated function that takes a Rust, Python or Go value converts it to Lean's representation on
every call, and its result back. The engines therefore keep each tenant's snapshot as a Lean
value with one owner (`leanfran::Owned<Snapshot>`, `leanfran.Local`, `leanfran.Value[Snapshot]`)
and convert only the principal, the command and the reply; `apply` receives the only reference
to the snapshot and Lean updates it in place.

The Rust memory engine keeps the snapshots under one lock and runs each command on the thread
that calls it: an `Owned` moves between threads with its lock, and lends the snapshot to one
command at a time. A test (`rust/calculator/tests/in_place.rs`) sends commands from several
threads, some of them refused, and checks that the snapshot is still the kind of Lean object
that is updated in place.

The hand-written logic runs 12 times as many commands as the Rust memory engine for one user,
9 times for 100, 15 times for 1,000 and 17 times for 10,000. The difference is the allocation of
the small Lean objects of each call, and the `List` the kernel keeps its users in: finding a user
walks the list.

The Go memory engine holds the snapshot in a `leanfran.Value` and hands it to `apply` with
`Take()`. A test (`go/calculator/in_place_test.go`) sends commands from several goroutines, some
of them refused, and checks that the snapshot still has one reference (`IsExclusive`).

## Layout

| Path | Contents |
|---|---|
| [`lean/`](lean) | the Lake package: `Leanharbor` (the kernel contract and the authorization guard), `Calculator` and `Notes` (kernels and proofs), `calculator-oracle` and `notes-oracle` (the kernels as native programs) |
| [`audit/`](audit) | the leanassay audits and the axiom check |
| [`rust/leanharbor`](rust/leanharbor) | the Rust shell: `Kernel`, `MemoryEngine`, tokens, `POST /rpc` |
| [`rust/calculator`](rust/calculator) | the generated kernel (`src/generated/`), the server, the benchmark, the differential test |
| [`rust/notes`](rust/notes) | the generated notes kernel (`src/generated/`), the server, the HTTP and differential tests |
| [`python/`](python) | the Python shell (`leanharbor`), the calculator (`leanharbor_calculator`) and the notes (`leanharbor_notes`), each with its generated `kernel.py` |
| [`go/leanharbor`](go/leanharbor) | the Go shell: `Kernel`, `MemoryEngine`, tokens, `POST /rpc` |
| [`go/calculator`](go/calculator) | the generated kernel (`kernel/`), the server and the benchmark (`cmd/`), the differential test |
| [`go/notes`](go/notes) | the generated notes kernel (`kernel/`), the differential test |
| [`bench/`](bench) | servers without a kernel (axum, actix-web, `net/http`, gin, FastAPI, Flask) for the HTTP comparison |
| [`docs/`](docs) | the measured runs (`speed.json`) and the charts drawn from them |
| [`testdata/`](testdata) | the command lists of the differential tests (`tools/gen-commands.py`, `tools/gen-notes-commands.py`) |

## Development

```sh
nix develop --command make check   # format, proofs, audit, generation, Rust, Python and Go tests
nix develop --command make bench
nix run                            # the Rust calculator server
```

`make generate` rewrites the generated Rust, Python and Go from `lean/`.

## License

[Apache-2.0](LICENSE).
