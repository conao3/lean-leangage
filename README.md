<p align="center">
  <img src="docs/assets/banner.png" alt="leangage: web services whose core is one pure function, proved in Lean 4" width="880">
</p>

<p align="center"><strong>Web services whose core is one pure function, proved in Lean 4 and generated to Rust, Python and Go</strong></p>

<p align="center">
  <a href="https://github.com/conao3/lean-leangage/actions/workflows/ci.yml"><img src="https://github.com/conao3/lean-leangage/actions/workflows/ci.yml/badge.svg?branch=master" alt="CI"></a>
  <a href="LICENSE"><img src="https://img.shields.io/github/license/conao3/lean-leangage" alt="License: Apache-2.0"></a>
  <a href="lean/lean-toolchain"><img src="https://img.shields.io/badge/Lean-v4.35.0-blue" alt="Lean v4.35.0"></a>
  <a href="rust/Cargo.toml"><img src="https://img.shields.io/badge/Rust-edition%202024-orange" alt="Rust edition 2024"></a>
  <a href="python/pyproject.toml"><img src="https://img.shields.io/badge/Python-%E2%89%A53.13-3776AB" alt="Python 3.13 or later"></a>
  <a href="go/go.mod"><img src="https://img.shields.io/badge/Go-1.27-00ADD8" alt="Go 1.27"></a>
  <a href="https://github.com/conao3/lean-leangage/stargazers"><img src="https://img.shields.io/github/stars/conao3/lean-leangage?style=flat" alt="GitHub stars"></a>
</p>

<p align="center">
  <a href="#the-calculator">Calculator</a> |
  <a href="#storing-a-kernel-in-postgresql">PostgreSQL</a> |
  <a href="#the-notes">Notes</a> |
  <a href="#what-is-proved-and-what-is-trusted">Proved and trusted</a> |
  <a href="#speed">Speed</a> |
  <a href="#layout">Layout</a> |
  <a href="#development">Development</a>
</p>

# leangage

Web services whose core is one pure function written and proved in Lean 4.

You write the kernel of a service as a Lean function: what a command does to one tenant's state.
You prove what callers rely on, and [leanfran](https://github.com/conao3/lean-leanfran) generates
the function to your language. leangage gives you 3 things around it:

- the contract the kernel fills;
- an authorization guard, proved once for every kernel and policy;
- the server that runs the generated code behind HTTP, in memory or on PostgreSQL.

The same kernel runs today from Rust, from Python and from Go.

The design follows [h5i-app](https://github.com/h5i-dev/h5i/blob/main/crates/h5i-app/README.md),
which does this for Rust by translating Rust to Lean. leangage goes the other way: Lean is the
source, and you get the host language by generation.

## The calculator

A kernel is one pure function. It takes a principal, one tenant's snapshot and a command, and
returns what to store and what to reply, or a refusal.
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

`compute` is `+`, `-`, `*` and `/` on 64-bit numbers. It refuses a result that doesn't fit 64 bits
(`overflow`), a subtraction below zero (`underflow`) and a division by zero (`division_by_zero`).

[`lean/Calculator/Proofs.lean`](lean/Calculator/Proofs.lean) proves 6 theorems for every
principal, snapshot and command. Among them:

- `transition_spec`: the reply is `specStep` (arithmetic on unbounded naturals) of the caller's
  number, and the command is refused exactly when `specStep` refuses;
- `get_after`: after an accepted command, `get` by the same user returns that command's reply;
- `others_unchanged`: a command leaves every other user's number as it was.

### Run it

The 3 servers run the same Lean modules, generated to Rust, to Python and to Go. Inside
`nix develop`, from the root of the repository:

```console
$ export LEANGAGE_SECRET=dev-secret
$ TOKEN=$(cd rust && LEANGAGE_ISSUE=1:7 cargo run --release -q --bin leangage-calculator)
$ cd rust && LEANGAGE_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8080/rpc
{"value":6}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"mul","arg":7}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"get"}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"div","arg":0}' 127.0.0.1:8080/rpc
{"error":"division_by_zero"}
$ cd python && LEANGAGE_LISTEN=127.0.0.1:8081 uv run leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8081/rpc
{"value":6}
$ cd go && LEANGAGE_LISTEN=127.0.0.1:8082 go run ./calculator/cmd/leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8082/rpc
{"value":6}
```

`LEANGAGE_ISSUE=<tenant>:<user>` prints a token that is good for one day. A token issued by one
server is accepted by the others, and a command, a body that is not one and a token that is
refused get the same status and body from the 3.

### One request

The server of each language is written by hand: axum in Rust, `http.server` in Python, `net/http`
in Go. It moves bytes and makes no decision about a request. For `POST /rpc`:

1. The generated `authenticate` reads the `Authorization` header into the claims of its token and
   the bytes its tag signs, or gives the answer (401). The server computes the HMAC-SHA256 of
   those bytes and compares it with the tag.
2. The JSON library of the language reads the body: serde_json, Go's `encoding/json/jsontext`,
   Python's `json`. One conversion file per language packs the tokens it read into one string, in
   the order of the text.
3. The generated `request` takes the claims, the time and the packed string. It refuses an
   expired token, unpacks the tokens and decodes them to a command, or gives the answer (400,
   401, 413).
4. The engine runs the generated `transition` and `apply` on the tenant's snapshot, which it
   keeps in memory or in PostgreSQL.
5. The generated `respond` gives the status and the body for the kernel's reply (200
   `{"value": v}`) or refusal (422 `{"error": name}`), and `failed` those for a failure of the
   engine.

The status and the body of an answer come from those generated functions, and each has theorems.
`decode_ok_iff` and `object_iff`, for one, say that a packed string decodes to a command exactly
when its tokens are those of an object with the fields of that command, in any order and with no
other member.
`make check` runs `tools/check-handlers.py`, which fails when a handler holds a status code or
calls a JSON library. One answer comes from the HTTP library: in Rust, axum itself answers 413 to
a body longer than 2 MiB, before a handler sees it.

The functions, their theorems and the trie that holds a tenant's numbers:
[docs/calculator.md](docs/calculator.md).

## Storing a kernel in PostgreSQL

A kernel declares its tables as a `List Tab` and each row type as an instance of `Leangage.Row`.
[`lean/Calculator/Store.lean`](lean/Calculator/Store.lean) stores the calculator's numbers in one
table keyed by the user:

```lean
def tables : List Tab := [⟨"memories", [⟨"user", .int, false⟩, ⟨"value", .int, false⟩], 1⟩]

def writes : Option Memory → List Write
  | none => []
  | some m => [.put 0 1 (toRow m)]
```

The SQL compiler `Leangage.Sql` is written in Lean and generated to the 3 servers. A PostgreSQL
engine sends only the text that compiler renders for a kernel's tables, with the tenant as `$1`
and the values as the parameters after it. Each command runs in one `SERIALIZABLE` transaction.

Lean proves the compiler against a model of PostgreSQL
([`lean/Leangage/Sql/Model.lean`](lean/Leangage/Sql/Model.lean)): a compiled statement changes
the tenant's rows as the model's `exec` says (`compile_sound`), and statements compiled for one tenant
leave every other tenant's rows as they were (`tenant_isolation`). That PostgreSQL does what the
model says is trusted, and tests on a real server check it.

The Rust, the Python and the Go calculator servers store their snapshots in PostgreSQL when
`LEANGAGE_DATABASE_URL` is set. An administrator first runs one of them with
`LEANGAGE_LOCKDOWN=<owner>:<engine role>`, which creates the tables for those roles and exits.
With the secret and the token of the quickstart:

```console
$ (cd rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=postgres dbname=calc' \
    LEANGAGE_LOCKDOWN=leangage_owner:leangage_engine cargo run --release -q --bin leangage-calculator)
$ cd rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=leangage_engine dbname=calc' \
    LEANGAGE_LISTEN=127.0.0.1:8083 cargo run --release -q --bin leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"add","arg":1}' 127.0.0.1:8083/rpc
{"value":1}
```

The 3 servers can run on one database at once: they read and write the same tables, and a reply
stored under an `Idempotency-Key` by one is replayed by another.

The 3 engines, their contract and the obligations of a `Leangage.Storage`:
[docs/postgresql.md](docs/postgresql.md).

## The notes

[`lean/Notes/Kernel.lean`](lean/Notes/Kernel.lean) keeps notes in an organization with members
and admins, after h5i's notes example. A note is visible to everyone if it is shared, otherwise to
its owner and admins; the owner or an admin edits and deletes it.

The kernel's `handle` decides what each command does and holds no authorization. The policy is
the Bool functions `permits`, `visible` and `stored`. The function the engine runs is `handle`
behind the guard of [`lean/Leangage/Authz.lean`](lean/Leangage/Authz.lean):

```lean
def transition (a : Principal) (s : Snapshot) (c : Command) :
    Except (Guarded Error) (List Write × Reply) :=
  guardViewed handle apply ⟨permits, visible, stored⟩ disclosed readOnly view a s c
```

The guard checks each write, and each row the reply discloses, against the policy. One refused
write or row refuses the whole command with `denied`, and nothing is stored.
[`lean/Leangage/AuthzProofs.lean`](lean/Leangage/AuthzProofs.lean) proves, once for every kernel
and policy:

- `guard_authorized`: a command the guard accepts is the kernel's own result, each write is
  permitted, and each disclosed row is stored and visible;
- `guard_complete`: a command the kernel accepted, whose writes are permitted and whose disclosed
  rows are visible, is accepted by the guard. The guard adds no other refusal;
- `guard_viewed_noninterference`: 2 states with the same view give a read-only command the same
  result, refusals included.

With the same secret, user 1 is an admin and user 2 is no member:

```console
$ A=$(cd rust && LEANGAGE_ISSUE=1:1 cargo run --release -q --bin leangage-notes)
$ B=$(cd rust && LEANGAGE_ISSUE=1:2 cargo run --release -q --bin leangage-notes)
$ cd rust && LEANGAGE_LISTEN=127.0.0.1:8086 cargo run --release -q --bin leangage-notes &
$ curl -s -H "Authorization: Bearer $A" -d '{"cmd":"add_member","user":1,"admin":true}' 127.0.0.1:8086/rpc
{"done":true}
$ curl -s -H "Authorization: Bearer $A" -d '{"cmd":"put_note","id":7,"body":"draft","shared":false}' 127.0.0.1:8086/rpc
{"done":true}
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"read_note","id":7}' 127.0.0.1:8086/rpc
{"error":"not_found"}
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"put_note","id":7,"body":"mine now","shared":true}' 127.0.0.1:8086/rpc
{"error":"denied"}
```

Only Rust has a notes server ([`rust/notes`](rust/notes)). The notes kernel is generated to
Python and Go too, and runs there in the differential tests.

The notes' theorems, requests and responses: [docs/notes.md](docs/notes.md).

## What is proved, and what is trusted

| | What | How |
|---|---|---|
| [Proved](docs/proofs.md#proved) | the calculator and the notes kernel, the authorization guard for every kernel and policy, the SQL compiler against a model of PostgreSQL, tenant isolation, the storage of a kernel, the token format, the JSON writer, the decoding of a request from the tokens of its body, and the status and the body of every answer the generated functions give | theorems in Lean about the definitions that are generated and run; every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` |
| [Checked](docs/proofs.md#checked) | that the generated Rust, Python and Go compute what Lean computes; that the theorems constrain the functions; that the request path calls the generated functions; that the PostgreSQL engines keep their contract | `make check`: differential tests against the kernels compiled natively by Lean (5,000 calculator commands, 3,000 notes commands), [leanassay](https://github.com/conao3/lean-leanassay), which breaks each function in small ways and runs the theorems on the broken versions, `tools/check-handlers.py`, and tests on a PostgreSQL server |
| [Trusted](docs/proofs.md#trusted) | the HTTP transport (axum, `http.server`, `net/http`); the JSON libraries and the conversion files, which hand over the tokens of a body; HMAC-SHA256, the secret and the clock; the memory and the PostgreSQL engines, and PostgreSQL itself; leanfran, rustc, CPython, the Go compiler and Lean's kernel; that the specifications and the policy say what the service should do | no theorem; the tests of the row above check parts of it |

What is proved starts at the tokens of a body. That those tokens are the ones of the text is
trusted to the JSON library of each language, and a test of each states where the 3 differ (a
lone surrogate escape, deep nesting, a number outside the range of a double).

Every theorem, every check with its counts, and every trusted part:
[docs/proofs.md](docs/proofs.md).

## Speed

Replies per second to `POST /rpc`, next to the usual servers of each language without a kernel
([`bench/`](bench)): those decode the JSON body and reply with a JSON value, check no token and
hold no state. Measured with `oha` on a cloud VM with 4 virtual CPUs; each cell is the mean of 2
runs. Every number is a rate, so higher is better.

![Replies per second over HTTP, Rust](docs/speed-http-rust.svg)

| Replies per second, Rust | get, 1 connection | apply, 1 connection | get, 64 connections | apply, 64 connections |
|---|---:|---:|---:|---:|
| leangage, Rust (axum) | 18,800 | 19,000 | 141,700 | 140,500 |
| axum, no kernel | 19,800 | 19,600 | 151,000 | 149,800 |
| actix-web, no kernel | 19,500 | 19,200 | 199,100 | 202,100 |

![Replies per second over HTTP, Go](docs/speed-http-go.svg)

| Replies per second, Go | get, 1 connection | apply, 1 connection | get, 64 connections | apply, 64 connections |
|---|---:|---:|---:|---:|
| leangage, Go (net/http) | 11,700 | 11,700 | 71,700 | 67,800 |
| net/http, no kernel | 12,800 | 12,800 | 96,400 | 92,400 |
| gin, no kernel | 13,100 | 13,000 | 80,600 | 77,100 |

- The Rust server gives 95% of the replies of axum without a kernel to `get` on one connection
  and 94% on 64, and 97% and 94% to `apply`. The 2 runs of a cell differ by up to 14%.
- The Go server gives 91% of the replies of `net/http` without a kernel to `get` on one
  connection and 74% on 64, and 91% and 73% to `apply`.
- The Python server is one process on `http.server`. On one connection it gives 79% of the
  replies of FastAPI to `get` and 71% to `apply`; on 64 connections it gives fewer than on one.

The kernel alone, the Python table, the PostgreSQL engine and the method:
[docs/speed.md](docs/speed.md).

## Layout

| Path | Contents |
|---|---|
| [`lean/`](lean) | the Lean source: `Leangage` (the contract, the guard, the SQL compiler, the token format, the JSON writer, the functions on requests, and their proofs), `Calculator`, `Notes`, and the native programs the differential tests compare with |
| [`audit/`](audit) | the leanassay audits, the axiom check and the obligation check |
| [`rust/`](rust) | the server library `leangage`, the PostgreSQL engine `leangage-pg`, the `calculator` and the `notes` server |
| [`python/`](python) | the server library `leangage` with the PostgreSQL engine `leangage.pg`, the calculator server, the notes kernel |
| [`go/`](go) | the server library `leangage` with the PostgreSQL engine `leangage/pg`, the calculator server, the notes kernel |
| [`bench/`](bench) | the servers without a kernel for the HTTP comparison |
| [`tools/`](tools) | the generators of the test lists, the measurement scripts and `check-handlers.py` |
| [`testdata/`](testdata) | the lists of commands, statements, tokens and requests of the differential tests |
| [`docs/`](docs) | the detail of each section above, the measured runs (`speed.json`) and the charts |

Each directory and its generated files: [docs/layout.md](docs/layout.md).

## Development

```sh
nix develop --command make check   # format, proofs, audit, generation, call sites, Rust, Python and Go tests
nix develop --command make bench
nix run                            # the Rust calculator server
```

`make generate` rewrites the generated Rust, Python and Go from `lean/`. The PostgreSQL tests
start a server of their own with `initdb` and `pg_ctl` from the devShell, in a directory under
`/tmp` that is removed when the test process exits. `make python` and `make go` build the Rust
calculator server, which the Python and the Go tests run next to their own on a shared database.

## License

[Apache-2.0](LICENSE). The SQL compiler is based on h5i; see [`NOTICE`](NOTICE).
