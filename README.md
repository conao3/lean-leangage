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

The server libraries are the crates [`leangage`](https://crates.io/crates/leangage) and
[`leangage-pg`](https://crates.io/crates/leangage-pg), the PyPI package
[`leangage`](https://pypi.org/project/leangage/) and the Go module
`github.com/conao3/lean-leangage/go`.

The design follows [h5i-app](https://github.com/h5i-dev/h5i/blob/main/crates/h5i-app/README.md),
which does this for Rust by translating Rust to Lean. leangage goes the other way: Lean is the
source, and you get the host language by generation.

## The calculator

A kernel is one pure function. A tenant is one organization's data, a snapshot is the state of
one tenant, and a principal is the caller: an organization and a user. The kernel takes a
principal, a snapshot and a command, and returns what to store and what to reply, or a refusal.
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

Among the theorems of [`lean/Calculator/Proofs.lean`](lean/Calculator/Proofs.lean): the reply is
`specStep` (arithmetic on unbounded naturals) of the caller's number, and the command is refused
exactly when `specStep` refuses (`transition_spec`); after an accepted command, `get` by the same
user returns that command's reply (`get_after`); a command leaves every other user's number as
it was (`others_unchanged`).

### Run it

The 3 servers run the same Lean modules, generated to Rust, to Python and to Go. Inside
`nix develop`, from the root of the repository (wait until a server listens before its `curl`):

```console
$ make generate
$ export LEANGAGE_SECRET=dev-secret
$ TOKEN=$(cd rust && LEANGAGE_ISSUE=1:7 cargo run --release -q --bin leangage-calculator)
$ cd rust && LEANGAGE_LISTEN=127.0.0.1:8080 cargo run --release -q --bin leangage-calculator &
$ cd python && LEANGAGE_LISTEN=127.0.0.1:8081 uv run python -m leangage_calculator &
$ cd go && LEANGAGE_LISTEN=127.0.0.1:8082 go run ./calculator/cmd/leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8080/rpc
{"value":6}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"mul","arg":7}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"get"}' 127.0.0.1:8080/rpc
{"value":42}
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"div","arg":0}' 127.0.0.1:8080/rpc
{"error":"division_by_zero"}
```

`LEANGAGE_ISSUE=<organization>:<user>` prints a bearer token that is good for one day. The same
4 requests to port 8081 (Python) and 8082 (Go) get the same 4 replies: a bearer token issued by
one server is accepted by the others, and a command, a body that is not one and a bearer token
that is refused get the same status and body from the 3, except for the JSON texts on which the
3 JSON libraries differ and for bodies longer than 2 MiB.

### One request

The server of each language is written by hand: axum in Rust, `http.server` in Python, `net/http`
in Go. The status and the body of every answer to `POST /rpc` come from generated functions,
except the 413 of step 3:

1. The generated `authenticate` reads the `Authorization` header into the claims of its bearer
   token and the bytes its tag signs, or gives the answer (401). The server computes the
   HMAC-SHA256 of those bytes and compares it with the tag.
2. The JSON library of the language reads the body: serde_json, Go's `encoding/json/jsontext`,
   Python's `json`. One conversion file per language packs the JSON tokens it read into one
   string, in the order of the text.
3. The generated `request` takes the claims, the time and the body: the packed JSON tokens, or
   the fact that the library refused the text, that the body is longer than 2 MiB or that it
   could not be read. It gives the command, or the answer: 401 to an expired bearer token, 400 to
   a body that is no JSON or no command, 413 to a body that is too long. Only the Go server
   passes it such a body: in Rust, axum itself answers 413 before a handler sees the body, and
   the Python server reads a body of any length and answers no 413.
4. The engine runs the generated `transition` and `apply` on the tenant's snapshot, which it
   keeps in memory or in PostgreSQL.
5. The generated `respond` gives the status and the body for the kernel's reply (200
   `{"value": v}`) or refusal (422 `{"error": name}`). `failed` gives those for a tag that
   doesn't match (401), a reused idempotency key (422) and a failure of the engine (503, 500).

`make check` runs `tools/check-handlers.py`, which fails when a handler of `POST /rpc` holds a
status code or calls a JSON library. The functions, their theorems and the trie that holds a tenant's numbers:
[docs/calculator.md](docs/calculator.md).

## Storing a kernel in PostgreSQL

A kernel declares its tables as a `List Tab`, and functions that write each row type to a row,
read it back and turn a write set into row writes.
[`lean/Calculator/Store.lean`](lean/Calculator/Store.lean) stores the calculator's numbers in one
table keyed by the user:

```lean
def tables : List Tab := [⟨"memories", [⟨"user", .int, false⟩, ⟨"value", .int, false⟩], 1⟩]
```

The SQL compiler `Leangage.Sql` is written in Lean and generated to the 3 servers. For a kernel's
tables, a PostgreSQL engine sends only the text that compiler renders, with the tenant as `$1`
and the values as the parameters after it. Its other statements are constants written by hand,
and trusted: the transaction control, the advisory locks, the tables of stored replies and of
tenant versions, and the roles of `lockdown`. A command runs in one `SERIALIZABLE` transaction, a
read-only command without an idempotency key in a `SERIALIZABLE READ ONLY DEFERRABLE` one, and an
attempt that ends in a serialization failure is retried.

Lean proves the compiler against a model of PostgreSQL
([`lean/Leangage/Sql/Model.lean`](lean/Leangage/Sql/Model.lean)). For a schema that `valid`
accepts and tables as `create` made them, a compiled statement runs and changes the tenant's
rows as the model's `exec` says (`compile_sound`), and statements compiled for one tenant leave
every other tenant's rows as they were (`tenant_isolation`). That PostgreSQL does what the model
says is trusted, and tests on a real server check it.

The Rust, the Python and the Go calculator servers store their snapshots in PostgreSQL when
`LEANGAGE_DATABASE_URL` is set. The database (`calc` below) and the engine's role
(`leangage_engine`) must exist, and the role may not be a superuser. An administrator then runs a
server with `LEANGAGE_LOCKDOWN=<owner>:<engine role>`, which creates the tables for those roles
and exits. With the secret and the bearer token of [Run it](#run-it):

```console
$ (cd rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=postgres dbname=calc' \
    LEANGAGE_LOCKDOWN=leangage_owner:leangage_engine cargo run --release -q --bin leangage-calculator)
$ cd rust && LEANGAGE_DATABASE_URL='host=/run/postgresql user=leangage_engine dbname=calc' \
    LEANGAGE_LISTEN=127.0.0.1:8083 cargo run --release -q --bin leangage-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"apply","op":"add","arg":1}' 127.0.0.1:8083/rpc
{"value":1}
```

The 3 servers can run on one database at once: they read and write the same tables, and a reply
stored under an `Idempotency-Key` header, which makes a repeated request get the stored reply, is
replayed by another server.

The 3 engines, their contract and the obligations of a `Leangage.Storage`:
[docs/postgresql.md](docs/postgresql.md).

## The notes

[`lean/Notes/Kernel.lean`](lean/Notes/Kernel.lean) keeps notes in an organization with members
and admins, after h5i's notes example. A note is visible to everyone if it is shared, otherwise to
its owner and admins; the owner or an admin edits and deletes it.

The kernel's `handle` decides what each command does and holds no authorization. The policy is
the Bool functions `permits`, `visible` and `stored`, and `view`, the rows of a snapshot the
caller may see; `disclosed` gives the rows a reply shows. The function the engine runs is `handle`
behind the guard of [`lean/Leangage/Authz.lean`](lean/Leangage/Authz.lean):

```lean
def transition (a : Principal) (s : Snapshot) (c : Command) :
    Except (Guarded Error) (List Write × Reply) :=
  guardViewed handle apply ⟨permits, visible, stored⟩ disclosed readOnly view a s c
```

The guard checks each write, and each row the reply discloses, against the policy. One refused
write or row refuses the whole command with `denied`, and nothing is stored. A read-only command
runs on the caller's view. [`lean/Leangage/AuthzProofs.lean`](lean/Leangage/AuthzProofs.lean)
proves, once for every kernel and policy:

- `guard_authorized`: a command that `guard` accepts is the kernel's own result, each write is
  permitted in the state the writes before it leave, and each disclosed row is stored and
  visible, before or after the command;
- `guard_complete`: `guard` accepts every command the kernel accepted whose writes are permitted
  and whose disclosed rows are stored and visible so. It adds no other refusal;
- `guard_viewed_authorized`: with `guardViewed`, which the notes run, an accepted command that
  writes is `guard`'s case, and an accepted read-only command is the kernel's result on the
  caller's view, with no writes and only rows stored and visible in the view;
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
$ curl -s -H "Authorization: Bearer $B" -d '{"cmd":"put_note","id":7,"body":"mine now","shared":true}' 127.0.0.1:8086/rpc
{"error":"denied"}
```

Only Rust has a notes server ([`rust/notes`](rust/notes)). The notes kernel is generated to
Python and Go too, and runs there in the differential tests. The notes' theorems, requests and
responses: [docs/notes.md](docs/notes.md).

## What is proved, and what is trusted

| | What | How |
|---|---|---|
| [Proved](docs/proofs.md#proved) | the theorems of the calculator and the notes kernel, the authorization guard for every kernel and policy, the SQL compiler against a model of PostgreSQL, tenant isolation of the compiled SQL, the storage of a kernel, the format of the bearer token, the JSON writer, the decoding of a request from the JSON tokens of its body, and the status and the body of every answer the generated functions give | theorems in Lean about the definitions that are generated and run; every theorem depends only on `propext`, `Classical.choice` and `Quot.sound` |
| [Checked](docs/proofs.md#checked) | that the generated Rust, Python and Go compute what Lean computes; that the theorems constrain the functions; that the request path calls the generated functions; that the PostgreSQL engines keep their contract | `make check`: differential tests against the kernels compiled natively by Lean (5,000 calculator commands, 3,000 notes commands), [leanassay](https://github.com/conao3/lean-leanassay), which breaks each function in small ways and runs the theorems on the broken versions, `tools/check-handlers.py`, and tests on a PostgreSQL server |
| [Trusted](docs/proofs.md#trusted) | the HTTP transport (axum, `http.server`, `net/http`); the handlers written by hand, whose text `tools/check-handlers.py` checks for patterns; the JSON libraries and the conversion files: what is proved starts at the JSON tokens of a body, and that those are the ones of its text is trusted (a test of each language states where the 3 libraries differ: a lone surrogate escape, deep nesting, a number outside the range of a double); HMAC-SHA256, the secret and the clock; the memory and the PostgreSQL engines, the database drivers and PostgreSQL itself; leanfran, its runtime libraries, rustc, CPython, the Go compiler and Lean's kernel; that the specifications and the policy say what the service should do | no theorem; the tests of the row above check parts of it |

Every theorem, check and trusted part: [docs/proofs.md](docs/proofs.md).

## Speed

Replies per second to `POST /rpc`, next to the usual servers of each language without a kernel
([`bench/`](bench)): those decode the JSON body and reply with a JSON value, check no bearer
token and hold no state. Measured with `oha` on a cloud VM with 4 virtual CPUs by
`tools/measure.py`; each cell is the mean of 2 runs. Every number is a rate, so higher is better.

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

Across the 4 columns, the Rust server gives 95%, 97%, 94% and 94% of the replies of axum without
a kernel, and the Go server 91%, 92%, 74% and 73% of those of `net/http`. The 2 runs of a cell
differ by up to 6% in the Rust table and up to 14% in the Go table. The Python server, one
process on `http.server`, gives 79% of the replies of FastAPI to `get` and 71% to `apply` on one
connection, and fewer on 64 connections than on one.

The kernel alone, Python, PostgreSQL and the method: [docs/speed.md](docs/speed.md).

## Layout

| Path | Contents |
|---|---|
| [`lean/`](lean) | the Lean source: `Leangage` (the contract, the guard, the SQL compiler, the format of the bearer token, the JSON writer, the functions on requests, and their proofs), `Calculator`, `Notes`, and the native programs the differential tests compare with |
| [`audit/`](audit) | the leanassay audits, the axiom check and the obligation check |
| [`rust/`](rust) | the server library `leangage`, the PostgreSQL engine `leangage-pg`, the `calculator` and the `notes` server |
| [`python/`](python) | the server library `leangage` with the PostgreSQL engine `leangage.pg`, the calculator server, the notes kernel and tables |
| [`go/`](go) | the server library `leangage` with the PostgreSQL engine `leangage/pg`, the calculator server, the notes kernel and tables |
| [`bench/`](bench) | the servers without a kernel for the HTTP comparison |
| [`tools/`](tools) | the generators of the test lists, the measurement scripts and `check-handlers.py` |
| [`testdata/`](testdata) | the lists of commands, SQL statements, bearer tokens, JSON token lists and requests of the differential tests |
| [`docs/`](docs) | the detail of each section above, the measured runs (`speed.json`) and the charts |

Each directory, its generated files and the tests' needs: [docs/layout.md](docs/layout.md).

## Development

```sh
nix develop --command make check   # format, proofs, audit, generation, call sites, Rust, Python and Go tests
nix develop --command make test-go # generation and the tests of one language: test-rust, test-python, test-go
nix develop --command make bench   # commands per second through the kernel; tools/measure.py measures HTTP
nix run                            # the Rust calculator server
```

A release is one run of the workflow, which pushes the tag and publishes `leangage` and
`leangage-pg` to crates.io and `leangage` to PyPI:

```sh
gh workflow run release.yml --ref master -f version_bump=patch
```

`make generate` writes the generated Rust, Python and Go from `lean/` into directories named
`gen`. Git holds the Go ones, which `go get` fetches, and ignores the Rust and Python ones: a
clone holds those after `make generate`, a test target or `make bench`.

## License

[Apache-2.0](LICENSE). Parts of the Lean source are based on h5i; see [`NOTICE`](NOTICE).
