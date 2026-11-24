# leanharbor

Web services whose core is one pure function written and proved in Lean 4.

You write the kernel of a service — what a command does to one tenant's state — as a Lean
function, prove what callers rely on, and [leanfran](https://github.com/conao3/lean-leanfran)
generates it to your language. leanharbor is the contract the kernel fills and the shell that
runs the generated code behind HTTP. The same kernel runs today from Rust and from Python.

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

[`lean/Calculator/Proofs.lean`](lean/Calculator/Proofs.lean) proves, for every principal, snapshot
and command:

| Theorem | Statement |
|---|---|
| `transition_spec` | the reply is `specStep` (arithmetic on unbounded naturals) of the caller's number, and the command is refused exactly when `specStep` refuses |
| `compute_spec` | `compute` is `+`, `-`, `*`, `/` on naturals when the result fits 64 bits, and a refusal otherwise |
| `get_after` | after an accepted command, `get` by the same user returns that command's reply |
| `others_unchanged` | a command leaves every other user's number as it was |
| `read_only_sound` | `get` returns no writes |

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
the same Lean module, generated to Python. Accepted and refused commands get the same status and
body from both servers, and a token issued by one is accepted by the other:

```console
$ cd python && LEANHARBOR_LISTEN=127.0.0.1:8081 uv run leanharbor-calculator &
$ curl -s -H "Authorization: Bearer $TOKEN" -d '{"cmd":"set","value":6}' 127.0.0.1:8081/rpc
{"value":6}
```

## What is proved, and what is trusted

Proved in Lean, about the definitions that are generated and run:

- the five theorems above, for the calculator kernel. Both shells call `transition` and `apply`;
- `Leanharbor.Kernel.Run.inv`: a property that holds for the initial snapshot and is kept by
  every accepted command holds in every snapshot a tenant can reach.

Checked by `make check`, not proved:

- **The theorems constrain the kernel.** [leanassay](https://github.com/conao3/lean-leanassay)
  breaks `transition`, `apply` and `compute` in 60 small ways and runs the theorems on each
  broken version: 48 are rejected, 5 behave the same on every input tried, 7 do not
  compile, and none satisfies every theorem while changing an output.
- **The generated code computes what Lean computes.** 5,000 commands (698 refusals, values up
  to 2^64 − 1) run through the generated Rust and the generated Python give the same output as
  the kernel compiled natively by Lean.
- **The code that runs is generated from the proved source.** The build regenerates both
  targets and fails on a difference from the committed files.
- **No extra axioms.** Every theorem depends only on `propext`, `Classical.choice` and
  `Quot.sound`.

Trusted, with no theorem:

| | Trusted |
|---|---|
| Translation | leanfran's Rust and Python backends and their runtimes, rustc, CPython, Lean's kernel |
| Engine | the memory engine: one command at a time per process, under one lock; replies stored per idempotency key |
| Authentication | the token format and its parser, HMAC-SHA256, the secret and its storage, the system clock |
| Wire format | JSON decoding of commands and encoding of replies and refusals (`Api`) |
| HTTP | axum, hyper and tokio (Rust); `http.server` (Python) |
| Specification | that `specStep` and the statements above say what a calculator should do |

State lives in the server's memory and is lost on restart. PostgreSQL storage with proved SQL
generation and tenant isolation, proved authorization guards, and a Go shell are designed and
not yet built.

## Speed

One command (`transition`, then `apply`), measured with `make bench` on an Intel Core i5-8400:

| | 1 user in the tenant | 100 users | 1,000 users | 10,000 users |
|---|---|---|---|---|
| Rust, generated kernel, snapshot as a Rust value | 213 ns | 3.9 µs | | 722 µs |
| Rust, generated kernel, snapshot as a Lean value | 115 ns | 0.38 µs | | 53 µs |
| Rust, memory engine | 156 ns | 0.42 µs | | 50 µs |
| Rust, the same logic by hand (not proved) | 10 ns | 44 ns | | 2.7 µs |
| Python, memory engine | 30 µs | 63 µs | 421 µs | |

A generated function that takes a Rust or Python value converts it to Lean's representation on
every call, and its result back. Both engines therefore keep each tenant's snapshot as a Lean
value with one owner (`leanfran::Owned<Snapshot>`, `leanfran.Local`) and convert only the
principal, the command and the reply; `apply` receives the only reference to the snapshot and
Lean updates it in place.

The Rust memory engine keeps the snapshots under one lock and runs each command on the thread
that calls it: an `Owned` moves between threads with its lock, and lends the snapshot to one
command at a time. A test (`rust/calculator/tests/in_place.rs`) sends commands from several
threads, some of them refused, and checks that the snapshot is still the kind of Lean object
that is updated in place.

What remains against the hand-written logic (16 times for one user, 10 times for 100, 19 times
for 10,000) is the allocation of the small Lean objects of each call, and the `List` the kernel
keeps its users in: finding a user walks the list.

## Layout

| Path | Contents |
|---|---|
| [`lean/`](lean) | the Lake package: `Leanharbor` (the kernel contract), `Calculator` (kernel and proofs), `calculator-oracle` (the kernel as a native program) |
| [`audit/`](audit) | the leanassay audit and the axiom check |
| [`rust/leanharbor`](rust/leanharbor) | the Rust shell: `Kernel`, `MemoryEngine`, tokens, `POST /rpc` |
| [`rust/calculator`](rust/calculator) | the generated kernel (`src/generated/`), the server, the benchmark, the differential test |
| [`python/`](python) | the Python shell (`leanharbor`) and the calculator (`leanharbor_calculator`, with the generated `kernel.py`) |
| [`testdata/`](testdata) | the command list of the differential tests (`tools/gen-commands.py`) |

## Development

```sh
nix develop --command make check   # format, proofs, audit, generation, Rust and Python tests
nix develop --command make bench
nix run                            # the Rust calculator server
```

`make generate` rewrites the generated Rust and Python from `lean/`.

## License

[Apache-2.0](LICENSE).
