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

- the five theorems above, for the calculator kernel. The Rust shell calls `transition`. The
  Python backend of leanfran 0.7.0 cannot return `Except` from a public function, so the Python
  shell calls `step`, which returns the same result as an inductive type; `step_eq` states that
  it is `transition`;
- `Leanharbor.Kernel.Run.inv`: a property that holds for the initial snapshot and is kept by
  every accepted command holds in every snapshot a tenant can reach.

Checked by `make check`, not proved:

- **The theorems constrain the kernel.** [leanassay](https://github.com/conao3/lean-leanassay)
  breaks `transition`, `apply`, `compute` and `step` in 65 small ways and runs the theorems on
  each broken version: 51 are rejected, 5 behave the same on every input tried, 9 do not
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
| Engine | the memory engine: one command at a time per process, replies stored per idempotency key |
| Authentication | the token format and its parser, HMAC-SHA256, the secret and its storage, the system clock |
| Wire format | JSON decoding of commands and encoding of replies and refusals (`Api`) |
| HTTP | axum, hyper and tokio (Rust); `http.server` (Python) |
| Specification | that `specStep` and the statements above say what a calculator should do |

State lives in the server's memory and is lost on restart. PostgreSQL storage with proved SQL
generation and tenant isolation, proved authorization guards, and a Go shell are designed and
not yet built.

## Speed

One command through the generated kernel (`transition`, then `apply`) and through the memory
engine, measured with `make bench` on an Intel Core i5-8400:

| | 1 user in the tenant | 100 users | 1,000 users | 10,000 users |
|---|---|---|---|---|
| Rust, generated kernel | 260 ns | 15.1 µs | | 1.52 ms |
| Rust, memory engine | 321 ns | 15.3 µs | | 1.53 ms |
| Rust, the same logic by hand (not proved) | 9 ns | 43 ns | | 2.7 µs |
| Python, memory engine | 44 µs | 837 µs | 8.9 ms | |

The generated kernel is 29 times slower than the hand-written logic for a tenant of one user and
350 times slower for a tenant of 100. Nearly all of that is conversion: each public function
converts its arguments from the host language's values to Lean's and its result back, and a
command converts the whole snapshot once in `transition` and once each way in `apply`. For 100
users, converting the snapshot to Lean and back takes 7.5 µs (75 ns per row), half of the
15.1 µs; cloning it takes 64 ns. Over HTTP on the same machine, with `oha` using 64 connections
against the Rust server, a tenant of one user serves 81,000 `get` and 71,000 `apply` requests
per second.

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
