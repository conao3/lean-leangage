# AGENTS.md

leangage: the contract of a kernel proved in Lean 4, and the servers that run the code
[leanfran](https://github.com/conao3/lean-leanfran) generates from it.

## Layout

- `lean/`: Lake package `leangage`, Lean 4.35.0, core only (no Mathlib). `Leangage/Kernel.lean`
  is the contract, `Leangage/Obligation.lean` the statements every kernel's theorems must state
  exactly, `Leangage/Sql.lean` the SQL compiler that is generated,
  `Leangage/Sql/Proofs.lean` its specifications and theorems, `Leangage/Sql/Model.lean` a
  model of PostgreSQL and what a statement means to a tenant, `Leangage/Sql/Sound.lean` the
  theorems that the compiled statements do that under the model, `Leangage/Sql/Isolation.lean`
  tenant isolation, and `Leangage/Store.lean` the class `Row`, the storage of a kernel
  (`Storage`) and the theorems proved once for every storage. `Leangage/Token.lean` is the
  token format that is generated and `Leangage/Token/Proofs.lean` its theorems.
  `Leangage/Json.lean` is the JSON writer that is generated and `Leangage/Json/Proofs.lean`
  its specification (a printer over JSON values, a string lexer) and theorems.
  `Leangage/Json/Lexemes.lean` (generated) holds the tokens of a JSON text as a conversion file
  hands them over, packed in one text (the kinds of the tokens, a line feed, and the texts of the
  numbers, the strings and the keys, each but the last after the count of its characters and a
  colon), the reading of that text into the tokens one by one (`Lexeme`, `unpack`, `texts`), the
  values that are not arrays or objects (`Scalar`), the reading of a number token (`numberOf`)
  and the members of an object (`scalar`, `members`, `object`), and
  `Leangage/Json/Lexemes/Proofs.lean` their theorems. `Leangage/Http.lean` (generated) decides what a
  server answers by itself: the reading of the `Authorization` header, the expiry of a token,
  a body that is not a JSON text, the failures of the engine; `Leangage/Http/Proofs.lean` holds its
  theorems.
  `Calculator/Kernel.lean` holds what is generated, `Calculator/Proofs.lean` the specifications
  and theorems; `Calculator/Store.lean` (generated) the calculator's table and row functions,
  `Calculator/Store/Proofs.lean` the calculator's `Storage` and its theorems;
  `Calculator/Wire.lean` (generated) the calculator's requests and responses (`request`,
  `respond`, `fingerprint`, `scope`), `Calculator/Wire/Proofs.lean` their theorems.
  `Leangage/Authz.lean` is the authorization guard and `Leangage/AuthzProofs.lean` its
  theorems. `Notes/` is the example with a policy, in the layout of `Calculator/`; its tables are
  `Notes/Store.lean` and `Notes/Store/Proofs.lean`, and its requests and responses
  `Notes/Wire.lean` (generated: `request`, `respond`, `fingerprint`, `scope`, `encodeReply`,
  `decodeReply`) and `Notes/Wire/Proofs.lean`.
  `CalculatorOracle.lean`, `NotesOracle.lean`, `SqlOracle.lean`, `TokenOracle.lean`,
  `JsonOracle.lean`, `RequestOracle.lean` and `NotesRequestOracle.lean` are the native programs
  the differential tests compare against. `Oracle/JsonText.lean` (the Lake library `Oracle`) is a
  JSON reader written in Lean, without proofs, that `RequestOracle.lean` and
  `NotesRequestOracle.lean` import to give the expected tokens of a text; it is generated for no
  server.
- `audit/`: a separate Lake package with leanassay (`Audit/Calculator.lean`, `Audit/Sql.lean`,
  `Audit/Store.lean`, `Audit/Token.lean`, `Audit/Json.lean`, `Audit/JsonLexemes.lean`, `Audit/Http.lean`, `Audit/Wire.lean`, `Audit/NotesWire.lean`, `Audit/Authz.lean`,
  `Audit/Notes*.lean`), the axiom
  check (`Audit/Axioms.lean`) and the obligation check `#obligations` (`Audit/Obligations.lean`,
  run on the calculator in `Audit/Calculator.lean` and on the notes in
  `Audit/NotesObligations.lean`). Each file in `audit/fail/` must fail to build with the error on
  its `-- expect:` line; `make check` builds them with `lake -d audit env lean`. A file is built
  only when it is in `roots` of `audit/lakefile.toml` or imported by `Audit.lean`. `#assay`
  derives instances named after the short names of the types it samples, so two audit files whose
  types share a short name (`Snapshot`, `Command`, `Value`, `State`) are separate roots and do
  not import each other.
- `rust/`: Cargo workspace, edition 2024. `leangage` is the server library, `leangage-pg` the engine
  that stores the snapshots in PostgreSQL, `calculator` and `notes` the examples.
- `python/`: uv project. `leangage` is the server library, `leangage.pg` the engine that stores the
  snapshots in PostgreSQL (driver psycopg 3), `leangage_calculator` and `leangage_notes` the
  examples.
- `go/`: Go module `github.com/conao3/lean-leangage/go`. `leangage` is the server library,
  `leangage/pg` the engine that stores the snapshots in PostgreSQL (pgx, pinned in `go.mod`)
  with the test server `leangage/pg/pgtest`, `calculator` and `notes` the examples, with the
  calculator's server and benchmark under `calculator/cmd/`.
- Each server library holds the SQL compiler generated from `Leangage.Sql`: `rust/leangage/src/generated/`
  (`leangage::sql`), `python/src/leangage/sql.py` and `go/leangage/sql/`. The calculator's
  table from `Calculator.Store` is `rust/calculator/src/generated/calculator_store.rs`,
  `python/src/leangage_calculator/store.py` and `go/calculator/store/`, and the notes' tables
  from `Notes.Store` are `rust/notes/src/generated/notes_store.rs`,
  `python/src/leangage_notes/store.py` and `go/notes/store/`. Each server library holds
  the token format generated from `Leangage.Token` (`leangage::token_format`,
  `python/src/leangage/token_format.py`, `go/leangage/token/`), the JSON writer generated from
  `Leangage.Json` (`leangage::json_format`, `python/src/leangage/json_format.py`,
  `go/leangage/jsonformat/`), the functions on the tokens of a JSON text generated from
  `Leangage.Json.Lexemes` (`leangage::json_lexemes`, `python/src/leangage/json_lexemes.py`,
  `go/leangage/jsonlexemes/`) and the
  functions generated from `Leangage.Http` (`leangage::http_format`,
  `python/src/leangage/http_format.py`, `go/leangage/httpformat/`). `Leangage.Http` is generated
  with the types of `Leangage.Json.Lexemes` (`--type-module` in Python and Go; in Rust by
  `leanfran module generate` with
  `--type-path Leangage.Json.Lexemes=crate::generated::leangage_json_lexemes`, run after
  `project generate`). The calculator's functions
  from `Calculator.Wire` are `rust/calculator/src/generated/calculator_wire.rs`,
  `python/src/leangage_calculator/wire.py` and `go/calculator/wire/`, generated with the types
  of the kernel, of `Leangage.Http` and of `Leangage.Json.Lexemes` as the table is with those of
  `Leangage.Sql`. The notes' functions from `Notes.Wire` are
  `rust/notes/src/generated/notes_wire.rs`, generated for Rust only, since only Rust has a notes
  server. Its `--type-path` lists `Leangage.Json.Lexemes` before `Leangage.Json`, which is a prefix
  of it, and maps `Leangage.Authz` to `crate::authz`, the module of `rust/notes/src/lib.rs`
  that gives the kernel's refusal the name the generated file uses.
- The request path of the calculator and of the notes passes bytes and tokens to generated functions: the `token` module of
  each server library calls `encodePayload` and `join` to issue a token, calls `authenticate`
  with the `Authorization` header and computes and compares the HMAC of the payload it returns;
  the handler (`rust/leangage/src/http.rs`, `python/src/leangage/http.py`,
  `go/leangage/http.go`) reads the body into tokens with the conversion file of its language
  (`rust/leangage/src/json_text.rs`, `python/src/leangage/json_text.py`,
  `go/leangage/json_text.go`), calls the kernel's `request` with the claims, the time and the
  body (`Body.json` of the tokens, or `Body.notJson` for bytes the library refuses), runs the engine, and sends the status and the body that the kernel's `respond` or `failed`
  returns. `tools/check-handlers.py` (`make handlers`, part of `make check`) fails when one of
  those files, or the file of the calculator or of the notes that passes the calls on
  (`rust/notes/src/lib.rs`, which also passes `Storage::encode_reply` and `decode_reply` to
  `encodeReply` and `decodeReply`), holds a JSON library, a status code or the JSON writer, or
  lacks a call of a generated function or of the conversion file. A change to a handler keeps it
  passing; a new decision about a request goes into `lean/`.
- The Python calculator (`python/src/leangage_calculator/__init__.py`) calls `wire.request.lean`
  and reads its result with the generated `answerOf`, `actorOf` and `cmdOf`, so the principal and
  the command reach `kernel.transition` as Lean handles. A kernel function that takes the
  principal or the command is called through its `.lean` variant there, which takes a handle or a
  Python value.
- A JSON library is called in the conversion file of each language only (`json_text.rs`,
  `json_text.py`, `json_text.go`: serde_json, `json`, `encoding/json`, whose token reader
  `encoding/json/jsontext` the Go file takes from a `sync.Pool`). The file hands over the
  tokens of the text in the order of the document, a member twice as two members, packed in one
  text: a character for the kind of each token (`{`, `}`, `[`, `]`, `n`, `t`, `f`, `#` for a
  number, `s` for a string, `k` for a key), a line feed, and the texts of the numbers, the
  strings and the keys, a number as the text of its token, each text but the last after the
  count of its characters and a colon. It looks up no member, checks no type of a value and fills in
  no default. `tools/check-handlers.py` fails when one of the 3 lacks the library's reading calls
  or holds a status code, a member lookup, a comparison with a text or a type of the library that
  holds a whole value. `rust/leangage/tests/json_library.rs`,
  `go/leangage/json_library_test.go` and `python/test/test_json_library.py` state what each
  library does with the texts on which the 3 differ (a lone surrogate escape, deep nesting, a
  number outside the range of a double); those texts stay out of `testdata/request-cases.txt`.
- The Rust calculator's table is generated by `leanfran module generate` with
  `--type-path Calculator.Kernel=crate::generated::calculator_kernel Leangage.Sql=::leangage::sql`,
  so that `load` and `writes` take and return the kernel's types and those of `leangage::sql`;
  `rust/calculator/src/lib.rs` declares it as the module `store`. The notes' tables are generated
  the same way, with `Notes.Kernel=crate::generated::notes_kernel`. A kernel stored in PostgreSQL
  implements `leangage::Storage` by delegating to such a module.
- The Python calculator's table is generated by `leanfran-python module generate` with
  `--type-module Calculator.Kernel=leangage_calculator.kernel Leangage.Sql=leangage.sql`, so
  that `load` returns the kernel's `Snapshot` that `transition` takes and `writes` takes the
  write set `transition` returns. `leangage_calculator.STORAGE` fills a `leangage.Storage`
  with it. The Python notes' tables are generated the same way, with
  `Notes.Kernel=leangage_notes.kernel`.
- The Go calculator's table is generated by `leanfran-go module generate` with
  `--type-module Calculator.Kernel=github.com/conao3/lean-leangage/go/calculator/kernel` and
  `--type-module Leangage.Sql=github.com/conao3/lean-leangage/go/leangage/sql`, so that
  the package `store` takes and returns the types of the packages `kernel` and `sql`. The
  calculator implements `leangage.Storage` with it.

## Lean and the host languages

- Lean owns the kernel: types, `transition`, `apply`, and every decision about a command.
  Definitions that are generated go in a module without proofs (`Calculator.Kernel`); theorems
  and specifications go in a module beside it (`Calculator.Proofs`).
- The servers own input and output: HTTP, the HMAC of a token, the clock, the engine. They call
  generated functions and make no decision about a request or a command themselves. The PostgreSQL engines send only the
  text of the generated `render` for a kernel's tables, with the values as parameters; their own
  statements are the constants of `rust/leangage-pg/src/lib.rs`,
  `python/src/leangage/pg/__init__.py` and `go/leangage/pg/pg.go` (transaction control,
  advisory locks, `leangage_idempotency`, `leangage_version`; the last three of the same text
  in the three, and the transaction control of the same text in Rust and Go, so that the servers
  share a database; a change to one is made to the others) and the role statements of
  `lockdown`. A transaction that writes a tenant's rows advances the tenant's row of
  `leangage_version` in the same transaction. The Python engine
  runs statements through psycopg's `RawCursor`, which sends the text unchanged, and the
  constants without parameters with `prepare=False`, so that COMMIT stays a simple query.
- The contract uses `Except` for refusals. The memory engines keep each tenant's snapshot as a Lean
  value with one owner (`leanfran::Owned` in Rust, lent as a `Local` by `Kernel::lend`;
  `leanfran.Local` in Python; `leanfran.Value` in Go) and call the generated functions that take
  one (`kernel::local::apply` in Rust, `kernel.apply.local` in Python, `kernel.Handle.Apply` in Go).
  `apply` must receive the only reference to the snapshot (a move in Rust, `take()` in Python,
  `Take()` in Go), and no `Local` may leave the closure of `lend`, or Lean copies instead of
  updating in place. The PostgreSQL engines keep the snapshots they remember the same way, and an
  attempt takes its tenant's snapshot out of the cache, so that it holds the only reference. `rust/calculator/tests/in_place.rs` and `go/calculator/in_place_test.go`
  check it.
- In Go, every handle belongs to a `leanfran.Region`, and the calls of one region run one at a
  time. The memory engine gives each tenant a region and a lock, the PostgreSQL engine each
  snapshot it loads a region, which stays with the snapshot while the engine remembers it, and a
  kernel's `Scoped` runs its calls in the region it is given with `region.WithValues`, calling
  only `kernel.Handle.In(scope)` and `kernel.Value.In(scope)` inside it. A handle that is neither
  closed nor taken keeps its Lean reference, and what it shares is then copied instead of updated
  in place: close the reply and the snapshot an engine drops (`Release`, `MemoryEngine.Close`,
  `pg.Engine.Close`), and give the write set to `Apply`, which takes it; `Writes` reads it. The
  concurrent tests of `go/calculator` and `go/notes` and `TestPostgresEngineLeaksNoValue` count
  the leaks with `leanfran.TrackLeakedValues`.
- Generated files (`rust/*/src/generated/`, `python/src/leangage_*/kernel.py`,
  `python/src/leangage_calculator/store.py`, `python/src/leangage_calculator/wire.py`,
  `go/*/kernel/`, `go/calculator/store/`, `go/calculator/wire/`, and the SQL compiler, the token
  format, the JSON writer, the functions of `Leangage.Json.Lexemes` and the functions of `Leangage.Http` in each server
  library) are committed and never edited.
  Run `make generate` after changing `lean/`.
- A function the servers call on every request takes `String`s and writes into an `Array UInt8`
  with loops over indices (`parseString`, `writeArray`), so a call converts no list of bytes. Its
  theorem states it equal to the definition over `List UInt8` (`parseString_spec`,
  `writeArray_spec`), whose theorems then hold for it, and the differential tests run both.
  `bench-bytes` in the Makefile times the two side by side, on its line (d) the reading of a
  body by the JSON library, the conversion and the generated `request`, and on its line (f) the
  server's `/rpc` handling called in process (token check, body, generated `request`, engine,
  `respond`) for the `get` and the `apply` body of `tools/measure.py`, which shows what a request
  costs the server apart from the socket. A body crosses into the generated code as 1 text
  whatever its number of tokens, for the same reason: a call converts each value that crosses,
  and in Go each Lean string and each list cell is an allocation. The kernels' functions compare member names and strings with `String`
  equality, and `numberOf` reads the digits of a number token with `Token.numberAt`. A function
  that reads the common spelling from the start of the packed text and the number at its end
  stands beside the one that decides every input from the unpacked tokens (`spelled` beside
  `unpack` and `decodeObject` in `Calculator.Wire`), with a theorem that the function the servers
  call is the second on every input (`decode_eq`), so that the other theorems hold for it.
- Authorization is the guard of `Leangage.Authz`: a kernel's `handle` decides a command with no
  authorization of its own, and the generated `transition` is `handle` behind `guardViewed` with
  the kernel's policy. The servers call `transition` only.
- When a function is added to a generated module, add a theorem about it and list it in the
  module's audit file (`audit/Audit/Calculator.lean`, `audit/Audit/Sql.lean`,
  `audit/Audit/Store.lean`, `audit/Audit/Token.lean`, `audit/Audit/Json.lean`,
  `audit/Audit/JsonLexemes.lean`, `audit/Audit/Http.lean`, `audit/Audit/Wire.lean`,
  `audit/Audit/NotesWire.lean`, `audit/Audit/Notes*.lean`) in the same change. A hypothesis of an audited theorem calls no
  generated function: a broken version of the function would change the hypothesis with the
  conclusion. A theorem stated on every input (`object_shape`, on any list of tokens) has no
  hypothesis to break.
  Theorems whose hypothesis fixes the result of the function (`transition a s c = .ok …`) cannot
  be run by leanassay; state the runnable form with `match` (`get_after_run`) and derive the
  other from it.
- The README states what is proved, what is checked and what is trusted. Keep its numbers equal
  to what `make check` and `make bench` print.

## Commands

All commands run inside `nix develop`.

- `make check`: `nix fmt -- --ci`, `lake -d lean build --wfail`, `lake -d audit build --wfail`,
  regeneration with `git diff --exit-code`, `tools/check-handlers.py`,
  `cargo clippy -- -D warnings`, `cargo test`, `uv run pytest`, `go vet`, `go test -race`.
- `make generate`, `make format`, `make bench`.
- The README's Speed section shows rates (higher is better) with a chart for each table, and
  every cell has a value. `python3 tools/measure.py` runs every measurement and writes
  `docs/speed.json`; it needs PostgreSQL's `initdb`, `pg_ctl` and `psql` on `PATH` or in
  `/usr/lib/postgresql/<version>/bin`, starts a server with the default settings in a temporary
  directory for the PostgreSQL measurements only (as root, as the user `postgres`), and stops with
  an error before measuring anything when PostgreSQL is missing. `python3 tools/speed-charts.py`
  draws `docs/speed-*.svg` and prints the tables to paste into the README. `bench/` holds the
  servers without a kernel that the HTTP measurement compares with (`axum_postgres` for the
  PostgreSQL engine); `make check` does not build them.
- The PostgreSQL tests (`rust/leangage-pg/tests/`, `tests/postgres.rs` and
  `tests/differential.rs` of `rust/calculator` and `rust/notes`; `python/test/test_pg_*.py`;
  `go/leangage/pg/*_test.go`, `go/calculator/postgres_test.go`) start one server per test
  process with `leangage_pg::testing::cluster`, `leangage.pg.testing.cluster` or
  `pgtest.Start` (`initdb` and `pg_ctl` from the devShell, a Unix socket under `/tmp`) and give
  each test a database of its own; a test that cannot start the server fails. Queries of
  `pg_locks` and `pg_stat_activity` in a test filter on the test's database, since tests run in
  parallel on one server.
- The differential tests read the oracles' paths from `LEANGAGE_CALCULATOR_ORACLE`,
  `LEANGAGE_NOTES_ORACLE`, `LEANGAGE_SQL_ORACLE`, `LEANGAGE_TOKEN_ORACLE`,
  `LEANGAGE_JSON_ORACLE`, `LEANGAGE_REQUEST_ORACLE` and `LEANGAGE_NOTES_REQUEST_ORACLE`; the
  Makefile sets them. The Python and the Go tests run the Rust
  calculator server from `LEANGAGE_RUST_CALCULATOR`, which `make python` and `make go` build and
  set. `tools/gen-commands.py` and `tools/gen-notes-commands.py` write the command lists.
  `testdata/sql-statements.txt` comes from `python3 tools/gen-statements.py 3000`,
  `testdata/token-cases.txt` from `python3 tools/gen-tokens.py 3000`,
  `testdata/json-cases.txt` from `python3 tools/gen-json.py 3000` and
  `testdata/request-cases.txt` from `python3 tools/gen-requests.py 3000` and
  `testdata/notes-request-cases.txt` from `python3 tools/gen-notes-requests.py 3000`; their line
  formats are described in `lean/SqlOracle.lean`, `lean/TokenOracle.lean`,
  `lean/JsonOracle.lean`, `lean/RequestOracle.lean` and `lean/NotesRequestOracle.lean`. A body and
  a JSON text of the request lists are bytes: the oracles read them with `Oracle/JsonText.lean`
  and pack the tokens with `pack`, and each language's test reads them with its conversion
  file and prints the `tokens` rows through the generated `unpack`, so the rows compare
  what the library hands over with that reader.
- A spec in a proofs module calls no generated function that the same `#assay` breaks, so that
  `#assay` does not break it along with the function (`kindOf` in `Leangage.Sql.Proofs` beside
  the generated `valKind`; `scalarOf` calls `numberOf`, which `Audit/JsonLexemes.lean` breaks in
  an `#assay` of its own).
- The servers read `LEANGAGE_SECRET` and `LEANGAGE_LISTEN`; `LEANGAGE_ISSUE=<org>:<user>`
  prints a one-day token and exits. The Rust, the Python and the Go calculator servers and the
  Rust notes server store the snapshots in PostgreSQL when `LEANGAGE_DATABASE_URL` is set; with
  `LEANGAGE_LOCKDOWN=<owner>:<engine role>` and an administrator's connection string they create
  the tables for those roles and exit.

## Conventions

- Commit messages, comments and documents are in English.
- The leanfran compilers come from the flake input pinned to a release commit; the crate, the
  PyPI package and the Go module are pinned to the same version (`=0.13.2`, `==0.13.2`,
  `v0.13.2`).
