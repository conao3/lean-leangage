# Layout

| Path | Contents |
|---|---|
| [`lean/`](../lean) | the Lake package: `Leangage` (the kernel contract, the obligations, the SQL compiler, a model of PostgreSQL, tenant isolation, the storage of a kernel, the token format, the JSON writer, the functions on the tokens of a JSON text, the functions on requests and responses, the authorization guard, and their proofs), `Calculator` (kernel, table, requests and responses, and proofs), `Notes` (kernel, policy, tables, requests and responses, and proofs), `calculator-oracle`, `notes-oracle`, `sql-oracle`, `token-oracle`, `json-oracle`, `request-oracle` and `notes-request-oracle` (the kernels, the SQL compiler, the token format, the JSON writer and the functions on requests as native programs), `Oracle` (the JSON reader of the last 2) |
| [`audit/`](../audit) | the leanassay audits, the axiom check and the obligation check, with the files that must fail it (`fail/`) |
| [`tools/`](../tools) | the generators of the test lists, the measurement scripts, and `check-handlers.py`, the check that the request path calls the generated functions and that the JSON library is called in the conversion files only |
| [`rust/leangage`](../rust/leangage) | the Rust server library: `Kernel`, `Storage`, `MemoryEngine`, tokens, `POST /rpc` (`http`), the conversion from serde_json to tokens (`json_text`), the generated SQL compiler, token format, JSON writer, functions on the tokens of a JSON text and functions on requests and responses (`src/gen/`) |
| [`rust/leangage-pg`](../rust/leangage-pg) | the PostgreSQL engine, `lockdown` (the owner and the engine's role), the contract tests and the test server (`testing`) |
| [`rust/calculator`](../rust/calculator) | the generated kernel, table and functions on the wire (`src/gen/`), the server, the benchmarks, the HTTP, differential and PostgreSQL tests |
| [`rust/notes`](../rust/notes) | the generated notes kernel, tables and functions on the wire (`src/gen/`), the server, the HTTP, differential and PostgreSQL tests |
| [`python/`](../python) | the Python server library (`leangage`, with the generated `gen/sql.py`, `gen/token_format.py`, `gen/json_format.py`, `gen/json_lexemes.py` and `gen/http_format.py`, the conversion from `json` to tokens `json_text.py`, and `leangage.pg`: the PostgreSQL engine, `lockdown` and the test server `testing`), the calculator (`leangage_calculator`, with the generated `gen/kernel.py`, `gen/store.py` and `gen/wire.py`), the notes (`leangage_notes`, with the generated `gen/kernel.py` and `gen/store.py`), and the tests (`test/`, among them the PostgreSQL engine's contract tests) |
| [`go/leangage`](../go/leangage) | the Go server library: `Kernel`, `Storage`, `MemoryEngine`, tokens, `POST /rpc`, the generated SQL compiler (`gen/sql/`), token format (`gen/token/`), JSON writer (`gen/jsonformat/`), functions on the tokens of a JSON text (`gen/jsonlexemes/`) and functions on requests and responses (`gen/httpformat/`), and the conversion from `encoding/json/jsontext` to tokens (`json_text.go`) |
| [`go/leangage/pg`](../go/leangage/pg) | the PostgreSQL engine, `Lockdown` (the owner and the engine's role), the contract tests and the test server (`pgtest/`) |
| [`go/calculator`](../go/calculator) | the generated kernel (`gen/kernel/`), table (`gen/store/`) and functions on the wire (`gen/wire/`), the server and the benchmarks (`cmd/`), the HTTP, differential and PostgreSQL tests |
| [`go/notes`](../go/notes) | the generated notes kernel (`gen/kernel/`) and tables (`gen/store/`), the differential test |
| [`bench/`](../bench) | servers without a kernel (axum, actix-web, `net/http`, gin, FastAPI, Flask, and axum with tokio-postgres) for the HTTP comparison |
| [`docs/`](.) | the files the README's sections link to, the measured runs (`speed.json`) and the charts drawn from them |
| [`testdata/`](../testdata) | the command lists (`tools/gen-commands.py`, `tools/gen-notes-commands.py`), the statement list (`tools/gen-statements.py`), the token list (`tools/gen-tokens.py`), the JSON token lists (`tools/gen-json.py`) and the request lines (`tools/gen-requests.py`, `tools/gen-notes-requests.py`) of the differential tests |

## Generation and tests

`make generate` writes the generated Rust, Python and Go from `lean/` into directories named
`gen`, which git ignores. The PostgreSQL tests start a server of their own with `initdb`
and `pg_ctl` from the devShell, in a directory under `/tmp` that is removed when the test process
exits. `make test-rust`, `make test-python` and `make test-go` each generate and test one
language, and `make test` runs the 3. `make test-python` and `make test-go` build the Rust
calculator server, which the Python and the Go tests run next to their own on a shared database.
