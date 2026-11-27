# Layout

| Path | Contents |
|---|---|
| [`lean/`](../lean) | the Lake package: `Leangage` (the kernel contract, the obligations, the SQL compiler, a model of PostgreSQL, tenant isolation, the storage of a kernel, the token format, the JSON writer, the functions on the tokens of a JSON text, the functions on requests and responses, the authorization guard, and their proofs), `Calculator` (kernel, table, requests and responses, and proofs), `Notes` (kernel, policy, tables, requests and responses, and proofs), `calculator-oracle`, `notes-oracle`, `sql-oracle`, `token-oracle`, `json-oracle`, `request-oracle` and `notes-request-oracle` (the kernels, the SQL compiler, the token format, the JSON writer and the functions on requests as native programs), `Oracle` (the JSON reader of the last 2) |
| [`audit/`](../audit) | the leanassay audits, the axiom check and the obligation check, with the files that must fail it (`fail/`) |
| [`tools/`](../tools) | the generators of the test lists, the measurement scripts, and `check-handlers.py`, the check that the request path calls the generated functions and that the JSON library is called in the conversion files only |
| [`rust/leangage`](../rust/leangage) | the Rust server library: `Kernel`, `Storage`, `MemoryEngine`, tokens, `POST /rpc` (`http`), the conversion from serde_json to tokens (`json_text`), the generated SQL compiler, token format, JSON writer, functions on the tokens of a JSON text and functions on requests and responses (`src/generated/`) |
| [`rust/leangage-pg`](../rust/leangage-pg) | the PostgreSQL engine, `lockdown` (the owner and the engine's role), the contract tests and the test server (`testing`) |
| [`rust/calculator`](../rust/calculator) | the generated kernel, table and functions on the wire (`src/generated/`), the server, the benchmarks, the HTTP, differential and PostgreSQL tests |
| [`rust/notes`](../rust/notes) | the generated notes kernel, tables and functions on the wire (`src/generated/`), the server, the HTTP, differential and PostgreSQL tests |
| [`python/`](../python) | the Python server library (`leangage`, with the generated `sql.py`, `token_format.py`, `json_format.py`, `json_lexemes.py` and `http_format.py`, the conversion from `json` to tokens `json_text.py`, and `leangage.pg`: the PostgreSQL engine, `lockdown` and the test server `testing`), the calculator (`leangage_calculator`, with the generated `kernel.py`, `store.py` and `wire.py`), the notes (`leangage_notes`, with the generated `kernel.py` and `store.py`), and the tests (`test/`, among them the PostgreSQL engine's contract tests) |
| [`go/leangage`](../go/leangage) | the Go server library: `Kernel`, `Storage`, `MemoryEngine`, tokens, `POST /rpc`, the generated SQL compiler (`sql/`), token format (`token/`), JSON writer (`jsonformat/`), functions on the tokens of a JSON text (`jsonlexemes/`) and functions on requests and responses (`httpformat/`), and the conversion from `encoding/json/jsontext` to tokens (`json_text.go`) |
| [`go/leangage/pg`](../go/leangage/pg) | the PostgreSQL engine, `Lockdown` (the owner and the engine's role), the contract tests and the test server (`pgtest/`) |
| [`go/calculator`](../go/calculator) | the generated kernel (`kernel/`), table (`store/`) and functions on the wire (`wire/`), the server and the benchmarks (`cmd/`), the HTTP, differential and PostgreSQL tests |
| [`go/notes`](../go/notes) | the generated notes kernel (`kernel/`) and tables (`store/`), the differential test |
| [`bench/`](../bench) | servers without a kernel (axum, actix-web, `net/http`, gin, FastAPI, Flask, and axum with tokio-postgres) for the HTTP comparison |
| [`docs/`](.) | the files the README's sections link to, the measured runs (`speed.json`) and the charts drawn from them |
| [`testdata/`](../testdata) | the command lists (`tools/gen-commands.py`, `tools/gen-notes-commands.py`), the statement list (`tools/gen-statements.py`), the token list (`tools/gen-tokens.py`), the JSON token lists (`tools/gen-json.py`) and the request lines (`tools/gen-requests.py`, `tools/gen-notes-requests.py`) of the differential tests |

## Generation and tests

`make generate` writes the generated Rust, Python and Go from `lean/`, and git ignores them. The
PostgreSQL tests start a server of their own with `initdb` and `pg_ctl` from the devShell, in a
directory under `/tmp` that is removed when the test process exits. `make python` and `make go`
build the Rust calculator server, which the Python and the Go tests run next to their own on a
shared database.
