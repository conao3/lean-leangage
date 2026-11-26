ORACLE := $(CURDIR)/lean/.lake/build/bin/calculator-oracle
SQL_ORACLE := $(CURDIR)/lean/.lake/build/bin/sql-oracle
TOKEN_ORACLE := $(CURDIR)/lean/.lake/build/bin/token-oracle
NOTES_ORACLE := $(CURDIR)/lean/.lake/build/bin/notes-oracle
JSON_ORACLE := $(CURDIR)/lean/.lake/build/bin/json-oracle
REQUEST_ORACLE := $(CURDIR)/lean/.lake/build/bin/request-oracle
NOTES_REQUEST_ORACLE := $(CURDIR)/lean/.lake/build/bin/notes-request-oracle
RUST_CALCULATOR := $(CURDIR)/rust/target/debug/leangage-calculator
GENERATED := rust/calculator/src/generated python/src/leangage_calculator/kernel.py go/calculator/kernel \
	python/src/leangage_calculator/store.py go/calculator/store \
	rust/leangage/src/generated python/src/leangage/sql.py go/leangage/sql \
	python/src/leangage/token_format.py go/leangage/token \
	python/src/leangage/json_format.py go/leangage/jsonformat \
	python/src/leangage/json_lexemes.py go/leangage/jsonlexemes \
	python/src/leangage/http_format.py go/leangage/httpformat \
	python/src/leangage_calculator/wire.py go/calculator/wire \
	rust/notes/src/generated python/src/leangage_notes/kernel.py go/notes/kernel \
	python/src/leangage_notes/store.py go/notes/store

.PHONY: all
all: check

.PHONY: check
check: format-check lean audit generated-check handlers rust python go

.PHONY: format
format:
	nix fmt

.PHONY: format-check
format-check:
	nix fmt -- --ci

.PHONY: lean
lean:
	lake -d lean build --wfail Leangage Calculator Notes calculator-oracle sql-oracle token-oracle notes-oracle json-oracle request-oracle notes-request-oracle

.PHONY: audit
audit: lean
	lake -d audit build --wfail
	@for f in audit/fail/*.lean; do \
	  expect="$$(sed -n 's/^-- expect: //p' "$$f")"; \
	  if [ -z "$$expect" ]; then echo "$$f: no -- expect: line"; exit 1; fi; \
	  if out="$$(lake -d audit env lean "$$f" 2>&1)"; then echo "$$f: built, but must fail"; exit 1; fi; \
	  if [ "$$(printf '%s\n' "$$out" | grep -c ': error')" != 1 ] || ! printf '%s\n' "$$out" | grep -qF -- "$$expect"; then \
	    printf '%s\n' "$$out"; echo "$$f: must fail with the one error: $$expect"; exit 1; \
	  fi; \
	  echo "$$f: fails with: $$expect"; \
	done

.PHONY: generate
generate: lean
	leanfran project generate --lake-dir lean --output-dir rust/calculator/src/generated --modules Calculator.Kernel --output text
	leanfran module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-path Calculator.Kernel=crate::generated::calculator_kernel Leangage.Sql=::leangage::sql --output-file rust/calculator/src/generated/calculator_store.rs --output text
	leanfran-python module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leangage_calculator/kernel.py --output text
	leanfran-go module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-dir go/calculator/kernel --output text
	leanfran-python module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=leangage_calculator.kernel Leangage.Sql=leangage.sql --output-file python/src/leangage_calculator/store.py --output text
	leanfran-go module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=github.com/conao3/lean-leangage/go/calculator/kernel --type-module Leangage.Sql=github.com/conao3/lean-leangage/go/leangage/sql --output-dir go/calculator/store --output text
	leanfran project generate --lake-dir lean --output-dir rust/leangage/src/generated --modules Leangage.Sql Leangage.Token Leangage.Json Leangage.Json.Lexemes Leangage.Http --output text
	leanfran module generate --module-name Leangage.Http --search-path lean/.lake/build/lib/lean --type-path Leangage.Json.Lexemes=crate::generated::leangage_json_lexemes --output-file rust/leangage/src/generated/leangage_http.rs --output text
	leanfran-python module generate --module-name Leangage.Sql --search-path lean/.lake/build/lib/lean --output-file python/src/leangage/sql.py --output text
	leanfran-go module generate --module-name Leangage.Sql --search-path lean/.lake/build/lib/lean --output-dir go/leangage/sql --output text
	leanfran-python module generate --module-name Leangage.Token --search-path lean/.lake/build/lib/lean --output-file python/src/leangage/token_format.py --output text
	leanfran-go module generate --module-name Leangage.Token --search-path lean/.lake/build/lib/lean --output-dir go/leangage/token --output text
	leanfran-python module generate --module-name Leangage.Json --search-path lean/.lake/build/lib/lean --output-file python/src/leangage/json_format.py --output text
	leanfran-go module generate --module-name Leangage.Json --search-path lean/.lake/build/lib/lean --package jsonformat --output-dir go/leangage/jsonformat --output text
	leanfran-python module generate --module-name Leangage.Json.Lexemes --search-path lean/.lake/build/lib/lean --output-file python/src/leangage/json_lexemes.py --output text
	leanfran-go module generate --module-name Leangage.Json.Lexemes --search-path lean/.lake/build/lib/lean --package jsonlexemes --output-dir go/leangage/jsonlexemes --output text
	leanfran-python module generate --module-name Leangage.Http --search-path lean/.lake/build/lib/lean --type-module Leangage.Json.Lexemes=leangage.json_lexemes --output-file python/src/leangage/http_format.py --output text
	leanfran-go module generate --module-name Leangage.Http --search-path lean/.lake/build/lib/lean --type-module Leangage.Json.Lexemes=github.com/conao3/lean-leangage/go/leangage/jsonlexemes --package httpformat --output-dir go/leangage/httpformat --output text
	leanfran module generate --module-name Calculator.Wire --search-path lean/.lake/build/lib/lean --type-path Calculator.Kernel=crate::generated::calculator_kernel Leangage.Http=::leangage::http_format Leangage.Json.Lexemes=::leangage::json_lexemes --output-file rust/calculator/src/generated/calculator_wire.rs --output text
	leanfran-python module generate --module-name Calculator.Wire --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=leangage_calculator.kernel Leangage.Http=leangage.http_format Leangage.Json.Lexemes=leangage.json_lexemes --output-file python/src/leangage_calculator/wire.py --output text
	leanfran-go module generate --module-name Calculator.Wire --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=github.com/conao3/lean-leangage/go/calculator/kernel --type-module Leangage.Http=github.com/conao3/lean-leangage/go/leangage/httpformat --type-module Leangage.Json.Lexemes=github.com/conao3/lean-leangage/go/leangage/jsonlexemes --output-dir go/calculator/wire --output text
	leanfran project generate --lake-dir lean --output-dir rust/notes/src/generated --modules Notes.Kernel --output text
	leanfran-python module generate --module-name Notes.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leangage_notes/kernel.py --output text
	leanfran-go module generate --module-name Notes.Kernel --search-path lean/.lake/build/lib/lean --output-dir go/notes/kernel --output text
	leanfran module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --type-path Notes.Kernel=crate::generated::notes_kernel Leangage.Sql=::leangage::sql --output-file rust/notes/src/generated/notes_store.rs --output text
	leanfran-python module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --type-module Notes.Kernel=leangage_notes.kernel Leangage.Sql=leangage.sql --output-file python/src/leangage_notes/store.py --output text
	leanfran-go module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --output-dir go/notes/store --output text
	leanfran module generate --module-name Notes.Wire --search-path lean/.lake/build/lib/lean --type-path Notes.Kernel=crate::generated::notes_kernel Leangage.Authz=crate::authz Leangage.Http=::leangage::http_format Leangage.Json.Lexemes=::leangage::json_lexemes Leangage.Json=::leangage::json_format --output-file rust/notes/src/generated/notes_wire.rs --output text

.PHONY: generated-check
generated-check: generate
	git diff --exit-code -- $(GENERATED)
	test -z "$$(git ls-files --others --exclude-standard -- $(GENERATED))"

.PHONY: handlers
handlers:
	python3 tools/check-handlers.py

.PHONY: rust
rust: lean
	cd rust && cargo clippy --all-targets -- -D warnings
	cd rust && LEANGAGE_CALCULATOR_ORACLE=$(ORACLE) LEANGAGE_SQL_ORACLE=$(SQL_ORACLE) LEANGAGE_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANGAGE_NOTES_ORACLE=$(NOTES_ORACLE) LEANGAGE_JSON_ORACLE=$(JSON_ORACLE) LEANGAGE_REQUEST_ORACLE=$(REQUEST_ORACLE) LEANGAGE_NOTES_REQUEST_ORACLE=$(NOTES_REQUEST_ORACLE) cargo test

.PHONY: python
python: lean
	cd rust && cargo build --quiet --bin leangage-calculator
	cd python && uv sync --quiet
	cd python && LEANGAGE_RUST_CALCULATOR=$(RUST_CALCULATOR) LEANGAGE_CALCULATOR_ORACLE=$(ORACLE) LEANGAGE_SQL_ORACLE=$(SQL_ORACLE) LEANGAGE_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANGAGE_NOTES_ORACLE=$(NOTES_ORACLE) LEANGAGE_JSON_ORACLE=$(JSON_ORACLE) LEANGAGE_REQUEST_ORACLE=$(REQUEST_ORACLE) uv run pytest -q

.PHONY: go
go: lean
	cd rust && cargo build --quiet --bin leangage-calculator
	cd go && go vet ./...
	cd go && LEANGAGE_CALCULATOR_ORACLE=$(ORACLE) LEANGAGE_SQL_ORACLE=$(SQL_ORACLE) LEANGAGE_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANGAGE_NOTES_ORACLE=$(NOTES_ORACLE) LEANGAGE_JSON_ORACLE=$(JSON_ORACLE) LEANGAGE_REQUEST_ORACLE=$(REQUEST_ORACLE) LEANGAGE_RUST_CALCULATOR=$(RUST_CALCULATOR) go test -race -count=1 ./...

.PHONY: bench
bench:
	cd rust && cargo run --release --quiet --bin bench
	cd python && uv run python -m leangage_calculator.bench
	cd go && go run ./calculator/cmd/bench

.PHONY: bench-bytes
bench-bytes:
	cd rust && cargo run --release --quiet --bin bytes_bench
	cd python && uv run python -m leangage_calculator.bytes_bench
	cd go && go run ./calculator/cmd/bytes-bench
