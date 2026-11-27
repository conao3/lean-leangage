ORACLE := $(CURDIR)/samples/lean/.lake/build/bin/calculator-oracle
SQL_ORACLE := $(CURDIR)/langs/lean/.lake/build/bin/sql-oracle
TOKEN_ORACLE := $(CURDIR)/langs/lean/.lake/build/bin/token-oracle
NOTES_ORACLE := $(CURDIR)/samples/lean/.lake/build/bin/notes-oracle
JSON_ORACLE := $(CURDIR)/langs/lean/.lake/build/bin/json-oracle
REQUEST_ORACLE := $(CURDIR)/samples/lean/.lake/build/bin/request-oracle
NOTES_REQUEST_ORACLE := $(CURDIR)/samples/lean/.lake/build/bin/notes-request-oracle
RUST_CALCULATOR := $(CURDIR)/samples/rust/target/debug/leangage-calculator
LEANFRAN ?= leanfran
LIB_PATH := langs/lean/.lake/build/lib/lean
SAMPLES_PATH := samples/lean/.lake/build/lib/lean $(LIB_PATH)
LIB_ORACLES := LEANGAGE_SQL_ORACLE=$(SQL_ORACLE) LEANGAGE_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANGAGE_JSON_ORACLE=$(JSON_ORACLE)
SAMPLES_ORACLES := LEANGAGE_CALCULATOR_ORACLE=$(ORACLE) LEANGAGE_NOTES_ORACLE=$(NOTES_ORACLE) LEANGAGE_REQUEST_ORACLE=$(REQUEST_ORACLE) LEANGAGE_NOTES_REQUEST_ORACLE=$(NOTES_REQUEST_ORACLE)

.PHONY: all
all: check

.PHONY: check
check: format-check audit generated-check handlers test

.PHONY: format
format:
	nix fmt

.PHONY: format-check
format-check:
	nix fmt -- --ci

.PHONY: lean
lean:
	lake -d langs/lean build --wfail Leangage sql-oracle token-oracle json-oracle
	lake -d samples/lean build --wfail Calculator Notes calculator-oracle notes-oracle request-oracle notes-request-oracle

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
	$(LEANFRAN) generate

.PHONY: generated-check
generated-check: generate
	git diff --exit-code -- langs/go/leangage/gen samples/go/calculator/gen samples/go/notes/gen
	test -z "$$(git ls-files --others --exclude-standard -- langs/go/leangage/gen samples/go/calculator/gen samples/go/notes/gen)"

.PHONY: handlers
handlers:
	python3 tools/check-handlers.py

.PHONY: test
test: test-rust test-python test-go

.PHONY: test-rust
test-rust: generate
	cd langs/rust && cargo clippy --all-targets -- -D warnings
	cd langs/rust && $(LIB_ORACLES) cargo test
	cd samples/rust && cargo clippy --all-targets -- -D warnings
	cd samples/rust && $(SAMPLES_ORACLES) cargo test

.PHONY: test-python
test-python: generate
	cd samples/rust && cargo build --quiet --bin leangage-calculator
	cd langs/python && uv sync --quiet
	cd langs/python && $(LIB_ORACLES) uv run pytest -q
	cd samples/python && uv sync --quiet
	cd samples/python && LEANGAGE_RUST_CALCULATOR=$(RUST_CALCULATOR) $(SAMPLES_ORACLES) uv run pytest -q

.PHONY: test-go
test-go: generate
	cd samples/rust && cargo build --quiet --bin leangage-calculator
	cd langs/go && go vet ./...
	cd langs/go && $(LIB_ORACLES) go test -race -count=1 ./...
	cd samples/go && go vet ./...
	cd samples/go && LEANGAGE_RUST_CALCULATOR=$(RUST_CALCULATOR) $(SAMPLES_ORACLES) go test -race -count=1 ./...

.PHONY: bench
bench: generate
	cd samples/rust && cargo run --release --quiet --bin bench
	cd samples/python && uv run python -m leangage_calculator.bench
	cd samples/go && go run ./calculator/cmd/bench

.PHONY: bench-bytes
bench-bytes: generate
	cd samples/rust && cargo run --release --quiet --bin bytes_bench
	cd samples/python && uv run python -m leangage_calculator.bytes_bench
	cd samples/go && go run ./calculator/cmd/bytes-bench
