ORACLE := $(CURDIR)/lean/.lake/build/bin/calculator-oracle
SQL_ORACLE := $(CURDIR)/lean/.lake/build/bin/sql-oracle
TOKEN_ORACLE := $(CURDIR)/lean/.lake/build/bin/token-oracle
NOTES_ORACLE := $(CURDIR)/lean/.lake/build/bin/notes-oracle
JSON_ORACLE := $(CURDIR)/lean/.lake/build/bin/json-oracle
RUST_CALCULATOR := $(CURDIR)/rust/target/debug/leanharbor-calculator
GENERATED := rust/calculator/src/generated python/src/leanharbor_calculator/kernel.py go/calculator/kernel \
	python/src/leanharbor_calculator/store.py go/calculator/store \
	rust/leanharbor/src/generated python/src/leanharbor/sql.py go/leanharbor/sql \
	python/src/leanharbor/token_format.py go/leanharbor/token \
	python/src/leanharbor/json_format.py go/leanharbor/jsonformat \
	rust/notes/src/generated python/src/leanharbor_notes/kernel.py go/notes/kernel \
	python/src/leanharbor_notes/store.py go/notes/store

.PHONY: all
all: check

.PHONY: check
check: format-check lean audit generated-check rust python go

.PHONY: format
format:
	nix fmt

.PHONY: format-check
format-check:
	nix fmt -- --ci

.PHONY: lean
lean:
	lake -d lean build --wfail Leanharbor Calculator Notes calculator-oracle sql-oracle token-oracle notes-oracle json-oracle

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
	leanfran module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-path Calculator.Kernel=crate::generated::calculator_kernel Leanharbor.Sql=::leanharbor::sql --output-file rust/calculator/src/generated/calculator_store.rs --output text
	leanfran-python module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor_calculator/kernel.py --output text
	leanfran-go module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-dir go/calculator/kernel --output text
	leanfran-python module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=leanharbor_calculator.kernel Leanharbor.Sql=leanharbor.sql --output-file python/src/leanharbor_calculator/store.py --output text
	leanfran-go module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --type-module Calculator.Kernel=github.com/conao3/lean-leanharbor/go/calculator/kernel --type-module Leanharbor.Sql=github.com/conao3/lean-leanharbor/go/leanharbor/sql --output-dir go/calculator/store --output text
	leanfran project generate --lake-dir lean --output-dir rust/leanharbor/src/generated --modules Leanharbor.Sql Leanharbor.Token Leanharbor.Json --output text
	leanfran-python module generate --module-name Leanharbor.Sql --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor/sql.py --output text
	leanfran-go module generate --module-name Leanharbor.Sql --search-path lean/.lake/build/lib/lean --output-dir go/leanharbor/sql --output text
	leanfran-python module generate --module-name Leanharbor.Token --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor/token_format.py --output text
	leanfran-go module generate --module-name Leanharbor.Token --search-path lean/.lake/build/lib/lean --output-dir go/leanharbor/token --output text
	leanfran-python module generate --module-name Leanharbor.Json --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor/json_format.py --output text
	leanfran-go module generate --module-name Leanharbor.Json --search-path lean/.lake/build/lib/lean --package jsonformat --output-dir go/leanharbor/jsonformat --output text
	leanfran project generate --lake-dir lean --output-dir rust/notes/src/generated --modules Notes.Kernel --output text
	leanfran-python module generate --module-name Notes.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor_notes/kernel.py --output text
	leanfran-go module generate --module-name Notes.Kernel --search-path lean/.lake/build/lib/lean --output-dir go/notes/kernel --output text
	leanfran module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --type-path Notes.Kernel=crate::generated::notes_kernel Leanharbor.Sql=::leanharbor::sql --output-file rust/notes/src/generated/notes_store.rs --output text
	leanfran-python module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --type-module Notes.Kernel=leanharbor_notes.kernel Leanharbor.Sql=leanharbor.sql --output-file python/src/leanharbor_notes/store.py --output text
	leanfran-go module generate --module-name Notes.Store --search-path lean/.lake/build/lib/lean --output-dir go/notes/store --output text

.PHONY: generated-check
generated-check: generate
	git diff --exit-code -- $(GENERATED)
	test -z "$$(git ls-files --others --exclude-standard -- $(GENERATED))"

.PHONY: rust
rust: lean
	cd rust && cargo clippy --all-targets -- -D warnings
	cd rust && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANHARBOR_NOTES_ORACLE=$(NOTES_ORACLE) LEANHARBOR_JSON_ORACLE=$(JSON_ORACLE) cargo test

.PHONY: python
python: lean
	cd rust && cargo build --quiet --bin leanharbor-calculator
	cd python && uv sync --quiet
	cd python && LEANHARBOR_RUST_CALCULATOR=$(RUST_CALCULATOR) LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANHARBOR_NOTES_ORACLE=$(NOTES_ORACLE) LEANHARBOR_JSON_ORACLE=$(JSON_ORACLE) uv run pytest -q

.PHONY: go
go: lean
	cd rust && cargo build --quiet --bin leanharbor-calculator
	cd go && go vet ./...
	cd go && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) LEANHARBOR_NOTES_ORACLE=$(NOTES_ORACLE) LEANHARBOR_JSON_ORACLE=$(JSON_ORACLE) LEANHARBOR_RUST_CALCULATOR=$(RUST_CALCULATOR) go test -race -count=1 ./...

.PHONY: bench
bench:
	cd rust && cargo run --release --quiet --bin bench
	cd python && uv run python -m leanharbor_calculator.bench
	cd go && go run ./calculator/cmd/bench
