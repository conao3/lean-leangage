ORACLE := $(CURDIR)/lean/.lake/build/bin/calculator-oracle
SQL_ORACLE := $(CURDIR)/lean/.lake/build/bin/sql-oracle
TOKEN_ORACLE := $(CURDIR)/lean/.lake/build/bin/token-oracle
GENERATED := rust/calculator/src/generated python/src/leanharbor_calculator/kernel.py go/calculator/kernel \
	python/src/leanharbor_calculator/store.py go/calculator/store \
	rust/leanharbor/src/generated python/src/leanharbor/sql.py go/leanharbor/sql \
	python/src/leanharbor/token_format.py go/leanharbor/token

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
	lake -d lean build --wfail Leanharbor Calculator calculator-oracle sql-oracle token-oracle

.PHONY: audit
audit: lean
	lake -d audit build --wfail

.PHONY: generate
generate: lean
	leanfran project generate --lake-dir lean --output-dir rust/calculator/src/generated --modules Calculator.Kernel Calculator.Store --output text
	leanfran-python module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor_calculator/kernel.py --output text
	leanfran-go module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-dir go/calculator/kernel --output text
	leanfran-python module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor_calculator/store.py --output text
	leanfran-go module generate --module-name Calculator.Store --search-path lean/.lake/build/lib/lean --output-dir go/calculator/store --output text
	leanfran project generate --lake-dir lean --output-dir rust/leanharbor/src/generated --modules Leanharbor.Sql Leanharbor.Token --output text
	leanfran-python module generate --module-name Leanharbor.Sql --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor/sql.py --output text
	leanfran-go module generate --module-name Leanharbor.Sql --search-path lean/.lake/build/lib/lean --output-dir go/leanharbor/sql --output text
	leanfran-python module generate --module-name Leanharbor.Token --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor/token_format.py --output text
	leanfran-go module generate --module-name Leanharbor.Token --search-path lean/.lake/build/lib/lean --output-dir go/leanharbor/token --output text

.PHONY: generated-check
generated-check: generate
	git diff --exit-code -- $(GENERATED)
	test -z "$$(git ls-files --others --exclude-standard -- $(GENERATED))"

.PHONY: rust
rust: lean
	cd rust && cargo clippy --all-targets -- -D warnings
	cd rust && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) cargo test

.PHONY: python
python: lean
	cd python && uv sync --quiet
	cd python && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) uv run pytest -q

.PHONY: go
go: lean
	cd go && go vet ./...
	cd go && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) LEANHARBOR_SQL_ORACLE=$(SQL_ORACLE) LEANHARBOR_TOKEN_ORACLE=$(TOKEN_ORACLE) go test -race -count=1 ./...

.PHONY: bench
bench:
	cd rust && cargo run --release --quiet --bin bench
	cd python && uv run python -m leanharbor_calculator.bench
	cd go && go run ./calculator/cmd/bench
