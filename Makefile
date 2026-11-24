ORACLE := $(CURDIR)/lean/.lake/build/bin/calculator-oracle
GENERATED := rust/calculator/src/generated python/src/leanharbor_calculator/kernel.py

.PHONY: all
all: check

.PHONY: check
check: format-check lean audit generated-check rust python

.PHONY: format
format:
	nix fmt

.PHONY: format-check
format-check:
	nix fmt -- --ci

.PHONY: lean
lean:
	lake -d lean build --wfail Leanharbor Calculator calculator-oracle

.PHONY: audit
audit: lean
	lake -d audit build --wfail

.PHONY: generate
generate: lean
	leanfran project generate --lake-dir lean --output-dir rust/calculator/src/generated --modules Calculator.Kernel --output text
	leanfran-python module generate --module-name Calculator.Kernel --search-path lean/.lake/build/lib/lean --output-file python/src/leanharbor_calculator/kernel.py --output text

.PHONY: generated-check
generated-check: generate
	git diff --exit-code -- $(GENERATED)
	test -z "$$(git ls-files --others --exclude-standard -- $(GENERATED))"

.PHONY: rust
rust: lean
	cd rust && cargo clippy --all-targets -- -D warnings
	cd rust && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) cargo test

.PHONY: python
python: lean
	cd python && uv sync --quiet
	cd python && LEANHARBOR_CALCULATOR_ORACLE=$(ORACLE) uv run pytest -q

.PHONY: bench
bench:
	cd rust && cargo run --release --quiet --bin bench
	cd python && uv run python -m leanharbor_calculator.bench
