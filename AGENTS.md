# AGENTS.md

leanharbor: the contract of a kernel proved in Lean 4, and the shells that run the code
[leanfran](https://github.com/conao3/lean-leanfran) generates from it.

## Layout

- `lean/`: Lake package `leanharbor`, Lean 4.35.0, core only (no Mathlib). `Leanharbor/` is the
  contract, `Calculator/Kernel.lean` holds what is generated, `Calculator/Proofs.lean` the
  specifications and theorems, `CalculatorOracle.lean` the native program the differential
  tests compare against.
- `audit/`: a separate Lake package with leanassay (`Audit/Calculator.lean`) and the axiom check
  (`Audit/Axioms.lean`).
- `rust/`: Cargo workspace, edition 2024. `leanharbor` is the shell, `calculator` the example.
- `python/`: uv project. `leanharbor` is the shell, `leanharbor_calculator` the example.
- `go/`: Go module `github.com/conao3/lean-leanharbor/go`. `leanharbor` is the shell,
  `calculator` the example, with the server and the benchmark under `calculator/cmd/`.

## Lean and the host languages

- Lean owns the kernel: types, `transition`, `apply`, and every decision about a command.
  Definitions that are generated go in a module without proofs (`Calculator.Kernel`); theorems
  and specifications go in a module beside it (`Calculator.Proofs`).
- The shells own input and output: HTTP, tokens, JSON, the engine. They call generated
  functions and make no decision about a command themselves.
- The contract uses `Except` for refusals. The engines keep each tenant's snapshot as a Lean
  value with one owner (`leanfran::Owned` in Rust, lent as a `Local` by `Kernel::lend`;
  `leanfran.Local` in Python; `leanfran.Value` in Go) and call the generated functions that take
  one (`kernel::local::apply` in Rust, `kernel.apply.local` in Python, `kernel.ApplyValue` in Go).
  `apply` must receive the only reference to the snapshot (a move in Rust, `take()` in Python,
  `Take()` in Go), and no `Local` may leave the closure of `lend`, or Lean copies instead of
  updating in place. `rust/calculator/tests/in_place.rs` and `go/calculator/in_place_test.go`
  check it.
- Generated files (`rust/calculator/src/generated/`, `python/src/leanharbor_calculator/kernel.py`,
  `go/calculator/kernel/`) are committed and never edited. Run `make generate` after changing
  `lean/`.
- When a function is added to a generated module, add a theorem about it and list it in
  `audit/Audit/Calculator.lean` in the same change. Theorems whose hypothesis fixes the result
  of the function (`transition a s c = .ok …`) cannot be run by leanassay; state the runnable
  form with `match` (`get_after_run`) and derive the other from it.
- The README states what is proved, what is checked and what is trusted. Keep its numbers equal
  to what `make check` and `make bench` print.

## Commands

All commands run inside `nix develop`.

- `make check`: `nix fmt -- --ci`, `lake -d lean build --wfail`, `lake -d audit build --wfail`,
  regeneration with `git diff --exit-code`, `cargo clippy -- -D warnings`, `cargo test`,
  `uv run pytest`, `go vet`, `go test -race`.
- `make generate`, `make format`, `make bench`.
- The README's Speed section shows rates (higher is better) with a chart for each table. After a
  measurement, put the runs in `docs/speed.json`, run `python3 tools/speed-charts.py`, and paste
  the tables it prints into the README.
- The differential tests read the oracle's path from `LEANHARBOR_CALCULATOR_ORACLE`; the
  Makefile sets it.
- The servers read `LEANHARBOR_SECRET` and `LEANHARBOR_LISTEN`; `LEANHARBOR_ISSUE=<org>:<user>`
  prints a one-day token and exits.

## Conventions

- Commit messages, comments and documents are in English.
- The leanfran compilers come from the flake input pinned to a release commit; the crate, the
  PyPI package and the Go module are pinned to the same version (`=0.10.0`, `==0.10.0`,
  `v0.10.0`).
