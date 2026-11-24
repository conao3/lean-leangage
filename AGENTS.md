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

## Lean and the host languages

- Lean owns the kernel: types, `transition`, `apply`, and every decision about a command.
  Definitions that are generated go in a module without proofs (`Calculator.Kernel`); theorems
  and specifications go in a module beside it (`Calculator.Proofs`).
- The shells own input and output: HTTP, tokens, JSON, the engine. They call generated
  functions and make no decision about a command themselves.
- The contract uses `Except` for refusals. The Python backend of leanfran 0.7.0 cannot return
  `Except` from a public function, so the calculator also exports `step`, the same function with
  the inductive type `Outcome`.
- Generated files (`rust/calculator/src/generated/`, `python/src/leanharbor_calculator/kernel.py`)
  are committed and never edited. Run `make generate` after changing `lean/`.
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
  `uv run pytest`.
- `make generate`, `make format`, `make bench`.
- The differential tests read the oracle's path from `LEANHARBOR_CALCULATOR_ORACLE`; the
  Makefile sets it.
- The servers read `LEANHARBOR_SECRET` and `LEANHARBOR_LISTEN`; `LEANHARBOR_ISSUE=<org>:<user>`
  prints a one-day token and exits.

## Conventions

- Commit messages, comments and documents are in English.
- The leanfran compilers come from the flake input pinned to a release commit; the crate and
  the PyPI package are pinned to the same version (`=0.7.0`, `==0.7.0`).
