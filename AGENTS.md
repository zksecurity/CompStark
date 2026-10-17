# CompStark agent guide

Fast, proved STARK components in Lean 4 on top of CompPoly. Start with `README.md`.

- `lake build` and `lake test` validate the library; `tests/` holds `#guard` known-answer tests under `CompStarkTests`.
- `CompStark.lean` imports every module; keep it in sync when adding files.
- Proofs must be kernel-checked: no `native_decide`, no `sorry` in commits, no `implemented_by` or externs.
- Every fast implementation needs a theorem equating it with its specification, and a benchmark against the Plonky3 component it replaces (`bench/rust`, pinned Plonky3 0.4.2).
- Prefer `simp only [...]` over bare `simp`; import specific Mathlib modules, not `Mathlib.Tactic`.
- CompPoly is pinned by commit in `lakefile.lean`; bump it deliberately.
