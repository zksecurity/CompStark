# CompStark agent guide

Fast, proved STARK components in Lean 4 on top of CompPoly. Start with `README.md`.

The goal is state-of-the-art prover and verifier performance and security analysis for every configuration people use, never one showcase or one field: read [VISION.md](VISION.md), whose north star decides what counts as progress here.

- `lake build` and `lake test` validate the library; `tests/` holds `#guard` known-answer tests under `CompStarkTests`.
- `CompStark.lean` imports every module; keep it in sync when adding files.
- Proofs must be kernel-checked: no `native_decide`, no `sorry` in commits, no `implemented_by` or externs.
- Every fast implementation needs a theorem equating it with its specification, and a benchmark against the Plonky3 component it replaces (`bench/rust`, pinned to Plonky3 revision `a4982ec`).
- Prefer `simp only [...]` over bare `simp`; import specific Mathlib modules, not `Mathlib.Tactic`.
- CompPoly is pinned by commit in `lakefile.lean`; bump it deliberately.
- Some proofs can exhaust memory if the kernel unfolds the concrete verifier: run Lean under a memory cap (`systemd-run --user --scope -p MemoryMax=12G -p MemorySwapMax=0 -- lake build`), and when it hits the cap, fix the proof (generic bind lemmas, no `rfl`/`decide` on the instantiated verifier) instead of retrying.
