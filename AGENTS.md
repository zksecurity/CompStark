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

## Performance

- Pushes to `main` pass the performance gate. `scripts/git-hooks/pre-push`, active once per clone with `git config core.hooksPath scripts/git-hooks` (worktrees share it), runs `scripts/perf-gate` on the pushed commit unless the pushed range changes only docs (`*.md`, `docs/`). Push `main` from a worktree whose HEAD is the pushed commit and whose tracked files are unchanged; the hook refuses otherwise.
- `scripts/perf-gate` builds `CompStarkBench` and counts the user-space instructions of single-threaded runs of fixed workloads, phase by phase (`CompStarkBench gate`: `wide 64` over the quartic and quintic extensions, Plonky3's Keccak AIR, a three-table batch, a lookup batch, with the verifier on `wide 64` and Keccak, a Merkle commitment, a coset LDE, scalar Keccak-f/Keccak-256 kernels and independent Keccak batches). It fails if an entry exceeds `bench/perf-baseline.json` by more than its tolerance, or falls below it by more than 2% or its tolerance, whichever is larger. Instruction counts do not depend on the host's load, so the gate runs beside other builds and takes no lock.
- An intended change of the counts, a win or a regression worth its price, is a baseline update in the same push: run `scripts/perf-gate --update` and commit `bench/perf-baseline.json` with the reason in the commit message.
- Every wall-clock benchmark run takes the shared lock, `flock /tmp/compstark-bench.lock <command>`, so that wall-clock runs never overlap. Wall-clock numbers in the README and the docs come from a quiet host under the lock.
- Every night a systemd user timer on the host (`compstark-perf.timer`) runs `scripts/perf-nightly` on main's HEAD in the checkout `~/code/compstark-nightly`: the README's workloads at full size, CompStark and Plonky3, on 16 threads and on one, once the load is below 1.5 and under the lock. It appends the times to `compstark/perf-history.md` in the notes repository (`mitschabaude-bot/notes`) and flags at the top of that file every CompStark time more than 5% above the previous night's; Plonky3's times are recorded as the reference, not flagged.
