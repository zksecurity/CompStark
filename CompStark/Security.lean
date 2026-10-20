/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.Sound.Numbers
public import CompStark.Complete.Quotient

/-! # Concrete security: 100 bits for the Fibonacci STARK and for `wide 64` on `2 ^ 20` rows

Both configurations fold FRI by arity `2` down to a constant, and both pick FRI's radius `δ` and
the extractor's `δ'` below the unique-decoding radius `(1 - rate) / 2`, where the candidate lists
have at most one element (`listSize_le_one`). The terms of `knowledgeError` are bounded in
`CompStark/Sound/Numbers.lean`:

* constraint folding: at most `#constraints - 1`;
* out of domain: `identityDegree + N + n`;
* batching: at `δ' = δ` the powers MCA error (`batchingError_le_mcaError`, `mcaError_powers_le`,
  [BCIKS20] Theorem 1.6), `(numOpened - 1) N`; at `δ < δ'` the curve bound
  `(numOpened - 1) max(T₁, T₂)` with `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ' / (δ' - δ)`,
  independent of `N` (`batchingError_le_curve`);
* FRI: each fold the powers MCA bound on its halving domain, `N / 2 + N / 4 + ⋯ ≤ N` together
  (`friError_le_of_le`), and `(1 - δ) ^ numQueries` for the queries;

all but the queries over `|𝕂| = p ^ 4 ≈ 2 ^ 123.95`.

`fibonacciSetup`: the Fibonacci AIR (2 columns, 5 constraints, 1 quotient chunk) on `2 ^ 10`
rows, blowup `16` (`N = 2 ^ 14`, rate `1/16`) and `123` queries, at `δ = δ' = 7/16`, below the
unique-decoding radius `15/32`. The integers are `4`, `2048 + 2 ^ 14 + 2 ^ 10`, `7 · 2 ^ 14` and
`2 ^ 14`, summing to `150532 ≤ 2 ^ 19`, and `(9/16) ^ 123 ≤ 2 ^ (-102.09)`; the error is at most
`2 ^ (-100)` (`fibonacci_knowledgeError_le`), about `2 ^ (-102.04)` exactly.

`wideSetup`: `wide 64` (64 columns, 64 constraints of degree `3`, 2 quotient chunks, so
`numOpened = 136`) on `2 ^ 20` rows, blowup `4` (`N = 2 ^ 22`, rate `1/4`) and `159` queries, with
FRI at `δ = 9/25` (below `3/8 - 1/N`) and the extractor at `δ' = 37/100` (below `3/8`):

* constraint folding `63`, about `2 ^ (-117.98)`;
* out of domain `(3 · 2 ^ 20 + 1) + 2 ^ 22 + 2 ^ 20`, about `2 ^ (-100.95)`;
* batching `135 · max(325/9, 37) = 4995`, about `2 ^ (-111.67)`;
* FRI's folds `2 ^ 22`, about `2 ^ (-101.95)`, and queries `(16/25) ^ 159`, about `2 ^ (-102.37)`.

The total is at most `2 ^ (-100)` (`wide_knowledgeError_le`), about `2 ^ (-100.05)` exactly. The
out-of-domain term is why `δ'` stays below the unique-decoding radius: from two candidates on,
`ℓ² · identityDegree` alone exceeds `2 ^ (-100)` at this size.

By `knowledgeSoundness`, a prover that the verifier accepts with probability above `2 ^ (-100)`
has committed to a trace within `δ'` of one that satisfies the AIR (`fibonacci_knowledgeSoundness`,
`wide_knowledgeSoundness`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

local notation "F" => KoalaBear.Fast.Field

/-- FRI with blowup `16`, folding by arity `2` down to a constant, and `123` queries. -/
def fibonacciParams : Fri.Params where
  logBlowup := 4
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 123
  commitPowBits := 0
  queryPowBits := 0

/-- The Fibonacci AIR on `2 ^ 10` rows with `fibonacciParams`. -/
def fibonacciSetup : Setup where
  params := fibonacciParams
  air := fibonacci
  logN := 10
  valid :=
    { colsInWidth := by unfold Air.ColsInWidth; decide
      degreeFits := fibonacci_degreeFits 10
      twoAdic := by decide
      chunksFit := by
        rw [logQuotientChunks_of _ 0 (by decide)]
        exact Nat.zero_le _
      folds := by decide
      finalPolyFits := by decide
      queries := by decide }
  blowup := by decide
  folds := by decide

/-- **100 bits.** The knowledge error of `fibonacciSetup` at `δ = δ' = 7/16` is at most
`2 ^ (-100)`. -/
theorem fibonacci_knowledgeError_le :
    knowledgeError fibonacciSetup (7 / 16) (7 / 16) ≤ (2 ^ 100)⁻¹ := by
  have ha : fibonacciSetup.params.maxLogArity = 1 := rfl
  have hrate : fibonacciSetup.rate = 1 / 2 ^ 4 := rate_eq _
  have h1 := knowledgeError_le_of_le fibonacciSetup ha (7 / 16) (by rw [hrate]; norm_num)
  have hq : fibonacciSetup.params.numQueries = 123 := rfl
  rw [hq] at h1
  refine h1.trans (numbers_le _ ?_)
  have hid : fibonacciSetup.identityDegree = 2048 := by
    simp only [Setup.identityDegree, Setup.n, Setup.chunks, fibonacciSetup]
    rw [logQuotientChunks_of _ 0 (by decide)]
    simp only [fibonacci, List.foldl, Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
    norm_num
  have hc : fibonacciSetup.chunks = 1 := by
    change 2 ^ fibonacci.logQuotientChunks = 1
    rw [logQuotientChunks_of _ 0 (by decide)]
    rfl
  simp only [Setup.numOpened, hid, hc, Setup.size, Setup.n]
  change (5 - 1) + (2048 + 2 ^ (10 + 4) + 2 ^ 10) + (2 * 2 + 4 * 1 - 1) * 2 ^ (10 + 4) +
    2 ^ (10 + 4) ≤ 2 ^ 19
  norm_num

/-- Knowledge soundness of `fibonacciSetup` with error `2 ^ (-100)`, FRI and the extractor both at
`7/16`: if no trace within `7/16` of the prover's committed trace satisfies the AIR, the verifier
accepts with probability at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeSoundness (publicValues : List F) (prover : Prover fibonacciSetup) :
    (∀ trace ∈ closeTraces fibonacciSetup (7 / 16 : NNReal) prover,
      ¬ fibonacci.Satisfied 10 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ := by
  intro h
  refine (knowledgeSoundness fibonacciSetup publicValues prover (7 / 16) (7 / 16) ?_
    h).trans
    fibonacci_knowledgeError_le
  rw [rate_eq]
  norm_num [fibonacciSetup, fibonacciParams]

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `159` queries. -/
def wideParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 159
  commitPowBits := 0
  queryPowBits := 0

/-- The wide AIR reads only its columns. -/
theorem wide_colsInWidth (w : Nat) : (wide w).ColsInWidth := by
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.colsBelow, Bool.true_and,
    Bool.and_self, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hj, Nat.mod_lt _ (by omega)⟩, hj⟩

/-- `wide 64` on `2 ^ 20` rows with `wideParams`. -/
def wideSetup : Setup where
  params := wideParams
  air := wide 64
  logN := 20
  valid :=
    { colsInWidth := wide_colsInWidth 64
      degreeFits := wide_degreeFits 64 20
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide }
  blowup := by decide
  folds := by decide

/-- The largest of values at most `b` is at most `b`. -/
theorem foldl_max_le {α : Type} (f : α → Nat) (b : Nat) :
    ∀ (l : List α) (a : Nat), a ≤ b → (∀ x ∈ l, f x ≤ b) → l.foldl (fun m x ↦ max m (f x)) a ≤ b
  | [], _, ha, _ => ha
  | x :: l, _, ha, h => foldl_max_le f b l _ (max_le ha (h x List.mem_cons_self))
      fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- **100 bits on `2 ^ 20` rows.** The knowledge error of `wideSetup`, FRI at `δ = 9/25` and the
extractor at `δ' = 37/100`, is at most `2 ^ (-100)`. -/
theorem wide_knowledgeError_le :
    knowledgeError wideSetup (9 / 25) (37 / 100) ≤ (2 ^ 100)⁻¹ := by
  have ha : wideSetup.params.maxLogArity = 1 := rfl
  have hrate : wideSetup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wideSetup.size : ℝ) = 2 ^ 22 := by norm_num [Setup.size, wideSetup, wideParams]
  have h1 := knowledgeError_le_curve wideSetup ha (9 / 25) (37 / 100)
    (by rw [hrate, hsize]; norm_num) (by norm_num) (by norm_num) (by rw [hrate]; norm_num)
  have hq : wideSetup.params.numQueries = 159 := rfl
  have hl : wideSetup.logN = 20 := rfl
  have hb : wideSetup.params.logBlowup = 2 := rfl
  rw [hq] at h1
  refine h1.trans (numbers_wide_le _ ?_ _ ?_)
  · have hc : wideSetup.chunks = 2 := by
      change 2 ^ (wide 64).logQuotientChunks = 2
      rw [wide_logQuotientChunks 64 (by decide)]
      rfl
    have hid : wideSetup.identityDegree ≤ 3 * 2 ^ 20 + 1 := by
      simp only [Setup.identityDegree, Setup.n, hc, hl]
      refine max_le (foldl_max_le _ _ _ _ (Nat.zero_le _) fun c hc ↦ ?_) (by norm_num)
      simp only [wideSetup, wide, List.mem_map, List.mem_range] at hc
      obtain ⟨j, -, rfl⟩ := hc
      simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
      norm_num
    have hw : wideSetup.air.constraints.length = 64 := by
      simp only [wideSetup, wide, List.length_map, List.length_range]
    simp only [hw, Setup.size, Setup.n, hl, hb]
    norm_num at hid ⊢
    generalize wideSetup.identityDegree = x at hid ⊢
    omega
  · have hc : wideSetup.chunks = 2 := by
      change 2 ^ (wide 64).logQuotientChunks = 2
      rw [wide_logQuotientChunks 64 (by decide)]
      rfl
    have ho : wideSetup.numOpened - 1 = 135 := by
      simp only [Setup.numOpened, hc]
      rfl
    rw [ho, hrate]
    norm_num

/-- Knowledge soundness of `wideSetup` with error `2 ^ (-100)`, FRI at `9/25` and the extractor
at `37/100`: if no trace within `37/100` of the prover's committed trace satisfies the AIR, the
verifier accepts with probability at most `2 ^ (-100)`. -/
theorem wide_knowledgeSoundness (publicValues : List F) (prover : Prover wideSetup) :
    (∀ trace ∈ closeTraces wideSetup (37 / 100 : NNReal) prover,
      ¬ (wide 64).Satisfied 20 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ := by
  intro h
  refine (knowledgeSoundness wideSetup publicValues prover (9 / 25) (37 / 100) ?_ h).trans
    wide_knowledgeError_le
  rw [rate_eq]
  norm_num [wideSetup, wideParams]

end CompStark.Iop
