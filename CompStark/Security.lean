/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.Sound.Numbers
public import CompStark.Complete.Quotient

/-! # Concrete security: 100 bits for the Fibonacci STARK

`fibonacciSetup`: the Fibonacci AIR (2 columns, 5 constraints, 1 quotient chunk) on `2 ^ 10`
rows, blowup `16` (`N = 2 ^ 14`, rate `1/16`), FRI folding by arity `2` down to a constant, and
`123` queries. With FRI and the extractor both at proximity `δ = δ' = 7/16`, below the
unique-decoding radius `15/32`, its knowledge error is at most `2 ^ (-100)`
(`fibonacci_knowledgeError_le`). So, by `knowledgeSoundness`, a prover that the verifier accepts with probability above `2 ^ (-100)` has committed to a trace
within `7/16` of one that satisfies the AIR (`fibonacci_knowledgeSoundness`).

The terms of `knowledgeError` (`CompStark/Sound/Numbers.lean`), over `|𝕂| = p ^ 4 ≥ 2 ^ 123`:

* constraint folding: lists of at most one candidate below the unique-decoding radius, so at most
  `#constraints - 1 = 4`;
* out of domain: `identityDegree + N + n = 2048 + 2 ^ 14 + 2 ^ 10`;
* batching: at a single radius at most the powers MCA error (`batchingError_le_mcaError`), bounded
  below the unique-decoding radius (`mcaError_powers_le`, [BCIKS20] Theorem 1.6) by
  `(numOpened - 1) N = 7 · 2 ^ 14`;
* FRI: `10` folds by affine lines, each at most `2 ^ 14` by the same bound, and
  `(9/16) ^ 123 ≤ 2 ^ (-102.09)` for the queries.

The four integers sum to `297988 ≤ 2 ^ 19`, so the error is at most
`2 ^ (19 - 123) + (9/16) ^ 123 ≤ 2 ^ (-101) + 2 ^ (-101)`; the exact value is about
`2 ^ (-101.99)`.

The same bound (`knowledgeError_le_of_le`) holds for any AIR at arity `2`, blowup at least `16`
and `δ ≤ 7/16`. The batching term `(numOpened - 1) N / |𝕂|` limits the domain size: for
`wide 64` (`64` columns, `64` constraints of degree `3`, `2` chunks, so `numOpened = 136`) at
blowup `16` and `123` queries the error is about `2 ^ (-101.4)` for `logN = 10`,
`2 ^ (-100.9)` for `logN = 11`, `2 ^ (-100.3)` for `logN = 12`, and below 100 bits from
`logN = 13` on. Larger traces need bounds beyond the unique-decoding radius.
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
  have hb : 4 ≤ fibonacciSetup.params.logBlowup := le_rfl
  have ha : fibonacciSetup.params.maxLogArity = 1 := rfl
  have h1 := knowledgeError_le_of_le fibonacciSetup hb ha (7 / 16) le_rfl
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
    (10 - 0) * 2 ^ (10 + 4) ≤ 2 ^ 19
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
  have hrate : fibonacciSetup.rate = 1 / 16 := by
    rw [Setup.rate]
    norm_num [fibonacciSetup, fibonacciParams]
  rw [hrate]
  norm_num

end CompStark.Iop
