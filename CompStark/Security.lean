/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.Sound.Numbers
public import CompStark.Sound.NumbersNi
public import CompStark.Complete.Quotient

/-! # Concrete security: 100 bits for the Fibonacci STARK and for `wide 64`

All configurations fold FRI by arity `2` down to a constant, and pick FRI's radius `δ` and the
extractor's `δ'` below the unique-decoding radius `(1 - rate) / 2`, where the candidate lists have
at most one element (`listSize_le_one`). The terms of `knowledgeError` are bounded in
`CompStark/Sound/Numbers.lean`:

* constraint folding: at most `#constraints - 1`;
* out of domain: `identityDegree + n`;
* batching, at `δ'' = δ' - 2/N`: for `δ ≤ δ''` the powers MCA error at `δ`
  (`batchingError_le_mcaError`, `mcaError_powers_le`, [BCIKS20] Theorem 1.6),
  `(numOpened - 1) N`; for `δ < δ''` the curve bound `(numOpened - 1) max(T₁, T₂)` with
  `T₁ = (1 - ρ - δ) / (δ (1 - ρ - 2δ))`, `T₂ = δ'' / (δ'' - δ)`, independent of `N`
  (`batchingError_le_curve`);
* FRI at a proximity loss `loss` (`friError_le_lossy`), for `δ ≤ (1 - ρ) / 2 - 2 ^ (-t)`: each
  fold onto a domain of at least `2 ^ t` points the lossy MCA bound `max(T₁, δ_int / loss)` with
  `δ_int = δ + loss`, independent of the domain; the smaller folds the powers MCA bound on their
  halving domains, `2 ^ t` together; and `(1 - δ + #folds · loss) ^ numQueries` for the queries;

all but the queries over `|𝕂| = p ^ 4 ≈ 2 ^ 123.95`.

`fibonacciSetup`: the Fibonacci AIR (2 columns, 5 constraints, 1 quotient chunk) on `2 ^ 10`
rows, blowup `16` (`N = 2 ^ 14`, rate `1/16`) and `110` queries, with FRI at
`δ = 15/32 - 2 ^ (-12)` and the extractor at `δ' = 15/32 - 2 ^ (-14) ≥ δ + 2/N`, below the
unique-decoding radius `15/32`. At this size the MCA bound is the better one for batching and for
every fold (`t = 14`, `loss = 2 ^ (-20)`). The integers are `4`, `2048 + 2 ^ 10`, `7 · 2 ^ 14` and
`2 ^ 14`, summing to `134148`, about `2 ^ (-106.92)`, and the queries
`(17/32 + 2 ^ (-12) + 10 · 2 ^ (-20)) ^ 110` are about `2 ^ (-100.30)`; the error is at most
`2 ^ (-100)` (`fibonacci_knowledgeError_le`), about `2 ^ (-100.29)` exactly; `109` queries do not
reach `2 ^ (-100)` with these bounds.

`wideSetup`: `wide 64` (64 columns, 64 constraints of degree `3`, 2 quotient chunks, so
`numOpened = 136`) on `2 ^ 20` rows, blowup `4` (`N = 2 ^ 22`, rate `1/4`) and `149` queries, with
FRI at `δ = 3/8 - 2 ^ (-12)`, the extractor at `δ' = 3/8 - 2 ^ (-16)`, `loss = 2 ^ (-17)` and
`t = 16`:

* constraint folding `63`, about `2 ^ (-117.98)`;
* out of domain `(3 · 2 ^ 20 + 1) + 2 ^ 20`, about `2 ^ (-101.95)`;
* batching `135 · max(T₁, T₂) ≤ 276841`, `T₁ = 1537 · 2048 / 1535 ≈ 2050.67`, `T₂ ≈ 1641.75`,
  about `2 ^ (-105.88)`;
* FRI's folds: the `6` onto at least `2 ^ 16` points `δ · 2 ^ 17 + 1 = 49121` each, the `14`
  smaller ones `2 ^ 16`, about `2 ^ (-105.50)`;
* FRI's queries `(5/8 + 2 ^ (-12) + 20 · 2 ^ (-17)) ^ 149`, about `2 ^ (-100.90)`.

The total is at most `2 ^ (-100)` (`wide_knowledgeError_le`), about `2 ^ (-100.26)` exactly. With
these bounds, numerically, no choice of the radii, the loss and `t` reaches `2 ^ (-100)` at `148`
queries: the out-of-domain term alone is about a quarter. It is also why `δ'` stays below the
unique-decoding radius: from two candidates on, `ℓ² · identityDegree` alone exceeds `2 ^ (-100)`
at this size.

`wide21Setup`: `wide 64` on `2 ^ 21` rows, blowup `4` (`N = 2 ^ 23`) and `150` queries, at the same
radii, loss and `t`: constraint folding as above, out of domain `(3 · 2 ^ 21 + 1) + 2 ^ 21`, about
`2 ^ (-100.95)`, batching as above (`T₂ ≈ 1640.04`), FRI's `7` large folds and `2 ^ 16`, about
`2 ^ (-105.31)`, and the queries `(5/8 + 2 ^ (-12) + 21 · 2 ^ (-17)) ^ 150`, about
`2 ^ (-101.57)`. The total is at most `2 ^ (-100)` (`wide21_knowledgeError_le`), about
`2 ^ (-100.16)` exactly; `149` queries do not reach it with these bounds.

By `knowledgeSoundness`, a prover that the verifier accepts with probability above `2 ^ (-100)`
has committed to a trace within `δ'` of one that satisfies the AIR (`fibonacci_knowledgeSoundness`,
`wide_knowledgeSoundness`, `wide21_knowledgeSoundness`).

`wideSp1Setup`: `wide 64` on `2 ^ 21` rows with SP1's FRI (soundcalc's core circuit, `sp1Params`):
blowup `4` (`N = 2 ^ 23`), `21` folds of arity `2` down to a constant, `124` queries and `16` bits
of query grinding. In the random-oracle model each round is one oracle answer, so the bound is on
the largest round error (`roundError`, `CompStark/NonInteractiveError.lean`, terms bounded in
`CompStark/Sound/NumbersNi.lean`), with FRI at `δ = 3/8 - 2 ^ (-16)`, the extractor at
`δ' = 3/8 - 2 ^ (-18)`, `loss = 2 ^ (-22)`, `δ_int = δ + loss` and `t = 16`:

* constraint folding `63`, about `2 ^ (-117.98)`;
* out of domain `(3 · 2 ^ 21 + 1) + 2 ^ 21`, about `2 ^ (-100.95)`;
* batching `135 · max(T₁, T₂)`, `T₁ ≈ 32770.67`, `T₂ ≈ 33464.83`, about `2 ^ (-101.85)`;
* FRI's folds: `max(T₁, δ_int / loss, 2 ^ t) ≈ 1572801` (`δ_int / loss`), about `2 ^ (-103.37)`;
* FRI's queries `powFraction 16 · (5/8 + 2 ^ (-16) + 21 · 2 ^ (-22) + 1/p) ^ 124`, with
  `powFraction 16 = 32513 / p ≈ 2 ^ (-15.99996)`, about `2 ^ (-100.075)`.

Every round error is at most `2 ^ (-100)` (`wideSp1_roundError_le`). `123` queries do not reach it
at any radius: `(5/8) ^ 123 · 2 ^ (-16)` alone is about `2 ^ (-99.40)`.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

local notation "F" => KoalaBear.Fast.Field

/-- FRI with blowup `16`, folding by arity `2` down to a constant, and `110` queries. -/
def fibonacciParams : Fri.Params where
  logBlowup := 4
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 110
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

/-- **100 bits.** The knowledge error of `fibonacciSetup`, FRI at
`δ = 1919/4096 = 15/32 - 2 ^ (-12)` and the extractor at `δ' = 7679/16384 = 15/32 - 2 ^ (-14)`, is
at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeError_le :
    knowledgeError fibonacciSetup (1919 / 4096) (7679 / 16384) ≤ (2 ^ 100)⁻¹ := by
  have ha : fibonacciSetup.params.maxLogArity = 1 := rfl
  have hrate : fibonacciSetup.rate = 1 / 2 ^ 4 := rate_eq _
  have hsize : (fibonacciSetup.size : ℝ) = 2 ^ 14 := by
    norm_num [Setup.size, fibonacciSetup, fibonacciParams]
  have h1 := knowledgeError_le_of_le fibonacciSetup (1919 / 4096) (7679 / 16384)
    (by rw [hsize]; norm_num) (by rw [hrate]; norm_num)
  have h2 := friError_le_lossy fibonacciSetup ha 14 (1919 / 4096) (1919 / 4096 + 1 / 2 ^ 20)
    (1 / 2 ^ 20) (by rw [hrate]; norm_num) (by norm_num) (lt_add_of_pos_right _ (by positivity))
    (by positivity)
  have hq : fibonacciSetup.params.numQueries = 110 := rfl
  have hlarge : fibonacciSetup.logN + fibonacciSetup.params.logBlowup - 14 = 0 := rfl
  have hfolds : fibonacciSetup.logN - fibonacciSetup.params.logFinalPolyLen = 10 := rfl
  rw [hq, hlarge, hfolds] at h2
  refine h1.trans ((add_le_add le_rfl h2).trans
    (numbers_le _ (2 ^ 17) _ _ _ _ 0 _ (2177 / 4096 + 10 / 2 ^ 20) ?_ ?_ le_rfl ?_ le_rfl
      (by norm_num) (by norm_num)))
  · have hid : fibonacciSetup.identityDegree = 2048 := by
      simp only [Setup.identityDegree, Setup.n, Setup.chunks, fibonacciSetup]
      rw [logQuotientChunks_of _ 0 (by decide)]
      simp only [fibonacci, List.foldl, Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
      norm_num
    have hc : fibonacciSetup.chunks = 1 := by
      change 2 ^ fibonacci.logQuotientChunks = 1
      rw [logQuotientChunks_of _ 0 (by decide)]
      rfl
    simp only [Setup.numOpened, hid, hc, Setup.size, Setup.n]
    change (5 - 1) + (2048 + 2 ^ 10) + (2 * 2 + 4 * 1 - 1) * 2 ^ (10 + 4) ≤ 2 ^ 17
    norm_num
  · rw [Nat.cast_zero, zero_mul]
  · norm_num

/-- Knowledge soundness of `fibonacciSetup` with error `2 ^ (-100)`, FRI at `1919/4096` and the
extractor at `7679/16384`: if no trace within `7679/16384` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeSoundness (publicValues : List F) (prover : Prover fibonacciSetup) :
    (∀ trace ∈ closeTraces fibonacciSetup (7679 / 16384 : NNReal) prover.trace,
      ¬ fibonacci.Satisfied 10 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ := by
  intro h
  refine (knowledgeSoundness fibonacciSetup publicValues prover (1919 / 4096) (7679 / 16384) ?_
    h).trans fibonacci_knowledgeError_le
  rw [rate_eq]
  norm_num [fibonacciSetup, fibonacciParams]

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `149` queries. -/
def wideParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 149
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

/-- `wide 64` has two quotient chunks. -/
theorem wide_chunks (S : Setup) (hair : S.air = wide 64) : S.chunks = 2 := by
  rw [Setup.chunks, hair, wide_logQuotientChunks 64 (by decide)]
  rfl

/-- `wide 64` opens `136` words. -/
theorem wide_numOpened (S : Setup) (hair : S.air = wide 64) : S.numOpened - 1 = 135 := by
  rw [Setup.numOpened, wide_chunks S hair, hair]
  rfl

/-- The constraint-folding and out-of-domain integers of `wide 64`: `63` and
`(3 n + 1) + n`. -/
theorem wide_integers_le (S : Setup) (hair : S.air = wide 64) :
    (S.air.constraints.length - 1) + (S.identityDegree + S.n) ≤ 4 * S.n + 64 := by
  have hid : S.identityDegree ≤ 3 * S.n + 1 := by
    rw [Setup.identityDegree, wide_chunks S hair]
    refine max_le (foldl_max_le _ _ _ _ (Nat.zero_le _) fun c hc ↦ ?_) (by omega)
    rw [hair] at hc
    simp only [wide, List.mem_map, List.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
    omega
  have hw : S.air.constraints.length = 64 := by
    rw [hair]
    simp only [wide, List.length_map, List.length_range]
  omega

/-- **100 bits on `2 ^ 20` rows.** The knowledge error of `wideSetup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is at
most `2 ^ (-100)`. -/
theorem wide_knowledgeError_le :
    knowledgeError wideSetup (1535 / 4096) (24575 / 65536) ≤ (2 ^ 100)⁻¹ := by
  have ha : wideSetup.params.maxLogArity = 1 := rfl
  have hrate : wideSetup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wideSetup.size : ℝ) = 2 ^ 22 := by norm_num [Setup.size, wideSetup, wideParams]
  have h1 := knowledgeError_le_curve wideSetup (1535 / 4096) (24575 / 65536)
    (by rw [hrate, hsize]; norm_num) (by norm_num) (by rw [hsize]; norm_num)
    (by rw [hrate]; norm_num)
  have h2 := friError_le_lossy wideSetup ha 16 (1535 / 4096) (1535 / 4096 + 1 / 2 ^ 17)
    (1 / 2 ^ 17) (by rw [hrate]; norm_num) (by norm_num) (lt_add_of_pos_right _ (by positivity))
    (by positivity)
  have hq : wideSetup.params.numQueries = 149 := rfl
  have hlarge : wideSetup.logN + wideSetup.params.logBlowup - 16 = 6 := rfl
  have hfolds : wideSetup.logN - wideSetup.params.logFinalPolyLen = 20 := rfl
  have hb : wideSetup.params.logBlowup = 2 := rfl
  rw [hq, hlarge, hfolds, hb] at h2
  refine h1.trans ((add_le_add le_rfl h2).trans
    (numbers_curve_le _ (2 ^ 22 + 64) _ _ _ _ 276841 _ 294726 _ (2561 / 4096 + 20 / 2 ^ 17)
      ?_ ?_ ?_ le_rfl ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
  · exact (wide_integers_le wideSetup rfl).trans (by decide)
  · rw [wide_numOpened wideSetup rfl, hrate, hsize]
    norm_num
  · simp only [LossyMca.lossyBound]
    norm_num
  · norm_num

/-- Knowledge soundness of `wideSetup` with error `2 ^ (-100)`, FRI at `1535/4096` and the
extractor at `24575/65536`: if no trace within `24575/65536` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem wide_knowledgeSoundness (publicValues : List F) (prover : Prover wideSetup) :
    (∀ trace ∈ closeTraces wideSetup (24575 / 65536 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 20 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ := by
  intro h
  refine (knowledgeSoundness wideSetup publicValues prover (1535 / 4096) (24575 / 65536) ?_
    h).trans wide_knowledgeError_le
  rw [rate_eq]
  norm_num [wideSetup, wideParams]

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `150` queries. -/
def wide21Params : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 150
  commitPowBits := 0
  queryPowBits := 0

/-- `wide 64` on `2 ^ 21` rows with `wide21Params`. -/
def wide21Setup : Setup where
  params := wide21Params
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide }
  blowup := by decide
  folds := by decide

/-- **100 bits on `2 ^ 21` rows.** The knowledge error of `wide21Setup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is at
most `2 ^ (-100)`. -/
theorem wide21_knowledgeError_le :
    knowledgeError wide21Setup (1535 / 4096) (24575 / 65536) ≤ (2 ^ 100)⁻¹ := by
  have ha : wide21Setup.params.maxLogArity = 1 := rfl
  have hrate : wide21Setup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wide21Setup.size : ℝ) = 2 ^ 23 := by
    norm_num [Setup.size, wide21Setup, wide21Params]
  have h1 := knowledgeError_le_curve wide21Setup (1535 / 4096) (24575 / 65536)
    (by rw [hrate, hsize]; norm_num) (by norm_num) (by rw [hsize]; norm_num)
    (by rw [hrate]; norm_num)
  have h2 := friError_le_lossy wide21Setup ha 16 (1535 / 4096) (1535 / 4096 + 1 / 2 ^ 17)
    (1 / 2 ^ 17) (by rw [hrate]; norm_num) (by norm_num) (lt_add_of_pos_right _ (by positivity))
    (by positivity)
  have hq : wide21Setup.params.numQueries = 150 := rfl
  have hlarge : wide21Setup.logN + wide21Setup.params.logBlowup - 16 = 7 := rfl
  have hfolds : wide21Setup.logN - wide21Setup.params.logFinalPolyLen = 21 := rfl
  have hb : wide21Setup.params.logBlowup = 2 := rfl
  rw [hq, hlarge, hfolds, hb] at h2
  refine h1.trans ((add_le_add le_rfl h2).trans
    (numbers_curve_le _ (2 ^ 23 + 64) _ _ _ _ 276841 _ 343847 _ (2561 / 4096 + 21 / 2 ^ 17)
      ?_ ?_ ?_ le_rfl ?_ (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
  · exact (wide_integers_le wide21Setup rfl).trans (by decide)
  · rw [wide_numOpened wide21Setup rfl, hrate, hsize]
    norm_num
  · simp only [LossyMca.lossyBound]
    norm_num
  · norm_num

/-- Knowledge soundness of `wide21Setup` with error `2 ^ (-100)`, FRI at `1535/4096` and the
extractor at `24575/65536`: if no trace within `24575/65536` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem wide21_knowledgeSoundness (publicValues : List F) (prover : Prover wide21Setup) :
    (∀ trace ∈ closeTraces wide21Setup (24575 / 65536 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ := by
  intro h
  refine (knowledgeSoundness wide21Setup publicValues prover (1535 / 4096) (24575 / 65536) ?_
    h).trans wide21_knowledgeError_le
  rw [rate_eq]
  norm_num [wide21Setup, wide21Params]

/-- SP1's FRI parameters (soundcalc's `sp1.toml`, core circuit): blowup `4`, folding by arity `2`
down to a constant (soundcalc's early-stop degree `4` is the final domain's size), `124` queries
with `16` bits of query grinding. -/
def sp1Params : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 124
  commitPowBits := 0
  queryPowBits := 16

/-- `wide 64` on `2 ^ 21` rows with `sp1Params`: SP1's FRI on `2 ^ 21` rows. -/
def wideSp1Setup : Setup where
  params := sp1Params
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide }
  blowup := by decide
  folds := by decide

/-- **100 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wideSp1Setup`, FRI at
`δ = 3/8 - 2 ^ (-16)` and the extractor at `δ' = 3/8 - 2 ^ (-18)`, is at most `2 ^ (-100)`. -/
theorem wideSp1_roundError_le :
    roundError wideSp1Setup (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ)) ≤ (2 ^ 100)⁻¹ := by
  have hδ := coe_three_eighths_sub (-16) 16 rfl (by norm_num)
  have hδ' := coe_three_eighths_sub (-18) 18 rfl (by norm_num)
  have hrate : wideSp1Setup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wideSp1Setup.size : ℝ) = 2 ^ 23 := by
    norm_num [Setup.size, wideSp1Setup, sp1Params]
  have h := roundError_le wideSp1Setup rfl 16 (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ))
    (1 / 2 ^ 22) (by rw [hδ, hrate, hsize]; norm_num)
    (by rw [hδ, hrate]; norm_num) (by rw [← NNReal.coe_pos, hδ]; norm_num)
    (by rw [hδ, hδ', hsize]; norm_num) (by rw [hδ', hrate]; norm_num) (by positivity)
  have hints := wide_integers_le wideSp1Setup rfl
  have hn : wideSp1Setup.n = 2097152 := rfl
  rw [hn] at hints
  have h1 := (Nat.le_add_right _ _).trans hints
  have h2 := (Nat.le_add_left _ _).trans hints
  have hcommit : wideSp1Setup.params.commitPowBits = 0 := rfl
  have hquery : wideSp1Setup.params.queryPowBits = 16 := rfl
  have hq : wideSp1Setup.params.numQueries = 124 := rfl
  have hfolds : wideSp1Setup.logN - wideSp1Setup.params.logFinalPolyLen = 21 := rfl
  have hb : wideSp1Setup.params.logBlowup = 2 := rfl
  rw [hcommit, hquery, hq, hfolds, hb, powFraction_zero, one_mul] at h
  refine h.trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · refine nat_div_card_le _ ((div_le_div_of_nonneg_right (Nat.cast_le.mpr h1)
      (by positivity)).trans ?_)
    norm_num
  · rw [hn]
    refine nat_div_card_le _ ((div_le_div_of_nonneg_right (Nat.cast_le.mpr h2)
      (by positivity)).trans ?_)
    norm_num
  · refine ofReal_div_card_le _ ?_
    rw [wide_numOpened wideSp1Setup rfl, hrate, hsize, hδ, hδ']
    norm_num
  · refine ofReal_div_card_le _ ?_
    simp only [LossyMca.lossyBound]
    rw [NNReal.coe_add, hδ]
    norm_num
  · refine powFraction_mul_le _ _ _ (by rw [hδ]; norm_num) ?_
    rw [hδ, KoalaBear.fieldSize]
    norm_num

end CompStark.Iop
