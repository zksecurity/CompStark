/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.KoalaBear.Challenge
public import CompStark.NonInteractive
public import CompStark.Sound.Numbers
public import CompStark.Sound.NumbersNi
public import CompStark.Complete.Quotient
public import CompStark.BatchNonInteractive
public import CompStark.Sound.BatchNumbersNi

/-! # Concrete security: 100 bits over the quartic extension, 117 with grinding, 128 over quintic

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

all but the queries over `|𝕂|`: `p ^ 4 ≈ 2 ^ 123.95` for `KoalaBear.Fast.Ext4`, which caps every
configuration below `2 ^ (-123.95)` (constraint folding alone is about `2 ^ (-117.98)`), and
`p ^ 5 ≈ 2 ^ 154.94` for `KoalaBear.Fast.Ext5`. In the random-oracle model, grinding divides every
round's error after `α` by about `2 ^ bits`; only constraint folding, which Plonky3 does not grind,
stays an integer over `|𝕂|`, so the quartic extension is capped near `2 ^ (-117.98)` instead.

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
at any radius: `(5/8) ^ 123 · 2 ^ (-16)` alone is about `2 ^ (-99.40)`. By `knowledgeSoundness_ro`,
a prover making `Q` oracle calls gets a proof accepted that the extractor cannot open with
probability at most `q · 2 ^ (-100) + 3 q² / |𝔽| ^ 8`, `q = Q + verifierQueries`,
`verifierQueries = 15 + 5 · 21 + 124 · 553 = 68692` (`wideSp1Setup_verifierQueries`,
`wideSp1_knowledgeSoundness_ro`).

`wideGrindSetup`: `wide 64` on `2 ^ 21` rows over the quartic extension, blowup `4`, `21` folds of
arity `2` down to a constant and `144` queries, grinding `20` bits before `ζ`, `12` before the
batching challenge, `8` per fold and `20` before the queries (`wideGrindParams`). In the
random-oracle model, with FRI at `δ = 3/8 - 2 ^ (-10)`, the extractor at `δ' = 3/8 - 2 ^ (-11)`,
`loss = 2 ^ (-15)`, `δ_int = δ + loss` and `t = 10`:

* constraint folding `63`, about `2 ^ (-117.98)`;
* out of domain `powFraction 20 · (2 ^ 23 + 64)`, `powFraction 20 = 2033 / p`, about
  `2 ^ (-120.95)`;
* batching `powFraction 12 · 135 · max(T₁, T₂)`, `T₁ ≈ 514.67`, `T₂ ≈ 767.37`, about
  `2 ^ (-119.29)`;
* FRI's folds: `powFraction 8 · max(T₁, δ_int / loss, 2 ^ t) = powFraction 8 · 12257`, about
  `2 ^ (-118.37)`;
* FRI's queries `powFraction 20 · (5/8 + 2 ^ (-10) + 21 · 2 ^ (-15) + 1/p) ^ 144`, about
  `2 ^ (-117.10)`.

Every round error is at most `2 ^ (-117)` (`wideGrind_roundError_le`); the queries dominate, and
constraint folding, without grinding, keeps any configuration above `2 ^ (-117.98)`. `143` queries
do not reach `2 ^ (-117)` at any radius: `(5/8) ^ 143 · powFraction 20` alone is about
`2 ^ (-116.96)`. By `knowledgeSoundness_ro`, a prover making `Q` oracle calls gets a proof accepted
that the extractor cannot open with probability at most `q · 2 ^ (-117) + 3 q² / |𝔽| ^ 8`,
`q = Q + verifierQueries`, `verifierQueries = 15 + 5 · 21 + 144 · 553 = 79752`
(`wideGrindSetup_verifierQueries`, `wideGrind_knowledgeSoundness_ro`).

`wide5Setup`: `wide 64` on `2 ^ 21` rows over the quintic extension `KoalaBear.Fast.Ext5` with
zkDTVM's FRI (soundcalc's `zkdtvm_v080.toml`, `wide5Params`): blowup `4` (`N = 2 ^ 23`), `21` folds
of arity `2` down to a constant, `160` queries and `20` bits of query grinding. In the random-oracle
model, with FRI at `δ = 3/8 - 2 ^ (-18)`, the extractor at `δ' = 3/8 - 2 ^ (-20)`,
`loss = 2 ^ (-26)`, `δ_int = δ + loss` and `t = 18`:

* constraint folding `63`, about `2 ^ (-148.97)`;
* out of domain `(3 · 2 ^ 21 + 1) + 2 ^ 21`, about `2 ^ (-131.94)`;
* batching `137 · max(T₁, T₂)`, `T₁ ≈ 131074.67`, `T₂ ≈ 142987.18`, about `2 ^ (-130.72)`;
* FRI's folds: `max(T₁, δ_int / loss, 2 ^ t) = δ · 2 ^ 26 + 1 = 25165569`, about `2 ^ (-130.36)`;
* FRI's queries `powFraction 20 · (5/8 + 2 ^ (-18) + 21 · 2 ^ (-26) + 1/p) ^ 160`, with
  `powFraction 20 = 2033 / p ≈ 2 ^ (-19.9993)`, about `2 ^ (-128.49)`.

Every round error is at most `2 ^ (-128)` (`wide5_roundError_le`). `159` queries do not reach it at
any radius: `(5/8) ^ 159 · powFraction 20` alone is about `2 ^ (-127.81)`.
By `knowledgeSoundness_ro`, a prover making `Q` oracle calls gets a proof accepted that the
extractor cannot open with probability at most `q · 2 ^ (-128) + 3 q² / |𝔽| ^ 8`,
`q = Q + verifierQueries`, `verifierQueries = 18 + 6 · 21 + 160 · 553 = 88624`
(`wide5Setup_verifierQueries`, `wide5_knowledgeSoundness_ro`).

`wide5iSetup`: the interactive counterpart, which gets no credit for grinding: `wide 64` on `2 ^ 21`
rows over `KoalaBear.Fast.Ext5`, blowup `4` and `190` queries (`wide5iParams`), with FRI at
`δ = 3/8 - 2 ^ (-14)`, the extractor at `δ' = 3/8 - 2 ^ (-17)`, `loss = 2 ^ (-18)` and `t = 14`:

* constraint folding and out of domain together at most `4 · 2 ^ 21 + 64`, about `2 ^ (-131.94)`;
* batching `137 · max(T₁, T₂) ≤ 1122670`, `T₁ ≈ 8194.67`, `T₂ ≈ 7053.05`, about `2 ^ (-134.84)`;
* FRI's folds: the `9` onto at least `2 ^ 14` points `δ · 2 ^ 18 + 1 = 98289` each, the `12` smaller
  ones `2 ^ 14`, about `2 ^ (-135.16)`;
* FRI's queries `(5/8 + 2 ^ (-14) + 21 · 2 ^ (-18)) ^ 190`, about `2 ^ (-128.77)`.

The total is at most `2 ^ (-128)` (`wide5i_knowledgeError_le`, `wide5i_knowledgeSoundness`), about
`2 ^ (-128.59)` exactly; `189` queries do not reach it at these radii.

`wideBatchSetup`: a batch of three `wideBus 64` instances on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows
over `KoalaBear.Fast.Ext5`, every row receiving four columns and sending four on one global bus
(`wideBus`: `wide 64` and two interactions of width `W = 4` per row, `T = 2 (2 ^ 20 + 2 ^ 19 +
2 ^ 16) = 3276800` in all; its LogUp constraints keep the two quotient chunks, add `4` constraints
of degree `3` and two permutation columns, `20` opened words over the quintic extension), with
`wide5iParams` (blowup `4`, `190` queries), FRI at `δ = 3/8 - 2 ^ (-14)`, the extractor at
`δ' = 3/8 - 2 ^ (-17)`, `loss = 2 ^ (-18)` and `t = 14` (`batchKnowledgeError_le_curve`,
`friErrorWith_le_lossy`):

* the lookup challenges: `T + (T - 1) W = 16383996` (`lookupError`), about `2 ^ (-130.98)`;
* constraint folding and out of domain, the worst instance's: at most `4 · 2 ^ 20 + 68`, about
  `2 ^ (-132.94)`;
* batching the `158` opened words of each instance's domain size, alone at its size:
  `157 · max(T₁, T₂) ≤ 1286615`, `T₁ ≈ 8194.67`, `T₂ ≈ 8191.67` on the smallest domain, about
  `2 ^ (-134.65)`;
* FRI's folds from `2 ^ 22` points, injecting the shorter instances' words at `2 ^ 21` and
  `2 ^ 18` points: the `8` folds onto at least `2 ^ 14` points and the `2` injections
  `δ · 2 ^ 18 + 1 = 98289` each, the `12` smaller folds `2 ^ 14`, about `2 ^ (-135.01)`;
* FRI's queries `(5/8 + 2 ^ (-14) + 20 · 2 ^ (-18)) ^ 190`, about `2 ^ (-128.77)`.

The total is at most `2 ^ (-128)` (`wideBatch_knowledgeError_le`, `wideBatch_knowledgeSoundness`),
about `2 ^ (-128.39)` exactly. The batch pays for the lookups once, for `α`, `ζ` and batching once,
as its failing instance would alone among the instances of its size; FRI pays one more fold error
per injected height. Plonky3's `p3-security` estimates LogUp's error as `N (W + 2) / |𝕂|` for `N`
interactions; the bound here, `(T + (T - 1) W) / |𝕂|`, is Schwartz–Zippel on the numerator with
every denominator cleared, at most `(W + 1) T / |𝕂|`, the same up to `T / |𝕂|`, and it counts the
poles of every tuple, whatever its multiplicity.

In the random-oracle model the batch pays each round once, at its worst instance
(`Batch.roundError`, `CompStark/BatchNonInteractiveError.lean`, terms bounded in
`CompStark/Sound/BatchNumbersNi.lean`), the lookup challenges with the lookup grinding; a fold
that injects a shorter instance's word costs twice the lossy bound (`friFoldErrorB_le`). For the
same three instances (`WideBatch`), with the extractor at `δ'` and every domain of at least
`2 ^ 18` points, so that `δ < δ' - 2/N` on each:

`wideBatch5Setup`, over `KoalaBear.Fast.Ext5` with `wide5Params` (`160` queries, `20` bits of query
grinding), FRI at `δ = 3/8 - 2 ^ (-16)`, the extractor at `δ' = 3/8 - 2 ^ (-18)`,
`loss = 2 ^ (-26)` and `t = 16`:

* the lookup challenges `16383996`, about `2 ^ (-130.98)`;
* constraint folding `67`, about `2 ^ (-148.88)`;
* out of domain at most `4 · 2 ^ 20 + 1`, about `2 ^ (-132.94)`;
* batching `157 · max(T₁, T₂) ≤ 157 · 98304`, `T₂` at most `(3/8) · 2 ^ 18` on the smallest
  domain, about `2 ^ (-131.06)`;
* FRI's folds `max(2 δ_int / loss, 2 ^ 16) = 2 · 25164801`, about `2 ^ (-129.36)`;
* FRI's queries `powFraction 20 · (5/8 + 2 ^ (-16) + 20 · 2 ^ (-26) + 1/p) ^ 160`, about
  `2 ^ (-128.49)`.

Every round error is at most `2 ^ (-128)` (`wideBatch5_roundError_le`), and
`verifierQueries = 11 + 18 + 6 · 20 + 160 · 622 = 99669` (`wideBatch5Setup_verifierQueries`,
`wideBatch5_knowledgeSoundness_ro`).

`wideBatchGrindSetup`, over `KoalaBear.Fast.Ext4` with `wideBusGrindParams` (`144` queries,
grinding in every round but `α`, `18` bits before the lookup challenges), FRI at
`δ = 3/8 - 2 ^ (-10)`, the extractor at `δ' = 3/8 - 2 ^ (-11)`, `loss = 2 ^ (-15)` and `t = 10`:

* the lookup challenges `powFraction 18 · 16383996`, about `2 ^ (-117.99)`, `2 ^ (-99.99)`
  without grinding;
* constraint folding `67`, about `2 ^ (-117.89)`;
* out of domain `powFraction 20 · (4 · 2 ^ 20 + 1)`, about `2 ^ (-121.95)`;
* batching `powFraction 12 · 151 · 781`, about `2 ^ (-119.11)`;
* FRI's folds `powFraction 8 · 2 · 12257`, about `2 ^ (-117.37)`;
* FRI's queries `powFraction 20 · (5/8 + 2 ^ (-10) + 20 · 2 ^ (-15) + 1/p) ^ 144`, about
  `2 ^ (-117.11)`.

Every round error is at most `2 ^ (-117)` (`wideBatchGrind_roundError_le`), and
`verifierQueries = 9 + 15 + 5 · 20 + 144 · 622 = 89692` (`wideBatchGrindSetup_verifierQueries`,
`wideBatchGrind_knowledgeSoundness_ro`). Constraint folding, which Plonky3 does not grind, keeps
the quartic extension above `2 ^ (-117.89)`: `117` bits is the best integer level, reached with
`18` bits of lookup grinding (`17` leave the lookup challenges at `2 ^ (-116.99)`).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

variable {EF : Type} [Challenge F EF]

/-- FRI with blowup `16`, folding by arity `2` down to a constant, and `110` queries. -/
def fibonacciParams : Fri.Params where
  logBlowup := 4
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 110
  commitPowBits := 0
  queryPowBits := 0

/-- The Fibonacci AIR on `2 ^ 10` rows with `fibonacciParams`. -/
def fibonacciSetup : Setup KoalaBear.Fast.Ext4 where
  params := fibonacciParams
  air := fibonacci
  logN := 10
  valid :=
    { colsInWidth := by unfold Air.ColsInWidth; decide
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := fibonacci_degreeFits 10
      twoAdic := by decide
      chunksFit := by
        rw [logQuotientChunks_of _ _ 0 rfl (by decide)]
        exact Nat.zero_le _
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
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
      rw [Setup.identityDegree_nil, Setup.chunks_nil]
      simp only [Setup.n, fibonacciSetup]
      rw [logQuotientChunks_of _ _ 0 rfl (by decide)]
      simp only [fibonacci, List.foldl, Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
      norm_num
    have hc : fibonacciSetup.chunks = 1 := by
      change 2 ^ fibonacci.logQuotientChunks 10 = 1
      rw [logQuotientChunks_of _ _ 0 rfl (by decide)]
      rfl
    rw [Setup.numConstraints_nil, Setup.numOpened_nil, hid, hc]
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
theorem wide_colsInWidth (w : Nat) : (wide w : Air F).ColsInWidth := by
  intro c hc
  simp only [wide, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.colsBelow, Bool.true_and,
    Bool.and_self, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨hj, Nat.mod_lt _ (by omega)⟩, hj⟩

/-- `wide 64` on `2 ^ 20` rows with `wideParams`. -/
def wideSetup : Setup KoalaBear.Fast.Ext4 where
  params := wideParams
  air := wide 64
  logN := 20
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 20
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- The largest of values at most `b` is at most `b`. -/
theorem foldl_max_le {α : Type} (f : α → Nat) (b : Nat) :
    ∀ (l : List α) (a : Nat), a ≤ b → (∀ x ∈ l, f x ≤ b) → l.foldl (fun m x ↦ max m (f x)) a ≤ b
  | [], _, ha, _ => ha
  | x :: l, _, ha, h => foldl_max_le f b l _ (max_le ha (h x List.mem_cons_self))
      fun y hy ↦ h y (List.mem_cons_of_mem _ hy)

/-- `wide 64` has two quotient chunks. -/
theorem wide_chunks (S : Setup EF) (hair : S.air = wide 64) : S.chunks = 2 := by
  rw [Setup.chunks_nil, hair, wide_logQuotientChunks 64 _ (by decide)]
  rfl

/-- `wide 64` opens `128 + 2 d` words. -/
theorem wide_numOpened (S : Setup EF) (hair : S.air = wide 64) :
    S.numOpened - 1 = 127 + 2 * Challenge.d EF := by
  rw [Setup.numOpened_nil, wide_chunks S hair, hair]
  change 2 * 64 + Challenge.d EF * 2 - 1 = _
  have := (Challenge.params EF).two_le
  omega

/-- The constraint-folding and out-of-domain integers of `wide 64`: `63` and
`(3 n + 1) + n`. -/
theorem wide_integers_le (S : Setup EF) (hair : S.air = wide 64) :
    (S.numConstraints - 1) + (S.identityDegree + S.n) ≤ 4 * S.n + 64 := by
  have hid : S.identityDegree ≤ 3 * S.n + 1 := by
    rw [Setup.identityDegree_nil, wide_chunks S hair]
    refine max_le (foldl_max_le _ _ _ _ (Nat.zero_le _) fun c hc ↦ ?_) (by omega)
    rw [hair] at hc
    simp only [wide, List.mem_map, List.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
    omega
  have hw : S.numConstraints = 64 := by
    rw [Setup.numConstraints_nil, hair]
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
      ?_ ?_ ?_ le_rfl ?_ (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)))
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
def wide21Setup : Setup KoalaBear.Fast.Ext4 where
  params := wide21Params
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
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
      ?_ ?_ ?_ le_rfl ?_ (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)))
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
def wideSp1Setup : Setup KoalaBear.Fast.Ext4 where
  params := sp1Params
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- The verifier's oracle calls on a proof for `wideSp1Setup`: `15 + 5 · 21 + 124 · 553`. -/
theorem wideSp1Setup_verifierQueries : wideSp1Setup.verifierQueries = 68692 := by decide +kernel

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
  have hood : wideSp1Setup.params.oodPowBits = 0 := rfl
  have hbatch : wideSp1Setup.params.batchPowBits = 0 := rfl
  have hcommit : wideSp1Setup.params.commitPowBits = 0 := rfl
  have hquery : wideSp1Setup.params.queryPowBits = 16 := rfl
  have hq : wideSp1Setup.params.numQueries = 124 := rfl
  have hfolds : wideSp1Setup.logN - wideSp1Setup.params.logFinalPolyLen = 21 := rfl
  have hb : wideSp1Setup.params.logBlowup = 2 := rfl
  rw [hood, hbatch, hcommit, hquery, hq, hfolds, hb] at h
  simp only [powFraction_zero, one_mul] at h
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
    rw [hδ, KoalaBear.card_eq]
    norm_num

/-- **100 bits per oracle call on `2 ^ 21` rows.** A prover for `wideSp1Setup` making at most `Q`
oracle calls gets a proof accepted while no trace close to the one it committed to satisfies the
AIR with probability at most `q · 2 ^ (-100) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideSp1_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : NIProver wideSp1Setup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run wideSp1Setup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = wideSp1Setup.logN ∧
        ∀ trace ∈ closeTraces wideSp1Setup (3 / 8 - 2 ^ (-18 : ℤ) : NNReal)
            (committedTrace wideSp1Setup log proof),
          ¬ wideSp1Setup.air.Satisfied wideSp1Setup.logN trace publicValues] ≤
      (Q + wideSp1Setup.verifierQueries) * (2 ^ 100)⁻¹ +
        hashError F (Q + wideSp1Setup.verifierQueries) := by
  refine (knowledgeSoundness_ro wideSp1Setup publicValues (3 / 8 - 2 ^ (-16 : ℤ))
    (3 / 8 - 2 ^ (-18 : ℤ)) ?_ Q prover hQ).trans ?_
  · rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num), rate_eq]
    norm_num [wideSp1Setup, sp1Params]
  · gcongr
    exact wideSp1_roundError_le

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `144` queries, with grinding
in every round after `α`: `20` bits before `ζ`, `12` before the batching challenge, `8` per fold
and `20` before the queries. -/
def wideGrindParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 144
  commitPowBits := 8
  queryPowBits := 20
  batchPowBits := 12
  oodPowBits := 20

/-- `wide 64` on `2 ^ 21` rows over the quartic extension with `wideGrindParams`. -/
def wideGrindSetup : Setup KoalaBear.Fast.Ext4 where
  params := wideGrindParams
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- The verifier's oracle calls on a proof for `wideGrindSetup`: `15 + 5 · 21 + 144 · 553`. -/
theorem wideGrindSetup_verifierQueries : wideGrindSetup.verifierQueries = 79752 := by
  decide +kernel

/-- **117 bits per oracle answer on `2 ^ 21` rows over the quartic extension.** Every round error
of `wideGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-10)` and the extractor at `δ' = 3/8 - 2 ^ (-11)`, is
at most `2 ^ (-117)`. -/
theorem wideGrind_roundError_le :
    roundError wideGrindSetup (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ)) ≤ (2 ^ 117)⁻¹ := by
  have hδ := coe_three_eighths_sub (-10) 10 rfl (by norm_num)
  have hδ' := coe_three_eighths_sub (-11) 11 rfl (by norm_num)
  have hrate : wideGrindSetup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wideGrindSetup.size : ℝ) = 2 ^ 23 := by
    norm_num [Setup.size, wideGrindSetup, wideGrindParams]
  have h := roundError_le wideGrindSetup rfl 10 (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ))
    (1 / 2 ^ 15) (by rw [hδ, hrate, hsize]; norm_num)
    (by rw [hδ, hrate]; norm_num) (by rw [← NNReal.coe_pos, hδ]; norm_num)
    (by rw [hδ, hδ', hsize]; norm_num) (by rw [hδ', hrate]; norm_num) (by positivity)
  have hints := wide_integers_le wideGrindSetup rfl
  have hn : wideGrindSetup.n = 2097152 := rfl
  rw [hn] at hints
  have h2 := (Nat.le_add_left _ _).trans hints
  have hood : wideGrindSetup.params.oodPowBits = 20 := rfl
  have hbatch : wideGrindSetup.params.batchPowBits = 12 := rfl
  have hcommit : wideGrindSetup.params.commitPowBits = 8 := rfl
  have hquery : wideGrindSetup.params.queryPowBits = 20 := rfl
  have hq : wideGrindSetup.params.numQueries = 144 := rfl
  have hfolds : wideGrindSetup.logN - wideGrindSetup.params.logFinalPolyLen = 21 := rfl
  have hb : wideGrindSetup.params.logBlowup = 2 := rfl
  have hc : wideGrindSetup.air.constraints.length - 1 = 63 := by
    simp only [wideGrindSetup, wide, List.length_map, List.length_range]
  rw [hood, hbatch, hcommit, hquery, hq, hfolds, hb, hc] at h
  refine h.trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · refine nat_div_card_le _ ?_
    norm_num
  · rw [hn]
    refine (mul_le_mul_right (ENNReal.div_le_div_right (Nat.cast_le.mpr h2) _) _).trans ?_
    rw [← ENNReal.ofReal_natCast]
    refine powFraction_mul_div_card_le _ _ ?_
    rw [KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_div_card_le _ _ ?_
    rw [wide_numOpened wideGrindSetup rfl, hrate, hsize, hδ, hδ', KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_div_card_le _ _ ?_
    simp only [LossyMca.lossyBound]
    rw [NNReal.coe_add, hδ, KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_le _ _ _ (by rw [hδ]; norm_num) ?_
    rw [hδ, KoalaBear.card_eq]
    norm_num

/-- **117 bits per oracle call on `2 ^ 21` rows over the quartic extension.** A prover for
`wideGrindSetup` making at most `Q` oracle calls gets a proof accepted while no trace close to the
one it committed to satisfies the AIR with probability at most
`q · 2 ^ (-117) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideGrind_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : NIProver wideGrindSetup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run wideGrindSetup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = wideGrindSetup.logN ∧
        ∀ trace ∈ closeTraces wideGrindSetup (3 / 8 - 2 ^ (-11 : ℤ) : NNReal)
            (committedTrace wideGrindSetup log proof),
          ¬ wideGrindSetup.air.Satisfied wideGrindSetup.logN trace publicValues] ≤
      (Q + wideGrindSetup.verifierQueries) * (2 ^ 117)⁻¹ +
        hashError F (Q + wideGrindSetup.verifierQueries) := by
  refine (knowledgeSoundness_ro wideGrindSetup publicValues (3 / 8 - 2 ^ (-10 : ℤ))
    (3 / 8 - 2 ^ (-11 : ℤ)) ?_ Q prover hQ).trans ?_
  · rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num), rate_eq]
    norm_num [wideGrindSetup, wideGrindParams]
  · gcongr
    exact wideGrind_roundError_le

/-- zkDTVM's FRI parameters (soundcalc's `zkdtvm_v080.toml`, compress circuit): blowup `4`, folding
by arity `2` down to a constant, `160` queries with `20` bits of query grinding. -/
def wide5Params : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 160
  commitPowBits := 0
  queryPowBits := 20

/-- `wide 64` on `2 ^ 21` rows over the quintic extension with `wide5Params`. -/
def wide5Setup : Setup KoalaBear.Fast.Ext5 where
  params := wide5Params
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- The verifier's oracle calls on a proof for `wide5Setup`: `18 + 6 · 21 + 160 · 553`. -/
theorem wide5Setup_verifierQueries : wide5Setup.verifierQueries = 88624 := by decide +kernel

/-- **128 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wide5Setup`, FRI at
`δ = 3/8 - 2 ^ (-18)` and the extractor at `δ' = 3/8 - 2 ^ (-20)`, is at most `2 ^ (-128)`. -/
theorem wide5_roundError_le :
    roundError wide5Setup (3 / 8 - 2 ^ (-18 : ℤ)) (3 / 8 - 2 ^ (-20 : ℤ)) ≤ (2 ^ 128)⁻¹ := by
  have hδ := coe_three_eighths_sub (-18) 18 rfl (by norm_num)
  have hδ' := coe_three_eighths_sub (-20) 20 rfl (by norm_num)
  have hrate : wide5Setup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wide5Setup.size : ℝ) = 2 ^ 23 := by
    norm_num [Setup.size, wide5Setup, wide5Params]
  have h := roundError_le wide5Setup rfl 18 (3 / 8 - 2 ^ (-18 : ℤ)) (3 / 8 - 2 ^ (-20 : ℤ))
    (1 / 2 ^ 26) (by rw [hδ, hrate, hsize]; norm_num)
    (by rw [hδ, hrate]; norm_num) (by rw [← NNReal.coe_pos, hδ]; norm_num)
    (by rw [hδ, hδ', hsize]; norm_num) (by rw [hδ', hrate]; norm_num) (by positivity)
  have hints := wide_integers_le wide5Setup rfl
  have hn : wide5Setup.n = 2097152 := rfl
  rw [hn] at hints
  have h1 := (Nat.le_add_right _ _).trans hints
  have h2 := (Nat.le_add_left _ _).trans hints
  have hood : wide5Setup.params.oodPowBits = 0 := rfl
  have hbatch : wide5Setup.params.batchPowBits = 0 := rfl
  have hcommit : wide5Setup.params.commitPowBits = 0 := rfl
  have hquery : wide5Setup.params.queryPowBits = 20 := rfl
  have hq : wide5Setup.params.numQueries = 160 := rfl
  have hfolds : wide5Setup.logN - wide5Setup.params.logFinalPolyLen = 21 := rfl
  have hb : wide5Setup.params.logBlowup = 2 := rfl
  rw [hood, hbatch, hcommit, hquery, hq, hfolds, hb] at h
  simp only [powFraction_zero, one_mul] at h
  refine h.trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_))))
  · refine nat_div_card_le _ ((div_le_div_of_nonneg_right (Nat.cast_le.mpr h1)
      (by positivity)).trans ?_)
    norm_num
  · rw [hn]
    refine nat_div_card_le _ ((div_le_div_of_nonneg_right (Nat.cast_le.mpr h2)
      (by positivity)).trans ?_)
    norm_num
  · refine ofReal_div_card_le _ ?_
    rw [wide_numOpened wide5Setup rfl, hrate, hsize, hδ, hδ']
    norm_num
  · refine ofReal_div_card_le _ ?_
    simp only [LossyMca.lossyBound]
    rw [NNReal.coe_add, hδ]
    norm_num
  · refine powFraction_mul_le _ _ _ (by rw [hδ]; norm_num) ?_
    rw [hδ, KoalaBear.card_eq]
    norm_num

/-- **128 bits per oracle call on `2 ^ 21` rows over the quintic extension.** A prover for
`wide5Setup` making at most `Q` oracle calls gets a proof accepted while no trace close to the one
it committed to satisfies the AIR with probability at most `q · 2 ^ (-128) + hashError q`,
`q = Q + verifierQueries`. -/
theorem wide5_knowledgeSoundness_ro (publicValues : List F) (Q : Nat)
    (prover : NIProver wide5Setup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run wide5Setup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = wide5Setup.logN ∧
        ∀ trace ∈ closeTraces wide5Setup (3 / 8 - 2 ^ (-20 : ℤ) : NNReal)
            (committedTrace wide5Setup log proof),
          ¬ wide5Setup.air.Satisfied wide5Setup.logN trace publicValues] ≤
      (Q + wide5Setup.verifierQueries) * (2 ^ 128)⁻¹ +
        hashError F (Q + wide5Setup.verifierQueries) := by
  refine (knowledgeSoundness_ro wide5Setup publicValues (3 / 8 - 2 ^ (-18 : ℤ))
    (3 / 8 - 2 ^ (-20 : ℤ)) ?_ Q prover hQ).trans ?_
  · rw [coe_three_eighths_sub (-20) 20 rfl (by norm_num), rate_eq]
    norm_num [wide5Setup, wide5Params]
  · gcongr
    exact wide5_roundError_le

/-- FRI with blowup `4`, folding by arity `2` down to a constant, and `190` queries without
grinding. -/
def wide5iParams : Fri.Params where
  logBlowup := 2
  logFinalPolyLen := 0
  maxLogArity := 1
  numQueries := 190
  commitPowBits := 0
  queryPowBits := 0

/-- `wide 64` on `2 ^ 21` rows over the quintic extension with `wide5iParams`. -/
def wide5iSetup : Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  air := wide 64
  logN := 21
  valid :=
    { colsInWidth := wide_colsInWidth 64
      preprocessedSize := rfl
      periodicFits := rfl
      degreeFits := wide_degreeFits 64 21
      twoAdic := by decide
      chunksFit := by
        rw [wide_logQuotientChunks 64 _ (by decide)]
        decide
      folds := by decide
      finalPolyFits := by decide
      queries := by decide
      blowup := by decide }
  folds := by decide

/-- **128 bits, interactively, on `2 ^ 21` rows.** The knowledge error of `wide5iSetup`, FRI at
`δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at `δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, is
at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeError_le :
    knowledgeError wide5iSetup (6143 / 16384) (49151 / 131072) ≤ (2 ^ 128)⁻¹ := by
  have ha : wide5iSetup.params.maxLogArity = 1 := rfl
  have hrate : wide5iSetup.rate = 1 / 2 ^ 2 := rate_eq _
  have hsize : (wide5iSetup.size : ℝ) = 2 ^ 23 := by
    norm_num [Setup.size, wide5iSetup, wide5iParams]
  have h1 := knowledgeError_le_curve wide5iSetup (6143 / 16384) (49151 / 131072)
    (by rw [hrate, hsize]; norm_num) (by norm_num) (by rw [hsize]; norm_num)
    (by rw [hrate]; norm_num)
  have h2 := friError_le_lossy wide5iSetup ha 14 (6143 / 16384) (6143 / 16384 + 1 / 2 ^ 18)
    (1 / 2 ^ 18) (by rw [hrate]; norm_num) (by norm_num) (lt_add_of_pos_right _ (by positivity))
    (by positivity)
  have hq : wide5iSetup.params.numQueries = 190 := rfl
  have hlarge : wide5iSetup.logN + wide5iSetup.params.logBlowup - 14 = 9 := rfl
  have hfolds : wide5iSetup.logN - wide5iSetup.params.logFinalPolyLen = 21 := rfl
  have hb : wide5iSetup.params.logBlowup = 2 := rfl
  rw [hq, hlarge, hfolds, hb] at h2
  refine h1.trans ((add_le_add le_rfl h2).trans
    (numbers_curve_le _ (2 ^ 23 + 64) _ _ _ _ 1122670 _ 884601 _ (10241 / 16384 + 21 / 2 ^ 18)
      ?_ ?_ ?_ le_rfl ?_ (by norm_num) (by norm_num) (by norm_num) ?_))
  · exact (wide_integers_le wide5iSetup rfl).trans (by decide)
  · rw [wide_numOpened wide5iSetup rfl, hrate, hsize]
    norm_num
  · simp only [LossyMca.lossyBound]
    norm_num
  · norm_num
  · norm_num

/-- Knowledge soundness of `wide5iSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `49151/131072`: if no trace within `49151/131072` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeSoundness (publicValues : List F) (prover : Prover wide5iSetup) :
    (∀ trace ∈ closeTraces wide5iSetup (49151 / 131072 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 128)⁻¹ := by
  intro h
  refine (knowledgeSoundness wide5iSetup publicValues prover (6143 / 16384) (49151 / 131072) ?_
    h).trans wide5i_knowledgeError_le
  rw [rate_eq]
  norm_num [wide5iSetup, wide5iParams]


/-! ### Batches with lookups -/

section WideBus
open CompStark.Lookup

theorem extMul_eq (a b : ExtExpr F) : a * b = .mul a b := rfl
theorem extSub_eq (a b : ExtExpr F) : a - b = .sub a b := rfl
theorem extAdd_eq (a b : ExtExpr F) : a + b = .add a b := rfl

/-- `wideBus 64` packs its one lookup as it is. -/
theorem wideBus_packedLookups (logN : ℕ) :
    (wideBus 64 : Air F).packedLookups logN = [wideBusLookup] := rfl

/-- The LogUp constraints of `wideBus 64`, of degree `3`, keep its two quotient chunks. -/
theorem wideBus_logQuotientChunksWith (logN : ℕ) :
    (wideBus 64 : Air F).logQuotientChunksWith logN (logUpConstraints [wideBusLookup]) = 1 := by
  have hmax : (wideBus 64 : Air F).maxDegree = 3 := by decide +kernel
  have hext : (logUpConstraints [wideBusLookup] : List (ExtExpr F)).foldl
      (fun m c ↦ max m c.degree) 0 = 3 := by decide +kernel
  unfold Air.logQuotientChunksWith extDegree Air.constraintDegree
  simp only [show (wideBus 64 : Air F).periodic = [] from rfl, ↓reduceIte, hmax, hext]
  rw [show max (max 3 3) 2 - 1 = 2 ^ 1 from rfl,
    Nat.nextPowerOfTwo_eq_self (isPowerOfTwo_two_pow 1),
    Nat.log2_two_pow]

end WideBus

section WideBusSetup
open CompStark.Lookup

/-- The lookup constraints of `wideBus 64`: the fraction pin and the accumulator's three. -/
theorem wideBus_logUpConstraints : (logUpConstraints [wideBusLookup] : List (ExtExpr F)) =
    [fractionPin 0 wideBusLookup, .base .isFirstRow * .perm 0,
      .base .isTransition * (.permNext 0 - .perm 0 - rowSum 1),
      .base .isLastRow * (.terminal - .perm 0 - rowSum 1)] := rfl

variable {ls : List (Lookup F)}

/-- `wideBus 64` keeps the two quotient chunks of `wide 64`. -/
theorem wideBus_chunks (T : Setup EF ls) (hls : ls = [wideBusLookup]) (hair : T.air = wideBus 64) :
    T.chunks = 2 := by
  subst hls
  show 2 ^ T.air.logQuotientChunksWith T.logN (logUpConstraints [wideBusLookup]) = 2
  rw [hair, wideBus_logQuotientChunksWith]
  rfl

/-- `wideBus 64` opens `128 + 2 d` trace and chunk words and `4 d` permutation words. -/
theorem wideBus_numOpened (T : Setup EF ls) (hls : ls = [wideBusLookup])
    (hair : T.air = wideBus 64) : T.numOpened - 1 = 127 + 6 * Challenge.d EF := by
  have hc := wideBus_chunks T hls hair
  subst hls
  show T.air.width + T.air.mainNextWidth + Challenge.d EF * T.chunks + T.air.preprocessedWidth +
    T.air.preprocessedNextWidth + 2 * (Challenge.d EF * 2) - 1 = _
  rw [hc, hair]
  change 64 + 64 + Challenge.d EF * 2 + 0 + 0 + 2 * (Challenge.d EF * 2) - 1 = _
  have := (Challenge.params EF).two_le
  omega

/-- `wideBus 64` folds its `64` constraints and its `4` LogUp constraints. -/
theorem wideBus_numConstraints (T : Setup EF ls) (hls : ls = [wideBusLookup])
    (hair : T.air = wideBus 64) : T.numConstraints = 68 := by
  subst hls
  show T.air.constraints.length + (logUpConstraints [wideBusLookup]).length = 68
  rw [hair, wideBus_logUpConstraints]
  simp only [wideBus, wide, List.length_map, List.length_range, List.length_cons, List.length_nil]

/-- The constraint identity of `wideBus 64` has degree at most `3 n + 1`: the AIR's transitions;
the LogUp constraints reach `3 n`. -/
theorem wideBus_identityDegree (T : Setup EF ls) (hls : ls = [wideBusLookup])
    (hair : T.air = wideBus 64) : T.identityDegree ≤ 3 * T.n + 1 := by
  have hc := wideBus_chunks T hls hair
  subst hls
  rw [Setup.identityDegree, hc]
  refine max_le (foldl_max_le _ _ _ _ (foldl_max_le _ _ _ _ (Nat.zero_le _) fun c hc ↦ ?_)
    fun g hg ↦ ?_) (by omega)
  · rw [hair] at hc
    simp only [wideBus, wide, List.mem_map, List.mem_range] at hc
    obtain ⟨j, -, rfl⟩ := hc
    simp only [Expr.mul_eq, Expr.sub_eq, Expr.add_eq, Expr.degBound]
    omega
  · change g ∈ (logUpConstraints [wideBusLookup] : List (ExtExpr F)) at hg
    rw [wideBus_logUpConstraints] at hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;>
      simp only [fractionPin, foldFractions, denominator, wideBusLookup, Stark.Lookup.tuples,
        rowSum, List.map, List.foldl, List.range, List.range.loop, extMul_eq, extSub_eq, extAdd_eq,
        ExtExpr.degBound, Expr.degBound] <;> omega

end WideBusSetup

/-- `wideBus 64` on `2 ^ logN` rows with FRI parameters of blowup `4` and a constant final
polynomial, for `logN ≤ 22`. -/
theorem wideBus_valid (P : Fri.Params) (hb : P.logBlowup = 2) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (logN : ℕ) (h : logN ≤ 22) :
    ValidConfig P (wideBus 64 : Air F) logN where
  colsInWidth := wide_colsInWidth 64
  preprocessedSize := by simp only [wideBus, wide, Array.size_empty, Nat.mul_zero]
  periodicFits := rfl
  degreeFits := wide_degreeFits 64 logN
  twoAdic := by
    rw [hb]
    change logN + 2 ≤ 24
    omega
  chunksFit := by
    rw [show (wideBus 64 : Air F).logQuotientChunks logN = 1 from
      wide_logQuotientChunks 64 _ (by decide), hb]
    decide
  folds := ha
  finalPolyFits := by rw [hf]; exact Nat.zero_le _
  queries := hq
  blowup := by rw [hb]; decide

/-- The lookup of `wideBus 64` fits its quotient chunks and reads its columns. -/
theorem wideBus_lookupsValid (P : Fri.Params) (hb : P.logBlowup = 2) (logN : ℕ) :
    LookupsValid P (wideBus 64 : Air F) logN
      (Batch.instanceLookups true (wideBus 64) logN) := by
  rw [show Batch.instanceLookups true (wideBus 64 : Air F) logN = [wideBusLookup] from
    wideBus_packedLookups logN]
  refine ⟨by rw [wideBus_logQuotientChunksWith, hb]; decide, fun l hl ↦ ?_⟩
  rw [List.mem_singleton.mp hl]
  unfold Stark.Lookup.Fits
  decide

/-- Three instances of `wideBus 64` exchange tuples of width `4` on one bus. -/
theorem wideBus_busesValid (logN : Fin 3 → ℕ) :
    Batch.BusesValid
      (List.ofFn fun i ↦ Batch.instanceLookups true (wideBus 64 : Air F) (logN i)) := by
  have hls : (List.ofFn fun i ↦ Batch.instanceLookups true (wideBus 64 : Air F) (logN i)) =
      [[wideBusLookup], [wideBusLookup], [wideBusLookup]] := rfl
  have hb : Batch.busLookups [[(wideBusLookup : Lookup F)], [wideBusLookup], [wideBusLookup]] =
      [(0, wideBusLookup), (0, wideBusLookup), (0, wideBusLookup)] := rfl
  rw [hls]
  refine ⟨fun l hl t ht ↦ ?_, fun x hx y hy _ ↦ ?_, fun x hx y hy _ ↦ ?_⟩
  · simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false, or_self] at hl
    subst hl
    revert t
    decide
  all_goals
    rw [hb] at hx hy
    simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx hy
    subst hx hy
    rfl

/-- Three instances of `wideBus 64` on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows over the quintic
extension with `wide5iParams`. -/
def wideBatchSetup : Batch.Setup KoalaBear.Fast.Ext5 where
  params := wide5iParams
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := wideBus_valid wide5iParams rfl (by decide) rfl (by decide) _
    (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

/-- The tallest instance has `2 ^ 20` rows. -/
theorem wideBatch_top : wideBatchSetup.logN wideBatchSetup.top = 20 := by
  have h := wideBatchSetup.logN_le_top ⟨0, by decide⟩
  have h' : ∀ i : Fin 3, (![20, 19, 16] : Fin 3 → ℕ) i ≤ 20 := by decide
  exact le_antisymm (h' wideBatchSetup.top) h

/-- Every instance's domain size has its instance alone, which opens `128 + 6 · 5 = 158` words. -/
theorem wideBatch_groupNumOpened (i : Fin 3) :
    wideBatchSetup.groupNumOpened (wideBatchSetup.logN i + wideBatchSetup.params.logBlowup) - 1 =
      157 := by
  have h (i : Fin 3) : (wideBatchSetup.instanceSetup i).numOpened = 158 := by
    have := wideBus_numOpened (wideBatchSetup.instanceSetup i) rfl rfl
    have hd : Challenge.d KoalaBear.Fast.Ext5 = 5 := rfl
    omega
  have hfilter : (Finset.univ.filter fun j : Fin 3 ↦
      wideBatchSetup.logN j + wide5iParams.logBlowup =
        wideBatchSetup.logN i + wide5iParams.logBlowup) = {i} := by
    fin_cases i <;> decide
  rw [Batch.Setup.groupNumOpened]
  change ∑ j ∈ Finset.univ.filter (fun j : Fin 3 ↦ wideBatchSetup.logN j + wide5iParams.logBlowup =
    wideBatchSetup.logN i + wide5iParams.logBlowup), _ - 1 = 157
  rw [hfilter, Finset.sum_singleton, h]

/-- FRI injects at most the two shorter instances' words, at heights of at least `2 ^ 18`. -/
theorem wideBatch_friHeights :
    wideBatchSetup.friHeights.length ≤ 2 ∧ ∀ m ∈ wideBatchSetup.friHeights, 14 ≤ m := by
  have h : wideBatchSetup.friHeights = [21, 18] := by decide +kernel
  rw [h]
  decide

/-- **128 bits, interactively, for a batch of three tables of mixed heights with lookups.** The
knowledge error of `wideBatchSetup`, FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at
`δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, is at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeError_le :
    Batch.knowledgeError wideBatchSetup (6143 / 16384) (49151 / 131072) ≤ (2 ^ 128)⁻¹ := by
  set D := wideBatchSetup.domainSetup
  have ha : D.params.maxLogArity = 1 := rfl
  have hrate : wideBatchSetup.rate = 1 / 2 ^ 2 := rfl
  have hDrate : D.rate = 1 / 2 ^ 2 := rate_eq D
  have hsize (i : Fin 3) : ((wideBatchSetup.instanceSetup i).size : ℝ) =
      2 ^ (wideBatchSetup.logN i + 2) := by
    rw [Setup.size]
    push_cast
    rfl
  have hlogN (i : Fin 3) : 16 ≤ wideBatchSetup.logN i ∧ wideBatchSetup.logN i ≤ 20 := by
    fin_cases i <;> decide
  have hpow (i : Fin 3) : (2 : ℝ) ^ 18 ≤ 2 ^ (wideBatchSetup.logN i + 2) :=
    pow_le_pow_right₀ (by norm_num) (by have := hlogN i; omega)
  have hT : wideBatchSetup.numInteractions = 3276800 := by decide +kernel
  have hW : wideBatchSetup.lookupWidth = 4 := by decide +kernel
  have h1 := batchKnowledgeError_le_curve wideBatchSetup (6143 / 16384) (49151 / 131072)
    16383996 (2 ^ 22 + 68) 1286615 (by rw [hT, hW])
    (fun i ↦ by
      have h1 := wideBus_numConstraints (wideBatchSetup.instanceSetup i) rfl rfl
      have h2 := wideBus_identityDegree (wideBatchSetup.instanceSetup i) rfl rfl
      have hn : (wideBatchSetup.instanceSetup i).n = 2 ^ wideBatchSetup.logN i := rfl
      have : 2 ^ wideBatchSetup.logN i ≤ 2 ^ 20 := Nat.pow_le_pow_right two_pos (hlogN i).2
      rw [hn] at h2
      omega)
    (fun i ↦ by
      rw [wideBatch_groupNumOpened i, hrate, hsize i]
      have hN : (2 : ℝ) / 2 ^ (wideBatchSetup.logN i + 2) ≤ 2 / 2 ^ 18 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (hpow i)
      have hgap : (6 : ℝ) / 2 ^ 17 ≤ ((49151 / 131072 : NNReal) : ℝ) -
          2 / 2 ^ (wideBatchSetup.logN i + 2) - ((6143 / 16384 : NNReal) : ℝ) := by
        push_cast
        norm_num at hN ⊢
        linarith
      have hT2 : (((49151 / 131072 : NNReal) : ℝ) - 2 / 2 ^ (wideBatchSetup.logN i + 2)) /
          (((49151 / 131072 : NNReal) : ℝ) - 2 / 2 ^ (wideBatchSetup.logN i + 2) -
            ((6143 / 16384 : NNReal) : ℝ)) ≤ 1286615 / 157 := by
        rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hgap)]
        push_cast at hgap ⊢
        nlinarith
      have hT1 : (1 - 1 / 2 ^ 2 - ((6143 / 16384 : NNReal) : ℝ)) /
          (((6143 / 16384 : NNReal) : ℝ) * (1 - 1 / 2 ^ 2 - 2 * ((6143 / 16384 : NNReal) : ℝ))) ≤
          1286615 / 157 := by
        norm_num
      calc ((157 : ℕ) : ℝ) * max _ _ ≤ 157 * (1286615 / 157) := by
            push_cast
            gcongr
            exact max_le hT1 hT2
        _ = 1286615 := by norm_num)
    (fun i ↦ by
      rw [hrate, hsize i]
      have := one_div_le_one_div_of_le (by positivity) (hpow i)
      push_cast
      norm_num at this ⊢
      linarith)
    (by norm_num)
    (fun i ↦ by
      rw [hsize i]
      have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) (by positivity) (hpow i)
      push_cast
      norm_num at this ⊢
      linarith)
    (by rw [hrate]; norm_num)
  have h2 := friErrorWith_le_lossy D ha 14 wideBatchSetup.friHeights
    (fits_friHeights wideBatchSetup) wideBatch_friHeights.2 (6143 / 16384)
    (6143 / 16384 + 1 / 2 ^ 18) (1 / 2 ^ 18) (by rw [hDrate]; norm_num) (by norm_num)
    (lt_add_of_pos_right _ (by positivity)) (by positivity)
  have hq : D.params.numQueries = 190 := rfl
  have hlarge : D.logN + D.params.logBlowup - 14 + wideBatchSetup.friHeights.length ≤ 10 := by
    have := wideBatch_friHeights.1
    change wideBatchSetup.logN wideBatchSetup.top + 2 - 14 + _ ≤ 10
    rw [wideBatch_top]
    omega
  have hfolds : D.logN - D.params.logFinalPolyLen = 20 := by
    change wideBatchSetup.logN wideBatchSetup.top - 0 = 20
    rw [wideBatch_top]
  have hb : D.params.logBlowup = 2 := rfl
  rw [hq, hfolds, hb] at h2
  rw [hb] at hlarge
  have h3 := h2.trans (add_le_add (add_le_add (ENNReal.div_le_div_right
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (show ((D.logN + 2 - 14 + wideBatchSetup.friHeights.length : ℕ) : ℝ) ≤ ((10 : ℕ) : ℝ) by
        exact_mod_cast hlarge) (le_trans (by positivity) (le_max_right _ _)))) _) le_rfl) le_rfl)
  rw [← add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add] at h1
  refine h1.trans ((add_le_add le_rfl h3).trans
    (numbers_curve_le _ (16383996 + (2 ^ 22 + 68)) _ _ _ _ 1286615 _ 982890 _
      (10241 / 16384 + 20 / 2 ^ 18)
      le_rfl le_rfl ?_ le_rfl ?_ (by norm_num) (by norm_num) (by norm_num) ?_))
  · norm_num [LossyMca.lossyBound]
  · norm_num
  · norm_num

/-- Knowledge soundness of `wideBatchSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `49151/131072`: if no three traces, each within `49151/131072` of its instance's
committed trace, satisfy the batch (`wideBus 64` each, the bus balanced), the verifier accepts
with probability at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeSoundness (publicValues : Fin 3 → List F)
    (prover : Batch.Prover wideBatchSetup) :
    (∀ traces ∈ Batch.closeTraces wideBatchSetup (49151 / 131072 : NNReal) prover.trace,
      ¬ wideBatchSetup.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ (2 ^ 128)⁻¹ := by
  intro h
  refine (batchKnowledgeSoundness wideBatchSetup publicValues prover (6143 / 16384)
    (49151 / 131072) ?_ h).trans wideBatch_knowledgeError_le
  rw [show wideBatchSetup.rate = 1 / 2 ^ 2 from rfl]
  norm_num

/-! ### The batch in the random-oracle model -/

/-- The three instances `wideBus 64` on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows over the quintic
extension with `wide5Params` (`160` queries, `20` bits of query grinding). -/
def wideBatch5Setup : Batch.Setup KoalaBear.Fast.Ext5 where
  params := wide5Params
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := wideBus_valid wide5Params rfl (by decide) rfl (by decide) _
    (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

/-- `wideGrindParams` with `18` bits of grinding before the lookup challenges. -/
def wideBusGrindParams : Fri.Params := { wideGrindParams with lookupPowBits := 18 }

/-- The three instances over the quartic extension with `wideBusGrindParams` (`144` queries,
grinding in every round but `α`). -/
def wideBatchGrindSetup : Batch.Setup KoalaBear.Fast.Ext4 where
  params := wideBusGrindParams
  k := 3
  air _ := wideBus 64
  logN := ![20, 19, 16]
  valid i := wideBus_valid wideBusGrindParams rfl (by decide) rfl (by decide) _
    (by fin_cases i <;> decide)
  folds i := by fin_cases i <;> decide
  nonempty := by decide
  lookupsValid _ := wideBus_lookupsValid _ rfl _
  buses := wideBus_busesValid _

section WideBatch
variable {EF : Type} [Challenge F EF]

/-- A batch of `wideBus 64` instances on `2 ^ 20`, `2 ^ 19` and `2 ^ 16` rows. -/
structure WideBatch (S : Batch.Setup EF) : Prop where
  air : ∀ i, S.air i = wideBus 64
  lookups : ∀ i, S.lookups i = [wideBusLookup]
  k : S.k = 3
  logN : ∀ i, S.logN i = (![20, 19, 16] : Fin 3 → ℕ) (Fin.cast k i)
  blowup : S.params.logBlowup = 2

variable (S : Batch.Setup EF) (hS : WideBatch S)
include hS

theorem WideBatch.logN_le (i : Fin S.k) : 16 ≤ S.logN i ∧ S.logN i ≤ 20 := by
  rw [hS.logN]
  generalize Fin.cast hS.k i = j
  fin_cases j <;> decide

theorem WideBatch.top : S.logN S.top = 20 := by
  refine le_antisymm (WideBatch.logN_le S hS S.top).2 ?_
  have h := S.logN_le_top (Fin.cast hS.k.symm ⟨0, by decide⟩)
  rw [hS.logN] at h
  simpa using h

/-- Every instance's domain size has its instance alone, which opens `128 + 6 d` words. -/
theorem WideBatch.groupNumOpened (i : Fin S.k) :
    S.groupNumOpened (S.logN i + S.params.logBlowup) - 1 = 127 + 6 * Challenge.d EF := by
  have hfilter : (Finset.univ.filter fun j : Fin S.k ↦
      S.logN j + S.params.logBlowup = S.logN i + S.params.logBlowup) = {i} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Nat.add_right_cancel_iff]
    constructor
    · intro h
      rw [hS.logN, hS.logN] at h
      have hj := Fin.cast_injective hS.k (a₁ := j) (a₂ := i)
      refine hj ?_
      generalize Fin.cast hS.k j = a at h
      generalize Fin.cast hS.k i = b at h
      fin_cases a <;> fin_cases b <;> first | rfl | (simp at h)
    · rintro rfl
      rfl
  rw [Batch.Setup.groupNumOpened, hfilter, Finset.sum_singleton]
  exact wideBus_numOpened (S.instanceSetup i) (hS.lookups i) (hS.air i)

/-- FRI injects the shorter instances' words at heights of at least `2 ^ 18`. -/
theorem WideBatch.friHeights_ge (m : ℕ) (hm : m ∈ S.friHeights) : 18 ≤ m := by
  obtain ⟨i, rfl, -⟩ := (Sound.mem_friHeights S m).mp hm
  rw [hS.blowup]
  have := (WideBatch.logN_le S hS i).1
  omega

theorem WideBatch.integers_le (i : Fin S.k) :
    (S.instanceSetup i).numConstraints - 1 + ((S.instanceSetup i).identityDegree +
      (S.instanceSetup i).n) ≤ 4 * 2 ^ 20 + 68 := by
  have h1 := wideBus_numConstraints (S.instanceSetup i) (hS.lookups i) (hS.air i)
  have h2 := wideBus_identityDegree (S.instanceSetup i) (hS.lookups i) (hS.air i)
  have : (S.instanceSetup i).n ≤ 2 ^ 20 :=
    Nat.pow_le_pow_right two_pos (WideBatch.logN_le S hS i).2
  omega

end WideBatch

/-- **128 bits per oracle answer for a batch of three tables of mixed heights with lookups.**
Every round error of `wideBatch5Setup`, FRI at `δ = 3/8 - 2 ^ (-16)` and the extractor at
`δ' = 3/8 - 2 ^ (-18)`, is at most `2 ^ (-128)`. -/
theorem wideBatch5_roundError_le :
    Batch.roundError wideBatch5Setup (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ)) ≤
      (2 ^ 128)⁻¹ := by
  set S := wideBatch5Setup
  have hS : WideBatch S := ⟨fun _ ↦ rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl⟩
  have hδ := coe_three_eighths_sub (-16) 16 rfl (by norm_num)
  have hδ' := coe_three_eighths_sub (-18) 18 rfl (by norm_num)
  have hrate : S.rate = 1 / 2 ^ 2 := rfl
  have hsize (i : Fin S.k) : ((S.instanceSetup i).size : ℝ) = 2 ^ (S.logN i + 2) := by
    rw [Setup.size]
    push_cast
    rfl
  have hpow (i : Fin S.k) : (2 : ℝ) ^ 18 ≤ 2 ^ (S.logN i + 2) :=
    pow_le_pow_right₀ (by norm_num) (by have := (WideBatch.logN_le S hS i).1; omega)
  have hinv (i : Fin S.k) : (1 : ℝ) / 2 ^ (S.logN i + 2) ≤ 1 / 2 ^ 18 :=
    one_div_le_one_div_of_le (by positivity) (hpow i)
  have hc (i : Fin S.k) : (S.instanceSetup i).numConstraints - 1 = 67 := by
    rw [wideBus_numConstraints (S.instanceSetup i) (hS.lookups i) (hS.air i)]
  have h := Batch.batchRoundError_le S rfl 16
    (fun m hm ↦ le_trans (by norm_num) (WideBatch.friHeights_ge S hS m hm))
    (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ)) (1 / 2 ^ 26) 16383996 67 (4 * 2 ^ 20 + 1)
    (157 * 98304) (by rw [show S.numInteractions = 3276800 by decide +kernel,
      show S.lookupWidth = 4 by decide +kernel])
    (fun i ↦ (hc i).le)
    (fun i ↦ by have := WideBatch.integers_le S hS i; rw [hc i] at this; omega)
    (fun i ↦ by
      rw [WideBatch.groupNumOpened S hS i, hrate, hsize i, hδ, hδ']
      have hd : Challenge.d KoalaBear.Fast.Ext5 = 5 := rfl
      rw [hd]
      have hN := hinv i
      have hgap : (1 : ℝ) / 2 ^ 18 ≤ ((3 : ℝ) / 8 - 1 / 2 ^ 18) - 2 / 2 ^ (S.logN i + 2) -
          (3 / 8 - 1 / 2 ^ 16) := by
        have : (2 : ℝ) / 2 ^ (S.logN i + 2) = 2 * (1 / 2 ^ (S.logN i + 2)) := by ring
        rw [this]
        norm_num at hN ⊢
        linarith
      have hT2 : (((3 : ℝ) / 8 - 1 / 2 ^ 18) - 2 / 2 ^ (S.logN i + 2)) /
          (((3 : ℝ) / 8 - 1 / 2 ^ 18) - 2 / 2 ^ (S.logN i + 2) - (3 / 8 - 1 / 2 ^ 16)) ≤ 98304 := by
        have hpos : (0 : ℝ) < ((3 : ℝ) / 8 - 1 / 2 ^ 18) - 2 / 2 ^ (S.logN i + 2) -
            (3 / 8 - 1 / 2 ^ 16) := lt_of_lt_of_le (by norm_num) hgap
        rw [div_le_iff₀ hpos]
        have : (0 : ℝ) ≤ 2 / 2 ^ (S.logN i + 2) := by positivity
        nlinarith
      have hT1 : (1 - 1 / 2 ^ 2 - (3 / 8 - 1 / 2 ^ 16 : ℝ)) /
          ((3 / 8 - 1 / 2 ^ 16) * (1 - 1 / 2 ^ 2 - 2 * (3 / 8 - 1 / 2 ^ 16))) ≤ 98304 := by
        norm_num
      rw [show ((127 + 6 * 5 : ℕ) : ℝ) = 157 by norm_num]
      exact mul_le_mul_of_nonneg_left (max_le hT1 hT2) (by norm_num))
    (fun i ↦ by rw [hδ, hrate, hsize i]; have := hinv i; norm_num at this ⊢; linarith)
    (by rw [hδ, hrate]; norm_num) (by rw [← NNReal.coe_pos, hδ]; norm_num)
    (fun i ↦ by
      rw [hδ, hδ', hsize i]
      have hN := hinv i
      have : (2 : ℝ) / 2 ^ (S.logN i + 2) = 2 * (1 / 2 ^ (S.logN i + 2)) := by ring
      rw [this]
      norm_num at hN ⊢
      linarith)
    (by rw [hδ', hrate]; norm_num) (by positivity)
  have hlook : S.params.lookupPowBits = 0 := rfl
  have hood : S.params.oodPowBits = 0 := rfl
  have hbatch : S.params.batchPowBits = 0 := rfl
  have hcommit : S.params.commitPowBits = 0 := rfl
  have hquery : S.params.queryPowBits = 20 := rfl
  have hq : S.params.numQueries = 160 := rfl
  have hfolds : S.logN S.top - S.params.logFinalPolyLen = 20 := by
    rw [WideBatch.top S hS]
    rfl
  have hb : S.params.logBlowup = 2 := rfl
  rw [hlook, hood, hbatch, hcommit, hquery, hq, hfolds, hb] at h
  simp only [powFraction_zero, one_mul] at h
  refine h.trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
  · refine nat_div_card_le _ ?_
    norm_num
  · refine nat_div_card_le _ ?_
    norm_num
  · refine nat_div_card_le _ ?_
    norm_num
  · refine ofReal_div_card_le _ ?_
    norm_num
  · refine ofReal_div_card_le _ ?_
    simp only [LossyMca.lossyBound]
    rw [NNReal.coe_add, hδ]
    norm_num
  · refine powFraction_mul_le _ _ _ (by rw [hδ]; norm_num) ?_
    rw [hδ, KoalaBear.card_eq]
    norm_num

/-- **117 bits per oracle answer for a batch of three tables of mixed heights over the quartic
extension.** Every round error of `wideBatchGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-10)` and the
extractor at `δ' = 3/8 - 2 ^ (-11)`, is at most `2 ^ (-117)`. -/
theorem wideBatchGrind_roundError_le :
    Batch.roundError wideBatchGrindSetup (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ)) ≤
      (2 ^ 117)⁻¹ := by
  set S := wideBatchGrindSetup
  have hS : WideBatch S := ⟨fun _ ↦ rfl, fun _ ↦ rfl, rfl, fun _ ↦ rfl, rfl⟩
  have hδ := coe_three_eighths_sub (-10) 10 rfl (by norm_num)
  have hδ' := coe_three_eighths_sub (-11) 11 rfl (by norm_num)
  have hrate : S.rate = 1 / 2 ^ 2 := rfl
  have hsize (i : Fin S.k) : ((S.instanceSetup i).size : ℝ) = 2 ^ (S.logN i + 2) := by
    rw [Setup.size]
    push_cast
    rfl
  have hpow (i : Fin S.k) : (2 : ℝ) ^ 18 ≤ 2 ^ (S.logN i + 2) :=
    pow_le_pow_right₀ (by norm_num) (by have := (WideBatch.logN_le S hS i).1; omega)
  have hinv (i : Fin S.k) : (1 : ℝ) / 2 ^ (S.logN i + 2) ≤ 1 / 2 ^ 18 :=
    one_div_le_one_div_of_le (by positivity) (hpow i)
  have hc (i : Fin S.k) : (S.instanceSetup i).numConstraints - 1 = 67 := by
    rw [wideBus_numConstraints (S.instanceSetup i) (hS.lookups i) (hS.air i)]
  have h := Batch.batchRoundError_le S rfl 10
    (fun m hm ↦ le_trans (by norm_num) (WideBatch.friHeights_ge S hS m hm))
    (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ)) (1 / 2 ^ 15) 16383996 67 (4 * 2 ^ 20 + 1)
    (151 * 781) (by rw [show S.numInteractions = 3276800 by decide +kernel,
      show S.lookupWidth = 4 by decide +kernel])
    (fun i ↦ (hc i).le)
    (fun i ↦ by have := WideBatch.integers_le S hS i; rw [hc i] at this; omega)
    (fun i ↦ by
      rw [WideBatch.groupNumOpened S hS i, hrate, hsize i, hδ, hδ']
      have hd : Challenge.d KoalaBear.Fast.Ext4 = 4 := rfl
      rw [hd]
      have hN := hinv i
      have hgap : (63 : ℝ) / 2 ^ 17 ≤ ((3 : ℝ) / 8 - 1 / 2 ^ 11) - 2 / 2 ^ (S.logN i + 2) -
          (3 / 8 - 1 / 2 ^ 10) := by
        have : (2 : ℝ) / 2 ^ (S.logN i + 2) = 2 * (1 / 2 ^ (S.logN i + 2)) := by ring
        rw [this]
        norm_num at hN ⊢
        linarith
      have hT2 : (((3 : ℝ) / 8 - 1 / 2 ^ 11) - 2 / 2 ^ (S.logN i + 2)) /
          (((3 : ℝ) / 8 - 1 / 2 ^ 11) - 2 / 2 ^ (S.logN i + 2) - (3 / 8 - 1 / 2 ^ 10)) ≤ 781 := by
        have hpos : (0 : ℝ) < ((3 : ℝ) / 8 - 1 / 2 ^ 11) - 2 / 2 ^ (S.logN i + 2) -
            (3 / 8 - 1 / 2 ^ 10) := lt_of_lt_of_le (by norm_num) hgap
        rw [div_le_iff₀ hpos]
        have : (0 : ℝ) ≤ 2 / 2 ^ (S.logN i + 2) := by positivity
        nlinarith
      have hT1 : (1 - 1 / 2 ^ 2 - (3 / 8 - 1 / 2 ^ 10 : ℝ)) /
          ((3 / 8 - 1 / 2 ^ 10) * (1 - 1 / 2 ^ 2 - 2 * (3 / 8 - 1 / 2 ^ 10))) ≤ 781 := by
        norm_num
      rw [show ((127 + 6 * 4 : ℕ) : ℝ) = 151 by norm_num]
      exact mul_le_mul_of_nonneg_left (max_le hT1 hT2) (by norm_num))
    (fun i ↦ by rw [hδ, hrate, hsize i]; have := hinv i; norm_num at this ⊢; linarith)
    (by rw [hδ, hrate]; norm_num) (by rw [← NNReal.coe_pos, hδ]; norm_num)
    (fun i ↦ by
      rw [hδ, hδ', hsize i]
      have hN := hinv i
      have : (2 : ℝ) / 2 ^ (S.logN i + 2) = 2 * (1 / 2 ^ (S.logN i + 2)) := by ring
      rw [this]
      norm_num at hN ⊢
      linarith)
    (by rw [hδ', hrate]; norm_num) (by positivity)
  have hlook : S.params.lookupPowBits = 18 := rfl
  have hood : S.params.oodPowBits = 20 := rfl
  have hbatch : S.params.batchPowBits = 12 := rfl
  have hcommit : S.params.commitPowBits = 8 := rfl
  have hquery : S.params.queryPowBits = 20 := rfl
  have hq : S.params.numQueries = 144 := rfl
  have hfolds : S.logN S.top - S.params.logFinalPolyLen = 20 := by
    rw [WideBatch.top S hS]
    rfl
  have hb : S.params.logBlowup = 2 := rfl
  rw [hlook, hood, hbatch, hcommit, hquery, hq, hfolds, hb] at h
  refine h.trans (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ (max_le ?_ ?_)))))
  · rw [← ENNReal.ofReal_natCast]
    refine powFraction_mul_div_card_le _ _ ?_
    rw [KoalaBear.card_eq]
    norm_num
  · refine nat_div_card_le _ ?_
    norm_num
  · rw [← ENNReal.ofReal_natCast]
    refine powFraction_mul_div_card_le _ _ ?_
    rw [KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_div_card_le _ _ ?_
    rw [KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_div_card_le _ _ ?_
    simp only [LossyMca.lossyBound]
    rw [NNReal.coe_add, hδ, KoalaBear.card_eq]
    norm_num
  · refine powFraction_mul_le _ _ _ (by rw [hδ]; norm_num) ?_
    rw [hδ, KoalaBear.card_eq]
    norm_num

theorem wideBatch5Setup_verifierQueries : wideBatch5Setup.verifierQueries = 99669 := by
  decide +kernel

theorem wideBatchGrindSetup_verifierQueries : wideBatchGrindSetup.verifierQueries = 89692 := by
  decide +kernel

/-- **128 bits per oracle call for a batch of three tables of mixed heights with lookups.** A
prover for `wideBatch5Setup` making at most `Q` oracle calls gets a proof accepted while no tuple of
traces close to the ones it committed to satisfies the batch with probability at most `q · 2 ^
(-128) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideBatch5_knowledgeSoundness_ro (publicValues : Fin wideBatch5Setup.k → List F) (Q : Nat)
    (prover : Batch.NIProver wideBatch5Setup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run wideBatch5Setup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn wideBatch5Setup.logN ∧
        ∀ traces ∈ Batch.closeTraces wideBatch5Setup (3 / 8 - 2 ^ (-18 : ℤ) : NNReal)
            (Batch.committedTraces wideBatch5Setup log proof),
          ¬ wideBatch5Setup.Satisfied traces publicValues] ≤
      (Q + wideBatch5Setup.verifierQueries) * (2 ^ 128)⁻¹ +
        hashError F (Q + wideBatch5Setup.verifierQueries) := by
  refine (Batch.batchKnowledgeSoundness_ro wideBatch5Setup publicValues (3 / 8 - 2 ^ (-16 : ℤ))
    (3 / 8 - 2 ^ (-18 : ℤ)) ?_ Q prover hQ).trans ?_
  · rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num),
      show wideBatch5Setup.rate = 1 / 2 ^ 2 from rfl]
    norm_num
  · gcongr
    exact wideBatch5_roundError_le

/-- **117 bits per oracle call for a batch of three tables with lookups over the quartic
extension.** A prover
for `wideBatchGrindSetup` making at most `Q` oracle calls gets a proof accepted while no tuple of
traces close to the ones it committed to satisfies the batch with probability at most
`q · 2 ^ (-117) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideBatchGrind_knowledgeSoundness_ro (publicValues : Fin wideBatchGrindSetup.k → List F)
    (Q : Nat) (prover : Batch.NIProver wideBatchGrindSetup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run wideBatchGrindSetup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn wideBatchGrindSetup.logN ∧
        ∀ traces ∈ Batch.closeTraces wideBatchGrindSetup (3 / 8 - 2 ^ (-11 : ℤ) : NNReal)
            (Batch.committedTraces wideBatchGrindSetup log proof),
          ¬ wideBatchGrindSetup.Satisfied traces publicValues] ≤
      (Q + wideBatchGrindSetup.verifierQueries) * (2 ^ 117)⁻¹ +
        hashError F (Q + wideBatchGrindSetup.verifierQueries) := by
  refine (Batch.batchKnowledgeSoundness_ro wideBatchGrindSetup publicValues (3 / 8 - 2 ^ (-10 : ℤ))
    (3 / 8 - 2 ^ (-11 : ℤ)) ?_ Q prover hQ).trans ?_
  · rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num),
      show wideBatchGrindSetup.rate = 1 / 2 ^ 2 from rfl]
    norm_num
  · gcongr
    exact wideBatchGrind_roundError_le

end CompStark.Iop
