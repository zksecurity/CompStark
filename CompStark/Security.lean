/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Soundness
public import CompStark.KoalaBear.Challenge
public import CompStark.NonInteractive
public import CompStark.Complete.Quotient
public import CompStark.BatchNonInteractive
public import CompStark.Sound.Calculator

/-! # Concrete security: 100 bits over the quartic extension, 117 with grinding, 128 over quintic

The security calculator (`CompStark/SecurityCalculator.lean`) bounds every error term of a setup
by a rational number computed from the setup's numbers, for a base field of `p` elements, at the
radii and parameters of an `Analysis`: FRI's proximity `δ`, the extractor's `δ'`, a proximity loss
and a fold threshold `2 ^ t`. Whether the bound reaches `bits` bits, `S.Secure p A bits` (or
`S.SecureRo p A bits` per oracle answer), is decidable, and `decide +kernel` checks it, evaluating
the AIR's constraints, widths and lookups in the kernel. The theorems below turn a checked
condition into the soundness statements: `knowledgeSoundness_of_secure`,
`knowledgeSoundness_ro_of_secureRo`, `batchKnowledgeSoundness_of_secure` and
`Batch.batchKnowledgeSoundness_ro_of_secureRo`, and their error bounds. `knowledgeErrorReport` and
`roundErrorReport` print the bits of each term (`#eval`).

All configurations below fold FRI by arity `2` down to a constant, and pick FRI's radius `δ` and
the extractor's `δ'` below the unique-decoding radius `(1 - rate) / 2`, where the candidate lists
have at most one element (`listSize_le_one`). Every term but the queries is then over `|𝕂|`:
`p ^ 4 ≈ 2 ^ 123.95` for `KoalaBear.Fast.Ext4`, which caps every configuration below
`2 ^ (-123.95)` (constraint folding alone is about `2 ^ (-117.98)`), and `p ^ 5 ≈ 2 ^ 154.94` for
`KoalaBear.Fast.Ext5`. In the random-oracle model, grinding divides every round's error after `α`
by about `2 ^ bits`; only constraint folding, which Plonky3 does not grind, stays an integer over
`|𝕂|`, so the quartic extension is capped near `2 ^ (-117.98)` instead.

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
the largest round error (`roundError`, `CompStark/NonInteractiveError.lean`), with FRI at
`δ = 3/8 - 2 ^ (-16)`, the extractor at `δ' = 3/8 - 2 ^ (-18)`, `loss = 2 ^ (-22)`,
`δ_int = δ + loss` and `t = 16`:

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
`δ' = 3/8 - 2 ^ (-17)`, `loss = 2 ^ (-18)` and `t = 14`:

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
(`Batch.roundError`, `CompStark/BatchNonInteractiveError.lean`), the lookup challenges with the
lookup grinding; a fold that injects a shorter instance's word costs twice the lossy bound. For
the same three instances, with the extractor at `δ'` and every domain of at least `2 ^ 18` points,
so that `δ < δ' - 2/N` on each:

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

/-! ### The calculator's theorems -/

section Calculator
variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF] {p : ℕ}

/-- **The calculator's knowledge error.** If the calculator certifies `bits` bits for `S` at the
analysis `A` (`S.Secure p A bits`, for `|F| = p`), the knowledge error with FRI at `A.δ` and the
extractor at `A.δ'` is at most `2 ^ (-bits)`. -/
theorem knowledgeError_le_of_secure {lookups : List (Lookup F)} (S : Setup EF lookups)
    (hp : Nat.card F = p) (A : Analysis) {bits : ℕ} (h : S.Secure p A bits) (δ δ' : NNReal)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    knowledgeError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (knowledgeError_le_bound S A hp h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Knowledge soundness from the calculator.** If the calculator certifies `bits` bits for `S`
at `A`, and no trace within `δ' = A.δ'` of the prover's committed trace satisfies the AIR, the
verifier accepts with probability at most `2 ^ (-bits)`. -/
theorem knowledgeSoundness_of_secure (S : Setup EF) (hp : Nat.card F = p) (A : Analysis)
    {bits : ℕ} (h : S.Secure p A bits) (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ')
    (publicValues : List F) (prover : Prover S) :
    (∀ trace ∈ closeTraces S δ' prover.trace, ¬ S.air.Satisfied S.logN trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ bits)⁻¹ := fun hfar ↦
  (knowledgeSoundness S publicValues prover _ δ' (lt_one_sub_rate S A h.1.2.1 δ' hδ')
    hfar).trans (knowledgeError_le_of_secure S hp A h _ δ' (coe_toNNReal_δ A h.1.2.1) hδ')

/-- **The calculator's round error.** If the calculator certifies `bits` bits per oracle answer
for `S` at `A` (`S.SecureRo p A bits`), the round error with FRI at `A.δ` and the extractor at
`A.δ'` is at most `2 ^ (-bits)`. -/
theorem roundError_le_of_secureRo (S : Setup EF) (hp : Nat.card F = p) (A : Analysis)
    {bits : ℕ} (h : S.SecureRo p A bits) (δ δ' : NNReal) (hδ : (δ : ℝ) = A.δ)
    (hδ' : (δ' : ℝ) = A.δ') :
    roundError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (roundError_le_bound A S hp h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Knowledge soundness in the random-oracle model from the calculator.** If the calculator
certifies `bits` bits per oracle answer for `S` at `A`, a prover making at most `Q` oracle calls
gets a proof accepted while no trace within `δ' = A.δ'` of the one it committed to satisfies the
AIR with probability at most `q · 2 ^ (-bits) + hashError q`, `q = Q + verifierQueries`. -/
theorem knowledgeSoundness_ro_of_secureRo (S : Setup EF) (hp : Nat.card F = p) (A : Analysis)
    {bits : ℕ} (h : S.SecureRo p A bits) (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ')
    (publicValues : List F) (Q : Nat) (prover : NIProver S) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits = S.logN ∧
        ∀ trace ∈ closeTraces S δ' (committedTrace S log proof),
          ¬ S.air.Satisfied S.logN trace publicValues] ≤
      (Q + S.verifierQueries) * (2 ^ bits)⁻¹ + hashError F (Q + S.verifierQueries) := by
  refine (knowledgeSoundness_ro S publicValues (Real.toNNReal A.δ) δ'
    (lt_one_sub_rate S A h.1.2.1 δ' hδ') Q prover hQ).trans ?_
  gcongr
  exact roundError_le_of_secureRo S hp A h _ δ' (coe_toNNReal_δ A h.1.2.1) hδ'

/-- **The calculator's batch knowledge error.** If the calculator certifies `bits` bits for the
batch `S` at `A`, its knowledge error with FRI at `A.δ` and the extractor at `A.δ'` is at most
`2 ^ (-bits)`. -/
theorem Batch.knowledgeError_le_of_secure {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) (A : Analysis) {bits : ℕ} (h : S.Secure p A bits) (δ δ' : NNReal)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.knowledgeError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (batchKnowledgeError_le_bound S A hp h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Batch knowledge soundness from the calculator.** If the calculator certifies `bits` bits
for the batch `S` at `A`, and no tuple of traces, each within `δ' = A.δ'` of its instance's
committed trace, satisfies the batch, the verifier accepts with probability at most
`2 ^ (-bits)`. -/
theorem batchKnowledgeSoundness_of_secure {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) (A : Analysis) {bits : ℕ} (h : S.Secure p A bits) (δ' : NNReal)
    (hδ' : (δ' : ℝ) = A.δ') (publicValues : Fin S.k → List F) (prover : Batch.Prover S) :
    (∀ traces ∈ Batch.closeTraces S δ' prover.trace, ¬ S.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ (2 ^ bits)⁻¹ := fun hfar ↦
  (batchKnowledgeSoundness S publicValues prover _ δ' (batch_lt_one_sub_rate S A h.1 δ' hδ')
    hfar).trans (Batch.knowledgeError_le_of_secure S hp A h _ δ' (coe_toNNReal_δ A h.1.2.1) hδ')

/-- **The calculator's batch round error.** If the calculator certifies `bits` bits per oracle
answer for the batch `S` at `A`, its round error with FRI at `A.δ` and the extractor at `A.δ'` is
at most `2 ^ (-bits)`. -/
theorem Batch.roundError_le_of_secureRo {withLookups : Bool} (S : Batch.Setup EF withLookups)
    (hp : Nat.card F = p) (A : Analysis) {bits : ℕ} (h : S.SecureRo p A bits) (δ δ' : NNReal)
    (hδ : (δ : ℝ) = A.δ) (hδ' : (δ' : ℝ) = A.δ') :
    Batch.roundError S δ δ' ≤ (2 ^ bits)⁻¹ :=
  (batchRoundError_le_bound S A hp h.1 δ δ' hδ hδ').trans (ofReal_le_inv_two_pow h.2)

/-- **Batch knowledge soundness in the random-oracle model from the calculator.** If the
calculator certifies `bits` bits per oracle answer for the batch `S` at `A`, a prover making at
most `Q` oracle calls gets a proof accepted while no tuple of traces within `δ' = A.δ'` of the
ones it committed to satisfies the batch with probability at most `q · 2 ^ (-bits) + hashError q`,
`q = Q + verifierQueries`. -/
theorem Batch.batchKnowledgeSoundness_ro_of_secureRo (S : Batch.Setup EF) (hp : Nat.card F = p)
    (A : Analysis) {bits : ℕ} (h : S.SecureRo p A bits) (δ' : NNReal) (hδ' : (δ' : ℝ) = A.δ')
    (publicValues : Fin S.k → List F) (Q : Nat) (prover : Batch.NIProver S)
    (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run S publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn S.logN ∧
        ∀ traces ∈ Batch.closeTraces S δ' (Batch.committedTraces S log proof),
          ¬ S.Satisfied traces publicValues] ≤
      (Q + S.verifierQueries) * (2 ^ bits)⁻¹ + hashError F (Q + S.verifierQueries) := by
  refine (Batch.batchKnowledgeSoundness_ro S publicValues (Real.toNNReal A.δ) δ'
    (batch_lt_one_sub_rate S A h.1 δ' hδ') Q prover hQ).trans ?_
  gcongr
  exact Batch.roundError_le_of_secureRo S hp A h _ δ' (coe_toNNReal_δ A h.1.2.1) hδ'

end Calculator

/-! ### Examples -/

local notation "F" => Montgomery.Native32.FastField _root_.KoalaBear.fieldSize

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

/-- FRI at `δ = 1919/4096 = 15/32 - 2 ^ (-12)`, the extractor at
`δ' = 7679/16384 = 15/32 - 2 ^ (-14)`, `loss = 2 ^ (-20)` and `t = 14`. -/
def fibonacciAnalysis : Analysis := ⟨1919 / 4096, 7679 / 16384, 1 / 2 ^ 20, 14⟩

theorem fibonacci_secure : fibonacciSetup.Secure 2130706433 fibonacciAnalysis 100 := by
  decide +kernel

/-- **100 bits.** The knowledge error of `fibonacciSetup`, FRI at
`δ = 1919/4096 = 15/32 - 2 ^ (-12)` and the extractor at `δ' = 7679/16384 = 15/32 - 2 ^ (-14)`, is
at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeError_le :
    knowledgeError fibonacciSetup (1919 / 4096) (7679 / 16384) ≤ (2 ^ 100)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq _ fibonacci_secure _ _
    (by norm_num [fibonacciAnalysis]) (by norm_num [fibonacciAnalysis])

/-- Knowledge soundness of `fibonacciSetup` with error `2 ^ (-100)`, FRI at `1919/4096` and the
extractor at `7679/16384`: if no trace within `7679/16384` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem fibonacci_knowledgeSoundness (publicValues : List F) (prover : Prover fibonacciSetup) :
    (∀ trace ∈ closeTraces fibonacciSetup (7679 / 16384 : NNReal) prover.trace,
      ¬ fibonacci.Satisfied 10 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq _ fibonacci_secure _
    (by norm_num [fibonacciAnalysis]) publicValues prover

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

/-- `wide w` on `2 ^ logN` rows with FRI parameters of blowup `4` and a constant final
polynomial, for `logN ≤ 22`. -/
theorem wide_valid (P : Fri.Params) (hb : P.logBlowup = 2) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (w : ℕ) (hw : 0 < w) (logN : ℕ)
    (h : logN ≤ 22) : ValidConfig P (wide w : Air F) logN where
  colsInWidth := wide_colsInWidth w
  preprocessedSize := by simp only [wide, Array.size_empty, Nat.mul_zero]
  periodicFits := rfl
  degreeFits := wide_degreeFits w logN
  twoAdic := by
    rw [hb]
    change logN + 2 ≤ 24
    omega
  chunksFit := by
    rw [wide_logQuotientChunks w _ hw, hb]
    decide
  folds := ha
  finalPolyFits := by rw [hf]; exact Nat.zero_le _
  queries := hq
  blowup := by rw [hb]; decide

/-- `wide 64` on `2 ^ 20` rows with `wideParams`. -/
def wideSetup : Setup KoalaBear.Fast.Ext4 where
  params := wideParams
  air := wide 64
  logN := 20
  valid := wide_valid wideParams rfl (by decide) rfl (by decide) 64 (by decide) 20
    (by decide)
  folds := by decide

/-- FRI at `δ = 1535/4096 = 3/8 - 2 ^ (-12)`, the extractor at
`δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, `loss = 2 ^ (-17)` and `t = 16`. -/
def wideAnalysis : Analysis := ⟨1535 / 4096, 24575 / 65536, 1 / 2 ^ 17, 16⟩

theorem wide_secure : wideSetup.Secure 2130706433 wideAnalysis 100 := by
  decide +kernel

/-- **100 bits on `2 ^ 20` rows.** The knowledge error of `wideSetup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is at
most `2 ^ (-100)`. -/
theorem wide_knowledgeError_le :
    knowledgeError wideSetup (1535 / 4096) (24575 / 65536) ≤ (2 ^ 100)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq _ wide_secure _ _
    (by norm_num [wideAnalysis]) (by norm_num [wideAnalysis])

/-- Knowledge soundness of `wideSetup` with error `2 ^ (-100)`, FRI at `1535/4096` and the
extractor at `24575/65536`: if no trace within `24575/65536` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem wide_knowledgeSoundness (publicValues : List F) (prover : Prover wideSetup) :
    (∀ trace ∈ closeTraces wideSetup (24575 / 65536 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 20 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq _ wide_secure _
    (by norm_num [wideAnalysis]) publicValues prover

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
  valid := wide_valid wide21Params rfl (by decide) rfl (by decide) 64 (by decide) 21
    (by decide)
  folds := by decide

theorem wide21_secure : wide21Setup.Secure 2130706433 wideAnalysis 100 := by
  decide +kernel

/-- **100 bits on `2 ^ 21` rows.** The knowledge error of `wide21Setup`, FRI at
`δ = 1535/4096 = 3/8 - 2 ^ (-12)` and the extractor at `δ' = 24575/65536 = 3/8 - 2 ^ (-16)`, is at
most `2 ^ (-100)`. -/
theorem wide21_knowledgeError_le :
    knowledgeError wide21Setup (1535 / 4096) (24575 / 65536) ≤ (2 ^ 100)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq _ wide21_secure _ _
    (by norm_num [wideAnalysis]) (by norm_num [wideAnalysis])

/-- Knowledge soundness of `wide21Setup` with error `2 ^ (-100)`, FRI at `1535/4096` and the
extractor at `24575/65536`: if no trace within `24575/65536` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-100)`. -/
theorem wide21_knowledgeSoundness (publicValues : List F) (prover : Prover wide21Setup) :
    (∀ trace ∈ closeTraces wide21Setup (24575 / 65536 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 100)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq _ wide21_secure _
    (by norm_num [wideAnalysis]) publicValues prover

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
  valid := wide_valid sp1Params rfl (by decide) rfl (by decide) 64 (by decide) 21
    (by decide)
  folds := by decide

/-- The verifier's oracle calls on a proof for `wideSp1Setup`: `15 + 5 · 21 + 124 · 553`. -/
theorem wideSp1Setup_verifierQueries : wideSp1Setup.verifierQueries = 68692 := by decide +kernel

/-- FRI at `δ = 3/8 - 2 ^ (-16)`, the extractor at `δ' = 3/8 - 2 ^ (-18)`, `loss = 2 ^ (-22)`
and `t = 16`. -/
def wideSp1Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 16, 3 / 8 - 1 / 2 ^ 18, 1 / 2 ^ 22, 16⟩

theorem wideSp1_secureRo : wideSp1Setup.SecureRo 2130706433 wideSp1Analysis 100 := by
  decide +kernel

/-- **100 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wideSp1Setup`, FRI at
`δ = 3/8 - 2 ^ (-16)` and the extractor at `δ' = 3/8 - 2 ^ (-18)`, is at most `2 ^ (-100)`. -/
theorem wideSp1_roundError_le :
    roundError wideSp1Setup (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ)) ≤ (2 ^ 100)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq _ wideSp1_secureRo _ _
    (by rw [coe_three_eighths_sub (-16) 16 rfl (by norm_num)]; norm_num [wideSp1Analysis])
    (by rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num)]; norm_num [wideSp1Analysis])

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
        hashError F (Q + wideSp1Setup.verifierQueries) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq _ wideSp1_secureRo _
    (by rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num)]; norm_num [wideSp1Analysis])
    publicValues Q prover hQ

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
  valid := wide_valid wideGrindParams rfl (by decide) rfl (by decide) 64 (by decide) 21
    (by decide)
  folds := by decide

/-- The verifier's oracle calls on a proof for `wideGrindSetup`: `15 + 5 · 21 + 144 · 553`. -/
theorem wideGrindSetup_verifierQueries : wideGrindSetup.verifierQueries = 79752 := by
  decide +kernel

/-- FRI at `δ = 3/8 - 2 ^ (-10)`, the extractor at `δ' = 3/8 - 2 ^ (-11)`, `loss = 2 ^ (-15)`
and `t = 10`. -/
def wideGrindAnalysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 10, 3 / 8 - 1 / 2 ^ 11, 1 / 2 ^ 15, 10⟩

theorem wideGrind_secureRo : wideGrindSetup.SecureRo 2130706433 wideGrindAnalysis 117 := by
  decide +kernel

/-- **117 bits per oracle answer on `2 ^ 21` rows over the quartic extension.** Every round error
of `wideGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-10)` and the extractor at `δ' = 3/8 - 2 ^ (-11)`, is
at most `2 ^ (-117)`. -/
theorem wideGrind_roundError_le :
    roundError wideGrindSetup (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ)) ≤ (2 ^ 117)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq _ wideGrind_secureRo _ _
    (by rw [coe_three_eighths_sub (-10) 10 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    (by rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num)]; norm_num [wideGrindAnalysis])

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
        hashError F (Q + wideGrindSetup.verifierQueries) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq _ wideGrind_secureRo _
    (by rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    publicValues Q prover hQ

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
  valid := wide_valid wide5Params rfl (by decide) rfl (by decide) 64 (by decide) 21
    (by decide)
  folds := by decide

/-- The verifier's oracle calls on a proof for `wide5Setup`: `18 + 6 · 21 + 160 · 553`. -/
theorem wide5Setup_verifierQueries : wide5Setup.verifierQueries = 88624 := by decide +kernel

/-- FRI at `δ = 3/8 - 2 ^ (-18)`, the extractor at `δ' = 3/8 - 2 ^ (-20)`, `loss = 2 ^ (-26)`
and `t = 18`. -/
def wide5Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 18, 3 / 8 - 1 / 2 ^ 20, 1 / 2 ^ 26, 18⟩

theorem wide5_secureRo : wide5Setup.SecureRo 2130706433 wide5Analysis 128 := by
  decide +kernel

/-- **128 bits per oracle answer on `2 ^ 21` rows.** Every round error of `wide5Setup`, FRI at
`δ = 3/8 - 2 ^ (-18)` and the extractor at `δ' = 3/8 - 2 ^ (-20)`, is at most `2 ^ (-128)`. -/
theorem wide5_roundError_le :
    roundError wide5Setup (3 / 8 - 2 ^ (-18 : ℤ)) (3 / 8 - 2 ^ (-20 : ℤ)) ≤ (2 ^ 128)⁻¹ :=
  roundError_le_of_secureRo _ KoalaBear.card_eq _ wide5_secureRo _ _
    (by rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num)]; norm_num [wide5Analysis])
    (by rw [coe_three_eighths_sub (-20) 20 rfl (by norm_num)]; norm_num [wide5Analysis])

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
        hashError F (Q + wide5Setup.verifierQueries) :=
  knowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq _ wide5_secureRo _
    (by rw [coe_three_eighths_sub (-20) 20 rfl (by norm_num)]; norm_num [wide5Analysis])
    publicValues Q prover hQ

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
  valid := wide_valid wide5iParams rfl (by decide) rfl (by decide) 64 (by decide) 21
    (by decide)
  folds := by decide

/-- FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)`, the extractor at
`δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, `loss = 2 ^ (-18)` and `t = 14`. -/
def wide5iAnalysis : Analysis := ⟨6143 / 16384, 49151 / 131072, 1 / 2 ^ 18, 14⟩

theorem wide5i_secure : wide5iSetup.Secure 2130706433 wide5iAnalysis 128 := by
  decide +kernel

/-- **128 bits, interactively, on `2 ^ 21` rows.** The knowledge error of `wide5iSetup`, FRI at
`δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at `δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, is
at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeError_le :
    knowledgeError wide5iSetup (6143 / 16384) (49151 / 131072) ≤ (2 ^ 128)⁻¹ :=
  knowledgeError_le_of_secure _ KoalaBear.card_eq _ wide5i_secure _ _
    (by norm_num [wide5iAnalysis]) (by norm_num [wide5iAnalysis])

/-- Knowledge soundness of `wide5iSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `49151/131072`: if no trace within `49151/131072` of the prover's committed trace
satisfies the AIR, the verifier accepts with probability at most `2 ^ (-128)`. -/
theorem wide5i_knowledgeSoundness (publicValues : List F) (prover : Prover wide5iSetup) :
    (∀ trace ∈ closeTraces wide5iSetup (49151 / 131072 : NNReal) prover.trace,
      ¬ (wide 64).Satisfied 21 trace publicValues) →
      acceptance publicValues prover ≤ (2 ^ 128)⁻¹ :=
  knowledgeSoundness_of_secure _ KoalaBear.card_eq _ wide5i_secure _
    (by norm_num [wide5iAnalysis]) publicValues prover

/-! ### Batches with lookups -/

section WideBus
open CompStark.Lookup

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
  exact log2_two_mul_two_pow_sub_one 1

end WideBus

/-- `wideBus 64` on `2 ^ logN` rows with FRI parameters of blowup `4` and a constant final
polynomial, for `logN ≤ 22`. -/
theorem wideBus_valid (P : Fri.Params) (hb : P.logBlowup = 2) (ha : 0 < P.maxLogArity)
    (hf : P.logFinalPolyLen = 0) (hq : 0 < P.numQueries) (logN : ℕ) (h : logN ≤ 22) :
    ValidConfig P (wideBus 64 : Air F) logN :=
  have hc : (wideBus 64 : Air F).logQuotientChunks logN = (wide 64).logQuotientChunks logN := by
    unfold Air.logQuotientChunks
    rfl
  { colsInWidth := wide_colsInWidth 64
    preprocessedSize := by simp only [wideBus, wide, Array.size_empty, Nat.mul_zero]
    periodicFits := rfl
    degreeFits := by
      unfold Air.DegreeFits
      rw [hc]
      exact wide_degreeFits 64 logN
    twoAdic := by
      rw [hb]
      change logN + 2 ≤ 24
      omega
    chunksFit := by
      rw [hc, wide_logQuotientChunks 64 _ (by decide), hb]
      decide
    folds := ha
    finalPolyFits := by rw [hf]; exact Nat.zero_le _
    queries := hq
    blowup := by rw [hb]; decide }

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

/-- FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)`, the extractor at
`δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, `loss = 2 ^ (-18)` and `t = 14`, as for `wide5iSetup`. -/
theorem wideBatch_secure : wideBatchSetup.Secure 2130706433 wide5iAnalysis 128 := by
  decide +kernel

/-- **128 bits, interactively, for a batch of three tables of mixed heights with lookups.** The
knowledge error of `wideBatchSetup`, FRI at `δ = 6143/16384 = 3/8 - 2 ^ (-14)` and the extractor at
`δ' = 49151/131072 = 3/8 - 2 ^ (-17)`, is at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeError_le :
    Batch.knowledgeError wideBatchSetup (6143 / 16384) (49151 / 131072) ≤ (2 ^ 128)⁻¹ :=
  Batch.knowledgeError_le_of_secure _ KoalaBear.card_eq _ wideBatch_secure _ _
    (by norm_num [wide5iAnalysis]) (by norm_num [wide5iAnalysis])

/-- Knowledge soundness of `wideBatchSetup` with error `2 ^ (-128)`, FRI at `6143/16384` and the
extractor at `49151/131072`: if no three traces, each within `49151/131072` of its instance's
committed trace, satisfy the batch (`wideBus 64` each, the bus balanced), the verifier accepts
with probability at most `2 ^ (-128)`. -/
theorem wideBatch_knowledgeSoundness (publicValues : Fin 3 → List F)
    (prover : Batch.Prover wideBatchSetup) :
    (∀ traces ∈ Batch.closeTraces wideBatchSetup (49151 / 131072 : NNReal) prover.trace,
      ¬ wideBatchSetup.Satisfied traces publicValues) →
      Batch.acceptance publicValues prover ≤ (2 ^ 128)⁻¹ :=
  batchKnowledgeSoundness_of_secure _ KoalaBear.card_eq _ wideBatch_secure _
    (by norm_num [wide5iAnalysis]) publicValues prover

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

/-- FRI at `δ = 3/8 - 2 ^ (-16)`, the extractor at `δ' = 3/8 - 2 ^ (-18)`, `loss = 2 ^ (-26)`
and `t = 16`. -/
def wideBatch5Analysis : Analysis := ⟨3 / 8 - 1 / 2 ^ 16, 3 / 8 - 1 / 2 ^ 18, 1 / 2 ^ 26, 16⟩

theorem wideBatch5_secureRo : wideBatch5Setup.SecureRo 2130706433 wideBatch5Analysis 128 := by
  decide +kernel

theorem wideBatchGrind_secureRo :
    wideBatchGrindSetup.SecureRo 2130706433 wideGrindAnalysis 117 := by
  decide +kernel

/-- **128 bits per oracle answer for a batch of three tables of mixed heights with lookups.**
Every round error of `wideBatch5Setup`, FRI at `δ = 3/8 - 2 ^ (-16)` and the extractor at
`δ' = 3/8 - 2 ^ (-18)`, is at most `2 ^ (-128)`. -/
theorem wideBatch5_roundError_le :
    Batch.roundError wideBatch5Setup (3 / 8 - 2 ^ (-16 : ℤ)) (3 / 8 - 2 ^ (-18 : ℤ)) ≤
      (2 ^ 128)⁻¹ :=
  Batch.roundError_le_of_secureRo _ KoalaBear.card_eq _ wideBatch5_secureRo _ _
    (by rw [coe_three_eighths_sub (-16) 16 rfl (by norm_num)]; norm_num [wideBatch5Analysis])
    (by rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num)]; norm_num [wideBatch5Analysis])

/-- **117 bits per oracle answer for a batch of three tables of mixed heights over the quartic
extension.** Every round error of `wideBatchGrindSetup`, FRI at `δ = 3/8 - 2 ^ (-10)` and the
extractor at `δ' = 3/8 - 2 ^ (-11)`, is at most `2 ^ (-117)`. -/
theorem wideBatchGrind_roundError_le :
    Batch.roundError wideBatchGrindSetup (3 / 8 - 2 ^ (-10 : ℤ)) (3 / 8 - 2 ^ (-11 : ℤ)) ≤
      (2 ^ 117)⁻¹ :=
  Batch.roundError_le_of_secureRo _ KoalaBear.card_eq _ wideBatchGrind_secureRo _ _
    (by rw [coe_three_eighths_sub (-10) 10 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    (by rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num)]; norm_num [wideGrindAnalysis])

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
        hashError F (Q + wideBatch5Setup.verifierQueries) :=
  Batch.batchKnowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq _ wideBatch5_secureRo _
    (by rw [coe_three_eighths_sub (-18) 18 rfl (by norm_num)]; norm_num [wideBatch5Analysis])
    publicValues Q prover hQ

/-- **117 bits per oracle call for a batch of three tables with lookups over the quartic
extension.** A prover for `wideBatchGrindSetup` making at most `Q` oracle calls gets a proof
accepted while no tuple of traces close to the ones it committed to satisfies the batch with
probability at most `q · 2 ^ (-117) + hashError q`, `q = Q + verifierQueries`. -/
theorem wideBatchGrind_knowledgeSoundness_ro (publicValues : Fin wideBatchGrindSetup.k → List F)
    (Q : Nat) (prover : Batch.NIProver wideBatchGrindSetup) (hQ : prover.IsTotalQueryBound Q) :
    Pr{let (proof, log, verdict) ← Batch.run wideBatchGrindSetup publicValues prover}[
      verdict = .ok () ∧ proof.degreeBits.toList = List.ofFn wideBatchGrindSetup.logN ∧
        ∀ traces ∈ Batch.closeTraces wideBatchGrindSetup (3 / 8 - 2 ^ (-11 : ℤ) : NNReal)
            (Batch.committedTraces wideBatchGrindSetup log proof),
          ¬ wideBatchGrindSetup.Satisfied traces publicValues] ≤
      (Q + wideBatchGrindSetup.verifierQueries) * (2 ^ 117)⁻¹ +
        hashError F (Q + wideBatchGrindSetup.verifierQueries) :=
  Batch.batchKnowledgeSoundness_ro_of_secureRo _ KoalaBear.card_eq _ wideBatchGrind_secureRo _
    (by rw [coe_three_eighths_sub (-11) 11 rfl (by norm_num)]; norm_num [wideGrindAnalysis])
    publicValues Q prover hQ

end CompStark.Iop
