/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.SoundnessError

/-! # The error of one random-oracle answer

In the random-oracle model, every challenge round of the interactive oracle proof
(`CompStark/Iop.lean`) is one oracle answer, and the prover attacks one round per query. Each
round has an error, the probability that a fresh answer makes it bad:

* `α`, `ζ` and `a`: `foldingError`, `outOfDomainError`, `batchingError`, as in the interactive
  knowledge error (`CompStark/SoundnessError.lean`).
* FRI fold `i` (`friFoldError`): ArkLib's lossy correlated-agreement error of the fold, at a
  proximity loss `loss`.
* FRI's queries (`friQueryError`): every query lands where the checks pass, a density of at most
  `1 - min (δ - k loss, δ - (k + 1) loss)` after `k + 1` safe folds, plus `1/p` per query for the
  bias of `sampleBits` (a residue of a uniform base element is not quite uniform).

A round with grinding (`oodPowBits` for `ζ`, `batchPowBits` for `a`, `commitPowBits` for the
folds, `queryPowBits` for the queries) also needs its proof-of-work sample to vanish on its low
bits, in the same answer: its error is multiplied by `powFraction`. `roundError` is the largest
round error, at the best proximity loss. `hashError` bounds collisions and predictions among the
digests of `q` queries, `(2 + 2 ^ h) q² / |F|⁸` for commitments to Merkle caps of height `h`
(`3 q² / |F|⁸` for roots).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable (S : Setup EF)

/-- Plonky3's folding arities for `S`: `logN - logFinalPolyLen` halvings. -/
def foldArities : List ℕ+ := Sound.folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)

/-- FRI folds `lastFold + 1` times. -/
def lastFold : Nat := S.foldArities.length - 1

/-- The arity of each fold, as ArkLib's folding schedule. -/
def schedule (i : Fin (S.lastFold + 1)) : ℕ+ := S.foldArities.getD i 1

end Setup

/-- The probability that `bits` low bits of a uniform element of `F`, `p = |F|`, vanish:
`((p - 1) / 2^bits + 1) / p ≤ 2^-bits + 1/p`, the multiples of `2 ^ bits` below `p`; `1` for
`bits = 0`. -/
noncomputable def powFraction (F : Type) (bits : Nat) : ENNReal :=
  (((Nat.card F - 1) / 2 ^ bits + 1 : Nat) : ENNReal) / Nat.card F

/-- FRI's fold `i` makes a far word near by folding (ArkLib's `foldingErrorLossy`): the lossy
correlated-agreement error of the fold's arity at proximity `δ` and loss `loss`. -/
noncomputable def friFoldError (S : Setup EF) (δ loss : NNReal) (i : Fin (S.lastFold + 1)) :
    ENNReal :=
  Fri.Spec.foldingErrorLossy (ω := S.domain) S.schedule (finalDegree S.params.logFinalPolyLen)
    δ loss i

/-- FRI's queries all land where the checks pass, after safe folds, for a word `δ`-far from the
code: `(1 - min (δ - k loss) (δ - (k + 1) loss) + 1/p) ^ numQueries`, `k + 1` folds. -/
noncomputable def friQueryError (S : Setup EF) (δ loss : NNReal) : ENNReal :=
  ENNReal.ofReal (1 - min ((δ : ℝ) - S.lastFold * loss) ((δ : ℝ) - (S.lastFold + 1) * loss) +
    1 / Nat.card F) ^ S.params.numQueries

/-- The error of one random-oracle answer: the IOP's round-by-round errors, every round after
`α` credited with its grinding. FRI's folds and queries share one proximity loss. -/
noncomputable def roundError (S : Setup EF) (δ δ' : NNReal) : ENNReal :=
  ⨅ loss : NNReal,
    (max (foldingError S δ') <|
      max (powFraction F S.params.oodPowBits * outOfDomainError S δ') <|
      max (powFraction F S.params.batchPowBits * batchingError S δ δ') <|
      max (powFraction F S.params.commitPowBits * ⨆ i, friFoldError S δ loss i)
        (powFraction F S.params.queryPowBits * friQueryError S δ loss))

/-- Digest collisions and predictions among `q` queries, digests of eight elements of `F`, each
commitment round binding the `2 ^ capHeight` digests of a Merkle cap. -/
noncomputable def hashError (F : Type) (capHeight q : Nat) : ENNReal :=
  (2 + 2 ^ capHeight) * q ^ 2 / (Nat.card F : ENNReal) ^ 8

end CompStark.Iop
