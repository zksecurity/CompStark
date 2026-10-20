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
  bias of `sampleBits` (a residue of a uniform KoalaBear element is not quite uniform).

A round with grinding (`commitPowBits` for the folds, `queryPowBits` for the queries) also needs
its proof-of-work sample to vanish on its low bits, in the same answer: its error is multiplied by
`powFraction`. `roundError` is the largest round error, at the best proximity loss. `hashError`
bounds collisions and predictions among the digests of `q` queries.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Sound

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4

namespace Setup
variable (S : Setup)

/-- Plonky3's folding arities for `S`: `logN - logFinalPolyLen` halvings. -/
def foldArities : List ℕ+ := Sound.folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen)

/-- FRI folds `lastFold + 1` times. -/
def lastFold : Nat := S.foldArities.length - 1

/-- The arity of each fold, as ArkLib's folding schedule. -/
def schedule (i : Fin (S.lastFold + 1)) : ℕ+ := S.foldArities.getD i 1

end Setup

/-- The probability that `bits` low bits of a uniform KoalaBear element vanish:
`(127 · 2^(24 - bits) + 1) / p ≤ 2^-bits (1 + 2^bits / p)`; `1` for `bits = 0`. -/
noncomputable def powFraction (bits : Nat) : ENNReal :=
  ((127 * 2 ^ (24 - bits) + 1 : Nat) : ENNReal) / Fintype.card 𝔽

/-- FRI's fold `i` makes a far word near by folding (ArkLib's `foldingErrorLossy`): the lossy
correlated-agreement error of the fold's arity at proximity `δ` and loss `loss`. -/
noncomputable def friFoldError (S : Setup) (δ loss : NNReal) (i : Fin (S.lastFold + 1)) :
    ENNReal :=
  Fri.Spec.foldingErrorLossy (ω := S.domain) S.schedule (finalDegree S.params.logFinalPolyLen)
    δ loss i

/-- FRI's queries all land where the checks pass, after safe folds, for a word `δ`-far from the
code: `(1 - min (δ - k loss) (δ - (k + 1) loss) + 1/p) ^ numQueries`, `k + 1` folds. -/
noncomputable def friQueryError (S : Setup) (δ loss : NNReal) : ENNReal :=
  ENNReal.ofReal (1 - min ((δ : ℝ) - S.lastFold * loss) ((δ : ℝ) - (S.lastFold + 1) * loss) +
    1 / Fintype.card 𝔽) ^ S.params.numQueries

/-- The error of one random-oracle answer: the IOP's round-by-round errors, the FRI rounds
credited with their grinding. FRI's folds and queries share one proximity loss. -/
noncomputable def roundError (S : Setup) (δ δ' : NNReal) : ENNReal :=
  ⨅ loss : NNReal,
    (max (foldingError S δ') <| max (outOfDomainError S δ') <|
      max (batchingError S δ ((δ' : ℝ) - 2 / S.size)) <|
      max (powFraction S.params.commitPowBits * ⨆ i, friFoldError S δ loss i)
        (powFraction S.params.queryPowBits * friQueryError S δ loss))

/-- Digest collisions and predictions among `q` queries. -/
noncomputable def hashError (q : Nat) : ENNReal := 3 * q ^ 2 / (Fintype.card 𝔽 : ENNReal) ^ 8

end CompStark.Iop
