/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchSoundnessError
public import CompStark.NonInteractiveError
public import CompStark.Sound.FriRun

/-! # The error of one random-oracle answer of the batch STARK

In the random-oracle model every challenge round of the batch STARK is one oracle answer, as for
the STARK (`CompStark/NonInteractiveError.lean`), and the prover attacks one round per query. If
no tuple of close traces satisfies every AIR, the rounds of `α`, `ζ` and `a` are bad for the
instance the extractor finds failing, as in the interactive knowledge error
(`CompStark/BatchSoundnessError.lean`), so each costs its worst instance's error:

* `α` and `ζ`: the instance's constraint-folding and out-of-domain errors (`foldingError`,
  `outOfDomainError`).
* `a`: the correlated-agreement error of the powers of `a` over the opened words of the instances
  of the failing instance's domain size (`batchingErrorOf`, at `δ' - 2/N`).
* FRI fold `j` (`friFoldError`): the lossy correlated-agreement error of the fold of FRI with the
  shorter instances' words injected, at a proximity loss `loss` (`FriGame.Rounds.foldErrorAt`,
  the summand of `friErrorWith`).
* FRI's queries (`friQueryError`): every query lands where the checks pass, a density of at most
  `1 - δ + m loss` after `m` safe folds, plus `1/p` per query for the bias of `sampleBits`.

Grinding multiplies each round's error after `α` by `powFraction`, as for the STARK. `roundError`
is the largest round error, at the best proximity loss.
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable (S : Setup EF)

/-- FRI's rounds: Plonky3's folding schedule from the tallest domain, injecting at the sizes of
the shorter instances' domains. Their errors depend on the sizes only. -/
noncomputable abbrev friRounds : FriGame.Rounds (Challenge.Spec EF)
    (S.logN S.top + S.params.logBlowup) :=
  S.domainSetup.friRounds (fun _ _ ↦ 0) S.friHeights

end Setup

/-- FRI's fold `j` makes a far word near by folding, its injected word with it: the lossy
correlated-agreement error of the fold at proximity `δ` and loss `loss`, `0` past the last fold. -/
noncomputable def friFoldError (S : Setup EF) (δ loss : NNReal) (j : ℕ) : ENNReal :=
  S.friRounds.foldErrorAt (2 ^ S.params.logFinalPolyLen) δ loss j S.domainSetup.domain

/-- FRI's queries all land where the checks pass, after `m` safe folds, for a word `δ`-far from
the code or an injected word `δ`-far from its own: `(1 - δ + m loss + 1/p) ^ numQueries`. -/
noncomputable def friQueryError (S : Setup EF) (δ loss : NNReal) : ENNReal :=
  ENNReal.ofReal (1 - δ + S.friRounds.numFolds * loss + 1 / Nat.card F) ^ S.params.numQueries

/-- The error of one random-oracle answer: every round's error at its worst instance, every round
after `α` credited with its grinding. FRI's folds and queries share one proximity loss. -/
noncomputable def roundError (S : Setup EF) (δ δ' : NNReal) : ENNReal :=
  ⨅ loss : NNReal,
    (max (⨆ i, foldingError (S.instanceSetup i) δ') <|
      max (powFraction F S.params.oodPowBits * ⨆ i, outOfDomainError (S.instanceSetup i) δ') <|
      max (powFraction F S.params.batchPowBits * ⨆ i, batchingErrorOf (S.instanceSetup i)
        (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
        ((δ' : ℝ) - 2 / (S.instanceSetup i).size)) <|
      max (powFraction F S.params.commitPowBits * ⨆ j, friFoldError S δ loss j)
        (powFraction F S.params.queryPowBits * friQueryError S δ loss))

end CompStark.Iop.Batch
