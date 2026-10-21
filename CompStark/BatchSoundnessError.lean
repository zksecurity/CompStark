/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchIop
public import CompStark.SoundnessError

/-! # The knowledge error of the batch STARK

The bound of `batchKnowledgeSoundness` (`CompStark/BatchSoundness.lean`), for FRI at proximity `δ`
and the extractor at a proximity `δ' ≥ δ + 2/N` below `1 - rate`. If no tuple of close traces
satisfies every AIR, some instance has no close trace that satisfies its AIR, and the challenges
`α` and `ζ` cost what they cost that instance alone (`CompStark/SoundnessError.lean`):

* `α` and `ζ`: the largest, over the instances, of the instance's constraint-folding and
  out-of-domain errors (`foldingError`, `outOfDomainError`), with its own list sizes, constraints
  and `identityDegree`.
* `a`: the correlated-agreement error of the powers of `a` over all opened words of all instances
  (`batchingErrorOf`, `numOpened` words).
* FRI accepts a word that is `δ`-far from low degree (`friError`, ArkLib's FRI soundness on `L`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable (S : Setup EF)

/-- `N = 2 ^ (logN + logBlowup)`, the size of `L`. -/
abbrev size : Nat := 2 ^ (S.logN + S.params.logBlowup)

/-- The rate `n / N` of the traces' code. -/
noncomputable def rate : ℝ := (2 ^ S.logN : Nat) / (S.size : ℝ)

/-- The number of opened words: every instance's. -/
abbrev numOpened : Nat := ∑ i, (S.instanceSetup i).numOpened

end Setup

/-- The knowledge error, for FRI at `δ` and the extractor at `δ' ≥ δ + 2/N`: the worst instance's
constraint-folding and out-of-domain errors, batching all opened words at `δ' - 2/N`, and FRI. -/
noncomputable def knowledgeError (S : Setup EF) (δ δ' : NNReal) : ENNReal :=
  (⨆ i, foldingError (S.instanceSetup i) δ' + outOfDomainError (S.instanceSetup i) δ') +
    batchingErrorOf S.domainSetup S.numOpened δ ((δ' : ℝ) - 2 / S.size) +
    friError S.domainSetup δ

end CompStark.Iop.Batch
