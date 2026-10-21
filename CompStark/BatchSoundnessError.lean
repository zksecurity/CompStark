/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchIop
public import CompStark.SoundnessError

/-! # The knowledge error of the batch STARK

The bound of `batchKnowledgeSoundness` (`CompStark/BatchSoundness.lean`), for FRI at proximity `δ`
and the extractor at a proximity `δ'` below `1 - rate`. If no tuple of close traces satisfies
every AIR, some instance has no close trace that satisfies its AIR; the challenges `α`, `ζ` and
`a` cost what they cost that instance (`CompStark/SoundnessError.lean`), batched with the other
instances of its domain's size:

* `α` and `ζ`: the instance's constraint-folding and out-of-domain errors (`foldingError`,
  `outOfDomainError`), with its own list sizes, constraints and `identityDegree`.
* `a`: the correlated-agreement error of the powers of `a` over the opened words of the instances
  of its domain's size (`batchingErrorOf`, `groupNumOpened` words), at `δ' - 2/N`, `N` its
  domain's size: decoding loses the up to two points of its domain where `ζ` or `ζ ω_n` lies.

The knowledge error takes the worst instance, and adds FRI's error with the shorter instances'
words injected (`friErrorWith`, `FriGame.acceptance_le`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable (S : Setup EF)

/-- The rate `1 / 2 ^ logBlowup` of every instance's code. -/
noncomputable def rate : ℝ := 1 / 2 ^ S.params.logBlowup

/-- The number of opened words of the instances whose domains have `2 ^ m` points. -/
noncomputable def groupNumOpened (m : ℕ) : Nat :=
  ∑ i with S.logN i + S.params.logBlowup = m, (S.instanceSetup i).numOpened

/-- An instance's error: constraint folding, out of domain, and batching with the other instances
of its domain's size. -/
noncomputable def instanceError (δ δ' : NNReal) (i : Fin S.k) : ENNReal :=
  foldingError (S.instanceSetup i) δ' + outOfDomainError (S.instanceSetup i) δ' +
    batchingErrorOf (S.instanceSetup i) (S.groupNumOpened (S.logN i + S.params.logBlowup)) δ
      ((δ' : ℝ) - 2 / (S.instanceSetup i).size)

end Setup

/-- The knowledge error, for FRI at `δ` and the extractor at `δ'`: the worst instance's error, and
FRI's with the shorter instances' words injected. -/
noncomputable def knowledgeError (S : Setup EF) (δ δ' : NNReal) : ENNReal :=
  (⨆ i, S.instanceError δ δ' i) + friErrorWith S.domainSetup S.friHeights δ

end CompStark.Iop.Batch
