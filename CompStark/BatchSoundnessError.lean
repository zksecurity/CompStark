/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.BatchIop
public import CompStark.SoundnessError

/-! # The knowledge error of the batch STARK

The bound of `batchKnowledgeSoundness` (`CompStark/BatchSoundness.lean`), for FRI at proximity `δ`
and the extractor at a proximity `δ'` below `1 - rate`. If no tuple of close traces satisfies the
batch (every AIR, and every bus balanced), then either the lookup challenges `(α_L, β_L)` are bad,
or some instance has no close trace and close permutation trace that satisfy all its constraints;
the challenges `α`, `ζ` and `a` cost what they cost that instance (`CompStark/SoundnessError.lean`),
batched with the other instances of its domain's size:

* `(α_L, β_L)`: for some tuple of close traces satisfying every AIR but unbalanced, a denominator
  `α_L + (b + 1) β_Lᵂ - ∑ⱼ tⱼ β_Lᵏ⁻¹⁻ʲ` vanishes or the sum of fractions of all lookup messages
  does (`lookupError`). Per tuple, the denominators of its `D` distinct (bus, tuple) keys vanish at
  `D |𝕂|` pairs, and the cleared numerator, a nonzero polynomial of total degree at most
  `(D - 1) W` in `(α_L, β_L)`, at most `(D - 1) W |𝕂|` (Schwartz–Zippel, `Sound/LogUp.lean`), with
  `D` at most the number `T` of interactions, every tuple on every row; times the list sizes of the
  instances' traces.
* `α` and `ζ`: the instance's constraint-folding and out-of-domain errors (`foldingError`,
  `outOfDomainError`), with its own list sizes, constraints and `identityDegree`, its LogUp
  constraints and permutation trace included.
* `a`: the correlated-agreement error of the powers of `a` over the opened words of the instances
  of its domain's size (`batchingErrorOf`, `groupNumOpened` words), at `δ' - 2/N`, `N` its
  domain's size: decoding loses the up to two points of its domain where `ζ` or `ζ ω_n` lies.

The knowledge error adds the lookup error, the worst instance's, and FRI's error with the shorter
instances' words injected (`friErrorWith`, `FriGame.acceptance_le`).
-/

@[expose] public section
namespace CompStark.Iop.Batch
open CompStark.Stark CompStark.Sound

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

namespace Setup
variable {withLookups : Bool} (S : Setup EF withLookups)

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

/-- The number `T` of the batch's interactions: every tuple of every lookup on every row of every
instance. -/
def numInteractions : Nat := ∑ i, 2 ^ S.logN i * ((S.lookups i).map (·.tuples.length)).sum

/-- The widest tuple of the batch, at least `1` (`W`). -/
abbrev lookupWidth : Nat := Lookup.maxWidth (List.ofFn S.lookups).flatten

/-- The most tuples of candidate traces at `δ`: the product of the instances' list sizes. -/
noncomputable def traceListSize (δ : ℝ) : Nat :=
  ∏ i, (S.instanceSetup i).listSize (Fin (S.air i).width) δ

/-- LogUp's error: `(T + (T - 1) W) / |𝕂|` per tuple of candidate traces. -/
noncomputable def lookupError (δ : NNReal) : ENNReal :=
  (S.traceListSize δ * (S.numInteractions + (S.numInteractions - 1) * S.lookupWidth) : Nat) /
    (Fintype.card (Challenge.Spec EF) : ENNReal)

end Setup

/-- The knowledge error, for FRI at `δ` and the extractor at `δ'`: the lookup error, the worst
instance's error, and FRI's with the shorter instances' words injected. -/
noncomputable def knowledgeError {withLookups : Bool} (S : Setup EF withLookups) (δ δ' : NNReal) :
    ENNReal :=
  S.lookupError δ' + (⨆ i, S.instanceError δ δ' i) + friErrorWith S.domainSetup S.friHeights δ

end CompStark.Iop.Batch
