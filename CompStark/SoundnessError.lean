/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop

/-! # The knowledge error of the STARK

The bound of `knowledgeSoundness` (`CompStark/Soundness.lean`), for FRI at proximity `δ` and the
extractor at a proximity `δ' ≥ δ + 2/N` below `1 - rate`. It has one term per challenge of the
interactive oracle proof (`CompStark/Iop.lean`), with `ℓ` the list sizes of the trace's and the
quotient's codes at `δ'` (`Setup.listSize`):

* `α`: folding the constraints by `α` makes a constraint that fails on some row of one of the
  `ℓ` candidate traces vanish on every row (`foldingError`).
* `ζ`: the constraints hold at `ζ` for one of the `ℓ²` candidate pairs although they fail as
  polynomials, or `ζ` lies on the trace domain (`outOfDomainError`).
* `a`: the batched DEEP word is `δ`-close to low degree although its summands are not on a common
  set at `δ' - 2/N` (`batchingError`, the correlated-agreement error of the powers of `a`; the
  difference `δ' - 2/N - δ` is the proximity loss). Decoding loses the up to two points of `L`
  where `ζ` or `ζ ω_n` lies, at which the DEEP quotients divide by zero.
* FRI accepts a word that is `δ`-far from low degree (`friError`, ArkLib's FRI soundness).

Below the unique-decoding radius `ℓ ≤ 1`; up to the Johnson bound `1 - √rate`, `ℓ` is small.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CoreDefinitions Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable (S : Setup EF)

/-- The rate `n / N` of the trace's code. -/
noncomputable def rate : ℝ := (S.n : ℝ) / S.size

/-- The most tuples of polynomials of degree at most `n`, indexed by `ι`, that agree with one
tuple of words on `L` on a common set of at least `(1 - δ) N` points: the list size of the
interleaved code. At most `1` below the unique-decoding radius, and bounded by the Johnson bound
below `1 - √rate`. -/
noncomputable def listSize (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ) : Nat :=
  Finset.univ.sup fun words : ι → S.Point → F ↦
    {polys : ι → F[X] | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}.ncard

/-- The number of opened words: each trace column twice, at `ζ` and `ζ ω_n`, each coordinate of
each chunk, and each preprocessed column at `ζ` and, if opened, at `ζ ω_n`. -/
abbrev numOpened : Nat :=
  2 * S.air.width + Challenge.d EF * S.chunks + S.air.preprocessedWidth +
    S.air.preprocessedNextWidth

/-- A bound on the degree of the constraint identity `C(X) = Z_H(X) Q(X)` in `ζ`, for trace
columns of degree at most `n`: the largest constraint degree and `n · (chunks + 1)`. -/
def identityDegree : Nat :=
  max (S.air.constraints.foldl
    (fun m c ↦ max m (c.degBound (S.n + 1) (S.air.periodicDegree S.n))) 0) (S.n * (S.chunks + 1))

/-- The Reed–Solomon code of FRI and the DEEP words: polynomials of degree below `n` on `L`. -/
noncomputable def code : ModuleCode S.Point 𝕂 𝕂 :=
  ReedSolomon.code ⟨fun i ↦ S.domain i, (S.domain).injective⟩ S.n

end Setup

/-- A word agrees with a codeword of `S.code` on at least `(1 - δ) N` points. -/
def Near (S : Setup EF) (δ : ℝ) (w : S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧ ∃ u ∈ S.code, ∀ i ∈ T, w i = u i

/-- Words are near the code on a common set of at least `(1 - δ) N` points. -/
def NearTogether (S : Setup EF) {ι : Type} (δ : ℝ) (ws : ι → S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧
    ∀ k, ∃ u ∈ S.code, ∀ i ∈ T, ws k i = u i

/-- `α` folds a constraint that fails on some row of a candidate trace into one that vanishes on
every row: at most `#constraints - 1` values of `α` per candidate, out of `|𝕂|`. -/
noncomputable def foldingError (S : Setup EF) (δ : NNReal) : ENNReal :=
  (S.listSize (Fin S.air.width) δ * (S.air.constraints.length - 1) : Nat) /
    (Fintype.card 𝕂 : ENNReal)

/-- For some pair of candidate trace and quotient, the constraint identity, a nonzero polynomial
of degree at most `identityDegree`, vanishes at `ζ`; or `ζ` lies on the trace domain `H`, `n`
points. -/
noncomputable def outOfDomainError (S : Setup EF) (δ : NNReal) : ENNReal :=
  (S.listSize (Fin S.air.width) δ * S.listSize (Fin S.chunks × Fin (Challenge.d EF)) δ *
    S.identityDegree + S.n : Nat) / (Fintype.card 𝕂 : ENNReal)

open Classical in
/-- The correlated-agreement error of the powers `1, a, a², …` over `m` words on `L`: the largest
probability, over the words, that their combination by the powers of a uniform `a` is `δ`-near
the code although the words are not near on a common set at radius `δ'`. -/
noncomputable def batchingErrorOf (S : Setup EF) (m : Nat) (δ : NNReal) (δ' : ℝ) : ENNReal :=
  ⨆ ws : Fin m → S.Point → 𝕂,
    ((Finset.univ.filter fun a : 𝕂 ↦
      Near S δ (fun i ↦ ∑ k : Fin m, a ^ (k : Nat) * ws k i) ∧
      ¬ NearTogether S δ' ws).card : ENNReal) / Fintype.card 𝕂

/-- The correlated-agreement error of the powers `1, a, a², …` over the opened words. -/
noncomputable def batchingError (S : Setup EF) (δ : NNReal) (δ' : ℝ) : ENNReal :=
  batchingErrorOf S S.numOpened δ δ'

/-- FRI's soundness error at proximity `δ` (ArkLib's `Fri.Spec.soundnessErrorLossy`): the lossy
correlated-agreement error of each fold, and `(1 - δ + #folds · loss) ^ numQueries` for the
queries, minimized over the proximity loss `loss ≥ 0`. -/
noncomputable def friError (S : Setup EF) (δ : NNReal) : ENNReal :=
  friErrorOf S.domain (Sound.folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen))
    S.params.logFinalPolyLen S.params.numQueries δ

/-- The knowledge error, for FRI at proximity `δ` and the extractor at `δ' ≥ δ + 2/N`; batching
at `δ' - 2/N` pays for the two points that decoding may lose. -/
noncomputable def knowledgeError (S : Setup EF) (δ δ' : NNReal) : ENNReal :=
  foldingError S δ' + outOfDomainError S δ' + batchingError S δ ((δ' : ℝ) - 2 / S.size) +
    friError S δ

end CompStark.Iop
