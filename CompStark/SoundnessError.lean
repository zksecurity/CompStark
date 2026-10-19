/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop

/-! # The knowledge error of the STARK

The bound of `knowledgeSoundness` (`CompStark/Soundness.lean`), at a proximity `δ` up to the
unique-decoding radius of the trace's code (`Setup.uniqueDecodingRadius`). It has one term per
challenge of the interactive oracle proof (`CompStark/Iop.lean`):

* `α`: folding the constraints by `α` makes a constraint that fails on some row vanish on every
  row (`foldingError`).
* `ζ`: the constraints hold at `ζ` although they fail as polynomials, or `ζ` lies in the base
  field (`outOfDomainError`).
* `a`: the batched DEEP word is `δ`-close to low degree although one of its summands is not
  (`batchingError`, the correlated-agreement error of the powers of `a`).
* FRI accepts a word that is `δ`-far from low degree (`friError`, ArkLib's FRI soundness).
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CoreDefinitions

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

namespace Setup
variable (S : Setup)

/-- `N = 2 ^ (logN + logBlowup)`, the size of `L`. -/
abbrev size : Nat := 2 ^ (S.logN + S.params.logBlowup)

/-- The unique-decoding radius of the polynomials of degree at most `n` on `L`, relative to
`N = |L|`: `(N - n - 1) / 2N`. -/
noncomputable def uniqueDecodingRadius : NNReal := ((S.size - S.n - 1 : Nat) : NNReal) / 2 / S.size

/-- The number of opened words: each trace column twice, at `ζ` and `ζ ω_n`, and each
coordinate of each chunk. -/
abbrev numOpened : Nat := 2 * S.air.width + 4 * S.chunks

/-- A bound on the degree of the constraint identity `C(X) = Z_H(X) Q(X)` in `ζ`, for trace
columns of degree at most `n`: the largest constraint degree and `n · (chunks + 1)`. -/
def identityDegree : Nat :=
  max (S.air.constraints.foldl (fun m c ↦ max m (c.degBound (S.n + 1))) 0) (S.n * (S.chunks + 1))

/-- The Reed–Solomon code of FRI and the DEEP words: polynomials of degree below `n` on `L`. -/
noncomputable def code : ModuleCode S.Point 𝕂 𝕂 :=
  ReedSolomon.code ⟨fun i ↦ S.domain i, (S.domain).injective⟩ S.n

end Setup

/-- `α` folds a constraint that fails on some row into one that vanishes on every row: at most
`#constraints - 1` of the `|𝕂|` values of `α` do. -/
noncomputable def foldingError (S : Setup) : ENNReal :=
  (S.air.constraints.length - 1 : Nat) / (Fintype.card 𝕂 : ENNReal)

/-- The constraint identity, a nonzero polynomial of degree at most `identityDegree`, vanishes at
`ζ`, or `ζ` lies in the base field. -/
noncomputable def outOfDomainError (S : Setup) : ENNReal :=
  (S.identityDegree + Fintype.card 𝔽 : Nat) / (Fintype.card 𝕂 : ENNReal)

/-- The correlated-agreement error of the powers `1, a, a², …` over the opened words at
proximity `δ`: the batched word is `δ`-close to `code` without the words being so on a common
set. -/
noncomputable def batchingError (S : Setup) (δ : NNReal) : ENNReal :=
  mcaError (univariatePowersGenerator 𝕂 (S.numOpened - 1)) S.code δ

/-- FRI's soundness error at proximity `δ` (ArkLib's `Fri.Spec.soundnessError`): the
correlated-agreement error of each fold, and `(1 - δ) ^ numQueries` for the queries. -/
noncomputable def friError (S : Setup) (δ : NNReal) : ENNReal :=
  friErrorOf S.domain (Sound.folds S.params.maxLogArity (S.logN - S.params.logFinalPolyLen))
    S.params.logFinalPolyLen S.params.numQueries δ

/-- The knowledge error at proximity `δ`. -/
noncomputable def knowledgeError (S : Setup) (δ : NNReal) : ENNReal :=
  foldingError S + outOfDomainError S + batchingError S δ + friError S δ

end CompStark.Iop
