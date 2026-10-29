/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Iop

/-! # The knowledge error of the STARK

The bound of `knowledgeSoundness` (`CompStark/Soundness.lean`), for FRI at proximity `δ` and the
extractor at a proximity `δ' ≥ δ` below `1 - rate`. It has one term per challenge of the
interactive oracle proof (`CompStark/Iop.lean`), with `ℓ` the list sizes of the committed words'
interleaved codes at `δ'` (`Setup.listSize`):

* `α`: folding the constraints by `α` makes a constraint that fails on some row of one of the
  `ℓ` candidate traces vanish on every row (`foldingError`).
* `ζ`: the constraints hold at `ζ` for one of the `ℓ` candidates of the committed words although
  they fail as polynomials, or `ζ` lies on the trace domain or on `L`, where the DEEP quotients
  divide by zero (`outOfDomainError`). The decoding
  step finds the trace, permutation trace and quotient polynomials on one common set, so the
  candidates are those of the committed words as one family, whose list size is that of an
  interleaved code: linear in the list size, as in DEEP-ALI's analysis (Haböck,
  <https://eprint.iacr.org/2022/1216>, Theorem 8).
* `a`: the batched DEEP word is `δ`-close to low degree although its summands are not on a common
  set at `δ'` (`batchingError`, the correlated-agreement error of the powers of `a`; the
  difference `δ' - δ` is the proximity loss).
* FRI accepts a word that is `δ`-far from low degree (`friError`, `FriGame.acceptance_le`).

Below the unique-decoding radius `ℓ ≤ 1`; up to the Johnson bound `1 - √rate`, `ℓ` is small.
-/

@[expose] public section
namespace CompStark.Iop
open CompStark.Stark CompStark.Sound CoreDefinitions Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

namespace Setup
variable {lookups : List (Lookup F)} (S : Setup EF lookups)

/-- The rate `n / N` of the trace's code. -/
noncomputable def rate : ℝ := (S.n : ℝ) / S.size

/-- The most tuples of polynomials of degree at most `n`, indexed by `ι`, that agree with one
tuple of words on `L` on a common set of at least `(1 - δ) N` points: the list size of the
interleaved code. At most `1` below the unique-decoding radius, and bounded by the Johnson bound
below `1 - √rate`. -/
noncomputable def listSize (ι : Type) [Fintype ι] [DecidableEq ι] (δ : ℝ) : Nat :=
  Finset.univ.sup fun words : ι → S.Point → F ↦
    {polys : ι → F[X] | (∀ k, (polys k).natDegree ≤ S.n) ∧ Agree S δ words polys}.ncard

/-- The list size of the permutation trace's coordinate words, `1` without lookups. -/
noncomputable abbrev permListSize (δ : ℝ) : Nat := match lookups with
  | [] => 1
  | _ :: _ => S.listSize (Fin S.permWidth × Fin (Challenge.d EF)) δ

/-- The number of opened words: each trace column at `ζ` and, if opened, at `ζ ω_n`, each
coordinate of each chunk, each preprocessed column at `ζ` and, if opened, at `ζ ω_n`, and each
coordinate of each permutation column at `ζ` and `ζ ω_n`. -/
abbrev numOpened : Nat :=
  S.air.width + S.air.mainNextWidth + Challenge.d EF * S.chunks + S.air.preprocessedWidth +
    S.air.preprocessedNextWidth + 2 * (Challenge.d EF * S.permWidth)

/-- The number of constraints the check at `ζ` folds: the AIR's and the LogUp constraints. -/
abbrev numConstraints : Nat := S.air.constraints.length + S.extConstraints.length

/-- A bound on the degree of the constraint identity `C(X) = Z_H(X) Q(X)` in `ζ`, for trace and
permutation columns of degree at most `n`: the largest constraint degree, LogUp constraints
included, and `n · (chunks + 1)`. -/
def identityDegree : Nat :=
  max (S.extConstraints.foldl
    (fun m g ↦ max m (g.degBound (S.n + 1) (S.air.periodicDegree S.n)))
    (S.air.constraints.foldl
      (fun m c ↦ max m (c.degBound (S.n + 1) (S.air.periodicDegree S.n))) 0))
    (S.n * (S.chunks + 1))

/-- Without lookups, the AIR's quotient chunks. -/
theorem chunks_nil (T : Setup EF) : T.chunks = 2 ^ T.air.logQuotientChunks T.logN := rfl

/-- Without lookups, the AIR's constraints. -/
theorem numConstraints_nil (T : Setup EF) : T.numConstraints = T.air.constraints.length := rfl

/-- Without lookups, the opened words of the trace, the chunks and the preprocessed trace. -/
theorem numOpened_nil (T : Setup EF) : T.numOpened = T.air.width + T.air.mainNextWidth +
    Challenge.d EF * T.chunks + T.air.preprocessedWidth + T.air.preprocessedNextWidth := rfl

/-- Without lookups, the AIR's constraint degrees and `n · (chunks + 1)`. -/
theorem identityDegree_nil (T : Setup EF) : T.identityDegree =
    max (T.air.constraints.foldl
      (fun m c ↦ max m (c.degBound (T.n + 1) (T.air.periodicDegree T.n))) 0)
      (T.n * (T.chunks + 1)) := rfl

/-- The Reed–Solomon code of FRI and the DEEP words: polynomials of degree below `n` on `L`. -/
noncomputable def code : ModuleCode S.Point 𝕂 𝕂 :=
  ReedSolomon.code ⟨fun i ↦ S.domain i, (S.domain).injective⟩ S.n

end Setup

variable {lookups : List (Lookup F)}

/-- A word agrees with a codeword of `S.code` on at least `(1 - δ) N` points. -/
def Near (S : Setup EF lookups) (δ : ℝ) (w : S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧ ∃ u ∈ S.code, ∀ i ∈ T, w i = u i

/-- Words are near the code on a common set of at least `(1 - δ) N` points. -/
def NearTogether (S : Setup EF lookups) {ι : Type} (δ : ℝ) (ws : ι → S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧
    ∀ k, ∃ u ∈ S.code, ∀ i ∈ T, ws k i = u i

/-- `α` folds a constraint that fails on some row of a candidate trace and permutation trace into
one that vanishes on every row: at most `#constraints - 1` values of `α` per candidate pair, out
of `|𝕂|`. -/
noncomputable def foldingError (S : Setup EF lookups) (δ : NNReal) : ENNReal :=
  (S.listSize (Fin S.air.width) δ * S.permListSize δ * (S.numConstraints - 1) : Nat) /
    (Fintype.card 𝕂 : ENNReal)

/-- For some candidate of the committed words as one family (`Setup.Committed`: trace,
permutation trace and quotient on one common set), the constraint identity, a nonzero polynomial
of degree at most `identityDegree`, vanishes at `ζ`; or `ζ` lies on the trace domain `H`, `n`
points, or on `L`, `N` points. -/
noncomputable def outOfDomainError (S : Setup EF lookups) (δ : NNReal) : ENNReal :=
  (S.listSize S.Committed δ * S.identityDegree + S.n + S.size : Nat) / (Fintype.card 𝕂 : ENNReal)

open Classical in
/-- The correlated-agreement error of the powers `1, a, a², …` over `m` words on `L`: the largest
probability, over the words, that their combination by the powers of a uniform `a` is `δ`-near
the code although the words are not near on a common set at radius `δ'`. -/
noncomputable def batchingErrorOf (S : Setup EF lookups) (m : Nat) (δ : NNReal) (δ' : ℝ) :
    ENNReal :=
  ⨆ ws : Fin m → S.Point → 𝕂,
    ((Finset.univ.filter fun a : 𝕂 ↦
      Near S δ (fun i ↦ ∑ k : Fin m, a ^ (k : Nat) * ws k i) ∧
      ¬ NearTogether S δ' ws).card : ENNReal) / Fintype.card 𝕂

/-- The correlated-agreement error of the powers `1, a, a², …` over the opened words. -/
noncomputable def batchingError (S : Setup EF lookups) (δ : NNReal) (δ' : ℝ) : ENNReal :=
  batchingErrorOf S S.numOpened δ δ'

/-- FRI's soundness error at proximity `δ` with inputs injected at the log heights `heights`
(`FriGame.error`): the lossy correlated-agreement error of each fold, and
`(1 - δ + #folds · loss) ^ numQueries` for the queries, minimized over the proximity loss
`loss ≥ 0`. It depends on the inputs' heights only. -/
noncomputable def friErrorWith (S : Setup EF lookups) (heights : List ℕ) (δ : NNReal) : ENNReal :=
  FriGame.error S.domain (S.friRounds (fun _ _ ↦ 0) heights)
    (2 ^ S.params.logFinalPolyLen) S.params.numQueries δ

/-- FRI's soundness error at proximity `δ`. -/
noncomputable def friError (S : Setup EF lookups) (δ : NNReal) : ENNReal := friErrorWith S [] δ

/-- The knowledge error, for FRI at proximity `δ` and the extractor at `δ' ≥ δ`. -/
noncomputable def knowledgeError (S : Setup EF lookups) (δ δ' : NNReal) : ENNReal :=
  foldingError S δ' + outOfDomainError S δ' + batchingError S δ δ' +
    friError S δ

/-- The rate at every trace length is the statement's. -/
theorem Statement.rate_setupAt (C : Statement F) (n : Nat) (h : C.Admits n)
    (hf : C.params.logFinalPolyLen < n) : (C.setupAt EF n h hf).rate = C.rate := by
  rw [Setup.rate, Setup.n, Setup.size, pow_add, Statement.rate]
  push_cast
  field_simp
  rfl

end CompStark.Iop
