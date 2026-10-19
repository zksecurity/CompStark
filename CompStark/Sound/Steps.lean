/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.SoundnessError

/-! # The steps of the soundness proof

`knowledgeSoundness` follows from four facts, stated here as propositions and proved in their
own files:

* `FriStep`: FRI rejects words far from the code (ArkLib's FRI soundness).
* `BatchingStep`: batching by powers keeps summands that are not near on a common set far, except
  for few `a` (mutual correlated agreement).
* `DecodingStep`: if the DEEP summands are near on a common set and `ζ` lies off `L` and the
  trace domain, the claimed values are those of a candidate trace and quotient.
* `AlgebraStep`: if a candidate trace fails the AIR, the constraint check at `ζ` passes for few
  `(α, ζ)`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

local notation "𝔽" => KoalaBear.Field
local notation "𝕂" => KoalaBear.Ext4
local notation "F" => KoalaBear.Fast.Field

/-- A word agrees with a codeword of `S.code` on at least `(1 - δ) N` points. -/
def Near (S : Setup) (δ : ℝ) (w : S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧ ∃ u ∈ S.code, ∀ i ∈ T, w i = u i

/-- The DEEP quotient of a word `f` with claimed value `y` at `z`: `(y - f(x)) / (z - x)`. -/
noncomputable def deepComponent (S : Setup) (f : S.Point → 𝔽) (z y : 𝕂) : S.Point → 𝕂 :=
  fun i ↦ (y - algebraMap 𝔽 𝕂 (f i)) / (z - S.domain i)

/-- `ζ` lies neither on `L` nor on the trace domain `H = ⟨ω_n⟩`: the DEEP quotients'
denominators `ζ - x`, `ζ ω_n - x` (`x ∈ L`) and the check's `Z_H(ζ)`, `ζ - 1`, `ζ - ω_n⁻¹` are
nonzero. -/
def OffDomain (S : Setup) (ζ : 𝕂) : Prop :=
  (∀ i : S.Point, ζ ≠ S.domain i) ∧ ζ ^ S.n ≠ 1

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
def FriStep (S : Setup) : Prop :=
  ∀ (δ : NNReal) (w : S.Point → 𝕂), ¬ Near S δ w → friAcceptance S w ≤ friError S δ

/-- FRI accepts with probability at most `1`. -/
def FriAtMostOne (S : Setup) : Prop := ∀ w : S.Point → 𝕂, friAcceptance S w ≤ 1

/-- Words are near the code on a common set of at least `(1 - δ) N` points. -/
def NearTogether (S : Setup) {ι : Type} (δ : ℝ) (ws : ι → S.Point → 𝕂) : Prop :=
  ∃ T : Finset S.Point, (T.card : ℝ) ≥ S.size * (1 - δ) ∧
    ∀ k, ∃ u ∈ S.code, ∀ i ∈ T, ws k i = u i

open Classical in
/-- If `numOpened` words are not near the code on a common set, their combination by the powers
of a uniform `a` is `δ`-near the code with probability at most `batchingError` (mutual
correlated agreement). -/
def BatchingStep (S : Setup) : Prop :=
  ∀ (δ : NNReal) (ws : Fin S.numOpened → S.Point → 𝕂), ¬ NearTogether S δ ws →
    ((Finset.univ.filter fun a : 𝕂 ↦
        Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * ws k i).card : ENNReal)
      / Fintype.card 𝕂 ≤ batchingError S δ

/-- The claimed values of polynomials `trace` and `quotient`: the true ones at `ζ`. -/
noncomputable def trueOpenings (S : Setup) (trace : Fin S.air.width → 𝔽[X])
    (quotient : Fin S.chunks → Fin 4 → 𝔽[X]) (ζ : 𝕂) : Openings S where
  traceAt j := aeval ζ (trace j)
  traceNext j := aeval (ζ * rootOfUnity S.logN) (trace j)
  quotientAt c e := aeval ζ (quotient c e)

/-- The DEEP components of the opened words, by position. -/
noncomputable def components {S : Setup} (p : Prover S) (α ζ : 𝕂) :
    Fin S.numOpened → S.Point → 𝕂 := fun k ↦
  let w := (openedWords p α ζ)[k.val]'(by
    have : (openedWords p α ζ).length = S.numOpened := by
      simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
        List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
      ring
    rw [this]; exact k.isLt)
  deepComponent S w.1 w.2.1 w.2.2

/-- If the DEEP components of the opened words are `δ`-near the code on a common set, `δ` below
`1 - rate` and `ζ` off `L` and the trace domain, the claimed values are those of polynomials of
degree at most `n` that agree with the trace and quotient words on a common set of `(1 - δ) N`
points: a candidate trace and quotient of the list decoding. -/
def DecodingStep (S : Setup) : Prop :=
  ∀ (δ : NNReal), (δ : ℝ) < 1 - S.rate → ∀ (prover : Prover S) (α ζ : 𝕂), OffDomain S ζ →
    NearTogether S δ (components prover α ζ) →
    ∃ (trace : Fin S.air.width → 𝔽[X]) (quotient : Fin S.chunks → Fin 4 → 𝔽[X]),
      (∀ j, (trace j).natDegree ≤ S.n) ∧ Agree S δ prover.trace trace ∧
      (∀ c e, (quotient c e).natDegree ≤ S.n) ∧
      Agree S δ (fun ce : Fin S.chunks × Fin 4 ↦ prover.quotient α ce.1 ce.2)
        (fun ce ↦ quotient ce.1 ce.2) ∧
      prover.openings α ζ = trueOpenings S trace quotient ζ

open Classical in
/-- If the trace of polynomials `trace` fails the AIR, then for all but `#constraints - 1` values
of `α`, whatever the quotient's polynomials, the constraints hold at at most `identityDegree`
values of `ζ` off `L` and the trace domain, with the true values. -/
def AlgebraStep (S : Setup) : Prop :=
  ∀ (publicValues : List F) (trace : Fin S.air.width → 𝔽[X]),
    (∀ j, (trace j).natDegree ≤ S.n) →
    ¬ S.air.Satisfied S.logN (traceOf S trace) publicValues →
    ∃ bad : Finset 𝕂, bad.card ≤ S.air.constraints.length - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin 4 → 𝔽[X], (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S trace quotient ζ)).card ≤
          S.identityDegree

end CompStark.Sound
