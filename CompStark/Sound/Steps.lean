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
* `BatchingStep`: batching by powers keeps summands that are not `δ'`-near on a common set
  `δ`-far, except for few `a` (correlated agreement).
* `DecodingStep`: if the DEEP summands are near on a common set and `ζ` lies off the trace
  domain, the claimed values are those of a candidate trace and quotient.
* `AlgebraStep`: if a candidate trace fails the AIR, the constraint check at `ζ` passes for few
  `(α, ζ)`.
-/

@[expose] public section
namespace CompStark.Sound
open CompStark.Stark CompStark.Iop Polynomial

variable {F : Type} [BaseField F] {EF : Type} [Challenge F EF]

local notation "𝕂" => Challenge.Spec EF

/-- The DEEP quotient of a word `f` with claimed value `y` at `z`: `(y - f(x)) / (z - x)`. -/
noncomputable def deepComponent (S : Setup EF) (f : S.Point → F) (z y : 𝕂) : S.Point → 𝕂 :=
  fun i ↦ (y - algebraMap F 𝕂 (f i)) / (z - S.domain i)

/-- `ζ` lies off the trace domain `H = ⟨ω_n⟩`: the check's denominators `Z_H(ζ)`, `ζ - 1`,
`ζ - ω_n⁻¹` are nonzero. -/
def OffTraceDomain (S : Setup EF) (ζ : 𝕂) : Prop := ζ ^ S.n ≠ 1

/-- FRI accepts a word that is not `δ`-near the code with probability at most `friError`. -/
def FriStep (S : Setup EF) : Prop :=
  ∀ (δ : NNReal) (w : S.Point → 𝕂), ¬ Near S δ w → friAcceptance S w ≤ friError S δ

/-- FRI accepts with probability at most `1`. -/
def FriAtMostOne (S : Setup EF) : Prop := ∀ w : S.Point → 𝕂, friAcceptance S w ≤ 1

open Classical in
/-- If `numOpened` words are not near the code on a common set at radius `δ'`, their combination
by the powers of a uniform `a` is `δ`-near the code with probability at most `batchingError`. -/
def BatchingStep (S : Setup EF) : Prop :=
  ∀ (δ : NNReal) (δ' : ℝ) (ws : Fin S.numOpened → S.Point → 𝕂), ¬ NearTogether S δ' ws →
    ((Finset.univ.filter fun a : 𝕂 ↦
        Near S δ fun i ↦ ∑ k : Fin S.numOpened, a ^ (k : Nat) * ws k i).card : ENNReal)
      / Fintype.card 𝕂 ≤ batchingError S δ δ'

/-- The preprocessed trace's polynomials have degree below `n`. -/
theorem natDegree_preprocessedPoly_le (S : Setup EF) (j : Nat) :
    (S.preprocessedPoly j).natDegree ≤ S.n := by
  rcases eq_or_ne (S.preprocessedPoly j) 0 with h | h
  · rw [h, natDegree_zero]; exact Nat.zero_le _
  · have := Lagrange.degree_interpolate_lt (s := Finset.range S.n)
      (v := fun i ↦ twoAdicGen (F := F) S.logN ^ i)
      (fun i ↦ S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0) ?_
    · rw [Finset.card_range] at this
      exact ((natDegree_lt_iff_degree_lt h).mpr this).le
    · intro a ha b hb hab
      exact (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
        (by have := S.valid.twoAdic; omega)).pow_inj
        (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab

/-- The preprocessed trace's polynomials take its values on the trace domain. -/
theorem eval_preprocessedPoly (S : Setup EF) (j i : Nat) (hi : i < S.n) :
    (S.preprocessedPoly j).eval (twoAdicGen S.logN ^ i) =
      S.air.preprocessed.getD (i * S.air.preprocessedWidth + j) 0 :=
  Lagrange.eval_interpolate_at_node _
    (fun a ha b hb hab ↦ (BaseField.isPrimitiveRoot_twoAdicGen (F := F) S.logN
      (by have := S.valid.twoAdic; omega)).pow_inj
      (Finset.mem_range.mp ha) (Finset.mem_range.mp hb) hab) (Finset.mem_range.mpr hi)

/-- The claimed values of polynomials `trace` and `quotient`, and of the preprocessed trace's: the
true ones at `ζ`. -/
noncomputable def trueOpenings (S : Setup EF) (trace : Fin S.air.width → F[X])
    (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]) (ζ : 𝕂) : Openings S where
  traceAt j := aeval ζ (trace j)
  traceNext j := aeval (ζ * rootOfUnity S.logN) (trace (Fin.castLE S.air.mainNextWidth_le j))
  quotientAt c e := aeval ζ (quotient c e)
  preprocessedAt j := aeval ζ (S.preprocessedPoly j)
  preprocessedNext j := aeval (ζ * rootOfUnity S.logN) (S.preprocessedPoly j)

/-- The DEEP components of the opened words, by position. -/
noncomputable def components {S : Setup EF} (p : Prover S) (α ζ : 𝕂) :
    Fin S.numOpened → S.Point → 𝕂 := fun k ↦
  let w := (openedWords p α ζ)[k.val]'(by
    have : (openedWords p α ζ).length = S.numOpened := by
      simp only [openedWords, List.length_append, List.length_map, List.length_finRange,
        List.length_flatMap, List.map_const', List.sum_replicate, smul_eq_mul, Setup.numOpened]
      ring
    rw [this]; exact k.isLt)
  deepComponent S w.1 w.2.1 w.2.2

/-- If the DEEP components of the opened words are `(δ - 2/N)`-near the code on a common set, `δ`
below `1 - rate` and `ζ` off the trace domain, the claimed values are those of polynomials of
degree at most `n` that agree with the trace and quotient words on a common set of `(1 - δ) N`
points: a candidate trace and quotient of the list decoding. The two points lost are those where
`ζ` or `ζ ω_n` may meet `L`. -/
def DecodingStep (S : Setup EF) : Prop :=
  ∀ (δ : NNReal), (δ : ℝ) < 1 - S.rate → ∀ (prover : Prover S) (α ζ : 𝕂), OffTraceDomain S ζ →
    NearTogether S ((δ : ℝ) - 2 / S.size) (components prover α ζ) →
    ∃ (trace : Fin S.air.width → F[X]) (quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X]),
      (∀ j, (trace j).natDegree ≤ S.n) ∧ Agree S δ prover.trace trace ∧
      (∀ c e, (quotient c e).natDegree ≤ S.n) ∧
      Agree S δ (fun ce : Fin S.chunks × Fin (Challenge.d EF) ↦ prover.quotient α ce.1 ce.2)
        (fun ce ↦ quotient ce.1 ce.2) ∧
      prover.openings α ζ = trueOpenings S trace quotient ζ

open Classical in
/-- If the trace of polynomials `trace` fails the AIR, then for all but `#constraints - 1` values
of `α`, whatever the quotient's polynomials, the constraints hold at at most `identityDegree`
values of `ζ` off the trace domain, with the true values. -/
def AlgebraStep (S : Setup EF) : Prop :=
  ∀ (publicValues : List F) (trace : Fin S.air.width → F[X]),
    (∀ j, (trace j).natDegree ≤ S.n) →
    ¬ S.air.Satisfied S.logN (traceOf S trace) publicValues →
    ∃ bad : Finset 𝕂, bad.card ≤ S.air.constraints.length - 1 ∧
      ∀ α ∉ bad, ∀ quotient : Fin S.chunks → Fin (Challenge.d EF) → F[X],
        (∀ c e, (quotient c e).natDegree ≤ S.n) →
        (Finset.univ.filter fun ζ : 𝕂 ↦ OffTraceDomain S ζ ∧
          ConstraintsHoldAt S publicValues α ζ (trueOpenings S trace quotient ζ)).card ≤
          S.identityDegree

end CompStark.Sound
