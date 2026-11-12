/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.PhasePolynomials

/-! # Deterministic boundaries between the Keccak GKR phases -/

@[expose] public section
open Polynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Shifting a position by zero leaves it unchanged. -/
theorem along_zero (j : Fin 1600) : along j 0 = j := by
  apply Fin.ext
  simp only [along, Nat.add_zero, Nat.mod_mod]
  have hq : j.val / 64 < 25 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simp)
  omega

/-- At an empty prefix a residual is the ordinary Boolean cube sum. -/
theorem residualSum_zero {E : Type*} [CommRing E] {n : Nat}
    (f : (Fin n → E) → E) (point : Fin n → E) :
    residualSum f point 0 = ∑ b : Fin (2^n), f (cubePoint b) := by
  simp only [residualSum, Nat.sub_zero, Nat.not_lt_zero, ite_false]
  rfl

/-- On Boolean points the equality kernel is the corresponding cube weight. -/
theorem eqEval_cubePoint {E : Type*} [CommRing E] {n : Nat}
    (r : Fin n → E) (b : Fin (2^n)) : eqEval r (cubePoint b) = eqWeight r b.val := by
  unfold eqEval eqWeight cubePoint
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp

/-- Evaluating the RMFE is the weighted sum of the sixteen column evaluations. -/
theorem kemb_eval {E : Type*} [CommRing E] [CharP E 2]
    (a : Fin 16 → E) (s : E) : (Embedding.kemb a).eval s = ∑ i, muAt s i * a i := by
  simp only [Embedding.kemb, LinearMap.coe_mk, AddHom.coe_mk, eval_finsetSum,
    eval_smul, smul_eq_mul, muAt_eq_eval, mul_comm]

/-- The joint pack cube selects its exact committed segment and pack. -/
theorem packTable_encode {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (j : Fin 1600) (m : Fin 2) (b : Fin (2^p)) :
    packTable q d s j ⟨b.val+2^p*m.val,by
      rw [pow_succ]
      have hm : m.val = 0 ∨ m.val = 1 := by omega
      rcases hm with hm | hm <;> simp only [hm, Nat.mul_zero, Nat.mul_one, Nat.add_zero] <;> omega⟩ = (packedLinear q d m b j).eval s := by
  unfold packTable
  congr 2
  · apply Fin.ext
    simp only [Nat.add_mul_div_left _ _ (by positivity : 0 < 2^p), Nat.div_eq_of_lt b.isLt, Nat.zero_add]
  · apply Fin.ext
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]

/-- The pack-and-segment initial residual is the honest product evaluation. -/
theorem pack_start_identity {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E) (r : Fin (p+1) → E) :
    residualSum (packSummand q d c s) r 0 = (honestProduct q d c).eval s := by
  rw [residualSum_zero]
  simp only [packSummand, eqEval_cubePoint, linearAtPack_eq_mle, mle_cubePoint]
  rw [cube_sum]
  simp only [packTable_encode, Finset.mul_sum, honestProduct, eval_finsetSum,
    eval_smul, smul_eq_mul, eval_add, eval_mul, kemb_eval, mul_one]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Position sums over the zero-padded cube reduce to the real 1600 positions. -/
theorem position_start_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p)
    (r : Fin 11 → E) :
    residualSum (positionSummand q d c t) r 0 = packSummand q d c t.point t.packPoint := by
  rw [residualSum_zero]
  simp only [positionSummand, shiftedEvaluation, mle_cubePoint]
  change (∑ b : Fin (1600+448), _) = _
  rw [Fin.sum_univ_add (a := 1600) (b := 448)]
  have hlow (j : Fin 1600) : (Fin.castAdd 448 j).val < 1600 := j.isLt
  have hhigh (j : Fin 448) : ¬ (Fin.natAdd 1600 j).val < 1600 := by
    simp only [Fin.val_natAdd]; omega
  simp only [hlow, hhigh, dite_true, dite_false, mul_zero, add_zero, Finset.sum_const_zero,
    packSummand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Fin.val_castAdd, Fin.eta, along_zero]
  ring

/-- The initial middle-opening residual is the honest weighted middle claim. -/
theorem word_start_identity {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (r : Fin 6 → E) :
    residualSum (wordSummand x q t) r 0 =
      (1-t.segment) * ∑ l : Fin 25, eqWeight t.lanePoint l.val * middleWord x q t ⟨25+l.val,by omega⟩ := by
  rw [residualSum_zero]
  simp only [wordSummand, mle_cubePoint]
  change (∑ b : Fin (25+39), _) = _
  rw [Fin.sum_univ_add (a := 25) (b := 39)]
  have hlow (i : Fin 25) : ¬ (25 ≤ (Fin.castAdd 39 i).val ∧ (Fin.castAdd 39 i).val < 50) := by
    simp only [Fin.val_castAdd]; omega
  simp only [hlow, dite_false, zero_mul, Finset.sum_const_zero, zero_add]
  rw [Fin.sum_univ_add (a := 25) (b := 14)]
  have hmid (i : Fin 25) : 25 ≤ 25+i.val ∧ 25+i.val < 50 := by omega
  have hhigh (i : Fin 14) : ¬ (25 ≤ 25+(25+i.val) ∧ 25+(25+i.val) < 50) := by omega
  simp only [hmid, hhigh, true_and, dite_true, dite_false, zero_mul, Finset.sum_const_zero, add_zero,
    Fin.val_natAdd, Fin.val_castAdd, Nat.add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hs : Fin.natAdd 25 (Fin.castAdd 14 i) = (⟨25+i.val,by omega⟩ : Fin 64) := by
    apply Fin.ext; simp only [Fin.val_natAdd, Fin.val_castAdd]
  rw [hs]
  ring

end CompStark.Keccak.Gkr
