/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticValues

/-! Honest coefficient identification for paired-row quadratic opening messages. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64
open scoped BigOperators

/-- The multilinear factor products represented by a row-major pair of opening buffers. -/
noncomputable def quadraticSummand (a b : Array W) (width n : Nat) (scale : W)
    (point : Fin n → W) : W :=
  scale*∑ c : Fin width,
    mle (fun row : Fin (2^n) => a[row.val*width+c.val]!) point *
      mle (fun row : Fin (2^n) => b[row.val*width+c.val]!) point

/-- The bounded multivariate polynomial of the paired opening-factor interpolations. -/
noncomputable def quadraticSummandPolynomial (a b : Array W) (width n : Nat) (scale : W) :
    MvPolynomial (Fin n) W :=
  MvPolynomial.C scale*∑ c : Fin width,
    MvPolynomial.MLE' (fun row : Fin (2^n) => a[row.val*width+c.val]!) *
      MvPolynomial.MLE' (fun row : Fin (2^n) => b[row.val*width+c.val]!)

/-- The opening-factor polynomial evaluates to the concrete quadratic summand. -/
theorem quadraticSummandPolynomial_eval (a b : Array W) (width n : Nat) (scale : W)
    (point : Fin n → W) :
    MvPolynomial.eval point (quadraticSummandPolynomial a b width n scale) =
      quadraticSummand a b width n scale point := by
  simp only [quadraticSummandPolynomial,quadraticSummand,map_mul,map_sum,MvPolynomial.eval_C,mle_eq_eval]

/-- Every opening-factor coordinate has degree at most two. -/
theorem quadraticSummand_degree (a b : Array W) (width n : Nat) (scale : W) :
    CoordinateDegree (quadraticSummand a b width n scale) 2 := by
  have hpoly : ∀ i, (quadraticSummandPolynomial a b width n scale).degreeOf i ≤ 2 := by
    intro i
    unfold quadraticSummandPolynomial
    apply (coordinate_mul_degree _ _ i (a := 0) (b := 2)
      (by simp only [MvPolynomial.degreeOf_C,le_refl]) ?_).trans (by decide)
    apply coordinate_sum_degree
    intro c
    exact coordinate_mul_degree _ _ i (tablePolynomial_degree _ i) (tablePolynomial_degree _ i)
  simpa only [quadraticSummandPolynomial_eval] using
    coordinateDegree_eval (quadraticSummandPolynomial a b width n scale) hpoly

/-- Folding the native factors binds exactly the first coordinate of their full quadratic summand. -/
theorem quadraticSummand_fold (a b : Array W) (width n : Nat) (scale r : W)
    (ha : a.size = 2^(n+1)*width) (hab : a.size = b.size) (point : Fin n → W) :
    quadraticSummand (fold a width r) (fold b width r) width n scale point =
      quadraticSummand a b width (n+1) scale (Fin.cons r point) := by
  unfold quadraticSummand
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro c _
  rw [fold_column_mle a ha,fold_column_mle b (hab.symm.trans ha)]

/-- The Boolean sum of the complete quadratic summand is its exact native table dot product. -/
theorem quadraticSummand_booleanSum (a b : Array W) (width n : Nat) (scale : W)
    (ha : a.size = 2^n*width) :
    booleanSum (quadraticSummand a b width n scale) = quadraticTableValue a b scale := by
  rw [booleanSum_eq_residual _ (fun _ => 0),residualSum_zero]
  simp only [quadraticSummand,mle_cubePoint]
  rw [← Finset.mul_sum]
  unfold quadraticTableValue
  rw [ha,range_sum_blocks]
  apply congrArg (fun value : W => scale*value)
  rw [Fin.sum_univ_eq_sum_range (fun i => ∑ c : Fin width,
    a[i*width+c.val]!*b[i*width+c.val]!) (2^n)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_eq_sum_range (fun j => a[i*width+j]!*b[i*width+j]!) width]
  simp only [Nat.mul_comm]

/-- A bound quadratic summand is the exact polynomial evaluated by the native coefficient loop. -/
theorem quadraticSummand_first (a b : Array W) (width n : Nat) (scale r : W)
    (ha : a.size = 2^(n+1)*width) (hab : a.size = b.size) :
    booleanSum (fun rest => quadraticSummand a b width (n+1) scale (Fin.cons r rest)) =
      quadraticRoundSum a b width scale r := by
  rw [← quadraticTableValue_fold a b width scale r hab]
  rw [← quadraticSummand_booleanSum (fold a width r) (fold b width r) width n scale (by
    rw [fold_rows_size,ha,pow_succ,Nat.mul_assoc]
    by_cases hw : width = 0
    · subst width; simp only [Nat.mul_zero,Nat.zero_div]
    · rw [Nat.mul_div_cancel _ (by omega)])]
  apply congrArg booleanSum
  funext rest
  exact (quadraticSummand_fold a b width n scale r ha hab rest).symm

/-- Native opening coefficients are the specification's honest compressed quadratic message. -/
theorem quadraticCoefficients_honest (a b : Array W) (width n : Nat) (scale : W)
    (ha : a.size = 2^(n+1)*width) (hab : a.size = b.size)
    (hf : CoordinateDegree (quadraticSummand a b width (n+1) scale) 2) :
    quadraticMessage (quadraticCoefficients a b width scale).1
      (quadraticCoefficients a b width scale).2 =
        Sumcheck.compress (firstHonestPolynomial (quadraticSummand a b width (n+1) scale) hf) := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 2 < Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  let coefficients := quadraticCoefficients a b width scale
  let message := quadraticMessage coefficients.1 coefficients.2
  have heq := firstHonestPolynomial_eq (quadraticSummand a b width (n+1) scale) hf hcard
    (Sumcheck.compressed (quadraticBooleanSum a b width scale) message) (by
      intro r
      rw [← Sumcheck.compressed_evaluate_eq,quadraticSummand_first a b width n scale r ha hab]
      rw [show (Sumcheck.compressedOps 1).evaluate (quadraticBooleanSum a b width scale) message r =
          coefficients.1+r*(quadraticBooleanSum a b width scale+coefficients.2+r*coefficients.2) by
        simp only [Sumcheck.compressedOps,message,quadraticMessage,Fin.sum_univ_one,
          Fin.val_zero,Nat.zero_add,CharTwo.sub_eq_add,show (2 : W) = 0 from CharP.cast_eq_zero W 2,
          zero_mul,add_zero]
        ring]
      exact quadraticCoefficients_decode a b width scale r)
  rw [heq,Sumcheck.compress_compressed]

end CompStark.Keccak.GkrProver
