/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.PositionHonest
public import CompStark.Keccak.GkrProver.Cofactor
public import CompStark.Keccak.GkrProver.PackedTableContraction

/-! Honest cofactor semantics of the retained native pack table and claim-based reconstruction. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64 Polynomial
open scoped BigOperators

/-- The weighted native chi cofactor on all remaining pack-table coordinates. -/
noncomputable def packTableCofactor (table : PackedE) (weights : Array W) (n : Nat)
    (scale kappa : W) (point : Fin n → W) : W :=
  scale*∑ j : Fin 1600,weights[j.val]! *
    (kappa*mle (fun row : Fin (2^n) => table.toArray[row.val*1600+j.val]!) point +
      (kappa+mle (fun row : Fin (2^n) => table.toArray[row.val*1600+shift j.val 1]!) point)*
        mle (fun row : Fin (2^n) => table.toArray[row.val*1600+shift j.val 2]!) point)

/-- The multivariate polynomial represented by the native retained pack factors. -/
noncomputable def packTablePolynomial (table : PackedE) (weights : Array W) (n : Nat)
    (scale kappa : W) : MvPolynomial (Fin n) W :=
  MvPolynomial.C scale * ∑ j : Fin 1600,MvPolynomial.C weights[j.val]! *
    chiPolynomial kappa (fun k => MvPolynomial.MLE' (fun row : Fin (2^n) =>
      table.toArray[row.val*1600+shift j.val k.val]!))

/-- The native pack-factor polynomial evaluates to its exact weighted chi cofactor. -/
theorem packTablePolynomial_eval (table : PackedE) (weights : Array W) (n : Nat)
    (scale kappa : W) (point : Fin n → W) :
    MvPolynomial.eval point (packTablePolynomial table weights n scale kappa) =
      packTableCofactor table weights n scale kappa point := by
  simp only [packTablePolynomial,packTableCofactor,chiPolynomial,map_mul,map_add,map_sum,
    MvPolynomial.eval_C,mle_eq_eval,Fin.val_zero,Fin.val_one]
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro j _
  have hz : shift j.val 0 = j.val := by
    change (along j 0).val = j.val
    rw [along_zero]
  simp only [hz]
  rfl

/-- The native equality-free pack cofactor has coordinate degree at most two. -/
theorem packTableCofactor_degree (table : PackedE) (weights : Array W) (n : Nat)
    (scale kappa : W) : CoordinateDegree (packTableCofactor table weights n scale kappa) 2 := by
  have hpoly : ∀ i,(packTablePolynomial table weights n scale kappa).degreeOf i ≤ 2 := by
    intro i
    unfold packTablePolynomial
    apply (coordinate_mul_degree _ _ i (a := 0) (b := 2)
      (by simp only [MvPolynomial.degreeOf_C,le_refl]) ?_).trans (by decide)
    apply coordinate_sum_degree
    intro j
    simpa only [zero_add] using coordinate_mul_degree _ _ i
      (show (MvPolynomial.C weights[j.val]! : MvPolynomial (Fin n) W).degreeOf i ≤ 0 by
        simp only [MvPolynomial.degreeOf_C,le_refl])
      (chiPolynomial_degree _ _ i (fun _ => tablePolynomial_degree _ i))
  simpa only [packTablePolynomial_eval] using coordinateDegree_eval
    (packTablePolynomial table weights n scale kappa) hpoly

/-- Folding the retained pack factors binds exactly their first multilinear coordinate. -/
theorem packTableCofactor_fold (table : PackedE) (weights : Array W) (n : Nat) (scale kappa r : W)
    (ht : table.size = 2^(n+1)*1600) (point : Fin n → W) :
    packTableCofactor (foldPacked table 1600 r) weights n scale kappa point =
      packTableCofactor table weights (n+1) scale kappa (Fin.cons r point) := by
  unfold packTableCofactor
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro j _
  rw [foldPacked_column_mle table ht r point j]
  have h1 : shift j.val 1 < 1600 := (along j 1).isLt
  have h2 : shift j.val 2 < 1600 := (along j 2).isLt
  rw [foldPacked_column_mle table ht r point ⟨shift j.val 1,h1⟩,
    foldPacked_column_mle table ht r point ⟨shift j.val 2,h2⟩]

/-- The bounded univariate cofactor authored by the native pack coefficient kernel. -/
noncomputable def packRoundPolynomial (table : PackedE) (weights suffix : Array W) (scale kappa : W) : W⦃≤ 2⦄[X] :=
  ⟨messagePolynomial (fun k : Fin 3 => scale*(packRound table weights (packConstants weights kappa)
    (eqTable suffix))[k.val]!),Polynomial.mem_degreeLE.mpr (messagePolynomial_degree _)⟩

/-- The native pack coefficient polynomial evaluates to its exact suffix-weighted affine chi sum. -/
theorem packRoundPolynomial_eval (table : PackedE) (weights suffix : Array W) (scale kappa r : W) :
    (packRoundPolynomial table weights suffix scale kappa).val.eval r =
      scale*∑ row ∈ Finset.range (table.size/3200),(eqTable suffix)[row]! *
        ∑ j : Fin 1600, weights[j.val]! *
          (kappa*line (table.get (3200*row+j.val)) (table.get (3200*row+1600+j.val)) r +
            (kappa+line (table.get (3200*row+shift j.val 1)) (table.get (3200*row+1600+shift j.val 1)) r)*
              line (table.get (3200*row+shift j.val 2)) (table.get (3200*row+1600+shift j.val 2)) r) := by
  change (messagePolynomial (fun k : Fin 3 => scale*(packRound table weights
    (packConstants weights kappa) (eqTable suffix))[k.val]!)).eval r = _
  rw [messagePolynomial_eval]
  have hscale : polyEval (fun k : Fin 3 => scale*(packRound table weights
      (packConstants weights kappa) (eqTable suffix))[k.val]!) r =
      scale*polyEval (fun k : Fin 3 => (packRound table weights (packConstants weights kappa)
        (eqTable suffix))[k.val]!) r := by
    simp only [polyEval,Finset.mul_sum,mul_assoc]
  rw [hscale,packRound_eval]
  apply congrArg (fun value : W => scale*value)
  apply Finset.sum_congr rfl
  intro row _
  rw [packRow_chi]

/-- The native retained-table cofactor polynomial is the exact honest remaining Boolean projection. -/
theorem packRoundPolynomial_first (table : PackedE) (weights suffix : Array W) (scale kappa r : W)
    (ht : table.size = 2^(suffix.size+1)*1600) :
    (packRoundPolynomial table weights suffix scale kappa).val.eval r =
      booleanSum (fun rest => eqEval (fun k : Fin suffix.size => suffix[k.val]!) rest *
        packTableCofactor table weights (suffix.size+1) scale kappa (Fin.cons r rest)) := by
  have heq : (fun rest => eqEval (fun k : Fin suffix.size => suffix[k.val]!) rest *
      packTableCofactor table weights (suffix.size+1) scale kappa (Fin.cons r rest)) =
      (fun rest => eqEval (fun k : Fin suffix.size => suffix[k.val]!) rest *
        packTableCofactor (foldPacked table 1600 r) weights suffix.size scale kappa rest) := by
    funext rest
    rw [packTableCofactor_fold table weights suffix.size scale kappa r ht]
  rw [heq,booleanSum_eq_residual _ (fun _ => 0),residualSum_zero]
  simp only [packTableCofactor,mle_cubePoint,eqEval_cubePoint]
  rw [packRoundPolynomial_eval,ht,show 2^(suffix.size+1)*1600/3200 = 2^suffix.size by
    rw [pow_succ]; omega]
  rw [Fin.sum_univ_eq_sum_range (fun row =>
    eqWeight (fun k : Fin suffix.size => suffix[k.val]!) row *
      (scale*∑ j : Fin 1600,weights[j.val]! *
        (kappa*(foldPacked table 1600 r).toArray[row*1600+j.val]! +
          (kappa+(foldPacked table 1600 r).toArray[row*1600+shift j.val 1]!)*
            (foldPacked table 1600 r).toArray[row*1600+shift j.val 2]!))) (2^suffix.size),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row hr
  have hr := Finset.mem_range.mp hr
  rw [eqTable_get suffix row hr]
  have hlen : (foldPacked table 1600 r).size = 2^suffix.size*1600 := by
    rw [foldPacked_size,ht,pow_succ]
    omega
  have hcell (j : Fin 1600) : (foldPacked table 1600 r).toArray[row*1600+j.val]! =
      line (table.get (3200*row+j.val)) (table.get (3200*row+1600+j.val)) r := by
    have hb : row*1600+j.val < (foldPacked table 1600 r).size := by rw [hlen]; exact row_index_lt j.isLt ⟨row,hr⟩
    rw [PackedE.get_toArray _ _ hb,foldPacked_get _ _ _ _ (by rwa [foldPacked_size] at hb)]
    have hd : (row*1600+j.val)/1600 = row := by have := j.isLt; omega
    have hm : (row*1600+j.val)%1600 = j.val := by have := j.isLt; omega
    rw [hd,hm,show 2*row*1600 = 3200*row by omega,
      show 3200*row+j.val+1600 = 3200*row+1600+j.val by omega]
  have hsum : (∑ j : Fin 1600,weights[j.val]! *
      (kappa*(foldPacked table 1600 r).toArray[row*1600+j.val]! +
        (kappa+(foldPacked table 1600 r).toArray[row*1600+shift j.val 1]!)*
          (foldPacked table 1600 r).toArray[row*1600+shift j.val 2]!)) =
      ∑ j : Fin 1600,weights[j.val]! *
        (kappa*line (table.get (3200*row+j.val)) (table.get (3200*row+1600+j.val)) r +
          (kappa+line (table.get (3200*row+shift j.val 1)) (table.get (3200*row+1600+shift j.val 1)) r)*
            line (table.get (3200*row+shift j.val 2)) (table.get (3200*row+1600+shift j.val 2)) r) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcell j,hcell ⟨shift j.val 1,(along j 1).isLt⟩,hcell ⟨shift j.val 2,(along j 2).isLt⟩]
  rw [hsum]
  ring

/-- The native coefficient polynomial is the specification's honest cofactor at the actual suffix point. -/
theorem packRoundPolynomial_honest (table : PackedE) (weights suffix : Array W) (scale kappa : W)
    (ht : table.size = 2^(suffix.size+1)*1600) :
    honestCofactorPolynomial (packTableCofactor table weights (suffix.size+1) scale kappa)
      (packTableCofactor_degree table weights (suffix.size+1) scale kappa)
      (fun k : Fin suffix.size => suffix[k.val]!) = packRoundPolynomial table weights suffix scale kappa := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 2 < Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  exact honestCofactorPolynomial_eq (packTableCofactor table weights (suffix.size+1) scale kappa)
    (packTableCofactor_degree table weights (suffix.size+1) scale kappa) _ hcard
    (packRoundPolynomial table weights suffix scale kappa)
    (fun r => packRoundPolynomial_first table weights suffix scale kappa r ht)

/-- Each native cofactor-polynomial coefficient is its scaled production coefficient. -/
theorem packRoundPolynomial_coeff (table : PackedE) (weights suffix : Array W) (scale kappa : W) (k : Fin 3) :
    (packRoundPolynomial table weights suffix scale kappa).val.coeff k.val =
      scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[k.val]! :=
  messagePolynomial_coeff _ k

/-- The exact equality-weighted remaining sum discharges the claim-reconstruction precondition. -/
theorem packRound_running_sum (table : PackedE) (weights suffix : Array W) (entering scale kappa : W)
    (ht : table.size = 2^(suffix.size+1)*1600) :
    booleanSum (fun point => eqEval (Fin.cons entering (fun k : Fin suffix.size => suffix[k.val]!)) point *
      packTableCofactor table weights (suffix.size+1) scale kappa point) =
        scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[0]! +
          entering*(scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[1]!+
            scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[2]!) := by
  have hsum := honestCofactorPolynomial_sum (packTableCofactor table weights (suffix.size+1) scale kappa)
    (packTableCofactor_degree table weights (suffix.size+1) scale kappa)
    (Fin.cons entering (fun k : Fin suffix.size => suffix[k.val]!))
  simp only [Fin.cons_zero,Fin.cons_succ] at hsum
  rw [packRoundPolynomial_honest table weights suffix scale kappa ht] at hsum
  have h0 := packRoundPolynomial_coeff table weights suffix scale kappa (0 : Fin 3)
  have h1 := packRoundPolynomial_coeff table weights suffix scale kappa (1 : Fin 3)
  have h2 := packRoundPolynomial_coeff table weights suffix scale kappa (2 : Fin 3)
  simp only [Fin.val_zero,Fin.val_one,show (2 : Fin 3).val = 2 from rfl] at h0 h1 h2
  rw [h0,h1,h2] at hsum
  exact hsum

/-- The native claim-based pack kernel is exact for the full remaining equality-weighted cofactor sum. -/
theorem packRoundFromClaim_refines (table : PackedE) (weights suffix : Array W) (entering scale kappa value : W)
    (ht : table.size = 2^(suffix.size+1)*1600)
    (hv : value = booleanSum (fun point => eqEval (Fin.cons entering (fun k : Fin suffix.size => suffix[k.val]!)) point *
      packTableCofactor table weights (suffix.size+1) scale kappa point)) :
    packRoundFromClaim table weights (packConstants weights kappa) (eqTable suffix) entering scale value =
      (packRound table weights (packConstants weights kappa) (eqTable suffix)).map (scale*·) := by
  apply packRoundFromClaim_eq
  exact hv.trans (packRound_running_sum table weights suffix entering scale kappa ht)

/-- The native cofactor polynomial has the exact scaled Horner evaluation used by the layer loop. -/
theorem packRoundPolynomial_horner (table : PackedE) (weights suffix : Array W) (scale kappa r : W) :
    (packRoundPolynomial table weights suffix scale kappa).val.eval r =
      scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[0]! +
        r*(scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[1]!+
          r*(scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[2]!)) := by
  rw [quadratic_polynomial_eval]
  have h0 := packRoundPolynomial_coeff table weights suffix scale kappa (0 : Fin 3)
  have h1 := packRoundPolynomial_coeff table weights suffix scale kappa (1 : Fin 3)
  have h2 := packRoundPolynomial_coeff table weights suffix scale kappa (2 : Fin 3)
  simp only [Fin.val_zero,Fin.val_one,show (2 : Fin 3).val = 2 from rfl] at h0 h1 h2
  rw [h0,h1,h2]
  ring

/-- A common scalar multiplies the full native pack cofactor without changing its factor tables. -/
theorem packTableCofactor_scale (table : PackedE) (weights : Array W) (n : Nat)
    (a scale kappa : W) (point : Fin n → W) :
    packTableCofactor table weights n (a*scale) kappa point =
      a*packTableCofactor table weights n scale kappa point := by
  unfold packTableCofactor
  rw [mul_assoc]

/-- The production pack claim update preserves the exact remaining sum after folding its factors. -/
theorem packRoundFromClaim_update (table : PackedE) (weights suffix : Array W)
    (entering scale kappa value r : W) (ht : table.size = 2^(suffix.size+1)*1600)
    (hv : value = booleanSum (fun point => eqEval (Fin.cons entering (fun k : Fin suffix.size => suffix[k.val]!)) point *
      packTableCofactor table weights (suffix.size+1) scale kappa point)) :
    let coefficients := packRoundFromClaim table weights (packConstants weights kappa) (eqTable suffix)
      entering scale value
    (1+entering+r)*(coefficients[0]!+r*(coefficients[1]!+r*coefficients[2]!)) =
      booleanSum (fun point => eqEval (fun k : Fin suffix.size => suffix[k.val]!) point *
        packTableCofactor (foldPacked table 1600 r) weights suffix.size ((1+entering+r)*scale) kappa point) := by
  rw [packRoundFromClaim_refines table weights suffix entering scale kappa value ht hv]
  have hget (k : Nat) (hk : k < 3) :
      ((packRound table weights (packConstants weights kappa) (eqTable suffix)).map (scale*·))[k]! =
        scale*(packRound table weights (packConstants weights kappa) (eqTable suffix))[k]! := by
    rw [getElem!_pos _ _ (by rw [Array.size_map,packRound_size]; exact hk),Array.getElem_map,
      ← getElem!_pos _ _ (by rw [packRound_size]; exact hk)]
  simp only [hget 0 (by decide),hget 1 (by decide),hget 2 (by decide)]
  rw [← packRoundPolynomial_horner,packRoundPolynomial_first table weights suffix scale kappa r ht]
  simp only [booleanSum,packTableCofactor_scale,
    packTableCofactor_fold table weights suffix.size scale kappa r ht,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro point _
  ring

end CompStark.Keccak.GkrProver
