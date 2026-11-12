/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.QuadraticTrace

/-! Honest cubic-message semantics of the native zero-padded position factors. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 100000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr BF64 Polynomial
open scoped BigOperators

/-- The position summand represented by the actual native weight and three shifted factor buffers. -/
noncomputable def positionTableSummand (weights : Array W) (t : Array (Array W))
    (n : Nat) (scale kappa : W) (point : Fin n → W) : W :=
  scale*mle (fun row : Fin (2^n) => weights[row.val]!) point *
    (kappa*mle (fun row : Fin (2^n) => (t[0]!)[row.val]!) point +
      (kappa+mle (fun row : Fin (2^n) => (t[1]!)[row.val]!) point)*
        mle (fun row : Fin (2^n) => (t[2]!)[row.val]!) point)

/-- The multivariate polynomial of the native position factor buffers. -/
noncomputable def positionTablePolynomial (weights : Array W) (t : Array (Array W))
    (n : Nat) (scale kappa : W) : MvPolynomial (Fin n) W :=
  MvPolynomial.C scale * MvPolynomial.MLE' (fun row : Fin (2^n) => weights[row.val]!) *
    chiPolynomial kappa (fun k => MvPolynomial.MLE' (fun row : Fin (2^n) => (t[k.val]!)[row.val]!))

/-- The factor-buffer polynomial evaluates to the complete native position summand. -/
theorem positionTablePolynomial_eval (weights : Array W) (t : Array (Array W))
    (n : Nat) (scale kappa : W) (point : Fin n → W) :
    MvPolynomial.eval point (positionTablePolynomial weights t n scale kappa) =
      positionTableSummand weights t n scale kappa point := by
  simp only [positionTablePolynomial,positionTableSummand,chiPolynomial,map_mul,map_add,
    MvPolynomial.eval_C,mle_eq_eval,Fin.val_zero,Fin.val_one]
  rfl

/-- The complete native position summand has coordinate degree at most three. -/
theorem positionTableSummand_degree (weights : Array W) (t : Array (Array W))
    (n : Nat) (scale kappa : W) : CoordinateDegree (positionTableSummand weights t n scale kappa) 3 := by
  have hpoly : ∀ i, (positionTablePolynomial weights t n scale kappa).degreeOf i ≤ 3 := by
    intro i
    unfold positionTablePolynomial
    apply coordinate_mul_degree _ _ i (a := 1) (b := 2)
    · simpa only [zero_add] using coordinate_mul_degree _ _ i
        (show (MvPolynomial.C scale : MvPolynomial (Fin n) W).degreeOf i ≤ 0 by
          simp only [MvPolynomial.degreeOf_C,le_refl]) (tablePolynomial_degree _ i)
    · exact chiPolynomial_degree _ _ i (fun _ => tablePolynomial_degree _ i)
  simpa only [positionTablePolynomial_eval] using coordinateDegree_eval
    (positionTablePolynomial weights t n scale kappa) hpoly

/-- Folding all native position factors binds their first multilinear coordinate exactly. -/
theorem positionTableSummand_fold (weights : Array W) (t : Array (Array W)) (n : Nat)
    (scale kappa r : W) (hw : weights.size = 2^(n+1))
    (ht : ∀ k : Fin 3,(t[k.val]!).size = 2^(n+1)) (point : Fin n → W) :
    positionTableSummand (fold weights 1 r) (t.map (fun a => fold a 1 r)) n scale kappa point =
      positionTableSummand weights t (n+1) scale kappa (Fin.cons r point) := by
  have h0 : (t[0]!).size = 2^(n+1) := ht 0
  have h1 : (t[1]!).size = 2^(n+1) := ht 1
  have h2 : (t[2]!).size = 2^(n+1) := ht 2
  unfold positionTableSummand
  rw [fold_mle weights hw]
  have hget (k : Nat) (hk3 : k < 3) : (t.map (fun a => fold a 1 r))[k]! = fold (t[k]!) 1 r := by
    by_cases hk : k < t.size
    · rw [getElem!_pos _ _ (by rw [Array.size_map]; exact hk),Array.getElem_map,
        ← getElem!_pos t _ hk]
    · have hz : (t[k]!).size = 0 := by rw [getElem!_neg t k hk]; rfl
      have htk : (t[k]!).size = 2^(n+1) := ht ⟨k,hk3⟩
      rw [hz] at htk
      have := Nat.two_pow_pos (n+1)
      omega
  rw [hget 0 (by decide),hget 1 (by decide),hget 2 (by decide),fold_mle (t[0]!) h0,fold_mle (t[1]!) h1,fold_mle (t[2]!) h2]

/-- All four coefficients of the actual native position round, before wire compression. -/
def positionCoefficients (weights : Array W) (t : Array (Array W)) (scale kappa : W) : Fin 4 → W :=
  fun k => scale*∑ row ∈ Finset.range (weights.size/2),positionCell weights t kappa row k

/-- The bounded univariate polynomial authored by one native position round. -/
noncomputable def positionRoundPolynomial (weights : Array W) (t : Array (Array W)) (scale kappa : W) : W⦃≤ 3⦄[X] :=
  ⟨messagePolynomial (positionCoefficients weights t scale kappa),
    Polynomial.mem_degreeLE.mpr (messagePolynomial_degree _)⟩

/-- The actual cubic coefficient polynomial evaluates to its complete affine-factor row sum. -/
theorem positionRoundPolynomial_eval (weights : Array W) (t : Array (Array W)) (scale kappa r : W) :
    (positionRoundPolynomial weights t scale kappa).val.eval r =
      scale*∑ row ∈ Finset.range (weights.size/2),
        line weights[2*row]! weights[2*row+1]! r *
          (kappa*line (t[0]!)[2*row]! (t[0]!)[2*row+1]! r +
            (kappa+line (t[1]!)[2*row]! (t[1]!)[2*row+1]! r)*
              line (t[2]!)[2*row]! (t[2]!)[2*row+1]! r) := by
  calc
    _ = scale*∑ row ∈ Finset.range (weights.size/2),polyEval (positionCell weights t kappa row) r := by
      simp only [positionRoundPolynomial,messagePolynomial_eval,positionCoefficients,polyEval,
        Finset.sum_mul,Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _ = _ := by
      apply congrArg (fun value : W => scale*value)
      apply Finset.sum_congr rfl
      intro row _
      simp only [positionCell,cubic_eval,line]
      ring

/-- The complete native position polynomial is the first honest projection of its factor-buffer summand. -/
theorem positionRoundPolynomial_first (weights : Array W) (t : Array (Array W)) (n : Nat)
    (scale kappa r : W) (hw : weights.size = 2^(n+1))
    (ht : ∀ k : Fin 3,(t[k.val]!).size = 2^(n+1)) :
    (positionRoundPolynomial weights t scale kappa).val.eval r =
      booleanSum (fun rest => positionTableSummand weights t (n+1) scale kappa (Fin.cons r rest)) := by
  have h0 : (t[0]!).size = 2^(n+1) := ht 0
  have h1 : (t[1]!).size = 2^(n+1) := ht 1
  have h2 : (t[2]!).size = 2^(n+1) := ht 2
  have heq : (fun rest => positionTableSummand weights t (n+1) scale kappa (Fin.cons r rest)) =
      positionTableSummand (fold weights 1 r) (t.map (fun a => fold a 1 r)) n scale kappa := by
    funext rest
    exact (positionTableSummand_fold weights t n scale kappa r hw ht rest).symm
  rw [heq,booleanSum_eq_residual _ (fun _ => 0),residualSum_zero]
  simp only [positionTableSummand,mle_cubePoint]
  rw [positionRoundPolynomial_eval,hw,pow_succ,Nat.mul_div_cancel _ (by decide)]
  rw [Fin.sum_univ_eq_sum_range (fun row =>
    scale*(fold weights 1 r)[row]! *
      (kappa*((t.map (fun a => fold a 1 r))[0]!)[row]!+
        (kappa+((t.map (fun a => fold a 1 r))[1]!)[row]!)*
          ((t.map (fun a => fold a 1 r))[2]!)[row]!)) (2^n),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row hr
  have hr := Finset.mem_range.mp hr
  have hget (k : Nat) (hk3 : k < 3) : (t.map (fun a => fold a 1 r))[k]! = fold (t[k]!) 1 r := by
    have hk : k < t.size := by
      by_contra hk
      have hz : (t[k]!).size = 0 := by rw [getElem!_neg t k hk]; rfl
      have htk : (t[k]!).size = 2^(n+1) := ht ⟨k,hk3⟩
      rw [hz] at htk
      have := Nat.two_pow_pos (n+1)
      omega
    rw [getElem!_pos _ _ (by rw [Array.size_map]; exact hk),Array.getElem_map,← getElem!_pos t _ hk]
  rw [hget 0 (by decide),hget 1 (by decide),hget 2 (by decide),fold_get weights hw r ⟨row,hr⟩,
    fold_get (t[0]!) h0 r ⟨row,hr⟩,fold_get (t[1]!) h1 r ⟨row,hr⟩,fold_get (t[2]!) h2 r ⟨row,hr⟩]
  simp only [foldCube]
  ring

/-- The transmitted native position coefficients are exactly the honest compressed cubic message. -/
theorem positionRound_honest (weights : Array W) (t : Array (Array W)) (n : Nat)
    (scale kappa : W) (hw : weights.size = 2^(n+1))
    (ht : ∀ k : Fin 3,(t[k.val]!).size = 2^(n+1))
    (hf : CoordinateDegree (positionTableSummand weights t (n+1) scale kappa) 3) :
    (scale*(positionRound weights t kappa)[0]!,
      fun k : Fin 2 => scale*(positionRound weights t kappa)[k.val+1]!) =
        Sumcheck.compress (firstHonestPolynomial (positionTableSummand weights t (n+1) scale kappa) hf) := by
  let : Fintype Ext3 := Fintype.ofFinite Ext3
  let : Fintype W := Fintype.ofEquiv Ext3 WordExt3.ringEquiv.toEquiv.symm
  have hcard : 3 < Fintype.card W := by
    rw [Fintype.card_congr WordExt3.ringEquiv.toEquiv,BF64.card_ext3]
    decide
  have heq := firstHonestPolynomial_eq (positionTableSummand weights t (n+1) scale kappa) hf
    hcard (positionRoundPolynomial weights t scale kappa)
    (fun r => positionRoundPolynomial_first weights t n scale kappa r hw ht)
  rw [heq]
  apply Prod.ext
  · change scale*(positionRound weights t kappa)[0]! =
      (messagePolynomial (positionCoefficients weights t scale kappa)).coeff 0
    have hc := messagePolynomial_coeff (positionCoefficients weights t scale kappa) (0 : Fin 4)
    simp only [Fin.val_zero] at hc
    rw [hc]
    have hr := positionRound_eq weights t kappa (0 : Fin 3)
    simp only [Fin.val_zero] at hr
    rw [hr]
    rfl
  · funext k
    change scale*(positionRound weights t kappa)[k.val+1]! =
      (messagePolynomial (positionCoefficients weights t scale kappa)).coeff (k.val+2)
    rw [messagePolynomial_coeff (positionCoefficients weights t scale kappa) ⟨k.val+2,by have := k.isLt; omega⟩]
    have hr := positionRound_eq weights t kappa ⟨k.val+1,by have := k.isLt; omega⟩
    rw [hr]
    fin_cases k <;> rfl

end CompStark.Keccak.GkrProver
