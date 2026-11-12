/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.GkrProver.SumcheckBlocks
public import CompStark.Keccak.GkrProver.Cofactor

/-! Block composition of equality-factored honest pack strategies. -/

set_option maxRecDepth 32768
set_option maxHeartbeats 200000

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak.Gkr Polynomial
open scoped BigOperators

/-- Equality kernels split at a concatenation of coordinate blocks. -/
theorem eqEval_join {F : Type} [CommRing F] [CharP F 2] {a b : Nat}
    (low low' : Fin a → F) (high high' : Fin b → F) :
    eqEval (joinPoint low high) (joinPoint low' high') = eqEval low low'*eqEval high high' := by
  induction a with
  | zero =>
    simp only [joinPoint_zero,eqEval,Fin.prod_univ_zero,one_mul]
    rfl
  | succ a ih =>
    rw [← Fin.cons_self_tail low,← Fin.cons_self_tail low',joinPoint_cons,joinPoint_cons,
      eqEval_cons,eqEval_cons,ih]
    ring

/-- Updating a low coordinate commutes with concatenating an independent high block. -/
theorem joinPoint_update_low {F : Type} {a b : Nat} (low : Fin a → F) (high : Fin b → F)
    (i : Fin a) (r : F) :
    Function.update (joinPoint low high) (⟨i.val,by omega⟩ : Fin (b+a)) r =
      joinPoint (Function.update low i r) high := by
  funext j
  by_cases hj : j.val<a
  · have he : j=(⟨i.val,by omega⟩ : Fin (b+a)) ↔ (⟨j.val,hj⟩ : Fin a)=i := by
      simp only [Fin.ext_iff]
    simp only [Function.update_apply,he,joinPoint,hj,dite_true]
  · have he : j≠(⟨i.val,by omega⟩ : Fin (b+a)) := by
      intro he
      have hv : j.val=i.val := congrArg Fin.val he
      have := i.isLt
      omega
    simp only [Function.update_of_ne he,joinPoint,hj,dite_false]

/-- A weighted Boolean projection preserves the coordinate degree of its unsummed block. -/
theorem coordinateDegree_project_low {F : Type} [CommRing F] {a b degree : Nat}
    (f : (Fin (b+a) → F) → F) (hf : CoordinateDegree f degree) (weight : (Fin b → F) → F) :
    CoordinateDegree (fun low => booleanSum (fun high => weight high*f (joinPoint low high))) degree := by
  classical
  intro i low
  choose P hdeg heval using fun high : Fin b → Fin 2 =>
    hf ⟨i.val,by omega⟩ (joinPoint low (fun j => ((high j).val : F)))
  refine ⟨∑ high,C (weight (fun j => ((high j).val : F)))*P high,
    (degree_sum_le _ _).trans (Finset.sup_le fun high _ => ?_),?_⟩
  · exact (degree_mul_le _ _).trans
      ((add_le_add degree_C_le (hdeg high)).trans (by simp only [zero_add]; exact le_rfl))
  · intro r
    simp only [eval_finsetSum,eval_mul,eval_C,heval,joinPoint_update_low,booleanSum]

/-- Early cofactor messages equal the honest strategy after summing out the later equality-weighted block. -/
theorem honestCofactorRounds_prefix {F : Type} [CommRing F] [CharP F 2] [IsDomain F] [Fintype F]
    {a b : Nat} (f : (Fin (b+a) → F) → F) (g : (Fin a → F) → F)
    (hf : CoordinateDegree f 2) (hg : CoordinateDegree g 2)
    (enterLow : Fin a → F) (enterHigh : Fin b → F)
    (sampleLow : Fin a → F) (sampleHigh : Fin b → F)
    (h : ∀ low,g low=booleanSum (fun high => eqEval enterHigh high*f (joinPoint low high)))
    (hcard : 2<Fintype.card F) (i : Fin a) :
    honestCofactorRounds f hf (joinPoint enterLow enterHigh) (joinPoint sampleLow sampleHigh)
      ⟨i.val,by omega⟩ = honestCofactorRounds g hg enterLow sampleLow i := by
  induction a with
  | zero => exact i.elim0
  | succ a ih =>
    have hp : joinPoint enterLow enterHigh =
        Fin.cons (enterLow 0) (joinPoint (fun i => enterLow i.succ) enterHigh) := by
      conv_lhs => rw [← Fin.cons_self_tail enterLow]
      exact joinPoint_cons _ _ _
    have hs : joinPoint sampleLow sampleHigh =
        Fin.cons (sampleLow 0) (joinPoint (fun i => sampleLow i.succ) sampleHigh) := by
      conv_lhs => rw [← Fin.cons_self_tail sampleLow]
      exact joinPoint_cons _ _ _
    rw [hp,hs]
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.val_zero,honestCofactorRounds,Fin.cons_zero,Fin.cons_succ]
      apply congrArg (fun P : F⦃≤ 2⦄[X] => (P.val.coeff 1,fun _ : Fin 1 => P.val.coeff 2))
      apply honestCofactorPolynomial_eq f hf _ hcard
      intro r
      rw [honestCofactorPolynomial_eval,booleanSum_join (a := a) (b := b)]
      unfold booleanSum
      apply Finset.sum_congr rfl
      intro low _
      dsimp only
      rw [h]
      simp only [booleanSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro high _
      change _ = eqEval
        (joinPoint (fun i => enterLow i.succ) enterHigh)
        (joinPoint (fun i => ((low i).val : F)) (fun i => ((high i).val : F))) *
        f (Fin.cons r (joinPoint (fun i => ((low i).val : F)) (fun i => ((high i).val : F))))
      rw [eqEval_join,joinPoint_cons]
      ring
    · simp only [Fin.val_succ,honestCofactorRounds,Fin.cons_succ]
      apply ih
      intro low
      rw [h]
      simp only [booleanSum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro high _
      rw [joinPoint_cons]
      simp only [Fin.cons_zero]
      ring

/-- Later cofactor messages equal the honest strategy with the earlier equality factors and challenges bound. -/
theorem honestCofactorRounds_suffix {F : Type} [CommRing F] [CharP F 2]
    {a b : Nat} (f : (Fin (b+a) → F) → F) (g : (Fin b → F) → F)
    (hf : CoordinateDegree f 2) (hg : CoordinateDegree g 2)
    (enterLow : Fin a → F) (enterHigh : Fin b → F)
    (sampleLow : Fin a → F) (sampleHigh : Fin b → F)
    (h : ∀ high,g high=eqEval enterLow sampleLow*f (joinPoint sampleLow high)) (i : Fin b) :
    honestCofactorRounds f hf (joinPoint enterLow enterHigh) (joinPoint sampleLow sampleHigh)
      ⟨a+i.val,by omega⟩ = honestCofactorRounds g hg enterHigh sampleHigh i := by
  induction a with
  | zero =>
    have hfg : g=f := by
      funext high
      simpa only [joinPoint_zero,eqEval,Fin.prod_univ_zero,one_mul] using h high
    subst g
    simp only [joinPoint_zero,Nat.zero_add]
    rfl
  | succ a ih =>
    have hp : joinPoint enterLow enterHigh =
        Fin.cons (enterLow 0) (joinPoint (fun i => enterLow i.succ) enterHigh) := by
      conv_lhs => rw [← Fin.cons_self_tail enterLow]
      exact joinPoint_cons _ _ _
    have hs : joinPoint sampleLow sampleHigh =
        Fin.cons (sampleLow 0) (joinPoint (fun i => sampleLow i.succ) sampleHigh) := by
      conv_lhs => rw [← Fin.cons_self_tail sampleLow]
      exact joinPoint_cons _ _ _
    rw [hp,hs]
    have hi : (⟨a+1+i.val,by omega⟩ : Fin (b+(a+1))) =
        (⟨a+i.val,by omega⟩ : Fin (b+a)).succ := Fin.ext (by simp only [Fin.val_succ]; omega)
    rw [hi]
    simp only [honestCofactorRounds,Fin.cons_zero,Fin.cons_succ]
    apply ih
    intro high
    rw [h,← Fin.cons_self_tail enterLow,← Fin.cons_self_tail sampleLow,eqEval_cons,joinPoint_cons]
    simp only [Fin.cons_zero,Fin.cons_succ]
    ring

end CompStark.Keccak.GkrProver
