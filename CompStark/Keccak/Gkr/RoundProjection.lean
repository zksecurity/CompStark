/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.PhasePolynomials

/-! # Honest sumcheck restrictions and finite bad challenge sets -/

@[expose] public section
open Polynomial MvPolynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- The honest univariate round polynomial fixes the prefix and sums the Boolean suffix. -/
noncomputable def roundProjection {E : Type*} [CommRing E] {n : Nat}
    (H : MvPolynomial (Fin n) E) (i : Fin n) (point : Fin n → E) : E[X] :=
  ∑ b : Fin (n-(i.val+1)) → Fin 2,
    H.evalExcept i (MvPolynomial.hypercubeSuffix i (fun j => point ⟨j.val,by omega⟩) b)

/-- The honest restriction retains the original coordinate degree cap. -/
theorem roundProjection_degree {E : Type*} [CommRing E] {n d : Nat}
    (H : MvPolynomial (Fin n) E) (i : Fin n) (point : Fin n → E)
    (h : H.degreeOf i ≤ d) : (roundProjection H i point).degree ≤ d := by
  apply (Polynomial.degree_sum_le _ _).trans
  apply Finset.sup_le
  intro b _
  exact Polynomial.degree_le_of_natDegree_le ((MvPolynomial.natDegree_evalExcept_le _ _ _).trans h)

/-- The updated prefix is the old prefix followed by the fresh coordinate. -/
theorem updated_prefix {E : Type*} {n : Nat} (point : Fin n → E) (i : Fin n) (r : E) :
    (fun j : Fin (i.val+1) => Function.update point i r ⟨j.val,by omega⟩) =
      Fin.snoc (fun j : Fin i.val => point ⟨j.val,by omega⟩) r := by
  classical
  funext j
  refine Fin.lastCases ?_ (fun k : Fin i.val => ?_) j
  · simp only [Fin.val_last, Fin.eta, Function.update_self, Fin.snoc_last]
  · have hk : (⟨k.val,by omega⟩ : Fin n) ≠ i := by
      intro h
      have hv : k.val = i.val := congrArg Fin.val h
      exact Nat.ne_of_lt k.isLt hv
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, Function.update_of_ne hk]

/-- The honest round polynomial's Boolean sum is exactly the entering residual. -/
theorem roundProjection_sum {E : Type*} [CommRing E] {n : Nat}
    (H : MvPolynomial (Fin n) E) (i : Fin n) (point : Fin n → E) :
    (roundProjection H i point).eval 0 + (roundProjection H i point).eval 1 =
      residualSum (fun r => H.eval r) point i.val := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [residualSum_eq_hypercubeSum H point i.val (by omega)]
    exact MvPolynomial.sum_eval_sum_evalExcept_hypercube H i _

/-- The honest round polynomial evaluates to exactly the next residual. -/
theorem roundProjection_eval {E : Type*} [CommRing E] {n : Nat}
    (H : MvPolynomial (Fin n) E) (i : Fin n) (point : Fin n → E) (r : E) :
    (roundProjection H i point).eval r =
      residualSum (fun z => H.eval z) (Function.update point i r) (i.val+1) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [residualSum_eq_hypercubeSum H (Function.update point i r) (i.val+1) (by omega), updated_prefix]
    exact MvPolynomial.eval_sum_evalExcept_hypercube H i _ r

/-- A fixed false residual can become true only on a degree-capped finite collision set. -/
theorem residual_round_bad_set {E : Type*} [Field E] {n d : Nat}
    (H : MvPolynomial (Fin n) E) (i : Fin n) (point : Fin n → E)
    (sent : Fin (d+1) → E) (target : E) (degree : H.degreeOf i ≤ d)
    (wrong : target ≠ residualSum (fun r => H.eval r) point i.val)
    (check : polyEval sent 0 + polyEval sent 1 = target) :
    ∃ bad : Finset E, bad.card ≤ d ∧ ∀ r,
      polyEval sent r = residualSum (fun z => H.eval z) (Function.update point i r) (i.val+1) → r ∈ bad := by
  classical
  have hne : roundProjection H i point ≠ messagePolynomial sent := by
    intro he
    apply wrong
    rw [← roundProjection_sum H i point, he]
    simpa only [messagePolynomial_eval] using check.symm
  refine ⟨collisionSet (roundProjection H i point) (messagePolynomial sent),
    collisionSet_card _ _ (roundProjection_degree H i point degree) (messagePolynomial_degree sent), ?_⟩
  intro r good
  apply (mem_collisionSet _ _ hne r).mpr
  simpa only [roundProjection_eval, messagePolynomial_eval] using good.symm

end CompStark.Keccak.Gkr
