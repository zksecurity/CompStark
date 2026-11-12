/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import ArkLib.Data.MvPolynomial.Hypercube
public import CompStark.Keccak.Gkr.LocalBounds
@[expose] public section
open Polynomial MvPolynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr
/-- Boolean coordinates agree with the little-endian integer cube encoding. -/
theorem cube_bit_cast {E : Type*} [CommRing E] {n : Nat} (b : Fin (2^n)) (i : Fin n) :
    (if b.val.testBit i.val then (1:E) else 0) = ((finFunctionFinEquiv.symm b i : Nat) : E) := by
  change _ = ((b.val / 2^i.val % 2 : Nat) : E)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have h := Nat.mod_lt (b.val / 2^i.val) (by omega : 0 < 2)
  split
  · rename_i ht
    have ht' : b.val / 2^i.val % 2 = 1 := of_decide_eq_true ht
    simp only [ht', Nat.cast_one]
  · rename_i ht
    have ht' : b.val / 2^i.val % 2 ≠ 1 := by simpa only [decide_eq_true_eq] using ht
    have hz : b.val / 2^i.val % 2 = 0 := by omega
    simp only [hz, Nat.cast_zero]

/-- The wire multilinear evaluator is ArkLib Boolean interpolation. -/
theorem mle_eq_eval {E : Type*} [CommRing E] {n : Nat} (a : Fin (2^n) → E) (r : Fin n → E) :
    MvPolynomial.eval r (MvPolynomial.MLE' a) = mle a r := by
  rw [MvPolynomial.MLE'_eval]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  rw [MvPolynomial.eqTilde, MvPolynomial.eqPolynomial_zeroOne]
  simp only [map_prod, apply_ite, map_sub, map_one, MvPolynomial.eval_X]
  unfold eqWeight
  apply Finset.prod_congr rfl
  intro i _
  change (if (⟨b.val / 2^i.val % 2, _⟩ : Fin 2) = 0 then _ else _) = _
  rw [Nat.testBit_eq_decide_div_mod_eq]
  split <;> split <;> simp_all only [Fin.mk_eq_zero, decide_eq_true_eq]
  all_goals omega

/-- Integer-indexed residual sums are the polynomial hypercube sums at the same prefix. -/
theorem residualSum_eq_hypercubeSum {E : Type*} [CommRing E] {n : Nat}
    (H : MvPolynomial (Fin n) E) (point : Fin n → E) (used : Nat) (hu : used ≤ n) :
    residualSum (fun r => H.eval r) point used =
      MvPolynomial.hypercubeSum n H used (fun j => point ⟨j.val, by omega⟩) := by
  classical
  unfold residualSum MvPolynomial.hypercubeSum
  simp only [Fintype.piFinset_univ]
  rw [← finFunctionFinEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  apply congrArg (fun r => H.eval r)
  funext j
  unfold MvPolynomial.hypercubePoint
  split
  · rfl
  · rename_i hj
    simpa only [Equiv.symm_apply_apply] using
      (cube_bit_cast (E := E) (finFunctionFinEquiv b) (⟨j.val-used, by omega⟩ : Fin (n-used)))

/-- The last residual sum is the summand evaluated at the full challenge point. -/
theorem residualSum_last {E : Type*} [CommRing E] {n : Nat}
    (f : (Fin n → E) → E) (point : Fin n → E) : residualSum f point n = f point := by
  simp [residualSum]

/-- The pack table selects the committed segment and pack indexed by one Boolean cube. -/
noncomputable def packTable {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (j : Fin 1600) (b : Fin (2^(p+1))) : E :=
  (packedLinear q d ⟨b.val / 2^p, by
    apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
    simpa only [pow_succ, Nat.mul_comm] using b.isLt⟩
    ⟨b.val % 2^p, Nat.mod_lt _ (by positivity)⟩ j).eval s

/-- Pack interpolation is the multilinear extension of the fixed committed pack table. -/
theorem linearAtPack_eq_mle {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (s : E) (r : Fin (p+1) → E) (j : Fin 1600) :
    linearAtPack q d s r j = mle (packTable q d s j) r := by
  unfold linearAtPack mle
  rw [cube_sum]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold packTable
  congr 2
  · apply Fin.ext
    simp only [Nat.add_mul_div_left _ _ (by positivity : 0 < 2^p),
      Nat.div_eq_of_lt b.isLt, Nat.zero_add]
  · apply Fin.ext
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt b.isLt]


/-- Cube weights split into low and high coordinate blocks. -/
theorem eqWeight_split {E : Type*} [CommRing E] {a b : Nat}
    (r : Fin (a+b) → E) (u : Fin (2^a)) (v : Fin (2^b)) :
    eqWeight r (u.val+2^a*v.val) =
      eqWeight (fun i => r (Fin.castAdd b i)) u.val *
      eqWeight (fun i => r (Fin.natAdd a i)) v.val := by
  unfold eqWeight
  rw [Fin.prod_univ_add]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Nat.add_comm u.val, Nat.testBit_two_pow_mul_add v.val u.isLt]
    simp only [Fin.val_castAdd, i.isLt, ite_true]
  · apply Finset.prod_congr rfl
    intro i _
    rw [Nat.add_comm u.val, Nat.testBit_two_pow_mul_add v.val u.isLt]
    simp only [Fin.val_natAdd, Nat.not_lt.mpr (Nat.le_add_right a i.val), ite_false,
      Nat.add_sub_cancel_left]

/-- An integer-indexed cube sum splits into its high and low blocks. -/
theorem cube_sum_split {A : Type*} [AddCommMonoid A] {a b : Nat}
    (f : Fin (2^(a+b)) → A) :
    ∑ w, f w = ∑ v : Fin (2^b), ∑ u : Fin (2^a),
      f ⟨u.val+2^a*v.val, by
        have he : 2^(a+b) = 2^b*2^a := by rw [pow_add, Nat.mul_comm]
        rw [he]
        have := (finProdFinEquiv (v,u)).isLt
        exact this⟩ := by
  let e : Fin (2^b) × Fin (2^a) ≃ Fin (2^(a+b)) :=
    finProdFinEquiv.trans (finCongr (by rw [pow_add, Nat.mul_comm]))
  calc
    _ = ∑ w : Fin (2^b) × Fin (2^a), f (e w) :=
      (Fintype.sum_equiv e _ _ (fun _ => rfl)).symm
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- Multilinear evaluation factors through low and high cube blocks. -/
theorem mle_split {E : Type*} [CommRing E] {a b : Nat}
    (f : Fin (2^a) → Fin (2^b) → E) (r : Fin (a+b) → E) :
    mle (fun w : Fin (2^(a+b)) =>
      f ⟨w.val%2^a,Nat.mod_lt _ (by positivity)⟩
        ⟨w.val/2^a,by
          apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
          simpa only [pow_add, Nat.mul_comm] using w.isLt⟩) r =
      ∑ v : Fin (2^b), eqWeight (fun i => r (Fin.natAdd a i)) v.val *
        mle (fun u => f u v) (fun i => r (Fin.castAdd b i)) := by
  unfold mle
  rw [cube_sum_split]
  simp_rw [eqWeight_split]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro u _
  have hm : (u.val+2^a*v.val)%2^a = u.val := by
    simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt u.isLt]
  have hd : (u.val+2^a*v.val)/2^a = v.val := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt u.isLt, Nat.zero_add]
  simp only [hm, hd]
  ring

/-- The Boolean cube point represented by an integer index. -/
def cubePoint {E : Type*} [Zero E] [One E] {n : Nat} (b : Fin (2^n)) : Fin n → E :=
  fun i => if b.val.testBit i.val then 1 else 0

/-- A multilinear extension recovers its table at each Boolean point. -/
theorem mle_cubePoint {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (2^n) → E) (b : Fin (2^n)) : mle a (cubePoint b) = a b := by
  rw [← mle_eq_eval]
  have hp : cubePoint (E := E) b = (fun i => ((finFunctionFinEquiv.symm b i : Nat) : E)) := by
    funext i; exact cube_bit_cast b i
  rw [hp]
  simp only [MvPolynomial.MLE', MvPolynomial.MLE_eval_zeroOne,
    Function.comp_apply, Equiv.apply_symm_apply]

/-- The finite bad challenge set of a polynomial collision test. -/
noncomputable def collisionSet {E : Type*} [Field E] (honest sent : E[X]) : Finset E :=
  by classical exact (honest-sent).roots.toFinset

/-- Distinct polynomial messages collide exactly on their fixed root set. -/
theorem mem_collisionSet {E : Type*} [Field E] (honest sent : E[X])
    (hne : honest ≠ sent) (r : E) :
    r ∈ collisionSet honest sent ↔ honest.eval r = sent.eval r := by
  classical
  simp only [collisionSet, Multiset.mem_toFinset, Polynomial.mem_roots (sub_ne_zero.mpr hne),
    Polynomial.IsRoot, Polynomial.eval_sub, sub_eq_zero]

/-- A degree-capped collision set has at most the cap many elements. -/
theorem collisionSet_card {E : Type*} [Field E] {n : Nat} (honest sent : E[X])
    (hh : honest.degree ≤ n) (hs : sent.degree ≤ n) :
    (collisionSet honest sent).card ≤ n := by
  classical
  exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' _).trans
    (Polynomial.natDegree_le_of_degree_le ((Polynomial.degree_sub_le _ _).trans (max_le hh hs))))

end CompStark.Keccak.Gkr
