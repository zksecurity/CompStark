/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Basic

/-! Linearity and Boolean interpolation for low-bit-first list-point multilinear extensions. -/

@[expose] public section

open CompStark.BinaryFields
namespace CompStark.Multilinear
open MvPolynomial
noncomputable section
/-- Multilinear extension commutes with addition of tables. -/
theorem mle_add (n : ℕ) (f g : ℕ → E) (z : List E) :
    mle n (fun i ↦ f i + g i) z = mle n f z + mle n g z := by
  simp only [mle, add_mul, Finset.sum_add_distrib]
/-- Multilinear extension commutes with scalar multiplication. -/
theorem mle_smul (n : ℕ) (a : E) (f : ℕ → E) (z : List E) :
    mle n (fun i ↦ a * f i) z = a * mle n f z := by
  simp only [mle, mul_assoc, Finset.mul_sum]
/-- Multilinear extension commutes with finite sums. -/
theorem mle_sum {ι : Type} (n : ℕ) (s : Finset ι) (f : ι → ℕ → E) (z : List E) :
    mle n (fun i ↦ ∑ j ∈ s, f j i) z = ∑ j ∈ s, mle n (f j) z := by
  simp only [mle, Finset.sum_mul]
  exact Finset.sum_comm
/-- Constant tables have constant extensions. -/
theorem mle_const (n : ℕ) (a : E) (z : List E) : mle n (fun _ ↦ a) z = a := by
  rw [mle_eq_evalMle]
  have ht : (Vector.ofFn fun _ : Fin (2 ^ n) ↦ a) = Vector.replicate (2 ^ n) a := by
    exact Vector.ext fun _ _ ↦ by simp only [Vector.getElem_ofFn, Vector.getElem_replicate]
  rw [ht]
  exact Algebra.evalMle_replicate _ _
/-- Multilinear extension commutes with subtraction of tables. -/
theorem mle_sub (n : ℕ) (f g : ℕ → E) (z : List E) :
    mle n (fun i ↦ f i - g i) z = mle n f z - mle n g z := by
  simp only [mle, sub_mul, Finset.sum_sub_distrib]
/-- Extending a table's Boolean evaluations recovers its extension. -/
theorem mle_idempotent (n : ℕ) (f : ℕ → E) (z : List E) :
    mle n (fun i ↦ mle n f (List.ofFn fun k : Fin n ↦ bit i k.val)) z = mle n f z := by
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [mle_bits n f i]
/-- Integer cube indices recover the Boolean coordinates. -/
theorem finFunction_bits (n : ℕ) (i : Fin (2 ^ n)) (k : Fin n) :
    ((finFunctionFinEquiv.symm i k).val : E) = bit i.val k.val := by
  change ((i.val / 2 ^ k.val % 2 : ℕ) : E) = _
  rw [bit, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_true_eq]
  split_ifs with h
  · rw [h]; rfl
  · have hz : i.val / 2 ^ k.val % 2 = 0 := by
      have := Nat.mod_lt (i.val / 2 ^ k.val) (by decide : 0 < 2)
      omega
    rw [hz]; rfl
/-- The polynomial equality kernel agrees with the low-bit-first scalar basis. -/
theorem eqTilde_bits (n : ℕ) (i : Fin (2 ^ n)) (z : List E) :
    eqTilde (finFunctionFinEquiv.symm i : Fin n → E) (fun k ↦ z.getD k.val 0) =
      ∏ k : Fin n, eqFactor (z.getD k.val 0) (bit i.val k.val) := by
  rw [eqTilde_eq_prod]
  apply Finset.prod_congr rfl
  intro k _
  rw [finFunction_bits]
  unfold eqFactor
  ring
/-- A multilinear polynomial is the extension of its Boolean evaluations. -/
theorem mle_eval_multilinear (n : ℕ) (p : MvPolynomial (Fin n) E)
    (hp : ∀ j, p.degreeOf j ≤ 1) (z : List E) :
    mle n (fun i ↦ MvPolynomial.eval (fun k ↦ bit i k.val) p) z =
      MvPolynomial.eval (fun k ↦ z.getD k.val 0) p := by
  have hm : p = MLE' (fun i : Fin (2 ^ n) ↦ MvPolynomial.eval (fun k ↦ bit i.val k.val) p) := by
    apply eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq _ _ hp
    intro x
    apply congrArg (fun f : Fin n → E ↦ MvPolynomial.eval f p)
    funext k
    have he := finFunction_bits n (finFunctionFinEquiv x) k
    simpa only [Equiv.symm_apply_apply] using he
  have hh := congrArg (MvPolynomial.eval (fun k : Fin n ↦ z.getD k.val 0)) hm
  rw [MLE'_eval] at hh
  refine Eq.trans ?_ hh.symm
  simp only [eqTilde_bits]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _
/-- A product with one affine factor per coordinate is multilinear. -/
theorem affine_product_degree (n : ℕ) (a b : Fin n → E) (j : Fin n) :
    (∏ k : Fin n, (C (a k) * (1 - X k) + C (b k) * X k) : MvPolynomial (Fin n) E).degreeOf j ≤ 1 := by
  classical
  refine (degreeOf_prod_le j _ _).trans ?_
  have h (k : Fin n) :
      (C (a k) * (1 - X k) + C (b k) * X k : MvPolynomial (Fin n) E).degreeOf j ≤ if j = k then 1 else 0 := by
    refine (degreeOf_add_le j _ _).trans (max_le ?_ ?_)
    · refine (degreeOf_mul_le j _ _).trans ?_
      rw [degreeOf_C, zero_add]
      exact (degreeOf_sub_le j _ _).trans (by simp only [degreeOf_one, degreeOf_X]; split_ifs <;> omega)
    · simpa only [degreeOf_C, degreeOf_X, zero_add] using degreeOf_mul_le j (C (b k)) (X k)
  apply le_trans (Finset.sum_le_sum fun k _ ↦ h k)
  simp
/-- Boolean interpolation preserves products with one affine factor per coordinate. -/
theorem mle_affine_product (n : ℕ) (a b : Fin n → E) (z : List E) :
    mle n (fun i ↦ ∏ k : Fin n, (a k * (1 - bit i k.val) + b k * bit i k.val)) z =
      ∏ k : Fin n, (a k * (1 - z.getD k.val 0) + b k * z.getD k.val 0) := by
  simpa only [map_prod, map_add, map_mul, MvPolynomial.eval_C, map_sub, map_one,
    MvPolynomial.eval_X] using mle_eval_multilinear n
      (∏ k : Fin n, (C (a k) * (1 - X k) + C (b k) * X k)) (affine_product_degree n a b) z

/-- Truncating a point after the last used coordinate preserves its extension. -/
theorem mle_take (n : ℕ) (values : ℕ → E) (z : List E) :
    mle n values (z.take n) = mle n values z := by
  apply mle_congr
  intro k hk
  simp only [List.getD, List.getElem?_take_of_lt hk]

end

end CompStark.Multilinear
