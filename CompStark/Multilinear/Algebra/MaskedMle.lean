/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Algebra.Mle

/-! Boolean-grid decisions for multilinear restrictions at partially fixed points. -/

@[expose] public section
namespace CompStark.Multilinear
open CompStark.BinaryFields

/-- Fill fixed coordinates from the mask and free coordinates from the supplied point. -/
def maskedPoint (n : ℕ) (mask : ℕ → Option E) (point : List E) : List E :=
  List.ofFn fun k : Fin n => (mask k.val).getD (point.getD k.val 0)

/-- A masked coordinate is its fixed value or its original point coordinate. -/
theorem maskedPoint_getD (n : ℕ) (mask : ℕ → Option E) (point : List E)
    (k : Fin n) : (maskedPoint n mask point).getD k.val 0 = (mask k.val).getD (point.getD k.val 0) := by
  simp only [maskedPoint, List.getD, List.getElem?_ofFn, k.isLt, dite_true, Option.getD_some]

/-- Restricting coordinates commutes with Boolean multilinear interpolation. -/
theorem mle_maskedPoint (n : ℕ) (values : ℕ → E) (mask : ℕ → Option E) (point : List E) :
    mle n (fun i => mle n values (maskedPoint n mask
      (List.ofFn fun k : Fin n => bit i k.val))) point =
      mle n values (maskedPoint n mask point) := by
  have inner (i : Fin (2 ^ n)) :
      mle n (fun j => ∏ k : Fin n,
        eqFactor ((mask k.val).getD (bit j k.val)) (bit i.val k.val)) point =
      ∏ k : Fin n, eqFactor ((mask k.val).getD (point.getD k.val 0)) (bit i.val k.val) := by
    let a : Fin n → E := fun k => eqFactor ((mask k.val).getD 0) (bit i.val k.val)
    let b : Fin n → E := fun k => eqFactor ((mask k.val).getD 1) (bit i.val k.val)
    have affine (k : Fin n) (x : E) :
        eqFactor ((mask k.val).getD x) (bit i.val k.val) = a k * (1 - x) + b k * x := by
      dsimp only [a, b]
      cases mask k.val <;> simp only [Option.getD_none, Option.getD_some, eqFactor] <;> ring
    simp only [affine]
    exact mle_affine_product n a b point
  change (∑ j : Fin (2 ^ n),
    (∑ i : Fin (2 ^ n), values i.val * ∏ k : Fin n,
      eqFactor ((maskedPoint n mask (List.ofFn fun k : Fin n => bit j.val k.val)).getD k.val 0)
        (bit i.val k.val)) * ∏ k : Fin n, eqFactor (point.getD k.val 0) (bit j.val k.val)) = _
  have coord (j : Fin (2 ^ n)) (k : Fin n) :
      (maskedPoint n mask (List.ofFn fun k : Fin n => bit j.val k.val)).getD k.val 0 =
        (mask k.val).getD (bit j.val k.val) := by
    rw [maskedPoint_getD]
    simp only [List.getD, List.getElem?_ofFn, k.isLt, dite_true, Option.getD_some]
  simp_rw [coord]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (∑ j : Fin (2 ^ n),
      (values i.val * ∏ k : Fin n, eqFactor ((mask k.val).getD (bit j.val k.val))
        (bit i.val k.val)) * ∏ k : Fin n, eqFactor (point.getD k.val 0) (bit j.val k.val)) =
      values i.val * mle n (fun j => ∏ k : Fin n,
        eqFactor ((mask k.val).getD (bit j k.val)) (bit i.val k.val)) point by
    simp only [mle, Finset.mul_sum, mul_assoc]]
  rw [inner]
  apply congrArg (fun value => values i.val * value)
  apply Finset.prod_congr rfl
  intro k _
  rw [maskedPoint_getD]

/-- Vanishing on the finite restricted Boolean grid decides vanishing on every compatible point. -/
theorem mle_masked_zero_iff (n : ℕ) (values : ℕ → E) (mask : ℕ → Option E) :
    (∀ point : List E, point.length = n →
      (∀ k value, mask k = some value → k < n → point.getD k 0 = value) →
      mle n values point = 0) ↔
    ∀ i : Fin (2 ^ n), mle n values
      (maskedPoint n mask (List.ofFn fun k : Fin n => bit i.val k.val)) = 0 := by
  constructor
  · intro zero i
    apply zero _ (List.length_ofFn)
    intro k value known bounded
    change (maskedPoint n mask _).getD k 0 = value
    rw [maskedPoint_getD n mask _ ⟨k, bounded⟩, known]
    rfl
  · intro zero point length fixed
    have same : maskedPoint n mask point = point := by
      apply List.ext_getElem
      · simpa only [maskedPoint, List.length_ofFn] using length.symm
      · intro k hk _
        have bounded : k < n := by simpa only [maskedPoint, List.length_ofFn] using hk
        have coord := maskedPoint_getD n mask point ⟨k, bounded⟩
        rw [List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ (length ▸ bounded)] at coord
        rw [coord]
        cases known : mask k with
        | none => rfl
        | some value =>
            simpa only [Option.getD_some, List.getD_eq_getElem _ _ (length ▸ bounded)]
              using (fixed k value known bounded).symm
    rw [← same, ← mle_maskedPoint]
    change (∑ i : Fin (2 ^ n), mle n values
      (maskedPoint n mask (List.ofFn fun k : Fin n => bit i.val k.val)) * _) = 0
    apply Finset.sum_eq_zero
    intro i _
    rw [zero i, zero_mul]

end CompStark.Multilinear
