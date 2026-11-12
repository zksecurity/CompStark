/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.PhasePolynomials

/-! # Tensor identities for the two committed-table openings -/

set_option maxRecDepth 8192
set_option maxHeartbeats 1000000
@[expose] public section
open Polynomial MvPolynomial
open scoped BigOperators
namespace CompStark.Keccak.Gkr

/-- Multilinear evaluation splits at any low-coordinate block with an explicit dimension equality. -/
theorem mle_blocks {E : Type*} [CommRing E] {n a b : Nat} (h : n = a+b)
    (f : Fin (2^a) → Fin (2^b) → E) (r : Fin n → E) :
    mle (fun w : Fin (2^n) =>
      f ⟨w.val%2^a,Nat.mod_lt _ (by positivity)⟩
        ⟨w.val/2^a,by
          apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
          calc
            w.val < 2^n := w.isLt
            _ = 2^b*2^a := by rw [h,pow_add,Nat.mul_comm]⟩) r =
      ∑ v : Fin (2^b), eqWeight (fun i : Fin b => r ⟨a+i.val,by omega⟩) v.val *
        mle (fun u => f u v) (fun i : Fin a => r ⟨i.val,by omega⟩) := by
  subst n
  exact mle_split f r

/-- The four low-instance coordinates of the input opening. -/
def inputLowPoint {E : Type*} (r : Fin 10 → E) : Fin 4 → E := fun i => r ⟨i.val,by omega⟩

/-- The six slot coordinates of the input opening. -/
def inputSlotPoint {E : Type*} (r : Fin 10 → E) : Fin 6 → E := fun i => r ⟨i.val+4,by omega⟩

/-- The input instance point combines the opening's low coordinates and the retained pack point. -/
def inputInstancePoint {E : Type*} {p : Nat} (c : Claim E p) (r : Fin 10 → E) : Fin (p+4) → E :=
  fun i => if h : i.val < 4 then r ⟨i.val,by omega⟩ else c.point ⟨i.val-4,by omega⟩

/-- The two disjoint opening weight blocks form one multilinear table. -/
noncomputable def inputTensorWeight {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (z : Fin 64) (w : Fin 1024) : E :=
  c.mu ⟨w.val%16,Nat.mod_lt _ (by decide)⟩ *
    inputWeight c ⟨w.val/16,(Nat.div_lt_iff_lt_mul (by decide)).mpr w.isLt⟩ z

/-- The committed bit table with the high-instance pack coordinates already evaluated. -/
noncomputable def inputTensorBits {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (c : Claim E p) (z : Fin 64) (w : Fin 1024) : E :=
  mle (fun b : Fin (2^p) => ZMod.castHom (dvd_refl 2) E
    (q (packInstance ⟨w.val%16,Nat.mod_lt _ (by decide)⟩ b)
      ⟨w.val/16,(Nat.div_lt_iff_lt_mul (by decide)).mpr w.isLt⟩ z))
    (fun i => c.point i.castSucc)

/-- Interpolating the tensor weight separates its low-instance and slot factors. -/
theorem inputTensorWeight_eval {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (c : Claim E p) (z : Fin 64) (r : Fin 10 → E) :
    mle (inputTensorWeight c z) r = mle c.mu (inputLowPoint r) *
      mle (fun slot => inputWeight c slot z) (inputSlotPoint r) := by
  have h := mle_split (a := 4) (b := 6)
    (fun low : Fin 16 => fun slot : Fin 64 => c.mu low * inputWeight c slot z) r
  change mle (inputTensorWeight c z) r = _ at h
  rw [h]
  have hlo : (fun i : Fin 4 => r (Fin.castAdd 6 i)) = inputLowPoint r := rfl
  have hhi : (fun i : Fin 6 => r (Fin.natAdd 4 i)) = inputSlotPoint r := by
    funext i; unfold inputSlotPoint; congr 1; apply Fin.ext
    simp only [Fin.val_natAdd]; omega
  rw [hlo,hhi]
  simp only [mle, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro slot _
  apply Finset.sum_congr rfl
  intro low _
  ring

/-- Interpolating input instances separates low four bits from their retained high pack point. -/
theorem inputInstancePoint_eval {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (c : Claim E p) (r : Fin 10 → E) (slot z : Fin 64) :
    mle (fun b => ZMod.castHom (dvd_refl 2) E (q b slot z)) (inputInstancePoint c r) =
      ∑ b : Fin (2^p), eqWeight (fun i => c.point i.castSucc) b.val *
        mle (fun low : Fin 16 => ZMod.castHom (dvd_refl 2) E (q (packInstance low b) slot z))
          (inputLowPoint r) := by
  have ht : (fun w : Fin (2^(p+4)) =>
    ZMod.castHom (dvd_refl 2) E (q
      (packInstance ⟨w.val%16,Nat.mod_lt _ (by decide)⟩
        ⟨w.val/16,by
          apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
          simpa only [pow_add, show (2^4 : Nat) = 16 by decide, Nat.mul_comm] using w.isLt⟩) slot z)) =
      (fun w => ZMod.castHom (dvd_refl 2) E (q w slot z)) := by
    funext w
    have hp : packInstance ⟨w.val%16,Nat.mod_lt _ (by decide)⟩
        ⟨w.val/16,by
          apply (Nat.div_lt_iff_lt_mul (by decide)).mpr
          simpa only [pow_add, show (2^4 : Nat) = 16 by decide, Nat.mul_comm] using w.isLt⟩ = w := by
      apply Fin.ext
      exact Nat.mod_add_div w.val 16
    rw [hp]
  have h := mle_blocks (n := p+4) (a := 4) (b := p) (by omega)
    (fun low b => ZMod.castHom (dvd_refl 2) E (q (packInstance low b) slot z)) (inputInstancePoint c r)
  simp only [show (2^4 : Nat) = 16 by decide] at h
  rw [ht] at h
  have hlo : (fun i : Fin 4 => inputInstancePoint c r ⟨i.val,by omega⟩) = inputLowPoint r := by
    funext i; simp only [inputInstancePoint, inputLowPoint, i.isLt, dite_true]
  have hhi : (fun i : Fin p => inputInstancePoint c r ⟨4+i.val,by omega⟩) =
      (fun i : Fin p => c.point i.castSucc) := by
    funext i
    simp only [inputInstancePoint, show ¬4+i.val < 4 by omega, dite_false, Nat.add_sub_cancel_left]
    rfl
  rw [hlo,hhi] at h
  exact h

/-- Interpolating committed tensor bits is the actual input instance and slot evaluation. -/
theorem inputTensorBits_eval {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (c : Claim E p) (z : Fin 64) (r : Fin 10 → E) :
    mle (inputTensorBits q c z) r =
      mle (fun slot => mle (fun b => ZMod.castHom (dvd_refl 2) E (q b slot z))
        (inputInstancePoint c r)) (inputSlotPoint r) := by
  have h := mle_blocks (n := 10) (a := 4) (b := 6) (by decide)
    (fun low slot => mle (fun b : Fin (2^p) => ZMod.castHom (dvd_refl 2) E
      (q (packInstance low b) slot z)) (fun i => c.point i.castSucc)) r
  change mle (inputTensorBits q c z) r = _ at h
  rw [h]
  have hlo : (fun i : Fin 4 => r ⟨i.val,by omega⟩) = inputLowPoint r := rfl
  have hhi : (fun i : Fin 6 => r ⟨4+i.val,by omega⟩) = inputSlotPoint r := by
    funext i; exact congrArg r (Fin.ext (Nat.add_comm 4 i.val))
  rw [hlo,hhi]
  change (∑ slot : Fin 64, eqWeight (inputSlotPoint r) slot.val * _) =
    ∑ slot : Fin 64, eqWeight (inputSlotPoint r) slot.val * _
  apply Finset.sum_congr rfl
  intro slot _
  rw [inputInstancePoint_eval]
  congr 1
  simp only [mle, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro low _
  ring

/-- The input-opening residual is a sum of products of multilinear tensor tables. -/
noncomputable def inputPolynomial {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) : MvPolynomial (Fin 10) E :=
  let c := nextClaim (t.layers (Fin.last 11))
  ∑ z : Fin 64, MLE' (inputTensorWeight c z) * MLE' (inputTensorBits q c z)

/-- The tensor polynomial evaluates to the concrete input-opening summand. -/
theorem inputPolynomial_eval {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (r : Fin 10 → E) :
    MvPolynomial.eval r (inputPolynomial q t) = inputSummand q t r := by
  simp only [inputPolynomial, map_sum, map_mul, mle_eq_eval, inputTensorWeight_eval,
    inputTensorBits_eval, inputSummand, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact mul_assoc _ _ _

/-- Both factors of each input-opening term are multilinear, giving the quadratic cap. -/
theorem inputPolynomial_degree {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (t : Transcript E p) (i : Fin 10) :
    (inputPolynomial q t).degreeOf i ≤ 2 := by
  apply coordinate_sum_degree
  intro z
  exact coordinate_mul_degree _ _ i (tablePolynomial_degree _ i) (tablePolynomial_degree _ i)

end CompStark.Keccak.Gkr
