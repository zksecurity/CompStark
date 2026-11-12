/-
Copyright (c) 2026 zkSecurity.
The RMFE construction follows leanEthereum/leanMultisig (Apache-2.0),
revision 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, crates/keccak_gkr/src/rmfe.rs.
-/
module

public import CompStark.Keccak.Construction
import Mathlib.LinearAlgebra.Pi

/-!
# Keccak's reverse multiplication friendly embedding

Wire bit `i` is coordinate `i`; polynomial bit `c` is the coefficient of `X^c`.
Thus both the instance index and polynomial encoding are little endian, exactly as in `rmfe.rs`.
The sixteen columns in `EmbeddingData` are the CRT construction's unit embeddings. Projection row `i`
selects coefficients with the set bits of its mask; the last row selects coefficient 46.
-/

set_option Elab.async false

@[expose] public section

namespace CompStark.Keccak.Embedding

open CompPoly Polynomial
open scoped BigOperators

/-- Projection commutes with extension of the coefficient ring. -/
theorem kproj_map {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : R[X]) (i : Fin 16) :
    kproj (p.map f) i = f (kproj p i) := by
  simp only [kproj, LinearMap.coe_mk, AddHom.coe_mk, coeff_map, map_sum]
  apply Finset.sum_congr rfl
  intro c _
  split <;> simp only [map_zero]

/-- The characteristic-two lift of the unit-vector product certificate. -/
theorem basis_product {R : Type*} [CommRing R] [CharP R 2]
    (i j k : Fin 16) :
    kproj (((basis i).map (ZMod.castHom (dvd_refl 2) R)) *
      ((basis j).map (ZMod.castHom (dvd_refl 2) R))) k =
      if i = j ∧ j = k then 1 else 0 := by
  rw [← Polynomial.map_mul, kproj_map, basis_product_poly, projectNat_eq]
  rw [CharTwo.natCast_eq_mod, basis_product_certificate]
  split <;> simp only [Nat.cast_one, Nat.cast_zero, map_one, map_zero]

/-- Reverse multiplication friendliness over every characteristic-two commutative ring.
In particular this applies to the GKR extension field, without requiring Boolean inputs. -/
theorem kproj_kemb_mul {R : Type*} [CommRing R] [CharP R 2]
    (u v : Fin 16 → R) : kproj (kemb u * kemb v) = fun i => u i * v i := by
  funext k
  simp only [kemb, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul,
    Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, basis_product,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_comm]

/-- Every embedding column has degree at most 23. -/
theorem basis_degree (i : Fin 16) : (basis i).degree ≤ 23 := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  rw [basis, coeff_toPoly]
  have hn' : 23 < n := by exact_mod_cast hn
  have hlen : (basisCoeffs i).length = 24 := by simp [basisCoeffs, wordCoeffs]
  rw [List.getElem?_eq_none (by omega), Option.getD_none, Nat.cast_zero]

/-- The embedding has degree at most 23, including after scalar extension. -/
theorem kemb_degree {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) :
    (kemb u).degree ≤ 23 := by
  change (∑ i, u i • (basis i).map (ZMod.castHom (dvd_refl 2) R)).degree ≤ 23
  apply (Polynomial.degree_sum_le _ _).trans
  apply Finset.sup_le
  intro i _
  exact (Polynomial.degree_smul_le _ _).trans
    (Polynomial.degree_map_le.trans (basis_degree i))

/-- Products of embeddings have degree at most 46. -/
theorem kemb_mul_degree {R : Type*} [CommRing R] [CharP R 2] (u v : Fin 16 → R) :
    (kemb u * kemb v).degree ≤ 46 := by
  exact (Polynomial.degree_mul_le _ _).trans
    (by convert add_le_add (kemb_degree u) (kemb_degree v) using 1; norm_num)

/-- Linearity of the embedding in its sixteen input coordinates. -/
theorem kemb_add {R : Type*} [CommRing R] [CharP R 2] (u v : Fin 16 → R) :
    kemb (u+v) = kemb u + kemb v := kemb.map_add u v

/-- Linearity of the projection on coefficient polynomials. -/
theorem kproj_add {R : Type*} [CommSemiring R] (p q : R[X]) :
    kproj (p+q) = kproj p + kproj q := kproj.map_add p q

/-- Multiplication by the all-ones embedding projects to the input itself. -/
theorem kproj_ones_mul {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) :
    kproj (kemb (fun _ => (1 : R)) * kemb u) = u := by
  simpa only [one_mul] using kproj_kemb_mul (fun _ => (1 : R)) u

/-- The embedding is injective. -/
theorem kemb_injective {R : Type*} [CommRing R] [CharP R 2] :
    Function.Injective (kemb (R := R)) := by
  intro u v h
  rw [← kproj_ones_mul u, ← kproj_ones_mul v, h]

/-- Only the sixteenth coordinate contributes to the embedding's coefficient of degree 23. -/
theorem basis_coeff_twentyThree (i : Fin 16) :
    (basis i).coeff 23 = if i = 15 then 1 else 0 := by
  rw [basis, coeff_toPoly]
  have h : ∀ i : Fin 16, (basisCoeffs i)[23]?.getD 0 = if i = 15 then 1 else 0 := by decide
  rw [h i]
  split <;> rfl

/-- The top embedding coefficient is exactly the sixteenth input coordinate. -/
theorem kemb_coeff_twentyThree {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) :
    (kemb u).coeff 23 = u 15 := by
  change (Polynomial.lcoeff R 23)
    (∑ i, u i • (basis i).map (ZMod.castHom (dvd_refl 2) R)) = u 15
  simp only [map_sum, map_smul, Polynomial.lcoeff_apply, coeff_map,
    basis_coeff_twentyThree, apply_ite, map_one, map_zero, smul_eq_mul,
    mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Projection's sixteenth coordinate reads precisely the coefficient of degree 46. -/
theorem kproj_top {R : Type*} [CommSemiring R] (p : R[X]) :
    kproj p 15 = p.coeff 46 := by
  have h : ∀ c : Fin 47, (projectionWords 15).testBit c.val = decide (c = 46) := by decide
  simp only [kproj, LinearMap.coe_mk, AddHom.coe_mk, h, decide_eq_true_eq,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rfl

/-- The top product coefficient carries the product of the two sixteenth coordinates. -/
theorem kemb_mul_coeff_fortySix {R : Type*} [CommRing R] [CharP R 2] (u v : Fin 16 → R) :
    (kemb u * kemb v).coeff 46 = u 15 * v 15 := by
  have h := congrFun (kproj_kemb_mul u v) 15
  rwa [kproj_top] at h

/-- Annex C's lifted identity holds over any characteristic-two field with independent
lane powers; the embedding identity itself needs no independence hypothesis. -/
theorem lifted_product {E : Type*} [Field E] [CharP E 2] (x : E)
    (_independent : ∀ c : Fin 64 → ZMod 2,
      (∑ i, ZMod.castHom (dvd_refl 2) E (c i) * x^i.val) = 0 → ∀ i, c i = 0)
    (u v : Fin 16 → E) : kproj (kemb u * kemb v) = fun i => u i * v i :=
  kproj_kemb_mul u v

end CompStark.Keccak.Embedding
