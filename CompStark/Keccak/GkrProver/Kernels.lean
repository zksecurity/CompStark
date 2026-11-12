/-
Copyright (c) 2026 zkSecurity.
Adapted from leanEthereum/leanMultisig (Apache-2.0), revision
9d8bce818aa7c7e18e67026e522a9b1539d0a57d, crates/keccak_gkr/src/{prover,open,protocol}.rs.
-/
module

public import CompStark.Keccak.Gkr.Protocol
public import CompPoly.Fields.Binary.BF64.WordField

/-! Executable coefficient kernels for the two-segment Keccak prover. -/

@[expose] public section
namespace CompStark.Keccak.GkrProver
open CompStark.Keccak
open scoped BigOperators

/-- One affine interpolation, with characteristic-two addition of endpoints. -/
@[inline] def line {F : Type*} [CommRing F] (a b r : F) : F := a + r * (a + b)

/-- Pairwise folding of a row-major table; `width` is the number of retained columns. -/
def fold {F : Type*} [CommRing F] [Inhabited F]
    (table : Array F) (width : Nat) (r : F) : Array F :=
  Array.ofFn fun i : Fin (table.size / (2 * width) * width) =>
    line table[2 * (i.val / width) * width + i.val % width]!
      table[(2 * (i.val / width) + 1) * width + i.val % width]! r

/-- The machine folding expression is the multilinear affine extension. -/
theorem line_eq {F : Type*} [CommRing F] [CharP F 2] (a b r : F) :
    line a b r = (1-r)*a+r*b := by
  rw [line, CharTwo.sub_eq_add]
  ring

/-- The coefficients of a quadratic dot-product round, before compression. -/
def quadratic {F : Type*} [CommRing F] (value zero infinity : F) : Fin 3 → F :=
  ![zero, value+infinity, infinity]

/-- A quadratic message sends its constant and quadratic coefficient. -/
def quadraticMessage {F : Type} [CommRing F] (zero infinity : F) :
    Sumcheck.CompressedMessage F 1 := (zero, fun _ => infinity)

/-- The compressed quadratic evaluates to its full polynomial. -/
theorem quadratic_decode {F : Type} [CommRing F] [CharP F 2]
    (value zero infinity r : F) :
    (Sumcheck.compressedOps 1).evaluate value (quadraticMessage zero infinity) r =
      Gkr.polyEval (quadratic value zero infinity) r := by
  simp only [Sumcheck.compressedOps, quadraticMessage, quadratic, Gkr.polyEval,
    Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [CharTwo.sub_eq_add]
  norm_num
  ring_nf
  have htwo : (2 : F) = 0 := CharP.cast_eq_zero F 2
  rw [htwo, mul_zero, add_zero]

/-- Four coefficients of a weighted chi gate on affine lines. -/
def cubic {F : Type*} [CommRing F] (w dw a da b db c dc k : F) : Fin 4 → F :=
  let q0 := k*a+(k+b)*c
  let q1 := k*da+(k+b)*dc+db*c
  let q2 := db*dc
  ![w*q0, w*q1+dw*q0, w*q2+dw*q1, dw*q2]

/-- The local cubic coefficients are the product of the weight and chi interpolation. -/
theorem cubic_eval {F : Type*} [CommRing F] (w dw a da b db c dc k r : F) :
    Gkr.polyEval (cubic w dw a da b db c dc k) r =
      (w+dw*r)*(k*(a+da*r)+(k+(b+db*r))*(c+dc*r)) := by
  simp only [Gkr.polyEval, cubic, Fin.sum_univ_succ]
  norm_num
  ring

/-- Coefficients of an embedding, directly from the proven CRT columns. -/
def embeddingCoeffs {F : Type*} [CommRing F] (u : Fin 16 → F) (c : Fin 24) : F :=
  ∑ i, if (Embedding.embeddingWords i).testBit c.val then u i else 0

/-- The coefficient kernel is the embedding used by the protocol theorem. -/
theorem embeddingCoeffs_eq {F : Type*} [CommRing F] [CharP F 2]
    (u : Fin 16 → F) (c : Fin 24) :
    embeddingCoeffs u c = (Embedding.kemb u).coeff c.val := by
  simp only [Embedding.kemb, LinearMap.coe_mk, AddHom.coe_mk, Polynomial.finsetSum_coeff,
    Polynomial.coeff_smul, smul_eq_mul, Polynomial.coeff_map, Embedding.basis,
    Embedding.coeff_toPoly, Embedding.basisCoeffs, Embedding.wordCoeffs,
    List.getElem?_ofFn, c.isLt, ↓reduceDIte, Option.getD_some, embeddingCoeffs]
  apply Finset.sum_congr rfl
  intro i _
  split <;> simp only [Nat.cast_one, Nat.cast_zero, map_one, map_zero, mul_one, mul_zero]

/-- Evaluate the sixteen embedding columns without constructing a polynomial. -/
def mu {F : Type*} [CommRing F] (s : F) (i : Fin 16) : F :=
  ∑ c : Fin 24, if (Embedding.embeddingWords i).testBit c.val then s^c.val else 0

/-- The executable column evaluations agree with the GKR instance weights. -/
theorem mu_eq {F : Type*} [CommRing F] [CharP F 2] (s : F) (i : Fin 16) :
    mu s i = Gkr.muAt s i := by
  have hdeg : (((Embedding.basis i).map (ZMod.castHom (dvd_refl 2) F))).natDegree < 24 := by
    have h : (((Embedding.basis i).map (ZMod.castHom (dvd_refl 2) F))).degree ≤ 23 :=
      Polynomial.degree_map_le.trans (Embedding.basis_degree i)
    exact Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_degree_le.mpr h)
  rw [Gkr.muAt_eq_eval, Polynomial.eval_eq_sum_range' hdeg]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro c _
  simp only [Polynomial.coeff_map, Embedding.basis, Embedding.coeff_toPoly,
    Embedding.basisCoeffs, Embedding.wordCoeffs, List.getElem?_ofFn,
    c.isLt, ↓reduceDIte, Option.getD_some]
  split <;> simp only [Nat.cast_one, Nat.cast_zero, map_one, map_zero, one_mul, zero_mul]

end CompStark.Keccak.GkrProver
