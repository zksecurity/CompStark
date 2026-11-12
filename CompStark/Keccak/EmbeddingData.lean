/-
Copyright (c) 2026 zkSecurity.
The RMFE construction follows leanEthereum/leanMultisig (Apache-2.0),
revision 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, crates/keccak_gkr/src/rmfe.rs.
-/
module

public import Mathlib.Algebra.CharP.Two
public import CompPoly.Data.Polynomial.RabinCertificate
import Mathlib.LinearAlgebra.Pi

/-!
# Keccak's reverse multiplication friendly embedding

Wire bit `i` is coordinate `i`; polynomial bit `c` is the coefficient of `X^c`.
Thus both the instance index and polynomial encoding are little endian, exactly as in `rmfe.rs`.
The sixteen columns below are the CRT construction's unit embeddings. Projection row `i`
selects coefficients with the set bits of its mask; the last row selects coefficient 46.
-/

set_option Elab.async false

@[expose] public section

namespace CompStark.Keccak.Embedding

open CompPoly Polynomial
open scoped BigOperators

/-- Unit-vector embeddings, in Rust's `RMFE.emb` order, encoded coefficient low bit first. -/
def embeddingWords : Fin 16 → Nat :=
  ![4244747,8354290,4935178,7500812,5461978,1907870,310894,7885382,
    621788,1089150,2036820,2178300,5045448,7821168,1602438,8489494]

/-- Unit-vector embedding masks through a bounded array lookup. -/
def embeddingWordsFast (i : Fin 16) : Nat :=
  (#[4244747,8354290,4935178,7500812,5461978,1907870,310894,7885382,
    621788,1089150,2036820,2178300,5045448,7821168,1602438,8489494] : Array Nat)[i.val]'i.isLt

/-- Array lookup preserves every pinned mask. -/
@[csimp] theorem embeddingWords_code : embeddingWords = embeddingWordsFast := by
  have checked : ∀ i : Fin 16, embeddingWords i = embeddingWordsFast i := by decide
  exact funext checked

/-- Coefficient-selection masks, in Rust's `RMFE.proj` order. -/
def projectionWords : Fin 16 → Nat :=
  ![1,140737488355327,43218598786281,32136906789799,111925089164473,
    101951566367639,112771593653537,102871349771039,126754541004432,
    60819261648545,20682647020959,30409630824272,11891857888673,
    6939470531743,76314673122000,70368744177664]

/-- Projection masks through a bounded array lookup. -/
def projectionWordsFast (i : Fin 16) : Nat :=
  (#[1,140737488355327,43218598786281,32136906789799,111925089164473,
    101951566367639,112771593653537,102871349771039,126754541004432,
    60819261648545,20682647020959,30409630824272,11891857888673,
    6939470531743,76314673122000,70368744177664] : Array Nat)[i.val]'i.isLt

/-- Array lookup preserves every pinned mask. -/
@[csimp] theorem projectionWords_code : projectionWords = projectionWordsFast := by
  have checked : ∀ i : Fin 16, projectionWords i = projectionWordsFast i := by decide
  exact funext checked

/-- Decode the low `n` coefficients of a binary word as structural natural-number data. -/
def wordCoeffs (n word : Nat) : List Nat :=
  List.ofFn (n := n) fun c => if word.testBit c then 1 else 0

/-- The coefficient data of each CRT embedding column. -/
def basisCoeffs (i : Fin 16) : List Nat := wordCoeffs 24 (embeddingWords i)

/-- Horner evaluation of little-endian natural coefficient data. -/
def evaluateCoeffs {R : Type*} [Semiring R] (point : R) : List ℕ → R
  | [] => 0
  | coefficient :: rest => (coefficient : R) + point * evaluateCoeffs point rest

set_option smartUnfolding true in
/-- Direct coefficient evaluation agrees with the mapped binary polynomial certificate. -/
theorem evaluateCoeffs_eq {R : Type*} [CommRing R] [CharP R 2]
    (point : R) (coefficients : List ℕ) :
    evaluateCoeffs point coefficients =
      ((RabinCert.toPoly 2 coefficients).map
        (ZMod.castHom (dvd_refl 2) R)).eval point := by
  induction coefficients with
  | nil => simp only [evaluateCoeffs, RabinCert.toPoly, Polynomial.map_zero, Polynomial.eval_zero]
  | cons coefficient rest ih =>
      simp only [evaluateCoeffs, RabinCert.toPoly, Polynomial.map_add, Polynomial.map_natCast,
        Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_add, Polynomial.eval_natCast,
        Polynomial.eval_mul, Polynomial.eval_X, map_natCast, ih]

/-- The binary polynomial embedding one coordinate. -/
noncomputable def basis (i : Fin 16) : (ZMod 2)[X] := RabinCert.toPoly 2 (basisCoeffs i)

/-- The linear extension of the projection to arbitrary polynomial coefficients. -/
noncomputable def kproj {R : Type*} [CommSemiring R] : R[X] →ₗ[R] (Fin 16 → R) where
  toFun p i := ∑ c : Fin 47, if (projectionWords i).testBit c then p.coeff c else 0
  map_add' p q := by
    funext i
    simp only [coeff_add, Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _
    split <;> simp only [add_zero]
  map_smul' a p := by
    funext i
    simp only [coeff_smul, Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro c _
    split <;> simp only [smul_zero]

/-- The binary embedding, extended coefficientwise to any characteristic-two ring. -/
noncomputable def kemb {R : Type*} [CommRing R] [CharP R 2] :
    (Fin 16 → R) →ₗ[R] R[X] where
  toFun u := ∑ i, u i • (basis i).map (ZMod.castHom (dvd_refl 2) R)
  map_add' u v := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]

/-- Coefficients of the structural certificate interpretation are ordinary list entries. -/
theorem coeff_toPoly (l : List Nat) (n : Nat) :
    (RabinCert.toPoly 2 l).coeff n = (l[n]?.getD 0 : ZMod 2) := by
  induction l generalizing n with
  | nil => simp only [RabinCert.toPoly_nil, coeff_zero, List.getElem?_nil, Option.getD_none, Nat.cast_zero]
  | cons a l ih =>
    cases n with
    | zero => simp [RabinCert.toPoly_cons]
    | succ n => simp [RabinCert.toPoly_cons, coeff_X_mul, ih]

/-- Executable coefficient selection over natural-number certificate data. -/
def projectNat (l : List Nat) (i : Fin 16) : Nat :=
  (List.ofFn (n := 47) fun c =>
    if (projectionWords i).testBit c then l[c.val]?.getD 0 else 0).sum

/-- The natural-number checker agrees with the polynomial projection after casting. -/
theorem projectNat_eq (l : List Nat) (i : Fin 16) :
    kproj (RabinCert.toPoly 2 l) i = (projectNat l i : ZMod 2) := by
  simp only [kproj, LinearMap.coe_mk, AddHom.coe_mk, coeff_toPoly, projectNat,
    List.sum_ofFn, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro c _
  split <;> simp only [Nat.cast_zero]

/-- Carryless multiplication by structural recursion on the selected low bits. -/
def clMulNat (a b : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if a.testBit n then (clMulNat a b n) ^^^ (b <<< n) else clMulNat a b n

/-- The unreduced product word of two embedding columns. -/
def productWord (i j : Fin 16) : Nat := clMulNat (embeddingWords i) (embeddingWords j) 24

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 0. -/
private theorem product_word_row0 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 0) (basisCoeffs j))
      (wordCoeffs 47 (productWord 0 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 1. -/
private theorem product_word_row1 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 1) (basisCoeffs j))
      (wordCoeffs 47 (productWord 1 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 2. -/
private theorem product_word_row2 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 2) (basisCoeffs j))
      (wordCoeffs 47 (productWord 2 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 3. -/
private theorem product_word_row3 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 3) (basisCoeffs j))
      (wordCoeffs 47 (productWord 3 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 4. -/
private theorem product_word_row4 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 4) (basisCoeffs j))
      (wordCoeffs 47 (productWord 4 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 5. -/
private theorem product_word_row5 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 5) (basisCoeffs j))
      (wordCoeffs 47 (productWord 5 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 6. -/
private theorem product_word_row6 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 6) (basisCoeffs j))
      (wordCoeffs 47 (productWord 6 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 7. -/
private theorem product_word_row7 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 7) (basisCoeffs j))
      (wordCoeffs 47 (productWord 7 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 8. -/
private theorem product_word_row8 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 8) (basisCoeffs j))
      (wordCoeffs 47 (productWord 8 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 9. -/
private theorem product_word_row9 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 9) (basisCoeffs j))
      (wordCoeffs 47 (productWord 9 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 10. -/
private theorem product_word_row10 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 10) (basisCoeffs j))
      (wordCoeffs 47 (productWord 10 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 11. -/
private theorem product_word_row11 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 11) (basisCoeffs j))
      (wordCoeffs 47 (productWord 11 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 12. -/
private theorem product_word_row12 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 12) (basisCoeffs j))
      (wordCoeffs 47 (productWord 12 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 13. -/
private theorem product_word_row13 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 13) (basisCoeffs j))
      (wordCoeffs 47 (productWord 13 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 14. -/
private theorem product_word_row14 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 14) (basisCoeffs j))
      (wordCoeffs 47 (productWord 14 j)) = true := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Carryless multiplication certificate for embedding column 15. -/
private theorem product_word_row15 : ∀ j : Fin 16,
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs 15) (basisCoeffs j))
      (wordCoeffs 47 (productWord 15 j)) = true := by
  decide +kernel

/-- The structural list multiplication agrees with all 256 carryless product words. -/
theorem product_word_certificate (i j : Fin 16) :
    RabinCert.eqModP 2 (RabinCert.mulNat (basisCoeffs i) (basisCoeffs j))
      (wordCoeffs 47 (productWord i j)) = true := by
  fin_cases i
  · exact product_word_row0 j
  · exact product_word_row1 j
  · exact product_word_row2 j
  · exact product_word_row3 j
  · exact product_word_row4 j
  · exact product_word_row5 j
  · exact product_word_row6 j
  · exact product_word_row7 j
  · exact product_word_row8 j
  · exact product_word_row9 j
  · exact product_word_row10 j
  · exact product_word_row11 j
  · exact product_word_row12 j
  · exact product_word_row13 j
  · exact product_word_row14 j
  · exact product_word_row15 j

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 0. -/
private theorem projection_row0 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 0 j)) k % 2 =
      if (0 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 1. -/
private theorem projection_row1 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 1 j)) k % 2 =
      if (1 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 2. -/
private theorem projection_row2 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 2 j)) k % 2 =
      if (2 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 3. -/
private theorem projection_row3 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 3 j)) k % 2 =
      if (3 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 4. -/
private theorem projection_row4 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 4 j)) k % 2 =
      if (4 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 5. -/
private theorem projection_row5 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 5 j)) k % 2 =
      if (5 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 6. -/
private theorem projection_row6 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 6 j)) k % 2 =
      if (6 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 7. -/
private theorem projection_row7 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 7 j)) k % 2 =
      if (7 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 8. -/
private theorem projection_row8 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 8 j)) k % 2 =
      if (8 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 9. -/
private theorem projection_row9 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 9 j)) k % 2 =
      if (9 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 10. -/
private theorem projection_row10 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 10 j)) k % 2 =
      if (10 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 11. -/
private theorem projection_row11 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 11 j)) k % 2 =
      if (11 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 12. -/
private theorem projection_row12 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 12 j)) k % 2 =
      if (12 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 13. -/
private theorem projection_row13 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 13 j)) k % 2 =
      if (13 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 14. -/
private theorem projection_row14 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 14 j)) k % 2 =
      if (14 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Projection certificate for embedding column 15. -/
private theorem projection_row15 : ∀ j k : Fin 16,
    projectNat (wordCoeffs 47 (productWord 15 j)) k % 2 =
      if (15 : Fin 16) = j ∧ j = k then 1 else 0 := by
  decide +kernel

/-- The masks recover the coordinatewise product from all 256 product words. -/
theorem basis_product_certificate (i j k : Fin 16) :
    projectNat (wordCoeffs 47 (productWord i j)) k % 2 =
      if i = j ∧ j = k then 1 else 0 := by
  fin_cases i
  · exact projection_row0 j k
  · exact projection_row1 j k
  · exact projection_row2 j k
  · exact projection_row3 j k
  · exact projection_row4 j k
  · exact projection_row5 j k
  · exact projection_row6 j k
  · exact projection_row7 j k
  · exact projection_row8 j k
  · exact projection_row9 j k
  · exact projection_row10 j k
  · exact projection_row11 j k
  · exact projection_row12 j k
  · exact projection_row13 j k
  · exact projection_row14 j k
  · exact projection_row15 j k

/-- The checked carryless words denote ordinary polynomial multiplication. -/
theorem basis_product_poly (i j : Fin 16) :
    basis i * basis j = RabinCert.toPoly 2 (wordCoeffs 47 (productWord i j)) := by
  exact (RabinCert.toPoly_mulNat _ _).symm.trans
    (RabinCert.toPoly_eq_of_eqModP (product_word_certificate i j))


end CompStark.Keccak.Embedding
