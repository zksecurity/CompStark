/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Fields.Binary.AdditiveNTT.BasisConversion
public import CompPoly.Fields.Binary.BF64.WordField
public import CompPoly.Univariate.SparseMul
public import CompPoly.Bivariate.GuruswamiSudan.FieldTransport
import all CompPoly.Univariate.Basic

/-! Certified sparse arithmetic for monomial-to-novel coefficient conversion. -/

set_option backward.isDefEq.respectTransparency false
@[expose] public section
namespace CompStark.Pcs
open CompPoly

/-- Select a binary novel-basis factor without invoking polynomial exponentiation. -/
def novelFactor {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (normalized : Array (CPolynomial F)) (index bit : Nat) : CPolynomial F :=
  if index.testBit bit then normalized.getD bit 0 else 1

/-- A selected factor is precisely its zero-or-one polynomial power. -/
theorem novelFactor_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (normalized : Array (CPolynomial F)) (index bit : Nat) :
    novelFactor normalized index bit = (normalized.getD bit 0) ^ Nat.getBit bit index := by
  rw [Nat.getBit_eq_testBit]
  unfold novelFactor
  cases index.testBit bit <;> simp only [Bool.false_eq_true, ite_false, ite_true, pow_zero, pow_one]

/-- Multiply normalized sparse factors without executing zero coefficient rows. -/
def novelPolynomialSparse {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (normalized : Array (CPolynomial F)) (vars index : Nat) : CPolynomial F :=
  (List.finRange vars).foldl (fun p i =>
    CPolynomial.mulSkipZeros (novelFactor normalized index i.val) p) 1

/-- Sparse factor multiplication preserves the original ordered novel basis. -/
theorem novelPolynomialSparse_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (normalized : Array (CPolynomial F)) (vars index : Nat) :
    novelPolynomialSparse normalized vars index =
      AdditiveNTT.novelBasisPolynomial normalized vars index := by
  unfold novelPolynomialSparse AdditiveNTT.novelBasisPolynomial
  simp only [novelFactor_eq]
  have fold (is : List (Fin vars)) (p : CPolynomial F) :
      is.foldl (fun p i => CPolynomial.mulSkipZeros
        ((normalized.getD i.val 0) ^ Nat.getBit i.val index) p) p =
        p * (is.map fun i => (normalized.getD i.val 0) ^ Nat.getBit i.val index).prod := by
    induction is generalizing p with
    | nil => simp only [List.foldl_nil, List.map_nil, List.prod_nil, mul_one]
    | cons i is ih =>
      rw [List.foldl_cons, ih, CPolynomial.mulSkipZeros_eq_mul, List.map_cons, List.prod_cons]
      ac_rfl
  rw [fold, one_mul]
  change (List.map _ (List.ofFn id)).prod = _
  rw [List.map_ofFn, List.prod_ofFn]
  rfl

/-- Share the current divisor, skipping a zero top coefficient before constructing it. -/
def triangularShared {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (basis : Nat → CPolynomial F) : Nat → CPolynomial F → Array F
  | 0, _ => #[]
  | n + 1, p =>
    if p.coeff n == 0 then (triangularShared basis n p).push 0 else
      let b := basis n
      let c := p.coeff n / b.coeff n
      (triangularShared basis n (p - CPolynomial.C c * b)).push c

/-- Shared elimination and its zero branch preserve every triangular coefficient. -/
theorem triangularShared_eq {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    (basis : Nat → CPolynomial F) (n : Nat) (p : CPolynomial F) :
    triangularShared basis n p = CPolynomial.triangularBasisCoefficients basis n p := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih =>
    rw [triangularShared, CPolynomial.triangularBasisCoefficients]
    split
    · rename_i h
      simp only [eq_of_beq h, zero_div, CPolynomial.C_zero, zero_mul, sub_zero, ih]
    · dsimp only
      rw [ih]

/-- Convert monomial coefficients with shared divisors and sparse normalized factors. -/
def monomialToNovelSparse {F : Type*} [Field F] [BEq F] [LawfulBEq F] {r : Nat}
    (basis : Fin r → F) (vars : Nat) (h : vars ≤ r) (p : CPolynomial F) : Array F :=
  let normalized := AdditiveNTT.normalizedSubspacePolynomials basis vars h
  triangularShared (novelPolynomialSparse normalized vars) (2 ^ vars) p

/-- Sparse multiplication and shared elimination change no converted coefficient. -/
@[csimp] theorem monomialToNovelSparse_code :
    @AdditiveNTT.monomialToNovelArray = @monomialToNovelSparse := by
  funext F _ _ _ r basis vars h p
  simp only [AdditiveNTT.monomialToNovelArray, monomialToNovelSparse, triangularShared_eq]
  congr 1
  funext i
  exact (novelPolynomialSparse_eq _ _ _).symm

section Transport
variable {F G : Type} [Field F] [BEq F] [LawfulBEq F]
  [Field G] [BEq G] [LawfulBEq G]

/-- Coefficient transport as a polynomial ring equivalence. -/
def coefficientEquiv (e : F ≃+* G) : CPolynomial F ≃+* CPolynomial G where
  toFun := CPolynomial.mapCoeffs e
  invFun := CPolynomial.mapCoeffs e.symm
  left_inv := CPolynomial.mapCoeffs_symm e
  right_inv := CPolynomial.mapCoeffs_symm e.symm
  map_add' a b := by
    apply CPolynomial.toPoly_injective
    simp only [CPolynomial.toPoly_mapCoeffs, CPolynomial.toPoly_add, Polynomial.map_add]
  map_mul' a b := by
    apply CPolynomial.toPoly_injective
    simp only [CPolynomial.toPoly_mapCoeffs, CPolynomial.toPoly_mul, Polynomial.map_mul]

/-- Transport preserves each scalar polynomial coefficient. -/
theorem coefficientEquiv_coeff (e : F ≃+* G) (p : CPolynomial F) (n : Nat) :
    (coefficientEquiv e p).coeff n = e (p.coeff n) :=
  CPolynomial.coeff_mapCoeffs e p n

/-- Transport preserves constant polynomials. -/
theorem coefficientEquiv_C (e : F ≃+* G) (a : F) :
    coefficientEquiv e (CPolynomial.C a) = CPolynomial.C (e a) := by
  apply CPolynomial.toPoly_injective
  simp only [coefficientEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk,
    CPolynomial.toPoly_mapCoeffs, CPolynomial.C_toPoly, Polynomial.map_C]
  rfl

/-- Triangular elimination commutes with a field isomorphism. -/
theorem triangular_map (e : F ≃+* G) (basis : Nat → CPolynomial F)
    (n : Nat) (p : CPolynomial F) :
    (CPolynomial.triangularBasisCoefficients basis n p).map e =
      CPolynomial.triangularBasisCoefficients (fun i => coefficientEquiv e (basis i)) n
        (coefficientEquiv e p) := by
  induction n generalizing p with
  | zero => simp only [CPolynomial.triangularBasisCoefficients, Array.map_empty]
  | succ n ih =>
    simp only [CPolynomial.triangularBasisCoefficients, Array.map_push, ih,
      coefficientEquiv_coeff, map_sub, map_mul, coefficientEquiv_C, map_div₀]

/-- The normalized subspace factors commute with coefficient transport. -/
theorem normalized_map (e : F ≃+* G) {r : Nat} (basis : Fin r → F) (i : Fin r) :
    coefficientEquiv e (AdditiveNTT.normalizedSubspacePolynomial basis i) =
      AdditiveNTT.normalizedSubspacePolynomial (fun j => e (basis j)) i := by
  have subspace : coefficientEquiv e (AdditiveNTT.subspacePolynomial basis i) =
      AdditiveNTT.subspacePolynomial (fun j => e (basis j)) i := by
    unfold AdditiveNTT.subspacePolynomial
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro mask _
    have maskmap : e (AdditiveNTT.subspaceMaskValue basis i mask.val) =
        AdditiveNTT.subspaceMaskValue (fun j => e (basis j)) i mask.val := by
      unfold AdditiveNTT.subspaceMaskValue
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      split <;> simp only [map_zero]
    simp only [CPolynomial.linearFactor, map_add, coefficientEquiv_C, map_neg, maskmap]
    congr 1
    apply CPolynomial.toPoly_injective
    simp only [coefficientEquiv, RingEquiv.coe_mk, Equiv.coe_fn_mk,
      CPolynomial.toPoly_mapCoeffs, CPolynomial.X_toPoly, Polynomial.map_X]
  unfold AdditiveNTT.normalizedSubspacePolynomial
  rw [map_mul, coefficientEquiv_C, map_inv₀, subspace]
  rw [← subspace]
  change CPolynomial.C ((e (CPolynomial.eval (basis i) (AdditiveNTT.subspacePolynomial basis i)))⁻¹) * _ =
    CPolynomial.C ((CPolynomial.eval (e (basis i))
      (CPolynomial.mapCoeffs e (AdditiveNTT.subspacePolynomial basis i)))⁻¹) * _
  rw [CPolynomial.eval_mapCoeffs]

/-- Every novel basis vector commutes with coefficient transport. -/
theorem novel_map (e : F ≃+* G) {r : Nat} (basis : Fin r → F) (vars : Nat)
    (h : vars ≤ r) (index : Nat) :
    coefficientEquiv e (AdditiveNTT.novelBasisPolynomial
      (AdditiveNTT.normalizedSubspacePolynomials basis vars h) vars index) =
      AdditiveNTT.novelBasisPolynomial
        (AdditiveNTT.normalizedSubspacePolynomials (fun i => e (basis i)) vars h) vars index := by
  unfold AdditiveNTT.novelBasisPolynomial AdditiveNTT.normalizedSubspacePolynomials
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, i.isLt, dite_true,
    Option.getD_some, map_pow, normalized_map]

/-- Field transport preserves every executable monomial-to-novel coefficient. -/
theorem monomialToNovel_map (e : F ≃+* G) {r : Nat} (basis : Fin r → F)
    (vars : Nat) (h : vars ≤ r) (p : CPolynomial F) :
    (AdditiveNTT.monomialToNovelArray basis vars h p).map e =
      AdditiveNTT.monomialToNovelArray (fun i => e (basis i)) vars h (coefficientEquiv e p) := by
  unfold AdditiveNTT.monomialToNovelArray
  rw [triangular_map]
  congr 1
  funext index
  exact novel_map e basis vars h index

/-- Run coefficient conversion on an isomorphic executable field carrier. -/
def mappedNovel (e : F ≃+* G) {r : Nat} (basis : Fin r → F)
    (vars : Nat) (h : vars ≤ r) (p : CPolynomial F) : Array F :=
  (AdditiveNTT.monomialToNovelArray (fun i => e (basis i)) vars h
    (CPolynomial.mapCoeffs e p)).map e.symm

/-- The word-carrier conversion gives exactly the specification coefficients. -/
theorem mappedNovel_eq (e : F ≃+* G) {r : Nat} (basis : Fin r → F)
    (vars : Nat) (h : vars ≤ r) (p : CPolynomial F) :
    mappedNovel e basis vars h p = AdditiveNTT.monomialToNovelArray basis vars h p := by
  unfold mappedNovel
  change (AdditiveNTT.monomialToNovelArray (fun i => e (basis i)) vars h
    (coefficientEquiv e p)).map e.symm = _
  rw [← monomialToNovel_map, Array.map_map]
  simp only [Function.comp_def, RingEquiv.symm_apply_apply]
  exact Array.map_id _

end Transport
end CompStark.Pcs
