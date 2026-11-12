/-
Copyright (c) 2026 zkSecurity.
The construction follows leanEthereum/leanMultisig (Apache-2.0),
revision 9d8bce818aa7c7e18e67026e522a9b1539d0a57d, crates/keccak_gkr/src/rmfe.rs.
-/
module

public import CompStark.Keccak.EmbeddingData
public import CompStark.Keccak.Factors

/-! # Exact correspondence with Rust's CRT table construction -/

set_option Elab.async false

@[expose] public section
namespace CompStark.Keccak.Embedding

open scoped BigOperators
open Polynomial

/-- Binary encodings of the seven factors, low coefficient first. -/
def factorWords : Fin 7 → Nat := ![2,3,11,13,37,41,47]

/-- Carryless long division; 64 cancellations suffice for every word used by `rmfe.rs`. -/
def pdivmod : Nat → Nat → Nat → Nat × Nat
  | 0, a, _ => (0, a)
  | fuel + 1, a, f =>
    if a = 0 ∨ a.log2 < f.log2 then (0, a)
    else
      let shift := a.log2 - f.log2
      let qr := pdivmod fuel (a ^^^ (f <<< shift)) f
      (qr.1 ||| (1 <<< shift), qr.2)

/-- Carryless remainder on the source's 64-bit word domain. -/
def pmod (a f : Nat) : Nat := (pdivmod 64 a f).2

/-- The binary product of all seven CRT factors, of degree 23. -/
def modulusWord : Nat :=
  (List.ofFn factorWords).foldl (fun a b => clMulNat a b 64) 1

/-- Which CRT factor carries each of the first fifteen coordinates. -/
def bitFactor : Fin 15 → Fin 7 := ![0,1,2,2,3,3,4,4,4,5,5,5,6,6,6]

/-- The local interpolation columns at 0, 1, and infinity, matching Rust's `residues`. -/
def residueWords : Fin 15 → Nat := ![1,1,3,2,3,2,3,2,6,3,2,6,3,2,6]

/-- The first inverse found by the source's increasing search. -/
def inverseWords : Fin 7 → Nat := ![1,1,3,6,28,3,12]

/-- Source CRT construction of a unit embedding; the last coordinate is the product modulus. -/
def constructedEmbedding (i : Fin 16) : Nat :=
  if h : i.val < 15 then
    let b : Fin 15 := ⟨i.val, h⟩
    let g := bitFactor b
    let cofactor := (pdivmod 64 modulusWord (factorWords g)).1
    let lift := clMulNat cofactor (inverseWords g) 64
    pmod (clMulNat (pmod lift modulusWord) (residueWords b) 64) modulusWord
  else modulusWord

/-- Parity of a binary word's low six coefficients, sufficient for all CRT residues. -/
def residueParity (r : Nat) : Nat :=
  (List.ofFn (n := 6) fun c => if r.testBit c then 1 else 0).sum % 2

/-- Source projection row, reading residues at 0, 1, and infinity; bit 15 reads degree 46. -/
def constructedProjection (i : Fin 16) : Nat :=
  if h : i.val < 15 then
    let b : Fin 15 := ⟨i.val, h⟩
    let g := factorWords (bitFactor b)
    (List.ofFn (n := 47) fun c =>
      let r := pmod (1 <<< c.val) g
      let v := if i.val = 1 ∨ residueWords b = 2 then residueParity r
        else if residueWords b = 6 then r >>> 4 else r % 2
      v <<< c.val).sum
  else 1 <<< 46

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the exact CRT table construction, including the first inverse
chosen by the source. All integers fit in the source's unsigned 64-bit intermediates. -/
theorem construction_certificate :
    modulusWord = 8489494 ∧
    (∀ g : Fin 7,
      let cofactor := (pdivmod 64 modulusWord (factorWords g)).1
      (pdivmod 64 modulusWord (factorWords g)).2 = 0 ∧
      pmod (clMulNat (pmod cofactor (factorWords g)) (inverseWords g) 64) (factorWords g) = 1 ∧
      ∀ n : Fin 32, 0 < n.val → n.val < inverseWords g →
        pmod (clMulNat (pmod cofactor (factorWords g)) n.val 64) (factorWords g) ≠ 1) ∧
    (∀ i : Fin 16, constructedEmbedding i = embeddingWords i) ∧
    (∀ i : Fin 16, constructedProjection i = projectionWords i) := by
  decide +kernel

/-- Polynomial interpretation of a factor word agrees with the irreducibility certificate. -/
theorem factor_word_eq (g : Fin 7) :
    CompPoly.RabinCert.toPoly 2 (wordCoeffs 6 (factorWords g)) = factor g := by
  apply CompPoly.RabinCert.toPoly_eq_of_eqModP
  have h : ∀ g : Fin 7, CompPoly.RabinCert.eqModP 2
      (wordCoeffs 6 (factorWords g)) (factorCoeffs g) = true := by decide
  exact h g

/-- The local interpolation polynomial contributed by a unit coordinate modulo one factor. -/
def unitResidueWord (i : Fin 16) (g : Fin 7) : Nat :=
  if h : i.val < 15 then
    if bitFactor ⟨i.val,h⟩ = g then residueWords ⟨i.val,h⟩ else 0
  else 0

/-- Local unit interpolation polynomials have at most three coefficients. -/
noncomputable def unitResidue (i : Fin 16) (g : Fin 7) : Polynomial (ZMod 2) :=
  CompPoly.RabinCert.toPoly 2 (wordCoeffs 3 (unitResidueWord i g))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- Each embedding column has the specified CRT residue, checked by a quotient identity. -/
theorem crt_unit_certificate : ∀ i : Fin 16, ∀ g : Fin 7,
    CompPoly.RabinCert.eqModP 2 (basisCoeffs i)
      (CompPoly.RabinCert.addNat
        (CompPoly.RabinCert.mulNat
          (wordCoeffs 24 (pdivmod 64 (embeddingWords i) (factorWords g)).1)
          (wordCoeffs 6 (factorWords g)))
        (wordCoeffs 3 (unitResidueWord i g))) = true := by
  decide +kernel

/-- The local polynomials have degree strictly below their corresponding CRT factor. -/
theorem unitResidue_degree (i : Fin 16) (g : Fin 7) :
    (unitResidue i g).degree < (factor g).degree := by
  rw [Polynomial.degree_eq_natDegree (factor_ne_zero g), factor_natDegree,
    Polynomial.degree_lt_iff_coeff_zero]
  intro n hn
  rw [unitResidue, coeff_toPoly]
  by_cases h : n < 3
  · have bits : ∀ i : Fin 16, ∀ g : Fin 7, ∀ n : Fin 3,
        factorDegree g ≤ n.val → (unitResidueWord i g).testBit n.val = false := by decide
    simp only [wordCoeffs, List.getElem?_ofFn, h, dite_true, Option.getD_some]
    rw [bits i g ⟨n,h⟩ hn]
    rfl
  · simp only [wordCoeffs, List.getElem?_ofFn, h, dite_false, Option.getD_none, Nat.cast_zero]

/-- The embedding columns realize their prescribed local CRT residues. -/
theorem basis_mod_factor (i : Fin 16) (g : Fin 7) :
    basis i %ₘ factor g = unitResidue i g := by
  have h := CompPoly.RabinCert.toPoly_eq_of_eqModP (crt_unit_certificate i g)
  rw [CompPoly.RabinCert.toPoly_addNat, CompPoly.RabinCert.toPoly_mulNat] at h
  rw [factor_word_eq] at h
  change basis i = _ at h
  rw [h, Polynomial.add_modByMonic, Polynomial.mul_self_modByMonic (factor_monic g),
    zero_add]
  exact (Polynomial.modByMonic_eq_self_iff (factor_monic g)).mpr (unitResidue_degree i g)

/-- Factor-local linear interpolation at 0, 1, and infinity, extended to coefficient rings. -/
noncomputable def h_g {R : Type*} [CommRing R] [CharP R 2] (g : Fin 7) :
    (Fin 16 → R) →ₗ[R] Polynomial R where
  toFun u := ∑ i, u i • (unitResidue i g).map (ZMod.castHom (dvd_refl 2) R)
  map_add' u v := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [Pi.smul_apply, smul_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum]

/-- CRT correspondence for arbitrary coefficient extensions: reduction of the embedding
modulo each factor is exactly its local linear interpolation map. -/
theorem kemb_mod_factor {R : Type*} [CommRing R] [CharP R 2]
    (u : Fin 16 → R) (g : Fin 7) :
    kemb u %ₘ (factor g).map (ZMod.castHom (dvd_refl 2) R) = h_g g u := by
  change (Polynomial.modByMonicHom ((factor g).map (ZMod.castHom (dvd_refl 2) R)))
    (∑ i, u i • (basis i).map (ZMod.castHom (dvd_refl 2) R)) =
    ∑ i, u i • (unitResidue i g).map (ZMod.castHom (dvd_refl 2) R)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  congr 1
  exact (Polynomial.map_modByMonic (ZMod.castHom (dvd_refl 2) R) (factor_monic g)).symm.trans
    (congrArg (Polynomial.map (ZMod.castHom (dvd_refl 2) R)) (basis_mod_factor i g))

/-- The local interpolation formulas in annex C, in CRT factor order. -/
noncomputable def localFormula {R : Type*} [CommRing R] (u : Fin 16 → R) :
    Fin 7 → Polynomial R :=
  ![C (u 0), C (u 1), C (u 2) + C (u 2 + u 3)*X,
    C (u 4) + C (u 4 + u 5)*X,
    C (u 6) + C (u 6+u 7+u 8)*X + C (u 8)*X^2,
    C (u 9) + C (u 9+u 10+u 11)*X + C (u 11)*X^2,
    C (u 12) + C (u 12+u 13+u 14)*X + C (u 14)*X^2]

/-- The factor-local maps are precisely annex C's interpolation at 0, 1, and infinity. -/
theorem h_g_eq_localFormula {R : Type*} [CommRing R] [CharP R 2]
    (u : Fin 16 → R) (g : Fin 7) : h_g g u = localFormula u g := by
  fin_cases g <;>
    simp [h_g, localFormula, Fin.sum_univ_succ, unitResidue, unitResidueWord,
      bitFactor, residueWords, wordCoeffs, List.ofFn_succ,
      CompPoly.RabinCert.toPoly_cons, CompPoly.RabinCert.toPoly_nil,
      Nat.testBit_eq_decide_div_mod_eq, Polynomial.smul_eq_C_mul] <;> ring

/-- The monic degree-23 product of all seven CRT factors. -/
noncomputable def modulus : Polynomial (ZMod 2) := ∏ g : Fin 7, factor g

/-- The product modulus is monic. -/
theorem modulus_monic : modulus.Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun g _ => factor_monic g)

/-- The seven factor degrees add to 23. -/
theorem modulus_natDegree : modulus.natDegree = 23 := by
  rw [modulus, Polynomial.natDegree_prod_of_monic _ _ (fun g _ => factor_monic g)]
  simp only [factor_natDegree]
  decide

/-- The product modulus has degree exactly 23. -/
theorem modulus_degree : modulus.degree = 23 := by
  rw [Polynomial.degree_eq_natDegree modulus_monic.ne_zero, modulus_natDegree]
  rfl

/-- The square carrying the top product bit is monic of degree 46. -/
theorem modulus_square : (modulus^2).Monic ∧ (modulus^2).natDegree = 46 := by
  exact ⟨modulus_monic.pow 2, by rw [Polynomial.natDegree_pow, modulus_natDegree]⟩

/-- Interpret a structural product of coefficient lists as a product of polynomials. -/
theorem toPoly_fold_product (l : List (List Nat)) :
    CompPoly.RabinCert.toPoly 2 (l.foldr CompPoly.RabinCert.mulNat [1]) =
      (l.map (CompPoly.RabinCert.toPoly 2)).prod := by
  induction l with
  | nil => exact CompPoly.RabinCert.toPoly_one
  | cons a l ih =>
    simp only [List.foldr_cons, CompPoly.RabinCert.toPoly_mulNat, List.map_cons,
      List.prod_cons, ih]

/-- The last unit embedding is the CRT product modulus, so its square carries degree 46. -/
theorem basis_last_eq_modulus : basis 15 = modulus := by
  have certificate : CompPoly.RabinCert.eqModP 2
      ((List.ofFn factorCoeffs).foldr CompPoly.RabinCert.mulNat [1])
      (basisCoeffs 15) = true := by decide
  have h := CompPoly.RabinCert.toPoly_eq_of_eqModP certificate
  rw [toPoly_fold_product] at h
  simpa only [List.map_ofFn, List.prod_ofFn, Function.comp_apply, basis, modulus, factor] using h.symm

/-- The lower fifteen embedding columns have degree at most 22. -/
theorem basis_low_degree (i : Fin 15) : (basis i.castSucc).degree ≤ 22 := by
  rw [Polynomial.degree_le_iff_coeff_zero]
  intro n hn
  have hn' : 22 < n := by exact_mod_cast hn
  rw [basis, coeff_toPoly]
  by_cases h : n < 24
  · have hn23 : n = 23 := by omega
    subst n
    have bits : ∀ i : Fin 15, (basisCoeffs i.castSucc)[23]?.getD 0 = 0 := by decide
    rw [bits]
    rfl
  · have hlen : (basisCoeffs i.castSucc).length = 24 := by simp [basisCoeffs, wordCoeffs]
    rw [List.getElem?_eq_none (by omega), Option.getD_none, Nat.cast_zero]

/-- The degree-below-23 CRT part, excluding the sixteenth coordinate. -/
noncomputable def crtPart {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) : Polynomial R :=
  ∑ i : Fin 15, u i.castSucc • (basis i.castSucc).map (ZMod.castHom (dvd_refl 2) R)

/-- The CRT part has degree strictly below the product modulus. -/
theorem crtPart_degree {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) :
    (crtPart u).degree < 23 := by
  have h : (crtPart u).degree ≤ 22 := by
    change (∑ i : Fin 15, u i.castSucc • (basis i.castSucc).map (ZMod.castHom (dvd_refl 2) R)).degree ≤ 22
    apply (Polynomial.degree_sum_le _ _).trans
    apply Finset.sup_le
    intro i _
    exact (Polynomial.degree_smul_le _ _).trans
      (Polynomial.degree_map_le.trans (basis_low_degree i))
  exact h.trans_lt (by norm_num)

/-- Annex C's `H_u + u_15 F` decomposition in any characteristic-two coefficient ring. -/
theorem kemb_eq_crtPart {R : Type*} [CommRing R] [CharP R 2] (u : Fin 16 → R) :
    kemb u = crtPart u + u 15 • modulus.map (ZMod.castHom (dvd_refl 2) R) := by
  change (∑ i : Fin 16, u i • (basis i).map (ZMod.castHom (dvd_refl 2) R)) = _
  rw [Fin.sum_univ_castSucc]
  change crtPart u + u 15 • (basis 15).map (ZMod.castHom (dvd_refl 2) R) = _
  rw [basis_last_eq_modulus]

end CompStark.Keccak.Embedding
