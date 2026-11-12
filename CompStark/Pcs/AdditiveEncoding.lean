/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.BinaryDomain
public import CompPoly.Fields.Binary.BF64.WordField

/-!
# Additive novel-basis encoding for WHIR

The mathematical encoder uses the normalized basis in CompPoly. Its domain includes
`vars + rate = 64`; the butterfly implementation has the additional strict bound.
-/

@[expose] public section

open CompStark.BinaryFields Polynomial Module
namespace CompStark.Pcs

/-- The exact normalized-basis weights and little-endian additive domain of Annex D. -/
abbrev encoding (vars rate : ℕ) (h : vars + rate ≤ 64) : Whir.Encoding K vars where
  rate := rate
  domain := domain h
  weight x u := ∏ i : Fin vars, if u i then
    Whir.normalizedSubspaceValue basis
      ⟨i.val, lt_of_lt_of_le i.isLt ((Nat.le_add_right vars rate).trans h)⟩ (domain h x) else 1

/-- The column weights satisfy WHIR's precise normalized-novel-basis clause. -/
theorem encoding_novel (vars rate : ℕ) (h : vars + rate ≤ 64) :
    ∃ beta : Fin 64 → K, beta 0 = 1 ∧
      (∀ x, (encoding vars rate h).domain x = ∑ i : Fin (vars + rate),
        if x.val.testBit i.val then beta (Fin.castLE h i) else 0) ∧
      ∀ x u, (encoding vars rate h).weight x u = ∏ i : Fin vars,
        if u i then Whir.normalizedSubspaceValue beta
          ⟨i.val, lt_of_lt_of_le i.isLt ((Nat.le_add_right vars rate).trans h)⟩
          ((encoding vars rate h).domain x) else 1 :=
  ⟨basis, basis_zero, fun _ => rfl, fun _ _ => rfl⟩

/-- Scalar extension commutes with the normalized subspace value. -/
theorem normalizedSubspaceValue_map {S : Type} [Field S] (phi : K →+* S)
    (i : Fin 64) (x : K) :
    phi (Whir.normalizedSubspaceValue basis i x) =
      Whir.normalizedSubspaceValue (fun j => phi (basis j)) i (phi x) := by
  simp only [Whir.normalizedSubspaceValue, map_div₀, map_prod, map_sub,
    Whir.binarySpanValue, map_sum, apply_ite phi, map_zero]

section ScalarExtension
variable {S : Type} [Field S] [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
  (phi : K →+* S)

/-- The base-field inclusion as a binary-linear map, independent of scalar-tower instances. -/
noncomputable def binaryLinearMap : K →ₗ[ZMod 2] S where
  toFun := phi
  map_add' := phi.map_add
  map_smul' c x := by
    rcases binary_cases c with rfl | rfl <;> simp only [zero_smul, one_smul, map_zero,
      RingHom.id_apply]

omit [Fintype S] [DecidableEq S] in
/-- The embedded 64 base-field vectors remain binary-linearly independent in S. -/
theorem extendedBasis_independent :
    LinearIndependent (ZMod 2) (fun j => phi (basis j)) :=
  basis_linearIndependent.map' (binaryLinearMap phi) (LinearMap.ker_eq_bot.mpr phi.injective)

/-- The embedded basis supplies CompPoly's independence premise. -/
instance extendedBasisFact : Fact (LinearIndependent (ZMod 2) (fun j => phi (basis j))) :=
  ⟨extendedBasis_independent phi⟩

/-- CompPoly's normalized subspace polynomial has the same Boolean-product evaluation. -/
theorem normalizedSubspaceValue_eq_eval (i : Fin 64) (x : S) :
    Whir.normalizedSubspaceValue (fun j => phi (basis j)) i x =
      (AdditiveNTT.normalizedW (ZMod 2) (fun j => phi (basis j)) i).eval x := by
  let : Fact (LinearIndependent (ZMod 2) (fun j => phi (basis j))) :=
    ⟨extendedBasis_independent phi⟩
  rw [← AdditiveNTT.evalNormalizedWAt_eq_normalizedW (𝔽q := ZMod 2) (β := fun j => phi (basis j)) (ℓ := 0) (R_rate := 0)]
  unfold AdditiveNTT.evalNormalizedWAt AdditiveNTT.evalWAt AdditiveNTT.getUElements
  simp only [List.map_map, AdditiveNTT.List.prod_finRange_eq_finset_prod]
  have product (x : S) :
      (Finset.univ.prod (fun u : Whir.Cube i.val => x - Whir.binarySpanValue (fun j => phi (basis j)) i u)) =
        Finset.univ.prod (fun a : Fin (2 ^ i.val) => x - ∑ j : Fin i.val,
          if Nat.getBit j.val a.val == 1 then phi (basis ⟨j.val, by omega⟩) else 0) := by
    rw [← (cubeEquiv i.val).prod_comp]
    apply Finset.prod_congr rfl
    intro a _
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [cubeEquiv_apply, mask,
      Nat.getBit_eq_testBit]
    by_cases bit : a.val.testBit j.val = true <;> simp only [bit, ↓reduceIte] <;> rfl
  simpa only [Whir.normalizedSubspaceValue, Function.comp_apply, div_eq_mul_inv] using
    congrArg₂ (fun a b : S => a / b) (product x) (product (phi (basis i)))

end ScalarExtension

/-- Evaluate a normalized subspace polynomial through the binary squaring recurrence. -/
def normalizedValueFast (i : Fin 64) (x : K) : K :=
  let constants := AdditiveNTT.subspacePolynomialConstantsArray (β := basis) (ℓ := 0) (R_rate := 0) i
  AdditiveNTT.evalWAtCachedConstants constants x /
    AdditiveNTT.evalWAtCachedConstants constants (basis i)

/-- The recurrence computes the exact normalized product used by WHIR. -/
theorem normalizedValueFast_eq (i : Fin 64) (x : K) :
    normalizedValueFast i x = Whir.normalizedSubspaceValue basis i x := by
  let : Fact (LinearIndependent (ZMod 2) basis) := ⟨basis_linearIndependent⟩
  rw [normalizedValueFast,
    AdditiveNTT.evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W (𝔽q := ZMod 2),
    AdditiveNTT.evalWAtCachedConstants_subspacePolynomialConstantsArray_eq_W (𝔽q := ZMod 2)]
  rw [show Whir.normalizedSubspaceValue basis i x =
    (AdditiveNTT.normalizedW (ZMod 2) basis i).eval x from
      normalizedSubspaceValue_eq_eval (RingHom.id K) i x]
  simp only [AdditiveNTT.normalizedW, Polynomial.eval_mul, Polynomial.eval_C,
    div_eq_mul_inv, one_mul]
  exact mul_comm _ _

/-- Fixed subspace recurrence coefficients and inverse normalizers for the binary basis. -/
def normalizedValueData : Vector (Array K × K) 64 :=
  Vector.ofFn fun i =>
    let constants := AdditiveNTT.subspacePolynomialConstantsArray
      (β := basis) (ℓ := 0) (R_rate := 0) i
    (constants, (AdditiveNTT.evalWAtCachedConstants constants (basis i))⁻¹)

/-- Evaluate with the shared basis constants and inverse normalizer. -/
def normalizedValueCached (i : Fin 64) (x : K) : K :=
  let data := normalizedValueData[i.val]
  AdditiveNTT.evalWAtCachedConstants data.1 x * data.2

/-- Sharing fixed basis data preserves every normalized query factor. -/
@[csimp] theorem normalizedValueFast_code : normalizedValueFast = normalizedValueCached := by
  funext i x
  simp only [normalizedValueFast, normalizedValueCached, normalizedValueData,
    Vector.getElem_ofFn, div_eq_mul_inv]

/-- Share the encoding's query image before embedding its coordinate values. -/
@[macro_inline] def queryWeightCached {F S : Type} [Semiring F] [Semiring S] {n : Nat}
    (enc : Whir.Encoding F n) (ι : F →+* S) (query : enc.Columns) : Whir.Table S n :=
  Whir.prepareQuery enc.weight (fun weight u => ι (weight u)) query

/-- Preparing the query once preserves its exact embedded weight table. -/
theorem queryWeightCached_eq {F S : Type} [Semiring F] [Semiring S] {n : Nat}
    (enc : Whir.Encoding F n) (ι : F →+* S) (query : enc.Columns) :
    queryWeightCached enc ι query = (fun u => ι (enc.weight query u)) := rfl

/-- Cache the normalized factors for one additive-domain query before coefficient lookup. -/
def encodingFast (vars rate : Nat) (h : vars + rate ≤ 64) : Whir.Encoding K vars where
  rate := rate
  domain := domain h
  weight := Whir.prepareQuery
    (fun x => Vector.ofFn fun i : Fin vars =>
      BF64.Word.ringEquiv.symm (normalizedValueFast ⟨i.val, by omega⟩ (domain h x)))
    (fun values u => BF64.Word.ringEquiv (∏ i : Fin vars, if u i then values[i] else 1))

/-- Cached normalized factors preserve every encoding weight and its ordered domain. -/
@[csimp] theorem encoding_code : @encoding = @encodingFast := by
  funext vars rate h
  unfold encoding encodingFast
  congr 1
  funext x u
  simp only [Whir.prepareQuery, map_prod, Fin.getElem_fin, Vector.getElem_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp only [map_one, RingEquiv.apply_symm_apply, normalizedValueFast_eq]

end CompStark.Pcs

namespace CompStark.Pcs
open CompStark.BinaryFields Polynomial Module

section ScalarExtension
variable {S : Type} [Field S] [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
  (phi : K →+* S)

/-- CompPoly's novel polynomial basis after extension of scalars. -/
noncomputable def novelBasis (vars : ℕ) (h : vars ≤ 64) :
    Basis (Fin (2 ^ vars)) S (degreeLT S (2 ^ vars)) := by
  letI : Fact (LinearIndependent (ZMod 2) (fun j => phi (basis j))) :=
    ⟨extendedBasis_independent phi⟩
  exact AdditiveNTT.novelPolynomialBasis (ZMod 2) (fun j => phi (basis j)) vars h

/-- Each vector of the basis is the corresponding CompPoly novel polynomial. -/
theorem novelBasis_apply (vars : ℕ) (h : vars ≤ 64) (j : Fin (2 ^ vars)) :
    ((novelBasis phi vars h j : degreeLT S (2 ^ vars)) : S[X]) =
      AdditiveNTT.Xⱼ (ZMod 2) (fun j => phi (basis j)) vars h j := by
  unfold novelBasis
  rw [AdditiveNTT.novelPolynomialBasis_is_basisVectors]
  rfl

/-- Interpret the Boolean message table directly as novel-basis coefficients. -/
noncomputable def coefficientPolynomial (vars : ℕ) (h : vars ≤ 64)
    (f : Whir.Table S vars) : degreeLT S (2 ^ vars) :=
  (novelBasis phi vars h).equivFun.symm (fun j => f (mask vars j))

/-- The coefficient interpretation is bijective; it performs no input basis conversion. -/
theorem coefficientPolynomial_bijective (vars : ℕ) (h : vars ≤ 64) :
    Function.Bijective (coefficientPolynomial phi vars h) := by
  constructor
  · intro f g hfg
    have hh := (novelBasis phi vars h).equivFun.symm.injective hfg
    funext u
    obtain ⟨j, rfl⟩ := (cubeEquiv vars).surjective u
    exact congrFun hh j
  · intro p
    refine ⟨fun u => (novelBasis phi vars h).equivFun p ((cubeEquiv vars).symm u), ?_⟩
    change (novelBasis phi vars h).equivFun.symm
      (fun j => (novelBasis phi vars h).equivFun p ((cubeEquiv vars).symm (cubeEquiv vars j))) = p
    simp only [Equiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The coefficient polynomial as a sum of the generic CompPoly novel polynomials. -/
theorem coefficientPolynomial_eq_sum (vars : ℕ) (h : vars ≤ 64) (f : Whir.Table S vars) :
    (coefficientPolynomial phi vars h f : S[X]) =
      ∑ j : Fin (2 ^ vars), C (f (mask vars j)) *
        AdditiveNTT.Xⱼ (ZMod 2) (fun j => phi (basis j)) vars h j := by
  simp only [coefficientPolynomial, Basis.equivFun_symm_apply, Submodule.coe_sum,
    Submodule.coe_smul_of_tower, smul_eq_C_mul, novelBasis_apply]

/-- The WHIR column formula is evaluation of CompPoly's coefficient polynomial. -/
theorem encode_eq_eval (vars rate : ℕ) (h : vars + rate ≤ 64) (f : Whir.Table S vars)
    (x : (encoding vars rate h).Columns) :
    (encoding vars rate h).encode phi f x =
      (coefficientPolynomial phi vars (by omega) f : S[X]).eval (phi (domain h x)) := by
  rw [coefficientPolynomial_eq_sum, Polynomial.eval_finsetSum]
  unfold Whir.Encoding.encode
  rw [← (cubeEquiv vars).sum_comp]
  apply Finset.sum_congr rfl
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, AdditiveNTT.Xⱼ, Polynomial.eval_prod]
  simp only [map_prod, eval_pow,
    Nat.getBit_eq_testBit, cubeEquiv_apply]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  change phi (if j.val.testBit i.val then _ else 1) = _
  split_ifs with hb
  · simpa only [hb, ↓reduceIte, pow_one, Fin.castLE] using
      (normalizedSubspaceValue_map phi _ _).trans (normalizedSubspaceValue_eq_eval phi _ _)
  · simp only [pow_zero, map_one]

omit [Fintype S] [Algebra (ZMod 2) S] in
/-- Low-degree polynomial evaluation is injective on the full additive domain. -/
theorem evaluation_injective (vars rate : ℕ) (h : vars + rate ≤ 64) :
    Function.Injective (fun p : degreeLT S (2 ^ vars) =>
      fun x : (encoding vars rate h).Columns => (p : S[X]).eval (phi (domain h x))) := by
  intro p q hpq
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero (p.val - q.val)
    (phi.injective.comp (domain h).injective)
    (fun x => by simpa only [Polynomial.eval_sub, sub_eq_zero, Function.comp_apply] using congrFun hpq x)
  have hd : (p.val - q.val).degree < (2 ^ vars : ℕ) :=
    (Polynomial.degree_sub_le _ _).trans_lt
      (max_lt (mem_degreeLT.mp p.property) (mem_degreeLT.mp q.property))
  have hn : (p.val - q.val).natDegree < 2 ^ vars := by
    by_cases hz : p.val - q.val = 0
    · simpa only [hz, Polynomial.natDegree_zero] using Nat.two_pow_pos vars
    · exact (Polynomial.natDegree_lt_iff_degree_lt hz).mpr hd
  simpa only [Fintype.card_fin] using hn.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.le_add_right vars rate))

/-- The concrete additive novel-basis encoding is injective after scalar extension. -/
theorem encoding_injective (vars rate : ℕ) (h : vars + rate ≤ 64) :
    Function.Injective ((encoding vars rate h).encode phi) := by
  intro f g hfg
  apply (coefficientPolynomial_bijective phi vars (by omega)).injective
  apply evaluation_injective phi vars rate h
  funext x
  simpa only [encode_eq_eval] using congrFun hfg x

/-- The encoder's image is exactly the Reed–Solomon code on the extended additive domain. -/
theorem encoding_image (vars rate : ℕ) (h : vars + rate ≤ 64) :
    Set.range ((encoding vars rate h).encode phi) =
      (ReedSolomon.code ((encoding vars rate h).extendedDomain phi) (2 ^ vars) :
        Set ((encoding vars rate h).Columns → S)) := by
  ext word
  constructor
  · rintro ⟨f, rfl⟩
    apply ReedSolomon.mem_code_iff_eval.mpr
    refine ⟨coefficientPolynomial phi vars (by omega) f,
      mem_degreeLT.mp (coefficientPolynomial phi vars (by omega) f).property, ?_⟩
    intro x
    exact (encode_eq_eval phi vars rate h f x).symm
  · intro hword
    obtain ⟨p, hp, heval⟩ := ReedSolomon.mem_code_iff_eval.mp hword
    obtain ⟨f, hf⟩ := (coefficientPolynomial_bijective phi vars (by omega)).surjective
      ⟨p, mem_degreeLT.mpr hp⟩
    refine ⟨f, ?_⟩
    funext x
    rw [encode_eq_eval, hf]
    exact heval x

/-- WHIR's complete encoder contract for the normalized flat basis, including dimension 64. -/
theorem encodingContract (vars rate : ℕ) (h : vars + rate ≤ 64) (hrate : 0 < rate) :
    Whir.EncodingContract (encoding vars rate h) phi where
  rate_pos := hrate
  dimension_le := h
  novel := encoding_novel vars rate h
  additive := domain_additive h
  injective := encoding_injective phi vars rate h
  image := encoding_image phi vars rate h

end ScalarExtension
end CompStark.Pcs

namespace CompStark.Pcs
open CompStark.BinaryFields Polynomial

/-- The base-field contract used by WHIR's initial oracle. -/
theorem baseEncodingContract (vars rate : ℕ) (h : vars + rate ≤ 64) (hrate : 0 < rate) :
    Whir.EncodingContract (encoding vars rate h) (RingHom.id K) :=
  encodingContract (RingHom.id K) vars rate h hrate

/-- The extension-field contract used by WHIR's challenge-field levels. -/
theorem extensionEncodingContract (vars rate : ℕ) (h : vars + rate ≤ 64) (hrate : 0 < rate) :
    Whir.EncodingContract (encoding vars rate h) (algebraMap K E) := by
  let : Fintype E := Fintype.ofFinite E
  let : Algebra (ZMod 2) E := (ZMod.castHom (by decide) E).toAlgebra
  exact encodingContract (algebraMap K E) vars rate h hrate

/-- Domain dimension accepted by the production `AdditiveNttF64::standard` constructor. -/
def ProductionDimension (vars rate : ℕ) : Prop := vars + rate ≤ 63

/-- The production encoder's explicit dimension check implies CompPoly's strict bound. -/
theorem production_dimension_lt {vars rate : ℕ} (h : ProductionDimension vars rate) :
    vars + rate < 64 := by exact Nat.lt_succ_of_le h

section Executable
variable {S : Type} [Field S] [Fintype S] [DecidableEq S] [Algebra (ZMod 2) S]
  (phi : K →+* S)

omit [DecidableEq S] in
/-- At level zero, CompPoly's domain enumeration is the flat ordered binary domain. -/
theorem evaluationPoint_zero (vars rate : ℕ) (h : vars + rate < 64)
    (x : Fin (2 ^ (vars + rate))) :
    AdditiveNTT.evaluationPointω (ZMod 2) (fun j => phi (basis j)) h
      (0 : Fin 64) (by exact Nat.zero_le vars) x = phi (domain h.le x) := by
  have hw : AdditiveNTT.normalizedW (ZMod 2) (fun j => phi (basis j)) (0 : Fin 64) = X := by
    rw [AdditiveNTT.normalizedW₀_eq_1_div_β₀]
    rw [basis_zero, map_one, div_one, C_1, mul_one]
  simp only [AdditiveNTT.evaluationPointω, show ((0 : Fin 64) : ℕ) = 0 from rfl,
    Nat.zero_add,
    domain, Function.Embedding.coeFn_mk, domainValue, map_sum, apply_ite phi, map_zero]
  apply Finset.sum_congr rfl
  intro i _
  change (if Nat.getBit i.val x.val = 1 then
    (AdditiveNTT.normalizedW (ZMod 2) (fun j => phi (basis j)) (0 : Fin 64)).eval
      (phi (basis (Fin.castLE h.le i))) else 0) = _
  rw [hw]
  simp only [Polynomial.eval_X, Nat.getBit_eq_testBit]
  cases x.val.testBit i.val <;> rfl

/-- CompPoly's executable additive NTT computes exactly the WHIR encoder's columns.
The strict bound is explicit; the algebraic `encodingContract` also covers dimension 64. -/
theorem computableAdditiveNTT_eq_encode (vars rate : ℕ) (h : vars + rate < 64)
    (f : Whir.Table S vars) :
    AdditiveNTT.computableAdditiveNTT (𝔽q := ZMod 2) (β := fun j => phi (basis j))
      (ℓ := vars) (R_rate := rate) h (fun j => f (mask vars j)) =
        (encoding vars rate h.le).encode phi f := by
  let : Fact (LinearIndependent (ZMod 2) (fun j => phi (basis j))) :=
    ⟨extendedBasis_independent phi⟩
  let : Fact ((fun j => phi (basis j)) 0 = 1) := ⟨by change phi (basis 0) = 1; rw [basis_zero, map_one]⟩
  rw [AdditiveNTT.computableAdditiveNTT_eq_additiveNTT]
  funext x
  rw [AdditiveNTT.additiveNTT_correctness (ZMod 2) (fun j => phi (basis j)) h
    (by omega) _ _ rfl x]
  change (AdditiveNTT.polynomialFromNovelCoeffs (ZMod 2) (fun j => phi (basis j)) vars
    (by omega) (fun j => f (mask vars j))).eval
      (AdditiveNTT.evaluationPointω (ZMod 2) (fun j => phi (basis j)) h
        (0 : Fin 64) (Nat.zero_le vars) x) = _
  rw [evaluationPoint_zero]
  exact (congrArg (fun p : S[X] => p.eval (phi (domain h.le x)))
    (coefficientPolynomial_eq_sum phi vars (by omega) f)).symm.trans
      (encode_eq_eval phi vars rate h.le f x).symm

end Executable
end CompStark.Pcs
