/-
  CompStark.Multilinear.Algebra.GrandProduct

  The grand-product polynomial of a multiset of tuples: it determines the multiset, and two
  different multisets give equal values at few points of a finite field. Candidate for ArkLib.
-/

module

public import CompStark.Multilinear.Algebra.Fingerprint
public import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Roots

/-!
# Grand products of multilinear fingerprints

A tuple is a table on `n` variables, and its fingerprint is the symbolic multilinear extension
`fingerprintPoly` (`CompStark.Multilinear.Algebra.Fingerprint`). The grand product of a multiset
`M` of tuples is `grandProductPoly M = Π_{t ∈ M} (X − fingerprint(t))`, a polynomial in the `n`
fingerprint variables and one more, `X`, indexed by `none`.

* Over an integral domain the polynomial determines the multiset, multiplicities included
  (`grandProductPoly_injective`): read as a polynomial in `X` over the fingerprint variables, it
  is monic and its roots are the fingerprints, and fingerprints determine their tuples. No bound
  relates the characteristic to the multiset's size.
* Each factor has total degree at most `max 1 n`, so two different multisets of at most `cap`
  tuples differ by a nonzero polynomial of degree at most `max 1 n · cap`, which vanishes at no
  more than `max 1 n · cap · |F|ⁿ` of the `|F|ⁿ⁺¹` points over a finite field `F`
  (`card_grandProduct_collision_le`, by ArkLib's counting Schwartz–Zippel). The multisets are
  fixed before the point.

The fingerprint is derived from leanth PR 16, revision
`23929f8c922cd4461ab22dbfaa6520f3ad23a3b2`, as attributed in `ToCompPoly/Fingerprint.lean`; the
product argument is new and uses Mathlib's `Polynomial.roots_multiset_prod_X_sub_C`. Requested
upstream as [ArkLib #901](https://github.com/Verified-zkEVM/ArkLib/issues/901).
-/

namespace CompStark.Multilinear.Algebra

open CompPoly CMlPolynomialEval

@[expose] public section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The product in a separate univariate challenge over the fingerprint coefficient ring. -/
noncomputable def grandProductUnivariate (M : Multiset (CMlPolynomialEval R n)) :
    Polynomial (MvPolynomial (Fin n) R) :=
  (M.map fun t ↦ Polynomial.X - Polynomial.C (fingerprintPoly t)).prod

/-- The same grand product with the product and fingerprint challenges as separate variables. -/
noncomputable def grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial (Option (Fin n)) R :=
  (M.map fingerprintFactorPoly).prod

/-- Renaming by `some` lands in the constant coefficients of the polynomial in the variable
`none`. -/
private theorem optionEquivLeft_rename_some {R σ : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) :
    MvPolynomial.optionEquivLeft R σ (MvPolynomial.rename some p) =
      Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- The joint-variable and univariate representations agree through the standard equivalence. -/
theorem optionEquivLeft_grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial.optionEquivLeft R (Fin n) (grandProductPoly M) =
      grandProductUnivariate M := by
  simp [grandProductPoly, grandProductUnivariate, map_multiset_prod,
    Multiset.map_map, Function.comp_def, fingerprintFactorPoly,
    optionEquivLeft_rename_some]

/-- Evaluation of the symbolic grand product is the actual product of fingerprint factors. -/
theorem eval₂_grandProductPoly {S : Type*} [CommRing S]
    (M : Multiset (CMlPolynomialEval R n)) (φ : R →+* S) (z : Vector S n) (β : S) :
    MvPolynomial.eval₂ φ (fun i ↦ i.elim β (fun j ↦ z[j])) (grandProductPoly M) =
      (M.map fun t ↦ β - eval₂Mle t φ z).prod := by
  change MvPolynomial.eval₂Hom φ (fun i ↦ i.elim β (fun j ↦ z[j]))
    (grandProductPoly M) = _
  simp only [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    MvPolynomial.coe_eval₂Hom, eval₂_fingerprintFactorPoly]

/-- Grand products commute with coefficient maps, including noninjective maps. -/
theorem map_grandProductPoly {S : Type*} [CommRing S]
    (φ : R →+* S) (M : Multiset (CMlPolynomialEval R n)) :
    MvPolynomial.map φ (grandProductPoly M) =
      grandProductPoly (M.map (CMlPolynomialEval.map φ)) := by
  simp [grandProductPoly, map_multiset_prod, Multiset.map_map, Function.comp_def,
    fingerprintFactorPoly, MvPolynomial.map_rename, map_fingerprintPoly]

/-- An injective coefficient embedding preserves the complete multiset of tuples. -/
theorem map_tupleMultiset_injective {R S : Type*} [Semiring R] [Semiring S]
    (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (Multiset.map (CMlPolynomialEval.map (n := n) φ)) := by
  exact Multiset.map_injective fun _ _ h ↦
    (Vector.map_inj_right fun _ _ h ↦ hφ h).mp h

/-- Every tuple contributes at most `max 1 n` to the joint total degree. -/
theorem totalDegree_grandProductPoly (M : Multiset (CMlPolynomialEval R n)) :
    (grandProductPoly M).totalDegree ≤ max 1 n * M.card := by
  refine (MvPolynomial.totalDegree_multiset_prod _).trans ?_
  simp only [Multiset.map_map, Function.comp_def]
  simpa [Nat.mul_comm] using
    (Multiset.sum_le_card_nsmul
      (M.map fun t ↦ (fingerprintFactorPoly t).totalDegree) (max 1 n)
      (by simpa using fun t (_ : t ∈ M) ↦ totalDegree_fingerprintFactorPoly t))

section Domain

variable [IsDomain R]

/-- The roots are exactly the fingerprints, with their original natural multiplicities. -/
theorem roots_grandProductUnivariate (M : Multiset (CMlPolynomialEval R n)) :
    (grandProductUnivariate M).roots = M.map fingerprintPoly := by
  have h := Polynomial.roots_multiset_prod_X_sub_C (M.map fingerprintPoly)
  simpa only [Multiset.map_map, Function.comp_def, grandProductUnivariate] using h

/-- Symbolic grand products determine tuple multisets in every characteristic. -/
theorem grandProductPoly_injective :
    Function.Injective (grandProductPoly (R := R) (n := n)) := by
  intro M N h
  have hu := congrArg (MvPolynomial.optionEquivLeft R (Fin n)) h
  rw [optionEquivLeft_grandProductPoly, optionEquivLeft_grandProductPoly] at hu
  have hr := congrArg Polynomial.roots hu
  rw [roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr

/-- Distinct multisets yield a nonzero difference polynomial without a cardinality premise. -/
theorem grandProduct_difference_ne_zero
    {M N : Multiset (CMlPolynomialEval R n)} (h : M ≠ N) :
    grandProductPoly M - grandProductPoly N ≠ 0 := by
  intro hz
  exact h (grandProductPoly_injective (sub_eq_zero.mp hz))

end Domain

/-- A common cardinality cap bounds the degree of the difference; the cardinalities may differ. -/
theorem totalDegree_grandProduct_difference_le
    (M N : Multiset (CMlPolynomialEval R n)) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (grandProductPoly M - grandProductPoly N).totalDegree ≤ max 1 n * cap := by
  refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
  · exact (totalDegree_grandProductPoly M).trans (Nat.mul_le_mul_left _ hM)
  · exact (totalDegree_grandProductPoly N).trans (Nat.mul_le_mul_left _ hN)

section FiniteField

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Two different multisets of at most `cap` tuples have grand products that agree at no more
than `max 1 n · cap · |F|ⁿ` of the `|F|ⁿ⁺¹` points, the bound attained in dimension zero. -/
theorem card_grandProduct_collision_le
    (M N : Multiset (CMlPolynomialEval F n)) (hne : M ≠ N) {cap : ℕ}
    (hM : M.card ≤ cap) (hN : N.card ≤ cap) :
    (Finset.univ.filter fun x : Option (Fin n) → F ↦
      MvPolynomial.eval x (grandProductPoly M) =
        MvPolynomial.eval x (grandProductPoly N)).card ≤
      (max 1 n * cap) * Fintype.card F ^ n := by
  have h := MvPolynomial.card_zeros_le_of_totalDegree_le
    (grandProductPoly M - grandProductPoly N)
    (grandProduct_difference_ne_zero hne)
    (totalDegree_grandProduct_difference_le M N hM hN)
  simpa only [MvPolynomial.eval_sub, sub_eq_zero, Fintype.card_option,
    Fintype.card_fin, Nat.add_sub_cancel] using h

end FiniteField

end
end CompStark.Multilinear.Algebra
