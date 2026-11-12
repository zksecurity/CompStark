/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Algebra.GrandProduct

/-! Beta-independent padding factors preserve the tuple roots of a fingerprint grand product. -/

@[expose] public section

namespace CompStark.Multilinear.Algebra
open CompPoly CMlPolynomialEval
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R] {n : ℕ}
omit [IsDomain R] in
/-- Coefficients independent of beta become constant univariate polynomials. -/
theorem optionEquivLeft_alpha (p : MvPolynomial (Fin n) R) :
    MvPolynomial.optionEquivLeft R (Fin n) (MvPolynomial.rename some p) = Polynomial.C p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]
/-- Nonzero beta-independent factors preserve the grand product's tuple roots. -/
theorem paddedGrandProduct_injective (A B : MvPolynomial (Fin n) R)
    (hA : A ≠ 0) (hB : B ≠ 0) (M N : Multiset (CMlPolynomialEval R n))
    (heq : MvPolynomial.rename some A * grandProductPoly M =
      MvPolynomial.rename some B * grandProductPoly N) : M = N := by
  have h := congrArg (MvPolynomial.optionEquivLeft R (Fin n)) heq
  rw [map_mul, map_mul, optionEquivLeft_alpha, optionEquivLeft_alpha,
    optionEquivLeft_grandProductPoly, optionEquivLeft_grandProductPoly] at h
  have hr := congrArg Polynomial.roots h
  rw [Polynomial.roots_C_mul _ hA, Polynomial.roots_C_mul _ hB,
    roots_grandProductUnivariate, roots_grandProductUnivariate] at hr
  exact Multiset.map_injective fingerprintPoly_injective hr
end
end CompStark.Multilinear.Algebra
