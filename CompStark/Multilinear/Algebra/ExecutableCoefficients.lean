/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompPoly.Univariate.Lagrange
public import ArkLib.ProofSystem.Sumcheck.Interaction.BadEvents

/-! Executable recovery of bounded round coefficients from their field evaluations. -/

@[expose] public section
namespace CompStark.Multilinear
open CompPoly Sumcheck.Interaction.Knowledge

/-- Interpolate a degree-bounded round using its fixed public distinct nodes. -/
def roundCoefficients {F : Type} [Field F] [BEq F] [LawfulBEq F] {degree : ℕ}
    (nodes : Fin (degree + 1) → F) (value : F → F) : Coefficients F degree :=
  let polynomial := CPolynomial.CLagrange.interpolate Finset.univ nodes (fun i => value (nodes i))
  fun j => polynomial.coeff j.val

/-- Materialize one interpolated polynomial's finite coefficient vector. -/
@[noinline, nospecialize] def roundCoefficientImage {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {degree : ℕ} (nodes : Fin (degree + 1) → F) (value : F → F) : Vector F (degree + 1) :=
  let polynomial := CPolynomial.CLagrange.interpolate Finset.univ nodes (fun i => value (nodes i))
  Vector.ofFn fun j => polynomial.coeff j.val

/-- Materialized coefficients agree with each scalar interpolation coefficient. -/
theorem roundCoefficientImage_get {F : Type} [Field F] [BEq F] [LawfulBEq F]
    {degree : ℕ} (nodes : Fin (degree + 1) → F) (value : F → F) (j : Fin (degree + 1)) :
    (roundCoefficientImage nodes value)[j.val] = roundCoefficients nodes value j := by
  simp only [roundCoefficientImage, Vector.getElem_ofFn, roundCoefficients]

/-- Interpolated runtime coefficients are those of the polynomial represented by the round evaluator. -/
theorem roundCoefficients_coeff {F : Type} [Field F] [BEq F] [LawfulBEq F] {degree : ℕ}
    (nodes : Fin (degree + 1) → F) (distinct : Function.Injective nodes)
    (value : F → F) (polynomial : Polynomial.degreeLE F degree)
    (evaluation : ∀ r, value r = polynomial.val.eval r) (j : Fin (degree + 1)) :
    roundCoefficients nodes value j = polynomial.val.coeff j.val := by
  have same := Lagrange.eq_interpolate_of_eval_eq
    (s := Finset.univ) (v := nodes) (fun i => value (nodes i))
    (fun i _ k _ equal => distinct equal)
    (show polynomial.val.degree < ((Finset.univ : Finset (Fin (degree + 1))).card : ℕ) by
      rw [Finset.card_univ, Fintype.card_fin]
      exact lt_of_le_of_lt (Polynomial.mem_degreeLE.mp polynomial.property)
        (by exact_mod_cast Nat.lt_succ_self degree))
    (fun i _ => (evaluation (nodes i)).symm)
  simp only [roundCoefficients, CPolynomial.coeff_toPoly,
    CPolynomial.CLagrange.cinterpolate_eq_interpolate, ← same]

/-- A bounded polynomial vanishes when all its executable coefficients vanish. -/
theorem polynomial_eq_zero_of_coefficients_zero {F : Type} [Semiring F] {degree : ℕ}
    (polynomial : Polynomial.degreeLE F degree) (coefficients : Coefficients F degree)
    (correct : ∀ j, coefficients j = polynomial.val.coeff j.val) (zero : coefficients = 0) :
    polynomial.val = 0 := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_zero]
  by_cases bounded : i < degree + 1
  · rw [← correct ⟨i, bounded⟩, zero]
    rfl
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have cap := Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp polynomial.property)
    omega

end CompStark.Multilinear
