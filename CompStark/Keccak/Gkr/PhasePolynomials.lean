/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Keccak.Gkr.ResidualAlgebra

/-! # Concrete polynomial realizations of the GKR residuals -/

@[expose] public section
open scoped BigOperators
namespace CompStark.Keccak.Gkr
open MvPolynomial

/-- Coordinate degree caps are preserved by finite sums. -/
theorem coordinate_sum_degree {E : Type*} [CommRing E] {n k : Nat} {ι : Type*} [Fintype ι]
    (f : ι → MvPolynomial (Fin n) E) (i : Fin n)
    (h : ∀ j, (f j).degreeOf i ≤ k) : (∑ j, f j).degreeOf i ≤ k := by
  exact (MvPolynomial.degreeOf_sum_le i _ _).trans (Finset.sup_le fun j _ => h j)

/-- Coordinate degree caps add under multiplication. -/
theorem coordinate_mul_degree {E : Type*} [CommRing E] {n a b : Nat}
    (f g : MvPolynomial (Fin n) E) (i : Fin n)
    (hf : f.degreeOf i ≤ a) (hg : g.degreeOf i ≤ b) : (f*g).degreeOf i ≤ a+b :=
  (MvPolynomial.degreeOf_mul_le i f g).trans (Nat.add_le_add hf hg)

/-- Coordinate degree caps are preserved by addition. -/
theorem coordinate_add_degree {E : Type*} [CommRing E] {n a : Nat}
    (f g : MvPolynomial (Fin n) E) (i : Fin n)
    (hf : f.degreeOf i ≤ a) (hg : g.degreeOf i ≤ a) : (f+g).degreeOf i ≤ a :=
  (MvPolynomial.degreeOf_add_le i f g).trans (max_le hf hg)

/-- A Boolean-table interpolation has coordinate degree at most one. -/
theorem tablePolynomial_degree {E : Type*} [CommRing E] {n : Nat}
    (a : Fin (2^n) → E) (i : Fin n) : (MvPolynomial.MLE' a).degreeOf i ≤ 1 :=
  MvPolynomial.MLE_degreeOf _ i

/-- The chi gate polynomial after fixing the product-evaluation challenge. -/
noncomputable def chiPolynomial {E : Type*} [CommRing E] {n : Nat}
    (one : E) (a : Fin 3 → MvPolynomial (Fin n) E) : MvPolynomial (Fin n) E :=
  C one * a 0 + (C one + a 1) * a 2

/-- Three multilinear shifted evaluations give a quadratic chi expression. -/
theorem chiPolynomial_degree {E : Type*} [CommRing E] {n : Nat}
    (one : E) (a : Fin 3 → MvPolynomial (Fin n) E) (i : Fin n)
    (ha : ∀ k, (a k).degreeOf i ≤ 1) : (chiPolynomial one a).degreeOf i ≤ 2 := by
  unfold chiPolynomial
  apply coordinate_add_degree
  · exact (coordinate_mul_degree _ _ i (le_refl ((C one).degreeOf i)) (ha 0)).trans (by
      simp only [degreeOf_C]; omega)
  · exact coordinate_mul_degree _ _ i
      (coordinate_add_degree _ _ i (by simp only [degreeOf_C]; omega) (ha 1)) (ha 2)

/-- The equality polynomial evaluates to the wire equality kernel. -/
theorem equalityPolynomial_eval {E : Type*} [CommRing E] {n : Nat}
    (r s : Fin n → E) : MvPolynomial.eval s (MvPolynomial.eqPolynomial r) = eqEval r s := by
  simp only [MvPolynomial.eqPolynomial_expanded, map_prod, map_add, map_mul, map_sub,
    map_one, MvPolynomial.eval_C, MvPolynomial.eval_X, eqEval]

/-- The pack-and-segment residual has a concrete multivariate polynomial realization. -/
noncomputable def packPolynomial {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E) : MvPolynomial (Fin (p+1)) E :=
  eqPolynomial c.point * ∑ j : Fin 1600, C (c.weights j) *
    chiPolynomial (∑ i, muAt s i) (fun k => MLE' (packTable q d s (along j k.val)))

/-- Evaluating the pack polynomial recovers the actual pack summand. -/
theorem packPolynomial_eval {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E) (r : Fin (p+1) → E) :
    MvPolynomial.eval r (packPolynomial q d c s) = packSummand q d c s r := by
  simp only [packPolynomial, chiPolynomial, map_mul, map_sum, map_add, eval_C,
    equalityPolynomial_eval, mle_eq_eval, ← linearAtPack_eq_mle, packSummand]
  have h (j : Fin 1600) : along j 0 = j := by
    apply Fin.ext
    simp only [along, Nat.add_zero, Nat.mod_mod]
    have hq : j.val / 64 < 25 := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simp)
    omega
  simp only [Fin.val_zero, Fin.val_one, h]
  rfl

/-- Equality times a quadratic chi summand gives the pack-and-segment cubic cap. -/
theorem packPolynomial_degree {E : Type*} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (s : E) (i : Fin (p+1)) :
    (packPolynomial q d c s).degreeOf i ≤ 3 := by
  apply coordinate_mul_degree _ _ i (MvPolynomial.eqPolynomial_degreeOf _ _) (a := 1) (b := 2)
  apply coordinate_sum_degree
  intro j
  simpa only [zero_add] using coordinate_mul_degree _ _ i
    (show (C (c.weights j) : MvPolynomial (Fin (p+1)) E).degreeOf i ≤ 0 by simp only [degreeOf_C, le_refl])
    (chiPolynomial_degree _ _ i (fun _ => tablePolynomial_degree _ i))

/-- Position interpolation uses the actual zero-padded shifted tables. -/
noncomputable def positionPolynomial {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) : MvPolynomial (Fin 11) E :=
  C (eqEval c.point t.packPoint) *
    MLE' (fun j : Fin 2048 => if h : j.val < 1600 then c.weights ⟨j.val,h⟩ else 0) *
    chiPolynomial (∑ i, muAt t.point i) (fun k => MLE' (fun j : Fin 2048 =>
      if h : j.val < 1600 then linearAtPack q d t.point t.packPoint (along ⟨j.val,h⟩ k.val) else 0))

/-- The position polynomial evaluates to the concrete position summand. -/
theorem positionPolynomial_eval {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) (r : Fin 11 → E) :
    MvPolynomial.eval r (positionPolynomial q d c t) = positionSummand q d c t r := by
  simp only [positionPolynomial, chiPolynomial, map_mul, map_add, eval_C, mle_eq_eval,
    positionSummand, shiftedEvaluation]
  rfl

/-- One multilinear weight and a quadratic chi gate give the position cubic cap. -/
theorem positionPolynomial_degree {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (q : Witness p) (d : Fin 12) (c : Claim E p) (t : LayerTranscript E p) (i : Fin 11) :
    (positionPolynomial q d c t).degreeOf i ≤ 3 := by
  apply coordinate_mul_degree _ _ i (a := 1) (b := 2)
  · simpa only [zero_add] using coordinate_mul_degree _ _ i
      (show (C (eqEval c.point t.packPoint) : MvPolynomial (Fin 11) E).degreeOf i ≤ 0 by simp only [degreeOf_C, le_refl])
      (tablePolynomial_degree _ i)
  · exact chiPolynomial_degree _ _ i (fun _ => tablePolynomial_degree _ i)

/-- The committed-middle opening is a product of its weight and word interpolations. -/
noncomputable def wordPolynomial {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) : MvPolynomial (Fin 6) E :=
  MLE' (fun slot : Fin 64 => if _h : 25 ≤ slot.val ∧ slot.val < 50 then
    (1-t.segment)*eqWeight t.lanePoint (slot.val-25) else 0) * MLE' (middleWord x q t)

/-- The committed-middle polynomial evaluates to its concrete opening summand. -/
theorem wordPolynomial_eval {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (r : Fin 6 → E) :
    MvPolynomial.eval r (wordPolynomial x q t) = wordSummand x q t r := by
  simp only [wordPolynomial, map_mul, mle_eq_eval, wordSummand]

/-- The committed-middle opening has coordinate degree at most two. -/
theorem wordPolynomial_degree {E : Type} [CommRing E] [CharP E 2] {p : Nat}
    (x : E) (q : Witness p) (t : Transcript E p) (i : Fin 6) :
    (wordPolynomial x q t).degreeOf i ≤ 2 :=
  coordinate_mul_degree _ _ i (tablePolynomial_degree _ i) (tablePolynomial_degree _ i)

end CompStark.Keccak.Gkr
