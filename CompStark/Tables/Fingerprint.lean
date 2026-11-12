/-
Copyright (c) 2026 zkSecurity.
Adapted from Verified-zkEVM/leanerVM (Apache-2.0), revision a9d42bfdae8081a4e16aef1cd8526cdaa2a8f4d6:
LeanerVM.Protocol.Fingerprint and BusSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Basic
public import CompStark.Multilinear.Algebra.GrandProduct

/-! Fingerprints of tuples of `2 ^ k` base-field values at `k` extension-field challenges, the
grand products of multisets of fingerprints, and the bound on their collisions. -/

@[expose] public section

namespace CompStark.Tables

open CompStark.BinaryFields CompStark.Multilinear OracleComp

noncomputable section

/-- The fingerprint of an extension-field tuple of `2 ^ k` entries at `k` coordinates. -/
def fingerprintE (k : ℕ) (α : Fin k → E) (tuple : Fin (2 ^ k) → E) : E :=
  ∑ i : Fin (2 ^ k), tuple i * ∏ j : Fin k, eqFactor (α j) (bit i.val j.val)

/-- The fingerprint of a base-field tuple of `2 ^ k` entries. -/
def fingerprint (k : ℕ) (α : Fin k → E) (tuple : Vector K (2 ^ k)) : E :=
  fingerprintE k α (fun i ↦ ofK tuple[i])

/-- The fingerprint is CompPoly's mixed-ring multilinear evaluation of the tuple. -/
theorem fingerprint_eq_eval₂Mle (k : ℕ) (α : Fin k → E) (t : Vector K (2 ^ k)) :
    fingerprint k α t = CompPoly.CMlPolynomialEval.eval₂Mle t (algebraMap K E) (Vector.ofFn α) := by
  rw [fingerprint, fingerprintE, CompPoly.CMlPolynomialEval.eval₂Mle, Algebra.evalMle_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.getElem_fin]
  rw [Algebra.lagrangeBasis_getElem_nat]
  simp only [CompPoly.CMlPolynomialEval.map, Fin.getElem_fin, Vector.getElem_map,
    CompPoly.Extension.Ext.algebraMap_eq_ofBase]
  apply congrArg (fun v : E ↦ ofK t[i] * v)
  apply Finset.prod_congr rfl
  intro j _
  dsimp only [eqFactor, bit]
  split <;> simp only [Vector.getElem_ofFn, sub_zero, sub_self, mul_one, mul_zero,
    zero_add, add_zero]

/-- The grand product of `β` minus the fingerprints of a multiset of tuples. -/
def sideProduct (k : ℕ) (α : Fin k → E) (β : E) (tuples : Multiset (Vector K (2 ^ k))) : E :=
  (tuples.map fun t ↦ β - fingerprint k α t).prod

/-- Two different multisets of at most `cap` tuples have equal grand products at a uniform
`(α, β)` with probability at most `max 1 k · cap / |E|`. -/
theorem sideProduct_collision_le (k : ℕ) (P Q : Multiset (Vector K (2 ^ k))) (cap : ℕ)
    (hne : P ≠ Q) (hP : P.card ≤ cap) (hQ : Q.card ≤ cap) :
    Pr{let ab ← ($ᵗ ((Fin k → E) × E))}[
      sideProduct k ab.1 ab.2 P = sideProduct k ab.1 ab.2 Q] ≤ overE (max 1 k * cap) := by
  classical
  let φ := algebraMap K E
  let P' := P.map (CompPoly.CMlPolynomialEval.map (n := k) φ)
  let Q' := Q.map (CompPoly.CMlPolynomialEval.map (n := k) φ)
  have hne' : P' ≠ Q' := fun h ↦ hne (Algebra.map_tupleMultiset_injective φ φ.injective h)
  let e : (Fin k → E) × E ≃ (Option (Fin k) → E) := {
    toFun := fun ab i ↦ i.elim ab.2 ab.1
    invFun := fun x ↦ (fun i ↦ x (some i), x none)
    left_inv := fun _ ↦ rfl
    right_inv := fun x ↦ funext fun i ↦ by cases i <;> rfl }
  have hval (ab : (Fin k → E) × E) (M : Multiset (Vector K (2 ^ k))) :
      sideProduct k ab.1 ab.2 M = MvPolynomial.eval (e ab)
        (Algebra.grandProductPoly (M.map (CompPoly.CMlPolynomialEval.map (n := k) φ))) := by
    rw [← Algebra.map_grandProductPoly, MvPolynomial.eval_map]
    have h := Algebra.eval₂_grandProductPoly M φ (Vector.ofFn ab.1) ab.2
    have heval : (fun i : Option (Fin k) ↦ i.elim ab.2 (fun j ↦ (Vector.ofFn ab.1)[j])) =
        e ab := by
      funext i
      cases i with
      | none => rfl
      | some i =>
        change (Vector.ofFn ab.1)[i] = ab.1 i
        simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rw [heval] at h
    rw [h, sideProduct]
    exact congrArg Multiset.prod (Multiset.map_congr rfl fun t _ ↦ by
      rw [fingerprint_eq_eval₂Mle])
  have hcount : Nat.card {ab : (Fin k → E) × E //
      sideProduct k ab.1 ab.2 P = sideProduct k ab.1 ab.2 Q} ≤
      max 1 k * cap * Fintype.card E ^ k := by
    have hc := Algebra.card_grandProduct_collision_le P' Q' hne'
      (cap := cap) (by simpa [P'] using hP) (by simpa [Q'] using hQ)
    rw [Nat.card_congr (e.subtypeEquiv (q := fun x ↦
        MvPolynomial.eval x (Algebra.grandProductPoly P') =
          MvPolynomial.eval x (Algebra.grandProductPoly Q')) fun ab ↦ by
            rw [hval, hval]), Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hc
  have hcard : Fintype.card ((Fin k → E) × E) = Fintype.card E * Fintype.card E ^ k := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, mul_comm]
  have hdiv : overE (max 1 k * cap) =
      ((max 1 k * cap * Fintype.card E ^ k : ℕ) : ENNReal) /
        Fintype.card ((Fin k → E) × E) := by
    rw [overE, hcard, Nat.cast_mul (max 1 k * cap), Nat.cast_mul (Fintype.card E),
      ENNReal.mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr (pow_ne_zero _ Fintype.card_ne_zero))
        (ENNReal.natCast_ne_top _)]
  rw [hdiv, SampleableType.prEvent_uniformSample_le_div_iff, ← Fintype.card_subtype,
    ← Nat.card_eq_fintype_card]
  exact hcount

end

end CompStark.Tables
