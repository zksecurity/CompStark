/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.Basic

/-! Fixed-polynomial agreement bounds obtained from the retained-witness sumcheck certificate. A singleton domain supplies a separating sum check for weighted round polynomials. -/

@[expose] public section

open CompStark.BinaryFields
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
namespace CompStark.Multilinear
open MvPolynomial Sumcheck.Interaction.MultivariateRound
noncomputable section
/-- A univariate polynomial represented on one multivariate coordinate. -/
def oneVariable (p : Polynomial E) : MvPolynomial (Fin 1) E :=
  ∑ k ∈ p.support, C (p.coeff k) * X 0 ^ k
/-- The one-variable representation evaluates as the original polynomial. -/
theorem oneVariable_eval (p : Polynomial E) (r : Fin 1 → E) :
    MvPolynomial.eval r (oneVariable p) = p.eval (r 0) := by
  simp only [oneVariable, map_sum, map_mul, MvPolynomial.eval_C, map_pow, MvPolynomial.eval_X,
    Polynomial.eval_eq_sum, Polynomial.sum]
/-- The one-variable representation has the original degree bound. -/
theorem oneVariable_degree (p : Polynomial E) (j : Fin 1) :
    (oneVariable p).degreeOf j ≤ p.natDegree := by
  unfold oneVariable
  refine (degreeOf_sum_le j _ _).trans (Finset.sup_le fun k hk ↦ ?_)
  refine (degreeOf_mul_le j _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_pow_le j _ _).trans ?_
  have h := Polynomial.le_natDegree_of_mem_supp k hk
  simp only [degreeOf_X]
  split_ifs <;> omega
/-- A singleton sumcheck domain at the separating evaluation point. -/
def singletonDomain (a : E) : Fin 1 ↪ E := ⟨fun _ ↦ a, fun i j _ ↦ Subsingleton.elim i j⟩
/-- The singleton domain contains exactly its separating point. -/
theorem singletonDomain_set (a : E) : Finset.univ.map (singletonDomain a) = {a} := by
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, singletonDomain,
    Finset.mem_singleton]
  exact ⟨fun ⟨_, h⟩ ↦ h.symm, fun h ↦ ⟨0, h.symm⟩⟩
set_option maxHeartbeats 800000 in
/-- The sumcheck certificate bounds agreement of two fixed bounded round polynomials. -/
theorem sumcheck_polynomial_eval_eq_le (d : ℕ) (P Q : Polynomial E)
    (hne : P ≠ Q) (hP : P.natDegree ≤ d) (hQ : Q.natDegree ≤ d) :
    Pr{let r ← ($ᵗ E)}[P.eval r = Q.eval r] ≤ overE d := by
  classical
  by_cases hd : d < Fintype.card E
  · obtain ⟨a, ha⟩ : ∃ a : E, P.eval a ≠ Q.eval a := by
      by_contra! h
      exact hne (Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q Function.injective_id
        h ((max_le hP hQ).trans_lt hd))
    let D := singletonDomain a
    let ops := Sumcheck.plainOps (Finset.univ.map D) (fun p : ↥(Polynomial.degreeLE E (d : WithBot ℕ)) ↦ p.val.eval)
    let p : Sumcheck.Spec.OracleStatement E 1 d () := ⟨oneVariable Q, by
      rw [MvPolynomial.mem_restrictDegree_iff_degreeOf_le]
      exact fun j ↦ (oneVariable_degree Q j).trans hQ⟩
    let msg : ↥(Polynomial.degreeLE E (d : WithBot ℕ)) := ⟨P, Polynomial.mem_degreeLE.mpr (Polynomial.degree_le_of_natDegree_le hP)⟩
    let stmt : Sumcheck.Spec.StatementRound E 1 0 := ⟨P.eval a, Fin.elim0⟩
    have pass : ops.accept stmt.target msg = true := by
      change decide (∑ x ∈ Finset.univ.map (singletonDomain a), P.eval x = P.eval a) = true
      simp only [singletonDomain_set, Finset.sum_singleton, decide_true]
    have initial : ¬ closedRelation E 1 d D 0
        ⟨stmt, (polynomialFamily E 1 d).behaviorOfRealizations (fun _ ↦ p)⟩ := by
      intro h
      change (∑ x ∈ (Finset.univ.map (singletonDomain a)) ^ᶠ 1,
        MvPolynomial.eval (Fin.append stmt.challenges x ∘ Fin.cast (by decide)) (oneVariable Q)) = P.eval a at h
      rw [singletonDomain_set] at h
      simp only [Fintype.piFinset_singleton, Finset.sum_singleton, oneVariable_eval] at h
      exact ha h.symm
    have bound := Sumcheck.Interaction.Knowledge.local_badChallenge_le ops D
      (Sumcheck.identityModel (Finset.univ.map D)) (fun _ : Unit ↦ True) (fun _ ↦ p) p
      (fun _ _ ↦ rfl) 0 0 (by decide) stmt true msg
    have inclusion (r : E) (hr : P.eval r = Q.eval r) : RoundExtractor.badChallenge
        ((Sumcheck.Interaction.Knowledge.roundExtractor ops
          (Sumcheck.Interaction.Knowledge.claimPredicate D (fun _ : Unit ↦ True) (fun _ ↦ p))
          1 0 (by decide) stmt true msg).2.2) (some r) := by
      refine ⟨(), ?_, ?_⟩
      · exact fun h ↦ initial h.2.2
      · change (true && ops.accept stmt.target msg) = true ∧ True ∧ _
        refine ⟨by rw [pass]; rfl, trivial, ?_⟩
        apply (closedRelation_last_iff E 1 d D _).mpr
        change MvPolynomial.eval (Fin.snoc stmt.challenges r) (oneVariable Q) = P.eval r
        rw [oneVariable_eval]
        exact hr.symm
    simp only [Sumcheck.Interaction.Knowledge.nextChallenge, pass, ↓reduceIte, prEvent_map] at bound
    exact (prEvent_mono _ _ _ inclusion).trans bound
  · apply (prEvent_le_one _).trans
    unfold overE
    exact (ENNReal.le_div_iff_mul_le (by simp) (by simp)).mpr (by rw [one_mul]; exact_mod_cast Nat.le_of_not_gt hd)

end

end CompStark.Multilinear
