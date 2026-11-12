/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.BadEvents

/-! Executable root events for simultaneous polynomial obligations on one candidate. -/

@[expose] public section
namespace CompStark.Multilinear
open OracleComp Sumcheck.Interaction.Knowledge
open scoped ENNReal

/-- A nonzero family of degree-bounded discrepancies simultaneously vanishes at the challenge. -/
def BadRootFamily {F : Type} [Semiring F] {degree : ℕ}
    (equations : List (Coefficients F degree)) (r : F) : Prop :=
  (∃ polynomial ∈ equations, polynomial ≠ 0) ∧
    ∀ polynomial ∈ equations, evalCoefficients polynomial r = 0

/-- Simultaneous root badness is decidable from the bounded coefficient vectors. -/
instance {F : Type} [Semiring F] [DecidableEq F] {degree : ℕ}
    (equations : List (Coefficients F degree)) (r : F) : Decidable (BadRootFamily equations r) := by
  unfold BadRootFamily
  infer_instance

/-- One nonzero family costs one degree bound, regardless of its number of simultaneous obligations. -/
theorem prob_badRootFamily_le {F : Type} [Field F] [Fintype F] [SampleableType F] {degree : ℕ}
    (equations : List (Coefficients F degree)) :
    Pr{let r ←$ᵗ F}[BadRootFamily equations r] ≤ (degree : ENNReal) / Fintype.card F := by
  classical
  by_cases nonzero : ∃ polynomial ∈ equations, polynomial ≠ 0
  · obtain ⟨polynomial, member, different⟩ := nonzero
    refine (prEvent_mono ($ᵗ F) _ (BadSummand [polynomial] 0) ?_).trans
      (prob_badSummand_singleton_le polynomial 0)
    intro r bad
    refine ⟨polynomial, List.mem_singleton_self _, Ne.symm different, ?_⟩
    simp only [evalCoefficients, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
    exact (bad.2 polynomial member).symm
  · exact (prEvent_eq_zero_of_forall_not ($ᵗ F) _ (fun _ bad => nonzero bad.1)).le.trans zero_le

/-- A decoded candidate contributes its fixed simultaneous discrepancy family. -/
def BadRootCandidates {F : Type} [Semiring F] {degree : ℕ}
    (candidates : List (List (Coefficients F degree))) (r : F) : Prop :=
  ∃ equations ∈ candidates, BadRootFamily equations r

/-- The root-family checker enumerates only the prefix-fixed candidate list. -/
def checkBadRootCandidates {F : Type} [Semiring F] [DecidableEq F] {degree : ℕ}
    (candidates : List (List (Coefficients F degree))) (r : F) : Bool :=
  candidates.any fun equations => decide (BadRootFamily equations r)

/-- The executable family checker is exact. -/
theorem checkBadRootCandidates_iff {F : Type} [Semiring F] [DecidableEq F] {degree : ℕ}
    (candidates : List (List (Coefficients F degree))) (r : F) :
    checkBadRootCandidates candidates r = true ↔ BadRootCandidates candidates r := by
  simp only [checkBadRootCandidates, List.any_eq_true, decide_eq_true_eq, BadRootCandidates]

/-- Revealing consistently masked columns preserves badness through candidate inclusion. -/
theorem BadRootCandidates.mono {F : Type} [Semiring F] {degree : ℕ}
    {small large : List (List (Coefficients F degree))} (subset : small ⊆ large) {r : F}
    (bad : BadRootCandidates small r) : BadRootCandidates large r := by
  obtain ⟨equations, member, bad⟩ := bad
  exact ⟨equations, subset member, bad⟩

/-- Zero-fill inclusion bounds masked candidates with the full-word degree and list bound. -/
theorem prob_badRootCandidates_le {F : Type} [Field F] [Fintype F] [SampleableType F] {degree : ℕ}
    (masked completed : List (List (Coefficients F degree))) (subset : masked ⊆ completed) :
    Pr{let r ←$ᵗ F}[BadRootCandidates masked r] ≤
      (completed.length : ENNReal) * ((degree : ENNReal) / Fintype.card F) := by
  classical
  refine (prEvent_mono ($ᵗ F) _ _ (fun _ bad => BadRootCandidates.mono subset bad)).trans ?_
  clear subset masked
  induction completed with
  | nil =>
      simp only [BadRootCandidates, List.not_mem_nil, false_and, exists_false, prEvent_false,
        List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons equations rest ih =>
      simp only [BadRootCandidates, List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      simpa only [BadRootCandidates, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        using add_le_add (prob_badRootFamily_le equations) ih

end CompStark.Multilinear
