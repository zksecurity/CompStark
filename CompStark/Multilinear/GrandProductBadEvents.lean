/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Multilinear.GrandProductDecision
public import CompStark.Multilinear.Algebra.RootFamily

/-! Candidate-list events for normalized product-tree rounds and progressive riders. -/

@[expose] public section
namespace CompStark.Multilinear.GrandProduct
open CompStark.BinaryFields
open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp
open scoped ENNReal

/-- A fixed candidate repairs its normalized cofactor or progressive rider obligation at this draw. -/
def BadNormalizedCandidate {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (q : W) (r : E) : Prop :=
  ¬ roundRelation R μ m ρ leaves last point lam current χ active q ∧
    roundRelation R μ m ρ leaves last point lam
      (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r) (χ ++ [r])
      (active && check (2 ^ ρ) (point.getD χ.length 0) current message) q

/-- The fixed candidate event is decided using finite rider grids. -/
instance {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (q : W) (r : E) :
    Decidable (BadNormalizedCandidate R μ m ρ leaves last point χ lam current active message q r) := by
  unfold BadNormalizedCandidate
  infer_instance

/-- Each candidate has the existing cofactor-degree bound, including its rider escape. -/
theorem prob_badNormalizedCandidate_le {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (q : W)
    (radix : ρ = 1 ∨ ρ = 2) (point_length : point.length = m) (prefix_length : χ.length < m) :
    Pr{let r ←$ᵗ E}[BadNormalizedCandidate R μ m ρ leaves last point χ lam current active message q r] ≤
      overE (2 ^ ρ) := by
  let n := m - χ.length - 1
  have length : χ.length + (n + 1) = m := by omega
  have bound := normalized_round_badChallenge_le R q μ m ρ n leaves last point χ
    lam current active message .done (fun _ _ => fun _ => True) radix point_length length
  simp only [roundSample, check_eq_true, ↓reduceIte, prEvent_map] at bound
  refine (prEvent_mono ($ᵗ E) _ _ ?_).trans bound
  intro r bad
  change ∃ witness, ¬ (witness = q ∧ roundRelation R μ m ρ leaves last point lam current χ active witness) ∧
    witness = q ∧ Retained.input (roundsLabels R μ m ρ leaves last point lam .done
      (fun _ _ => fun _ => True) n (χ ++ [r])
      (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r)
      (active && check (2 ^ ρ) (point.getD χ.length 0) current message)) witness
  exact ⟨q, (fun good => bad.1 good.2), rfl,
    (congrFun (roundsLabels_input R μ m ρ leaves last point lam .done (fun _ _ => fun _ => True)
      n _ _ _) q).mpr bad.2⟩

/-- Bad normalized rounds are the union over the prefix-fixed decoded candidate list. -/
def BadNormalizedRound {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (candidates : List (W))
    (r : E) : Prop :=
  ∃ q ∈ candidates, BadNormalizedCandidate R μ m ρ leaves last point χ lam current active message q r

/-- The normalized checker enumerates candidates and each candidate's finite rider grid. -/
def checkBadNormalizedRound {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (candidates : List (W))
    (r : E) : Bool :=
  candidates.any fun q => decide (BadNormalizedCandidate R μ m ρ leaves last point χ lam current active message q r)

/-- The finite normalized checker decides exactly the candidate-list event. -/
theorem checkBadNormalizedRound_iff {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ)) (candidates : List (W)) (r : E) :
    checkBadNormalizedRound R μ m ρ leaves last point χ lam current active message candidates r = true ↔
      BadNormalizedRound R μ m ρ leaves last point χ lam current active message candidates r := by
  simp only [checkBadNormalizedRound, List.any_eq_true, decide_eq_true_eq, BadNormalizedRound]

/-- Revealing consistent columns preserves candidate-list normalized badness. -/
theorem BadNormalizedRound.mono {W : Type} {R : Riders W} {μ m ρ : ℕ}
    {leaves : W → Fin 3 → ℕ → E} {last : Bool} {point χ : List E}
    {lam current : E} {active : Bool} {message : Message (2 ^ ρ)}
    {small large : List (W)} (subset : small ⊆ large) {r : E}
    (bad : BadNormalizedRound R μ m ρ leaves last point χ lam current active message small r) :
    BadNormalizedRound R μ m ρ leaves last point χ lam current active message large r := by
  obtain ⟨q, member, bad⟩ := bad
  exact ⟨q, subset member, bad⟩

/-- Zero-fill candidate inclusion preserves the original list-times-cofactor-degree error. -/
theorem prob_badNormalizedRound_le {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (point χ : List E)
    (lam current : E) (active : Bool) (message : Message (2 ^ ρ))
    (masked completed : List (W)) (subset : masked ⊆ completed)
    (radix : ρ = 1 ∨ ρ = 2) (point_length : point.length = m) (prefix_length : χ.length < m) :
    Pr{let r ←$ᵗ E}[BadNormalizedRound R μ m ρ leaves last point χ lam current active message masked r] ≤
      (completed.length : ENNReal) * overE (2 ^ ρ) := by
  refine (prEvent_mono ($ᵗ E) _ _ (fun _ bad => bad.mono subset)).trans ?_
  clear subset masked
  change Pr{let r ←$ᵗ E}[∃ q ∈ completed,
    BadNormalizedCandidate R μ m ρ leaves last point χ lam current active message q r] ≤ _
  induction completed with
  | nil => simp only [List.not_mem_nil, false_and, exists_false,
      prEvent_false, List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons q rest ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        using add_le_add (prob_badNormalizedCandidate_le R μ m ρ leaves last point χ lam current active
          message q radix point_length prefix_length) ih

/-- The authored normalized escape belongs to the event for every candidate list retaining its witness. -/
theorem normalized_escape_subset_badNormalizedRound {W : Type} (R : Riders W) [DecidablePred R.Fits] (q : W)
    (μ m ρ n : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (point χ : List E) (lam current : E) (active : Bool) (message : Message (2 ^ ρ))
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (candidates : List (W)) (member : q ∈ candidates) (r : E)
    (escape : RoundExtractor.badChallenge
      ((Retained.extractor q (roundsLabels R μ m ρ leaves last point lam tail out
        (n + 1) χ current active) message).2.2) (some r)) :
    BadNormalizedRound R μ m ρ leaves last point χ lam current active message candidates r := by
  change ∃ witness, ¬ (witness = q ∧ roundRelation R μ m ρ leaves last point lam current χ active witness) ∧
    witness = q ∧ Retained.input (roundsLabels R μ m ρ leaves last point lam tail out n (χ ++ [r])
      (evaluate (2 ^ ρ) (point.getD χ.length 0) current message r)
      (active && check (2 ^ ρ) (point.getD χ.length 0) current message)) witness at escape
  obtain ⟨witness, bad, same, good⟩ := escape
  subst witness
  exact ⟨q, member, (fun known => bad ⟨rfl, known⟩),
    (congrFun (roundsLabels_input R μ m ρ leaves last point lam tail out n _ _ _) q).mp good⟩

/-- A child-coordinate draw repairs one fixed candidate's child values or progressive riders. -/
def BadInterpolationCandidate {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (q : W) (r : E) : Prop :=
  ¬ interpolationRelation R μ m ρ leaves last χ u children active q ∧
    interpolationRelation R μ m ρ leaves last χ (u ++ [r]) children active q

/-- The child-coordinate candidate event uses finite interpolation and rider-grid decisions. -/
instance {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (q : W) (r : E) :
    Decidable (BadInterpolationCandidate R μ m ρ leaves last χ u children active q r) := by
  unfold BadInterpolationCandidate
  infer_instance

/-- Every fixed interpolation candidate retains the existing one-root bound. -/
theorem prob_badInterpolationCandidate_le {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (q : W)
    (sum_length : χ.length = m) (child_length : u.length < ρ)
    (cover : last = true → R.maxHeight ≤ m + ρ) :
    Pr{let r ←$ᵗ E}[BadInterpolationCandidate R μ m ρ leaves last χ u children active q r] ≤ overE 1 := by
  let n := ρ - u.length - 1
  have length : u.length + (n + 1) = ρ := by omega
  let out : Claim → Bool → Retained.Labels (W) Protocol.done.tree := fun c good q =>
    good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
      (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
        else RidersZero R q)
  have endpoint : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q) := fun _ _ _ => Iff.rfl
  have bound := interpolation_badChallenge_le R q μ m ρ n leaves last χ u children active
    .done out sum_length length cover endpoint
  refine (prEvent_mono ($ᵗ E) _ _ ?_).trans bound
  intro r bad
  change ∃ witness, ¬ (witness = q ∧ interpolationRelation R μ m ρ leaves last χ u children active witness) ∧
    witness = q ∧ Retained.input
      (interpolationLabels R μ m ρ leaves last χ children active .done out n (u ++ [r])) witness
  refine ⟨q, (fun good => bad.1 good.2), rfl, ?_⟩
  exact (interpolationLabels_input R μ m ρ leaves last χ (u ++ [r]) children active .done out
    sum_length n (by simp only [List.length_append, List.length_singleton]; omega) cover endpoint q).mpr bad.2

/-- The masked child-coordinate event ranges over the prefix-fixed decoded candidate list. -/
def BadInterpolation {W : Type} (R : Riders W) (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (candidates : List (W)) (r : E) : Prop :=
  ∃ q ∈ candidates, BadInterpolationCandidate R μ m ρ leaves last χ u children active q r

/-- Child interpolation badness has an executable candidate-list checker. -/
def checkBadInterpolation {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (candidates : List (W)) (r : E) : Bool :=
  candidates.any fun q => decide (BadInterpolationCandidate R μ m ρ leaves last χ u children active q r)

/-- The child-coordinate checker decides exactly the fixed-list event. -/
theorem checkBadInterpolation_iff {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool) (candidates : List (W)) (r : E) :
    checkBadInterpolation R μ m ρ leaves last χ u children active candidates r = true ↔
      BadInterpolation R μ m ρ leaves last χ u children active candidates r := by
  simp only [checkBadInterpolation, List.any_eq_true, decide_eq_true_eq, BadInterpolation]

/-- Revealing consistently masked columns preserves a child-coordinate witness. -/
theorem BadInterpolation.mono {W : Type} {R : Riders W} {μ m ρ : ℕ}
    {leaves : W → Fin 3 → ℕ → E} {last : Bool} {χ u : List E}
    {children : Fin 3 → Fin (2 ^ ρ) → E} {active : Bool}
    {small large : List (W)} (subset : small ⊆ large) {r : E}
    (bad : BadInterpolation R μ m ρ leaves last χ u children active small r) :
    BadInterpolation R μ m ρ leaves last χ u children active large r := by
  obtain ⟨q, member, bad⟩ := bad
  exact ⟨q, subset member, bad⟩

/-- Zero fill bounds the masked interpolation list with the original one-root cost. -/
theorem prob_badInterpolation_le {W : Type} (R : Riders W) [DecidablePred R.Fits] (μ m ρ : ℕ)
    (leaves : W → Fin 3 → ℕ → E) (last : Bool) (χ u : List E)
    (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (masked completed : List (W)) (subset : masked ⊆ completed)
    (sum_length : χ.length = m) (child_length : u.length < ρ)
    (cover : last = true → R.maxHeight ≤ m + ρ) :
    Pr{let r ←$ᵗ E}[BadInterpolation R μ m ρ leaves last χ u children active masked r] ≤
      (completed.length : ENNReal) * overE 1 := by
  refine (prEvent_mono _ _ _ (fun _ bad => bad.mono subset)).trans ?_
  clear masked subset
  change Pr{let r ←$ᵗ E}[∃ q ∈ completed, BadInterpolationCandidate R μ m ρ leaves last χ u children active q r] ≤ _
  induction completed with
  | nil => simp only [List.not_mem_nil, false_and, exists_false, prEvent_false,
      List.length_nil, Nat.cast_zero, zero_mul, le_refl]
  | cons q rest ih =>
      simp only [List.mem_cons, exists_eq_or_imp]
      refine (prEvent_or_le _ _ _).trans ?_
      simpa only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
        using add_le_add (prob_badInterpolationCandidate_le R μ m ρ leaves last χ u children active q
          sum_length child_length cover) ih

/-- Authored interpolation escapes use the same fixed candidate, including their endpoint boundary. -/
theorem interpolation_escape_subset_badInterpolation {W : Type} (R : Riders W) [DecidablePred R.Fits] (q : W)
    (μ m ρ n : ℕ) (leaves : W → Fin 3 → ℕ → E) (last : Bool)
    (χ u : List E) (children : Fin 3 → Fin (2 ^ ρ) → E) (active : Bool)
    (tail : Protocol) (out : Claim → Bool → Retained.Labels (W) tail.tree)
    (sum_length : χ.length = m) (child_length : u.length + (n + 1) = ρ)
    (cover : last = true → R.maxHeight ≤ m + ρ)
    (endpoint : ∀ c good q, Retained.input (out c good) q ↔
      good = true ∧ R.Fits q ∧ c.Holds μ (m + ρ) (leaves q) ∧
        (if last then ∀ i, rider R q i (c.point.take (R.height i)) = 0
          else RidersZero R q))
    (candidates : List (W)) (member : q ∈ candidates) (r : E)
    (escape : RoundExtractor.badChallenge (Retained.extractor q
      (interpolationLabels R μ m ρ leaves last χ children active tail out (n + 1) u)) r) :
    BadInterpolation R μ m ρ leaves last χ u children active candidates r := by
  change ∃ witness, ¬ (witness = q ∧ interpolationRelation R μ m ρ leaves last χ u children active witness) ∧
    witness = q ∧ Retained.input
      (interpolationLabels R μ m ρ leaves last χ children active tail out n (u ++ [r])) witness at escape
  obtain ⟨witness, bad, same, good⟩ := escape
  subst witness
  refine ⟨q, member, (fun known => bad ⟨rfl, known⟩), ?_⟩
  exact (interpolationLabels_input R μ m ρ leaves last χ (u ++ [r]) children active tail out sum_length n
    (by simp only [List.length_append, List.length_singleton]; omega) cover endpoint q).mp good

end CompStark.Multilinear.GrandProduct
