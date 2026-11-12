/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Levels

/-! The encoded levels of every production schedule and their kernel-checked error levels: every
algebraic WHIR row is at most `2^-128` and every column-query row at most `2^-111`. -/

@[expose] public section

namespace CompStark.Pcs

/-- The encoded levels of a certified schedule. -/
def certifiedLevels {vars rate : ℕ} (schedule : CertifiedSchedule vars rate) : List Level :=
  scheduleLevels schedule.schedule schedule.johnson

/-- Transporting a certified dimension preserves its levels. -/
@[simp] theorem certifiedLevels_cast {a b rate : ℕ} (h : a = b) (schedule : CertifiedSchedule a rate) :
    certifiedLevels (h ▸ schedule) = certifiedLevels schedule := by
  subst b
  rfl

/-- One ladder level records its fold, dimension, rate, queries and chosen multiplicity before
the recursive tail. -/
theorem ladder_levels (choices : JohnsonChoices) (queries : ℕ → ℕ)
    (vars fold rate : ℕ) (hvars : fold + 2 ≤ vars) (hfold : 0 < fold)
    (hrate : 0 < rate) (hdim : vars - fold + rate ≤ 63) :
    certifiedLevels (ladder choices queries vars fold rate hvars hfold hrate hdim) =
      if last : vars - fold ≤ 5 then
        [⟨fold, vars - fold, rate, queries rate, (choices (vars - fold) rate (by omega) hrate).m⟩]
      else ⟨fold, vars - fold, rate, queries rate, (choices (vars - fold) rate (by omega) hrate).m⟩ ::
        certifiedLevels (ladder choices queries (vars - fold) 4 (rate + 3)
          (by omega) (by decide) (by omega) (by omega)) := by
  rw [ladder]
  split <;> simp only [certifiedLevels_cast] <;> rfl

/-- Production levels from a query ladder: `fuel` bounds the number of levels. -/
def ladderLevels (queries : List ℕ) : (fuel vars fold rate level : ℕ) → List Level
  | 0, _, _, _, _ => []
  | fuel + 1, vars, fold, rate, level =>
    let head : Level := ⟨fold, vars - fold, rate, queries.getD level 0,
      productionMultiplicity (vars - fold) rate⟩
    if vars - fold ≤ 5 then [head]
    else head :: ladderLevels queries fuel (vars - fold) 4 (rate + 3) (level + 1)

/-- The levels of the production schedule at initial inverse-rate exponent `r + 1` and stacked
dimension `n + 15`. -/
def productionLevels (r : Fin 4) (n : Fin 14) : List Level :=
  ladderLevels (productionQueries r n) 8 (n.val + 15) 6 (r.val + 1) 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
/-- The production schedule's levels are the tabulated production levels. -/
theorem productionSchedule_levels (vars rate : ℕ)
    (hvars : 15 ≤ vars ∧ vars ≤ 28) (hrate : 1 ≤ rate ∧ rate ≤ 4) :
    certifiedLevels (productionSchedule productionChoices vars rate hvars hrate) =
      productionLevels ⟨rate - 1, by omega⟩ ⟨vars - 15, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n : Fin 14, vars = n.val + 15 :=
    ⟨⟨vars - 15, by omega⟩, by change vars = (vars - 15) + 15; omega⟩
  obtain ⟨r, rfl⟩ : ∃ r : Fin 4, rate = r.val + 1 :=
    ⟨⟨rate - 1, by omega⟩, by change rate = (rate - 1) + 1; omega⟩
  unfold productionSchedule
  fin_cases n <;> fin_cases r <;>
    simp only [ladder_levels, Nat.reduceSub, Nat.reduceAdd, Nat.reduceLeDiff, ↓reduceDIte] <;>
    rfl

/-- The certified level of every algebraic error row. -/
def algebraicLevel : ℕ := 128

/-- The certified level of every column-query row. -/
def queryLevel : ℕ := 111

set_option maxRecDepth 16384 in
/-- Every production configuration passes the level check with leanMultisig's 142 initial claims,
and its first level bounds outer rows of numerator up to `2^42`. -/
theorem productionLevels_check : ∀ r : Fin 4, ∀ n : Fin 14,
    levelsCheck algebraicLevel queryLevel (productionLevels r n) 142 = true ∧
      (productionLevels r n).head!.admissibleCheck = true ∧
      (productionLevels r n).head!.outerCheck algebraicLevel (2 ^ 42) = true := by
  decide +kernel

end CompStark.Pcs
