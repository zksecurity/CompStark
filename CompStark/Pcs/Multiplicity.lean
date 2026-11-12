/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Schedule
public import CompStark.Pcs.LevelBounds

/-! The production Johnson multiplicities. Each production level's integer `m` is the largest one
with every algebraic error at that level at most `2^-128` at every production configuration, up to
the cap `m ≤ 2^(vars + rate)`; levels off the production ladder use `m = 3`. -/

@[expose] public section

namespace CompStark.Pcs

/-- Multiplicities by inverse-rate exponent from `1`: the first tabulated encoded dimension and the
multiplicities of consecutive dimensions from there. -/
def multiplicityTable : List (ℕ × List ℕ) :=
  [(9, [1024, 1366, 1189, 1035, 901, 784, 683, 594, 517, 450, 392, 341, 297, 258]),
   (9, [1109, 965, 840, 732, 637, 554, 482, 420, 365, 318, 277, 241, 209, 182]),
   (9, [784, 682, 594, 517, 450, 392, 341, 297, 258, 224, 195, 170, 148, 129]),
   (5, [512, 837, 730, 636, 554, 482, 420, 365, 318, 277, 241, 209, 182, 158, 138, 120, 104, 91]),
   (5, [676, 591, 516, 449, 391, 341, 296, 258, 224, 195, 170, 148, 129, 112]),
   (5, [478, 418, 364, 318, 276, 241, 209, 182, 158, 138, 120, 104, 91, 79]),
   (2, [474, 432, 384, 338, 295, 257, 224, 195, 170, 148, 129, 112, 97, 84, 73, 64, 55]),
   (2, [335, 305, 271, 238, 208, 182, 158, 138, 120, 104, 91, 79, 68]),
   (2, [237, 216, 192, 168, 147, 128, 112, 97, 84, 73, 64, 55, 48]),
   (2, [167, 152, 135, 119, 104, 90, 79, 68, 59, 52, 45, 39, 34]),
   (2, [118, 107, 95, 84, 73, 64, 55, 48, 42]),
   (2, [83, 76, 67, 59, 51, 45, 39, 34, 29]),
   (2, [58, 53, 47, 41, 36, 31, 27, 24, 20]),
   (2, [41, 37, 33, 29, 25]),
   (2, [29, 26, 23, 20, 18]),
   (2, [20, 18, 16, 14, 12]),
   (2, [14]),
   (2, [10]),
   (2, [6])]

/-- The production multiplicity at an encoded dimension and inverse-rate exponent. -/
def productionMultiplicity (vars rate : ℕ) : ℕ :=
  match multiplicityTable[rate - 1]? with
  | some (first, ms) => if first ≤ vars then ms.getD (vars - first) 3 else 3
  | none => 3

/-- Natural-number form of the admissibility of a multiplicity at least three. -/
def Admissible (vars rate m : ℕ) : Prop :=
  3 ≤ m ∧ m ≤ 2 ^ (vars + rate) ∧ (m + 1) ^ 2 * (2 ^ vars - 1) < m ^ 2 * 2 ^ (vars + rate)

/-- Admissibility is decided by natural-number comparisons. -/
instance (vars rate m : ℕ) : Decidable (Admissible vars rate m) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Three is admissible at every positive-rate level with at least two variables. -/
theorem admissible_three (vars rate : ℕ) (hv : 2 ≤ vars) (hr : 0 < rate) : Admissible vars rate 3 := by
  have hpow : 4 ≤ 2 ^ vars := by
    simpa only [show (2 ^ 2 : ℕ) = 4 by decide] using Nat.pow_le_pow_right (n := 2) (by decide) hv
  have hrate : 2 * 2 ^ vars ≤ 2 ^ (vars + rate) := by
    rw [Nat.pow_add]
    have : 2 ≤ 2 ^ rate := by
      simpa only [Nat.pow_one] using Nat.pow_le_pow_right (by decide : 0 < 2) hr
    nlinarith
  refine ⟨le_rfl, ?_, ?_⟩ <;> omega

set_option maxRecDepth 8192 in
/-- Every tabulated multiplicity is admissible at its own level. -/
theorem multiplicityTable_admissible :
    ∀ i (hi : i < multiplicityTable.length) j (hj : j < (multiplicityTable[i]).2.length),
      Admissible ((multiplicityTable[i]).1 + j) (i + 1) (multiplicityTable[i]).2[j] := by
  decide +kernel

/-- Every production multiplicity is admissible. -/
theorem productionMultiplicity_admissible (vars rate : ℕ) (hv : 2 ≤ vars) (hr : 0 < rate) :
    Admissible vars rate (productionMultiplicity vars rate) := by
  unfold productionMultiplicity
  cases entry : multiplicityTable[rate - 1]? with
  | none => exact admissible_three vars rate hv hr
  | some row =>
    obtain ⟨first, ms⟩ := row
    obtain ⟨hi, hrow⟩ := List.getElem?_eq_some_iff.mp entry
    dsimp only
    split
    · rename_i hfirst
      by_cases hj : vars - first < ms.length
      · rw [List.getD_eq_getElem _ _ hj]
        have := multiplicityTable_admissible (rate - 1) hi (vars - first) (by rw [hrow]; exact hj)
        simp only [hrow] at this
        rwa [Nat.add_sub_cancel' hfirst, Nat.sub_add_cancel hr] at this
      · rw [List.getD_eq_default _ _ (by omega)]
        exact admissible_three vars rate hv hr
    · exact admissible_three vars rate hv hr

/-- The production Johnson choices: the tabulated multiplicity at every level. -/
def productionChoices : JohnsonChoices := fun vars rate hv hr =>
  let admissible := productionMultiplicity_admissible vars rate hv hr
  { m := productionMultiplicity vars rate
    positive_m := by have := admissible.1; omega
    bounded_m := admissible.2.1
    gap := johnsonSlack_lt _ rate (by have := admissible.1; omega) admissible.2.2 }

end CompStark.Pcs
