/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.Radius
public import CompPoly.Bivariate.GuruswamiSudan.Parameters

/-! Finite GS parameter selection succeeds at the production Johnson agreement cutoff. -/

@[expose] public section
namespace CompStark.Pcs
open CompPoly.GuruswamiSudan

/-- Twice the triangular monomial sum, expressed without natural subtraction. -/
theorem monomialPrefix_twice (d w q : ℕ) (hq : w * q ≤ d) :
    2 * ((List.range (q + 1)).map fun y => d - w * y + 1).sum + w * q * (q + 1) =
      2 * (q + 1) * (d + 1) := by
  induction q with
  | zero => simp only [Nat.zero_add, List.range_one, List.map_cons, Nat.mul_zero,
      Nat.sub_zero, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Nat.mul_one]
  | succ q ih =>
    have hprev : w * q ≤ d := by nlinarith
    have hsub : d - w * (q + 1) + w * (q + 1) = d := Nat.sub_add_cancel hq
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    have := ih hprev
    nlinarith

/-- The weighted triangular interpolation basis has at least its geometric area. -/
theorem interpolationMonomialCount_area (k s d : ℕ) (hk : 1 < k) :
    (d + 1) ^ 2 ≤ 2 * (k - 1) * interpolationMonomialCount ⟨k, s, d⟩ := by
  let w := k - 1
  have hw : 0 < w := by dsimp [w]; omega
  let q := d / w
  have hq : w * q ≤ d := Nat.mul_div_le d w
  have hr : d < w * (q + 1) := by
    have := Nat.mod_lt d hw
    have := Nat.mod_add_div d w
    dsimp [q]
    nlinarith
  have hsum := monomialPrefix_twice d w q hq
  change (d + 1) ^ 2 ≤ 2 * w * ((List.range (q + 1)).map fun y => d - w * y + 1).sum
  have hproduct : 0 ≤ (w * (q + 1) - (d + 1)) * (d + 1 - w * q) := Nat.zero_le _
  have hleft : w * (q + 1) - (d + 1) + (d + 1) = w * (q + 1) :=
    Nat.sub_add_cancel (by omega)
  have hright : d + 1 - w * q + w * q = d + 1 := Nat.sub_add_cancel (by omega)
  nlinarith

/-- The integer Johnson condition gives interpolation dimension slack at multiplicity m. -/
theorem parameterDimensionTest_johnson (k length cutoff m : ℕ) (hk : 1 < k)
    (hlen : 0 < length) (hm : 0 < m) (hcutoff : 0 < cutoff) (hcutoffle : cutoff ≤ length)
    (agreement : johnsonAgreement k length m cutoff) :
    parameterDimensionTest k length (length - cutoff) m = true := by
  have harea := interpolationMonomialCount_area k m (m * cutoff - 1) hk
  have hpositive : 0 < m * cutoff := Nat.mul_pos hm hcutoff
  have hdegree : m * cutoff - 1 + 1 = m * cutoff := Nat.sub_add_cancel (by omega)
  rw [hdegree] at harea
  have hw : 0 < k - 1 := by omega
  have constraints_twice (s : ℕ) : 2 * interpolationConstraintCount s = s * (s + 1) := by
    induction s with
    | zero => rfl
    | succ s ih => rw [interpolationConstraintCount_succ]; nlinarith
  have hconstraints := constraints_twice m
  have hn : length * interpolationConstraintCount m <
      interpolationMonomialCount ⟨k, m, m * cutoff - 1⟩ := by
    unfold johnsonAgreement at agreement
    have hgap : m * (m + 1) < (m + 1) ^ 2 := by nlinarith
    have hscaled := Nat.mul_lt_mul_of_pos_right hgap (Nat.mul_pos hw hlen)
    have hcountscaled := congrArg (fun x => (k - 1) * length * x) hconstraints
    have hstrict : 2 * (k - 1) * (length * interpolationConstraintCount m) <
        2 * (k - 1) * interpolationMonomialCount ⟨k, m, m * cutoff - 1⟩ := by
      calc
        _ = m * (m + 1) * ((k - 1) * length) := by nlinarith only [hcountscaled]
        _ < (m + 1) ^ 2 * ((k - 1) * length) := hscaled
        _ ≤ m ^ 2 * cutoff ^ 2 := by simpa only [Nat.mul_assoc] using agreement
        _ = (m * cutoff) ^ 2 := by ring
        _ ≤ _ := harea
    exact (Nat.mul_lt_mul_left (by omega : 0 < 2 * (k - 1))).mp hstrict
  unfold parameterDimensionTest agreementInterpParams
  rw [decide_eq_true_eq]
  simpa only [Nat.sub_sub_self hcutoffle] using hn

/-- Finite parameter selection succeeds under the integer Johnson contract. -/
theorem finiteGSParamSelector_isSome (k length cutoff m : ℕ) (hk : 1 < k)
    (hlen : 0 < length) (hm : 0 < m) (hmle : m ≤ length)
    (hcutoff : 0 < cutoff) (hcutoffle : cutoff ≤ length)
    (agreement : johnsonAgreement k length m cutoff) :
    (finiteGSParamSelector.choose k length (length - cutoff)).isSome := by
  change (if 1 < k ∧ length - cutoff < length then
    ((List.range length).find? fun i => parameterDimensionTest k length (length - cutoff) (i + 1)).map
      (fun i => ({ interp := agreementInterpParams k length (length - cutoff) (i + 1), radius := length - cutoff } : GSExecParams))
    else none).isSome
  rw [ite_eq_left (show 1 < k ∧ length - cutoff < length by omega), Option.isSome_map]
  apply List.find?_isSome.mpr
  refine ⟨m - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [Nat.sub_add_cancel hm]
  exact parameterDimensionTest_johnson k length cutoff m hk hlen hm hcutoff hcutoffle agreement

/-- Integer Johnson choices for each encoded level, without real-valued runtime fields. -/
def JohnsonParameters : {n : ℕ} → Whir.Schedule CompStark.BinaryFields.K n → Type
  | _, .last _ _ _ _ => ℕ
  | _, .more _ _ _ rest => ℕ × JohnsonParameters rest

/-- The reduced-rate Johnson slack `√ρ⁻ / m` attached to one discrete level. -/
noncomputable def johnsonSlack (vars rate m : ℕ) : ℝ :=
  Real.sqrt (((2 ^ vars - 1 : ℕ) : ℝ) / 2 ^ (vars + rate)) / m

/-- The Johnson slack is positive at a positive multiplicity and positive message dimension. -/
theorem johnsonSlack_pos {vars : ℕ} (rate : ℕ) {m : ℕ} (hv : 0 < vars) (hm : 0 < m) :
    0 < johnsonSlack vars rate m := by
  have hD : (0 : ℝ) < ((2 ^ vars - 1 : ℕ) : ℝ) := by
    have : 1 < 2 ^ vars := Nat.one_lt_two_pow (Nat.ne_of_gt hv)
    exact_mod_cast (by omega : 0 < 2 ^ vars - 1)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold johnsonSlack
  exact div_pos (Real.sqrt_pos.mpr (by positivity)) hmR

/-- Analytical level security computed from the discrete Johnson integer. -/
noncomputable def johnsonLevelSecurity (vars rate m : ℕ) : Whir.LevelSecurity :=
  ⟨johnsonSlack vars rate m⟩

/-- Analytical security parameters computed from each encoded level's integer choice. -/
noncomputable def johnsonSecurity : {n : ℕ} → (schedule : Whir.Schedule CompStark.BinaryFields.K n) →
    JohnsonParameters schedule → Whir.SecurityParameters schedule
  | _, .last _ tail enc _, m => johnsonLevelSecurity tail enc.rate m
  | _, .more (tail := tail) _ enc _ rest, ms =>
      (johnsonLevelSecurity tail enc.rate ms.1, johnsonSecurity rest ms.2)

end CompStark.Pcs
