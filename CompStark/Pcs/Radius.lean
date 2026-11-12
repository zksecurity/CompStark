/-
Copyright (c) 2026 zkSecurity.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Pcs.AdditiveEncoding
public import ArkLib.ProofSystem.Whir.Coding

/-! Exact integer agreement cutoffs for reduced-rate Johnson decoding. -/

@[expose] public section

namespace CompStark.Pcs

/-- Integer form of the reduced-rate Johnson agreement condition. -/
def johnsonAgreement (k length m agreement : ℕ) : Prop :=
  (m + 1) ^ 2 * (k - 1) * length ≤ m ^ 2 * agreement ^ 2

/-- The integer agreement condition has a constructive decision procedure. -/
instance (k length m agreement : ℕ) : Decidable (johnsonAgreement k length m agreement) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- Increasing the number of agreements preserves the integer Johnson condition. -/
theorem johnsonAgreement_mono (k length m : ℕ) : Monotone (johnsonAgreement k length m) := by
  intro a b hab ha
  exact ha.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab 2))

/-- Squaring the nonnegative real agreement bound gives exactly the integer test. -/
theorem johnsonAgreement_iff_real (k length m agreement : ℕ)
    (hm : 0 < m) (hlen : 0 < length) :
    johnsonAgreement k length m agreement ↔
      (1 + 1 / (m : ℝ)) * Real.sqrt (((k - 1 : ℕ) : ℝ) / length) * length ≤ agreement := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (0 : ℝ) < length := by exact_mod_cast hlen
  let r := Real.sqrt (((k - 1 : ℕ) : ℝ) / length)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = ((k - 1 : ℕ) : ℝ) / length := Real.sq_sqrt (by positivity)
  have hsquare : (((m : ℝ) + 1) * r * length) ^ 2 =
      ((m : ℝ) + 1) ^ 2 * ((k - 1 : ℕ) : ℝ) * length := by
    rw [mul_pow, mul_pow, hrsq]
    field_simp
  have htest : johnsonAgreement k length m agreement ↔
      ((m : ℝ) + 1) ^ 2 * ((k - 1 : ℕ) : ℝ) * length ≤
        (m : ℝ) ^ 2 * (agreement : ℝ) ^ 2 := by
    unfold johnsonAgreement
    exact_mod_cast Iff.rfl
  rw [htest, ← hsquare, ← mul_pow,
    sq_le_sq₀ (show 0 ≤ ((m : ℝ) + 1) * r * length by positivity)
      (show 0 ≤ (m : ℝ) * agreement by positivity)]
  have heq : 1 + 1 / (m : ℝ) = ((m : ℝ) + 1) / m := by field_simp
  rw [heq]
  change ((m : ℝ) + 1) * r * length ≤ (m : ℝ) * agreement ↔ _
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hmR, mul_comm (agreement : ℝ)]

/-- Binary search for the first agreement count satisfying the monotone condition. -/
def agreementSearch (k length m lo hi : ℕ) : ℕ :=
  if h : lo < hi then
    let mid := (lo + hi) / 2
    if johnsonAgreement k length m mid then agreementSearch k length m lo mid
    else agreementSearch k length m (mid + 1) hi
  else lo
termination_by hi - lo

/-- Binary search never returns below its lower endpoint. -/
theorem agreementSearch_ge (k length m lo hi : ℕ) : lo ≤ agreementSearch k length m lo hi := by
  rw [agreementSearch]
  dsimp only
  split_ifs with h hp
  · exact agreementSearch_ge k length m lo ((lo + hi) / 2)
  · exact (show lo ≤ (lo + hi) / 2 + 1 by omega).trans
      (agreementSearch_ge k length m ((lo + hi) / 2 + 1) hi)
  · rfl
termination_by hi - lo

/-- Binary search separates precisely the satisfying counts inside its interval. -/
theorem agreementSearch_spec (k length m lo hi : ℕ) (hle : lo ≤ hi)
    (hhi : johnsonAgreement k length m hi) (a : ℕ) (hlo : lo ≤ a) (ha : a ≤ hi) :
    agreementSearch k length m lo hi ≤ a ↔ johnsonAgreement k length m a := by
  rw [agreementSearch]
  dsimp only
  split_ifs with h hmid
  · by_cases hamid : a ≤ (lo + hi) / 2
    · exact agreementSearch_spec k length m lo ((lo + hi) / 2) (by omega)
        hmid a hlo hamid
    · have hs := (agreementSearch_spec k length m lo ((lo + hi) / 2) (by omega)
        hmid ((lo + hi) / 2) (by omega) (by omega)).mpr hmid
      exact iff_of_true (by omega) (johnsonAgreement_mono k length m (by omega) hmid)
  · by_cases hamid : (lo + hi) / 2 < a
    · exact agreementSearch_spec k length m ((lo + hi) / 2 + 1) hi (by omega)
        hhi a (by omega) ha
    · have hn : ¬ johnsonAgreement k length m a :=
        fun good => hmid (johnsonAgreement_mono k length m (by omega) good)
      have lower := agreementSearch_ge k length m ((lo + hi) / 2 + 1) hi
      exact iff_of_false (by omega) hn
  · have : lo = hi := by omega
    subst hi
    have : a = lo := by omega
    subst a
    exact iff_of_true (Nat.le_refl _) hhi
termination_by hi - lo

/-- The minimum certified number of simultaneous agreeing columns. -/
def agreementCutoff (k length m : ℕ) : ℕ := agreementSearch k length m 0 length

/-- The cutoff implements the exact squared comparison, including equality. -/
theorem agreementCutoff_le_iff (k length m : ℕ) (h : johnsonAgreement k length m length)
    (a : ℕ) (ha : a ≤ length) :
    agreementCutoff k length m ≤ a ↔ johnsonAgreement k length m a :=
  agreementSearch_spec k length m 0 length (Nat.zero_le _) h a (Nat.zero_le _) ha

/-- Exact initial production agreement cutoff. -/
theorem agreementCutoff_initial : agreementCutoff 8192 16384 3 = 15447 := by decide +kernel

/-- Exact middle production agreement cutoff. -/
theorem agreementCutoff_middle : agreementCutoff 512 8192 3 = 2728 := by decide +kernel

/-- Exact final production agreement cutoff. -/
theorem agreementCutoff_final : agreementCutoff 32 4096 3 = 476 := by decide +kernel

end CompStark.Pcs
