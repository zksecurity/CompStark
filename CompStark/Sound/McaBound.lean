/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.CurveUniqueAgreement
public import ArkLib.Data.CodingTheory.ProximityGenerator.PolynomialGenerator
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.CurveProbability

/-! # Bounds on mutual correlated agreement for Reed–Solomon codes and power curves

A `McaBound` is a computable bound on the mutual correlated-agreement error of the powers generator
`z ↦ (1, z, …, z^M)` for Reed–Solomon codes: `admits N k δ` says that it covers the code of degree
below `k` on `N` points at radius `δ`, and `count N k M δ` bounds the exceptional seeds there for
curves of degree `M`. `McaBound.Holds B` asks that the counts are exception counts over every
finite field `K` and on every evaluation domain: the MCA error is at most `count / |K|`. The
security calculator (`CompStark/SecurityCalculator.lean`) is parametric in the bound, and the
soundness theorems built on it take `Holds` as their hypothesis.

* `uniqueDecoding`: within the unique-decoding radius, `2 ⌊δ N⌋ ≤ N - k`, at most `M N` exceptional
  seeds (`uniqueDecoding_holds`, from ArkLib's exact power agreement for curves below the
  unique-decoding radius, [BCIKS20] Theorem 6.1, at the radius `⌊δ N⌋ / N`, which has the same MCA
  events).
* `johnson`: up to the Johnson radius `1 - √ρ₋`, `ρ₋ = (k - 1) / N`, `M` times [DKT26] Theorem
  5.12's exception count for lines, `johnsonLineCount`, ArkLib's `johnsonExceptionCount` in `Nat`
  and `ℚ` arithmetic, at the agreement threshold `⌈(1 - δ) N⌉` and the multiplicity
  `m = max(⌈r / (2 (1 - δ - r))⌉, 3)`, `r ≥ √ρ₋` dyadic (`johnson_holds`, from ArkLib's
  Johnson-regime MCA for power curves at the slack `η = √ρ₋ / (2m)`, whose multiplicity is `m`).
  The kernel evaluates it: `⌈√x⌉` is `ceilSqrt`, through `Nat.sqrt`.
* `min`: the smaller count where both bounds apply (`min_holds`); `uniqueOrJohnson` combines the
  two above.
-/

@[expose] public section
namespace CompStark.Sound
open NNReal CoreDefinitions LinearCode Code

/-- A computable bound on the MCA error of power curves for Reed–Solomon codes: where
`admits N k δ`, at most `count N k M δ` exceptional seeds for curves of degree `M` over the code
of degree below `k` on `N` points at radius `δ`. -/
structure McaBound where
  admits : ℕ → ℕ → ℚ → Bool
  count : ℕ → ℕ → ℕ → ℚ → ℚ
  count_nonneg : ∀ N k M δ, 0 ≤ count N k M δ
  /-- The count grows with the curve's degree. -/
  count_mono : ∀ N k δ, Monotone fun M ↦ count N k M δ

namespace McaBound

/-- The bound holds: over every finite field `K` and on every domain of `N` points it admits, the
MCA error of the powers `1, z, …, z^M` for the code of degree below `k` at radius `δ` is at most
`count N k M δ / |K|`. -/
def Holds (B : McaBound) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] [SampleableType K] (N k M : ℕ)
    (domain : Fin N ↪ K) (δ : ℚ), B.admits N k δ →
    mcaError (univariatePowersGenerator K M) (ReedSolomon.code domain k) (δ : ℝ) ≤
      ENNReal.ofReal (B.count N k M δ / Fintype.card K)

/-- Within the unique-decoding radius, `2 ⌊δ N⌋ ≤ N - k`: at most `M N` exceptional seeds. -/
def uniqueDecoding : McaBound where
  admits N k δ := decide (0 < k ∧ k ≤ N ∧ 0 ≤ δ ∧ 2 * ⌊δ * N⌋₊ ≤ N - k)
  count N _ M _ := M * N
  count_nonneg _ _ _ _ := by positivity
  count_mono _ _ _ _ _ h := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (Nat.cast_nonneg _)

/-- The smaller of the counts of `B` and `B'` where both apply. -/
def min (B B' : McaBound) : McaBound where
  admits N k δ := B.admits N k δ || B'.admits N k δ
  count N k M δ :=
    if B.admits N k δ then
      if B'.admits N k δ then Min.min (B.count N k M δ) (B'.count N k M δ) else B.count N k M δ
    else B'.count N k M δ
  count_nonneg N k M δ := by
    have := B.count_nonneg N k M δ
    have := B'.count_nonneg N k M δ
    split_ifs <;> first | assumption | exact le_min ‹_› ‹_›
  count_mono N k δ a b h := by
    have := B.count_mono N k δ h
    have := B'.count_mono N k δ h
    dsimp only at *
    split_ifs <;> first | assumption | exact min_le_min ‹_› ‹_›

/-- A dyadic upper bound `r ≥ √ρ`, `r ≤ √ρ + 2 ^ (-20)`. -/
def sqrtUpper (ρ : ℚ) : ℚ := ((⌊ρ * 2 ^ 40⌋₊.sqrt + 1 : ℕ) : ℚ) / 2 ^ 20

/-- `⌈√x⌉` for a rational `x`: `0` for `⌈x⌉ = 0`, else `⌊√(⌈x⌉ - 1)⌋ + 1`, the least `c` with
`x ≤ c²` (`ceilSqrt_le_iff`). -/
def ceilSqrt (x : ℚ) : ℕ := if ⌈x⌉₊ = 0 then 0 else (⌈x⌉₊ - 1).sqrt + 1

/-- [DKT26]'s exception count for lines, as ArkLib's `johnsonExceptionCount` computes it, for the
code of degree at most `D` on `n` points, agreement threshold `A` and multiplicity `m`:
`(2μ - 1) h + θ (h + μ + 4 D μ h) + (n - D - 1) μ` with `t = m + 1/2`, `ρ₋ = D / n`,
`μ = ⌈t / √ρ₋⌉ - 1`, `h = ⌈t² / (3 ρ₋)⌉ - 1` and `θ = (n - D) / (A - D)`. -/
def johnsonLineCount (n D A m : ℕ) : ℚ :=
  let ρ : ℚ := (D : ℚ) / n
  let t : ℚ := m + 1 / 2
  let μ : ℕ := ceilSqrt (t ^ 2 / ρ) - 1
  let h : ℕ := ⌈t ^ 2 / (3 * ρ)⌉₊ - 1
  ((2 * μ - 1 : ℕ) : ℚ) * h + ((n - D : ℕ) : ℚ) / (A - D : ℕ) * (h + μ + 4 * D * μ * h) +
    ((n - D - 1 : ℕ) : ℚ) * μ

/-- The Johnson multiplicity at radius `δ` for `ρ₋`: `max(⌈r / (2 (1 - δ - r))⌉, 3)` with
`r = sqrtUpper ρ₋ ≥ √ρ₋`. -/
def johnsonMult (ρ δ : ℚ) : ℕ :=
  Max.max ⌈sqrtUpper ρ / (2 * (1 - δ - sqrtUpper ρ))⌉₊ 3

/-- The Johnson regime: for `2 ≤ k < N` and `δ < 1 - r`, `r = sqrtUpper ρ₋ ≥ √ρ₋`,
`ρ₋ = (k - 1) / N`, the count `M · johnsonLineCount N (k - 1) ⌈(1 - δ) N⌉ m` at the multiplicity
`m = johnsonMult ρ₋ δ`: [DKT26] Theorem 5.12's exception count for lines, times the curve degree
`M`. -/
def johnson : McaBound where
  admits N k δ := decide (2 ≤ k ∧ k < N ∧ 0 ≤ δ ∧ sqrtUpper ((k - 1 : ℕ) / N) < 1 - δ)
  count N k M δ :=
    M * johnsonLineCount N (k - 1) ⌈N * (1 - δ)⌉₊ (johnsonMult ((k - 1 : ℕ) / N) δ)
  count_nonneg N k M δ := by
    unfold johnsonLineCount
    positivity
  count_mono N k δ a b h :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr h) (by unfold johnsonLineCount; positivity)

/-- Up to the Johnson radius: `johnson`'s count, the smaller of the two counts within the
unique-decoding radius, and `uniqueDecoding`'s alone for the constant code (`k = 1`), which
`johnson` does not admit. -/
def uniqueOrJohnson : McaBound := uniqueDecoding.min johnson

variable {K : Type} [Field K] [Fintype K] [SampleableType K]

/-- The MCA error grows with the radius, through the agreement sets it admits: if every
agreement-set size admitted at `δ` is admitted at `δ'`, the error at `δ` is at most the error at
`δ'`. -/
theorem mcaError_le_of_card {N M k : ℕ} (domain : Fin N ↪ K) (δ δ' : ℝ)
    (h : ∀ t : ℕ, t ≤ N → (t : ℝ) ≥ N * (1 - δ) → (t : ℝ) ≥ N * (1 - δ')) :
    mcaError (univariatePowersGenerator K M) (ReedSolomon.code domain k) δ ≤
      mcaError (univariatePowersGenerator K M) (ReedSolomon.code domain k) δ' := by
  refine iSup_mono fun U ↦ prEvent_mono _ _ _ fun z hz ↦ ?_
  obtain ⟨T, hT, hv, hj⟩ := hz
  refine ⟨T, ?_, hv, hj⟩
  have hTN := Finset.card_le_univ T
  rw [Fintype.card_fin] at hTN hT ⊢
  exact h T.card hTN hT

/-- The bound within the unique-decoding radius holds. -/
theorem uniqueDecoding_holds : uniqueDecoding.Holds := by
  intro K _ _ _ _ N k M domain δ h
  simp only [uniqueDecoding, decide_eq_true_eq] at h
  obtain ⟨hk, hkN, hδ0, hfl⟩ := h
  have hN : 0 < N := hk.trans_le hkN
  have : NeZero N := ⟨hN.ne'⟩
  have : NeZero k := ⟨hk.ne'⟩
  set e := ⌊δ * N⌋₊
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  -- The radius `⌊δ N⌋ / N` admits the same agreement sets.
  have heR : (e : ℝ) ≤ δ * N := by
    have := Nat.floor_le (mul_nonneg hδ0 (Nat.cast_nonneg N))
    exact_mod_cast this
  have hmono : mcaError (univariatePowersGenerator K M) (ReedSolomon.code domain k) (δ : ℝ) ≤
      mcaError (univariatePowersGenerator K M) (ReedSolomon.code domain k)
        ((((e : ℝ≥0) / N : ℝ≥0)) : ℝ) := by
    refine mcaError_le_of_card domain _ _ fun t ht hT ↦ ?_
    have hle : N - t ≤ e := by
      refine Nat.le_floor ?_
      have : ((N - t : ℕ) : ℝ) ≤ (δ : ℝ) * N := by
        rw [Nat.cast_sub ht]
        nlinarith
      exact_mod_cast this
    have hcast : ((((e : ℝ≥0) / N : ℝ≥0)) : ℝ) = e / N := by push_cast; rfl
    rw [hcast, mul_sub, mul_one, mul_div_cancel₀ _ hNR.ne', ge_iff_le, sub_le_iff_le_add]
    have : (N : ℝ) ≤ t + (N - t : ℕ) := by rw [Nat.cast_sub ht]; linarith
    have : ((N - t : ℕ) : ℝ) ≤ e := by exact_mod_cast hle
    linarith
  have hδ' : (e : ℝ≥0) / N ≤
      relativeUniqueDecodingRadius (ReedSolomon.code domain k : Set (Fin N → K)) := by
    rw [relativeUniqueDecodingRadius, dist_eq_minDist,
      ReedSolomon.minDist_of_le (by rwa [Fintype.card_fin]), Fintype.card_fin]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    rw [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, le_div_iff₀ two_pos,
      ← NNReal.coe_le_coe]
    exact_mod_cast (show e * 2 ≤ N - k by omega)
  refine hmono.trans ((ProximityGap.mcaError_powers_le_of_exactPowerAgreement k domain M _
    ((M * N : ℕ) : ℝ) _ le_rfl fun U ↦ ?_).trans (le_of_eq ?_))
  · obtain ⟨E, hE, hgood⟩ := ProximityGap.exists_exactPowerAgreement_unique domain U hk
      (by rwa [Fintype.card_fin]) _ hδ'
    rw [Fintype.card_fin] at hE
    exact ⟨E, by exact_mod_cast hE, hgood⟩
  · simp only [uniqueDecoding]
    push_cast
    rfl

/-- The smaller of two bounds that hold holds. -/
theorem min_holds {B B' : McaBound} (hB : B.Holds) (hB' : B'.Holds) : (B.min B').Holds := by
  intro K _ _ _ _ N k M domain δ h
  have hK : (0 : ℝ) ≤ Fintype.card K := Nat.cast_nonneg _
  simp only [min, Bool.or_eq_true] at h ⊢
  by_cases h1 : B.admits N k δ <;> by_cases h2 : B'.admits N k δ <;>
    simp only [h1, h2, ↓reduceIte, Bool.false_eq_true, or_self, or_false, false_or] at h ⊢
  · rw [Rat.cast_min, ← min_div_div_right hK, ENNReal.ofReal_min]
    exact le_min (hB K N k M domain δ h1) (hB' K N k M domain δ h2)
  · exact hB K N k M domain δ h1
  · exact hB' K N k M domain δ h2

/-- `sqrtUpper ρ` bounds `√ρ` from above. -/
theorem sqrt_le_sqrtUpper (ρ : ℚ) : √(ρ : ℝ) ≤ (sqrtUpper ρ : ℝ) := by
  set n := ⌊ρ * 2 ^ 40⌋₊
  have hn : ρ * 2 ^ 40 < (n.sqrt + 1 : ℕ) * (n.sqrt + 1 : ℕ) := by
    have h1 := Nat.lt_floor_add_one (ρ * 2 ^ 40)
    have h2 : n + 1 ≤ (n.sqrt + 1) * (n.sqrt + 1) := Nat.lt_succ_sqrt n
    have h3 : ((n + 1 : ℕ) : ℚ) ≤ ((n.sqrt + 1) * (n.sqrt + 1) : ℕ) := by exact_mod_cast h2
    push_cast at h1 h3 ⊢
    linarith
  have hu : (0 : ℝ) ≤ (sqrtUpper ρ : ℝ) := by unfold sqrtUpper; positivity
  rw [Real.sqrt_le_left hu]
  have : (ρ : ℝ) ≤ (sqrtUpper ρ : ℝ) ^ 2 := by
    have : ρ ≤ sqrtUpper ρ ^ 2 := by
      unfold sqrtUpper
      rw [div_pow, le_div_iff₀ (by positivity)]
      push_cast at hn ⊢
      nlinarith
    exact_mod_cast this
  exact this

/-- `ceilSqrt x ≤ c` exactly when `x ≤ c²`. -/
theorem ceilSqrt_le_iff (x : ℚ) (c : ℕ) : ceilSqrt x ≤ c ↔ x ≤ (c : ℚ) ^ 2 := by
  have hc : x ≤ (c : ℚ) ^ 2 ↔ ⌈x⌉₊ ≤ c ^ 2 := by
    rw [Nat.ceil_le]
    push_cast
    rfl
  rw [hc, ceilSqrt]
  generalize ⌈x⌉₊ = y
  split_ifs with h
  · simp only [zero_le, h]
  · rw [Nat.add_one_le_iff, Nat.sqrt_lt']
    omega

/-- `⌈√x⌉ = ceilSqrt x`. -/
theorem natCeil_sqrt (x : ℚ) : ⌈√(x : ℝ)⌉₊ = ceilSqrt x := by
  refine le_antisymm (Nat.ceil_le.mpr ?_) ((ceilSqrt_le_iff x _).mpr ?_)
  · rw [Real.sqrt_le_left (Nat.cast_nonneg _)]
    exact_mod_cast (ceilSqrt_le_iff x (ceilSqrt x)).mp le_rfl
  · have : (x : ℝ) ≤ (⌈√(x : ℝ)⌉₊ : ℝ) ^ 2 := by
      rcases le_or_gt (x : ℝ) 0 with hx | hx
      · exact hx.trans (sq_nonneg _)
      · calc (x : ℝ) = √(x : ℝ) ^ 2 := (Real.sq_sqrt hx.le).symm
          _ ≤ _ := pow_le_pow_left₀ (Real.sqrt_nonneg _) (Nat.le_ceil _) 2
    exact_mod_cast this

/-- `⌈x⌉₊` of a rational is the same in `ℝ`. -/
theorem natCeil_ratCast (x : ℚ) : ⌈(x : ℝ)⌉₊ = ⌈x⌉₊ :=
  Nat.ceil_congr fun n ↦ by rw [← Rat.cast_natCast, Rat.cast_le]

open ReedSolomon HiddenDerivative in
/-- At the slack `η = √ρ₋ / (2m)`, `m ≥ 3`, ArkLib's Johnson exception count is
`johnsonLineCount`: the multiplicity is `m`. -/
theorem johnsonExceptionCount_eq {n D A m : ℕ} (hD : 1 ≤ D) (hDn : D < n) (hm : 3 ≤ m) :
    johnsonExceptionCount n D A (√(johnsonRhoMinus n D) / (2 * m)) =
      (johnsonLineCount n D A m : ℝ) := by
  have hs : 0 < √(johnsonRhoMinus n D) := Real.sqrt_pos.2 (johnsonRhoMinus_pos hD hDn)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set η := √(johnsonRhoMinus n D) / (2 * m)
  have hM : johnsonM n D η = m := by
    rw [johnsonM, show √(johnsonRhoMinus n D) / (2 * η) = (m : ℝ) by
      simp only [η]; field_simp, Nat.ceil_natCast]
    exact max_eq_left hm
  have hT : johnsonT n D η = (((m : ℚ) + 1 / 2 : ℚ) : ℝ) := by
    rw [johnsonT, hM]
    push_cast
    rfl
  have hρ : johnsonRhoMinus n D = (((D : ℚ) / n : ℚ) : ℝ) := by
    rw [johnsonRhoMinus]
    push_cast
    rfl
  have hμ : johnsonMu n D η = ceilSqrt (((m : ℚ) + 1 / 2) ^ 2 / ((D : ℚ) / n)) - 1 := by
    rw [johnsonMu, ← natCeil_sqrt, hT]
    congr 2
    rw [hρ, Rat.cast_div (((m : ℚ) + 1 / 2) ^ 2), Rat.cast_pow,
      Real.sqrt_div' _ (Rat.cast_nonneg.mpr (by positivity)), Real.sqrt_sq (by positivity)]
  have hh : johnsonH n D η = ⌈((m : ℚ) + 1 / 2) ^ 2 / (3 * ((D : ℚ) / n))⌉₊ - 1 := by
    rw [johnsonH, ← natCeil_ratCast, hT, hρ]
    push_cast
    rfl
  rw [johnsonExceptionCount, johnsonTheta, hμ, hh, johnsonLineCount]
  push_cast
  rfl

open ReedSolomon HiddenDerivative in
/-- **The Johnson bound holds**, from ArkLib's Johnson-regime MCA for power curves
(`ReedSolomon.exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype`, [DKT26] Theorem 5.12
for curves) at the slack `η = √ρ₋ / (2m)`: the multiplicity is `m`, and `√ρ₋ + η ≤ 1 - δ` because
`m ≥ r / (2 (1 - δ - r))` with `r ≥ √ρ₋`. -/
theorem johnson_holds : johnson.Holds := by
  intro K _ _ _ _ N k M domain δ h
  simp only [johnson, decide_eq_true_eq] at h
  obtain ⟨hk, hkN, hδ0, hr⟩ := h
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · rw [RSCode.mcaError_zeroPowers_eq_zero]
    exact bot_le
  obtain ⟨D, rfl⟩ : ∃ D, k = D + 1 := ⟨k - 1, by omega⟩
  have hD : 1 ≤ D := by omega
  simp only [Nat.add_sub_cancel] at hr ⊢
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  set ρ : ℚ := (D : ℚ) / N with hρdef
  set r := sqrtUpper ρ
  set m := johnsonMult ρ δ
  have hρR : johnsonRhoMinus N D = (ρ : ℝ) := by
    rw [johnsonRhoMinus, hρdef]
    push_cast
    rfl
  have hsq : √(johnsonRhoMinus N D) ≤ (r : ℝ) := by
    rw [hρR]
    exact sqrt_le_sqrtUpper ρ
  have hs : 0 < √(johnsonRhoMinus N D) := Real.sqrt_pos.2 (johnsonRhoMinus_pos hD (by omega))
  have hm3 : 3 ≤ m := le_max_right _ _
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  set η : ℝ := √(johnsonRhoMinus N D) / (2 * m)
  have hη : 0 < η := by positivity
  -- `r ≤ 2 m (1 - δ - r)`, so `√ρ₋ (1 + 2m) ≤ 2 m (1 - δ)`.
  have hgap : (0 : ℝ) < 1 - δ - r := by
    have : (r : ℝ) < 1 - δ := by exact_mod_cast hr
    linarith
  have hmr : (r : ℝ) ≤ 2 * m * (1 - δ - r) := by
    have h1 : r / (2 * (1 - δ - r)) ≤ (m : ℚ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast le_max_left _ _)
    have h2 : ((r / (2 * (1 - δ - r)) : ℚ) : ℝ) ≤ m := by exact_mod_cast h1
    push_cast at h2
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have hagree : johnsonAgreement N D η ≤ 1 - δ := by
    rw [johnsonAgreement]
    have : √(johnsonRhoMinus N D) * (2 * m + 1) ≤ 2 * m * (1 - δ) := by nlinarith
    simp only [η]
    rw [← sub_nonneg] at this ⊢
    have h' : (1 - (δ : ℝ)) - (√(johnsonRhoMinus N D) + √(johnsonRhoMinus N D) / (2 * m)) =
        (2 * m * (1 - δ) - √(johnsonRhoMinus N D) * (2 * m + 1)) / (2 * m) := by
      field_simp
    rw [h']
    positivity
  set A := ⌈(N : ℚ) * (1 - δ)⌉₊
  have hA : johnsonAgreement N D η * N ≤ A := by
    have h1 : ((N : ℚ) * (1 - δ) : ℚ) ≤ (A : ℚ) := Nat.le_ceil _
    have h2 : ((N * (1 - δ) : ℚ) : ℝ) ≤ (A : ℝ) := by exact_mod_cast h1
    push_cast at h2
    nlinarith
  have hAN : A ≤ N := by
    refine Nat.ceil_le.mpr ?_
    have : (0 : ℚ) ≤ N * δ := by positivity
    linarith
  have hthr : A ≤ ⌈(Fintype.card (Fin N) : ℝ) * (1 - (δ : ℝ))⌉₊ := by
    rw [Fintype.card_fin, show (N : ℝ) * (1 - (δ : ℝ)) = ((N * (1 - δ) : ℚ) : ℝ) by push_cast; rfl,
      natCeil_ratCast]
  refine (ProximityGap.mcaError_powers_le_of_exactPowerAgreement (D + 1) domain M A _ _ hthr
    fun w ↦ exists_johnson_curve_exactPowerAgreement_line_mul_of_fintype domain w hD
      (by rw [Fintype.card_fin]; omega) hη hM (by rwa [Fintype.card_fin])
      (by rwa [Fintype.card_fin])).trans
    (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (le_of_eq ?_) (Nat.cast_nonneg _)))
  rw [Fintype.card_fin, johnsonExceptionCount_eq hD (by omega) hm3]
  simp only [johnson, Nat.add_sub_cancel]
  push_cast
  rfl

/-- The bound up to the Johnson radius holds. -/
theorem uniqueOrJohnson_holds : uniqueOrJohnson.Holds :=
  min_holds uniqueDecoding_holds johnson_holds

end McaBound

end CompStark.Sound
