/-
Copyright (c) 2026 zkSecurity. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import CompStark.Sound.PowersMca

/-! # Bounds on mutual correlated agreement for Reed–Solomon codes and power curves

A `McaBound` is a computable bound on the mutual correlated-agreement error of the powers generator
`z ↦ (1, z, …, z^M)` for Reed–Solomon codes: `admits N k δ` says that it covers the code of degree
below `k` on `N` points at radius `δ`, and `count N k M δ` bounds the exceptional seeds there for
curves of degree `M`. `McaBound.Holds B` asks that the counts are exception counts over every
finite field `K` and on every evaluation domain: the MCA error is at most `count / |K|`. The
security calculator (`CompStark/SecurityCalculator.lean`) is parametric in the bound, and the
soundness theorems built on it take `Holds` as their hypothesis.

* `uniqueDecoding`: within the unique-decoding radius, `2 ⌊δ N⌋ ≤ N - k`, at most `M N` exceptional
  seeds (`uniqueDecoding_holds`, from `mcaError_powers_le` at the radius `⌊δ N⌋ / N`, which has the
  same MCA events).
* `johnson`: up to the Johnson radius `1 - √ρ₋`, `ρ₋ = (k - 1) / N`, the closed form
  `M · 8 N t³ / (3 ρ₋)` of [DKT26] Theorem 5.12's line bound times the curve degree, with
  `t = m + 1/2`, `m = max(⌈r / (2η)⌉, 3)`, `r ≥ √ρ₋` dyadic and `η = 1 - δ - r > 0`.
* `min`: the smaller count where both bounds apply (`min_holds`).
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

/-- A dyadic upper bound `r ≥ √ρ`, `r ≤ √ρ + 2 ^ (-20)`. -/
def sqrtUpper (ρ : ℚ) : ℚ := ((⌊ρ * 2 ^ 40⌋₊.sqrt + 1 : ℕ) : ℚ) / 2 ^ 20

/-- The Johnson regime: for `2 ≤ k < N` and `δ < 1 - r`, `r = sqrtUpper ρ₋ ≥ √ρ₋`,
`ρ₋ = (k - 1) / N`, the count `M · 8 N t³ / (3 ρ₋)` with `t = max(⌈r / (2η)⌉, 3) + 1/2` and
`η = 1 - δ - r`: [DKT26] Theorem 5.12's closed form, times the curve degree `M`. -/
def johnson : McaBound where
  admits N k δ := decide (2 ≤ k ∧ k < N ∧ 0 ≤ δ ∧ sqrtUpper ((k - 1 : ℕ) / N) < 1 - δ)
  count N k M δ :=
    let ρ : ℚ := (k - 1 : ℕ) / N
    let r := sqrtUpper ρ
    let t : ℚ := (Max.max ⌈r / (2 * (1 - δ - r))⌉₊ 3 : ℕ) + 1 / 2
    M * (8 * N * t ^ 3 / (3 * ρ))
  count_nonneg N k M δ := by
    dsimp only
    positivity

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
  refine hmono.trans ((mcaError_powers_le hk hkN M ?_).trans (le_of_eq ?_))
  · rw [relativeUniqueDecodingRadius, dist_eq_minDist,
      ReedSolomon.minDist_of_le (by rwa [Fintype.card_fin]), Fintype.card_fin]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg N)
    rw [Nat.cast_add, Nat.cast_one, add_tsub_cancel_right, le_div_iff₀ two_pos,
      ← NNReal.coe_le_coe]
    exact_mod_cast (show e * 2 ≤ N - k by omega)
  · have hK : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
    rw [ENNReal.ofReal_div_of_pos hK, ENNReal.ofReal_natCast]
    simp only [uniqueDecoding]
    push_cast
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast]
    congr 1
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]

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

end McaBound

end CompStark.Sound
